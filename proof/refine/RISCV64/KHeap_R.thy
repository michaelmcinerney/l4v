(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_R
imports
  Machine_R
begin

lemma lookupAround2_known1:
  "m x = Some y \<Longrightarrow> fst (lookupAround2 x m) = Some (x, y)"
  by (fastforce simp: lookupAround2_char1)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma obj_at_getObject:
  assumes R:
  "\<And>a b n ko s obj::'a::pspace_storable.
  \<lbrakk> (a, b) \<in> fst (loadObject t t n ko s); projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(rv::'a::pspace_storable) s. P rv\<rbrace>"
  by (auto simp: getObject_def obj_at'_def in_monad valid_def
                 split_def lookupAround2_known1
           dest: R)

declare projectKO_inv [wp]

lemma loadObject_default_inv:
  "\<lbrace>P\<rbrace> loadObject_default addr addr' next obj \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: loadObject_default_def magnitudeCheck_def
                   alignCheck_def unless_def alignError_def
          | wp hoare_vcg_split_case_option
               hoare_drop_imps hoare_vcg_all_lift)+
  done

lemma getObject_inv:
  assumes x: "\<And>p q n ko. \<lbrace>P\<rbrace> loadObject p q n ko \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  by (simp add: getObject_def split_def | wp x)+

lemma getObject_inv_tcb [wp]: "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>(rv :: Structures_H.tcb). P\<rbrace>"
  apply (rule getObject_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done
end
(* FIXME: this should go somewhere in spec *)
translations
  (type) "'a kernel" <=(type) "kernel_state \<Rightarrow> ('a \<times> kernel_state) set \<times> bool"

context begin interpretation Arch . (*FIXME: arch_split*)

lemma no_fail_loadObject_default [wp]:
  "no_fail (\<lambda>s. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and>
                      is_aligned p (objBits obj) \<and> q = p
                      \<and> case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n)
           (loadObject_default p q n ko :: ('a::pre_storable) kernel)"
  apply (simp add: loadObject_default_def split_def projectKO_def
                   alignCheck_def alignError_def magnitudeCheck_def
                   unless_def)
  apply (rule no_fail_pre)
   apply (wp case_option_wp)
  apply (clarsimp simp: is_aligned_mask)
  apply (clarsimp split: option.split_asm)
  apply (clarsimp simp: is_aligned_mask[symmetric])
  apply simp
  done

lemma no_fail_getObject_tcb [wp]:
  "no_fail (tcb_at' t) (getObject t :: tcb kernel)"
  apply (simp add: getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps'
                      cong: conj_cong)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (fastforce split: option.split_asm simp: objBits_simps')
  done

lemma typ_at_to_obj_at':
  "typ_at' (koType (TYPE ('a :: pspace_storable))) p s
     = obj_at' (\<top> :: 'a \<Rightarrow> bool) p s"
  by (simp add: typ_at'_def obj_at'_real_def project_koType[symmetric])

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]


lemma corres_get_tcb:
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t) (gets (get_tcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp add: gets_def get_def return_def bind_def get_tcb_def)
  apply (frule in_inv_by_hoareD [OF getObject_inv_tcb])
  apply (clarsimp simp add: obj_at_def is_tcb obj_at'_def projectKO_def
                            projectKO_opt_tcb split_def
                            getObject_def loadObject_default_def in_monad)
  apply (case_tac koa)
   apply (simp_all add: fail_def return_def)
  apply (case_tac bb)
   apply (simp_all add: fail_def return_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply clarsimp
   apply blast
  apply (clarsimp simp add: other_obj_relation_def
                            lookupAround2_known1)
  done

lemma lookupAround2_same1[simp]:
  "(fst (lookupAround2 x s) = Some (x, y)) = (s x = Some y)"
  apply (rule iffI)
   apply (simp add: lookupAround2_char1)
  apply (simp add: lookupAround2_known1)
  done

lemma getObject_tcb_at':
  "\<lbrace> \<top> \<rbrace> getObject t \<lbrace>\<lambda>r::tcb. tcb_at' t\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad
                     loadObject_default_def obj_at'_def split_def
                     in_magnitude_check objBits_simps')

text \<open>updateObject_cte lemmas\<close>

lemma koType_objBitsKO:
  "koTypeOf k = koTypeOf k' \<Longrightarrow> objBitsKO k = objBitsKO k'"
  by (auto simp: objBitsKO_def archObjSize_def
          split: kernel_object.splits arch_kernel_object.splits)

lemma updateObject_objBitsKO:
    "(ko', t') \<in> fst (updateObject (val :: 'a :: pspace_storable) ko p q n t)
         \<Longrightarrow> objBitsKO ko' = objBitsKO ko"
  apply (drule updateObject_type)
  apply (erule koType_objBitsKO)
  done

lemma updateObject_cte_is_tcb_or_cte:
  fixes cte :: cte and ptr :: machine_word
  shows "\<lbrakk> fst (lookupAround2 p (ksPSpace s)) = Some (q, ko);
           snd (lookupAround2 p (ksPSpace s)) = n;
           (ko', s') \<in> fst (updateObject cte ko p q n s) \<rbrakk> \<Longrightarrow>
  (\<exists>tcb getF setF. ko = KOTCB tcb \<and> s' = s \<and> tcb_cte_cases (p - q) = Some (getF, setF)
    \<and> ko' = KOTCB (setF (\<lambda>x. cte) tcb) \<and> is_aligned q tcbBlockSizeBits \<and> ps_clear q tcbBlockSizeBits s) \<or>
  (\<exists>cte'. ko = KOCTE cte' \<and> ko' = KOCTE cte \<and> s' = s
        \<and> p = q \<and> is_aligned p cte_level_bits \<and> ps_clear p cte_level_bits s)"
  apply (clarsimp simp: updateObject_cte typeError_def alignError_def
                        tcbVTableSlot_def tcbCTableSlot_def to_bl_1 rev_take  objBits_simps'
                        in_monad map_bits_to_bl cte_level_bits_def in_magnitude_check field_simps
                        lookupAround2_char1
         split: kernel_object.splits)
  apply (subst(asm) in_magnitude_check3, simp+)
   apply (simp add: in_monad tcbCTableSlot_def tcbVTableSlot_def
                    tcbReplySlot_def tcbCallerSlot_def tcbIPCBufferSlot_def
             split: if_split_asm)
  apply (simp add: in_monad tcbCTableSlot_def tcbVTableSlot_def
                   tcbReplySlot_def tcbCallerSlot_def tcbIPCBufferSlot_def
            split: if_split_asm)
  done

declare plus_1_less[simp]

lemma updateObject_default_result:
  "(x, s'') \<in> fst (updateObject_default e ko p q n s) \<Longrightarrow> x = injectKO e"
  by (clarsimp simp add: updateObject_default_def in_monad)

lemma obj_at_setObject1:
  assumes R: "\<And>(v::'a::pspace_storable) p q n ko s x s''.
                (x, s'') \<in> fst (updateObject v ko p q n s) \<Longrightarrow> x = injectKO v"
  shows
  "\<lbrace> obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>
   setObject p (v::'a::pspace_storable)
  \<lbrace> \<lambda>rv. obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad obj_at'_def lookupAround2_char1 project_inject
                 dest!: R)
  apply (subgoal_tac "objBitsKO (injectKO v) = objBitsKO (injectKO obj)")
   apply (intro conjI impI, simp_all)
      apply fastforce+
  apply (fold objBits_def)
  apply (rule Q)
  done

lemma obj_at_setObject2:
  fixes v :: "'a::pspace_storable"
  fixes P :: "'b::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s' (v :: 'a) oko x y n s. (ko, s') \<in> fst (updateObject v oko x y n s)
                                  \<Longrightarrow> koTypeOf ko \<noteq> koType TYPE('b)"
  shows
  "\<lbrace> obj_at' P t \<rbrace>
   setObject p (v::'a)
  \<lbrace> \<lambda>rv. obj_at' P t \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (drule R)
  apply (clarsimp simp: obj_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: lookupAround2_char1)
   apply (drule iffD1 [OF project_koType, OF exI])
   apply simp
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
  done

lemma updateObject_ep_eta:
  "updateObject (v :: endpoint) = updateObject_default v"
  by ((rule ext)+, simp)

lemma updateObject_tcb_eta:
  "updateObject (v :: tcb) = updateObject_default v"
  by ((rule ext)+, simp)

lemma updateObject_ntfn_eta:
  "updateObject (v :: Structures_H.notification) = updateObject_default v"
  by ((rule ext)+, simp)

lemmas updateObject_eta =
  updateObject_ep_eta updateObject_tcb_eta updateObject_ntfn_eta

lemma objBits_type:
  "koTypeOf k = koTypeOf k' \<Longrightarrow> objBitsKO k = objBitsKO k'"
  by (erule koType_objBitsKO)

lemma setObject_typ_at_inv:
  "\<lbrace>typ_at' T p'\<rbrace> setObject p v \<lbrace>\<lambda>r. typ_at' T p'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def typ_at'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd)
  apply (drule updateObject_type)
  apply clarsimp
  apply (drule objBits_type)
  apply (simp add: ps_clear_upd)
  done

lemma setObject_typ_at_not:
  "\<lbrace>\<lambda>s. \<not> (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. \<not> (typ_at' T p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def)
  apply (erule notE)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_char1
                 split: if_split_asm)
   apply (drule updateObject_type)
   apply clarsimp
   apply (drule objBits_type)
   apply (clarsimp elim!: ps_clear_domE)
   apply fastforce
  apply (clarsimp elim!: ps_clear_domE)
  apply fastforce
  done

lemma setObject_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. P (typ_at' T p' s)\<rbrace>"
  by (blast intro: P_bool_lift setObject_typ_at_inv setObject_typ_at_not)

lemmas setObject_typ_ats [wp] = typ_at_lifts [OF setObject_typ_at']

lemma setObject_cte_wp_at2':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>\<lambda>s. P' (cte_wp_at' P p s) \<and> Q s\<rbrace> setObject ptr v \<lbrace>\<lambda>rv s. P' (cte_wp_at' P p s)\<rbrace>"
  apply (clarsimp simp add: setObject_def valid_def in_monad split_def)
  apply (simp add: cte_wp_at_cases' split del: if_split)
  apply (erule rsubst[where P=P'])
  apply (rule iffI)
   apply (erule disjEI)
    apply (clarsimp simp: ps_clear_upd lookupAround2_char1 y)
   apply (erule exEI [where 'a=machine_word])
   apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
   apply (drule(1) x)
    apply (clarsimp simp: lookupAround2_char1 prod_eqI)
   apply (fastforce dest: bspec [OF _ ranI])
  apply (erule disjEI)
   apply (clarsimp simp: ps_clear_upd lookupAround2_char1
                  split: if_split_asm)
   apply (frule updateObject_type)
   apply (case_tac ba, simp_all add: y)[1]
  apply (erule exEI)
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1
                 split: if_split_asm)
  apply (frule updateObject_type)
  apply (case_tac ba, simp_all)
  apply (drule(1) x)
   apply (clarsimp simp: prod_eqI lookupAround2_char1)
  apply (fastforce dest: bspec [OF _ ranI])
  done

lemma setObject_cte_wp_at':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>cte_wp_at' P p and Q\<rbrace> setObject ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding pred_conj_def
  by (rule setObject_cte_wp_at2'[OF x y], assumption+)

lemma setObject_ep_pre:
  assumes "\<lbrace>P and ep_at' p\<rbrace> setObject p (e::endpoint) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (e::endpoint) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad in_magnitude_check)
  done

lemma setObject_ntfn_pre:
  assumes "\<lbrace>P and ntfn_at' p\<rbrace> setObject p (e::Structures_H.notification) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (e::Structures_H.notification) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad in_magnitude_check)
  done

lemma setObject_tcb_pre:
  assumes "\<lbrace>P and tcb_at' p\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad in_magnitude_check)
  done

lemma setObject_tcb_ep_at:
  shows
  "\<lbrace> ep_at' t \<rbrace>
   setObject p (x::tcb)
  \<lbrace> \<lambda>rv. ep_at' t \<rbrace>"
  apply (rule obj_at_setObject2)
  apply (auto dest: updateObject_default_result)
  done

lemma obj_at_setObject3:
  fixes Q::"'a::pspace_storable \<Rightarrow> bool"
  fixes P::"'a::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows "\<lbrace>(\<lambda>s. P v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  apply (clarsimp simp add: valid_def in_monad obj_at'_def
                            setObject_def split_def project_inject objBits_def[symmetric]
                            R updateObject_default_def in_magnitude_check P ps_clear_upd)
  apply fastforce
  done

lemma setObject_tcb_strongest:
  "\<lbrace>\<lambda>s. if t = t' then P tcb else obj_at' P t' s\<rbrace>
  setObject t (tcb :: tcb)
  \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (cases "t = t'")
   apply simp
   apply (rule hoare_weaken_pre)
    apply (rule obj_at_setObject3)
     apply simp
    apply (simp add: objBits_simps')
   apply simp
  apply (simp add: setObject_def split_def)
  apply (clarsimp simp: valid_def obj_at'_def split_def in_monad
                        updateObject_default_def ps_clear_upd)
  done

lemma getObject_obj_at':
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. obj_at' ((=) r) p\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad
                     loadObject_default_def obj_at'_def
                     split_def in_magnitude_check lookupAround2_char1
                     x P project_inject objBits_def[symmetric])

lemma getObject_valid_obj:
  assumes x: "\<And>p q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows "\<lbrace> valid_objs' \<rbrace> getObject p \<lbrace>\<lambda>rv::'a::pspace_storable. valid_obj' (injectKO rv) \<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_obj_at' [OF x P])
    apply (rule getObject_inv)
    apply (subst x)
    apply (rule loadObject_default_inv)
   apply (clarsimp, assumption)
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: project_inject)
  done

declare fail_inv[simp]

lemma typeError_inv [wp]:
  "\<lbrace>P\<rbrace> typeError x y \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: typeError_def|wp)+

lemma getObject_cte_inv [wp]: "\<lbrace>P\<rbrace> (getObject addr :: cte kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getObject_def loadObject_cte split_def)
  apply (clarsimp simp: valid_def in_monad)
  apply (clarsimp simp: typeError_def in_monad magnitudeCheck_def
                 split: kernel_object.split_asm if_split_asm option.split_asm)
  done

lemma getObject_ko_at:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. ko_at' r p\<rbrace>"
  by (subst eq_commute, rule getObject_obj_at' [OF x P])

lemma getObject_ko_at_tcb [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::tcb. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: objBits_simps')+

lemma OMG_getObject_tcb:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(tcb :: tcb) s. P tcb\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad)
  done

lemma setObject_nosch:
  assumes x: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma getObject_ep_inv: "\<lbrace>P\<rbrace> (getObject addr :: endpoint kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma getObject_ntfn_inv:
  "\<lbrace>P\<rbrace> (getObject addr :: Structures_H.notification kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma get_ep_inv'[wp]: "\<lbrace>P\<rbrace> getEndpoint ep \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getEndpoint_def getObject_ep_inv)

lemma get_ntfn_inv'[wp]: "\<lbrace>P\<rbrace> getNotification ntfn \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getNotification_def getObject_ntfn_inv)

lemma get_ep'_valid_ep[wp]:
  "\<lbrace> invs' and ep_at' ep \<rbrace> getEndpoint ep \<lbrace> valid_ep' \<rbrace>"
  apply (simp add: getEndpoint_def)
  apply (rule hoare_chain)
  apply (rule getObject_valid_obj)
     apply simp
    apply (simp add: objBits_simps')
   apply clarsimp
  apply (simp add: valid_obj'_def)
  done

lemma get_ntfn'_valid_ntfn[wp]:
  "\<lbrace> invs' and ntfn_at' ep \<rbrace> getNotification ep \<lbrace> valid_ntfn' \<rbrace>"
  apply (simp add: getNotification_def)
  apply (rule hoare_chain)
  apply (rule getObject_valid_obj)
     apply simp
    apply (simp add: objBits_simps')
   apply clarsimp
  apply (simp add: valid_obj'_def)
  done

lemma setObject_distinct[wp]:
  shows     "\<lbrace>pspace_distinct'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad lookupAround2_char1
                        pspace_distinct'_def ps_clear_upd objBits_def[symmetric]
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_aligned[wp]:
  shows     "\<lbrace>pspace_aligned'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad lookupAround2_char1
                        pspace_aligned'_def ps_clear_upd objBits_def[symmetric]
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_canonical[wp]:
  shows     "\<lbrace>pspace_canonical'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_canonical'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad lookupAround2_char1
                        pspace_canonical'_def ps_clear_upd objBits_def[symmetric]
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma setObject_in_kernel_mappings[wp]:
  shows     "\<lbrace>pspace_in_kernel_mappings'\<rbrace> setObject p val \<lbrace>\<lambda>rv. pspace_in_kernel_mappings'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad lookupAround2_char1
                        pspace_in_kernel_mappings'_def ps_clear_upd objBits_def[symmetric]
                 split: if_split_asm
                 dest!: updateObject_objBitsKO)
   apply (fastforce dest: bspec[OF _ domI])
  apply (fastforce dest: bspec[OF _ domI])
  done

lemma set_ep_aligned' [wp]:
  "\<lbrace>pspace_aligned'\<rbrace> setEndpoint ep v  \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  unfolding setEndpoint_def by wp

lemma set_ep_distinct' [wp]:
  "\<lbrace>pspace_distinct'\<rbrace> setEndpoint ep v  \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  unfolding setEndpoint_def by wp

crunches setEndpoint, getEndpoint
  for pspace_canonical'[wp]: "pspace_canonical'"
  and pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

lemma setEndpoint_cte_wp_at':
  "\<lbrace>cte_wp_at' P p\<rbrace> setEndpoint ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding setEndpoint_def
  apply (rule setObject_cte_wp_at'[where Q="\<top>", simplified])
   apply (clarsimp simp add: updateObject_default_def in_monad
                     intro!: set_eqI)+
  done

lemma setEndpoint_pred_tcb_at'[wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def setEndpoint_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma get_ntfn_ko':
  "\<lbrace>\<top>\<rbrace> getNotification ep \<lbrace>\<lambda>rv. ko_at' rv ep\<rbrace>"
  apply (simp add: getNotification_def)
  apply (rule getObject_ko_at)
   apply simp
  apply (simp add: objBits_simps')
  done

lemma set_ntfn_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  unfolding setNotification_def by wp

lemma set_ntfn_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  unfolding setNotification_def by wp

lemma setNotification_cte_wp_at':
  "\<lbrace>cte_wp_at' P p\<rbrace> setNotification ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding setNotification_def
  apply (rule setObject_cte_wp_at'[where Q="\<top>", simplified])
   apply (clarsimp simp add: updateObject_default_def in_monad
                     intro!: set_eqI)+
  done

lemma setObject_ep_tcb':
  "\<lbrace>tcb_at' t\<rbrace> setObject p (e::endpoint) \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (rule setObject_typ_ats)

lemma setObject_ntfn_tcb':
  "\<lbrace>tcb_at' t\<rbrace> setObject p (e::Structures_H.notification) \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  by (rule setObject_typ_ats)

lemma set_ntfn_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setNotification ntfn v \<lbrace> \<lambda>rv. tcb_at' t \<rbrace>"
  by (simp add: setNotification_def setObject_ntfn_tcb')

lemma pspace_dom_update:
  "\<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  apply (simp add: pspace_dom_def dom_fun_upd2 del: dom_fun_upd)
  apply (rule SUP_cong [OF refl])
  apply clarsimp
  apply (simp add: obj_relation_cuts_def3)
  done

lemmas ps_clear_def3 = ps_clear_def2 [OF order_less_imp_le [OF aligned_less_plus_1]]

declare diff_neg_mask[simp del]

lemma cte_wp_at_ctes_of:
  "cte_wp_at' P p s = (\<exists>cte. ctes_of s p = Some cte \<and> P cte)"
  apply (simp add: cte_wp_at_cases' map_to_ctes_def Let_def
                   cte_level_bits_def objBits_simps'
          split del: if_split)
  apply (safe del: disjCI)
    apply (clarsimp simp: ps_clear_def3 field_simps)
   apply (clarsimp simp: ps_clear_def3 field_simps
              split del: if_split)
   apply (frule is_aligned_sub_helper)
    apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
   apply (case_tac "n = 0")
    apply (clarsimp simp: field_simps)
   apply (subgoal_tac "ksPSpace s p = None")
    apply clarsimp
    apply (clarsimp simp: field_simps)
   apply (elim conjE)
   apply (subst(asm) mask_in_range, assumption)
   apply (drule arg_cong[where f="\<lambda>S. p \<in> S"])
   apply (simp add: dom_def field_simps)
   apply (erule mp)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule word_le_minus_one_leq)
   apply clarsimp
   apply (simp add: field_simps)
  apply (clarsimp split: if_split_asm del: disjCI)
   apply (simp add: ps_clear_def3 field_simps)
  apply (rule disjI2, rule exI[where x="(p - (p && ~~ mask 10))"])
  apply (clarsimp simp: ps_clear_def3[where na=10] is_aligned_mask add_ac
                        word_bw_assocs)
  done

lemma ctes_of_canonical:
  assumes canonical: "pspace_canonical' s"
  assumes ctes_of: "ctes_of s p = Some cte"
  shows "canonical_address p"
proof -
  from ctes_of have "cte_wp_at' ((=) cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis using canonical canonical_bit_def
    by (fastforce simp: pspace_canonical'_def tcb_cte_cases_def field_simps objBits_defs
                 split: if_splits
                  elim: cte_wp_atE' canonical_address_add)
qed

(* FIXME rt merge: move to Word_lib *)
lemma max_word_minus_1[simp]: "0xFFFFFFFF + 2^x = (2^x - 1::32 word)"
  by simp

lemma ctes_of'_after_update:
  "ko_wp_at' (same_caps' val) p s \<Longrightarrow> ctes_of (s\<lparr>ksPSpace := ksPSpace s(p \<mapsto> val)\<rparr>) x = ctes_of s x"
  apply (clarsimp simp only: ko_wp_at'_def map_to_ctes_def Let_def)
  apply (rule if_cong)
    apply (cases val; fastforce split: if_splits)
   apply (cases val; fastforce split: if_splits)
  apply (rule if_cong)
    apply (cases val; clarsimp; fastforce)
   apply (cases val; clarsimp simp: tcb_cte_cases_def)
  apply simp
  done

lemma ex_cap_to'_after_update:
  "\<lbrakk> ex_nonz_cap_to' p s; ko_wp_at' (same_caps' val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to' p (s\<lparr>ksPSpace := ksPSpace s(p' \<mapsto> val)\<rparr>)"
  unfolding ex_nonz_cap_to'_def cte_wp_at_ctes_of
  using ctes_of'_after_update
  by fastforce

lemma tcb_cte_cases_small:
  "\<lbrakk> tcb_cte_cases v = Some (getF, setF) \<rbrakk>
      \<Longrightarrow> v < 2 ^ tcbBlockSizeBits"
  by (simp add: tcb_cte_cases_def objBits_defs split: if_split_asm)

lemmas tcb_cte_cases_aligned_helpers =
    is_aligned_add_helper [OF _ tcb_cte_cases_small]
    is_aligned_sub_helper [OF _ tcb_cte_cases_small]

lemma ctes_of_from_cte_wp_at:
  assumes x: "\<And>P P' p. \<lbrace>\<lambda>s. P (cte_wp_at' P' p s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>r s. P (cte_wp_at' P' p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ctes_of s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: valid_def
                 elim!: rsubst[where P=P]
                intro!: ext)
  apply (case_tac "ctes_of s x", simp_all)
   apply (drule_tac P1=Not and P'1="\<top>" and p1=x in use_valid [OF _ x],
           simp_all add: cte_wp_at_ctes_of)
  apply (drule_tac P1=id and P'1="(=) aa" and p1=x in use_valid [OF _ x],
          simp_all add: cte_wp_at_ctes_of)
  done

lemmas setObject_ctes_of = ctes_of_from_cte_wp_at [OF setObject_cte_wp_at2']

lemma map_to_ctes_upd_cte:
  "\<lbrakk> s p = Some (KOCTE cte'); is_aligned p cte_level_bits;
     {p + 1..p + mask cte_level_bits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> (KOCTE cte))) = ((map_to_ctes s) (p \<mapsto> cte))"
  apply (rule ext)
  apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
           split del: if_split del: dom_fun_upd)
  apply (case_tac "x = p")
   apply (simp add: objBits_simps' cte_level_bits_def mask_def field_simps)
  apply (case_tac "(x && ~~ mask (objBitsKO (KOTCB undefined))) = p")
   apply clarsimp
  apply (simp del: dom_fun_upd split del: if_split cong: if_cong
              add: dom_fun_upd2 field_simps objBits_simps)
  done

declare overflow_plus_one_self[simp]

lemma map_to_ctes_upd_tcb:
  "\<lbrakk> s p = Some (KOTCB tcb'); is_aligned p tcbBlockSizeBits; {p + 1..p + mask tcbBlockSizeBits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> (KOTCB tcb))) =
      (\<lambda>x. if \<exists>getF setF. tcb_cte_cases (x - p) = Some (getF, setF)
                  \<and> getF tcb \<noteq> getF tcb'
           then (case tcb_cte_cases (x - p) of Some (getF, setF) \<Rightarrow> Some (getF tcb))
           else map_to_ctes s x)"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (subgoal_tac "p && ~~ (mask tcbBlockSizeBits) = p")
   apply (rule ext)
   apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
            split del: if_split del: dom_fun_upd
                 cong: option.case_cong if_cong)
   apply (case_tac "x = p")
    apply (simp add: objBits_simps' field_simps map_to_ctes_def mask_def)
   apply (case_tac "x && ~~ mask (objBitsKO (KOTCB undefined)) = p")
    apply (case_tac "tcb_cte_cases (x - p)")
     apply (simp split del: if_split cong: if_cong option.case_cong)
    apply (subgoal_tac "s x = None")
     apply (simp add: field_simps objBits_simps' mask_def split del: if_split
                cong: if_cong option.case_cong)
     apply clarsimp
    apply (subst(asm) mask_in_range[where bits="objBitsKO v" for v])
     apply (simp add: objBits_simps')
    apply (drule_tac a=x in equals0D)
    apply (simp add: dom_def objBits_simps' mask_def field_simps)
    apply (erule mp)
    apply (rule ccontr, simp add: linorder_not_le)
    apply (drule word_le_minus_one_leq, simp)
   apply (case_tac "tcb_cte_cases (x - p)")
    apply (simp split del: if_split cong: if_cong option.case_cong)
   apply (rule FalseE)
   apply (subst(asm) mask_in_range[where bits="objBitsKO v" for v])
    apply (simp add: objBitsKO_def)
   apply (subgoal_tac "x - p < 2 ^ tcbBlockSizeBits")
    apply (frule word_le_minus_one_leq)
    apply (frule(1) is_aligned_no_wrap')
    apply (drule word_plus_mono_right[where x=p])
     apply (simp only: field_simps)
     apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps' field_simps)
   apply (clarsimp simp: tcb_cte_cases_def objBits_simps' mask_def field_simps
                  split: if_split_asm)
  apply (subst mask_in_range, assumption)
  apply (simp only: atLeastAtMost_iff order_refl simp_thms)
  apply (erule is_aligned_no_overflow)
  done

lemma map_to_ctes_upd_other:
  "\<lbrakk> s p = Some ko; case ko of KOTCB tcb \<Rightarrow> False | KOCTE cte \<Rightarrow> False | _ \<Rightarrow> True;
     case ko' of KOTCB tcb \<Rightarrow> False | KOCTE cte \<Rightarrow> False | _ \<Rightarrow> True \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> ko')) = (map_to_ctes s)"
  apply (rule ext)
  apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
           split del: if_split del: dom_fun_upd
                cong: if_cong)
  apply (rule if_cong)
    apply clarsimp
    apply fastforce
   apply clarsimp
  apply (rule if_cong)
    apply clarsimp
    apply fastforce
   apply clarsimp
  apply (rule refl)
  done

lemma ctes_of_eq_cte_wp_at':
  "cte_wp_at' ((=) cte) x s \<Longrightarrow> ctes_of s x = Some cte"
  by (simp add: cte_wp_at_ctes_of)

lemma tcb_cte_cases_change:
  "tcb_cte_cases x = Some (getF, setF) \<Longrightarrow>
   (\<exists>getF. (\<exists>setF. tcb_cte_cases y = Some (getF, setF)) \<and> getF (setF f tcb) \<noteq> getF tcb)
     = (x = y \<and> f (getF tcb) \<noteq> getF tcb)"
  apply (rule iffI)
   apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
  apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
  done

lemma cte_level_bits_nonzero [simp]: "0 < cte_level_bits"
  by (simp add: cte_level_bits_def)

lemma ctes_of_setObject_cte:
  "\<lbrace>\<lambda>s. P ((ctes_of s) (p \<mapsto> cte))\<rbrace> setObject p (cte :: cte) \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim exE conjE disjE rsubst[where P=P])
   apply (clarsimp simp: lookupAround2_char1)
   apply (subst map_to_ctes_upd_tcb; assumption?)
    apply (clarsimp simp: mask_def objBits_defs field_simps ps_clear_def3)
   apply (clarsimp simp: tcb_cte_cases_change)
   apply (rule ext, clarsimp)
   apply (intro conjI impI)
    apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
   apply (drule(1) cte_wp_at_tcbI'[where P="(=) cte"])
      apply (simp add: ps_clear_def3 field_simps)
     apply assumption+
   apply (simp add: cte_wp_at_ctes_of)
  apply (clarsimp simp: map_to_ctes_upd_cte ps_clear_def3 field_simps mask_def)
  done

declare foldl_True[simp]

lemma real_cte_at':
  "real_cte_at' p s \<Longrightarrow> cte_at' p s"
  by (clarsimp simp add: cte_wp_at_cases' obj_at'_def objBits_simps' cte_level_bits_def
                    del: disjCI)

lemma no_fail_getEndpoint [wp]:
  "no_fail (ep_at' ptr) (getEndpoint ptr)"
  apply (simp add: getEndpoint_def getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps' lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply (simp add: word_bits_conv)
  apply (clarsimp split: option.split_asm simp: objBits_simps')
  done

lemma getEndpoint_corres:
  "corres ep_relation (ep_at ptr) (ep_at' ptr)
     (get_endpoint ptr) (getEndpoint ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getEndpoint_def get_object_def
                   getObject_def bind_assoc ep_at_def2)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def)
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ep partial_inv_def)
  apply (clarsimp simp: loadObject_default_def in_monad in_magnitude_check objBits_simps')
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

declare magnitudeCheck_inv [wp]

declare alignCheck_inv [wp]

lemma setObject_ct_inv:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_cd_inv:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_it_inv:
"\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ksDomSchedule_inv:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma projectKO_def2:
  "projectKO ko = assert_opt (projectKO_opt ko)"
  by (simp add: projectKO_def assert_opt_def)

lemma no_fail_magnitudeCheck[wp]:
  "no_fail (\<lambda>s. case y of None \<Rightarrow> True | Some z \<Rightarrow> 2 ^ n \<le> z - x)
    (magnitudeCheck x y n)"
  apply (clarsimp simp add: magnitudeCheck_def split: option.splits)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma no_fail_setObject_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "no_fail (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr)
                  (setObject ptr ob)"
  apply (simp add: setObject_def x split_def updateObject_default_def
                   projectKO_def2 alignCheck_def alignError_def)
  apply (rule no_fail_pre)
   apply (wp )
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def
                        objBits_def[symmetric] project_inject lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (subst add_diff_eq[symmetric])
    apply (erule is_aligned_no_wrap')
    apply simp
   apply simp
  apply (fastforce simp: oassert_opt_def project_inject split: option.splits)
  done

lemma obj_relation_cut_same_type:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko z;
    (y', P') \<in> obj_relation_cuts ko' x'; P' ko' z \<rbrakk>
     \<Longrightarrow> (a_type ko = a_type ko') \<or> (\<exists>n n'. a_type ko = ACapTable n \<and> a_type ko' = ACapTable n')
         \<or> (\<exists>n n'. a_type ko = ASchedContext n \<and> a_type ko' = ASchedContext n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  apply (auto simp: other_obj_relation_def cte_relation_def pte_relation_def
             split: Structures_A.kernel_object.split_asm if_split_asm
                    Structures_H.kernel_object.split_asm
                    arch_kernel_obj.split_asm)
  done

lemma replyNexts_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> ko)\<rparr>) = replyNexts_of s'"
  by (fastforce simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: kernel_object.splits)

definition replyNext_same :: "'a :: pspace_storable \<Rightarrow> 'a \<Rightarrow> bool" where
  "replyNext_same obj1 obj2 \<equiv>
    (case (injectKO obj1, injectKO obj2) of
       (KOReply r1, KOReply r2) \<Rightarrow> replyNext r1 = replyNext r2
      | _ \<Rightarrow> True)"

lemma replyNexts_of_replyNext_same_update:
  "\<And>s'. \<lbrakk>typ_at' ReplyT ptr s'; ksPSpace s' ptr = Some ko;
   koTypeOf (injectKO (ob':: 'a :: pspace_storable)) = ReplyT;
   projectKO_opt ko = Some ab; replyNext_same (ob':: 'a) ab\<rbrakk>
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> injectKO ob')\<rparr>) = replyNexts_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyNext_same_def project_inject projectKO_opts_defs opt_map_def)

lemma replyPrevs_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> ko)\<rparr>) = replyPrevs_of s'"
  by (fastforce simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: kernel_object.splits)

definition replyPrev_same :: "'a :: pspace_storable \<Rightarrow> 'a \<Rightarrow> bool" where
  "replyPrev_same obj1 obj2 \<equiv>
    (case (injectKO obj1, injectKO obj2) of
       (KOReply r1, KOReply r2) \<Rightarrow> replyPrev r1 = replyPrev r2
      | _ \<Rightarrow> True)"

lemma replyPrevs_of_replyPrev_same_update:
  "\<And>s'. \<lbrakk>typ_at' ReplyT ptr s'; ksPSpace s' ptr = Some ko;
   koTypeOf (injectKO (ob':: 'a :: pspace_storable)) = ReplyT;
   projectKO_opt ko = Some ab; replyPrev_same (ob':: 'a) ab\<rbrakk>
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> injectKO ob')\<rparr>) = replyPrevs_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyPrev_same_def project_inject projectKO_opts_defs opt_map_def)

lemma setObject_other_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes e: "\<And>ko. P ko \<Longrightarrow> exst_same' (injectKO ko) (injectKO ob')"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObject ptr ob')"
  supply image_cong_simp [cong del] projectKOs[simp del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def in_magnitude_check[OF _ P]
                        updateObject_default_def)
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI[rotated])
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
   apply (simp split: arch_kernel_obj.splits if_splits)
  apply (fold fun_upd_def)
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t)
   apply (drule(1) bspec)
   apply clarsimp
   apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type,
           (fastforce simp add: is_other_obj_relation_type t)+)
   apply (erule disjE)
    apply (simp add: is_other_obj_relation_type t)
   apply (erule disjE)
    apply (insert t,
      clarsimp simp: is_other_obj_relation_type_CapTable a_type_def)
   apply (erule disjE)
    apply (insert t,
       clarsimp simp: is_other_obj_relation_type_UserData a_type_def)
   apply (insert t,
      clarsimp simp: is_other_obj_relation_type_DeviceData a_type_def)
  apply (simp only: ekheap_relation_def)
  apply (rule ballI, drule(1) bspec)
  apply (drule domD)
  apply (insert e)
  apply atomize
  apply (clarsimp simp: obj_at'_def)
  apply (erule_tac x=obj in allE)
  apply (clarsimp simp: projectKO_eq project_inject)
  apply (case_tac ob;
         simp_all add: a_type_def other_obj_relation_def etcb_relation_def
                       is_other_obj_relation_type t exst_same_def)
    apply (clarsimp simp: is_other_obj_relation_type t exst_same_def
                   split: Structures_A.kernel_object.splits Structures_H.kernel_object.splits
                          arch_kernel_obj.splits)+
  done

lemmas obj_at_simps = obj_at_def obj_at'_def map_to_ctes_upd_other
                      is_other_obj_relation_type_def
                      a_type_def objBits_simps other_obj_relation_def pageBits_def

lemma setEndpoint_corres:
  "ep_relation e e' \<Longrightarrow>
  corres dc (ep_at ptr) (ep_at' ptr)
            (set_endpoint ptr e) (setEndpoint ptr e')"
  apply (simp add: set_simple_ko_def setEndpoint_def is_ep_def[symmetric])
    apply (corres_search search: setObject_other_corres[where P="\<lambda>_. True"])
  apply (corressimp wp: get_object_ret get_object_wp)+
  by (fastforce simp: is_ep obj_at_simps objBits_defs partial_inv_def)

lemma setNotification_corres:
  "ntfn_relation ae ae' \<Longrightarrow>
  corres dc (ntfn_at ptr) (ntfn_at' ptr)
            (set_notification ptr ae) (setNotification ptr ae')"
  apply (simp add: set_simple_ko_def setNotification_def is_ntfn_def[symmetric])
       apply (corres_search search: setObject_other_corres[where P="\<lambda>_. True"])
  apply (corressimp wp: get_object_ret get_object_wp)+
  by (fastforce simp: is_ntfn obj_at_simps objBits_defs partial_inv_def)

lemma no_fail_getNotification [wp]:
  "no_fail (ntfn_at' ptr) (getNotification ptr)"
  apply (simp add: getNotification_def getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps' lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply (simp add: word_bits_conv)
  apply (clarsimp split: option.split_asm simp: objBits_simps')
  done

lemma getNotification_corres:
  "corres ntfn_relation (ntfn_at ptr) (ntfn_at' ptr)
     (get_notification ptr) (getNotification ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getNotification_def get_object_def
                   getObject_def bind_assoc)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def)
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ntfn partial_inv_def)
  apply (clarsimp simp: loadObject_default_def in_monad in_magnitude_check objBits_simps')
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

lemma setObject_ko_wp_at:
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes n: "\<And>v' :: 'a. objBits v' = n"
  assumes m: "(1 :: machine_word) < 2 ^ n"
  shows      "\<lbrace>\<lambda>s. obj_at' (\<lambda>x :: 'a. True) p s \<longrightarrow>
                    P (ko_wp_at' (if p = p' then K (P' (injectKO v)) else P')p' s)\<rbrace>
                setObject p v
              \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad
                        ko_wp_at'_def split_def
                        R updateObject_default_def
                        obj_at'_real_def
             split del: if_split)
  apply (clarsimp simp: project_inject objBits_def[symmetric] n
                        in_magnitude_check [OF _ m]
                 elim!: rsubst[where P=P]
             split del: if_split)
  apply (rule iffI)
   apply (clarsimp simp: n ps_clear_upd objBits_def[symmetric]
                  split: if_split_asm)
  apply (clarsimp simp: n project_inject objBits_def[symmetric]
                        ps_clear_upd
                 split: if_split_asm)
  done

lemma typ_at'_valid_obj'_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  notes [wp] = hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_const_Ball_lift typ_at_lifts [OF P]
  shows      "\<lbrace>\<lambda>s. valid_obj' obj s\<rbrace> f \<lbrace>\<lambda>rv s. valid_obj' obj s\<rbrace>"
  apply (cases obj; simp add: valid_obj'_def hoare_TrueI)
     apply (rename_tac endpoint)
     apply (case_tac endpoint; simp add: valid_ep'_def, wp)
    apply (rename_tac notification)
    apply (case_tac "ntfnObj notification";
            simp add: valid_ntfn'_def valid_bound_tcb'_def split: option.splits,
            (wpsimp|rule conjI)+)
   apply (rename_tac tcb)
   apply (case_tac "tcbState tcb";
          simp add: valid_tcb'_def valid_tcb_state'_def split_def valid_bound_ntfn'_def
             split: option.splits,
          wpsimp)
  apply (wpsimp simp: valid_cte'_def)
  done

lemmas setObject_valid_obj = typ_at'_valid_obj'_lift [OF setObject_typ_at']

lemma setObject_valid_objs':
  assumes x: "\<And>x n ko s ko' s'.
       \<lbrakk> (ko', s') \<in> fst (updateObject val ko ptr x n s); P s;
          valid_obj' ko s; lookupAround2 ptr (ksPSpace s) = (Some (x, ko), n) \<rbrakk>
           \<Longrightarrow> valid_obj' ko' s"
  shows "\<lbrace>valid_objs' and P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "\<forall>ko. valid_obj' ko s \<longrightarrow> valid_obj' ko b")
   defer
   apply clarsimp
   apply (erule (1) use_valid [OF _ setObject.typ_at_sc_at'_n_lifts'(3)])
  apply (clarsimp simp: setObject_def split_def in_monad
                        lookupAround2_char1)
  apply (simp add: valid_objs'_def)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (drule(1) x)
    apply (simp add: ranI)
   apply (simp add: prod_eqI lookupAround2_char1)
  apply (clarsimp elim!: ranE split: if_split_asm simp: ranI)
  done

lemma setObject_iflive':
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s x y n. (updateObject v ko ptr y n s)
                   = (updateObject_default v ko ptr y n s)"
  assumes n: "\<And>x :: 'a. objBits x = n"
  assumes m: "(1 :: machine_word) < 2 ^ n"
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); P s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> (live' (injectKO v) \<longrightarrow> ex_nonz_cap_to' ptr s) \<and> P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding if_live_then_nonz_cap'_def ex_nonz_cap_to'_def
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (rule setObject_ko_wp_at [OF R])
   apply (rule hoare_vcg_ex_lift)
   apply (rule setObject_cte_wp_at'[where Q = P, OF x y])
      apply assumption+
  apply clarsimp
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma setObject_qs[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_qsL1[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_qsL2[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_ifunsafe':
  fixes v :: "'a :: pspace_storable"
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); P s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  assumes z: "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQNode (ksInterruptState s))\<rbrace>
                     setObject ptr v \<lbrace>\<lambda>rv s. P (intStateIRQNode (ksInterruptState s))\<rbrace>"
  shows      "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp only: if_unsafe_then_cap'_def ex_cte_cap_to'_def
                    cte_wp_at_ctes_of)
  apply (rule hoare_use_eq_irq_node' [OF z])
  apply (rule setObject_ctes_of [OF x y], assumption+)
  done

lemma setObject_it[wp]:
  assumes x: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

\<comment>\<open>
  `idle_tcb_ps val` asserts that `val` is a pspace_storable value
  which corresponds to an idle TCB.
\<close>
definition idle_tcb_ps :: "('a :: pspace_storable) \<Rightarrow> bool" where
  "idle_tcb_ps val \<equiv> (\<exists>tcb. projectKO_opt (injectKO val) = Some tcb \<and> idle_tcb' tcb)"

lemma setObject_idle':
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko ptr y n s)
                   = (updateObject_default v ko ptr y n s)"
  assumes n: "\<And>x :: 'a. objBits x = n"
  assumes m: "(1 :: machine_word) < 2 ^ n"
  assumes z: "\<And>P p q n ko.
       \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> updateObject v p q n ko
       \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_idle' s \<and>
                   (ptr = ksIdleThread s
                        \<longrightarrow> (\<exists>val :: 'a. idle_tcb_ps val)
                        \<longrightarrow> idle_tcb_ps v)\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. valid_idle' s\<rbrace>"
  apply (simp add: valid_idle'_def pred_tcb_at'_def o_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf2 [where f="ksIdleThread"])
    apply (simp add: pred_tcb_at'_def obj_at'_real_def)
    apply (rule setObject_ko_wp_at [OF R n m])
   apply (wp z)
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def idle_tcb_ps_def)
  apply (clarsimp simp add: project_inject)
  done

lemma setObject_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> setObject p v \<lbrace>\<lambda>r. no_0_obj'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def no_0_obj'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd)
  done

lemma valid_updateCapDataI:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  apply (unfold updateCapData_def Let_def RISCV64_H.updateCapData_def)
  apply (cases c)
  apply (simp_all add: isCap_defs valid_cap'_def capUntypedPtr_def isCap_simps
                       capAligned_def word_size word_bits_def word_bw_assocs
                split: arch_capability.splits capability.splits)
  done

lemma no_fail_threadGet [wp]:
  "no_fail (tcb_at' t) (threadGet f t)"
  by (simp add: threadGet_def, wp)

lemma no_fail_getThreadState [wp]:
  "no_fail (tcb_at' t) (getThreadState t)"
  by (simp add: getThreadState_def, wp)

lemma no_fail_setObject_tcb [wp]:
  "no_fail (tcb_at' t) (setObject t (t'::tcb))"
  apply (rule no_fail_pre, wp)
   apply (rule ext)+
   apply simp
  apply (simp add: objBits_simps)
  done

lemma no_fail_threadSet [wp]:
  "no_fail (tcb_at' t) (threadSet f t)"
  apply (simp add: threadSet_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma dmo_return' [simp]:
  "doMachineOp (return x) = return x"
  apply (simp add: doMachineOp_def select_f_def return_def gets_def get_def
                   bind_def modify_def put_def)
  done

lemma dmo_storeWordVM' [simp]:
  "doMachineOp (storeWordVM x y) = return ()"
  by (simp add: storeWordVM_def)

declare mapM_x_return [simp]

lemma no_fail_dmo' [wp]:
  "no_fail P f \<Longrightarrow> no_fail (P o ksMachineState) (doMachineOp f)"
  apply (simp add: doMachineOp_def split_def)
  apply (rule no_fail_pre, wp)
  apply simp
  apply (simp add: no_fail_def)
  done

lemma setEndpoint_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setEndpoint val ptr
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setEndpoint_def)
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setNotification_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setNotification val ptr
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setNotification_def)
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma set_ep_valid_objs':
  "\<lbrace>valid_objs' and valid_ep' ep\<rbrace>
  setEndpoint epptr ep
  \<lbrace>\<lambda>r s. valid_objs' s\<rbrace>"
  apply (simp add: setEndpoint_def)
  apply (rule setObject_valid_objs')
  apply (clarsimp simp: updateObject_default_def in_monad valid_obj'_def)
  done

lemma set_ep_ctes_of[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> setEndpoint p val \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: setEndpoint_def)
  apply (rule setObject_ctes_of[where Q="\<top>", simplified])
   apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: updateObject_default_def bind_def)
  done

lemma set_ep_valid_mdb' [wp]:
  "\<lbrace>valid_mdb'\<rbrace>
     setObject epptr (ep::endpoint)
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def)
  apply (rule set_ep_ctes_of[simplified setEndpoint_def])
  done

lemma setEndpoint_valid_mdb':
  "\<lbrace>valid_mdb'\<rbrace> setEndpoint p v \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  unfolding setEndpoint_def
  by (rule set_ep_valid_mdb')

lemma set_ep_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and valid_ep' ep\<rbrace>
  setEndpoint epptr ep
  \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp set_ep_aligned' [simplified] set_ep_valid_objs')
   apply (wp hoare_vcg_conj_lift)
    apply (simp add: setEndpoint_def)
    apply (wp setEndpoint_valid_mdb')+
  apply auto
  done

lemma set_ep_valid_bitmapQ[wp]:
  "\<lbrace>Invariants_H.valid_bitmapQ\<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>rv. Invariants_H.valid_bitmapQ\<rbrace>"
  apply (unfold setEndpoint_def)
  apply (rule setObject_ep_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma set_ep_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  apply (unfold setEndpoint_def)
  apply (rule setObject_ep_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma set_ep_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  apply (unfold setEndpoint_def)
  apply (rule setObject_ep_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp add: bitmapQ_def)+
  done

lemma set_ep_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: Invariants_H.valid_queues_def)
  apply (wp hoare_vcg_conj_lift)
    apply (simp add: setEndpoint_def valid_queues_no_bitmap_def)
    apply (wp hoare_Ball_helper hoare_vcg_all_lift)
      apply (rule obj_at_setObject2)
      apply (clarsimp simp: updateObject_default_def in_monad)
     apply (wp updateObject_default_inv set_ep_valid_bitmapQ[unfolded setEndpoint_def]
            | simp add: valid_queues_no_bitmap_def)+
  done

lemma set_ep_valid_queues'[wp]:
  "\<lbrace>valid_queues'\<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (unfold setEndpoint_def)
  apply (simp only: valid_queues'_def imp_conv_disj
                    obj_at'_real_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (rule setObject_ko_wp_at)
      apply simp
     apply (simp add: objBits_simps')
    apply simp
   apply (wp updateObject_default_inv | simp)+
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma ct_in_state_thread_state_lift':
  assumes ct: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes st: "\<And>t. \<lbrace>st_tcb_at' P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  shows "\<lbrace>ct_in_state' P\<rbrace> f \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def)
  apply (clarsimp simp: valid_def)
  apply (frule (1) use_valid [OF _ ct])
  apply (drule (1) use_valid [OF _ st], assumption)
  done

lemma sch_act_wf_lift:
  assumes tcb: "\<And>P t. \<lbrace>st_tcb_at' P t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes tcb_cd: "\<And>t. \<lbrace> tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>_ . tcb_in_cur_domain' t \<rbrace>"
  assumes kCT: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes ksA: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  f
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule (1) use_valid [OF _ ksA])
  apply (case_tac "ksSchedulerAction b", simp_all)
  apply (drule (2) use_valid [OF _ ct_in_state_thread_state_lift' [OF kCT tcb]])
  apply (clarsimp)
  apply (rule conjI)
  apply (drule (2) use_valid [OF _ tcb])
  apply (drule (2) use_valid [OF _ tcb_cd])
  done

lemma tcb_in_cur_domain'_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes b: "\<And>x. \<lbrace>obj_at' (\<lambda>tcb. x = tcbDomain tcb) t\<rbrace> f \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. x = tcbDomain tcb) t\<rbrace>"
  shows "\<lbrace> tcb_in_cur_domain' t \<rbrace> f \<lbrace> \<lambda>_. tcb_in_cur_domain' t \<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule_tac f="ksCurDomain" in  hoare_lift_Pf)
   apply (rule b)
  apply (rule a)
  done

lemma ct_idle_or_in_cur_domain'_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes e: "\<And>d t t'. \<lbrace>\<lambda>s. t = t' \<or> obj_at' (\<lambda>tcb. d = tcbDomain tcb) t s\<rbrace>
                            f
                       \<lbrace>\<lambda>_ s. t = t' \<or> obj_at' (\<lambda>tcb. d = tcbDomain tcb) t s\<rbrace>"
  shows "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> f \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (rule_tac f="ksCurThread" in  hoare_lift_Pf)
   apply (rule_tac f="ksIdleThread" in hoare_lift_Pf)
    apply (rule_tac f="ksSchedulerAction" in  hoare_lift_Pf)
     apply (rule_tac f="ksCurDomain" in  hoare_lift_Pf)
      apply (wp hoare_vcg_imp_lift)
       apply (rule e)
      apply simp
     apply (rule a)
    apply (rule b)
   apply (rule c)
  apply (rule d)
  done


lemma setObject_ep_obj_at'_tcb[wp]:
  "\<lbrace>obj_at' (P :: tcb \<Rightarrow> bool) t \<rbrace> setObject ptr (e::endpoint) \<lbrace>\<lambda>_. obj_at' (P :: tcb \<Rightarrow> bool) t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setObject_ep_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject ptr (e::endpoint) \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setEndpoint_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setEndpoint epptr ep \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  apply (clarsimp simp: setEndpoint_def)
  apply (rule tcb_in_cur_domain'_lift; wp)
  done

lemma setEndpoint_obj_at'_tcb[wp]:
  "\<lbrace>obj_at' (P :: tcb \<Rightarrow> bool) t \<rbrace> setEndpoint ptr (e::endpoint) \<lbrace>\<lambda>_. obj_at' (P :: tcb \<Rightarrow> bool) t\<rbrace>"
  by (clarsimp simp: setEndpoint_def, wp)

lemma set_ep_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setEndpoint epptr ep
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp sch_act_wf_lift)
    apply (simp add: setEndpoint_def split_def setObject_def
              | wp updateObject_default_inv)+
  done

lemma setObject_state_refs_of':
  assumes x: "updateObject val = updateObject_default val"
  assumes y: "(1 :: machine_word) < 2 ^ objBits val"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def x in_magnitude_check y
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (clarsimp simp: state_refs_of'_def objBits_def[symmetric]
                        ps_clear_upd
                  cong: if_cong option.case_cong)
  done

lemma setObject_state_refs_of_eq:
  assumes x: "\<And>s s' obj obj' ptr' ptr''.
                  (obj', s') \<in> fst (updateObject val obj ptr ptr' ptr'' s)
                    \<Longrightarrow> refs_of' obj' = refs_of' obj"
  shows
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def in_magnitude_check lookupAround2_char1
                 elim!: rsubst[where P=P]
                intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (frule x, drule updateObject_objBitsKO)
  apply (simp add: state_refs_of'_def ps_clear_upd
             cong: option.case_cong if_cong)
  done

lemma set_ep_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (epptr := ep_q_refs_of' ep))\<rbrace>
     setEndpoint epptr ep
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding setEndpoint_def
  by (wp setObject_state_refs_of',
      simp_all add: objBits_simps' fun_upd_def[symmetric])

lemma set_ntfn_ctes_of[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> setNotification p val \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: setNotification_def)
  apply (rule setObject_ctes_of[where Q="\<top>", simplified])
   apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: updateObject_default_def bind_def)
  done

lemma set_ntfn_valid_mdb' [wp]:
  "\<lbrace>valid_mdb'\<rbrace>
    setObject epptr (ntfn::Structures_H.notification)
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def)
  apply (rule set_ntfn_ctes_of[simplified setNotification_def])
  done

lemma set_ntfn_valid_objs':
  "\<lbrace>valid_objs' and valid_ntfn' ntfn\<rbrace>
    setNotification p ntfn
   \<lbrace>\<lambda>r s. valid_objs' s\<rbrace>"
  apply (simp add: setNotification_def)
  apply (rule setObject_valid_objs')
  apply (clarsimp simp: updateObject_default_def in_monad
                        valid_obj'_def)
  done

lemma set_ntfn_valid_pspace'[wp]:
  "\<lbrace>valid_pspace' and valid_ntfn' ntfn\<rbrace>
    setNotification p ntfn
   \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp set_ntfn_aligned' [simplified] set_ntfn_valid_objs')
      apply (simp add: setNotification_def,wp)
     apply auto
  done

lemma set_ntfn_valid_bitmapQ[wp]:
  "\<lbrace>Invariants_H.valid_bitmapQ\<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. Invariants_H.valid_bitmapQ\<rbrace>"
  apply (unfold setNotification_def)
  apply (rule setObject_ntfn_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp)+
  done

lemma set_ntfn_bitmapQ_no_L1_orphans[wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. bitmapQ_no_L1_orphans \<rbrace>"
  apply (unfold setNotification_def)
  apply (rule setObject_ntfn_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp)+
  done

lemma set_ntfn_bitmapQ_no_L2_orphans[wp]:
  "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. bitmapQ_no_L2_orphans \<rbrace>"
  apply (unfold setNotification_def)
  apply (rule setObject_ntfn_pre)
  apply (simp add: bitmapQ_defs setObject_def split_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift updateObject_default_inv | simp)+
  done

lemma set_ntfn_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: Invariants_H.valid_queues_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_conj_lift)
    apply (simp add: setNotification_def valid_queues_no_bitmap_def)
    apply (wp hoare_Ball_helper hoare_vcg_all_lift)
      apply (rule obj_at_setObject2)
      apply (clarsimp simp: updateObject_default_def in_monad)
     apply (wp updateObject_default_inv set_ep_valid_bitmapQ[unfolded setEndpoint_def]
            | simp add: valid_queues_no_bitmap_def)+
  done

lemma set_ntfn_valid_queues'[wp]:
  "\<lbrace>valid_queues'\<rbrace> setNotification p ntfn \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (unfold setNotification_def)
  apply (rule setObject_ntfn_pre)
  apply (simp only: valid_queues'_def imp_conv_disj
                    obj_at'_real_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (rule setObject_ko_wp_at)
      apply simp
     apply (simp add: objBits_simps')
    apply simp
   apply (wp updateObject_default_inv | simp)+
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma set_ntfn_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (epptr := ntfn_q_refs_of' (ntfnObj ntfn)
                                      \<union> ntfn_bound_refs' (ntfnBoundTCB ntfn)))\<rbrace>
     setNotification epptr ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding setNotification_def
  by (wp setObject_state_refs_of',
      simp_all add: objBits_simps' fun_upd_def)

lemma setNotification_pred_tcb_at'[wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def setNotification_def)
  apply (rule obj_at_setObject2)
   apply simp
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setObject_ntfn_cur_domain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> setObject ptr (ntfn::Structures_H.notification) \<lbrace> \<lambda>_s . P (ksCurDomain s) \<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ntfn_obj_at'_tcb[wp]:
  "\<lbrace>obj_at' (P :: tcb \<Rightarrow> bool) t \<rbrace> setObject ptr (ntfn::Structures_H.notification) \<lbrace>\<lambda>_. obj_at' (P :: tcb \<Rightarrow> bool) t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setNotification_ksCurDomain[wp]:
  "\<lbrace> \<lambda>s. P (ksCurDomain s) \<rbrace> setNotification ptr (ntfn::Structures_H.notification) \<lbrace> \<lambda>_s . P (ksCurDomain s) \<rbrace>"
   apply (simp add: setNotification_def)
   apply wp
   done

lemma setNotification_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setNotification epptr ep \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  apply (clarsimp simp: setNotification_def)
  apply (rule tcb_in_cur_domain'_lift; wp)
  done

lemma set_ntfn_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setNotification ntfnptr ntfn
   \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp sch_act_wf_lift | clarsimp simp: setNotification_def)+
    apply (simp add: setNotification_def split_def setObject_def
         | wp updateObject_default_inv)+
  done

lemmas cur_tcb_lift =
  hoare_lift_Pf [where f = ksCurThread and P = tcb_at', folded cur_tcb'_def]

lemma set_ntfn_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setNotification ptr ntfn \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  apply (wp cur_tcb_lift)
  apply (simp add: setNotification_def setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setEndpoint_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  unfolding setEndpoint_def
  by (rule setObject_typ_at')

lemmas setEndpoint_typ_ats[wp] = typ_at_lifts [OF setEndpoint_typ_at']

lemma get_ep_sp':
  "\<lbrace>P\<rbrace> getEndpoint r \<lbrace>\<lambda>t. P and ko_at' t r\<rbrace>"
  by (clarsimp simp: getEndpoint_def getObject_def loadObject_default_def
                     in_monad valid_def obj_at'_def objBits_simps' in_magnitude_check split_def)

lemma setEndpoint_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setEndpoint p v \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  apply (wp cur_tcb_lift)
  apply (simp add: setEndpoint_def setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setEndpoint_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (v \<noteq> IdleEP \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
     setEndpoint p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setEndpoint_def
  apply (wp setObject_iflive'[where P="\<top>"])
       apply simp
      apply (simp add: objBits_simps')
     apply simp
    apply (clarsimp simp: updateObject_default_def in_monad)
   apply (clarsimp simp: updateObject_default_def in_monad bind_def)
  apply clarsimp
  done

declare setEndpoint_cte_wp_at'[wp]

lemma ex_nonz_cap_to_pres':
  assumes y: "\<And>P p. \<lbrace>cte_wp_at' P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  shows      "\<lbrace>ex_nonz_cap_to' p\<rbrace> f \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp only: ex_nonz_cap_to'_def)
  apply (intro hoare_vcg_disj_lift hoare_vcg_ex_lift
               y hoare_vcg_all_lift)
  done

lemma setEndpoint_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setEndpoint p' v \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma setEndpoint_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setEndpoint p v \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding setEndpoint_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: updateObject_default_def in_monad
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setEndpoint_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s\<rbrace>
   setEndpoint p v
   \<lbrace>\<lambda>_. valid_idle'\<rbrace>"
  unfolding setEndpoint_def
  apply (wp setObject_idle')
       apply (simp add: objBits_simps' updateObject_default_inv idle_tcb_ps_def)+
  done

crunch it[wp]: setEndpoint "\<lambda>s. P (ksIdleThread s)"
  (simp: updateObject_default_inv)

lemma setObject_ksPSpace_only:
  "\<lbrakk> \<And>p q n ko. \<lbrace>P\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv. P \<rbrace>;
        \<And>f s. P (ksPSpace_update f s) = P s \<rbrakk>
     \<Longrightarrow> \<lbrace>P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp | assumption)+
  done

lemma setObject_ksMachine:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)

lemma setObject_ksInterrupt:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)

lemma valid_irq_handlers_lift':
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  shows      "\<lbrace>valid_irq_handlers'\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def irq_issued'_def)
  apply (rule hoare_use_eq [where f=cteCaps_of, OF x y])
  done

lemmas valid_irq_handlers_lift'' = valid_irq_handlers_lift' [unfolded cteCaps_of_def]

lemma valid_global_refs_lift':
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes irqn: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  assumes maxObj: "\<And>P. \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> f \<lbrace>\<lambda>_ s. P (gsMaxObjectSize s)\<rbrace>"
  shows "\<lbrace>valid_global_refs'\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def global_refs'_def valid_cap_sizes'_def)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (rule hoare_lift_Pf [where f="ksIdleThread"])
    apply (rule hoare_lift_Pf [where f="irq_node'"])
     apply (rule hoare_lift_Pf [where f="gsMaxObjectSize"])
      apply (wp ctes hoare_vcg_const_Ball_lift arch idle irqn maxObj)+
  done

lemma valid_arch_state_lift':
  assumes typs: "\<And>T p P. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def valid_global_pts'_def
                   vspace_table_at'_defs)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (wp typs hoare_vcg_all_lift hoare_vcg_ball_lift arch typ_at_lifts)+
  done

lemma setObject_ep_ct:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::endpoint) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_ep_eta split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ntfn_ct:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::Structures_H.notification)
   \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma get_ntfn_sp':
  "\<lbrace>P\<rbrace> getNotification r \<lbrace>\<lambda>t. P and ko_at' t r\<rbrace>"
  by (clarsimp simp: getNotification_def getObject_def loadObject_default_def
                     in_monad valid_def obj_at'_def objBits_simps' in_magnitude_check split_def)

lemma set_ntfn_pred_tcb_at' [wp]:
  "\<lbrace> pred_tcb_at' proj P t \<rbrace>
   setNotification ep v
   \<lbrace> \<lambda>rv. pred_tcb_at' proj P t \<rbrace>"
  apply (simp add: setNotification_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma set_ntfn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (live' (KONotification v) \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
     setNotification p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setNotification_def)
  apply (wp setObject_iflive'[where P="\<top>"])
       apply simp
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps')
    apply (clarsimp simp: updateObject_default_def in_monad)
   apply (clarsimp simp: updateObject_default_def bind_def)
  apply clarsimp
  done

declare setNotification_cte_wp_at'[wp]

lemma set_ntfn_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setNotification p' v \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma setNotification_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setNotification p v \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  unfolding setNotification_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: updateObject_default_def in_monad
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setNotification_idle'[wp]:
  "\<lbrace>\<lambda>s. valid_idle' s\<rbrace> setNotification p v \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding setNotification_def
  apply (wp setObject_idle')
        apply (simp add: objBits_simps' updateObject_default_inv idle_tcb_ps_def)+
  done

crunch it[wp]: setNotification "\<lambda>s. P (ksIdleThread s)"
  (wp: updateObject_default_inv)

lemma set_ntfn_arch' [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setNotification ntfn p \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (simp add: setNotification_def setObject_def split_def)
  apply (wp updateObject_default_inv|simp)+
  done

lemma set_ntfn_ksInterrupt[wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  by (simp add: setNotification_def | wp setObject_ksInterrupt updateObject_default_inv)+

lemma set_ntfn_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (simp add: setNotification_def | wp setObject_ksMachine updateObject_default_inv)+

lemma set_ntfn_maxObj [wp]:
  "\<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv s. P (gsMaxObjectSize s)\<rbrace>"
  by (simp add: setNotification_def | wp setObject_ksPSpace_only updateObject_default_inv)+

lemma set_ntfn_global_refs' [wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setNotification ptr val \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

crunch typ_at' [wp]: setNotification "\<lambda>s. P (typ_at' T p s)" (ignore_del: setObject)

lemma set_ntfn_valid_arch' [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setNotification ptr val \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemmas valid_irq_node_lift =
    hoare_use_eq_irq_node' [OF _ typ_at_lift_valid_irq_node']

lemmas untyped_ranges_zero_lift
    = hoare_use_eq[where f="gsUntypedZeroRanges"
        and Q="\<lambda>v s. untyped_ranges_zero_inv (f s) v" for f]

lemma valid_irq_states_lift':
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s))\<rbrace> f \<lbrace>\<lambda>rv s. P (intStateIRQTable (ksInterruptState s))\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks (ksMachineState s))\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_masks (ksMachineState s))\<rbrace>"
  shows      "\<lbrace>valid_irq_states'\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (rule hoare_use_eq [where f="\<lambda>s. irq_masks (ksMachineState s)"], rule y)
  apply (rule hoare_use_eq [where f="\<lambda>s. intStateIRQTable (ksInterruptState s)"], rule x)
  apply wp
  done

lemmas set_ntfn_irq_handlers'[wp] = valid_irq_handlers_lift'' [OF set_ntfn_ctes_of set_ntfn_ksInterrupt]

lemmas set_ntfn_irq_states' [wp] = valid_irq_states_lift' [OF set_ntfn_ksInterrupt set_ntfn_ksMachine]

lemma set_ntfn_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: setNotification_def valid_machine_state'_def pointerInDeviceData_def pointerInUserData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
  by (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv |
      simp)+

lemma irqs_masked_lift:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s))\<rbrace> f
               \<lbrace>\<lambda>rv s. P (intStateIRQTable (ksInterruptState s))\<rbrace>"
  shows "\<lbrace>irqs_masked'\<rbrace> f \<lbrace>\<lambda>_. irqs_masked'\<rbrace>"
  apply (simp add: irqs_masked'_def)
  apply (wp assms)
  done

lemma setObject_pspace_domain_valid[wp]:
  "setObject ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  by (clarsimp simp: setObject_def split_def pspace_domain_valid_def valid_def
                      in_monad lookupAround2_char1 updateObject_size
              split: if_split_asm)

lemma ct_not_inQ_lift:
  assumes sch_act: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
      and not_inQ: "\<lbrace>\<lambda>s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
                    f \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  shows "\<lbrace>ct_not_inQ\<rbrace> f \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  unfolding ct_not_inQ_def
  by (rule hoare_convert_imp [OF sch_act not_inQ])

lemma obj_at'_ignoring_obj:
  "obj_at' (\<lambda>_ :: 'a :: pspace_storable. P) p s = (obj_at' (\<lambda>_ :: 'a. True) p s \<and> P)"
  by (rule iffI; clarsimp simp: obj_at'_def)

lemma forall_ko_at'_equiv_projection:
  "(\<lambda>s. \<forall>ko::'a::pspace_storable. ko_at' ko p s \<longrightarrow> P ko s) =
   (\<lambda>s. obj_at' (\<lambda>_::'a::pspace_storable. True) p s \<longrightarrow> P (the ((ksPSpace s |> projectKO_opt) p)) s)"
  by (fastforce simp: obj_at'_def projectKOs opt_map_red)

end

locale pspace_only' =
  fixes f :: "'a kernel"
  assumes pspace: "(rv, s') \<in> fst (f s) \<Longrightarrow> \<exists>g. s' = ksPSpace_update g s"
begin

lemma it[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  and ct[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  and cur_domain[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
  and ksDomSchedule[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
  and l1Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and l2Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  and gsUserPages[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUserPages s)\<rbrace>"
  and gsCNodes[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsCNodes s)\<rbrace>"
  and gsUntypedZeroRanges[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
  and gsMaxObjectSize[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
  and ksDomScheduleIdx[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  and ksDomainTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomainTime s)\<rbrace>"
  and ksReadyQueues[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>"
  and ksReleaseQueue[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReleaseQueue s)\<rbrace>"
  and ksConsumedTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksConsumedTime s)\<rbrace>"
  and ksCurTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurTime s)\<rbrace>"
  and ksCurSc[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurSc s)\<rbrace>"
  and ksReprogramTimer[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReprogramTimer s)\<rbrace>"
  and ksSchedulerAction[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  and ksInterruptState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
  and ksWorkUnitsCompleted[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksWorkUnitsCompleted s)\<rbrace>"
  and ksArchState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  and ksMachineState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>"
  unfolding valid_def using pspace
  by (all \<open>fastforce\<close>)

lemma sch_act_simple[wp]:
  "f \<lbrace>\<lambda>s. P (sch_act_simple s)\<rbrace>"
  apply (wpsimp wp: ksSchedulerAction simp: sch_act_simple_def)
  done

end

locale simple_ko' =
  fixes f :: "obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
    and g :: "obj_ref \<Rightarrow> 'a kernel"
  assumes f_def: "f p v = setObject p v"
  assumes g_def: "g p = getObject p"
  assumes default_update: "updateObject (v::'a) = updateObject_default (v::'a)"
  assumes default_load: "(loadObject ptr ptr' next obj :: 'a kernel_r) =
                              loadObject_default ptr ptr' next obj"
  assumes not_cte: "projectKO_opt (KOCTE cte) = (None::'a option)"
begin

lemma updateObject_cte[simp]:
  "fst (updateObject (v::'a) (KOCTE cte) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_cte bind_def)

lemma pspace_aligned'[wp]: "f p v \<lbrace>pspace_aligned'\<rbrace>"
  and pspace_distinct'[wp]: "f p v \<lbrace>pspace_distinct'\<rbrace>"
  and pspace_bounded'[wp]: "f p v \<lbrace>pspace_bounded'\<rbrace>"
  and no_0_obj'[wp]: "f p v \<lbrace>no_0_obj'\<rbrace>"
  unfolding f_def by (all \<open>wpsimp simp: default_update updateObject_default_def in_monad\<close>)

lemma valid_objs':
  "\<lbrace>valid_objs' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding f_def
  by (rule setObject_valid_objs')
     (clarsimp simp: default_update updateObject_default_def in_monad projectKOs)+

lemma typ_at'[wp]:
  "f p v \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
  unfolding f_def
  by (rule setObject_typ_at')

lemma sc_at'_n[wp]: "f p v \<lbrace>\<lambda>s. P (sc_at'_n n p' s)\<rbrace>"
  unfolding f_def
  by (clarsimp simp: valid_def setObject_def in_monad split_def ko_wp_at'_def ps_clear_upd
                     updateObject_size lookupAround2_char1 updateObject_type)

sublocale typ_at_all_props' "f p v" for p v by typ_at_props'

sublocale pspace_only' "f p v" for p v
  unfolding f_def
  by unfold_locales
     (fastforce simp: setObject_def updateObject_default_def magnitudeCheck_def default_update
                      in_monad split_def projectKOs
                split: option.splits)

lemma set_ep_valid_bitmapQ[wp]:
  "f p v \<lbrace> valid_bitmapQ \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma bitmapQ_no_L1_orphans[wp]:
  "f p v \<lbrace> bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma bitmapQ_no_L2_orphans[wp]:
  "f p v \<lbrace> bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma state_refs_of':
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
   f ptr val
   \<lbrace>\<lambda>_ s. P (state_refs_of' s)\<rbrace>"
  unfolding f_def
  by (auto intro: setObject_state_refs_of' simp: default_update)

lemma valid_arch_state'[wp]:
  "f p v \<lbrace> valid_arch_state' \<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemmas valid_irq_node'[wp] = valid_irq_node_lift[OF ksInterruptState typ_at']
lemmas irq_states' [wp] = valid_irq_states_lift' [OF ksInterruptState ksMachineState]
lemmas irqs_masked'[wp] = irqs_masked_lift[OF ksInterruptState]

lemma valid_machine_state'[wp]:
  "f p v \<lbrace>valid_machine_state'\<rbrace>"
  unfolding valid_machine_state'_def pointerInDeviceData_def pointerInUserData_def
  by (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma pspace_domain_valid[wp]:
  "f ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  unfolding f_def by (wpsimp simp: default_update updateObject_default_def in_monad projectKOs)

lemmas x = ct_not_inQ_lift[OF ksSchedulerAction]

lemma setObject_wp:
  "\<lbrace>\<lambda>s. P (set_obj' ptr obj s)\<rbrace>
   setObject ptr (obj :: 'a :: pspace_storable)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp simp: setObject_def default_update updateObject_default_def fun_upd_def
                      ARM_H.fromPPtr_def) (* FIXME: arch split *)
                                          (* FIXME: this is a simp rule, why isn't it available? *)
  done

lemmas set_wp = setObject_wp[folded f_def]

\<comment>\<open>
  Keeps the redundant @{term "obj_at \<top>"} precondition because this matches common abbreviations
  like @{term "tcb_at'"}.
\<close>
lemma setObject_pre:
  fixes obj :: 'a
  assumes "\<lbrace>P and obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) p
              and obj_at' (\<lambda>_ :: 'a. True) p\<rbrace>
           setObject p obj
           \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p obj \<lbrace>Q\<rbrace>"
  supply simps = in_magnitude_check[OF _, unfolded objBits_def] valid_def
                 setObject_def in_monad split_def default_update updateObject_default_def
                 projectKO_eq2 project_inject objBits_def
                 ARM_H.fromPPtr_def (* FIXME: arch split *)
  using assms
  apply (clarsimp simp: simps)
  apply (rename_tac s ko)
  apply (drule_tac x=s in spec)
  apply (clarsimp simp: obj_at'_def projectKO_eq split_paired_Ball project_inject)
  apply (erule impE)
   apply fastforce
  apply (drule spec, erule mp)
  apply (fastforce simp: simps)
  done

\<comment>\<open>
  Keeps the redundant @{term "obj_at \<top>"} precondition because this matches common abbreviations
  like @{term "tcb_at'"}.

  Lets the postcondition pointer depend on the state for things like @{term "ksCurThread"}.
\<close>
lemma setObject_obj_at'_strongest:
  fixes obj :: 'a
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) ptr s
              \<and> obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) ptr s
              \<longrightarrow> (let s' = set_obj' ptr obj s in
                    Q ((ptr = ptr' s' \<longrightarrow> P s' obj)
                       \<and> (ptr \<noteq> ptr' s' \<longrightarrow> obj_at' (P s') (ptr' s') s)))\<rbrace>
         setObject ptr obj
         \<lbrace>\<lambda>rv s. Q (obj_at' (P s) (ptr' s) s)\<rbrace>"
  apply (rule setObject_pre)
  apply (wpsimp wp: setObject_wp
              simp: Let_def)
  apply (erule rsubst[where P=Q])
  apply (case_tac "ptr = ptr' (set_obj' ptr obj s)"; simp)
   apply (clarsimp simp: same_size_obj_at'_set_obj'_iff
                         obj_at'_ignoring_obj[where P="P f obj" for f])
  apply (clarsimp simp: obj_at'_def projectKO_eq project_inject ps_clear_upd)
  done

lemmas obj_at'_strongest = setObject_obj_at'_strongest[folded f_def]

lemma setObject_obj_at':
  fixes v :: 'a
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) p s \<longrightarrow> P (if p = p' then P' v else obj_at' P' p' s)\<rbrace>
         setObject p v
         \<lbrace>\<lambda>rv s. P (obj_at' P' p' s)\<rbrace>"
  by (wpsimp wp: setObject_obj_at'_strongest split: if_splits)

lemmas obj_at' = setObject_obj_at'[folded f_def]

lemma getObject_wp:
  "\<lbrace>\<lambda>s. \<forall>ko :: 'a. ko_at' ko p s \<longrightarrow> P ko s\<rbrace>
   getObject p
   \<lbrace>P\<rbrace>"
  apply (wpsimp simp: getObject_def default_load ARM_H.fromPPtr_def loadObject_default_def
                      projectKO_def readObject_def omonad_defs split_def)
  apply (rename_tac ko)
  apply (prop_tac "ko_at' ko p s")
   apply (clarsimp simp: obj_at'_def project_inject projectKO_eq objBits_def[symmetric]
                         read_magnitudeCheck_def
                         lookupAround2_no_after_ps_clear
                         lookupAround2_after_ps_clear[OF _ _]
                  split: if_split_asm option.split_asm)
  apply fastforce
  done

lemma getObject_wp':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_::'a. True) p s \<longrightarrow> P (the ((ksPSpace s |> projectKO_opt) p)) s\<rbrace>
   getObject p
   \<lbrace>P::'a \<Rightarrow> _ \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  by (metis forall_ko_at'_equiv_projection)

lemmas get_wp = getObject_wp[folded g_def]
lemmas get_wp' = getObject_wp'[folded g_def]

lemma loadObject_default_inv:
  "\<lbrace>P\<rbrace> gets_the $ loadObject_default addr addr' next obj \<lbrace>\<lambda>rv. P\<rbrace>"
  by wpsimp

lemma getObject_inv:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a). P\<rbrace>"
  by (wpsimp simp: default_load getObject_def split_def wp: loadObject_default_inv)

lemmas get_inv = getObject_inv[folded g_def]

lemma getObject_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>rv::'a. P and ko_at' rv r\<rbrace>"
  apply (clarsimp simp: getObject_def loadObject_default_def default_load
                        projectKOs in_monad valid_def obj_at'_def project_inject
                        split_def ARM_H.fromPPtr_def readObject_def omonad_defs
                 split: if_split_asm option.split_asm)
  by (clarsimp simp: objBits_def)

lemmas getObject_sp' = getObject_sp[folded g_def]

lemma setObject_preserves_some_obj_at':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow> P (obj_at' (\<lambda>_ :: 'a. True) p' s)\<rbrace>
   setObject p (ko :: 'a)
   \<lbrace>\<lambda>_ s. P (obj_at' (\<lambda>_ :: 'a. True) p' s)\<rbrace>"
  apply (wpsimp wp: setObject_obj_at'_strongest)
  apply (case_tac "p = p'"; clarsimp)
  done

lemmas set_preserves_some_obj_at' = setObject_preserves_some_obj_at'[folded f_def]

lemma getObject_wp_rv_only:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) p s \<longrightarrow> obj_at' (\<lambda>ko :: 'a. P ko) p s\<rbrace> getObject p \<lbrace>\<lambda>rv _. P rv\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas get_wp_rv_only = getObject_wp_rv_only[folded g_def]

\<comment>\<open> Stronger than getObject_inv. \<close>
lemma getObject_wp_state_only:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow> P s\<rbrace> getObject p \<lbrace>\<lambda>_ :: 'a. P\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas get_wp_state_only = getObject_wp_state_only[folded g_def]

lemma setObject_no_update:
  assumes [simp]: "\<And>ko :: 'a. Q (upd ko) = Q ko"
  shows
  "\<lbrace>\<lambda>s. P (obj_at' Q p' s) \<and> ko_at' ko p s\<rbrace>
   setObject p (upd ko)
   \<lbrace>\<lambda>_ s. P (obj_at' Q p' s)\<rbrace>"
  apply (wpsimp wp: setObject_obj_at'_strongest)
  apply (case_tac "p = p'"; clarsimp simp: obj_at'_def)
  done

lemmas set_no_update = setObject_no_update[folded f_def]

lemmas getObject_ko_at' = getObject_ko_at[OF default_load]

lemmas get_ko_at' = getObject_ko_at'[folded g_def]

lemmas ko_wp_at = setObject_ko_wp_at[where 'a='a, folded f_def,
                                     simplified default_update, simplified]

lemma setObject_valid_reply':
  "setObject p (ko :: 'a) \<lbrace>valid_reply' reply'\<rbrace>"
  unfolding valid_reply'_def valid_bound_obj'_def
  apply (wpsimp split: option.splits
                   wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply fastforce
  done

lemmas set_valid_reply' = setObject_valid_reply'[folded f_def]

lemma setObject_ko_at':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow>
          (p = p' \<longrightarrow> P (ko = ko')) \<and>
          (p \<noteq> p' \<longrightarrow> P (ko_at' ko' p' s))\<rbrace>
   setObject p (ko :: 'a)
   \<lbrace>\<lambda>_ s. P (ko_at' (ko' :: 'a) p' s)\<rbrace>"
  apply (wpsimp wp: obj_at'_strongest[unfolded f_def])
  apply (case_tac "p = p'"; clarsimp simp: obj_at'_def)
  done

lemmas set_ko_at' = setObject_ko_at'[folded f_def]

end

locale simple_non_tcb_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                       "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_tcb: "projectKO_opt (KOTCB sc) = (None :: 'a option)"
begin

lemma updateObject_tcb[simp]:
  "fst (updateObject (v::'a) (KOTCB tcb) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_tcb bind_def)

lemma not_inject_tcb[simp]:
  "injectKO (v::'a) \<noteq> KOTCB tcb"
  by (simp flip: project_inject add: projectKOs not_tcb)

lemma typeOf_not_tcb[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> TCBT"
  by (cases "injectKO v"; simp)

lemma cte_wp_at'[wp]: "f p v \<lbrace>\<lambda>s. P (cte_wp_at' Q p' s)\<rbrace>"
  unfolding f_def by (rule setObject_cte_wp_at2'[where Q="\<top>", simplified]; simp)

lemma ctes_of[wp]: "f p v \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding f_def by (rule setObject_ctes_of[where Q="\<top>", simplified]; simp)

lemma valid_mdb'[wp]: "f p v \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def by wp

lemma obj_at_tcb'[wp]:
  "f p v \<lbrace>\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) p' s)\<rbrace>"
  unfolding f_def obj_at'_real_def
  apply (wp setObject_ko_wp_at; simp add: default_update)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko; simp add: projectKOs not_tcb)
  done

lemma valid_queues[wp]:
  "f p v \<lbrace> valid_queues \<rbrace>"
  unfolding valid_queues_def valid_queues_no_bitmap_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift |wps)+

lemma valid_inQ_queues[wp]:
  "f p v \<lbrace> valid_inQ_queues \<rbrace>"
  unfolding valid_inQ_queues_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift | wps)+

lemma set_non_tcb_valid_queues'[wp]:
  "f p v \<lbrace>valid_queues'\<rbrace>"
  unfolding valid_queues'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma set_non_tcb_valid_release_queue[wp]:
  "f p v \<lbrace>valid_release_queue\<rbrace>"
  unfolding valid_release_queue_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift | wps)+

lemma set_non_tcb_valid_release_queue'[wp]:
  "f p v \<lbrace>valid_release_queue'\<rbrace>"
  unfolding valid_release_queue'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift | wps)+

lemma tcb_in_cur_domain'[wp]:
  "f p v \<lbrace>tcb_in_cur_domain' t\<rbrace>"
  by (rule tcb_in_cur_domain'_lift; wp)

lemma pred_tcb_at'[wp]:
  "f p v \<lbrace> \<lambda>s. Q (pred_tcb_at' proj P t s) \<rbrace>"
  unfolding pred_tcb_at'_def by wp

lemma sch_act_wf[wp]:
  "f p v \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift)

lemma cur_tcb'[wp]:
  "f p v \<lbrace>cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma cap_to'[wp]:
  "f p' v \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma ifunsafe'[wp]:
  "f p v \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding f_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_tcb
                          not_cte
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def default_update)
  apply (wp updateObject_default_inv | simp)+
  done

lemmas irq_handlers[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]
lemmas irq_handlers'[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]

lemma valid_global_refs'[wp]:
  "f p v \<lbrace>valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

lemma ct_not_inQ[wp]:
  "f p v \<lbrace>ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift, wp)
  apply (rule hoare_lift_Pf[where f=ksCurThread]; wp)
  done

lemma ct_idle_or_in_cur_domain'[wp]:
  "f p v \<lbrace> ct_idle_or_in_cur_domain' \<rbrace>"
  by (rule ct_idle_or_in_cur_domain'_lift; wp)

lemma untyped_ranges_zero'[wp]:
  "f p ko \<lbrace>untyped_ranges_zero'\<rbrace>"
  unfolding cteCaps_of_def o_def
  apply (wpsimp wp: untyped_ranges_zero_lift)
  done

end

locale simple_non_reply_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                         "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_reply: "projectKO_opt (KOReply reply) = (None :: 'a option)"
begin

lemma updateObject_reply[simp]:
  "fst (updateObject (v::'a) (KOReply c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_reply bind_def)

lemma not_inject_reply[simp]:
  "injectKO (v::'a) \<noteq> KOReply sc"
  by (simp flip: project_inject add: projectKOs not_reply)

lemma typeOf_not_reply[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> ReplyT"
  by (cases "injectKO v"; simp)

end

locale simple_non_tcb_non_reply_ko' =
   simple_non_reply_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                        "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g
begin

\<comment>\<open>
  preservation of valid_replies' requires us to not be touching either of a Reply or a TCB
\<close>

lemma valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned'\<rbrace>
   f p v
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
   (is "\<lbrace>?pre valid_replies'\<rbrace> _ \<lbrace>?post\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre valid_replies'_alt" in hoare_post_imp;
         clarsimp simp: valid_replies'_def2)
  unfolding obj_at'_real_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift ko_wp_at hoare_vcg_ex_lift)
  by (fastforce simp: valid_replies'_def2 obj_at'_def ko_wp_at'_def projectKOs)

lemma valid_pspace':
  "\<lbrace>valid_pspace' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def by (wpsimp wp: valid_objs')

end

locale simple_non_sc_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_sc: "projectKO_opt (KOSchedContext sc) = (None :: 'a option)"
begin

lemma updateObject_sc[simp]:
  "fst (updateObject (v::'a) (KOSchedContext c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_sc bind_def)

lemma not_inject_sc[simp]:
  "injectKO (v::'a) \<noteq> KOSchedContext sc"
  by (simp flip: project_inject add: projectKOs not_sc)

lemma typeOf_not_sc[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> SchedContextT"
  by (cases "injectKO v"; simp)

end

locale simple_non_tcb_non_sc_ko' =
   simple_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                     "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g
begin

\<comment>\<open>
  preservation of valid_idle' requires us to not be touching either of an SC or a TCB
\<close>

lemma idle'[wp]:
  "f p v \<lbrace>valid_idle'\<rbrace>"
  unfolding f_def
  apply (wp setObject_idle'
         ; simp add: default_update updateObject_default_inv idle_tcb_ps_def idle_sc_ps_def)
  apply (clarsimp simp: projectKOs)
  done

end

locale simple_non_tcb_non_sc_non_reply_ko' =
   simple_non_tcb_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_non_reply_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" for f g

(* FIXME: should these be in Arch + sublocale instead? *)
interpretation set_ep': simple_non_tcb_non_sc_non_reply_ko' setEndpoint getEndpoint
  by unfold_locales (simp_all add: setEndpoint_def getEndpoint_def projectKO_opts_defs
                                   objBits_simps')

interpretation set_ntfn': simple_non_tcb_non_sc_non_reply_ko' setNotification getNotification
  by unfold_locales (simp_all add: setNotification_def getNotification_def projectKO_opts_defs
                                   objBits_simps')

interpretation set_reply': simple_non_tcb_non_sc_ko' setReply getReply
  by unfold_locales (simp_all add: setReply_def getReply_def projectKO_opts_defs objBits_simps')

interpretation set_sc': simple_non_tcb_non_reply_ko' setSchedContext getSchedContext
  by unfold_locales (simp_all add: setSchedContext_def getSchedContext_def projectKO_opts_defs
                                   objBits_simps' scBits_pos_power2)

interpretation set_tcb': simple_non_sc_ko' "\<lambda>p v. setObject p (v::tcb)"
                                           "\<lambda>p. getObject p :: tcb kernel"
  by unfold_locales (simp_all add: projectKO_opts_defs objBits_simps')

interpretation threadSet: pspace_only' "threadSet f p"
  unfolding threadSet_def
  apply unfold_locales
  apply (clarsimp simp: in_monad)
  apply (drule_tac P="(=) s" in use_valid[OF _ getObject_tcb_inv], rule refl)
  apply (fastforce dest: set_tcb'.pspace)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

(* aliases for compatibility with master *)

lemmas setObject_ep_pre = set_ep'.setObject_pre
lemmas setObject_ntfn_pre = set_ntfn'.setObject_pre
lemmas setObject_tcb_pre = set_tcb'.setObject_pre
lemmas setObject_reply_pre = set_reply'.setObject_pre
lemmas setObject_sched_context_pre = set_sc'.setObject_pre

lemmas getEndpoint_wp = set_ep'.get_wp
lemmas getNotification_wp = set_ntfn'.get_wp
lemmas getTCB_wp = set_tcb'.get_wp
lemmas getReply_wp[wp] = set_reply'.get_wp
lemmas getSchedContext_wp[wp] = set_sc'.get_wp

lemmas getEndpoint_wp' = set_ep'.get_wp'
lemmas getNotification_wp' = set_ntfn'.get_wp'
lemmas getTCB_wp' = set_tcb'.get_wp'
lemmas getReply_wp' = set_reply'.get_wp'
lemmas getSchedContext_wp' = set_sc'.get_wp'

lemmas getObject_ep_inv = set_ep'.getObject_inv
lemmas getObject_ntfn_inv = set_ntfn'.getObject_inv
lemmas getObject_reply_inv = set_reply'.getObject_inv
lemmas getObject_sc_inv = set_sc'.getObject_inv
(* FIXME RT: the one below is deferred because it requires to
   move the simple_ko' locale at the beginning of this theory
   which turns out to be quite a lot more work *)
(*lemmas getObject_tcb_inv = set_tcb'.getObject_inv*)

lemmas get_ep_inv'[wp] = set_ep'.get_inv
lemmas get_ntfn_inv'[wp] = set_ntfn'.get_inv
lemmas get_tcb_inv' = set_tcb'.get_inv
lemmas get_reply_inv' = set_reply'.get_inv
lemmas get_sc_inv' = set_sc'.get_inv

lemmas get_ep_sp' = set_ep'.getObject_sp'
lemmas get_ntfn_sp' = set_ntfn'.getObject_sp'
lemmas get_tcb_sp' = set_tcb'.getObject_sp'
lemmas get_reply_sp' = set_reply'.getObject_sp'
lemmas get_sc_sp' = set_sc'.getObject_sp'

lemmas setObject_tcb_wp = set_tcb'.setObject_wp
lemmas setObject_sc_wp = set_sc'.setObject_wp
lemmas setObject_tcb_obj_at'_strongest = set_tcb'.setObject_obj_at'_strongest

lemmas set_ep_valid_objs'[wp] =
  set_ep'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_ep_valid_pspace'[wp] =
  set_ep'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_ntfn_valid_objs'[wp] =
  set_ntfn'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_ntfn_valid_pspace'[wp] =
  set_ntfn'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_reply_valid_objs'[wp] =
  set_reply'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_sc_valid_objs'[wp] =
  set_sc'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_sc_valid_pspace'[wp] =
  set_sc'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemma set_ep_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (p := ep_q_refs_of' ep))\<rbrace>
     setEndpoint p ep
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_ep'.state_refs_of') (simp flip: fun_upd_def)

lemma set_ntfn_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (p := ntfn_q_refs_of' (ntfnObj ntfn) \<union>
                                    get_refs NTFNBound (ntfnBoundTCB ntfn) \<union>
                                    get_refs NTFNSchedContext (ntfnSc ntfn)))\<rbrace>
     setNotification p ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_ntfn'.state_refs_of') (simp flip: fun_upd_def)

lemma setSchedContext_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs SCNtfn (scNtfn sc) \<union>
                                   get_refs SCTcb (scTCB sc) \<union>
                                   get_refs SCYieldFrom (scYieldFrom sc) \<union>
                                   get_refs SCReply (scReply sc)))\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_sc'.state_refs_of') (simp flip: fun_upd_def)

lemma setReply_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs ReplySchedContext (replySC reply) \<union>
                                   get_refs ReplyTCB (replyTCB reply)))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_reply'.state_refs_of') (simp flip: fun_upd_def)

lemma setReply_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P ((replyNexts_of s)(rptr := replyNext_of reply))
          ((replyPrevs_of s)(rptr := replyPrev reply))
          ((replyTCBs_of s)(rptr := replyTCB reply))
          ((replySCs_of s)(rptr := replySC reply))\<rbrace>
   setReply rptr reply
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  apply (wpsimp simp: setReply_def updateObject_default_def setObject_def split_def)
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def list_refs_of_reply'_def map_set_def projectKO_opt_reply
                    split: option.splits)+
  done

lemma updateReply_wp_all:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko rptr s \<longrightarrow> P (set_obj' rptr (upd ko) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateReply_def
  apply (wpsimp wp: set_reply'.set_wp)
  done

lemma setSchedContext_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and (\<lambda>s. live_sc' sc \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setSchedContext_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad scBits_pos_power2
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setReply_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' p\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setReply_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setEndpoint_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (v \<noteq> IdleEP \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
   setEndpoint p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setEndpoint_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setReply_list_refs_of_replies'[wp]:
  "\<lbrace>\<lambda>s. P ((list_refs_of_replies' s)(p := list_refs_of_reply' reply))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (list_refs_of_replies' s)\<rbrace>"
  apply (wpsimp simp: setReply_def updateObject_default_def setObject_def split_def)
  apply (erule arg_cong[where f=P, THEN iffD1, rotated])
  apply (clarsimp simp: opt_map_def sym_refs_def fun_upd_def list_refs_of_reply'_def
                        map_set_def projectKO_opt_reply)
  apply (rule ext)
  apply (clarsimp simp: projectKO_opt_reply list_refs_of_reply'_def)
  done

lemma setObject_ksPSpace_only:
  "\<lbrakk> \<And>p q n ko. \<lbrace>P\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv. P \<rbrace>;
        \<And>f s. P (ksPSpace_update f s) = P s \<rbrakk>
     \<Longrightarrow> \<lbrace>P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp | assumption)+
  done

lemma setObject_ksMachine:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)

lemma setObject_ksInterrupt:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)


lemma set_ntfn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (live' (KONotification v) \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
     setNotification p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setNotification_def)
  apply (wp setObject_iflive'[where P="\<top>"])
     apply simp
    apply (simp add: objBits_simps)
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs bind_def)
  apply clarsimp
  done

lemma valid_pde_mappings'_def2:
  "valid_pde_mappings' =
     (\<lambda>s. \<forall>x. pde_at' x s \<longrightarrow> obj_at' (valid_pde_mapping' (x && mask pdBits)) x s)"
  apply (clarsimp simp: valid_pde_mappings'_def typ_at_to_obj_at_arches)
  apply (rule ext, rule iff_allI)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (auto simp add: objBits_simps archObjSize_def)
  done

lemma valid_pde_mappings_lift':
  assumes x: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes y: "\<And>x. \<lbrace>obj_at' (valid_pde_mapping' (x && mask pdBits)) x\<rbrace>
                    f \<lbrace>\<lambda>rv. obj_at' (valid_pde_mapping' (x && mask pdBits)) x\<rbrace>"
  shows      "\<lbrace>valid_pde_mappings'\<rbrace> f \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (simp only: valid_pde_mappings'_def2 imp_conv_disj)
  apply (rule hoare_vcg_all_lift hoare_vcg_disj_lift x y)+
  done

lemma set_ntfn_valid_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule valid_pde_mappings_lift')
   apply wp
  apply (simp add: setNotification_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

end

lemma set_ntfn_minor_invs':
  "\<lbrace>invs'
      and valid_ntfn' val
      and (\<lambda>s. live' (KONotification val) \<longrightarrow> ex_nonz_cap_to' ptr s)\<rbrace>
   setNotification ptr val
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def cteCaps_of_def valid_dom_schedule'_def)
  apply (wpsimp wp: irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift
              simp: o_def)
  done

lemma ep_redux_simps':
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> SendEP xs)
        = (set xs \<times> {EPSend})"
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> RecvEP xs)
        = (set xs \<times> {EPRecv})"
  "ntfn_q_refs_of' (case xs of [] \<Rightarrow> IdleNtfn | y # ys \<Rightarrow> WaitingNtfn xs)
        = (set xs \<times> {NTFNSignal})"
  by (fastforce split: list.splits
                simp: valid_ep_def valid_ntfn_def)+


(* There are two wp rules for preserving valid_ioc over set_object.
   First, the more involved rule for CNodes and TCBs *)
(* Second, the simpler rule suitable for all objects except CNodes and TCBs. *)
lemma valid_refs'_def2:
  "valid_refs' R (ctes_of s) = (\<forall>cref. \<not>cte_wp_at' (\<lambda>c. R \<inter> capRange (cteCap c) \<noteq> {}) cref s)"
  by (auto simp: valid_refs'_def cte_wp_at_ctes_of ran_def)

lemma idle_is_global [intro!]:
  "ksIdleThread s \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemma idle_sc_is_global [intro!]:
  "idle_sc_ptr \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemma valid_globals_cte_wpD':
  "\<lbrakk> valid_global_refs' s; cte_wp_at' P p s; ptr \<in> global_refs' s \<rbrakk>
       \<Longrightarrow> \<exists>cte. P cte \<and> ptr \<notin> capRange (cteCap cte)"
  by (fastforce simp: valid_global_refs'_def valid_refs'_def  cte_wp_at_ctes_of)

lemmas valid_globals_cte_wpD'_idleThread = valid_globals_cte_wpD'[OF _ _ idle_is_global]
lemmas valid_globals_cte_wpD'_idleSC = valid_globals_cte_wpD'[OF _ _ idle_sc_is_global]

lemma dmo_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_aligned'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_distinct'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_inv':
  assumes R: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> doMachineOp f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  apply (drule in_inv_by_hoareD [OF R])
  apply simp
  done

crunches doMachineOp
  for cte_wp_at'2[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation doMachineOp: typ_at_all_props' "doMachineOp mop"
  by typ_at_props'

lemma doMachineOp_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     doMachineOp m \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      doMachineOp m
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: doMachineOp_def split_def
                valid_pspace'_def valid_queues_def valid_queues_no_bitmap_def bitmapQ_defs
       | wp cur_tcb_lift sch_act_wf_lift tcb_in_cur_domain'_lift
       | fastforce elim: state_refs_of'_pspaceI)+

crunch obj_at'[wp]: doMachineOp "\<lambda>s. P (obj_at' P' p s)"

crunch it[wp]: doMachineOp "\<lambda>s. P (ksIdleThread s)"
crunch idle'[wp]: doMachineOp "valid_idle'"
  (wp: crunch_wps simp: crunch_simps valid_idle'_pspace_itI)

lemma setEndpoint_ksMachine:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (simp add: setEndpoint_def | wp setObject_ksMachine updateObject_default_inv)+

lemmas setEndpoint_valid_irq_states'  =
  valid_irq_states_lift' [OF setEndpoint_ksInterruptState setEndpoint_ksMachine]

lemma setEndpoint_ct':
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setEndpoint a b \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setEndpoint_def setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemmas setEndpoint_valid_globals[wp]
    = valid_global_refs_lift' [OF set_ep_ctes_of set_ep_arch'
                                  setEndpoint_it setEndpoint_ksInterruptState]
lemma obj_at'_is_canonical:
  "\<lbrakk>pspace_canonical' s; obj_at' P t s\<rbrakk> \<Longrightarrow> canonical_address t"
  apply (clarsimp simp: obj_at'_def pspace_canonical'_def)
  by (drule_tac x=t in bspec) clarsimp+

end
end
