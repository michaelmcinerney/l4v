(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContextInv_R
imports Invocations_R Tcb_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

primrec valid_sc_inv' :: "sched_context_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_inv' (InvokeSchedContextConsumed scptr args) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextBind scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and
             bound_sc_tcb_at' ((=) None) t and
             obj_at' (\<lambda>sc. scTCB sc = None) scptr \<^cancel>\<open> and
             FIXME RT: can hopefully be established via assertions:
             (\<lambda>s. st_tcb_at' (ipc_queued_thread_state) t s
                     \<longrightarrow> sc_at_pred' (sc_released (cur_time s)) scptr s) \<close>
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and
             obj_at' (\<lambda>ntfn. ntfnSc ntfn = None) n and
             obj_at' (\<lambda>sc. scNtfn sc = None) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbindObject scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and obj_at' (\<lambda>sc. scTCB sc = Some t) scptr and
             (\<lambda>s. t \<noteq> ksCurThread s)
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and obj_at' (\<lambda>sc. scNtfn sc = Some n) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbind scptr) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextYieldTo scptr args) =
     (\<lambda>s. ex_nonz_cap_to' scptr s \<and>
          (\<forall>ct. ct = ksCurThread s \<longrightarrow>
                bound_yt_tcb_at' ((=) None) ct s \<and>
                obj_at' (\<lambda>sc. \<exists>t. scTCB sc = Some t \<and> t \<noteq> ct) scptr s))"

definition
  valid_refills_number' :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_refills_number' max_refills n \<equiv> max_refills \<le> refillAbsoluteMax' n"

primrec valid_sc_ctrl_inv' :: "sched_control_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_ctrl_inv' (InvokeSchedControlConfigureFlags scptr budget period mrefills badge flags) =
     ((\<lambda>s. \<exists>n. sc_at'_n n scptr s \<and> valid_refills_number' mrefills n) and
      ex_nonz_cap_to' scptr and K (MIN_REFILLS \<le> mrefills) and
      K (budget \<le> MAX_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         period \<le> MAX_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         budget \<le> period))"

primrec sc_inv_rel :: "Invocations_A.sched_context_invocation \<Rightarrow> sched_context_invocation \<Rightarrow> bool"
  where
  "sc_inv_rel (Invocations_A.InvokeSchedContextConsumed sc_ptr bf) sci' =
   (sci' = InvokeSchedContextConsumed sc_ptr bf)"
| "sc_inv_rel (Invocations_A.InvokeSchedContextBind sc_ptr cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextBind sc_ptr cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbindObject sc_ptr cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextUnbindObject sc_ptr cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbind sc_ptr) sci' =
   (sci' = InvokeSchedContextUnbind sc_ptr)"
| "sc_inv_rel (Invocations_A.InvokeSchedContextYieldTo sc_ptr bf) sci' =
   (sci' = InvokeSchedContextYieldTo sc_ptr bf)"

primrec sc_ctrl_inv_rel ::
  "Invocations_A.sched_control_invocation \<Rightarrow> sched_control_invocation \<Rightarrow> bool" where
  "sc_ctrl_inv_rel (Invocations_A.InvokeSchedControlConfigureFlags sc_ptr budget period refills badge flags) sci' =
    (sci' = InvokeSchedControlConfigureFlags sc_ptr budget period refills badge flags)"

lemma decodeSchedContext_Bind_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContext_Bind sc_ptr excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_Bind_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_UnbindObject_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContext_UnbindObject sc_ptr excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_UnbindObject_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_YieldTo_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s \<and> ex_nonz_cap_to' sc_ptr s\<rbrace>
   decodeSchedContext_YieldTo sc_ptr args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_YieldTo_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp getTCB_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

lemma decodeSchedContextInvocation_wf:
  "\<lbrace>\<lambda>s. \<exists>n. valid_cap' (SchedContextCap sc_ptr n) s
        \<and> ex_nonz_cap_to' sc_ptr s
        \<and> (\<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
        \<and> (\<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedContextInvocation label sc_ptr excaps args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (simp add: decodeSchedContextInvocation_def)
  apply (wpsimp wp: decodeSchedContext_Bind_wf
                    decodeSchedContext_UnbindObject_wf
                    decodeSchedContext_YieldTo_wf)
  apply (fastforce dest: valid_SchedContextCap_sc_at')
  done

lemma decodeSchedControlInvocation_wf:
  "\<lbrace>invs' and (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s)
    and (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s)\<rbrace>
   decodeSchedControlInvocation label args excaps
   \<lbrace>valid_sc_ctrl_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedControlInvocation_def)
  apply (case_tac "genInvocationType label"; simp; (solves wpsimp)?)
  apply (wpsimp simp: decodeSchedControl_ConfigureFlags_def)
  apply (cases excaps; simp)
  apply (rename_tac a list, case_tac a; simp add: isSchedContextCap_def)
  apply (clarsimp simp: valid_cap'_def  ko_wp_at'_def scBits_simps valid_refills_number'_def
                        MAX_PERIOD_def maxPeriodUs_def usToTicks_def us_to_ticks_mono
                        MIN_BUDGET_def kernelWCET_ticks_def timeArgSize_def minBudgetUs_def
                        MIN_REFILLS_def minRefills_def not_less
                  cong: conj_cong)
  apply (insert getCurrentTime_buffer_bound)
  apply (intro conjI impI; (fastforce intro: us_to_ticks_mono)?)
   apply (rule_tac order_trans[OF MIN_BUDGET_helper])
   apply (rule us_to_ticks_mono)
    apply blast
   apply (fastforce intro: order_trans[OF mult_le_mono1]
                     simp: word_le_nat_alt)
  apply (fastforce intro: order_trans[OF mult_le_mono1] us_to_ticks_mono
                    simp: word_le_nat_alt)
  done

lemma decodeSchedcontext_Bind_corres:
  "list_all2 cap_relation excaps excaps'
   \<Longrightarrow> corres (ser \<oplus> sc_inv_rel)
         (invs and valid_sched and sc_at sc_ptr and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x))
         (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
         (decode_sched_context_bind sc_ptr excaps)
         (decodeSchedContext_Bind sc_ptr excaps')"
  apply (clarsimp simp: decode_sched_context_bind_def decodeSchedContext_Bind_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (case_tac cap; clarsimp)
   apply (clarsimp simp: bindE_assoc)
   apply (rule corres_splitEE_skip; (solves wpsimp)?)
    apply (corressimp simp: sc_relation_def)
   apply (rule corres_splitEE''[where r'="(=)"]; (solves wpsimp)?)
    apply (corressimp corres: getNotification_corres
                        simp: get_sk_obj_ref_def ntfn_relation_def valid_cap_def valid_cap'_def
                          wp: hoare_vcg_all_lift)
   apply (rule corres_splitEE_skip; (solves wpsimp)?)
    apply (corressimp corres: getNotification_corres
                        simp: get_sk_obj_ref_def sc_relation_def)
   apply (clarsimp simp: returnOk_def)
  apply (clarsimp simp: bindE_assoc get_tcb_obj_ref_def)
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply (corressimp simp: sc_relation_def)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply (clarsimp simp: valid_cap_def)
     apply (clarsimp simp: valid_cap'_def)
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; (solves \<open>wpsimp simp: valid_cap'_def obj_at'_def\<close>)?)
   apply (corressimp corres: getNotification_corres
                       simp: get_sk_obj_ref_def sc_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule corres_splitEE)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (clarsimp simp: returnOk_def)
         apply (subst corres_liftE_rel_sum)
         apply (rule corres_rel_imp)
          apply (rule isBlocked_corres)
         apply simp
        apply wpsimp
       apply wpsimp
      apply (rule corres_liftE_rel_sum[THEN iffD2, OF get_sc_released_corres])
     apply wpsimp
    apply (wpsimp simp: scReleased_def scActive_def)
   apply (fastforce simp: obj_at_def is_tcb_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma decodeSchedContext_UnbindObject_corres:
  "list_all2 cap_relation excaps excaps'
   \<Longrightarrow> corres (ser \<oplus> sc_inv_rel)
         (invs and sc_at sc_ptr)
         invs'
         (decode_sched_context_unbind_object sc_ptr excaps)
         (decodeSchedContext_UnbindObject sc_ptr excaps')"
  apply (clarsimp simp: decode_sched_context_unbind_object_def decodeSchedContext_UnbindObject_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (case_tac cap; clarsimp)
   apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
   apply (rule corres_splitEE'')
      apply (corressimp corres: get_sc_corres)
      apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
     apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
    apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
   apply (corressimp simp: sc_relation_def)
   apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp simp: sc_relation_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply (rule corres_splitEE'')
     apply (corressimp corres: getCurThread_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply corressimp
  done

lemma decodeSchedContext_YieldTo_corres:
  "corres (ser \<oplus> sc_inv_rel)
          (invs and sc_at sc_ptr)
          invs'
          (decode_sched_context_yield_to sc_ptr args')
          (decodeSchedContext_YieldTo sc_ptr args')"
  apply add_cur_tcb'
  apply (clarsimp simp: decode_sched_context_yield_to_def decodeSchedContext_YieldTo_def)
  apply (clarsimp simp: bindE_assoc get_sc_obj_ref_def liftE_bind_return_bindE_returnOk)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp simp: sc_relation_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply (rule corres_splitEE'')
     apply (corressimp corres: getCurThread_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply (corressimp simp: sc_relation_def)
  apply (clarsimp simp: sc_relation_def)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply (fastforce dest: invs_valid_objs valid_objs_ko_at
                       simp: valid_obj_def valid_sched_context_def)
     apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                      simp: valid_sched_context'_def)
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply fastforce
     apply (fastforce simp: cur_tcb'_def)
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (rule corres_splitEE''[where r'="(=)"])
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule threadGet_corres)
       apply (clarsimp simp: tcb_relation_def)
      apply fastforce
     apply fastforce
    apply (rule liftE_validE[THEN iffD2, OF thread_get_sp])
   apply (rule liftE_validE[THEN iffD2, OF threadGet_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma decode_sc_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_inv_rel)
          (invs and valid_sched and sc_at sc_ptr and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x))
          (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
          (decode_sched_context_invocation (mi_label mi) sc_ptr excaps args')
          (decodeSchedContextInvocation (mi_label mi) sc_ptr excaps' args')"
  apply (clarsimp simp: decode_sched_context_invocation_def decodeSchedContextInvocation_def
             split del: if_split)
  apply (cases "gen_invocation_type (mi_label mi)"
         ; clarsimp split: gen_invocation_labels.split list.splits
                split del: if_split)
      apply (clarsimp simp: returnOk_def)
     apply (corressimp corres: decodeSchedcontext_Bind_corres)
    defer
    apply (corressimp corres: decodeSchedContext_UnbindObject_corres)
   apply (corressimp corres: decodeSchedContext_YieldTo_corres)
  apply (rule corres_splitEE'')
     apply (corressimp corres: get_sc_corres)
     apply (fastforce intro: sc_at'_cross_rel[unfolded cross_rel_def, rule_format])
    apply (rule liftE_validE[THEN iffD2, OF get_sched_context_sp])
   apply (rule liftE_validE[THEN iffD2, OF get_sc_sp'])
  apply (rule corres_splitEE'')
     apply (corressimp corres: getCurThread_corres)
    apply (rule liftE_validE[THEN iffD2, OF gets_sp])
   apply (rule liftE_validE[THEN iffD2, OF getCurThread_sp])
  apply (rule corres_splitEE_skip; corressimp)
  apply (clarsimp simp: sc_relation_def)
  done

lemma decode_sc_ctrl_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_ctrl_inv_rel) \<top> \<top>
          (decode_sched_control_invocation_flags (mi_label mi) args' excaps)
          (decodeSchedControlInvocation (mi_label mi) args' excaps')"
  apply (clarsimp simp: decode_sched_control_invocation_flags_def decodeSchedControlInvocation_def)
  apply (cases "gen_invocation_type (mi_label mi)"
         ; clarsimp simp: decodeSchedControl_ConfigureFlags_def TIME_ARG_SIZE_def timeArgSize_def)
  apply (cases excaps; clarsimp)
  apply (rename_tac cap list)
  apply (cases excaps'; clarsimp)
  apply (rule corres_splitEE_skip; (solves wpsimp)?)
   apply corressimp
  apply (rule corres_splitEE'')
      apply corressimp
     apply (case_tac cap; clarsimp simp: isSchedContextCap_def)
    apply (rule whenE_throwError_sp[simplified validE_R_def])+
  apply corressimp
  apply (auto simp: minBudgetUs_def MIN_BUDGET_US_def maxPeriodUs_def parse_time_arg_def
                    parseTimeArg_def usToTicks_def minRefills_def MIN_REFILLS_def
                    max_num_refills_eq_refillAbsoluteMax' refillAbsoluteMax_def max_refills_cap_def
             split: cap.splits)
  done

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma invoke_sched_context_corres:
  "sc_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres (=)
          (einvs and valid_sched_context_inv sc_inv and simple_sched_action and ct_active)
          (invs' and sch_act_simple and valid_sc_inv' sc_inv' and ct_active')
          (invoke_sched_context sc_inv)
          (invokeSchedContext sc_inv')"
  apply (simp add: invoke_sched_context_def invokeSchedContext_def)
  (* most of the next layer down should go into SchedContext_R, because some of these are
     reused in Finalise and IpcCancel *)
  sorry

lemmas sc_relation_refillResetRR1 =
  sc_relation_updateRefillTl[where f="r_amount_update (\<lambda>_. 0)" and f'="rAmount_update (\<lambda>_. 0)"]

lemma sc_relation_refillResetRR2:
  "\<lbrakk>sc_relation sc n sc'; length (sc_refills sc) = 2; sc_refill_max sc = MIN_REFILLS;
    sc_valid_refills' sc'; 1 < scRefillCount sc'\<rbrakk>
    \<Longrightarrow> sc_relation
             (sc_refills_update
               (\<lambda>refills. r_amount_update (\<lambda>m. m + r_amount (hd (tl refills))) (hd refills) # tl refills)
               sc)
             n ((scRefills_update
                         (\<lambda>_. updateAt (scRefillHead sc') (scRefills sc')
                                (\<lambda>hd. rAmount_update (\<lambda>_. rAmount hd + rAmount (refillTl sc')) hd)))
                 sc')"
  apply (case_tac "sc_refills sc"; simp)
  apply (rename_tac ls; case_tac ls; clarsimp simp: MIN_REFILLS_def)
  apply (cases sc; simp add: sc_relation_def refills_map_def)
  apply (prop_tac "scRefillCount sc' = 2")
   apply (insert length_wrap_slice[of "scRefillCount sc'" "scRefillMax sc'" "scRefillHead sc'" "scRefills sc'"])
   apply (case_tac "scRefillHead sc'"; simp)
  apply (clarsimp simp: refill_map_def updateAt_def Let_def null_def)
  apply (clarsimp simp: wrap_slice_def)
  apply (intro conjI; clarsimp simp: updateAt_def Let_def null_def refill_map_def)
   apply (case_tac "scRefills sc'"; simp)
   apply (rename_tac list; case_tac list; simp add: refill_map_def refillTl_def refillTailIndex_def)
  apply (case_tac "scRefillHead sc'"; simp)
  apply (intro conjI; clarsimp)
  apply (case_tac "scRefills sc'"; simp)
  apply (rename_tac list; case_tac list; simp add: refill_map_def refillTl_def refillTailIndex_def)
  done

lemma sc_relation_refillResetRR:
  "\<lbrakk>sc_relation sc n sc'; length (sc_refills sc) = 2; sc_refill_max sc = MIN_REFILLS;
    sc_valid_refills' sc'; 1 < scRefillCount sc'\<rbrakk>
   \<Longrightarrow> sc_relation
             (sc_refills_update
               ((\<lambda>refills. butlast refills @ [last refills\<lparr>r_amount := 0\<rparr>]) \<circ>
                (\<lambda>refills. r_amount_update (\<lambda>m. m + r_amount (hd (tl refills))) (hd refills) # tl refills))
               sc)
             n (((\<lambda>sc. scRefills_update (\<lambda>_. updateAt (refillTailIndex sc) (scRefills sc) (rAmount_update (\<lambda>_. 0)))
                         sc) \<circ>
                 (\<lambda>sc. scRefills_update
                         (\<lambda>_. updateAt (scRefillHead sc) (scRefills sc)
                                (\<lambda>hd. rAmount_update (\<lambda>_. rAmount hd + rAmount (refillTl sc)) hd))
                         sc))
                 sc')"
  apply (drule sc_relation_refillResetRR2; fastforce?)
  by (drule sc_relation_refillResetRR1; clarsimp simp: refill_map_def)

lemma refillResetRR_corres:
  "corres dc (sc_at csc_ptr and is_active_sc csc_ptr
                  and round_robin csc_ptr and valid_refills csc_ptr)
             (valid_objs' and sc_at' csc_ptr)
             (refill_reset_rr csc_ptr) (refillResetRR csc_ptr)"
  (is "corres dc ?abs ?conc _ _")
  supply projection_rewrites[simp]
  apply (subst is_active_sc_rewrite)
  apply (subst valid_refills_rewrite)
  apply (rule_tac Q="is_active_sc' csc_ptr" in corres_cross_add_guard)
   apply (fastforce dest!: is_active_sc'_cross[OF state_relation_pspace_relation])
  apply (rule_tac Q="\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' = 2) |< scs_of' s') csc_ptr"
         in corres_cross_add_guard)
   apply (clarsimp simp: obj_at'_def projectKOs round_robin2_def obj_at_def is_sc_obj
                         rr_valid_refills_def is_active_sc2_def is_active_sc'_def opt_map_red)
   apply (drule (1) pspace_relation_absD[where x=csc_ptr, OF _ state_relation_pspace_relation])
   apply (erule (1) valid_objsE')
   apply (clarsimp simp: sc_relation_def refills_map_def valid_sched_context'_def valid_obj'_def)
  apply (clarsimp simp: refill_reset_rr_def refillResetRR_def get_refills_def updateRefillTl_def
                        update_sched_context_decompose[symmetric, simplified] update_refill_tl_def)
  apply (rule corres_guard_imp)
    apply (rule monadic_rewrite_corres'[OF _ monadic_rewrite_sym[OF updateSchedContext_decompose[simplified]]])
    apply (rule updateSchedContext_corres_gen[where
                 P="(\<lambda>s. ((\<lambda>sc. length (sc_refills sc) = 2 \<and> sc_refill_max sc = MIN_REFILLS) |< scs_of2 s) csc_ptr)"
            and P'="valid_objs' and is_active_sc' csc_ptr and (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' = 2) |< scs_of' s') csc_ptr)"])
      apply (clarsimp, drule (2) state_relation_sc_relation)
      apply (clarsimp simp: is_sc_obj obj_at_simps is_active_sc'_def opt_map_red)
      apply (erule (1) valid_objsE', clarsimp simp: valid_obj'_def valid_sched_context'_def)
      apply (fastforce elim!: sc_relation_refillResetRR[simplified])
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red
                     dest!: state_relation_sc_replies_relation_sc)
     apply (clarsimp simp: objBits_simps)+
   apply (clarsimp simp: round_robin2_def obj_at_def is_sc_obj rr_valid_refills_def opt_map_red)
  by (clarsimp simp: objBits_simps)

lemma refillNew_corres:
  "\<lbrakk>1 < max_refills; valid_refills_number' max_refills (min_sched_context_bits + n)\<rbrakk>
   \<Longrightarrow> corres dc
         (pspace_aligned and pspace_distinct and sc_obj_at n sc_ptr) \<top>
            (refill_new sc_ptr max_refills budget period)
            (refillNew sc_ptr max_refills budget period)"
  supply projection_rewrites[simp]
  supply getSchedContext_wp[wp del] set_sc'.get_wp[wp del]
  apply (rule corres_cross_add_guard[where
      Q = "sc_at' sc_ptr and (\<lambda>s'. ((\<lambda>sc. objBits sc = minSchedContextBits + n) |< scs_of' s') sc_ptr)"])
   apply (fastforce dest!: sc_obj_at_cross[OF state_relation_pspace_relation]
                     simp: obj_at'_def projectKOs opt_map_red)
  apply (unfold refillNew_def refill_new_def setRefillHd_def updateRefillHd_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ getCurTime_corres])
      (* period *)
      apply (rule corres_split[OF updateSchedContext_corres]; clarsimp simp: objBits_simps)
     apply (fastforce simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red
                     dest!: state_relation_sc_relation)
     apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red
                     dest!: state_relation_sc_replies_relation_sc)
        (* budget *)
        apply (rule corres_split[OF updateSchedContext_corres]; (clarsimp simp: objBits_simps)?)
     apply (fastforce simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red
                     dest!: state_relation_sc_relation)
           apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red
                           dest!: state_relation_sc_replies_relation_sc)
          (* max_refills, sc_refills update *)
          (* rewrite into one step updateSchedContext corres *)
          apply (rename_tac ctime)
          apply (rule_tac P="sc_obj_at n sc_ptr and (\<lambda>s. ctime = cur_time s)"
                      and P'="sc_at' sc_ptr and (\<lambda>s'. ctime = ksCurTime s')
                              and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n) |< scs_of' s') sc_ptr)"
                 in corres_inst)
          apply (subst bind_assoc[symmetric])
          apply (subst update_sched_context_decompose[symmetric, simplified])
          apply (subst bind_assoc[symmetric])
          apply (subst bind_assoc[symmetric])
          apply (subst bind_assoc)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF  monadic_rewrite_corres'
                                           [OF _ monadic_rewrite_sym
                                                   [OF updateSchedContext_decompose_x2[simplified]]]])
                  (* use setSchedContext_corres *)
                  apply (rule monadic_rewrite_corres[OF _ update_sched_context_rewrite[where n=n]])
                  apply (simp add: updateSchedContext_def)
                  apply (rule corres_split[OF get_sc_corres])
                    apply (rename_tac sc')
                    apply (rule_tac P="ko_at (kernel_object.SchedContext sc n) sc_ptr"
                                and P'="ko_at' sc' sc_ptr
                                        and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n) |< scs_of' s') sc_ptr)"
                           in corres_inst)
                    apply (rule_tac F="length (scRefills sc') = max_num_refills (min_sched_context_bits + n)"
                           in corres_req)
                     apply (clarsimp simp: obj_at_simps scBits_simps opt_map_red)
                    using scBits_inverse_sc apply fastforce
                    apply (rule stronger_corres_guard_imp)
                      apply (rule_tac sc'="sc'\<lparr> scRefillMax := max_refills,
                                                scRefillHead := 0,
                                                scRefillCount := Suc 0,
                                                scRefills := updateAt 0 (scRefills sc') (\<lambda>r. Refill ctime budget)\<rparr>"
                             in setSchedContext_corres)
                       apply (clarsimp simp: sc_relation_def refills_map_def valid_refills_number'_def
                                             wrap_slice_start_0 max_num_refills_eq_refillAbsoluteMax')
                       apply (case_tac "scRefills sc'"; simp add: updateAt_def null_def refill_map_def)
                      apply (clarsimp simp: objBits_simps scBits_simps)
                     apply simp
                    apply (fastforce simp: obj_at_simps is_sc_obj opt_map_red
                                    dest!: sc_replies_relation_prevs_list[OF state_relation_sc_replies_relation])
                   apply (wpsimp wp: getSchedContext_wp')+
                 apply (clarsimp simp: objBits_simps)+
              (* last step : add tail *)
              apply (rule_tac P="sc_obj_at n sc_ptr and is_active_sc2 sc_ptr"
                          and P'="sc_at' sc_ptr
                                  and (\<lambda>s'. ((\<lambda>sc'. objBits sc' = minSchedContextBits + n
                                             \<and> scRefillHead sc' = 0 \<and> scRefillCount sc' = 1
                                             \<and> scRefillMax sc' = max_refills) |< scs_of' s') sc_ptr)"
                     in corres_inst)
              apply (rule stronger_corres_guard_imp)
                apply (rule maybeAddEmptyTail_corres[simplified dc_def])
               apply simp
              apply (clarsimp simp: obj_at_simps is_sc_obj scBits_simps opt_map_red
                                    valid_refills_number'_def)
              apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, rotated])
              using scBits_inverse_sc apply fastforce
             apply (wpsimp wp: update_sched_context_wp updateSchedContext_wp)+
           apply (clarsimp simp:  obj_at_def is_sc_obj is_active_sc2_def)
          apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] valid_objs'_def ps_clear_upd
                                opt_map_red)
         apply (wpsimp wp: update_sched_context_wp updateSchedContext_wp)+
   apply (clarsimp simp:  obj_at_def is_sc_obj is_active_sc2_def)
  apply (clarsimp simp: obj_at_simps fun_upd_def[symmetric] valid_objs'_def ps_clear_upd opt_map_red)
  done

lemma refillUpdate_corres:
  "\<lbrakk>1 < max_refills; valid_refills_number' max_refills (min_sched_context_bits + n)\<rbrakk>
   \<Longrightarrow> corres dc
              ((is_active_sc2 sc_ptr and sc_obj_at n sc_ptr) and (pspace_aligned and pspace_distinct))
              (valid_refills' sc_ptr)
              (refill_update sc_ptr period budget max_refills)
              (refillUpdate sc_ptr period budget max_refills)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> corres _ (?pred and _) ?conc _ _")
  supply getSchedContext_wp[wp del] set_sc'.get_wp[wp del] projection_rewrites[simp]
  apply (rule corres_cross_add_guard[where
      Q = "sc_at' sc_ptr and (\<lambda>s'. ((\<lambda>sc. objBits sc = minSchedContextBits + n) |< scs_of' s') sc_ptr)"])
   apply (fastforce dest!: sc_obj_at_cross[OF state_relation_pspace_relation]
                     simp: obj_at'_def projectKOs opt_map_red)
  apply (rule_tac Q="is_active_sc' sc_ptr" in corres_cross_add_guard)
   apply (rule is_active_sc'_cross, fastforce+)
  apply (rule corres_guard_imp)
    apply (rule_tac P="?pred" and P'="?conc and sc_at' sc_ptr" in corres_inst)
    apply (unfold refillUpdate_def refill_update_def)
    apply simp
    (* rewrite the refill list update steps into one step updateSchedContext corres *)
    apply (subst bind_assoc[where m="update_sched_context _ _", symmetric])
    apply (subst update_sched_context_decompose[symmetric, simplified])
    apply (subst bind_assoc[where m="updateSchedContext _ _", symmetric])
    apply (subst bind_assoc[where m="do _ \<leftarrow> updateSchedContext _ _; updateSchedContext _ _ od", symmetric])
    apply (subst bind_assoc[where m="do _ \<leftarrow> (do _ \<leftarrow> updateSchedContext _ _; updateSchedContext _ _ od);
                                     updateSchedContext _ _ od", symmetric])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (subst bind_assoc[where m="updateSchedContext _ _"])
    apply (rule stronger_corres_guard_imp)
      apply (rule corres_split[OF  monadic_rewrite_corres'
                                     [OF _ monadic_rewrite_sym
                                             [OF updateSchedContext_decompose_x3[simplified]]]])
                                       (* now use setSchedContext_corres *)
             apply (rule corres_inst[where P="?pred and sc_obj_at n sc_ptr" and P'="?conc and sc_at' sc_ptr"])
             (* one of the sc_obj_at n sc_ptr will be consumed by the next line *)
             apply (rule monadic_rewrite_corres[OF _ update_sched_context_rewrite[where n=n]])
             apply (simp add: updateSchedContext_def)
             apply (rule stronger_corres_guard_imp)
               apply (rule corres_split[OF get_sc_corres])
                 apply (rename_tac sc sc')
                 apply (rule_tac P="?pred and ko_at (kernel_object.SchedContext sc n) sc_ptr"
                             and P'="ko_at' sc' sc_ptr
                                     and K (objBits sc' = minSchedContextBits + n
                                                \<and> 0 < scRefillMax sc' \<and> sc_valid_refills' sc')"
                        in corres_inst)
                apply (rule_tac F="0 < scRefillMax sc' \<and> sc_valid_refills' sc'
                                    \<and> length (scRefills sc') = max_num_refills (min_sched_context_bits + n)"
                        in corres_req)
                  apply clarsimp
                  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps scBits_simps)
                 using scBits_inverse_sc apply fastforce
                 apply (rule stronger_corres_guard_imp)
                   apply (rule setSchedContext_corres)
                    apply (unfold sc_relation_def; elim conjE exE; intro conjI; fastforce?)
                    apply (clarsimp simp: refills_map_def wrap_slice_start_0 hd_map neq_Nil_lengthI
                                          refill_map_def updateAt_def null_def refillHd_def hd_wrap_slice
                                          valid_refills_number'_def max_num_refills_eq_refillAbsoluteMax')
                   apply (clarsimp simp: objBits_simps scBits_simps)
                  apply simp
                 apply (clarsimp simp: obj_at_simps scBits_simps is_sc_obj)
                 apply (fastforce elim!: sc_replies_relation_prevs_list[OF state_relation_sc_replies_relation])
                apply wpsimp
               apply (wpsimp wp: getSchedContext_wp')
              apply (clarsimp simp: obj_at_def is_sc_obj)
             apply (drule state_relation_sc_relation[where ptr=sc_ptr];
                   (fastforce simp: obj_at_simps is_sc_obj obj_bits_def)?)
             apply (clarsimp simp: obj_at_simps is_sc_obj valid_refills_number'_def scBits_simps
                                   opt_map_red valid_refills'_def
                            dest!: scRefills_length)
            apply ((clarsimp simp: objBits_simps)+)[2]
        (* sc_period *)
        apply (rule corres_split[OF updateSchedContext_corres])
             apply (fastforce dest!: state_relation_sc_relation
                               simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red)
            apply (fastforce dest!: state_relation_sc_replies_relation_sc
                              simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red)
           apply (simp add: objBits_simps)
          (* sc_budget *)
          apply (rule corres_split[OF updateSchedContext_corres])
               apply (fastforce dest!: state_relation_sc_relation
                                 simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red)
              apply (fastforce dest!: state_relation_sc_replies_relation_sc
                                simp: obj_at_simps is_sc_obj sc_relation_def opt_map_red)
             apply (simp add: objBits_simps)
            (* the rest *)
            apply (rule_tac P="sc_obj_at n sc_ptr and
                              (\<lambda>s. ((\<lambda>sc. sc_refills sc\<noteq> [] \<and> 0 < sc_refill_max sc) |< scs_of s) sc_ptr)"
                       and P'="sc_at' sc_ptr and
                              (\<lambda>s'. ((\<lambda>ko. 1 < scRefillMax ko \<and> scRefillCount ko = 1 \<and> sc_valid_refills' ko)
                                            |< scs_of' s') sc_ptr)"
                   in corres_inst)
            apply (simp add: when_def[symmetric] whenM_def ifM_def bind_assoc split del: if_split)
            apply (rule corres_guard_imp)
              apply (rule corres_split[OF refillReady_corres]) (* projection version *)
                (* when-block *)
                apply (rule corres_split[OF corres_when], simp)
                   apply (rule corres_split[OF getCurTime_corres])
                     apply (rule corres_guard_imp)
                       apply (rule updateRefillHd_corres, simp)
                       apply (simp add: refill_map_def)
                      apply (simp+)[2]
                    apply (wpsimp+)[2]
                  apply (simp add: liftM_def bind_assoc)
                  apply (rule corres_split[OF get_sc_corres])
                    (* if-block *)
                    apply (rename_tac sc sc')
                    apply (rule_tac P="ko_at (kernel_object.SchedContext sc n) sc_ptr
                                       and K (0 < sc_refill_max sc) and K (sc_refills sc \<noteq> [])
                                        and K (valid_sched_context_size n)"
                                and P'="ko_at' sc' sc_ptr
                                        and K (1 < scRefillMax sc' \<and> scRefillCount sc' = 1 \<and> sc_valid_refills' sc')"
                           in corres_inst)
                    apply (rule_tac F="refill_hd sc = refill_map (refillHd sc')" in corres_req)
                     apply (fastforce dest!: refill_hd_relation)
                    apply (rule corres_guard_imp)
                      apply (rule corres_if)
                        apply (clarsimp simp: refill_map_def)
                       apply (rule corres_split[OF updateRefillHd_corres], simp)
                          apply (clarsimp simp: refill_map_def)
                         apply (rule maybeAddEmptyTail_corres)
                        apply (wpsimp simp: update_refill_hd_rewrite)
                       apply (wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)
                      apply (rule refillAddTail_corres)
                      apply (clarsimp simp: refill_map_def)
                     apply (clarsimp simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_red)
                    apply (clarsimp simp: obj_at_simps opt_map_red is_sc_obj ps_clear_upd
                                          scBits_simps fun_upd_def[symmetric] valid_refills'_def)
                   apply wpsimp
                  apply (wpsimp wp: getSchedContext_wp')
                 apply (wpsimp simp: update_refill_hd_def wp: update_sched_context_wp)
                apply (wpsimp simp: updateRefillHd_def objBits_simps
                                wp: updateSchedContext_wp)
               apply (wpsimp wp: get_sc_refill_ready_wp)
              apply (wpsimp wp: refillReady_wp')
             apply (fastforce simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_red)
            apply (fastforce simp: obj_at_simps ps_clear_upd fun_upd_def[symmetric]
                                   valid_refills'_def opt_map_red)
           apply ((wpsimp wp: updateSchedContext_wp update_sched_context_wp simp: objBits_simps)+)[5]
      apply (rule monadic_rewrite_refine_valid[where P''=\<top>, OF updateSchedContext_decompose_x3, simplified])
          apply ((clarsimp simp: objBits_simps)+)[2]
      apply (wpsimp wp: updateSchedContext_wp simp: objBits_simps)
     apply (clarsimp simp: obj_at_def is_sc_obj is_active_sc2_def opt_map_red)
    apply (clarsimp simp: obj_at_simps scBits_simps ps_clear_upd fun_upd_def[symmetric]
                          valid_refills_number'_def is_sc_obj)
    apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation])
    apply (fastforce simp: valid_sched_context'_def valid_obj'_def valid_refills_number'_def
                           valid_sched_context_size'_def scBits_simps objBits_simps opt_map_red
                    dest!: scRefills_length)
   apply clarsimp+
  done

lemma valid_sched_context'_scBadge_update[simp]:
  "valid_sched_context' (scBadge_update f ko) s = valid_sched_context' ko s"
  by (clarsimp simp: valid_sched_context'_def)

lemma valid_sched_context_size'_scBadge_update[simp]:
  "valid_sched_context_size' (scBadge_update f sc') = valid_sched_context_size' sc'"
  by (clarsimp simp: valid_sched_context_size'_def objBits_simps)

lemma valid_sched_context'_scSporadic_update[simp]:
  "valid_sched_context' (scSporadic_update f ko) s = valid_sched_context' ko s"
  by (clarsimp simp: valid_sched_context'_def)

lemma valid_sched_context_size'_scSporadic_update[simp]:
  "valid_sched_context_size' (scSporadic_update f sc') = valid_sched_context_size' sc'"
  by (clarsimp simp: valid_sched_context_size'_def objBits_simps)

lemma scBadge_update_corres:
  "\<lbrakk>\<forall>x y. x = y \<longrightarrow> f x = f' y\<rbrakk> \<Longrightarrow>
    corres dc (sc_at scPtr) (ko_at' sc' scPtr)
          (update_sched_context scPtr (sc_badge_update f))
          (setSchedContext scPtr (scBadge_update f' sc'))"
  apply (clarsimp simp: update_sched_context_def)
  apply (rule corres_symb_exec_l[rotated 2, OF get_object_sp])
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>" for P f Q \<Rightarrow> -\<close>)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply wpsimp
   apply (clarsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj; clarsimp;
         (solves \<open>fastforce simp: obj_at_def is_sc_obj_def corres_underlying_def\<close>)?)
  apply (corressimp corres: setSchedContext_no_stack_update_corres
                              [where f="sc_badge_update f" and f'="scBadge_update f'" ])
  apply (clarsimp simp: sc_relation_def objBits_def objBitsKO_def obj_at_def)
  done

lemma scSporadic_update_corres:
  "\<lbrakk>\<forall>x y. x = y \<longrightarrow> f x = f' y\<rbrakk> \<Longrightarrow>
    corres dc (sc_at scPtr) (ko_at' sc' scPtr)
          (update_sched_context scPtr (sc_sporadic_update f))
          (setSchedContext scPtr (scSporadic_update f' sc'))"
  apply (clarsimp simp: update_sched_context_def)
  apply (rule corres_symb_exec_l[rotated 2, OF get_object_sp])
    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>" for P f Q \<Rightarrow> -\<close>)
    apply (fastforce intro: get_object_exs_valid
                      simp: obj_at_def)
   apply wpsimp
   apply (clarsimp simp: obj_at_def)
  apply (rename_tac obj)
  apply (case_tac obj; clarsimp;
         (solves \<open>fastforce simp: obj_at_def is_sc_obj_def corres_underlying_def\<close>)?)
  apply (corressimp corres: setSchedContext_no_stack_update_corres
                              [where f="sc_sporadic_update f" and f'="scSporadic_update f'" ])
  apply (clarsimp simp: sc_relation_def objBits_def objBitsKO_def obj_at_def)
  done

crunches commitTime, refillNew, refillUpdate
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedDequeue_valid_refills'[wp]:
  "tcbSchedDequeue tcbPtr \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (clarsimp simp: tcbSchedDequeue_def)
  apply (wpsimp wp: threadSet_wp threadGet_wp
              simp: bitmap_fun_defs setQueue_def
         | intro conjI impI)+
  apply (fastforce simp: obj_at_simps valid_refills'_def opt_map_def split: option.splits)
  done

crunches tcbSchedDequeue, tcbReleaseRemove
  for ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (wp: crunch_wps threadSet_wp simp: setQueue_def valid_refills'_def bitmap_fun_defs crunch_simps)

lemma tcbReleaseRemove_valid_refills'[wp]:
  "tcbReleaseRemove tcbPtr \<lbrace>valid_refills' scPtr\<rbrace>"
  apply (clarsimp simp: tcbReleaseRemove_def)
  apply (wpsimp wp: threadSet_wp threadGet_wp
              simp: bitmap_fun_defs setReleaseQueue_def setReprogramTimer_def
         | intro conjI impI)+
    apply (fastforce simp: obj_at_simps valid_refills'_def opt_map_def split: option.splits)+
  done

lemma updateSchedContext_scBadge_update_active_sc_at'[wp]:
  "updateSchedContext scPtr' (scBadge_update f) \<lbrace>active_sc_at' scPtr\<rbrace>"
  apply (clarsimp simp: updateSchedContext_def)
  apply (wpsimp wp: set_sc'.set_wp)
  apply (fastforce simp: active_sc_at'_def obj_at_simps scBits_simps ps_clear_def)
  done

lemma updateSchedContext_scSporadic_update_active_sc_at'[wp]:
  "updateSchedContext scPtr' (scSporadic_update f) \<lbrace>active_sc_at' scPtr\<rbrace>"
  apply (clarsimp simp: updateSchedContext_def)
  apply (wpsimp wp: set_sc'.set_wp)
  apply (fastforce simp: active_sc_at'_def obj_at_simps scBits_simps ps_clear_def)
  done

crunches commit_time, refill_new, refill_update
  for sc_at[wp]: "sc_at sc_ptr"
  and tcb_at[wp]: "tcb_at tcb_ptr"
  (wp: crunch_wps)

lemma update_sched_context_sc_obj_at_n[wp]:
  "update_sched_context sc_ptr' f \<lbrace>\<lambda>s. Q (sc_obj_at n sc_ptr s)\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: obj_at_def is_sc_obj_def)
  done

lemma refill_budget_check_round_robin_sc_obj_at_n[wp]:
  "refill_budget_check_round_robin usage \<lbrace>\<lambda>s. Q (sc_obj_at n sc_ptr s)\<rbrace>"
  by (wpsimp simp: refill_budget_check_round_robin_def update_refill_hd_def update_refill_tl_def)

crunches handle_overrun_loop, head_insufficient_loop
  for sc_obj_at[wp]: "\<lambda>s. Q (sc_obj_at n sc_ptr s)"
  (wp: crunch_wps)

lemma refill_budget_check_sc_obj_at_n[wp]:
  "refill_budget_check usage \<lbrace>\<lambda>s. Q (sc_obj_at n sc_ptr s)\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (wpsimp wp: is_round_robin_wp)
  done

lemma commit_time_sc_obj_at[wp]:
  "commit_time \<lbrace>\<lambda>s. Q (sc_obj_at n sc_ptr s)\<rbrace>"
  by (wpsimp simp: commit_time_def)

lemma tcb_release_remove_cur_sc_in_release_q_imp_zero_consumed'[wp_unsafe]:
  "tcb_release_remove tcb_ptr
   \<lbrace>\<lambda>s. cur_sc_in_release_q_imp_zero_consumed_2 sc_ptr (release_queue s) (consumed_time s) (tcb_scps_of s)\<rbrace>"
  apply (wpsimp wp: tcb_release_remove_wp simp: cur_sc_in_release_q_imp_zero_consumed_def)
  apply (case_tac "t = tcb_ptr"; clarsimp simp: in_queue_2_def tcb_sched_dequeue_def)
  done

end

global_interpretation commitTime: typ_at_all_props' "commitTime"
  by typ_at_props'

global_interpretation refillNew: typ_at_all_props' "refillNew scPtr maxRefills budget period"
  by typ_at_props'

global_interpretation refillUpdate: typ_at_all_props' "refillUpdate  scPtr newPeriod newBudget newMaxRefills"
  by typ_at_props'

global_interpretation updateSchedContext: typ_at_all_props' "updateSchedContext scPtr f"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

crunches commitTime, refillNew, refillUpdate
  for ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  (wp: crunch_wps simp: crunch_simps)

lemma tcb_release_remove_sc_not_in_release_q':
  "\<lbrace>\<lambda>s. heap_ref_eq sc_ptr tptr (tcb_scps_of s) \<and> heap_refs_inj (tcb_scps_of s)\<rbrace>
   tcb_release_remove tptr
   \<lbrace>\<lambda>_. sc_not_in_release_q sc_ptr\<rbrace>"
  apply (clarsimp simp: tcb_release_remove_def)
  apply wpsimp
  apply (clarsimp simp: tcb_sched_dequeue_def in_queue_2_def heap_refs_inj_eq)
  done

lemma tcb_sched_dequeue_sc_not_in_ready_q':
  "\<lbrace>\<lambda>s. heap_ref_eq sc_ptr tptr (tcb_scps_of s) \<and> heap_refs_inj (tcb_scps_of s) \<and> valid_ready_qs s
        \<and> tcb_at tptr s\<rbrace>
   tcb_sched_action tcb_sched_dequeue tptr
   \<lbrace>\<lambda>rv. sc_not_in_ready_q sc_ptr\<rbrace>"
  apply (clarsimp simp: tcb_sched_action_def set_tcb_queue_def)
  apply (wpsimp wp: thread_get_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_sched_dequeue_def heap_refs_inj_eq
                        in_queues_2_def  valid_ready_qs_def is_tcb_def)
  apply (rename_tac ko)
  apply (case_tac ko; clarsimp)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec, blast)
  apply (prop_tac "t=tptr")
   apply (clarsimp simp:heap_refs_inj_eq)
  apply (clarsimp simp: vs_all_heap_simps)
  done

crunches maybeAddEmptyTail, setRefillHd
  for invs'[wp]: invs'
  (simp: crunch_simps wp: crunch_wps)

lemma refillNew_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> (\<exists>n. sc_at'_n n scPtr s \<and> valid_refills_number' maxRefills n)
        \<and> ex_nonz_cap_to' scPtr s \<and> MIN_REFILLS \<le> maxRefills\<rbrace>
   refillNew scPtr maxRefills budget period
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  (is "\<lbrace>?P\<rbrace> _ \<lbrace>?Q\<rbrace>")
  apply (clarsimp simp: refillNew_def)
  apply (rule hoare_seq_ext_skip, wpsimp)

  apply (rule hoare_seq_ext_skip)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wpsimp wp: updateSchedContext_invs')
    apply (fastforce dest: invs'_ko_at_valid_sched_context'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
   apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)

  apply (rule hoare_seq_ext_skip)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wpsimp wp: updateSchedContext_invs')
    apply (fastforce dest: invs'_ko_at_valid_sched_context'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
   apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)

  apply (simp flip: bind_assoc)
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (rule hoare_seq_ext)
   apply wpsimp

  apply (clarsimp simp: pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. active_sc_at' scPtr\<rbrace>" for P f \<Rightarrow> -\<close>)
   apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: active_sc_at'_def obj_at_simps MIN_REFILLS_def ps_clear_def)
  apply (clarsimp simp: updateSchedContext_def bind_assoc)
  apply (subst bind_dummy_ret_val)+
  apply (rule hoare_weaken_pre)
   apply (rule_tac P'="?P" and P''="sc_at' scPtr" and Q="?Q"
                in monadic_rewrite_refine_valid[OF getSchedContext_setSchedContext_decompose];
          (solves wpsimp)?)
   apply (wpsimp wp: setSchedContext_invs')
   apply (fastforce dest: invs'_ko_at_valid_sched_context'
                    simp: valid_sched_context'_def valid_sched_context_size'_def obj_at_simps
                          ko_wp_at'_def valid_refills_number'_def)
  apply (clarsimp simp: obj_at_simps ko_wp_at'_def)
  apply (case_tac ko; clarsimp)
  done

lemma refillUpdate_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> (\<exists>n. sc_at'_n n scPtr s \<and> valid_refills_number' newMaxRefills n)
        \<and> ex_nonz_cap_to' scPtr s \<and> MIN_REFILLS \<le> newMaxRefills\<rbrace>
   refillUpdate  scPtr newPeriod newBudget newMaxRefills
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  (is "\<lbrace>?P\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: refillUpdate_def)
  apply (simp flip: bind_assoc)
  apply (rule_tac B="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_seq_ext)
   apply (wpsimp wp: updateRefillHd_invs')
  apply (clarsimp simp: pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. active_sc_at' scPtr\<rbrace>" for P f \<Rightarrow> -\<close>)
   apply (wpsimp wp: updateSchedContext_wp refillReady_wp
               simp: updateRefillHd_def)
   apply (clarsimp simp: active_sc_at'_def obj_at_simps MIN_REFILLS_def ps_clear_def)
  apply (rule_tac B="\<lambda>_. invs'" in hoare_seq_ext)
   apply wpsimp
  apply (rule_tac B="\<lambda>_. invs' and active_sc_at' scPtr" in hoare_seq_ext)
   apply (wpsimp wp: updateRefillHd_invs' refillReady_wp)
  apply (clarsimp simp: pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. active_sc_at' scPtr\<rbrace>" for P f \<Rightarrow> -\<close>)
   apply (wpsimp wp: updateSchedContext_wp refillReady_wp
               simp: updateRefillHd_def)
   apply (clarsimp simp: active_sc_at'_def obj_at_simps MIN_REFILLS_def ps_clear_def)
  apply (rule_tac B="\<lambda>_. invs' and ex_nonz_cap_to' scPtr" in hoare_seq_ext)
   apply (wpsimp wp: updateSchedContext_invs')
   apply (fastforce dest: invs'_ko_at_valid_sched_context'
                    simp: valid_sched_context'_def valid_sched_context_size'_def obj_at_simps)
  apply (clarsimp simp: pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. ex_nonz_cap_to' scPtr\<rbrace>" for P f \<Rightarrow> -\<close>)
   apply (wpsimp wp: updateSchedContext_ex_nonz_cap_to' refillReady_wp
               simp: updateRefillHd_def)
  apply (rule_tac B="\<lambda>_. invs' and ex_nonz_cap_to' scPtr" in hoare_seq_ext)
   apply (wpsimp wp: updateSchedContext_invs')
   apply (fastforce dest: invs'_ko_at_valid_sched_context'
                    simp: valid_sched_context'_def valid_sched_context_size'_def obj_at_simps)
  apply (simp add: bind_assoc)
  apply (clarsimp simp: pred_conj_def)
  apply (intro hoare_vcg_conj_lift_pre_fix)
   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. ex_nonz_cap_to' scPtr\<rbrace>" for P f \<Rightarrow> -\<close>)
   apply (wpsimp wp: updateSchedContext_ex_nonz_cap_to')

  apply (rule hoare_seq_ext_skip)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
    apply (wpsimp wp: updateSchedContext_invs')
    apply (fastforce dest: invs'_ko_at_valid_sched_context'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
   apply (wpsimp wp: updateSchedContext_wp)
   apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)
  apply (rule_tac B="\<lambda>_. ?P and (\<lambda>s'. ((\<lambda>sc'. scRefillHead sc' = 0) |< scs_of' s') scPtr)"
               in hoare_seq_ext[rotated])
   apply (clarsimp simp: pred_conj_def)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
     apply (wpsimp wp: updateSchedContext_invs')
     apply (fastforce dest: invs'_ko_at_valid_sched_context'
                      simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
    apply (wpsimp wp: updateSchedContext_wp)
    apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)
   apply (wpsimp wp: updateSchedContext_wp)
  apply (rule_tac B="\<lambda>_. ?P and (\<lambda>s'. ((\<lambda>sc'. scRefillHead sc' = 0) |< scs_of' s') scPtr)
                            and (\<lambda>s'. ((\<lambda>sc'. scRefillCount sc' = 1) |< scs_of' s') scPtr)"
               in hoare_seq_ext[rotated])
   apply (clarsimp simp: pred_conj_def)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
      apply (wpsimp wp: updateSchedContext_invs')
      apply (fastforce dest: invs'_ko_at_valid_sched_context'
                     simp: valid_sched_context'_def valid_sched_context_size'_def objBits_simps)
     apply (wpsimp wp: updateSchedContext_wp)
     apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)
    apply (wpsimp wp: updateSchedContext_wp)
    apply (clarsimp simp: obj_at_simps ko_wp_at'_def ps_clear_def opt_map_def)
   apply (wpsimp wp: updateSchedContext_wp)
  apply (wpsimp wp: updateSchedContext_invs')
  apply (fastforce dest: invs'_ko_at_valid_sched_context'
                   simp: valid_sched_context'_def valid_sched_context_size'_def obj_at_simps
                         ko_wp_at'_def valid_refills_number'_def opt_map_red)
  done

lemma sc_sporadic_flag_eq_schedContextSporadicFlag:
  "sc_sporadic_flag = schedContextSporadicFlag"
  by (simp add: sc_sporadic_flag_def schedContextSporadicFlag_def)

lemma gts_corres':
  "t = t' \<Longrightarrow> corres thread_state_relation (tcb_at t) (tcb_at' t')
                                           (get_thread_state t) (getThreadState t')"
  apply (simp add: get_thread_state_def getThreadState_def)
  apply (rule threadGet_corres)
  apply (simp add: tcb_relation_def)
  done

lemma tcb_release_remove_sc_tcb_at'[wp]:
  "tcb_release_remove tcb_ptr \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
   unfolding tcb_release_remove_def
   by wpsimp

lemma commit_time_sc_tcb_sc_at[wp]:
  "commit_time \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  (is "_ \<lbrace>?Q\<rbrace>")
  apply (clarsimp simp: commit_time_def)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule_tac B="\<lambda>_. ?Q" in hoare_seq_ext)
   apply wpsimp
  apply clarsimp
  apply (rule hoare_when_cases, simp)
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule_tac B="\<lambda>_. ?Q" in hoare_seq_ext)
   apply (wpsimp wp: update_sched_context_wp)
   apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  apply (wpsimp wp: update_sched_context_wp)
  done

crunches refill_add_tail
  for sc_tcb_sc_at[wp]: "\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)"

lemma maybe_add_empty_tail_sc_tcb_sc_at[wp]:
  "maybe_add_empty_tail sc_ptr \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  by (wpsimp simp: maybe_add_empty_tail_def)


lemma refill_new_sc_tcb_sc_at[wp]:
  "refill_new sc_ptr mrefills budget period \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  unfolding refill_new_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (fastforce simp: sc_tcb_sc_at_def obj_at_def)
  done

lemma refill_update_sc_tcb_sc_at'[wp]:
  "refill_update sc_ptr mrefills budget period \<lbrace>\<lambda>s. Q (sc_tcb_sc_at P sc_ptr s)\<rbrace>"
  unfolding refill_update_def refill_add_tail_def update_refill_tl_def update_refill_hd_def
             bind_assoc update_sched_context_set_refills_rewrite
  apply (wpsimp wp: update_sched_context_wp set_refills_wp get_refills_wp)
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

crunches commitTime
  for ex_nonz_cap_to'[wp]: "ex_nonz_cap_to' ptr"
  (wp: crunch_wps simp: crunch_simps)

lemma minRefills_eq_MIN_REFILLS:
  "minRefills = MIN_REFILLS"
  apply (clarsimp simp: minRefills_def MIN_REFILLS_def)
  done

lemma ex_corres:
  "(\<And>n. corres_underlying srel nf nf' rrel (\<lambda>s. P n s \<and> Q s) P' G G' )
    \<Longrightarrow> corres_underlying srel nf nf' rrel (\<lambda>s. (\<exists>n. P n s) \<and> Q s) P' G G'"
  by (fastforce simp: corres_underlying_def)

lemma isRunnable_corres':
  "t = t' \<Longrightarrow> corres (\<lambda>ts runn. runnable ts = runn) (tcb_at t) (tcb_at' t)
     (get_thread_state t) (isRunnable t')"
  apply (simp add: isRunnable_def)
  apply (subst bind_return[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[OF _ getThreadState_corres])
      apply (case_tac rv, clarsimp+)
     apply (wp hoare_TrueI)+
   apply auto
  done

lemma possibleSwitchTo_corres':
  "t = t' \<Longrightarrow> corres dc
    (valid_sched_action and tcb_at t and pspace_aligned and pspace_distinct
     and valid_tcbs and active_sc_valid_refills)
    (valid_queues and valid_queues' and valid_release_queue_iff and valid_tcbs')
      (possible_switch_to t)
      (possibleSwitchTo t')"
sorry

lemma invokeSchedControlConfigureFlags_corres:
  "sc_ctrl_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres dc
          (einvs and valid_sched_control_inv sc_inv and cur_sc_active and schact_is_rct
           and ct_not_in_release_q and ct_not_queued and ct_active
           and current_time_bounded 5 and consumed_time_bounded
           and (\<lambda>s. cur_sc_offset_ready (consumed_time s) s)
           and (\<lambda>s. cur_sc_offset_sufficient (consumed_time s) s))
          (invs' and sch_act_simple and valid_sc_ctrl_inv' sc_inv' and ct_active')
          (invoke_sched_control_configure_flags sc_inv)
          (invokeSchedControlConfigureFlags sc_inv')"
  (is "_ \<Longrightarrow> corres _ ?abs ?conc _ _")
  apply (cases sc_inv)
  apply (rename_tac sc_ptr budget period mrefills badge flag)
  apply (simp add: invoke_sched_control_configure_flags_def invokeSchedControlConfigureFlags_def)
  apply (subst bind_dummy_ret_val)+

  apply (rule_tac Q="\<lambda>s. sc_at sc_ptr s" in corres_cross_add_abs_guard)
   apply (fastforce intro: valid_sched_context_size_objsI
                     simp: sc_at_pred_n_def obj_at_def is_sc_obj_def)
  apply (rule_tac Q="\<lambda>s'. sc_at' sc_ptr s'" in corres_cross_add_guard)
   apply (fastforce intro: sc_at_cross)
  apply (rule_tac Q="\<lambda>s. sc_at (cur_sc s) s" in corres_cross_add_abs_guard)
   apply (fastforce intro: cur_sc_tcb_sc_at_cur_sc)
  apply (rule_tac Q="\<lambda>s'. active_sc_at' (ksCurSc s') s'" in corres_cross_add_guard)
   apply (fastforce intro: active_sc_at'_cross simp: state_relation_def)

  apply (rule_tac Q="\<lambda>_ s. ?abs s \<and> sc_at sc_ptr s \<and> sc_at (cur_sc s) s"
              and Q'="\<lambda>_  s'. ?conc s' \<and> ex_nonz_cap_to' sc_ptr s' \<and> sc_at' sc_ptr s'
                              \<and> active_sc_at' (ksCurSc s') s'"
               in corres_split')

     apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
     apply wps_conj_solves
      apply (wpsimp wp: update_sc_badge_invs')
      apply (fastforce dest: ex_nonz_cap_to_not_idle_sc_ptr)
     apply (wpsimp wp: update_sched_context_wp)
     apply (clarsimp simp: obj_at_def)

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (wps_conj_solves wp: ct_in_state_thread_state_lift')
     apply (clarsimp simp: updateSchedContext_def)
     apply (wpsimp wp: setSchedContext_invs')
     apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc')

   apply (clarsimp simp: updateSchedContext_def)
   apply (rule corres_symb_exec_r[rotated, OF get_sc_sp' get_sc_inv'])
    apply (wpsimp wp: no_fail_getMiscObject)
   apply (corressimp corres: scBadge_update_corres)

  apply (clarsimp split del: if_split)
  apply (rule_tac Q="\<lambda>_ s. sc_at sc_ptr s \<and> ?abs s \<and> sc_at (cur_sc s) s"
              and Q'="\<lambda>_  s'. ?conc s' \<and> sc_at' sc_ptr s' \<and> active_sc_at' (ksCurSc s') s'
                              \<and> ex_nonz_cap_to' sc_ptr s'"
               in corres_split')

     apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
     apply wps_conj_solves
      apply (wpsimp wp: update_sc_sporadic_invs')
      apply (fastforce dest: ex_nonz_cap_to_not_idle_sc_ptr)
     apply (wpsimp wp: update_sched_context_wp)
     apply (clarsimp simp: obj_at_def)

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (wps_conj_solves wp: ct_in_state_thread_state_lift')
     apply (clarsimp simp: updateSchedContext_def)
     apply (wpsimp wp: setSchedContext_invs')
     apply (fastforce dest!: sc_ko_at_valid_objs_valid_sc')

   apply (clarsimp simp: updateSchedContext_def)
   apply (rule corres_symb_exec_r[rotated, OF get_sc_sp' get_sc_inv'])
    apply (wpsimp wp: no_fail_getMiscObject)
   apply (corressimp corres: scSporadic_update_corres
                       simp: sc_sporadic_flag_eq_schedContextSporadicFlag)

  apply (rule_tac F="budget \<le> MAX_PERIOD \<and> budget \<ge> MIN_BUDGET \<and> period \<le> MAX_PERIOD
                     \<and> budget \<ge> MIN_BUDGET \<and> MIN_REFILLS \<le> mrefills \<and> budget \<le> period"
               in corres_req)
   apply simp

  apply (clarsimp simp: sc_at_sc_obj_at)
  apply (rule ex_corres)
  apply (rename_tac n)
  apply (rule corres_split'[rotated 2, OF get_sched_context_sp get_sc_sp'])
   apply (rule corres_guard_imp)
     apply (rule_tac n=n in get_sc_corres_size)
    apply fast
   apply fast

  apply (rule_tac F="valid_refills_number' mrefills (min_sched_context_bits + n)" in corres_req)
   apply (clarsimp simp: obj_at_simps valid_refills_number'_def ko_wp_at'_def  sc_const_eq)
   apply (rule_tac y="refillAbsoluteMax' (scBitsFromRefillLength' (length (scRefills obj)))"
                in order_trans)
    apply fastforce
   apply (fastforce intro: refillAbsoluteMax'_mono
                     simp: sc_const_eq)

  apply (rename_tac sc')
  apply (rule_tac Q="\<lambda>_ s. invs s \<and> schact_is_rct s \<and> current_time_bounded 5 s
                           \<and> valid_sched_action s \<and> active_sc_valid_refills s
                           \<and> valid_ready_qs s \<and> valid_release_q s
                           \<and> sc_at (cur_sc s) s
                           \<and> sc_not_in_release_q sc_ptr s \<and> sc_not_in_ready_q sc_ptr s
                           \<and> sc_ptr \<noteq> idle_sc_ptr \<and> sc_at sc_ptr s
                           \<and> sc_refill_max_sc_at (\<lambda>rm. rm = sc_refill_max sc) sc_ptr s
                           \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s
                           \<and> sc_obj_at n sc_ptr s
                           \<and> (\<forall>tcb_ptr. sc_tcb_sc_at ((=) (Some tcb_ptr)) sc_ptr s \<longrightarrow> tcb_at tcb_ptr s)"
              and Q'="\<lambda>_ s'. invs' s' \<and> sc_at' (ksCurSc s') s'
                             \<and> (\<exists>n. sc_at'_n n sc_ptr s' \<and> valid_refills_number' mrefills n)
                             \<and> ex_nonz_cap_to' sc_ptr s'"
              and r'=dc
               in corres_split')

     apply (clarsimp simp: when_def split del: if_split)
     apply (rule corres_if_split; (solves \<open>corressimp simp: sc_relation_def\<close>)?)
     apply (rule corres_symb_exec_l[rotated])
        apply (wpsimp wp: exs_valid_assert_opt)
       apply (rule assert_opt_sp)
      apply wpsimp
     apply (rule_tac F="scTCB sc' = Some tcb_ptr" in corres_req)
      apply (fastforce simp: sc_relation_def)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF tcbReleaseRemove_corres])
          apply (clarsimp simp: sc_relation_def)
         apply clarsimp
         apply (rule corres_split[OF tcbSchedDequeue_corres])
           apply (rule corres_split[OF getCurSc_corres])
             apply clarsimp
             apply (simp add: dc_def[symmetric])
             apply (rule commitTime_corres)
            apply (wpsimp wp: hoare_drop_imps tcbReleaseRemove_valid_queues | wps)+
      apply (intro conjI impI; fastforce?)
       apply (fastforce dest: invs_valid_objs valid_sched_context_objsI
                        simp: valid_sched_context_def valid_bound_obj_def obj_at_def)
      apply (fastforce intro: active_sc_valid_refillsE)
     apply (fastforce dest: invs_valid_objs' sc_ko_at_valid_objs_valid_sc'
                     intro: valid_objs'_valid_refills'
                      simp: valid_sched_context'_def valid_bound_obj'_def active_sc_at'_rewrite)

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply wps_conj_solves
            apply (wpsimp wp: commit_time_invs)
           apply (wpsimp wp: commit_time_valid_sched_action hoare_vcg_imp_lift')
           apply fastforce
          apply (wpsimp wp: commit_time_active_sc_valid_refills
                            tcb_release_remove_cur_sc_in_release_q_imp_zero_consumed'
                            hoare_vcg_imp_lift')
          apply (frule cur_sc_tcb_are_bound_cur_sc_in_release_q_imp_zero_consumed[rotated 2])
            apply (fastforce intro: invs_strengthen_cur_sc_tcb_are_bound)
           apply fastforce
          apply (fastforce intro: cur_sc_active_offset_ready_and_sufficient_implies_cur_sc_more_than_ready)
         apply (wpsimp wp: commit_time_valid_ready_qs hoare_vcg_imp_lift'
                           tcb_sched_dequeue_valid_ready_qs hoare_vcg_disj_lift)
         apply (fastforce intro: cur_sc_active_offset_ready_and_sufficient_implies_cur_sc_more_than_ready)
        apply (wpsimp wp: commit_time_valid_release_q hoare_vcg_imp_lift'
                          tcb_release_remove_cur_sc_in_release_q_imp_zero_consumed'
               | strengthen invs_valid_stateI)+
        apply (frule cur_sc_tcb_are_bound_cur_sc_in_release_q_imp_zero_consumed[rotated 2])
          apply (fastforce intro: invs_strengthen_cur_sc_tcb_are_bound)
         apply fastforce
        apply (fastforce simp: cur_sc_in_release_q_imp_zero_consumed_2_def)
       apply (wpsimp wp: tcb_release_remove_sc_not_in_release_q'
                 wp_del: tcb_release_remove_sc_not_in_release_q)
       apply (intro conjI impI; fastforce?)
         apply (fastforce dest!: invs_sym_refs sym_ref_sc_tcb
                           simp: heap_refs_inv_def vs_all_heap_simps obj_at_def sc_at_pred_n_def)
        apply (fastforce intro: sym_refs_inj_tcb_scps)
       apply (drule valid_sched_valid_release_q)
       apply (clarsimp simp: vs_all_heap_simps)
       apply (frule_tac ref=t in valid_release_q_no_sc_not_in_release_q)
        apply (fastforce dest!: invs_sym_refs sym_ref_tcb_sc
                          simp: obj_at_def vs_all_heap_simps is_sc_obj_def)
       apply fastforce
      apply (wpsimp wp: tcb_sched_dequeue_sc_not_in_ready_q'
                wp_del: tcb_dequeue_sc_not_in_ready_q)

       apply (intro conjI impI; fastforce?)
         apply (fastforce dest!: invs_sym_refs sym_ref_sc_tcb
                           simp: heap_refs_inv_def vs_all_heap_simps obj_at_def sc_at_pred_n_def)
        apply (fastforce intro: sym_refs_inj_tcb_scps)
       apply (frule invs_valid_objs)
       apply (frule_tac r=sc_ptr in valid_sched_context_objsI)
        apply (fastforce simp: obj_at_def)
       apply (clarsimp simp: valid_sched_context_def)
       apply (drule valid_sched_valid_ready_qs)
       apply (clarsimp simp: vs_all_heap_simps)
       apply (frule_tac ref=t in valid_ready_qs_no_sc_not_queued)
        apply (fastforce dest!: invs_sym_refs sym_ref_tcb_sc
                          simp: obj_at_def vs_all_heap_simps is_sc_obj_def)
       apply fastforce
     apply wpsimp
     using idle_sc_no_ex_cap apply fastforce
    apply wpsimp
    apply (clarsimp simp: sc_at_pred_n_def obj_at_def)

     apply (rule hoare_when_cases, simp)
      apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
     apply (rule_tac Q="sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr" in hoare_weaken_pre[rotated])
      apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
     apply (rule hoare_seq_ext_skip, wpsimp)+
     apply wpsimp

    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (fastforce dest: invs_valid_objs valid_sched_context_objsI
                     simp: valid_sched_context_def valid_bound_obj_def sc_at_pred_n_def obj_at_def
                    split: option.splits)

   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
   apply (wps_conj_solves wp: commitTime_invs' tcbReleaseRemove_invs'
                        simp: active_sc_at'_rewrite)

  apply (rule_tac Q="\<lambda>_ s. invs s \<and> schact_is_rct s \<and> current_time_bounded 5 s
                           \<and> valid_sched_action s \<and> active_sc_valid_refills s
                           \<and> valid_ready_qs s \<and> valid_release_q s
                           \<and> sc_at (cur_sc s) s
                           \<and> sc_at sc_ptr s
                           \<and> sc_tcb_sc_at (\<lambda>to. to = sc_tcb sc) sc_ptr s
                           \<and> (\<forall>tcb_ptr. sc_tcb_sc_at ((=) (Some tcb_ptr)) sc_ptr s \<longrightarrow> tcb_at tcb_ptr s)"
              and Q'="\<lambda>_ s'. invs' s' \<and>  sc_at' (ksCurSc s') s'"
              and r'=dc
               in corres_split')

     apply (rule corres_if_split; (solves simp)?)

      apply (clarsimp simp: minRefills_eq_MIN_REFILLS)
      apply (rule corres_guard_imp)
        apply (rule_tac n=n in refillNew_corres)
         apply (clarsimp simp: MIN_REFILLS_def)
        apply (clarsimp simp: valid_refills_number'_def MIN_REFILLS_def)
       apply fastforce
      apply simp

     apply (rule corres_if_split)
       apply (clarsimp simp: sc_relation_def)

      apply (rule corres_symb_exec_l[rotated 2, OF assert_opt_sp]; (solves wpsimp)?)
       apply (rule corres_split'[rotated 2, OF gts_sp isRunnable_sp])
        apply (corressimp corres: isRunnable_corres')
        apply (fastforce simp: sc_relation_def sc_at_pred_n_def obj_at_def
                       intro!: tcb_at_cross Some_to_the)

       apply (rule corres_if_split; (solves simp)?)

        apply (rule_tac Q="is_active_sc' sc_ptr" in corres_cross_add_guard)
         apply (fastforce simp: is_active_sc_rewrite[symmetric] sc_at_pred_n_def obj_at_def
                                is_sc_obj_def vs_all_heap_simps opt_map_def active_sc_def
                        intro!: is_active_sc'_cross)

        apply (rule corres_guard_imp)
          apply (rule_tac n=n in refillUpdate_corres)
           apply (clarsimp simp: MIN_REFILLS_def)
          apply (clarsimp simp: valid_refills_number'_def MIN_REFILLS_def)
         apply clarsimp
         apply (fastforce simp: is_active_sc_rewrite[symmetric] sc_at_pred_n_def obj_at_def
                                vs_all_heap_simps active_sc_def)
        apply (rule valid_objs'_valid_refills')
          apply fastforce
         apply (clarsimp simp: obj_at_simps ko_wp_at'_def)
         apply (rename_tac ko obj, case_tac ko; clarsimp)
        apply simp

      apply (rule corres_guard_imp)
        apply (rule_tac n=n in refillNew_corres)
         apply (clarsimp simp: MIN_REFILLS_def)
        apply (clarsimp simp: valid_refills_number'_def MIN_REFILLS_def)
       apply fastforce
      apply simp

     apply (rule corres_guard_imp)
       apply (rule_tac n=n in refillNew_corres)
        apply (clarsimp simp: MIN_REFILLS_def)
       apply (clarsimp simp: valid_refills_number'_def MIN_REFILLS_def)
      apply fastforce
     apply simp

    apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
    apply (rule hoare_if)
     apply (wps_conj_solves wp: refill_new_valid_sched_action refill_new_valid_release_q)
       apply (wpsimp wp: refill_new_active_sc_valid_refills)
       apply (clarsimp simp: current_time_bounded_def sc_at_pred_n_def obj_at_def)
      apply (wpsimp wp: refill_new_valid_ready_qs)
      apply (clarsimp simp: current_time_bounded_def active_sc_def MIN_REFILLS_def)
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)

    apply (rule hoare_if)
     apply (rule hoare_seq_ext_skip, wpsimp)
     apply (rule hoare_seq_ext[OF _ gts_sp])
     apply (rule hoare_if)

      apply (wps_conj_solves wp: refill_update_valid_sched_action refill_update_invs)
         apply (wpsimp wp: refill_update_active_sc_valid_refills)
         apply (clarsimp simp: current_time_bounded_def sc_at_pred_n_def obj_at_def
                               active_sc_valid_refills_def vs_all_heap_simps active_sc_def)
        apply (wpsimp wp: refill_update_valid_ready_qs)
        apply (simp add: obj_at_kh_kheap_simps pred_map_eq_normalise)
       apply (wpsimp wp: refill_update_valid_release_q)
       apply (clarsimp simp: active_sc_valid_refills_def vs_all_heap_simps)
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

     apply (wps_conj_solves wp: refill_new_valid_sched_action refill_new_valid_release_q)
       apply (wpsimp wp: refill_new_active_sc_valid_refills)
       apply (clarsimp simp: current_time_bounded_def sc_at_pred_n_def obj_at_def)
      apply (wpsimp wp: refill_new_valid_ready_qs)
      apply (clarsimp simp: current_time_bounded_def active_sc_def MIN_REFILLS_def)
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)

     apply (wps_conj_solves wp: refill_new_valid_sched_action refill_new_valid_release_q)
       apply (wpsimp wp: refill_new_active_sc_valid_refills)
       apply (clarsimp simp: current_time_bounded_def sc_at_pred_n_def obj_at_def)
      apply (wpsimp wp: refill_new_valid_ready_qs)
      apply (clarsimp simp: current_time_bounded_def active_sc_def MIN_REFILLS_def)
     apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)

   apply (find_goal \<open>match conclusion in "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q  \<Rightarrow> -\<close>)
   apply (rule hoare_if)
    apply wps_conj_solves
     apply (wpsimp wp: refillNew_invs')
    apply (clarsimp simp: ko_wp_at'_def valid_refills_number'_def minRefills_eq_MIN_REFILLS)
   apply (rule hoare_if)
    apply wps_conj_solves
    apply (rule hoare_seq_ext[OF _ isRunnable_sp])
    apply (rule hoare_if)
     apply (wpsimp wp: refillUpdate_invs')
     apply (clarsimp simp: ko_wp_at'_def valid_refills_number'_def minRefills_eq_MIN_REFILLS)
    apply (wpsimp wp: refillNew_invs')
    apply (clarsimp simp: ko_wp_at'_def valid_refills_number'_def minRefills_eq_MIN_REFILLS)
   apply wps_conj_solves
   apply (wpsimp wp: refillNew_invs')
  apply (clarsimp simp: ko_wp_at'_def valid_refills_number'_def minRefills_eq_MIN_REFILLS)

  apply (clarsimp simp: when_def; intro conjI impI; (solves \<open>clarsimp simp: sc_relation_def\<close>)?)
  apply (rule corres_symb_exec_l[rotated 2, OF assert_opt_sp]; (solves wpsimp)?)

  apply (rule_tac F="sc_tcb sc = Some tcb_ptr" in corres_req)
   apply fastforce

  apply (clarsimp simp: sc_relation_def)
  apply (rule corres_split'[rotated 2, OF gts_sp isRunnable_sp])
   apply (corressimp corres: isRunnable_corres')
   apply (fastforce simp: sc_relation_def sc_at_pred_n_def obj_at_def
                  intro!: tcb_at_cross Some_to_the)

  apply (rule corres_guard_imp)
    apply (rule corres_split[OF schedContextResume_corres])
      apply (rule corres_split[OF getCurThread_corres])
        apply (rule corres_if)
          apply fastforce
         apply (rule rescheduleRequired_corres)
        apply (rule corres_if)
       apply (clarsimp simp: thread_state_relation_def)
         apply (rule possibleSwitchTo_corres')
         apply clarsimp
        apply clarsimp
       apply wpsimp
      apply wpsimp
     apply ((wpsimp wp: hoare_vcg_imp_lift' sched_context_resume_valid_sched_action
            | strengthen valid_objs_valid_tcbs)+)[1]
    apply (rule_tac Q="\<lambda>_. invs'" in hoare_post_imp, fastforce)
    apply (wpsimp wp: schedContextResume_invs')
   apply (fastforce simp: sc_at_pred_n_def obj_at_def schact_is_rct_def
                   intro: valid_sched_action_weak_valid_sched_action)
  apply fastforce
  done

end

end
