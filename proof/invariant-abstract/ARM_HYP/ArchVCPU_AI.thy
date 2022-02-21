(*
 * Copyright 2022, ???
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVCPU_AI
imports AInvs
begin

context Arch begin global_naming ARM_HYP (*FIXME: arch_split*)

definition active_cur_vcpu_of :: "'z::state_ext state \<Rightarrow> obj_ref option" where
  "active_cur_vcpu_of s \<equiv>
     case arm_current_vcpu (arch_state s) of Some (vr, True) \<Rightarrow> Some vr
                                           | _  \<Rightarrow> None"

abbreviation "arch_tcb_at \<equiv> pred_tcb_at itcb_arch"

definition cur_vcpu_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "cur_vcpu_valid s \<equiv> arch_tcb_at (\<lambda>a. itcb_vcpu a = active_cur_vcpu_of s) (cur_thread s) s"

lemma cur_vcpu_valid_lift:
  assumes arch_state: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  and arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  shows "f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ arch_state] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemma cur_vcpu_valid_lift2:
  assumes arch_state: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  and arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ arch_state] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

\<comment> \<open>For forward reasoning in Hoare proofs, these lemmas allow skipping over the
    left-hand-side of monadic bind, while keeping the same precondition.\<close>
lemmas hoare_seq_ext_skip
  = hoare_seq_ext[where B="\<lambda>_. A" and A=A for A, rotated]

lemma as_user_cur_vcpu_valid[wp]:
  "as_user tptr f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: as_user_def active_cur_vcpu_of_def)
  apply (rule cur_vcpu_valid_lift)
apply (wpsimp wp: select_f_wp set_object_wp)
apply (fastforce simp: active_cur_vcpu_of_def)
apply (wpsimp wp: set_object_wp)
apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
done

lemma machine_state_update_active_cur_vcpu_of[simp]:
  "P (active_cur_vcpu_of s) \<Longrightarrow> P (active_cur_vcpu_of (s\<lparr>machine_state := b\<rparr>))"
  by (fastforce simp: active_cur_vcpu_of_def)

crunches do_machine_op
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  and cur_vcpu_valid'[wp]: "\<lambda>s. cur_vcpu_valid s"
  (wp: cur_vcpu_valid_lift2 cur_vcpu_valid_lift crunch_wps)

lemma vcpu_save_reg_cur_vcpu_valid[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>"
  apply (clarsimp simp: vcpu_save_reg_def vcpu_update_def)
apply (rule hoare_seq_ext_skip, wpsimp)
apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
done

lemma vcpu_write_reg_cur_vcpu_valid[wp]:
  "vcpu_write_reg vr reg val \<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>"
  apply (clarsimp simp: vcpu_write_reg_def vcpu_update_def)
apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
done


lemma save_virt_timer_cur_vcpu_valid[wp]:
  "save_virt_timer vcpu_timer \<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>"
apply (clarsimp simp: save_virt_timer_def vcpu_update_def)
apply (rule hoare_seq_ext_skip, wpsimp)+
apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
done

lemma vgic_update_cur_vcpu_valid[wp]:
  "vgic_update vr f \<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>"
apply (clarsimp simp: vgic_update_def vcpu_update_def)
apply (rule hoare_seq_ext_skip, wpsimp)+
apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
done

lemma vcpu_disable_cur_vcpu_valid[wp]:
  "vcpu_disable vo \<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>"
apply (clarsimp simp: vcpu_disable_def)
apply (rule hoare_seq_ext_skip, wpsimp)+
apply wpsimp
done



crunches vcpu_disable
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid s"
  (wp: cur_vcpu_valid_lift crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps)

crunches do_machine_op
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: cur_vcpu_valid_lift crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps)

lemma set_vcpu_arch_tcb_at_cur_thread[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
done

crunches vcpu_disable, vcpu_restore, vcpu_save_reg_range, vgic_update_lr, vcpu_save, set_vm_root
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps active_cur_vcpu_of_def)

crunches vcpu_update, do_machine_op, invalidate_hw_asid_entry, invalidate_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps active_cur_vcpu_of_def)

crunches vcpu_restore, do_machine_op, vcpu_save_reg, vgic_update, save_virt_timer
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid s"
  (wp: cur_vcpu_valid_lift crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def simp: crunch_simps)

lemma vcpu_save_reg_active_cur_vcpu_of[wp]:
  "vcpu_save_reg a b \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: vcpu_save_reg_def)

crunches vcpu_save_reg_range, vcpu_save_reg_range, vgic_update_lr, vcpu_enable, vcpu_save
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid s"
  (wp: cur_vcpu_valid_lift crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def simp: crunch_simps)

lemma switch_vcpu_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. arch_tcb_at (\<lambda>a. itcb_vcpu a = v) t s\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: vcpu_switch_def)
  apply (cases v; clarsimp)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (case_tac x; clarsimp)
apply wpsimp
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)
apply (clarsimp simp: when_def)
apply (intro conjI impI)
prefer 2
apply wpsimp

apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)
apply (rule hoare_seq_ext_skip)

apply wpsimp

apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)

apply (rule hoare_seq_ext[OF _ gets_sp])
apply (case_tac x; clarsimp)
apply (rule hoare_seq_ext_skip, wpsimp)
apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)

apply (intro conjI impI)
apply (rule hoare_seq_ext_skip, wpsimp)
apply (rule hoare_seq_ext_skip, wpsimp)

apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)

apply (clarsimp simp: when_def)
apply (intro conjI impI)
prefer 2
apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)

apply (rule hoare_seq_ext_skip, wpsimp)
apply (rule hoare_seq_ext_skip, wpsimp)

apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)

done

lemma store_hw_asid_active_cur_vcpu_of[wp]:
  "store_hw_asid pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
apply (clarsimp simp: store_hw_asid_def find_pd_for_asid_assert_def active_cur_vcpu_of_def)
apply (wpsimp simp: find_pd_for_asid_assert_def)
done

lemma asdf[wp]:
  "find_free_hw_asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
apply (clarsimp simp: find_free_hw_asid_def find_pd_for_asid_assert_def)
apply (intro hoare_seq_ext[OF _ gets_inv])
apply (clarsimp split: option.splits)
apply (rule hoare_seq_ext_skip, wpsimp)+
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)
apply (wpsimp simp: find_pd_for_asid_assert_def )
done

lemma arm_context_switch_active_cur_vcpu_of[wp]:
  "arm_context_switch pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
apply (clarsimp simp: arm_context_switch_def get_hw_asid_def)
apply (wpsimp wp: load_hw_asid_wp)
done

lemma set_vm_root_active_cur_vcpu_of[wp]:
  "set_vm_root a \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
apply (clarsimp simp: set_vm_root_def find_pd_for_asid_def)
apply (wpsimp simp: find_pd_for_asid_def wp: get_cap_wp)
done

crunches set_vm_root
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  (wp: cur_vcpu_valid_lift2 crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def simp: crunch_simps)

lemma arch_switch_to_thread_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: arch_switch_to_thread_def)
apply (rule hoare_seq_ext[OF _ gets_the_sp])
apply wpsimp
apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def get_tcb_def)
\<comment> \<open>apply (intro conjI)\<close>
apply (case_tac "kheap s t"; clarsimp)
apply (case_tac a; clarsimp)

done

lemma no_fail_do_extended_op:
  "\<lbrakk>no_fail P f; empty_fail f\<rbrakk> \<Longrightarrow> no_fail P (do_extended_op f)"
apply (clarsimp simp: no_fail_def do_extended_op_def get_def in_monad select_f_def mk_ef_def modify_def
put_def bind_def)
apply (intro conjI)
  apply fastforce
apply (clarsimp simp: empty_fail_def)
  apply (metis wrap_ext_op_det_ext_ext_def)
apply (clarsimp simp: empty_fail_def)
  apply (metis wrap_ext_op_det_ext_ext_def)
done

\<comment> \<open>lemma asdf2:
  "\<lbrakk>no_fail \<top> f; empty_fail f\<rbrakk> \<Longrightarrow>   do     y <- do_extended_op f;
          modify (cur_thread_update (\<lambda>_. t))
       od  =  do modify (cur_thread_update (\<lambda>_. t));
       do_extended_op f
       od "
thm dxo_noop
apply (frule (1) no_fail_do_extended_op)
apply (clarsimp simp: tcb_sched_action_extended.dxo_eq)
apply (auto simp: bind_def'  get_def select_f_def mk_ef_def
modify_def return_def put_def tcb_sched_action_def ethread_get_def gets_the_def gets_def assert_opt_def
get_etcb_def get_tcb_queue_def set_tcb_queue_def tcb_sched_dequeue_def
wrap_ext_op_det_ext_ext_def wrap_ext_op_unit_def dxo_noop)
apply (rule ext)
apply safe
apply (clarsimp simp:  wrap_ext_op_det_ext_ext_def wrap_ext_op_unit_def no_fail_def empty_fail_def)
apply (clarsimp simp: do_extended_op_def select_f_def in_monad mk_ef_def bind_def get_def
modify_def put_def)

find_theorems wrap_ext_op
find_theorems (68) do_extended_op\<close>

lemma switch_to_thread_cur_vcpu_valid:
  "switch_to_thread t \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: switch_to_thread_def)
apply (rule hoare_seq_ext[OF _ get_sp])
apply (rule hoare_seq_ext[OF _ assert_sp])
apply (subst bind_assoc[symmetric])
apply (wp modify_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def active_cur_vcpu_of_def get_tcb_def obj_at_def)

find_theorems modify valid
find_theorems switch_to_thread
find_theorems monadic_rewrite
find_theorems  (100) modify -valid
term oblivious
apply wpsimp
apply (wpsimp simp: cur_vcpu_valid_def)
done

lemma arch_switch_to_idle_thread_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> valid_idle s \<and> t = idle_thread s\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: arch_switch_to_idle_thread_def)
apply wpsimp
apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_arch_idle_def)
done

lemma switch_to_idle_thread_cur_vcpu_valid:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: switch_to_idle_thread_def)
apply (wpsimp wp:)
done



\<comment> \<open>A variant which works nicely with subgoals that do not contain schematics\<close>
lemmas hoare_vcg_conj_lift_pre_fix
  = hoare_vcg_conj_lift[where P=R and P'=R for R, simplified]


lemma dissociate_vcpu_ccb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: dissociate_vcpu_tcb_def)
apply (clarsimp simp: arch_thread_get_def)
apply (rule hoare_seq_ext[OF _ gets_the_sp])
apply (clarsimp simp: get_vcpu_def bind_assoc)
apply (rule hoare_seq_ext[OF _ get_object_sp])
apply (case_tac x; clarsimp)
apply (case_tac x5; clarsimp)
apply (rule hoare_seq_ext[OF _ assert_sp])
apply (rule hoare_seq_ext[OF _ gets_sp])

apply (simp flip: bind_assoc)
apply (rule hoare_seq_ext)
apply wpsimp
apply (simp add: bind_assoc)

apply (clarsimp simp: when_def)
apply (intro conjI impI)

prefer 2
apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
apply (intro conjI impI allI)
apply (clarsimp split: if_splits)
apply (clarsimp split: option.splits)

apply (case_tac ba; clarsimp)
apply fastforce
apply (clarsimp split: if_splits)


apply (clarsimp simp: vcpu_invalidate_active_def bind_assoc)
apply (rule hoare_seq_ext[OF _ gets_sp])

apply (case_tac x; clarsimp)
apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (case_tac b; clarsimp)
prefer 2
apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
apply (clarsimp split: if_splits)


find_theorems (100) vcpu_disable

apply (rule_tac B="\<lambda>_. (\<lambda>s.
                  cur_vcpu_valid s \<and>
                  sym_refs (state_hyp_refs_of s) \<and> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = Some vr) t s
) and
             (\<lambda>s. arm_current_vcpu (arch_state s) = Some (vr, a)) and
             (\<lambda>s. arm_current_vcpu (arch_state s) = Some (aa, True))" in hoare_seq_ext[rotated])

apply (clarsimp simp: pred_conj_def)
apply (intro hoare_vcg_conj_lift_pre_fix)

apply wpsimp
apply wpsimp
apply wpsimp

apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
apply (case_tac "kheap s t"; clarsimp)
apply (case_tac aa; clarsimp)
apply wpsimp
apply wpsimp

apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
apply (clarsimp split: if_splits)
apply (case_tac "kheap s t"; clarsimp)
\<comment> \<open>apply (case_tac aa; clarsimp)\<close>
apply (prop_tac "(vr, TCBHypRef) \<in> hyp_refs_of (TCB tcb)")
  apply fastforce

apply (prop_tac "(t, HypTCBRef) \<in> hyp_refs_of (ArchObj (VCPU v))")

apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def hyp_refs_of_def refs_of_a_def


 split: option.splits
)

apply (drule_tac x="t" in spec)
apply clarsimp
apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def hyp_refs_of_def refs_of_a_def


 split: option.splits
)
apply (drule_tac x="cur_thread s" in spec)
apply clarsimp
apply (clarsimp simp: vcpu_tcb_refs_def split: option.splits)

done

lemma associate_vcpu_tcb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
apply (clarsimp simp: associate_vcpu_tcb_def )
apply (clarsimp simp: arch_thread_get_def)
apply (rule hoare_seq_ext[OF _ gets_the_sp])
apply (rule_tac B="\<lambda>_. ?pre" in hoare_seq_ext[rotated])
apply (wpsimp wp: dissociate_vcpu_ccb_cur_vcpu_valid)
apply (rule hoare_seq_ext_skip, wpsimp)
apply (rule_tac B="\<lambda>_. ?pre" in hoare_seq_ext[rotated])
apply (wpsimp wp: dissociate_vcpu_ccb_cur_vcpu_valid)

apply (rule_tac P="\<lambda>s. t = cur_thread s" in hoare_pre_tautI)
prefer 2

apply (subst bind_assoc[symmetric])
apply (rule_tac B="\<lambda>_ s. cur_vcpu_valid s \<and> t \<noteq> cur_thread s" in hoare_seq_ext[rotated])

apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (clarsimp simp: when_def)
apply (intro conjI impI)
apply (rule hoare_weaken_pre)
apply (rule hoare_pre_cont)
  apply fastforce
apply wpsimp
apply (rule_tac Q="\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>) \<and> t= cur_thread s" in hoare_post_imp)
  apply fastforce
apply (intro hoare_vcg_conj_lift_pre_fix)
prefer 2

apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)

apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
get_tcb_def)
done


end

end