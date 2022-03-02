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

lemma cur_vcpu_valid_lift_ct_Q:
  assumes arch_tcb_of_cur_thread: "\<And>P. \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s \<and> Q s\<rbrace>
                                    f \<lbrace>\<lambda>_ s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  and active_cur_vcpu_of: "\<And>P. \<lbrace>\<lambda>s. P (active_cur_vcpu_of s) \<and> Q s\<rbrace>
                                    f \<lbrace>\<lambda>_ s. P (active_cur_vcpu_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ active_cur_vcpu_of] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemmas cur_vcpu_valid_lift_ct = cur_vcpu_valid_lift_ct_Q[where Q=\<top>, simplified]

lemma cur_vcpu_valid_lift:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>; \<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>;
    \<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>\<rbrakk>
   \<Longrightarrow> f \<lbrace>cur_vcpu_valid\<rbrace> "
  apply (rule cur_vcpu_valid_lift_ct)
   apply (rule_tac f=cur_thread in hoare_lift_Pf3)
   apply fastforce+
  done

lemma cur_vcpu_valid_lift_weak_ct_Q':
  assumes arch_tcb_of_cur_thread: "\<And>P. \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s \<and> Q s\<rbrace>
                                        f \<lbrace>\<lambda>_ s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  and arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda> _s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ arch_state] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemmas cur_vcpu_valid_lift_weak_ct = cur_vcpu_valid_lift_weak_ct_Q'[where Q=\<top>, simplified]

lemma cur_vcpu_valid_lift_weak:
  "\<lbrakk>\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>; \<And>P t. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>; \<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>\<rbrakk>
   \<Longrightarrow> f \<lbrace>cur_vcpu_valid\<rbrace> "
  apply (rule cur_vcpu_valid_lift_weak_ct)
   apply (rule_tac f=cur_thread in hoare_lift_Pf3)
   apply fastforce+
  done

lemma cur_vcpu_valid_lift_cur_thread_update:
  assumes arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>"
  and arch_state: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ arch_state] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

crunches as_user
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def)

lemma as_user_cur_vcpu_valid[wp]:
  "as_user tptr f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (rule cur_vcpu_valid_lift)
   apply (rule hoare_weaken_pre)
   apply (wpsimp wp: as_user_pred_tcb_at | wps)+
  done

lemma machine_state_update_active_cur_vcpu_of[simp]:
  "P (active_cur_vcpu_of (s\<lparr>machine_state := ms\<rparr>)) = P (active_cur_vcpu_of s)"
  by (fastforce simp: active_cur_vcpu_of_def)

crunches do_machine_op
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  and cur_vcpu_valid[wp]: cur_vcpu_valid
  and cur_vcpu_valid_cur_thread_update[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  (wp: cur_vcpu_valid_lift_cur_thread_update cur_vcpu_valid_lift crunch_wps)

lemma cur_vcpu_valid_vcpu_update[simp]:
  "vcpu_at vr s \<Longrightarrow> cur_vcpu_valid (s\<lparr>kheap := kheap s(vr \<mapsto> ArchObj (VCPU f))\<rparr>) = cur_vcpu_valid s"
  by (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)

crunches vcpu_save_reg, vcpu_write_reg, save_virt_timer, vgic_update, vcpu_disable
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: set_vcpu_wp)

lemma set_vcpu_arch_tcb_at_cur_thread[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

crunches vcpu_disable, vcpu_restore, vcpu_save, set_vm_root
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: crunch_wps)

crunches vcpu_update, do_machine_op, invalidate_hw_asid_entry, invalidate_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

lemma vcpu_save_reg_active_cur_vcpu_of[wp]:
  "vcpu_save_reg vr reg \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: vcpu_save_reg_def)

crunches vcpu_restore, do_machine_op, vcpu_save_reg, vgic_update, save_virt_timer,
         vcpu_save_reg_range, vgic_update_lr, vcpu_enable, vcpu_save
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def crunch_simps)

lemma switch_vcpu_cur_vcpu_valid_cur_thread_update[wp]:
  "\<lbrace>\<lambda>s. arch_tcb_at (\<lambda>a. itcb_vcpu a = v) t s\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: vcpu_switch_def)
  apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  by fastforce

crunches store_hw_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def)

lemma find_free_hw_asid_active_cur_vcpu_of[wp]:
  "find_free_hw_asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  apply (clarsimp simp: find_free_hw_asid_def find_pd_for_asid_assert_def)
  apply (intro hoare_seq_ext[OF _ gets_inv])
  apply (clarsimp split: option.splits)
  apply (rule hoare_seq_ext_skip, wpsimp)+
   apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)
  apply (wpsimp simp: find_pd_for_asid_assert_def)
  done

lemma arm_context_switch_active_cur_vcpu_of[wp]:
  "arm_context_switch pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  apply (clarsimp simp: arm_context_switch_def get_hw_asid_def)
  by (wpsimp wp: load_hw_asid_wp)

lemma set_vm_root_active_cur_vcpu_of[wp]:
  "set_vm_root tcb \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: set_vm_root_def find_pd_for_asid_def wp: get_cap_wp)

crunches set_vm_root
  for cur_vcpu_valid_cur_thread_update[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  (wp: cur_vcpu_valid_lift_cur_thread_update)

lemma arch_switch_to_thread_cur_vcpu_valid_cur_thread_update[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_thread_def
  apply wpsimp
  by (fastforce simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def get_tcb_def
               split: option.splits kernel_object.splits)

lemma switch_to_thread_cur_vcpu_valid[wp]:
  "switch_to_thread t \<lbrace>cur_vcpu_valid\<rbrace>"
  unfolding switch_to_thread_def
  by (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)

lemma arch_switch_to_idle_thread_cur_vcpu_valid_cur_thread_update[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> valid_idle s \<and> t = idle_thread s\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  unfolding arch_switch_to_idle_thread_def
  apply wpsimp
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_arch_idle_def)

lemma switch_to_idle_thread_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def)

lemma dissociate_vcpu_tcb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: dissociate_vcpu_tcb_def)
  apply (clarsimp simp: arch_thread_get_def)
  apply (rule hoare_seq_ext[OF _ gets_the_sp])
  apply (clarsimp simp: get_vcpu_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
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
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                          get_tcb_def
                   split: if_splits option.splits bool.splits)
  apply (clarsimp simp: vcpu_invalidate_active_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac cur_vcpu)
  apply (case_tac cur_vcpu; clarsimp)
   apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (rename_tac active)
  apply (case_tac active; clarsimp)
   prefer 2
   apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                   split: if_splits)
  apply (rule_tac B="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)
                           \<and> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = Some vr) t s
                           \<and> arm_current_vcpu (arch_state s) = Some (vr, True)"
               in hoare_seq_ext[rotated])
   apply (clarsimp simp: pred_conj_def)
   apply wpsimp
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def get_tcb_def
                   split: kernel_object.splits option.splits)
  apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                 split: if_splits kernel_object.splits option.splits)
  apply (prop_tac "(t, HypTCBRef) \<in> hyp_refs_of (ArchObj (VCPU v))")
   apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def)
   apply (fastforce split: option.splits)
  apply (fastforce simp: sym_refs_def state_hyp_refs_of_def vcpu_tcb_refs_def
                  split: option.splits)
  done

lemma associate_vcpu_tcb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: associate_vcpu_tcb_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: dissociate_vcpu_tcb_cur_vcpu_valid)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: dissociate_vcpu_tcb_cur_vcpu_valid)
  apply (rule_tac P="\<lambda>s. t \<noteq> cur_thread s" in hoare_pre_tautI)
   apply (subst bind_assoc[symmetric])
   apply (rule_tac B="\<lambda>_ s. cur_vcpu_valid s \<and> t \<noteq> cur_thread s" in hoare_seq_ext[rotated])
    apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
    apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp simp: when_def)
   apply (intro conjI impI)
    apply (fastforce intro: hoare_weaken_pre hoare_pre_cont)
   apply wpsimp
  apply (rule_tac Q="\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>) \<and> t = cur_thread s" in hoare_post_imp)
   apply fastforce
  apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def)
  done

lemma set_thread_state_arch_tcb_at[wp]:
  "set_thread_state ts ref \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches set_thread_state
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches activate_thread
  for cur_vcpu_valid[wp]: cur_vcpu_valid

crunches tcb_sched_action
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def)

crunches tcb_sched_action
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches schedule_choose_new_thread
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (simp: crunch_simps cur_vcpu_valid_def active_cur_vcpu_of_def wp: crunch_wps)

lemma schedule_cur_vcpu_valid_det_ext[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   (schedule :: (unit,det_ext) s_monad)
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  unfolding schedule_def schedule_switch_thread_fastfail_def ethread_get_when_def ethread_get_def
  by (wpsimp wp: hoare_drop_imps gts_wp )

lemma schedule_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   (schedule :: (unit,unit) s_monad)
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  unfolding schedule_def allActiveTCBs_def
  by (wpsimp wp: alternative_wp select_wp)

crunches cancel_all_ipc, blocked_cancel_ipc, unbind_maybe_notification, cancel_all_signals,
         bind_notification, fast_finalise, deleted_irq_handler, post_cap_deletion, cap_delete_one,
         reply_cancel_ipc, cancel_ipc, update_waiting_ntfn, send_signal, send_ipc, send_fault_ipc,
         receive_ipc, handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault,
         send_signal, do_reply_transfer, unbind_notification, suspend, cap_swap, bind_notification,
         restart, reschedule_required, possible_switch_to, thread_set_priority, reply_from_kernel
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: mapM_x_wp_inv thread_set.arch_state select_wp crunch_wps
   simp: crunch_simps possible_switch_to_def reschedule_required_def)

lemma do_unbind_notification_arch_tcb_at[wp]:
  "do_unbind_notification ntfnptr ntfn tcbptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding set_bound_notification_def set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp get_simple_ko_wp thread_get_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma unbind_notification_arch_tcb_at[wp]:
  "unbind_notification tcb \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding unbind_notification_def
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  by wpsimp

lemma bind_notification_arch_tcb_at[wp]:
  "bind_notification tcbptr ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding bind_notification_def set_bound_notification_def set_simple_ko_def
  apply (wpsimp wp: set_object_wp get_object_wp get_simple_ko_wp)
  by (fastforce simp: pred_tcb_at_def obj_at_def get_tcb_def)

lemma unbind_maybe_notification_arch_tcb_at[wp]:
  "unbind_maybe_notification ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding unbind_maybe_notification_def
  by wpsimp

crunches blocked_cancel_ipc, cap_delete_one, cancel_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma reply_cancel_ipc_arch_tcb_at[wp]:
  "reply_cancel_ipc ntfnptr \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding reply_cancel_ipc_def thread_set_def
  apply (wpsimp wp: set_object_wp select_wp)
  by (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)

crunches cancel_ipc, send_ipc, receive_ipc
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

lemma send_fault_ipc_arch_tcb_at[wp]:
  "send_fault_ipc tptr fault \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding send_fault_ipc_def thread_set_def Let_def
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE, solves wpsimp)+
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunches handle_fault, handle_interrupt, handle_vm_fault, handle_hypervisor_fault, send_signal
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (wp: cur_vcpu_valid_lift mapM_x_wp_inv crunch_wps)

crunches reschedule_required, set_scheduler_action, tcb_sched_action
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def set_tcb_queue_def
         get_tcb_queue_def)

lemma do_reply_transfer_arch_tcb_at[wp]:
  "do_reply_transfer sender receiver slot grant \<lbrace>arch_tcb_at P t\<rbrace>"
  unfolding do_reply_transfer_def thread_set_def
  apply (rule hoare_seq_ext_skip, solves wpsimp, clarsimp?)+
  apply (rename_tac fault_opt)
  apply (case_tac fault_opt; clarsimp)
   apply wpsimp
  apply (rule hoare_seq_ext_skip, solves wpsimp)+
  apply (wpsimp wp: set_object_wp hoare_drop_imps | intro conjI impI)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunches send_ipc, send_fault_ipc, receive_ipc, handle_fault, handle_interrupt, handle_vm_fault,
         handle_hypervisor_fault, send_signal, do_reply_transfer, cancel_all_ipc,
         cancel_all_signals, unbind_maybe_notification, suspend,
         deleting_irq_handler, unbind_notification
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak crunch_wps)

crunches init_arch_objects, reset_untyped_cap
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps preemption_point_inv hoare_unless_wp mapME_x_wp'
   simp:  crunch_simps)

crunches invoke_untyped
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps mapME_x_inv_wp preemption_point_inv  simp: crunch_simps  mapM_x_def[symmetric])

lemma invoke_untyped_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> invs s \<and>  valid_untyped_inv ui s \<and> ct_active s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule cur_vcpu_valid_lift_weak_ct_Q')
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule invoke_untyped_pred_tcb_at[where proj=itcb_arch])
    apply clarsimp
    apply wpsimp
   apply (wpsimp wp: invoke_untyped_Q)
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma cur_vcpu_valid_is_original_cap_update[simp]:
  "cur_vcpu_valid (is_original_cap_update f s) = cur_vcpu_valid s"
  by (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)

crunches cap_insert, cap_move
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches suspend, unbind_notification, cap_swap_for_delete
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: crunch_wps thread_set_hyp_refs_trivial select_wp simp: crunch_simps)

lemma prepare_thread_delete_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   prepare_thread_delete p
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  unfolding prepare_thread_delete_def arch_thread_get_def
  by (wpsimp wp: dissociate_vcpu_tcb_cur_vcpu_valid)

lemma active_cur_vcpu_of_arm_asid_table_update[simp]:
  "P (active_cur_vcpu_of (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>))
   = P (active_cur_vcpu_of s)"
  by (clarsimp simp: active_cur_vcpu_of_def)

crunches delete_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches store_pte, store_pde, set_asid_pool
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps active_cur_vcpu_of_def)

crunches unmap_page, unmap_page_table, delete_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps cur_vcpu_valid_lift)

crunches delete_asid_pool, unmap_page, unmap_page_table, delete_asid
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift)

crunches vcpu_finalise, arch_finalise_cap, finalise_cap
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (simp: crunch_simps)

crunches prepare_thread_delete, deleting_irq_handler, delete_asid_pool, flush_page
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma store_pte_state_hyp_refs_of[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: state_hyp_refs_of_def sym_refs_def obj_at_def)

lemma unmap_page_state_hyp_refs_of[wp]:
  "unmap_page pgsz asid vptr pptr \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding unmap_page_def lookup_pt_slot_def find_pd_for_asid_def
  by (wpsimp wp: hoare_drop_imps mapM_wp_inv get_pde_wp store_pde_state_hyp_refs_of)

crunches flush_table, page_table_mapped, delete_asid, vcpu_finalise, unmap_page_table, finalise_cap
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma preemption_point_state_hyp_refs_of[wp]:
  "preemption_point \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp wp: preemption_point_inv)

lemma preemption_point_cur_vcpu_valid[wp]:
  "preemption_point \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (wpsimp wp: preemption_point_inv)
    by (clarsimp simp: cur_vcpu_valid_def trans_state_def pred_tcb_at_def obj_at_def
                       active_cur_vcpu_of_def)+

crunches cap_swap_for_delete, empty_slot
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

lemma rec_del_state_hyp_refs_of[wp]:
  "rec_del call \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  by (rule rec_del_preservation; (solves wpsimp)?)

crunches cap_delete
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma rec_del_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_ s. cur_vcpu_valid s\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (rule rec_del_preservation; (solves wpsimp)?)

crunches cap_delete
  for cur_vcpu_valid[wp]: cur_vcpu_valid

lemma cap_revoke_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>_ s. cur_vcpu_valid s\<rbrace>"
  (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre" in hoare_post_imp, fastforce)
  by (wpsimp wp: cap_revoke_preservation)

crunches cancel_badged_sends, invoke_irq_control, invoke_irq_handler
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and arch_State[wp]: "\<lambda>s. P (arch_state s)"
  (wp: filterM_preserved)

crunches store_pte, set_cap, set_mrs
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

crunches perform_page_table_invocation, perform_page_directory_invocation, perform_page_invocation,
         perform_asid_pool_invocation, invoke_vcpu_inject_irq, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunches cancel_badged_sends, invoke_irq_control, invoke_irq_handler, invoke_vcpu_inject_irq,
         bind_notification
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches perform_asid_pool_invocation, perform_page_table_invocation,
         perform_page_directory_invocation, perform_page_invocation, invoke_vcpu_read_register,
         invoke_vcpu_write_register, invoke_vcpu_ack_vppi
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift)

lemma invoke_cnode_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   invoke_cnode iv
   \<lbrace>\<lambda>_ s. cur_vcpu_valid s\<rbrace>"
  unfolding invoke_cnode_def
  apply (cases iv; clarsimp)
  by (wpsimp | intro conjI impI | wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)+

lemma cur_vcpu_valid_trans_state[simp]:
  "cur_vcpu_valid (trans_state f s) = cur_vcpu_valid s"
  by (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)

crunches restart, reschedule_required, possible_switch_to, thread_set_priority
  for arch_tcb_at[wp]: "arch_tcb_at P t"
  (simp: possible_switch_to_def set_tcb_queue_def get_tcb_queue_def)

crunches restart, reschedule_required, possible_switch_to, thread_set_priority
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches restart, arch_post_modify_registers, arch_get_sanitise_register_info
  for cur_vcpu_valid[wp]: cur_vcpu_valid

lemma thread_set_cur_vcpu_valid:
  "(\<And>tcb. tcb_arch (f tcb) = tcb_arch tcb) \<Longrightarrow> thread_set f tptr \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (rule cur_vcpu_valid_lift_weak)
    unfolding thread_set_def
    apply (wpsimp wp: set_object_wp)+
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def get_tcb_def)
  apply wpsimp
  done

lemma fault_handler_update_cur_vcpu_valid[wp]:
  "option_update_thread thread (tcb_fault_handler_update \<circ> f) opt \<lbrace>cur_vcpu_valid\<rbrace>"
  unfolding option_update_thread_def
  by (wpsimp wp: thread_set_cur_vcpu_valid)

lemma fault_handler_update_state_hyp_refs_of[wp]:
  "option_update_thread thread (tcb_fault_handler_update \<circ> f) opt \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding option_update_thread_def
  by (fastforce intro: thread_set_hyp_refs_trivial split: option.splits)

crunches set_mcpriority, set_priority
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (simp: set_priority_def)

lemma ethread_set_hyp_refs[wp]:
  "ethread_set f t \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  done

crunches tcb_sched_action, possible_switch_to, set_scheduler_action, reschedule_required
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: thread_set_hyp_refs_trivial
   simp: tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def possible_switch_to_def
         reschedule_required_def set_scheduler_action_def)

crunches set_mcpriority, set_priority
  for state_hyp_refs_of[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (wp: thread_set_hyp_refs_trivial simp: set_priority_def thread_set_priority_def)

lemma invoke_tcb_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   invoke_tcb iv
   \<lbrace>\<lambda>_ s. cur_vcpu_valid s\<rbrace>"
  apply (cases iv; clarsimp; (solves \<open>wpsimp wp: mapM_x_wp_inv\<close>)?)
   defer
   subgoal for tcb_ptr ntfn_ptr_opt
     by (case_tac ntfn_ptr_opt; wpsimp)
  \<comment> \<open>ThreadControl\<close>
  apply (rename_tac target slot faultep mcp priority croot vroot buffer)
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE, solves wpsimp)+
  apply (rule hoare_seq_ext_skipE)
   apply (case_tac croot; clarsimp)
    apply wpsimp
   apply (rule_tac Q="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)"
               and E="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)"
                in hoare_post_impErr)
     apply (rule hoare_seq_ext_skipE)
      apply (wpsimp wp: cap_delete_cur_vcpu_valid)
     apply (wpsimp wp: check_cap_inv)
    apply simp
   apply simp
  apply (rule hoare_seq_ext_skipE)
   apply (case_tac vroot; clarsimp)
    apply wpsimp
   apply (rule_tac Q="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)"
               and E="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)"
                in hoare_post_impErr)
     apply (rule hoare_seq_ext_skipE)
      apply (wpsimp wp: cap_delete_cur_vcpu_valid)
     apply (wpsimp wp: check_cap_inv)
    apply simp
   apply simp
  apply (rule hoare_seq_ext_skipE)
   apply (case_tac buffer; clarsimp)
    apply wpsimp
   apply (rule hoare_seq_ext_skipE)
    apply (wpsimp wp: cap_delete_cur_vcpu_valid)
   apply (wpsimp wp: check_cap_inv hoare_drop_imps thread_set_hyp_refs_trivial thread_set_cur_vcpu_valid)
  apply wpsimp
  done

crunches invoke_domain
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and arch_tcb_at[wp]: "\<lambda>s. arch_tcb_at P t s"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

crunches perform_asid_control_invocation
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s )"
  and active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (simp: active_cur_vcpu_of_def)

lemma perform_asid_control_invocation_cur_vcpu_valid:
  "\<lbrace>cur_vcpu_valid and invs and valid_aci iv and ct_active\<rbrace>
   perform_asid_control_invocation iv
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule cur_vcpu_valid_lift_ct_Q)
    apply (rule_tac f=cur_thread in hoare_lift_Pf2)
     apply (rule perform_asid_control_invocation_pred_tcb_at[where proj=itcb_arch])
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma perform_vcpu_invocation_cur_vcpu_valid:
  "\<lbrace>cur_vcpu_valid and invs\<rbrace>
   perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  unfolding perform_vcpu_invocation_def
  by (wpsimp wp: associate_vcpu_tcb_cur_vcpu_valid)

lemma perform_invocation_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and invs and valid_invocation i and ct_active\<rbrace>
   perform_invocation blocking call i
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (case_tac i, simp_all; (solves wpsimp)?)
   apply (wpsimp wp: invoke_untyped_cur_vcpu_valid)
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_vcpu_invocation_cur_vcpu_valid perform_asid_control_invocation_cur_vcpu_valid)
  apply (fastforce simp: valid_arch_inv_def)
  done

crunches reply_from_kernel, receive_signal
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift_weak)

lemma handle_invocation_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and invs and ct_active\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  unfolding handle_invocation_def
  by (wp syscall_valid set_thread_state_ct_st
               | simp add: split_def | wpc
               | wp (once) hoare_drop_imps)+
     (auto simp: ct_in_state_def elim: st_tcb_ex_cap)

lemma handle_recv_cur_vcpu_valid[wp]:
  "handle_recv is_blocking \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper delete_caller_cap_def)
  by (wpsimp wp: hoare_drop_imps)

lemma handle_event_cur_vcpu_valid:
  "\<lbrace>cur_vcpu_valid and invs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   handle_event ev
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (cases ev; clarsimp; (solves wpsimp)?)
  unfolding handle_call_def handle_send_def handle_reply_def handle_yield_def
  by (wpsimp wp: get_cap_wp)+

lemma call_kernel_cur_vcpu_valid:
  "\<lbrace>cur_vcpu_valid and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   (call_kernel e) :: (unit, unit) s_monad
   \<lbrace>\<lambda>_ . cur_vcpu_valid\<rbrace>"
  unfolding call_kernel_def
  apply (simp flip: bind_assoc)
  by (wpsimp wp: handle_event_cur_vcpu_valid hoare_vcg_if_lift2 hoare_drop_imps
      | strengthen invs_valid_idle)+

lemma call_kernel_cur_vcpu_valid_det_ext:
  "\<lbrace>cur_vcpu_valid and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   (call_kernel e) :: (unit, det_ext) s_monad
   \<lbrace>\<lambda>_ . cur_vcpu_valid\<rbrace>"
  unfolding call_kernel_def
  apply (simp flip: bind_assoc)
  by (wpsimp wp: handle_event_cur_vcpu_valid hoare_vcg_if_lift2 hoare_drop_imps
      | strengthen invs_valid_idle)+

end

end