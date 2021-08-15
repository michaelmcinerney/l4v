(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetSchedDomainTime_AI
imports "../DetSchedDomainTime_AI"
begin

context Arch begin global_naming ARM

named_theorems DetSchedDomainTime_AI_assms

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply,
  arch_invoke_irq_control, handle_vm_fault, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, make_arch_fault_msg,init_arch_objects,
  arch_post_modify_registers, arch_post_cap_deletion, arch_invoke_irq_handler
  "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps)

crunches arch_finalise_cap
  for domain_time_scheduler_action_inv[wp, DetSchedDomainTime_AI_assms]:
        "\<lambda>s. P (domain_time s) (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

crunches arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
         handle_arch_fault_reply, init_arch_objects, arch_invoke_irq_control, handle_vm_fault,
         prepare_thread_delete, handle_hypervisor_fault, arch_post_modify_registers,
         arch_post_cap_deletion, arch_invoke_irq_handler
  for domain_time_scheduler_action_inv[wp, DetSchedDomainTime_AI_assms]:
        "\<lambda>s :: det_state. P (domain_time s) (scheduler_action s)"
  (wp: crunch_wps)

declare init_arch_objects_exst[DetSchedDomainTime_AI_assms]
        make_arch_fault_msg_inv[DetSchedDomainTime_AI_assms]
        arch_get_sanitise_register_info_inv[DetSchedDomainTime_AI_assms]

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

context Arch begin global_naming ARM

crunches arch_perform_invocation, arch_mask_irq_signal
  for domain_time_scheduler_action_inv[wp, DetSchedDomainTime_AI_assms]:
        "\<lambda>s :: det_state. P (domain_time s) (scheduler_action s)"
  and domain_list_inv [wp, DetSchedDomainTime_AI_assms]: "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s::det_state. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

lemma handle_interrupt_valid_domain_time[DetSchedDomainTime_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace>
   handle_interrupt i
   \<lbrace>\<lambda>_ s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
  apply (rule_tac Q="\<lambda>_. dtime_bounded" in hoare_strengthen_post[rotated])
   apply (clarsimp simp: dtime_bounded_def)
  apply (unfold handle_interrupt_def)
  apply (wpsimp simp: handle_reserved_irq_def dtime_bounded_def
         | wp (once) hoare_drop_imp)+
  done


crunches handle_reserved_irq
  for domain_time_scheduler_action_inv[wp, DetSchedDomainTime_AI_assms]:
        "\<lambda>s. P (domain_time s) (scheduler_action s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: handle_reserved_irq "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps)

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

end
