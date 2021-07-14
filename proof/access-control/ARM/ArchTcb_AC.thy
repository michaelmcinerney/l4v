(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_AC
imports Tcb_AC
begin

context Arch begin global_naming ARM_A

named_theorems Tcb_AC_assms

declare arch_get_sanitise_register_info_inv[Tcb_AC_assms]

crunches arch_post_modify_registers
  for pas_refined[Tcb_AC_assms, wp]: "pas_refined aag"

lemma arch_post_modify_registers_respects[Tcb_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_subject aag t)\<rbrace>
   arch_post_modify_registers cur t
   \<lbrace>\<lambda>_ s. integrity aag X st s\<rbrace>"
  by wpsimp

lemma install_tcb_cap_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> install_tcb_cap target slot n slot_opt \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding install_tcb_cap_def
  by (wpsimp wp: check_cap_inv | intro conjI)+

lemma install_tcb_frame_cap_valid_sched:
  "\<lbrace>valid_sched and simple_sched_action\<rbrace> install_tcb_frame_cap target slot slot_opt \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding install_tcb_frame_cap_def
  by (wpsimp wp: check_cap_inv reschedule_preserves_valid_sched thread_set_not_state_valid_sched hoare_drop_imp)

lemma install_tcb_cap_pas_refined:
  "authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf) \<Longrightarrow>
   \<lbrace>pas_refined aag and einvs and simple_sched_action
                    and K ((n,slot_opt) \<in> {(0,croot),(1,vroot),(5,ep)})
                    and K (case_option True (\<lambda>(a,b). \<not> is_master_reply_cap a) slot_opt)\<rbrace>
    install_tcb_cap t sl n slot_opt
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding install_tcb_cap_def
  apply (rule hoare_gen_asm)+
  by (wpsimp wp: checked_insert_pas_refined cap_delete_pas_refined' cap_delete_invs
      | fastforce simp: authorised_tcb_inv_def emptyable_def
      | strengthen invs_strgs invs_arch_state_strg invs_vspace_objs | intro conjI)+

lemma install_tcb_cap_integrity:
  "authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf) \<Longrightarrow>
   \<lbrace>integrity aag X st and pas_refined aag and einvs and simple_sched_action
                       and K ((n,slot_opt) \<in> {(0,croot),(1,vroot),(5,ep)})
                       and K (case_option True (\<lambda>(a,b). \<not> is_master_reply_cap a) slot_opt)\<rbrace>
    install_tcb_cap t sl n slot_opt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding install_tcb_cap_def
  apply (rule hoare_gen_asm)+
  by (wpsimp wp: checked_insert_pas_refined check_cap_inv cap_insert_integrity_autarch
                 cap_delete_invs cap_delete_pas_refined' cap_delete_respects'
      | fastforce simp: authorised_tcb_inv_def emptyable_def
      | strengthen invs_strgs)+

lemma install_tcb_frame_cap_pas_refined:
  "authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf) \<Longrightarrow>
   \<lbrace> pas_refined aag and einvs and simple_sched_action
                     and K (case_option True (\<lambda>(a,b). case_option True (\<lambda>(a,b). \<not> is_master_reply_cap a) b) buf)\<rbrace>
    install_tcb_frame_cap t sl buf
   \<lbrace>\<lambda>_.  pas_refined aag\<rbrace>"
  unfolding install_tcb_frame_cap_def
  apply (rule hoare_gen_asm)+
  by (wpsimp wp: checked_insert_pas_refined cap_delete_pas_refined' cap_delete_deletes
                 cap_delete_invs thread_set_tcb_ipc_buffer_cap_cleared_invs thread_set_pas_refined
      | rule_tac Q="\<lambda>_. invs and pas_refined aag" in hoare_post_imp
      | strengthen invs_strgs invs_arch_state_strg invs_vspace_objs
      | fastforce simp: authorised_tcb_inv_def emptyable_def)+

lemma install_tcb_frame_cap_integrity:
  "authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf) \<Longrightarrow>
   \<lbrace> integrity aag X st and pas_refined aag and einvs and simple_sched_action
                        and K (case_option True (\<lambda>(a,b). case_option True (\<lambda>(a,b). \<not> is_master_reply_cap a) b) buf)\<rbrace>
    install_tcb_frame_cap t sl buf
   \<lbrace>\<lambda>_.  integrity aag X st\<rbrace>"
  unfolding install_tcb_frame_cap_def
  apply (rule hoare_gen_asm)+
  by (wpsimp wp: checked_insert_pas_refined cap_insert_integrity_autarch cap_delete_pas_refined'
                 cap_delete_respects' cap_delete_deletes cap_delete_invs thread_set_pas_refined
                 thread_set_integrity_autarch thread_set_tcb_ipc_buffer_cap_cleared_invs
                 check_cap_inv hoare_vcg_const_imp_lift
      | fastforce simp: authorised_tcb_inv_def emptyable_def)+

lemma invoke_tcb_tc_respects_aag[Tcb_AC_assms]:
  "\<lbrace> integrity aag X st and pas_refined aag
         and einvs and simple_sched_action
         and tcb_inv_wf (ThreadControl t sl ep mcp priority croot vroot buf)
         and K (authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf))\<rbrace>
     invoke_tcb (ThreadControl t sl ep mcp priority croot vroot buf)
   \<lbrace>\<lambda>rv. integrity aag X st and pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (subst invoke_tcb.simps)
  apply (subst set_priority_extended.dxo_eq)
  apply (rule hoare_vcg_precond_imp)
   apply (clarsimp simp: emptyable_def cong: conj_cong
          | wp install_tcb_frame_cap_integrity install_tcb_frame_cap_pas_refined
               install_tcb_cap_integrity install_tcb_cap_pas_refined
               install_tcb_cap_invs install_tcb_cap_valid_sched
               install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
               set_mcpriority_integrity_autarch thread_set_valid_cap
               thread_set_invs_trivial[OF ball_tcb_cap_casesI]
               thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
               thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
               hoare_vcg_all_lift_R hoare_vcg_all_lift
               hoare_vcg_const_imp_lift_R hoare_vcg_const_imp_lift
          | strengthen tcb_cap_always_valid_strg | wpc
          | simp add: set_mcpriority_def)+
  apply (intro conjI impI allI)
  (* slow: 60s *)
  by (clarsimp split: option.split
      | fastforce simp: is_cnode_or_valid_arch_def is_valid_vtable_root_def is_cap_simps
                        tcb_cap_valid_def tcb_at_st_tcb_at authorised_tcb_inv_def
                 intro: tcb_ep_slot_cte_wp_at elim: cte_wp_at_weakenE)+

end


global_interpretation Tcb_AC_1?: Tcb_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Tcb_AC_assms)
qed

end
