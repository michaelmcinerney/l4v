(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_IF
imports Tcb_IF
begin

context Arch begin global_naming ARM

named_theorems Tcb_IF_assms

section "arm global pd"

crunch arm_global_pd[wp]: set_irq_state, suspend "\<lambda>s. P (arm_global_pd (arch_state s))"
  (wp: mapM_x_wp select_inv hoare_vcg_if_lift2 hoare_drop_imps dxo_wp_weak
   simp: unless_def
   ignore: empty_slot_ext reschedule_required)

crunch arm_global_pd[wp]: as_user, restart "\<lambda>s. P (arm_global_pd (arch_state s))" (wp: dxo_wp_weak)

lemma cap_ne_global_pd:
  "\<lbrakk> ex_nonz_cap_to word s; valid_global_refs s \<rbrakk>
     \<Longrightarrow> word \<noteq> arm_global_pd (arch_state s)"
  unfolding ex_nonz_cap_to_def
  apply (simp only: cte_wp_at_caps_of_state zobj_refs_to_obj_refs)
  apply (elim exE conjE)
  apply (drule valid_global_refsD2,simp)
  apply (unfold global_refs_def)
  apply clarsimp
  apply (unfold cap_range_def)
  apply blast
  done

lemma valid_arch_caps_vs_lookup[Tcb_IF_assms]:
  "valid_arch_caps s \<Longrightarrow> valid_vs_lookup s"
  by (simp add: valid_arch_caps_def)

lemma no_cap_to_idle_thread'[Tcb_IF_assms]:
  "valid_global_refs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (clarsimp simp add: ex_nonz_cap_to_def valid_global_refs_def valid_refs_def)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (clarsimp simp: cte_wp_at_def global_refs_def cap_range_def)
  apply (case_tac cap,simp_all)
  done

lemma no_cap_to_idle_thread''[Tcb_IF_assms]:
  "valid_global_refs s \<Longrightarrow> caps_of_state s ref \<noteq> Some (ThreadCap (idle_thread s))"
  apply (clarsimp simp add: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)
  apply (drule_tac x="fst ref" in spec)
  apply (drule_tac x="snd ref" in spec)
  apply (simp add: cap_range_def global_refs_def)
  done

crunches arch_post_modify_registers
  for globals_equiv[Tcb_IF_assms, wp]: "globals_equiv st"
  and valid_arch_state[Tcb_IF_assms, wp]: valid_arch_state

lemma arch_post_modify_registers_reads_respects_f[Tcb_IF_assms, wp]:
  "reads_respects_f aag l \<top> (arch_post_modify_registers cur t)"
  by wpsimp

lemma arch_get_sanitise_register_info_reads_respects_f[Tcb_IF_assms, wp]:
  "reads_respects_f aag l \<top> (arch_get_sanitise_register_info rv)"
  by wpsimp

end


global_interpretation Tcb_IF_1?: Tcb_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Tcb_IF_assms)?)
qed


context Arch begin global_naming ARM

(* FIXME: Pretty general. Probably belongs somewhere else *)
lemma invoke_tcb_thread_preservation[Tcb_IF_assms]:
  assumes cap_delete_P: "\<And>slot. \<lbrace>invs and P and emptyable slot\<rbrace> cap_delete slot \<lbrace>\<lambda>_. P\<rbrace>"
  assumes cap_insert_P: "\<And>new_cap src dest. \<lbrace>invs and P\<rbrace> cap_insert new_cap src dest \<lbrace>\<lambda>_. P\<rbrace>"
  assumes thread_set_P: "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_ipc_buffer_update f) ptr \<lbrace>\<lambda>_. P\<rbrace>"
  assumes thread_set_P': "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_fault_handler_update f) ptr \<lbrace>\<lambda>_. P\<rbrace>"
  assumes set_mcpriority_P: "\<And>mcp ptr. \<lbrace>invs and P\<rbrace> set_mcpriority ptr mcp \<lbrace>\<lambda>_. P\<rbrace>"
  assumes P_trans[simp]: "\<And>f s. P (trans_state f s) = P s"
  shows
    "\<lbrace>P and invs and tcb_inv_wf (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)\<rbrace>
     invoke_tcb (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)
     \<lbrace>\<lambda>rv s :: det_state. P s\<rbrace>"
  supply set_priority_extended.dxo_eq[simp del]
proof -
  have install_tcb_cap_preservation:
    "\<And>t sl n slo. \<lbrace>invs and K (n \<in> {0,1,5}) and P\<rbrace> install_tcb_cap t sl n slo \<lbrace>\<lambda>_. P\<rbrace>"
    unfolding install_tcb_cap_def
    by (wpsimp wp: check_cap_inv2 cap_insert_P cap_delete_P
        | rule conjI impI | fastforce simp: emptyable_def)+
  have install_tcb_frame_cap_preservation:
    "\<And>t sl buf. \<lbrace>invs and P\<rbrace> install_tcb_frame_cap t sl buf \<lbrace>\<lambda>_. P\<rbrace>"
    unfolding install_tcb_frame_cap_def
    by (wpsimp wp: check_cap_inv2 cap_insert_P cap_delete_P cap_delete_deletes hoare_vcg_const_imp_lift_R
                      hoare_vcg_const_imp_lift dxo_wp_weak thread_set_P thread_set_tcb_ipc_buffer_cap_cleared_invs
        | fastforce simp: emptyable_def)+
  show ?thesis
    apply (simp add: split_def cong: option.case_cong)
    apply (rule hoare_vcg_precond_imp)
     apply (clarsimp simp: emptyable_def cong: conj_cong
            | wpsimp wp: dxo_wp_weak hoare_vcg_const_imp_lift_R hoare_vcg_const_imp_lift
                         hoare_vcg_all_lift_R hoare_vcg_all_lift thread_set_valid_cap
                         install_tcb_frame_cap_preservation install_tcb_cap_preservation
                         install_tcb_cap_invs install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
                         set_mcpriority_P thread_set_invs_trivial[OF ball_tcb_cap_casesI]
                         thread_set_cte_at
                         thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
                         thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
            | simp add: set_mcpriority_def
            | strengthen tcb_cap_always_valid_strg)+
    apply(intro conjI impI allI)
    (* slow, ~30s *)
    by (clarsimp split: option.split
        | fastforce simp: is_cnode_or_valid_arch_def is_valid_vtable_root_def is_cap_simps
                          tcb_cap_valid_def tcb_at_st_tcb_at authorised_tcb_inv_def
                   intro: tcb_ep_slot_cte_wp_at elim: cte_wp_at_weakenE)+
qed

lemma tc_reads_respects_f[Tcb_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  and tc[simp]: "ti = ThreadControl x41 x42 x43 x44 x45 x46 x47 x48"
  notes validE_valid[wp del] static_imp_wp [wp]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action
                        and pas_refined aag and pas_cur_domain aag and tcb_inv_wf ti
                        and is_subject aag \<circ> cur_thread
                        and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
       (invoke_tcb ti)"
  apply (simp add: split_def cong: option.case_cong)
  apply (rule gen_asm_ev)
  apply (clarsimp simp: emptyable_def cong: conj_cong imp_cong
         | wp set_priority_reads_respects[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
              install_tcb_frame_cap_reads_respects_f
              install_tcb_frame_cap_silc_inv
              install_tcb_frame_cap_pas_refined
              install_tcb_cap_reads_respects_f
              install_tcb_cap_silc_inv
              install_tcb_cap_invs
              install_tcb_cap_valid_sched
              install_tcb_cap_pas_refined
              hoare_vcg_all_lift_R hoare_vcg_all_lift
              hoare_vcg_const_imp_lift_R hoare_vcg_const_imp_lift
              install_tcb_cap_cte_at install_tcb_cap_cte_wp_at_ep
              set_mcpriority_reads_respects[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
              set_mcpriority_only_timer_irq_inv[where st=st' and irq=irq]
              thread_set_cte_at
              thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
              thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
         | wpc | assumption | simp add: set_mcpriority_def
         | strengthen tcb_cap_always_valid_strg invs_strgs)+
  using assms
  apply(intro conjI impI allI; assumption?)
  (* slow, ~90s *)
  by (clarsimp split: option.split
      | fastforce simp: is_cnode_or_valid_arch_def is_valid_vtable_root_def is_cap_simps tcb_cap_valid_def
                        tcb_at_st_tcb_at authorised_tcb_inv_def authorised_tcb_inv_extra_def
                 intro: tcb_ep_slot_cte_wp_at elim: cte_wp_at_weakenE)+

end


global_interpretation Tcb_IF_2?: Tcb_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Tcb_IF_assms)?)
qed

end
