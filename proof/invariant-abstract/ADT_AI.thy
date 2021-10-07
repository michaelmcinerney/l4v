(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Abstract datatype for the abstract specification\<close>

theory ADT_AI
imports
  ArchADT_AI
begin

context begin interpretation Arch .

requalify_consts
  empty_context
  init_A_st
  ptable_lift
  ptable_rights
  addrFromPPtr
  ptrFromPAddr

end

text \<open>
  The general refinement calculus (see theory Simulation) requires
  the definition of a so-called ``abstract datatype'' for each refinement layer.
  This theory defines this datatype for the abstract specification.
  Along the path, the theory extends the abstract specification of the kernel
  with respect to user-mode transitions.
\<close>

text \<open>
  We constrain idle thread behaviour, so we distinguish three main
  machine control states:
\<close>
datatype mode = UserMode | KernelMode | IdleMode

text \<open>
  The global state contains the current user's register context of the machine
  as well as the internal kernel state, the mode and the current event (if any).
\<close>
type_synonym 'k global_state = "(user_context \<times> 'k) \<times> mode \<times> event option"

text \<open>
  As observable state, we take the global abstract state.
\<close>
type_synonym 'a observable = "('a state) global_state"

text \<open>
  From the kernel's perspective,
  the user memory is a mapping from addresses to bytes.
  A virtual-memory view will later on be built on top of that.
\<close>
type_synonym user_mem = "machine_word \<Rightarrow> word8 option"

(* This is a temperary solution to model the user device memory *)
type_synonym device_state = "machine_word \<Rightarrow> word8 option"

text \<open>
  A user state consists of a register context and (physical) user memory.
\<close>
type_synonym user_state = "user_context \<times> user_mem \<times> device_state"

text \<open>Virtual-memory mapping: translates virtual to physical addresses\<close>
type_synonym vm_mapping = "machine_word \<rightharpoonup> machine_word"

text \<open>Memory rights for each virtual adress\<close>
type_synonym mem_rights = "machine_word \<Rightarrow> vm_rights"

text \<open>
  A user transition is characterized by a function
  that takes the following arguments:
  a current thread identifier,
  a virtual-memory mapping
    (i.e., a partial function from virtual to physical addresses),
  a memory-rights mapping
    (i.e., a partial function from virtual addresses to rights).

  The function is then a non-deterministic state monad on user state,
  returning an optional kernel-entry event.

  Note that the current-thread identifiers are identical in both specs
    (i.e. @{term "Structures_A.cur_thread :: 'z state \<Rightarrow> obj_ref"}
          in the abstract kernel model and
          @{text "KernelStateData_H.ksCurThread \<Colon> kernel_state \<Rightarrow> machine_word"}
          in the executable specification).
\<close>
type_synonym user_transition =
  "obj_ref \<Rightarrow> vm_mapping \<Rightarrow> mem_rights \<Rightarrow> (user_state, event option) nondet_monad"

text \<open>Abbreviation for user context plus additional state\<close>
type_synonym 'k uc_state = "user_context \<times> 'k"

text \<open>
  The following definition models machine and kernel entry/exit behaviour
  abstractly.
  Furthermore, it constrains the behaviour of user threads as well as
  the idle thread.

  The first parameter is used to check of pending interrupts, potentially
  modifying the machine state embedded in the kernel state.
  The second parameter lifts a user-thread transition into
  the kernel state (i.e. the new user memory should be injected into the
  kernel state) and the third parameter provides a kernel specification (it
  will later be used with the abstract specification, the executable
  specification, as well as the C implementation).

  Despite the fact that the global automaton does not distinguish different
  kinds of transitions to the outside world, the definition groups them into
  6 kinds:
  1. Kernel transition: The kernel specification is started in kernel mode and
     uses the event part of the state as input.
     The next control state will either be user mode or idle mode
     (idle thread running).
  2. Normal user-mode executions.
     The computed new user states are then lifted into the kernel state
     using the first parameter to the definition below.
  3. and 4. Event generation in user mode.
     In user mode, events may be generated by the user and
     any interrupt can be generated at any time.
  5. and 6. Finally, events generated by the idle thread.
     These can only be interrupts. If there is no interrupt, we stay in idle mode.
\<close>
definition
  global_automaton ::
    "('k uc_state \<times> (bool \<times> 'k uc_state)) set
     \<Rightarrow> ('k uc_state \<times> (event option \<times> 'k uc_state)) set
     \<Rightarrow> (event \<Rightarrow> ('k uc_state \<times> mode \<times> 'k uc_state) set)
     \<Rightarrow> ('k global_state \<times> 'k global_state) set"
  where
  "global_automaton get_active_irq do_user_op kernel_call \<equiv>
  \<comment> \<open> Kernel transition \<close>
     { ( (s, KernelMode, Some e),
         (s', m, None) ) |s s' e m. (s, m, s') \<in> kernel_call e } \<union>
  \<comment> \<open> User to user transition, no kernel entry \<close>
     { ( (s, UserMode, None),
         (s', UserMode, None) ) |s s'. (s, None, s') \<in> do_user_op} \<union>
  \<comment> \<open> User to kernel transition, potentially includes Interrupt from user mode \<close>
     { ( (s, UserMode, None),
         (s', KernelMode, Some e) ) |s s' e. (s, Some e, s') \<in> do_user_op} \<union>
  \<comment> \<open> User to kernel transition, Interrupt from user mode \<close>
     { ( (s, UserMode, None),
         (s', KernelMode, Some Interrupt) ) |s s'. (s, True, s') \<in> get_active_irq} \<union>
  \<comment> \<open> Idling in idle mode \<close>
     { ( (s, IdleMode, None),
         (s', IdleMode, None) ) |s s'.  (s, False, s') \<in> get_active_irq} \<union>
  \<comment> \<open> Interrupt while in idle mode \<close>
     { ( (s, IdleMode, None),
         (s', KernelMode, Some Interrupt) ) |s s'.  (s, True, s') \<in> get_active_irq}"

text \<open>
  After kernel initialisation, the machine is in UserMode, running the initial thread.
\<close>
definition
  Init_A :: "'a::state_ext state global_state set"
where
  "Init_A \<equiv> {((empty_context, init_A_st), UserMode, None)}"

definition
  "user_memory_update um \<equiv> modify (\<lambda>ms.
    ms\<lparr>underlying_memory := (\<lambda>a. case um a of Some x \<Rightarrow> x
                                 | None \<Rightarrow> underlying_memory ms a)\<rparr>)"
definition
  "device_memory_update um \<equiv> modify (\<lambda>ms.
    ms\<lparr>device_state := (device_state ms ++ um ) \<rparr>)"

definition
  "option_to_0 x \<equiv> case x of None \<Rightarrow> 0 | Some y \<Rightarrow> y"

text \<open>
  The below definition gives the kernel monad computation that checks for
  active interrupts, given the present user_context. This is necessarily
  a computation in the kernel monad because checking interrupts will update
  the interrupt state.
\<close>
definition
  check_active_irq :: "(bool,'z :: state_ext) s_monad"
  where
  "check_active_irq \<equiv> do
      irq \<leftarrow> do_machine_op $ getActiveIRQ False;
      return (irq \<noteq> None)
  od"

definition
  check_active_irq_A :: "(('z :: state_ext) state uc_state \<times> bool \<times> ('z :: state_ext) state uc_state) set"
  where
  "check_active_irq_A \<equiv> {((tc, s), (irq, (tc, s'))). (irq , s') \<in> fst (check_active_irq s)}"

text \<open>
  The definition below lifts a user transition into the kernel monad.
  Note that the user memory (as seen by the kernel) is
  converted to true physical addresses and
  restricted to those addresses, the current thread is permitted to access.
  Furthermore, user memory is updated if and only if
  the current thread has write permission.

  NOTE: An unpermitted write access would generate a page fault on the machine.
    The global transitions, however, model page faults non-deterministically.
\<close>

definition
  do_user_op :: "user_transition \<Rightarrow> user_context \<Rightarrow> (event option \<times> user_context,'z::state_ext) s_monad"
  where
  "do_user_op uop tc \<equiv>
   do t \<leftarrow> gets cur_thread;
      conv \<leftarrow> gets (ptable_lift t);
      rights \<leftarrow> gets (ptable_rights t);
      um \<leftarrow> gets (\<lambda>s. (user_mem s) \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. (device_mem s) \<circ> ptrFromPAddr);
      ds \<leftarrow> gets (device_state \<circ> machine_state);
      (e,tc',um',ds') \<leftarrow> select (fst
                     (uop t (restrict_map conv {pa. rights pa \<noteq> {}}) rights
                       (tc, restrict_map um {pa. \<exists>va. conv va = Some pa \<and> AllowRead \<in> rights va}
                       ,(ds \<circ> ptrFromPAddr) |`  {pa. \<exists>va. conv va = Some pa \<and> AllowRead \<in> rights va} )
                     ));
      do_machine_op (user_memory_update
          ((um' |` {pa. \<exists>va. conv va = Some pa \<and> AllowWrite \<in> rights va} \<circ> addrFromPPtr) |` (- dom ds)));
      do_machine_op (device_memory_update
          ((ds' |` {pa. \<exists>va. conv va = Some pa \<and> AllowWrite \<in> rights va} \<circ> addrFromPPtr) |` (dom ds)));
      return (e, tc')
   od"


definition
  monad_to_transition ::
 "(user_context \<Rightarrow> ('s, event option \<times> user_context) nondet_monad) \<Rightarrow>
  ('s uc_state \<times> event option \<times> 's uc_state) set"
where
  "monad_to_transition m \<equiv> {((tc,s),(e,tc',s')). ((e,tc'),s') \<in> fst (m tc s)}"

definition
  do_user_op_A :: "user_transition \<Rightarrow>
                   ('z state uc_state \<times> event option \<times> ('z::state_ext state) uc_state) set"
  where
  "do_user_op_A uop \<equiv> monad_to_transition (do_user_op uop)"


text \<open>
  Kernel calls are described completely by the abstract and concrete spec.
  We model kernel entry by allowing an arbitrary user (register) context.
  The mode after a kernel call is either user or idle
  (see also thm in Refine.thy).
\<close>

(* FIXME: The IPC buffer pointer and TLS_BASE are stored in registers
   in restore_user_context, which is currently invisible to verification.
   The effect should be modelled in the ADT. *)
definition
  kernel_entry :: "event \<Rightarrow> user_context \<Rightarrow> (user_context,'z::state_ext) s_monad"
  where
  "kernel_entry e tc \<equiv> do
    t \<leftarrow> gets cur_thread;
    thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_context_set tc (tcb_arch tcb) \<rparr>) t;
    call_kernel e;
    t' \<leftarrow> gets cur_thread;
    thread_get (arch_tcb_context_get o tcb_arch) t'
  od"


definition
  kernel_call_A
    :: "event \<Rightarrow> ((user_context \<times> ('a::state_ext state)) \<times> mode \<times> (user_context \<times> 'a state)) set"
  where
  "kernel_call_A e \<equiv>
      {(s, m, s'). s' \<in> fst (split (kernel_entry e) s) \<and>
                   m = (if ct_running (snd s') then UserMode else IdleMode)}"

text \<open>Putting together the final abstract datatype\<close>

(* NOTE: the extensible abstract specification leaves the type of the extension
     unspecified; later on, we will instantiate this type with det_ext from the
     deterministic abstract specification as well as with unit.  The former is
     used for refinement between the deterministic specification and C.  The
     latter is used for refinement between the non-deterministic specification
     and C. *)

definition
  "observable_memory ms fs \<equiv> ms \<lparr>underlying_memory := option_to_0 \<circ> fs\<rparr>"

definition
  "abs_state s \<equiv> s\<lparr>machine_state:= observable_memory (machine_state s) (user_mem s)\<rparr>"

definition
  ADT_A :: "user_transition \<Rightarrow> (('a::state_ext state) global_state, 'a observable, unit) data_type"
where
 "ADT_A uop \<equiv>
  \<lparr> Init = \<lambda>s. Init_A, Fin = \<lambda>((tc,s),m,e). ((tc, abs_state s),m,e),
    Step = (\<lambda>u. global_automaton check_active_irq_A (do_user_op_A uop) kernel_call_A) \<rparr>"


text \<open>
  Lifting a state relation on kernel states to global states.
\<close>
definition
  "lift_state_relation sr \<equiv>
   { (((tc,s),m,e), ((tc,s'),m,e))|s s' m e tc. (s,s') \<in> sr }"

lemma lift_state_relationD:
  "(((tc, s), m, e), ((tc', s'), m', e')) \<in> lift_state_relation R \<Longrightarrow>
  (s,s') \<in> R \<and> tc' = tc \<and> m' = m \<and> e' = e"
  by (simp add: lift_state_relation_def)

lemma lift_state_relationI:
  "(s,s') \<in> R \<Longrightarrow> (((tc, s), m, e), ((tc, s'), m, e)) \<in> lift_state_relation R"
  by (fastforce simp: lift_state_relation_def)

lemma in_lift_state_relation_eq:
  "(((tc, s), m, e), (tc', s'), m', e') \<in> lift_state_relation R \<longleftrightarrow>
   (s, s') \<in> R \<and> tc' = tc \<and> m' = m \<and> e' = e"
  by (auto simp add: lift_state_relation_def)

end
