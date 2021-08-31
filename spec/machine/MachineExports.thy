(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory MachineExports
imports "./$L4V_ARCH/MachineOps"
begin

lemma mult_le_mono':
  "\<lbrakk>a \<le> a'; b \<le> b'; a' * b' \<le> c\<rbrakk> \<Longrightarrow> a * b \<le> (c :: nat)"
  using le_trans mult_le_mono by blast

notepad begin

define factor1 :: "64 word" where "factor1 = of_nat 50"
define factor2 :: "64 word" where "factor2 = of_nat 1"
define kernelWCET_us :: "64 word" where "kernelWCET_us = of_nat 100"
define MAX_PERIOD_US :: "64 word" where "MAX_PERIOD_US = 60 * 60 * 1000 * 1000"
define \<mu>s_in_ms :: "64 word" where "\<mu>s_in_ms = 1000"

have factor1_non_zero: "factor1 \<noteq> 0" using factor1_def by simp

have MIN_BUDGET_bound: "2 * unat kernelWCET_us * unat factor1 < unat max_time"
  apply (subst unat_max_word[symmetric])
  apply clarsimp
  apply (prop_tac "unat kernelWCET_us \<le> 100")
   apply (fastforce simp: kernelWCET_us_def)
  apply (prop_tac "unat factor1 \<le> 50")
   apply (fastforce simp: factor1_def)
  apply (rule_tac y="10000" in le_less_trans)
   apply (rule_tac a'=200 and b'=50 in mult_le_mono'; fastforce)
  apply simp
  done

have getCurrentTime_buffer_bound:
  "unat kernelWCET_us * unat factor1 + 5 * unat MAX_PERIOD_US * unat factor1 < unat max_time"
  apply (subst unat_max_word[symmetric])
  apply clarsimp
  apply (rule_tac a'=5000 and b'="5 * 60 * 60 * 1000 * 1000 * 50" in less_mono)
    apply (fastforce simp: kernelWCET_us_def factor1_def)
   apply (fastforce simp: kernelWCET_us_def factor1_def MAX_PERIOD_US_def)
  apply linarith
  done

have kernelWCET_pos': "0 < (kernelWCET_us * factor1) div factor2"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def factor1_def factor2_def max_word_def)+
  done

have MIN_BUDGET_pos': "0 < 2 * ((kernelWCET_us * factor1) div factor2)"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def factor1_def factor2_def max_word_def)+
  done

have domain_time_pos: "0 < ((15 * \<mu>s_in_ms) * factor1) div factor2"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_mult_lem' | subst unat_div
         | fastforce simp: \<mu>s_in_ms_def factor1_def factor2_def max_word_def)+
  done

have getCurrentTime_buffer_pos:
  "0 < (kernelWCET_us * factor1) div factor2 + 5 * (MAX_PERIOD_US * factor1 div factor2)"
  apply (clarsimp simp: word_less_nat_alt)
  apply (subst unat_add_lem'' | subst unat_mult_lem' | subst unat_div
         | fastforce simp: kernelWCET_us_def MAX_PERIOD_US_def factor1_def factor2_def max_word_def)+
  done

end

context begin interpretation Arch .

(* Check consistency of machine_word and machine_word_len. *)
term "id :: machine_word \<Rightarrow> machine_word_len word"

requalify_types
  machine_word
  machine_word_len
  vmfault_type
  hyp_fault_type
  irq
  ticks
  time

requalify_consts
  getActiveIRQ
  maskInterrupt
  freeMemory
  loadWord
  storeWord
  storeWordVM
  setNextPC
  getRestartPC
  setRegister
  getRegister
  initContext
  exceptionMessage
  syscallMessage
  timeoutMessage
  gpRegisters
  frameRegisters
  replyRegister
  nbsendRecvDest
  ackInterrupt
  ackDeadlineIRQ
  resetTimer
  getCurrentTime
  maxIRQ
  minIRQ
  timerIRQ
  word_size_bits
  clearMemory
  non_kernel_IRQs
  tlsBaseRegister
  configureTimer
  kernelWCET_us
  kernelWCET_ticks
  maxTimer_us
  max_ticks_to_us
  max_us_to_ticks
  MAX_PERIOD_US
  MAX_PERIOD
  us_to_ticks
  ticks_to_us
  setDeadline
  timerPrecision
  max_time
  getCurrentTime_buffer
  ticks_per_timer_unit
  timer_unit
  \<mu>s_in_ms

requalify_facts
  MAX_PERIOD_US_def
  MAX_PERIOD_def
  kernelWCET_ticks_def
  replicate_no_overflow
  getCurrentTime_buffer_nonzero'
  getCurrentTime_buffer_no_overflow'
  getCurrentTime_buffer_no_overflow'_stronger
  getCurrentTime_buffer_minus
  getCurrentTime_buffer_minus'
  MAX_PERIOD_mult
  ticks_per_timer_unit_non_zero
  MIN_BUDGET_bound
  getCurrentTime_buffer_bound
  kernelWCET_pos'
  MIN_BUDGET_pos'
  domain_time_pos
  getCurrentTime_buffer_pos
  us_to_ticks_def
  getCurrentTime_buffer_no_overflow
  us_to_ticks_mono
  MIN_BUDGET_helper
  \<mu>s_in_ms_def

definition "MAX_RELEASE_TIME = max_time - 5 * MAX_PERIOD"

lemma unat_MAX_RELEASE_TIME:
  "unat MAX_RELEASE_TIME = unat max_time - 5 * unat MAX_PERIOD"
  apply (clarsimp simp: MAX_RELEASE_TIME_def unat_sub MAX_PERIOD_mult)
  done

(* HERE IS THE PLACE FOR GENERIC WORD LEMMAS FOR ALL ARCHITECTURES *)

lemma Suc_unat_mask_div_obfuscated:
  "Suc (unat (mask sz div (word_size::machine_word))) = 2 ^ (min sz word_bits - word_size_bits)"
  unfolding word_size_bits_def
  by (rule Suc_unat_mask_div)

lemma word_size_size_bits_nat:
  "2^word_size_bits = (word_size :: nat)"
  by (simp add: word_size_bits_def word_size_def)

lemma word_size_size_bits_word:
  "2^word_size_bits = (word_size :: 'a :: len word)"
  by (simp add: word_size_bits_def word_size_def)

end

end
