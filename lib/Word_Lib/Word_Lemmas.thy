(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Lemmas with Generic Word Length"

theory Word_Lemmas
  imports
    Complex_Main
    Word_EqI
    Word_Enum
    "HOL-Library.Sublist"
begin

lemma word_plus_mono_left:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y \<le> z; x \<le> x + z\<rbrakk> \<Longrightarrow> y + x \<le> z + x"
  by unat_arith

lemma word_shiftl_add_distrib:
  fixes x :: "'a :: len word"
  shows "(x + y) << n = (x << n) + (y << n)"
  by (simp add: shiftl_t2n ring_distribs)

lemma less_Suc_unat_less_bound:
  "n < Suc (unat (x :: 'a :: len word)) \<Longrightarrow> n < 2 ^ LENGTH('a)"
  by (auto elim!: order_less_le_trans intro: Suc_leI)

lemma up_ucast_inj:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> len_of TYPE ('b) \<rbrakk> \<Longrightarrow> x = (y::'a::len word)"
  by (subst (asm) bang_eq) (fastforce simp: nth_ucast word_size intro: word_eqI)

lemmas ucast_up_inj = up_ucast_inj

lemma up_ucast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow> (ucast x = (ucast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_ucast_inj)

lemma no_plus_overflow_neg:
  "(x :: 'a :: len word) < -y \<Longrightarrow> x \<le> x + y"
  by (metis diff_minus_eq_add less_imp_le sub_wrap_lt)

lemma ucast_ucast_eq:
  "\<lbrakk> ucast x = (ucast (ucast y::'a word)::'c::len word); LENGTH('a) \<le> LENGTH('b);
     LENGTH('b) \<le> LENGTH('c) \<rbrakk> \<Longrightarrow>
   x = ucast y" for x :: "'a::len word" and y :: "'b::len word"
  by (fastforce intro: word_eqI simp: bang_eq nth_ucast word_size)

lemma ucast_0_I:
  "x = 0 \<Longrightarrow> ucast x = 0"
  by simp

text \<open>right-padding a word to a certain length\<close>

definition
  "bl_pad_to bl sz \<equiv> bl @ (replicate (sz - length bl) False)"

lemma bl_pad_to_length:
  assumes lbl: "length bl \<le> sz"
  shows   "length (bl_pad_to bl sz) = sz"
  using lbl by (simp add: bl_pad_to_def)

lemma bl_pad_to_prefix:
  "prefix bl (bl_pad_to bl sz)"
  by (simp add: bl_pad_to_def)

lemma same_length_is_parallel:
  assumes len: "\<forall>y \<in> set as. length y = x"
  shows  "\<forall>x \<in> set as. \<forall>y \<in> set as - {x}. x \<parallel> y"
proof (rule, rule)
  fix x y
  assume xi: "x \<in> set as" and yi: "y \<in> set as - {x}"
  from len obtain q where len': "\<forall>y \<in> set as. length y = q" ..

  show "x \<parallel> y"
  proof (rule not_equal_is_parallel)
    from xi yi show "x \<noteq> y" by auto
    from xi yi len' show "length x = length y" by (auto dest: bspec)
  qed
qed

text \<open>Lemmas about words\<close>

lemmas and_bang = word_and_nth

lemma of_drop_to_bl:
  "of_bl (drop n (to_bl x)) = (x && mask (size x - n))"
  by (simp add: of_bl_drop word_size_bl)

lemma word_add_offset_less:
  fixes x :: "'a :: len word"
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mnv: "sz < LENGTH('a :: len)"
  and    xv': "x < 2 ^ (LENGTH('a :: len) - n)"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from mnv mn have nv: "n < LENGTH('a)" and mv: "m < LENGTH('a)"  by auto

  have uy: "unat y < 2 ^ n"
    by (rule order_less_le_trans [OF unat_mono [OF yv] order_eq_refl],
        rule unat_power_lower[OF nv])

  have ux: "unat x < 2 ^ m"
    by (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl],
        rule unat_power_lower[OF mv])

  then show "x * 2 ^ n + y < 2 ^ (m + n)" using ux uy nv mnv xv'
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)+
    apply (subst mod_less)
     apply simp
     apply (subst mult.commute)
     apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
     apply (rule order_less_le_trans [OF unat_mono [OF xv']])
     apply (cases "n = 0"; simp)
    apply (subst unat_power_lower[OF nv])
    apply (subst mod_less)
     apply (erule order_less_le_trans [OF nat_add_offset_less], assumption)
      apply (rule mn)
     apply simp
    apply (simp add: mn mnv)
    apply (erule nat_add_offset_less; simp)
    done
qed

lemma word_less_power_trans:
  fixes n :: "'a :: len word"
  assumes nv: "n < 2 ^ (m - k)"
  and     kv: "k \<le> m"
  and     mv: "m < len_of TYPE ('a)"
  shows "2 ^ k * n < 2 ^ m"
  using nv kv mv
  apply -
  apply (subst word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply simp
   apply (rule nat_less_power_trans)
    apply (erule order_less_trans [OF unat_mono])
    apply simp
   apply simp
  apply simp
  apply (rule nat_less_power_trans)
   apply (subst unat_power_lower[where 'a = 'a, symmetric])
    apply simp
   apply (erule unat_mono)
  apply simp
  done

lemma Suc_unat_diff_1:
  fixes x :: "'a :: len word"
  assumes lt: "1 \<le> x"
  shows "Suc (unat (x - 1)) = unat x"
proof -
  have "0 < unat x"
    by (rule order_less_le_trans [where y = 1], simp, subst unat_1 [symmetric],
        rule iffD1 [OF word_le_nat_alt lt])

  then show ?thesis
    by ((subst unat_sub [OF lt])+, simp only:  unat_1)
qed

lemma word_div_sub:
  fixes x :: "'a :: len word"
  assumes yx: "y \<le> x"
  and     y0: "0 < y"
  shows "(x - y) div y = x div y - 1"
  apply (rule word_unat.Rep_eqD)
  apply (subst unat_div)
  apply (subst unat_sub [OF yx])
  apply (subst unat_sub)
   apply (subst word_le_nat_alt)
   apply (subst unat_div)
   apply (subst le_div_geq)
     apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
     apply simp
    apply (subst word_le_nat_alt [symmetric], rule yx)
   apply simp
  apply (subst unat_div)
  apply (subst le_div_geq [OF _ iffD1 [OF word_le_nat_alt yx]])
   apply (rule order_le_less_trans [OF _ unat_mono [OF y0]])
   apply simp
  apply simp
  done

lemma word_mult_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k < j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto intro: order_less_subst2 simp: word_less_nat_alt elim: mult_less_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_less_dest:
  fixes i :: "'a :: len word"
  assumes ij: "i * k < j * k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk ij
  by (auto simp: word_less_nat_alt iffD1 [OF unat_mult_lem] elim: mult_less_mono1)

lemma word_mult_less_cancel:
  fixes k :: "'a :: len word"
  assumes knz: "0 < k"
  and    uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows "(i * k < j * k) = (i < j)"
  by (rule iffI [OF word_mult_less_dest [OF _ uik ujk] word_mult_less_mono1 [OF _ knz ujk]])

lemma Suc_div_unat_helper:
  assumes szv: "sz < LENGTH('a :: len)"
  and   usszv: "us \<le> sz"
  shows "2 ^ (sz - us) = Suc (unat (((2::'a :: len word) ^ sz - 1) div 2 ^ us))"
proof -
  note usv = order_le_less_trans [OF usszv szv]

  from usszv obtain q where qv: "sz = us + q" by (auto simp: le_iff_add)

  have "Suc (unat (((2:: 'a word) ^ sz - 1) div 2 ^ us)) =
    (2 ^ us + unat ((2:: 'a word) ^ sz - 1)) div 2 ^ us"
    apply (subst unat_div unat_power_lower[OF usv])+
    apply (subst div_add_self1, simp+)
    done

  also have "\<dots> = ((2 ^ us - 1) + 2 ^ sz) div 2 ^ us" using szv
    by (simp add: unat_minus_one)

  also have "\<dots> = 2 ^ q + ((2 ^ us - 1) div 2 ^ us)"
    apply (subst qv)
    apply (subst power_add)
    apply (subst div_mult_self2; simp)
    done

  also have "\<dots> = 2 ^ (sz - us)" using qv by simp

  finally show ?thesis ..
qed


lemma set_enum_word8_def:
  "(set enum::word8 set) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                            20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
                            37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
                            54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
                            71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
                            88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
                            104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                            118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
                            132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                            146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
                            160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                            174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
                            188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                            202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
                            216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
                            230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
                            244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255}"
  by eval

lemma set_strip_insert: "\<lbrakk> x \<in> insert a S; x \<noteq> a \<rbrakk> \<Longrightarrow> x \<in> S"
  by simp

lemma word8_exhaust:
  fixes x :: word8
  shows "\<lbrakk>x \<noteq> 0; x \<noteq> 1; x \<noteq> 2; x \<noteq> 3; x \<noteq> 4; x \<noteq> 5; x \<noteq> 6; x \<noteq> 7; x \<noteq> 8; x \<noteq> 9; x \<noteq> 10; x \<noteq> 11; x \<noteq>
          12; x \<noteq> 13; x \<noteq> 14; x \<noteq> 15; x \<noteq> 16; x \<noteq> 17; x \<noteq> 18; x \<noteq> 19; x \<noteq> 20; x \<noteq> 21; x \<noteq> 22; x \<noteq>
          23; x \<noteq> 24; x \<noteq> 25; x \<noteq> 26; x \<noteq> 27; x \<noteq> 28; x \<noteq> 29; x \<noteq> 30; x \<noteq> 31; x \<noteq> 32; x \<noteq> 33; x \<noteq>
          34; x \<noteq> 35; x \<noteq> 36; x \<noteq> 37; x \<noteq> 38; x \<noteq> 39; x \<noteq> 40; x \<noteq> 41; x \<noteq> 42; x \<noteq> 43; x \<noteq> 44; x \<noteq>
          45; x \<noteq> 46; x \<noteq> 47; x \<noteq> 48; x \<noteq> 49; x \<noteq> 50; x \<noteq> 51; x \<noteq> 52; x \<noteq> 53; x \<noteq> 54; x \<noteq> 55; x \<noteq>
          56; x \<noteq> 57; x \<noteq> 58; x \<noteq> 59; x \<noteq> 60; x \<noteq> 61; x \<noteq> 62; x \<noteq> 63; x \<noteq> 64; x \<noteq> 65; x \<noteq> 66; x \<noteq>
          67; x \<noteq> 68; x \<noteq> 69; x \<noteq> 70; x \<noteq> 71; x \<noteq> 72; x \<noteq> 73; x \<noteq> 74; x \<noteq> 75; x \<noteq> 76; x \<noteq> 77; x \<noteq>
          78; x \<noteq> 79; x \<noteq> 80; x \<noteq> 81; x \<noteq> 82; x \<noteq> 83; x \<noteq> 84; x \<noteq> 85; x \<noteq> 86; x \<noteq> 87; x \<noteq> 88; x \<noteq>
          89; x \<noteq> 90; x \<noteq> 91; x \<noteq> 92; x \<noteq> 93; x \<noteq> 94; x \<noteq> 95; x \<noteq> 96; x \<noteq> 97; x \<noteq> 98; x \<noteq> 99; x \<noteq>
          100; x \<noteq> 101; x \<noteq> 102; x \<noteq> 103; x \<noteq> 104; x \<noteq> 105; x \<noteq> 106; x \<noteq> 107; x \<noteq> 108; x \<noteq> 109; x \<noteq>
          110; x \<noteq> 111; x \<noteq> 112; x \<noteq> 113; x \<noteq> 114; x \<noteq> 115; x \<noteq> 116; x \<noteq> 117; x \<noteq> 118; x \<noteq> 119; x \<noteq>
          120; x \<noteq> 121; x \<noteq> 122; x \<noteq> 123; x \<noteq> 124; x \<noteq> 125; x \<noteq> 126; x \<noteq> 127; x \<noteq> 128; x \<noteq> 129; x \<noteq>
          130; x \<noteq> 131; x \<noteq> 132; x \<noteq> 133; x \<noteq> 134; x \<noteq> 135; x \<noteq> 136; x \<noteq> 137; x \<noteq> 138; x \<noteq> 139; x \<noteq>
          140; x \<noteq> 141; x \<noteq> 142; x \<noteq> 143; x \<noteq> 144; x \<noteq> 145; x \<noteq> 146; x \<noteq> 147; x \<noteq> 148; x \<noteq> 149; x \<noteq>
          150; x \<noteq> 151; x \<noteq> 152; x \<noteq> 153; x \<noteq> 154; x \<noteq> 155; x \<noteq> 156; x \<noteq> 157; x \<noteq> 158; x \<noteq> 159; x \<noteq>
          160; x \<noteq> 161; x \<noteq> 162; x \<noteq> 163; x \<noteq> 164; x \<noteq> 165; x \<noteq> 166; x \<noteq> 167; x \<noteq> 168; x \<noteq> 169; x \<noteq>
          170; x \<noteq> 171; x \<noteq> 172; x \<noteq> 173; x \<noteq> 174; x \<noteq> 175; x \<noteq> 176; x \<noteq> 177; x \<noteq> 178; x \<noteq> 179; x \<noteq>
          180; x \<noteq> 181; x \<noteq> 182; x \<noteq> 183; x \<noteq> 184; x \<noteq> 185; x \<noteq> 186; x \<noteq> 187; x \<noteq> 188; x \<noteq> 189; x \<noteq>
          190; x \<noteq> 191; x \<noteq> 192; x \<noteq> 193; x \<noteq> 194; x \<noteq> 195; x \<noteq> 196; x \<noteq> 197; x \<noteq> 198; x \<noteq> 199; x \<noteq>
          200; x \<noteq> 201; x \<noteq> 202; x \<noteq> 203; x \<noteq> 204; x \<noteq> 205; x \<noteq> 206; x \<noteq> 207; x \<noteq> 208; x \<noteq> 209; x \<noteq>
          210; x \<noteq> 211; x \<noteq> 212; x \<noteq> 213; x \<noteq> 214; x \<noteq> 215; x \<noteq> 216; x \<noteq> 217; x \<noteq> 218; x \<noteq> 219; x \<noteq>
          220; x \<noteq> 221; x \<noteq> 222; x \<noteq> 223; x \<noteq> 224; x \<noteq> 225; x \<noteq> 226; x \<noteq> 227; x \<noteq> 228; x \<noteq> 229; x \<noteq>
          230; x \<noteq> 231; x \<noteq> 232; x \<noteq> 233; x \<noteq> 234; x \<noteq> 235; x \<noteq> 236; x \<noteq> 237; x \<noteq> 238; x \<noteq> 239; x \<noteq>
          240; x \<noteq> 241; x \<noteq> 242; x \<noteq> 243; x \<noteq> 244; x \<noteq> 245; x \<noteq> 246; x \<noteq> 247; x \<noteq> 248; x \<noteq> 249; x \<noteq>
          250; x \<noteq> 251; x \<noteq> 252; x \<noteq> 253; x \<noteq> 254; x \<noteq> 255\<rbrakk> \<Longrightarrow> P"
  apply (subgoal_tac "x \<in> set enum", subst (asm) set_enum_word8_def)
    apply (drule set_strip_insert, assumption)+
   apply (erule emptyE)
  apply (subst enum_UNIV, rule UNIV_I)
  done

lemma upto_enum_red':
  assumes lt: "1 \<le> X"
  shows "[(0::'a :: len word) .e. X - 1] =  map of_nat [0 ..< unat X]"
proof -
  have lt': "unat X < 2 ^ LENGTH('a)"
    by (rule unat_lt2p)

  show ?thesis
    apply (subst upto_enum_red)
    apply (simp del: upt.simps)
    apply (subst Suc_unat_diff_1 [OF lt])
    apply (rule map_cong [OF refl])
    apply (rule toEnum_of_nat)
    apply simp
    apply (erule order_less_trans [OF _ lt'])
    done
qed

lemma upto_enum_red2:
  assumes szv: "sz < LENGTH('a :: len)"
  shows "[(0:: 'a :: len word) .e. 2 ^ sz - 1] =
  map of_nat [0 ..< 2 ^ sz]" using szv
  apply (subst unat_power_lower[OF szv, symmetric])
  apply (rule upto_enum_red')
  apply (subst word_le_nat_alt, simp)
  done

lemma upto_enum_step_red:
  assumes szv: "sz < LENGTH('a)"
  and   usszv: "us \<le> sz"
  shows "[0 :: 'a :: len word , 2 ^ us .e. 2 ^ sz - 1] =
  map (\<lambda>x. of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]" using szv
  unfolding upto_enum_step_def
  apply (subst if_not_P)
   apply (rule leD)
   apply (subst word_le_nat_alt)
   apply (subst unat_minus_one)
    apply simp
   apply simp
  apply simp
  apply (subst upto_enum_red)
  apply (simp del: upt.simps)
  apply (subst Suc_div_unat_helper [where 'a = 'a, OF szv usszv, symmetric])
  apply clarsimp
  apply (subst toEnum_of_nat)
   apply (erule order_less_trans)
   using szv
   apply simp
  apply simp
  done

lemma upto_enum_word:
  "[x .e. y] = map of_nat [unat x ..< Suc (unat y)]"
  apply (subst upto_enum_red)
  apply clarsimp
  apply (subst toEnum_of_nat)
   prefer 2
   apply (rule refl)
  apply (erule disjE, simp)
  apply clarsimp
  apply (erule order_less_trans)
  apply simp
  done

lemma word_upto_Cons_eq:
  "x < y \<Longrightarrow> [x::'a::len word .e. y] = x # [x + 1 .e. y]"
  apply (subst upto_enum_red)
  apply (subst upt_conv_Cons, unat_arith)
  apply (simp only: list.map list.inject upto_enum_red to_from_enum simp_thms)
  apply (rule map_cong[OF _ refl])
  apply (rule arg_cong2[where f = "\<lambda>x y. [x ..< y]"], unat_arith)
  apply (rule refl)
  done

lemma distinct_enum_upto:
  "distinct [(0 :: 'a::len word) .e. b]"
proof -
  have "\<And>(b::'a word). [0 .e. b] = nths enum {..< Suc (fromEnum b)}"
    apply (subst upto_enum_red)
    apply (subst nths_upt_eq_take)
    apply (subst enum_word_def)
    apply (subst take_map)
    apply (subst take_upt)
     apply (simp only: add_0 fromEnum_unat)
     apply (rule order_trans [OF _ order_eq_refl])
      apply (rule Suc_leI [OF unat_lt2p])
     apply simp
    apply clarsimp
    apply (rule toEnum_of_nat)
    apply (erule order_less_trans [OF _ unat_lt2p])
    done

  then show ?thesis
    by (rule ssubst) (rule distinct_nthsI, simp)
qed

lemma upto_enum_set_conv [simp]:
  fixes a :: "'a :: len word"
  shows "set [a .e. b] = {x. a \<le> x \<and> x \<le> b}"
  apply (subst upto_enum_red)
  apply (subst set_map)
  apply safe
    apply simp
    apply clarsimp
    apply (erule disjE)
     apply simp
     apply (erule iffD2 [OF word_le_nat_alt])
    apply clarsimp
    apply (erule word_unat.Rep_cases [OF unat_le [OF order_less_imp_le]])
    apply simp
    apply (erule iffD2 [OF word_le_nat_alt])
   apply simp

   apply clarsimp
   apply (erule disjE)
    apply simp
   apply clarsimp
   apply (rule word_unat.Rep_cases [OF unat_le  [OF order_less_imp_le]])
    apply assumption
   apply simp
   apply (erule order_less_imp_le [OF iffD2 [OF word_less_nat_alt]])
  apply clarsimp
  apply (rule_tac x="fromEnum x" in image_eqI)
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply (subst word_le_nat_alt [symmetric])
   apply simp
  apply safe
   apply (simp add: word_le_nat_alt [symmetric])
  apply (simp add: word_less_nat_alt [symmetric])
  done

lemma upto_enum_less:
  assumes xin: "x \<in> set [(a::'a::len word).e.2 ^ n - 1]"
  and     nv:  "n < LENGTH('a::len)"
  shows   "x < 2 ^ n"
proof (cases n)
  case 0
  then show ?thesis using xin by simp
next
  case (Suc m)
  show ?thesis using xin nv by simp
qed

lemma upto_enum_len_less:
  "\<lbrakk> n \<le> length [a, b .e. c]; n \<noteq> 0 \<rbrakk> \<Longrightarrow> a \<le> c"
  unfolding upto_enum_step_def
  by (simp split: if_split_asm)

lemma length_upto_enum_step:
  fixes x :: "'a :: len word"
  shows "x \<le> z \<Longrightarrow> length [x , y .e. z] = (unat ((z - x) div (y - x))) + 1"
  unfolding upto_enum_step_def
  by (simp add: upto_enum_red)

lemma map_length_unfold_one:
  fixes x :: "'a::len word"
  assumes xv: "Suc (unat x) < 2 ^ LENGTH('a)"
  and     ax: "a < x"
  shows   "map f [a .e. x] = f a # map f [a + 1 .e. x]"
  by (subst word_upto_Cons_eq, auto, fact+)

lemma upto_enum_set_conv2:
  fixes a :: "'a::len word"
  shows "set [a .e. b] = {a .. b}"
  by auto

lemma of_nat_unat [simp]:
  "of_nat \<circ> unat = id"
  by (rule ext, simp)

lemma Suc_unat_minus_one [simp]:
  "x \<noteq> 0 \<Longrightarrow> Suc (unat (x - 1)) = unat x"
  by (metis Suc_diff_1 unat_gt_0 unat_minus_one)

lemma word_add_le_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k \<le> j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i \<le> j"
  using uik ujk le
  by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem] elim: add_le_mono1)

lemma mask_shift:
  "(x && ~~ (mask y)) >> y = x >> y"
  by word_eqI

lemma word_add_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k \<le> j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: add_le_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_le_mono2:
  fixes i :: "'a :: len word"
  shows "\<lbrakk>i \<le> j; unat j + unat k < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> k + i \<le> k + j"
  by (subst field_simps, subst field_simps, erule (1) word_add_le_mono1)

lemma word_add_le_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k \<le> j + k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i + k \<le> j + k" by (rule word_add_le_mono1) fact+
next
  assume "i + k \<le> j + k"
  show "i \<le> j" by (rule word_add_le_dest) fact+
qed

lemma word_add_less_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i < j"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i + k < j + k"
proof -
  from ij ujk have jk: "unat i + unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_less_nat_alt elim: add_less_mono1)

  then show ?thesis using ujk ij
    by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem])
qed

lemma word_add_less_dest:
  fixes i :: "'a :: len word"
  assumes le: "i + k < j + k"
  and    uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and    ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "i < j"
  using uik ujk le
  by (auto simp: word_less_nat_alt iffD1 [OF unat_add_lem] elim: add_less_mono1)

lemma word_add_less_iff:
  fixes i :: "'a :: len word"
  assumes uik: "unat i + unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j + unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i + k < j + k) = (i < j)"
proof
  assume "i < j"
  show "i + k < j + k" by (rule word_add_less_mono1) fact+
next
  assume "i + k < j + k"
  show "i < j" by (rule word_add_less_dest) fact+
qed

lemma shiftr_div_2n':
  "unat (w >> n) = unat w div 2 ^ n"
  apply (unfold unat_def)
  apply (subst shiftr_div_2n)
  apply (subst nat_div_distrib)
   apply simp
  apply (simp add: nat_power_eq)
  done

lemma shiftl_shiftr_id:
  assumes nv: "n < LENGTH('a)"
  and     xv: "x < 2 ^ (LENGTH('a) - n)"
  shows "x << n >> n = (x::'a::len word)"
  apply (simp add: shiftl_t2n)
  apply (rule word_unat.Rep_eqD)
  apply (subst shiftr_div_2n')
  apply (cases n)
   apply simp
  apply (subst iffD1 [OF unat_mult_lem])+
   apply (subst unat_power_lower[OF nv])
   apply (rule nat_less_power_trans [OF _ order_less_imp_le [OF nv]])
   apply (rule order_less_le_trans [OF unat_mono [OF xv] order_eq_refl])
   apply (rule unat_power_lower)
   apply simp
  apply (subst unat_power_lower[OF nv])
  apply simp
  done

lemma ucast_shiftl_eq_0:
  fixes w :: "'a :: len word"
  shows "\<lbrakk> n \<ge> LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (w << n) = (0 :: 'b :: len word)"
  by (case_tac "size w \<le> n", clarsimp simp: shiftl_zero_size)
     (clarsimp simp: not_le ucast_bl bl_shiftl bang_eq test_bit_of_bl rev_nth nth_append)

lemma word_mult_less_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k < j * k) = (i < j)"
  using assms by (rule word_mult_less_cancel)

lemma word_le_imp_diff_le:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n \<le> m\<rbrakk> \<Longrightarrow> n - k \<le> m"
  by (auto simp: unat_sub word_le_nat_alt)

lemma word_less_imp_diff_less:
  fixes n :: "'a::len word"
  shows "\<lbrakk>k \<le> n; n < m\<rbrakk> \<Longrightarrow> n - k < m"
  by (clarsimp simp: unat_sub word_less_nat_alt
             intro!: less_imp_diff_less)

lemma word_mult_le_mono1:
  fixes i :: "'a :: len word"
  assumes ij: "i \<le> j"
  and    knz: "0 < k"
  and    ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "i * k \<le> j * k"
proof -
  from ij ujk knz have jk: "unat i * unat k < 2 ^ len_of TYPE ('a)"
    by (auto elim: order_le_less_subst2 simp: word_le_nat_alt elim: mult_le_mono1)

  then show ?thesis using ujk knz ij
    by (auto simp: word_le_nat_alt iffD1 [OF unat_mult_lem])
qed

lemma word_mult_le_iff:
  fixes i :: "'a :: len word"
  assumes knz: "0 < k"
  and     uik: "unat i * unat k < 2 ^ len_of TYPE ('a)"
  and     ujk: "unat j * unat k < 2 ^ len_of TYPE ('a)"
  shows  "(i * k \<le> j * k) = (i \<le> j)"
proof
  assume "i \<le> j"
  show "i * k \<le> j * k" by (rule word_mult_le_mono1) fact+
next
  assume p: "i * k \<le> j * k"

  have "0 < unat k" using knz by (simp add: word_less_nat_alt)
  then show "i \<le> j" using p
    by (clarsimp simp: word_le_nat_alt iffD1 [OF unat_mult_lem uik]
      iffD1 [OF unat_mult_lem ujk])
qed

lemma word_diff_less:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>0 < n; 0 < m; n \<le> m\<rbrakk> \<Longrightarrow> m - n < m"
  apply (subst word_less_nat_alt)
  apply (subst unat_sub)
   apply assumption
  apply (rule diff_less)
   apply (simp_all add: word_less_nat_alt)
   done

lemma MinI:
  assumes fa: "finite A"
  and     ne: "A \<noteq> {}"
  and     xv: "m \<in> A"
  and    min: "\<forall>y \<in> A. m \<le> y"
  shows "Min A = m" using fa ne xv min
proof (induct A arbitrary: m rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case (insert y F)

  from insert.prems have yx: "m \<le> y" and fx: "\<forall>y \<in> F. m \<le> y" by auto
  have "m \<in> insert y F" by fact
  then show ?case
  proof
    assume mv: "m = y"

    have mlt: "m \<le> Min F"
      by (rule iffD2 [OF Min_ge_iff [OF insert.hyps(1) insert.hyps(2)] fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mv [symmetric])
      apply (auto simp: min_def mlt)
      done
  next
    assume "m \<in> F"
    then have mf: "Min F = m"
      by (rule insert.hyps(4) [OF _ fx])

    show ?case
      apply (subst Min_insert [OF insert.hyps(1) insert.hyps(2)])
      apply (subst mf)
      apply (rule iffD2 [OF _ yx])
      apply (auto simp: min_def)
      done
  qed
qed

lemma length_upto_enum [simp]:
  fixes a :: "'a :: len word"
  shows "length [a .e. b] = Suc (unat b) - unat a"
  apply (simp add: word_le_nat_alt upto_enum_red)
  apply (clarsimp simp: Suc_diff_le)
  done

lemma length_upto_enum_cases:
  fixes a :: "'a::len word"
  shows "length [a .e. b] = (if a \<le> b then Suc (unat b) - unat a else 0)"
  apply (case_tac "a \<le> b")
   apply (clarsimp)
  apply (clarsimp simp: upto_enum_def)
  apply unat_arith
  done

lemma length_upto_enum_less_one:
  "\<lbrakk>a \<le> b; b \<noteq> 0\<rbrakk>
  \<Longrightarrow> length [a .e. b - 1] = unat (b - a)"
  apply clarsimp
  apply (subst unat_sub[symmetric], assumption)
  apply clarsimp
  done

lemma drop_upto_enum:
  "drop (unat n) [0 .e. m] = [n .e. m]"
  apply (clarsimp simp: upto_enum_def)
  apply (induct m, simp)
  by (metis drop_map drop_upt plus_nat.add_0)

lemma distinct_enum_upto' [simp]:
  "distinct [a::'a::len word .e. b]"
  apply (subst drop_upto_enum [symmetric])
  apply (rule distinct_drop)
  apply (rule distinct_enum_upto)
  done

lemma length_interval:
  "\<lbrakk>set xs = {x. (a::'a::len word) \<le> x \<and> x \<le> b}; distinct xs\<rbrakk>
  \<Longrightarrow> length xs = Suc (unat b) - unat a"
  apply (frule distinct_card)
  apply (subgoal_tac "set xs = set [a .e. b]")
   apply (cut_tac distinct_card [where xs="[a .e. b]"])
    apply (subst (asm) length_upto_enum)
    apply clarsimp
   apply (rule distinct_enum_upto')
  apply simp
  done

lemma not_empty_eq:
  "(S \<noteq> {}) = (\<exists>x. x \<in> S)"
  by auto

lemma range_subset_lower:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> c \<le> a"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_upper:
  fixes c :: "'a ::linorder"
  shows "\<lbrakk> {a..b} \<subseteq> {c..d}; x \<in> {a..b} \<rbrakk> \<Longrightarrow> b \<le> d"
  apply (frule (1) subsetD)
  apply (rule classical)
  apply clarsimp
  done

lemma range_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subseteq> {c..d}) = (c \<le> a \<and> b \<le> d)"
  apply (insert non_empty)
  apply (rule iffI)
   apply (frule range_subset_lower [where x=a], simp)
   apply (drule range_subset_upper [where x=a], simp)
   apply simp
  apply auto
  done

lemma range_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} = {c..d}) = (a = c \<and> b = d)"
  by (metis atLeastatMost_subset_iff eq_iff non_empty)

lemma range_strict_subset_eq:
  fixes a::"'a::linorder"
  assumes non_empty: "a \<le> b"
  shows "({a..b} \<subset> {c..d}) = (c \<le> a \<and> b \<le> d \<and> (a = c \<longrightarrow> b \<noteq> d))"
  apply (insert non_empty)
  apply (subst psubset_eq)
  apply (subst range_subset_eq, assumption+)
  apply (subst range_eq, assumption+)
  apply simp
  done

lemma range_subsetI:
  fixes x :: "'a :: order"
  assumes xX: "X \<le> x"
  and     yY: "y \<le> Y"
  shows   "{x .. y} \<subseteq> {X .. Y}"
  using xX yY by auto

lemma set_False [simp]:
  "(set bs \<subseteq> {False}) = (True \<notin> set bs)" by auto

declare of_nat_power [simp del]

(* TODO: move to word *)
lemma unat_of_bl_length:
  "unat (of_bl xs :: 'a::len word) < 2 ^ (length xs)"
proof (cases "length xs < LENGTH('a)")
  case True
  then have "(of_bl xs::'a::len word) < 2 ^ length xs"
    by (simp add: of_bl_length_less)
  with True
  show ?thesis
    by (simp add: word_less_nat_alt word_unat_power unat_of_nat)
next
  case False
  have "unat (of_bl xs::'a::len word) < 2 ^ LENGTH('a)"
    by (simp split: unat_split)
  also
  from False
  have "LENGTH('a) \<le> length xs" by simp
  then have "2 ^ LENGTH('a) \<le> (2::nat) ^ length xs"
    by (rule power_increasing) simp
  finally
  show ?thesis .
qed

lemma is_aligned_0'[simp]:
  "is_aligned 0 n"
  by (simp add: is_aligned_def)

lemma p_assoc_help:
  fixes p :: "'a::{ring,power,numeral,one}"
  shows "p + 2^sz - 1 = p + (2^sz - 1)"
  by simp

lemma word_add_increasing:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p + w \<le> x; p \<le> p + w \<rbrakk> \<Longrightarrow> p \<le> x"
  by unat_arith

lemma word_random:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> p \<le> p + x'; x \<le> x' \<rbrakk> \<Longrightarrow> p \<le> p + x"
  by unat_arith

lemma word_sub_mono:
  "\<lbrakk> a \<le> c; d \<le> b; a - b \<le> a; c - d \<le> c \<rbrakk>
    \<Longrightarrow> (a - b) \<le> (c - d :: 'a :: len word)"
  by unat_arith

lemma power_not_zero:
  "n < LENGTH('a::len) \<Longrightarrow> (2 :: 'a word) ^ n \<noteq> 0"
  by (metis p2_gt_0 word_neq_0_conv)

lemma word_gt_a_gt_0:
  "a < n \<Longrightarrow> (0 :: 'a::len word) < n"
  apply (case_tac "n = 0")
   apply clarsimp
  apply (clarsimp simp: word_neq_0_conv)
  done

lemma word_shift_nonzero:
  "\<lbrakk> (x::'a::len word) \<le> 2 ^ m; m + n < LENGTH('a::len); x \<noteq> 0\<rbrakk>
   \<Longrightarrow> x << n \<noteq> 0"
  apply (simp only: word_neq_0_conv word_less_nat_alt
                    shiftl_t2n mod_0 unat_word_ariths
                    unat_power_lower word_le_nat_alt)
  apply (subst mod_less)
   apply (rule order_le_less_trans)
    apply (erule mult_le_mono2)
   apply (subst power_add[symmetric])
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply simp
  done

lemma word_power_less_1 [simp]:
  "sz < LENGTH('a::len) \<Longrightarrow> (2::'a word) ^ sz - 1 < 2 ^ sz"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_minus_one)
  apply (simp add: word_unat.Rep_inject [symmetric])
  apply simp
  done

lemma nasty_split_lt:
  "\<lbrakk> (x :: 'a:: len word) < 2 ^ (m - n); n \<le> m; m < LENGTH('a::len) \<rbrakk>
     \<Longrightarrow> x * 2 ^ n + (2 ^ n - 1) \<le> 2 ^ m - 1"
  apply (simp only: add_diff_eq)
  apply (subst mult_1[symmetric], subst distrib_right[symmetric])
  apply (rule word_sub_mono)
     apply (rule order_trans)
      apply (rule word_mult_le_mono1)
        apply (rule inc_le)
        apply assumption
       apply (subst word_neq_0_conv[symmetric])
       apply (rule power_not_zero)
       apply simp
      apply (subst unat_power_lower, simp)+
      apply (subst power_add[symmetric])
      apply (rule power_strict_increasing)
       apply simp
      apply simp
     apply (subst power_add[symmetric])
     apply simp
    apply simp
   apply (rule word_sub_1_le)
   apply (subst mult.commute)
   apply (subst shiftl_t2n[symmetric])
   apply (rule word_shift_nonzero)
     apply (erule inc_le)
    apply simp
   apply (unat_arith)
  apply (drule word_power_less_1)
  apply simp
  done

lemma nasty_split_less:
  "\<lbrakk>m \<le> n; n \<le> nm; nm < LENGTH('a::len); x < 2 ^ (nm - n)\<rbrakk>
   \<Longrightarrow> (x :: 'a word) * 2 ^ n + (2 ^ m - 1) < 2 ^ nm"
  apply (simp only: word_less_sub_le[symmetric])
  apply (rule order_trans [OF _ nasty_split_lt])
     apply (rule word_plus_mono_right)
      apply (rule word_sub_mono)
         apply (simp add: word_le_nat_alt)
        apply simp
       apply (simp add: word_sub_1_le[OF power_not_zero])
      apply (simp add: word_sub_1_le[OF power_not_zero])
     apply (rule is_aligned_no_wrap')
      apply (rule is_aligned_mult_triv2)
     apply simp
    apply (erule order_le_less_trans, simp)
   apply simp+
  done

lemma int_not_emptyD:
  "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<and> x \<in> B"
  by (erule contrapos_np, clarsimp simp: disjoint_iff_not_equal)

lemma unat_less_power:
  fixes k :: "'a::len word"
  assumes szv: "sz < LENGTH('a)"
  and     kv:  "k < 2 ^ sz"
  shows   "unat k < 2 ^ sz"
  using szv unat_mono [OF kv] by simp

lemma unat_mult_power_lem:
  assumes kv: "k < 2 ^ (LENGTH('a::len) - sz)"
  shows "unat (2 ^ sz * of_nat k :: (('a::len) word)) = 2 ^ sz * k"
proof cases
  assume szv: "sz < LENGTH('a::len)"
  show ?thesis
  proof (cases "sz = 0")
    case True
    then show ?thesis using kv szv
     by (simp add: unat_of_nat)
  next
    case False
    then have sne: "0 < sz" ..

    have uk: "unat (of_nat k :: 'a word) = k"
      apply (subst unat_of_nat)
      apply (simp add: nat_mod_eq less_trans[OF kv] sne)
      done

    show ?thesis using szv
      apply (subst iffD1 [OF unat_mult_lem])
      apply (simp add: uk nat_less_power_trans[OF kv order_less_imp_le [OF szv]])+
      done
  qed
next
  assume "\<not> sz < LENGTH('a)"
  with kv show ?thesis by (simp add: not_less power_overflow)
qed

lemma aligned_add_offset_no_wrap:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off < 2 ^ sz"
  shows  "unat x + unat off < 2 ^ LENGTH('a)"
proof cases
  assume szv: "sz < LENGTH('a)"
  from al obtain k where xv: "x = 2 ^ sz * (of_nat k)"
    and kl: "k < 2 ^ (LENGTH('a) - sz)"
    by (auto elim: is_alignedE)

  show ?thesis using szv
    apply (subst xv)
    apply (subst unat_mult_power_lem[OF kl])
    apply (subst mult.commute, rule nat_add_offset_less)
      apply (rule less_le_trans[OF unat_mono[OF offv, simplified]])
      apply (erule eq_imp_le[OF unat_power_lower])
     apply (rule kl)
    apply simp
   done
next
  assume "\<not> sz < LENGTH('a)"
  with offv show ?thesis by (simp add: not_less power_overflow )
qed

lemma aligned_add_offset_mod:
  fixes x :: "('a::len) word"
  assumes al: "is_aligned x sz"
  and     kv: "k < 2 ^ sz"
  shows   "(x + k) mod 2 ^ sz = k"
proof cases
  assume szv: "sz < LENGTH('a)"

  have ux: "unat x + unat k < 2 ^ LENGTH('a)"
    by (rule aligned_add_offset_no_wrap) fact+

  show ?thesis using al szv
    apply -
    apply (erule is_alignedE)
    apply (subst word_unat.Rep_inject [symmetric])
    apply (subst unat_mod)
    apply (subst iffD1 [OF unat_add_lem], rule ux)
    apply simp
    apply (subst unat_mult_power_lem, assumption+)
    apply (simp)
    apply (rule mod_less[OF less_le_trans[OF unat_mono], OF kv])
    apply (erule eq_imp_le[OF unat_power_lower])
    done
next
  assume "\<not> sz < LENGTH('a)"
  with al show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask mask_def
                  word_mod_by_0)
qed

lemma word_plus_mcs_4:
  "\<lbrakk>v + x \<le> w + x; x \<le> v + x\<rbrakk> \<Longrightarrow> v \<le> (w::'a::len word)"
  by uint_arith

lemma word_plus_mcs_3:
  "\<lbrakk>v \<le> w; x \<le> w + x\<rbrakk> \<Longrightarrow> v + x \<le> w + (x::'a::len word)"
  by unat_arith

lemma aligned_neq_into_no_overlap:
  fixes x :: "'a::len word"
  assumes neq: "x \<noteq> y"
  and     alx: "is_aligned x sz"
  and     aly: "is_aligned y sz"
  shows  "{x .. x + (2 ^ sz - 1)} \<inter> {y .. y + (2 ^ sz - 1)} = {}"
proof cases
  assume szv: "sz < LENGTH('a)"
  show ?thesis
  proof (rule equals0I, clarsimp)
    fix z
    assume xb: "x \<le> z" and xt: "z \<le> x + (2 ^ sz - 1)"
      and yb: "y \<le> z" and yt: "z \<le> y + (2 ^ sz - 1)"

    have rl: "\<And>(p::'a word) k w. \<lbrakk>uint p + uint k < 2 ^ LENGTH('a); w = p + k; w \<le> p + (2 ^ sz - 1) \<rbrakk>
      \<Longrightarrow> k < 2 ^ sz"
      apply -
      apply simp
      apply (subst (asm) add.commute, subst (asm) add.commute, drule word_plus_mcs_4)
      apply (subst add.commute, subst no_plus_overflow_uint_size)
      apply (simp add: word_size_bl)
      apply (erule iffD1 [OF word_less_sub_le[OF szv]])
      done

    from xb obtain kx where
      kx: "z = x + kx" and
      kxl: "uint x + uint kx < 2 ^ LENGTH('a)"
      by (clarsimp dest!: word_le_exists')

    from yb obtain ky where
      ky: "z = y + ky" and
      kyl: "uint y + uint ky < 2 ^ LENGTH('a)"
      by (clarsimp dest!: word_le_exists')

    have "x = y"
    proof -
      have "kx = z mod 2 ^ sz"
      proof (subst kx, rule sym, rule aligned_add_offset_mod)
        show "kx < 2 ^ sz" by (rule rl) fact+
      qed fact+

      also have "\<dots> = ky"
      proof (subst ky, rule aligned_add_offset_mod)
        show "ky < 2 ^ sz"
          using kyl ky yt by (rule rl)
      qed fact+

      finally have kxky: "kx = ky" .
      moreover have "x + kx = y + ky" by (simp add: kx [symmetric] ky [symmetric])
      ultimately show ?thesis by simp
    qed

    then show False using neq by simp
  qed
next
  assume "\<not> sz < LENGTH('a)"
  with neq alx aly
  have False by (simp add: is_aligned_mask mask_def power_overflow)
  then show ?thesis ..
qed

lemma less_two_pow_divD:
  "\<lbrakk> (x :: nat) < 2 ^ n div 2 ^ m \<rbrakk>
    \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (rule context_conjI)
   apply (rule ccontr)
   apply (simp add: power_strict_increasing)
  apply (simp add: power_sub)
  done

lemma less_two_pow_divI:
  "\<lbrakk> (x :: nat) < 2 ^ (n - m); m \<le> n \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  by (simp add: power_sub)

lemma word_less_two_pow_divI:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (n - m); m \<le> n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> x < 2 ^ n div 2 ^ m"
  apply (simp add: word_less_nat_alt)
  apply (subst unat_word_ariths)
  apply (subst mod_less)
   apply (rule order_le_less_trans [OF div_le_dividend])
   apply (rule unat_lt2p)
  apply (simp add: power_sub)
  done

lemma word_less_two_pow_divD:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ n div 2 ^ m \<rbrakk>
     \<Longrightarrow> n \<ge> m \<and> (x < 2 ^ (n - m))"
  apply (cases "n < LENGTH('a)")
   apply (cases "m < LENGTH('a)")
    apply (simp add: word_less_nat_alt)
    apply (subst(asm) unat_word_ariths)
    apply (subst(asm) mod_less)
     apply (rule order_le_less_trans [OF div_le_dividend])
     apply (rule unat_lt2p)
    apply (clarsimp dest!: less_two_pow_divD)
   apply (simp add: power_overflow)
   apply (simp add: word_div_def)
  apply (simp add: power_overflow word_div_def)
  done

lemma of_nat_less_two_pow_div_set:
  "\<lbrakk> n < LENGTH('a) \<rbrakk> \<Longrightarrow>
   {x. x < (2 ^ n div 2 ^ m :: 'a::len word)}
      = of_nat ` {k. k < 2 ^ n div 2 ^ m}"
  apply (simp add: image_def)
  apply (safe dest!: word_less_two_pow_divD less_two_pow_divD
             intro!: word_less_two_pow_divI)
   apply (rule_tac x="unat x" in exI)
   apply (simp add: power_sub[symmetric])
   apply (subst unat_power_lower[symmetric, where 'a='a])
    apply simp
   apply (erule unat_mono)
  apply (subst word_unat_power)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply assumption
  done

lemma  word_less_power_trans2:
  fixes n :: "'a::len word"
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk> \<Longrightarrow> n * 2 ^ k < 2 ^ m"
  by (subst field_simps, rule word_less_power_trans)

(* shadows the slightly weaker Word.nth_ucast *)
lemma nth_ucast:
  "(ucast (w::'a::len0 word)::'b::len0 word) !! n =
   (w !! n \<and> n < min LENGTH('a) LENGTH('b))"
  by (simp add: ucast_def test_bit_bin word_ubin.eq_norm nth_bintr word_size)
     (fast elim!: bin_nth_uint_imp)

lemma ucast_less:
  "LENGTH('b) < LENGTH('a) \<Longrightarrow>
   (ucast (x :: 'b :: len word) :: ('a :: len word)) < 2 ^ LENGTH('b)"
  by (meson Word.nth_ucast test_bit_conj_lt le_def upper_bits_unset_is_l2p)

lemma ucast_range_less:
  "LENGTH('a :: len) < LENGTH('b :: len) \<Longrightarrow>
   range (ucast :: 'a word \<Rightarrow> 'b word) = {x. x < 2 ^ len_of TYPE ('a)}"
  apply safe
   apply (erule ucast_less)
  apply (simp add: image_def)
  apply (rule_tac x="ucast x" in exI)
  by word_eqI_solve

lemma word_power_less_diff:
  "\<lbrakk>2 ^ n * q < (2::'a::len word) ^ m; q < 2 ^ (LENGTH('a) - n)\<rbrakk> \<Longrightarrow> q < 2 ^ (m - n)"
  apply (case_tac "m \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (case_tac "n \<ge> LENGTH('a)")
   apply (simp add: power_overflow)
  apply (cases "n = 0")
   apply simp
  apply (subst word_less_nat_alt)
  apply (subst unat_power_lower)
   apply simp
  apply (rule nat_power_less_diff)
  apply (simp add: word_less_nat_alt)
  apply (subst (asm) iffD1 [OF unat_mult_lem])
   apply (simp add:nat_less_power_trans)
  apply simp
  done

lemmas word_diff_ls'' = word_diff_ls [where xa=x and x=x for x]
lemmas word_diff_ls' = word_diff_ls'' [simplified]

lemmas word_l_diffs' = word_l_diffs [where xa=x and x=x for x]
lemmas word_l_diffs = word_l_diffs' [simplified]

lemma is_aligned_diff:
  fixes m :: "'a::len word"
  assumes alm: "is_aligned m s1"
  and     aln: "is_aligned n s2"
  and    s2wb: "s2 < LENGTH('a)"
  and      nm: "m \<in> {n .. n + (2 ^ s2 - 1)}"
  and    s1s2: "s1 \<le> s2"
  and     s10: "0 < s1" (* Probably can be folded into the proof \<dots> *)
  shows  "\<exists>q. m - n = of_nat q * 2 ^ s1 \<and> q < 2 ^ (s2 - s1)"
proof -
  have rl: "\<And>m s. \<lbrakk> m < 2 ^ (LENGTH('a) - s); s < LENGTH('a) \<rbrakk> \<Longrightarrow> unat ((2::'a word) ^ s * of_nat m) = 2 ^ s * m"
  proof -
    fix m :: nat and  s
    assume m: "m < 2 ^ (LENGTH('a) - s)" and s: "s < LENGTH('a)"
    then have "unat ((of_nat m) :: 'a word) = m"
      apply (subst unat_of_nat)
      apply (subst mod_less)
       apply (erule order_less_le_trans)
       apply (rule power_increasing)
        apply simp_all
      done

    then show "?thesis m s" using s m
      apply (subst iffD1 [OF unat_mult_lem])
      apply (simp add: nat_less_power_trans)+
      done
  qed
  have s1wb: "s1 < LENGTH('a)" using s2wb s1s2 by simp
  from alm obtain mq where mmq: "m = 2 ^ s1 * of_nat mq" and mq: "mq < 2 ^ (LENGTH('a) - s1)"
    by (auto elim: is_alignedE simp: field_simps)
  from aln obtain nq where nnq: "n = 2 ^ s2 * of_nat nq" and nq: "nq < 2 ^ (LENGTH('a) - s2)"
    by (auto elim: is_alignedE simp: field_simps)
  from s1s2 obtain sq where sq: "s2 = s1 + sq" by (auto simp: le_iff_add)

  note us1 = rl [OF mq s1wb]
  note us2 = rl [OF nq s2wb]

  from nm have "n \<le> m" by clarsimp
  then have "(2::'a word) ^ s2 * of_nat nq \<le> 2 ^ s1 * of_nat mq" using nnq mmq by simp
  then have "2 ^ s2 * nq \<le> 2 ^ s1 * mq" using s1wb s2wb
    by (simp add: word_le_nat_alt us1 us2)
  then have nqmq: "2 ^ sq * nq \<le> mq" using sq by (simp add: power_add)

  have "m - n = 2 ^ s1 * of_nat mq - 2 ^ s2 * of_nat nq" using mmq nnq by simp
  also have "\<dots> = 2 ^ s1 * of_nat mq - 2 ^ s1 * 2 ^ sq * of_nat nq" using sq by (simp add: power_add)
  also have "\<dots> = 2 ^ s1 * (of_nat mq - 2 ^ sq * of_nat nq)" by (simp add: field_simps)
  also have "\<dots> = 2 ^ s1 * of_nat (mq - 2 ^ sq * nq)" using s1wb s2wb us1 us2 nqmq
    by (simp add:  word_unat_power)
  finally have mn: "m - n = of_nat (mq - 2 ^ sq * nq) * 2 ^ s1" by simp
  moreover
  from nm have "m - n \<le> 2 ^ s2 - 1"
    by - (rule word_diff_ls', (simp add: field_simps)+)
  then have "(2::'a word) ^ s1 * of_nat (mq - 2 ^ sq * nq) < 2 ^ s2" using mn s2wb by (simp add: field_simps)
  then have "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (s2 - s1)"
  proof (rule word_power_less_diff)
    have mm: "mq - 2 ^ sq * nq < 2 ^ (LENGTH('a) - s1)" using mq by simp
    moreover from s10 have "LENGTH('a) - s1 < LENGTH('a)"
      by (rule diff_less, simp)
    ultimately show "of_nat (mq - 2 ^ sq * nq) < (2::'a word) ^ (LENGTH('a) - s1)"
      apply (simp add: word_less_nat_alt)
      apply (subst unat_of_nat)
      apply (subst mod_less)
       apply (erule order_less_le_trans)
       apply simp+
      done
  qed
  then have "mq - 2 ^ sq * nq < 2 ^ (s2 - s1)" using mq s2wb
    apply (simp add: word_less_nat_alt)
    apply (subst (asm) unat_of_nat)
    apply (subst (asm) mod_less)
    apply (rule order_le_less_trans)
    apply (rule diff_le_self)
    apply (erule order_less_le_trans)
    apply simp
    apply assumption
    done
  ultimately show ?thesis by auto
qed

lemma word_less_sub_1:
  "x < (y :: 'a :: len word) \<Longrightarrow> x \<le> y - 1"
  apply (erule udvd_minus_le')
   apply (simp add: udvd_def)+
  done

lemma word_sub_mono2:
  "\<lbrakk> a + b \<le> c + d; c \<le> a; b \<le> a + b; d \<le> c + d \<rbrakk>
    \<Longrightarrow> b \<le> (d :: 'a :: len word)"
  apply (drule(1) word_sub_mono)
    apply simp
   apply simp
  apply simp
  done

lemma word_not_le:
  "(\<not> x \<le> (y :: 'a :: len word)) = (y < x)"
  by fastforce

lemma word_subset_less:
  "\<lbrakk> {x .. x + r - 1} \<subseteq> {y .. y + s - 1};
     x \<le> x + r - 1; y \<le> y + (s :: 'a :: len word) - 1;
     s \<noteq> 0 \<rbrakk>
     \<Longrightarrow> r \<le> s"
  apply (frule subsetD[where c=x])
   apply simp
  apply (drule subsetD[where c="x + r - 1"])
   apply simp
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (drule(1) word_sub_mono2)
    apply (simp_all add: olen_add_eqv[symmetric])
  apply (erule word_le_minus_cancel)
  apply (rule ccontr)
  apply (simp add: word_not_le)
  done

lemma uint_power_lower:
  "n < LENGTH('a) \<Longrightarrow> uint (2 ^ n :: 'a :: len word) = (2 ^ n :: int)"
  by (rule uint_2p_alt)

lemma power_le_mono:
  "\<lbrakk>2 ^ n \<le> (2::'a::len word) ^ m; n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> n \<le> m"
  apply (clarsimp simp add: le_less)
  apply safe
  apply (simp add: word_less_nat_alt)
  apply (simp only: uint_arith_simps(3))
  apply (drule uint_power_lower)+
  apply simp
  done

lemma sublist_equal_part:
  "prefix xs ys \<Longrightarrow> take (length xs) ys = xs"
  by (clarsimp simp: prefix_def)

lemma two_power_eq:
  "\<lbrakk>n < LENGTH('a); m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> ((2::'a::len word) ^ n = 2 ^ m) = (n = m)"
  apply safe
  apply (rule order_antisym)
   apply (simp add: power_le_mono[where 'a='a])+
  done

lemma prefix_length_less:
  "strict_prefix xs ys \<Longrightarrow> length xs < length ys"
  apply (clarsimp simp: strict_prefix_def)
  apply (frule prefix_length_le)
  apply (rule ccontr, simp)
  apply (clarsimp simp: prefix_def)
  done

lemmas take_less = take_strict_prefix

lemma not_prefix_longer:
  "\<lbrakk> length xs > length ys \<rbrakk> \<Longrightarrow> \<not> prefix xs ys"
  by (clarsimp dest!: prefix_length_le)

lemma of_bl_length:
  "length xs < LENGTH('a) \<Longrightarrow> of_bl xs < (2 :: 'a::len word) ^ length xs"
  by (simp add: of_bl_length_less)

lemma unat_of_nat_eq:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x ::'a::len word) = x"
  by (rule unat_of_nat_len)

lemma unat_eq_of_nat:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat (x :: 'a::len word) = n) = (x = of_nat n)"
  by (subst unat_of_nat_eq[where x=n, symmetric], simp+)

lemma unat_less_helper:
  "x < of_nat n \<Longrightarrow> unat x < n"
  apply (simp add: word_less_nat_alt)
  apply (erule order_less_le_trans)
  apply (simp add: unat_of_nat)
  done

lemma nat_uint_less_helper:
  "nat (uint y) = z \<Longrightarrow> x < y \<Longrightarrow> nat (uint x) < z"
  apply (erule subst)
  apply (subst unat_def [symmetric])
  apply (subst unat_def [symmetric])
  by (simp add: unat_mono)

lemma of_nat_0:
  "\<lbrakk>of_nat n = (0::'a::len word); n < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> n = 0"
  by (drule unat_of_nat_eq, simp)

lemma word_leq_le_minus_one:
  "\<lbrakk> x \<le> y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x - 1 < (y :: 'a :: len word)"
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst unat_minus_one)
   apply assumption
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma of_nat_inj:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
   (of_nat x = (of_nat y :: 'a :: len word)) = (x = y)"
  by (simp add: word_unat.norm_eq_iff [symmetric])

lemma map_prefixI:
  "prefix xs ys \<Longrightarrow> prefix (map f xs) (map f ys)"
  by (clarsimp simp: prefix_def)

lemma if_Some_None_eq_None:
  "((if P then Some v else None) = None) = (\<not> P)"
  by simp

lemma CollectPairFalse [iff]:
  "{(a,b). False} = {}"
  by (simp add: split_def)

lemma if_conj_dist:
  "((if b then w else x) \<and> (if b then y else z) \<and> X) =
  ((if b then w \<and> y else x \<and> z) \<and> X)"
  by simp

lemma if_P_True1:
  "Q \<Longrightarrow> (if P then True else Q)"
  by simp

lemma if_P_True2:
  "Q \<Longrightarrow> (if P then Q else True)"
  by simp

lemma list_all2_induct [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q xs ys"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys. \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys\<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P xs ys"
  using lall
proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
  case 1 then show ?case by auto fact+
next
  case (2 x xs y ys)

  show ?case
  proof (rule consr)
    from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
    then show "P xs ys" by (intro "2.hyps")
  qed
qed

lemma list_all2_induct_suffixeq [consumes 1, case_names Nil Cons]:
  assumes lall: "list_all2 Q as bs"
  and     nilr: "P [] []"
  and    consr: "\<And>x xs y ys.
  \<lbrakk>list_all2 Q xs ys; Q x y; P xs ys; suffix (x # xs) as; suffix (y # ys) bs\<rbrakk>
  \<Longrightarrow> P (x # xs) (y # ys)"
  shows  "P as bs"
proof -
  define as' where "as' == as"
  define bs' where "bs' == bs"

  have "suffix as as' \<and> suffix bs bs'" unfolding as'_def bs'_def by simp
  then show ?thesis using lall
  proof (induct rule: list_induct2 [OF list_all2_lengthD [OF lall]])
    case 1 show ?case by fact
  next
    case (2 x xs y ys)

    show ?case
    proof (rule consr)
      from "2.prems" show "list_all2 Q xs ys" and "Q x y" by simp_all
      then show "P xs ys" using "2.hyps" "2.prems" by (auto dest: suffix_ConsD)
      from "2.prems" show "suffix (x # xs) as" and "suffix (y # ys) bs"
      by (auto simp: as'_def bs'_def)
    qed
  qed
qed

lemma upto_enum_step_shift:
  "\<lbrakk> is_aligned p n \<rbrakk> \<Longrightarrow>
  ([p , p + 2 ^ m .e. p + 2 ^ n - 1])
      = map ((+) p) [0, 2 ^ m .e. 2 ^ n - 1]"
  apply (erule is_aligned_get_word_bits)
   prefer 2
   apply (simp add: map_idI)
  apply (clarsimp simp: upto_enum_step_def)
  apply (frule is_aligned_no_overflow)
  apply (simp add: linorder_not_le [symmetric])
  done

lemma upto_enum_step_shift_red:
  "\<lbrakk> is_aligned p sz; sz < LENGTH('a); us \<le> sz \<rbrakk>
     \<Longrightarrow> [p :: 'a :: len word, p + 2 ^ us .e. p + 2 ^ sz - 1]
          = map (\<lambda>x. p + of_nat x * 2 ^ us) [0 ..< 2 ^ (sz - us)]"
  apply (subst upto_enum_step_shift, assumption)
  apply (simp add: upto_enum_step_red)
  done

lemma div_to_mult_word_lt:
  "\<lbrakk> (x :: 'a :: len word) \<le> y div z \<rbrakk> \<Longrightarrow> x * z \<le> y"
  apply (cases "z = 0")
   apply simp
  apply (simp add: word_neq_0_conv)
  apply (rule order_trans)
   apply (erule(1) word_mult_le_mono1)
   apply (simp add: unat_div)
   apply (rule order_le_less_trans [OF div_mult_le])
   apply simp
  apply (rule word_div_mult_le)
  done

lemma upto_enum_step_subset:
  "set [x, y .e. z] \<subseteq> {x .. z}"
  apply (clarsimp simp: upto_enum_step_def linorder_not_less)
  apply (drule div_to_mult_word_lt)
  apply (rule conjI)
   apply (erule word_random[rotated])
   apply simp
  apply (rule order_trans)
   apply (erule word_plus_mono_right)
   apply simp
  apply simp
  done

lemma shiftr_less_t2n':
  "\<lbrakk> x && mask (n + m) = x; m < LENGTH('a) \<rbrakk> \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  apply (simp add: word_size mask_eq_iff_w2p[symmetric])
  apply word_eqI
  apply (erule_tac x="na + n" in allE)
  apply fastforce
  done

lemma shiftr_less_t2n:
  "x < 2 ^ (n + m) \<Longrightarrow> x >> n < 2 ^ m" for x :: "'a :: len word"
  apply (rule shiftr_less_t2n')
   apply (erule less_mask_eq)
  apply (rule ccontr)
  apply (simp add: not_less)
  apply (subst (asm) p2_eq_0[symmetric])
  apply (simp add: power_add)
  done

lemma shiftr_eq_0:
  "n \<ge> LENGTH('a) \<Longrightarrow> ((w::'a::len word) >> n) = 0"
  apply (cut_tac shiftr_less_t2n'[of w n 0], simp)
   apply (simp add: mask_eq_iff)
  apply (simp add: lt2p_lem)
  apply simp
  done

lemma shiftr_not_mask_0:
  "n+m \<ge> LENGTH('a :: len) \<Longrightarrow> ((w::'a::len word) >> n) && ~~ (mask m) = 0"
  apply (simp add: and_not_mask shiftr_less_t2n shiftr_shiftr)
  apply (subgoal_tac "w >> n + m = 0", simp)
  apply (simp add: le_mask_iff[symmetric] mask_def le_def)
  apply (subst (asm) p2_gt_0[symmetric])
  apply (simp add: power_add not_less)
  done

lemma shiftl_less_t2n:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x < (2 ^ (m - n)); m < LENGTH('a) \<rbrakk> \<Longrightarrow> (x << n) < 2 ^ m"
  apply (simp add: word_size mask_eq_iff_w2p[symmetric])
  apply word_eqI
  apply (erule_tac x="na - n" in allE)
  apply auto
  done

lemma shiftl_less_t2n':
  "(x::'a::len word) < 2 ^ m \<Longrightarrow> m+n < LENGTH('a) \<Longrightarrow> x << n < 2 ^ (m + n)"
  by (rule shiftl_less_t2n) simp_all

lemma ucast_ucast_mask:
  "(ucast :: 'a :: len word \<Rightarrow> 'b :: len word) (ucast x) = x && mask (len_of TYPE ('a))"
  by word_eqI

lemma ucast_ucast_len:
  "\<lbrakk> x < 2 ^ LENGTH('b) \<rbrakk> \<Longrightarrow> ucast (ucast x::'b::len word) = (x::'a::len word)"
  apply (subst ucast_ucast_mask)
  apply (erule less_mask_eq)
  done

lemma ucast_ucast_id:
  "LENGTH('a) < LENGTH('b) \<Longrightarrow> ucast (ucast (x::'a::len word)::'b::len word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)

lemma unat_ucast:
  "unat (ucast x :: ('a :: len0) word) = unat x mod 2 ^ (LENGTH('a))"
  apply (simp add: unat_def ucast_def)
  apply (subst word_uint.eq_norm)
  apply (subst nat_mod_distrib)
    apply simp
   apply simp
  apply (subst nat_power_eq)
   apply simp
  apply simp
  done

lemma ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow>
   (ucast x < ((ucast (y :: 'a::len word)) :: 'b::len word)) = (x < y)"
  apply (simp add: word_less_nat_alt unat_ucast)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply simp
  done

\<comment> \<open>This weaker version was previously called @{text ucast_less_ucast}. We retain it to
    support existing proofs.\<close>
lemmas ucast_less_ucast_weak = ucast_less_ucast[OF order.strict_implies_order]

lemma sints_subset:
  "m \<le> n \<Longrightarrow> sints m \<subseteq> sints n"
  apply (simp add: sints_num)
  apply clarsimp
  apply (rule conjI)
   apply (erule order_trans[rotated])
   apply simp
  apply (erule order_less_le_trans)
  apply simp
  done

lemma up_scast_inj:
      "\<lbrakk> scast x = (scast y :: 'b :: len word); size x \<le> LENGTH('b) \<rbrakk>
         \<Longrightarrow> x = y"
  apply (simp add: scast_def)
  apply (subst(asm) word_sint.Abs_inject)
    apply (erule subsetD [OF sints_subset])
    apply (simp add: word_size)
   apply (erule subsetD [OF sints_subset])
   apply (simp add: word_size)
  apply simp
  done

lemma up_scast_inj_eq:
  "LENGTH('a) \<le> len_of TYPE ('b) \<Longrightarrow>
  (scast x = (scast y::'b::len word)) = (x = (y::'a::len word))"
  by (fastforce dest: up_scast_inj simp: word_size)

lemma nth_bounded:
  "\<lbrakk>(x :: 'a :: len word) !! n; x < 2 ^ m; m \<le> len_of TYPE ('a)\<rbrakk> \<Longrightarrow> n < m"
  apply (frule test_bit_size)
  apply (clarsimp simp: test_bit_bl word_size)
  apply (simp add: nth_rev)
  apply (subst(asm) is_aligned_add_conv[OF is_aligned_0',
                                        simplified add_0_left, rotated])
   apply assumption+
  apply (simp only: to_bl_0)
  apply (simp add: nth_append split: if_split_asm)
  done

lemma is_aligned_add_or:
  "\<lbrakk>is_aligned p n; d < 2 ^ n\<rbrakk> \<Longrightarrow> p + d = p || d"
  by (rule word_plus_and_or_coroll, word_eqI) blast

lemma two_power_increasing:
  "\<lbrakk> n \<le> m; m < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n \<le> 2 ^ m"
  by (simp add: word_le_nat_alt)

lemma is_aligned_add_less_t2n:
  "\<lbrakk>is_aligned (p::'a::len word) n; d < 2^n; n \<le> m; p < 2^m\<rbrakk> \<Longrightarrow> p + d < 2^m"
  apply (case_tac "m < LENGTH('a)")
   apply (subst mask_eq_iff_w2p[symmetric])
    apply (simp add: word_size)
   apply (simp add: is_aligned_add_or word_ao_dist less_mask_eq)
   apply (subst less_mask_eq)
    apply (erule order_less_le_trans)
    apply (erule(1) two_power_increasing)
   apply simp
  apply (simp add: power_overflow)
  done


lemma aligned_offset_non_zero:
  "\<lbrakk> is_aligned x n; y < 2 ^ n; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  apply (cases "y = 0")
   apply simp
  apply (subst word_neq_0_conv)
  apply (subst gt0_iff_gem1)
  apply (erule is_aligned_get_word_bits)
   apply (subst field_simps[symmetric], subst plus_le_left_cancel_nowrap)
     apply (rule is_aligned_no_wrap')
      apply simp
     apply (rule word_leq_le_minus_one)
      apply simp
     apply assumption
    apply (erule (1) is_aligned_no_wrap')
   apply (simp add: gt0_iff_gem1 [symmetric] word_neq_0_conv)
  apply simp
  done

lemmas mask_inner_mask = mask_eqs(1)

lemma mask_add_aligned:
  "is_aligned p n \<Longrightarrow> (p + q) && mask n = q && mask n"
  apply (simp add: is_aligned_mask)
  apply (subst mask_inner_mask [symmetric])
  apply simp
  done

lemma take_prefix:
  "(take (length xs) ys = xs) = prefix xs ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case Cons then show ?case by (cases ys) auto
qed

lemma cart_singleton_empty:
  "(S \<times> {e} = {}) = (S = {})"
  by blast

lemma word_div_1:
  "(n :: 'a :: len word) div 1 = n"
  by (simp add: word_div_def)

lemma word_minus_one_le:
  "-1 \<le> (x :: 'a :: len word) = (x = -1)"
  apply (insert word_n1_ge[where y=x])
  apply safe
  apply (erule(1) order_antisym)
  done

lemma mask_out_sub_mask:
  "(x && ~~ (mask n)) = x - (x && (mask n))"
  by (simp add: field_simps word_plus_and_or_coroll2)

lemma is_aligned_addD1:
  assumes al1: "is_aligned (x + y) n"
  and     al2: "is_aligned (x::'a::len word) n"
  shows "is_aligned y n"
  using al2
proof (rule is_aligned_get_word_bits)
  assume "x = 0" then show ?thesis using al1 by simp
next
  assume nv: "n < LENGTH('a)"
  from al1 obtain q1
    where xy: "x + y = 2 ^ n * of_nat q1" and "q1 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  moreover from al2 obtain q2
    where x: "x = 2 ^ n * of_nat q2" and "q2 < 2 ^ (LENGTH('a) - n)"
    by (rule is_alignedE)
  ultimately have "y = 2 ^ n * (of_nat q1 - of_nat q2)"
    by (simp add: field_simps)
  then show ?thesis using nv by (simp add: is_aligned_mult_triv1)
qed

lemmas is_aligned_addD2 =
       is_aligned_addD1[OF subst[OF add.commute,
                                 of "%x. is_aligned x n" for n]]

lemma is_aligned_add:
  "\<lbrakk>is_aligned p n; is_aligned q n\<rbrakk> \<Longrightarrow> is_aligned (p + q) n"
  by (simp add: is_aligned_mask mask_add_aligned)

lemma word_le_add:
  fixes x :: "'a :: len word"
  shows "x \<le> y \<Longrightarrow> \<exists>n. y = x + of_nat n"
  by (rule exI [where x = "unat (y - x)"]) simp

lemma word_plus_mcs_4':
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x + v \<le> x + w; x \<le> x + v\<rbrakk> \<Longrightarrow> v \<le> w"
  apply (rule word_plus_mcs_4)
   apply (simp add: add.commute)
  apply (simp add: add.commute)
  done

lemma shiftl_mask_is_0[simp]:
  "(x << n) && mask n = 0"
  apply (rule iffD1 [OF is_aligned_mask])
  apply (rule is_aligned_shiftl_self)
  done

definition
  sum_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a + 'c \<Rightarrow> 'b + 'd" where
 "sum_map f g x \<equiv> case x of Inl v \<Rightarrow> Inl (f v) | Inr v' \<Rightarrow> Inr (g v')"

lemma sum_map_simps[simp]:
  "sum_map f g (Inl v) = Inl (f v)"
  "sum_map f g (Inr w) = Inr (g w)"
  by (simp add: sum_map_def)+

lemma if_and_helper:
  "(If x v v') && v'' = If x (v && v'') (v' && v'')"
  by (rule if_distrib)

lemma unat_Suc2:
  fixes n :: "'a :: len word"
  shows
  "n \<noteq> -1 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  apply (subst add.commute, rule unatSuc)
  apply (subst eq_diff_eq[symmetric], simp add: minus_equation_iff)
  done

lemmas word_unat_Rep_inject1 = word_unat.Rep_inject[where y=1]
lemmas unat_eq_1 = unat_eq_0 word_unat_Rep_inject1[simplified]


lemma rshift_sub_mask_eq:
  "(a >> (size a - b)) && mask b = a >> (size a - b)"
  using shiftl_shiftr2[where a=a and b=0 and c="size a - b"]
  apply (cases "b < size a")
   apply simp
  apply (simp add: linorder_not_less mask_def word_size
                   p2_eq_0[THEN iffD2])
  done

lemma shiftl_shiftr3:
  "b \<le> c \<Longrightarrow> a << b >> c = (a >> c - b) && mask (size a - c)"
  apply (cases "b = c")
   apply (simp add: shiftl_shiftr1)
  apply (simp add: shiftl_shiftr2)
  done

lemma and_mask_shiftr_comm:
  "m\<le>size w \<Longrightarrow> (w && mask m) >> n = (w >> n) && mask (m-n)"
  by (simp add: and_mask shiftr_shiftr) (simp add: word_size shiftl_shiftr3)

lemma and_mask_shiftl_comm:
  "m+n \<le> size w \<Longrightarrow> (w && mask m) << n = (w << n) && mask (m+n)"
  by (simp add: and_mask word_size shiftl_shiftl) (simp add: shiftl_shiftr1)

lemma le_mask_shiftl_le_mask: "s = m + n \<Longrightarrow> x \<le> mask n \<Longrightarrow> x << m \<le> mask s"
  by (simp add: le_mask_iff shiftl_shiftr3)

lemma and_not_mask_twice:
  "(w && ~~ (mask n)) && ~~ (mask m) = w && ~~ (mask (max m n))"
  apply (simp add: and_not_mask)
  apply (case_tac "n<m";
         simp add: shiftl_shiftr2 shiftl_shiftr1 not_less max_def shiftr_shiftr shiftl_shiftl)
   apply (cut_tac and_mask_shiftr_comm [where w=w and m="size w" and n=m, simplified,symmetric])
   apply (simp add: word_size mask_def)
  apply (cut_tac and_mask_shiftr_comm [where w=w and m="size w" and n=n, simplified,symmetric])
  apply (simp add: word_size mask_def)
  done

lemma word_less_cases:
  "x < y \<Longrightarrow> x = y - 1 \<or> x < y - (1 ::'a::len word)"
  apply (drule word_less_sub_1)
  apply (drule order_le_imp_less_or_eq)
  apply auto
  done

lemma eq_eqI:
  "a = b \<Longrightarrow> (a = x) = (b = x)"
  by simp

lemma mask_and_mask:
  "mask a && mask b = mask (min a b)"
  by word_eqI

lemma mask_eq_0_eq_x:
  "(x && w = 0) = (x && ~~ w = x)"
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

lemma mask_eq_x_eq_0:
  "(x && w = x) = (x && ~~ w = 0)"
  using word_plus_and_or_coroll2[where x=x and w=w]
  by auto

definition
  "limited_and (x :: 'a :: len word) y = (x && y = x)"

lemma limited_and_eq_0:
  "\<lbrakk> limited_and x z; y && ~~ z = y \<rbrakk> \<Longrightarrow> x && y = 0"
  unfolding limited_and_def
  apply (subst arg_cong2[where f="(&&)"])
    apply (erule sym)+
  apply (simp(no_asm) add: word_bw_assocs word_bw_comms word_bw_lcs)
  done

lemma limited_and_eq_id:
  "\<lbrakk> limited_and x z; y && z = z \<rbrakk> \<Longrightarrow> x && y = x"
  unfolding limited_and_def
  by (erule subst, fastforce simp: word_bw_lcs word_bw_assocs word_bw_comms)

lemma lshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x << n) (z << n)"
  unfolding limited_and_def
  by (simp add: shiftl_over_and_dist[symmetric])

lemma rshift_limited_and:
  "limited_and x z \<Longrightarrow> limited_and (x >> n) (z >> n)"
  unfolding limited_and_def
  by (simp add: shiftr_over_and_dist[symmetric])

lemmas limited_and_simps1 = limited_and_eq_0 limited_and_eq_id

lemmas is_aligned_limited_and
    = is_aligned_neg_mask_eq[unfolded mask_def, folded limited_and_def]

lemma compl_of_1: "~~ 1 = (-2 :: 'a :: len word)"
  by simp

lemmas limited_and_simps = limited_and_simps1
       limited_and_simps1[OF is_aligned_limited_and]
       limited_and_simps1[OF lshift_limited_and]
       limited_and_simps1[OF rshift_limited_and]
       limited_and_simps1[OF rshift_limited_and, OF is_aligned_limited_and]
       compl_of_1 shiftl_shiftr1[unfolded word_size mask_def]
       shiftl_shiftr2[unfolded word_size mask_def]

lemma split_word_eq_on_mask:
  "(x = y) = (x && m = y && m \<and> x && ~~ m = y && ~~ m)"
  by safe word_eqI_solve

lemma map2_Cons_2_3:
  "(map2 f xs (y # ys) = (z # zs)) = (\<exists>x xs'. xs = x # xs' \<and> f x y = z \<and> map2 f xs' ys = zs)"
  by (case_tac xs, simp_all)

lemma map2_xor_replicate_False:
  "map2 (\<lambda>x y. x \<longleftrightarrow> \<not> y) xs (replicate n False) = take n xs"
  apply (induct xs arbitrary: n, simp)
  apply (case_tac n; simp)
  done

lemma word_and_1_shiftl:
  "x && (1 << n) = (if x !! n then (1 << n) else 0)" for x :: "'a :: len word"
  by word_eqI_solve

lemmas word_and_1_shiftls'
    = word_and_1_shiftl[where n=0]
      word_and_1_shiftl[where n=1]
      word_and_1_shiftl[where n=2]

lemmas word_and_1_shiftls = word_and_1_shiftls' [simplified]

lemma word_and_mask_shiftl:
  "x && (mask n << m) = ((x >> m) && mask n) << m"
  by word_eqI_solve

lemma plus_Collect_helper:
  "(+) x ` {xa. P (xa :: 'a :: len word)} = {xa. P (xa - x)}"
  by (fastforce simp add: image_def)

lemma plus_Collect_helper2:
  "(+) (- x) ` {xa. P (xa :: 'a :: len word)} = {xa. P (x + xa)}"
  using plus_Collect_helper [of "- x" P] by (simp add: ac_simps)

lemma word_FF_is_mask:
  "0xFF = mask 8"
  by (simp add: mask_def)

lemma word_1FF_is_mask:
  "0x1FF = mask 9"
  by (simp add: mask_def)

lemma ucast_of_nat_small:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> ucast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply (rule sym, subst word_unat.inverse_norm)
  apply (simp add: ucast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: unat_of_nat)
  done

lemma word_le_make_less:
  fixes x :: "'a :: len word"
  shows "y \<noteq> -1 \<Longrightarrow> (x \<le> y) = (x < (y + 1))"
  apply safe
  apply (erule plus_one_helper2)
  apply (simp add: eq_diff_eq[symmetric])
  done

lemmas finite_word = finite [where 'a="'a::len word"]

lemma word_to_1_set:
  "{0 ..< (1 :: 'a :: len word)} = {0}"
  by fastforce

lemma range_subset_eq2:
  "{a :: 'a :: len word .. b} \<noteq> {} \<Longrightarrow> ({a .. b} \<subseteq> {c .. d}) = (c \<le> a \<and> b \<le> d)"
  by simp

lemma word_leq_minus_one_le:
  fixes x :: "'a::len word"
  shows "\<lbrakk>y \<noteq> 0; x \<le> y - 1 \<rbrakk> \<Longrightarrow> x < y"
  using le_m1_iff_lt word_neq_0_conv by blast

lemma word_count_from_top:
  "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: 'a :: len word} = {0 ..< n - 1} \<union> {n - 1}"
  apply (rule set_eqI, rule iffI)
   apply simp
   apply (drule word_le_minus_one_leq)
   apply (rule disjCI)
   apply simp
  apply simp
  apply (erule word_leq_minus_one_le)
  apply fastforce
  done

lemma word_minus_one_le_leq:
  "\<lbrakk> x - 1 < y \<rbrakk> \<Longrightarrow> x \<le> (y :: 'a :: len word)"
  apply (cases "x = 0")
   apply simp
  apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply (subst(asm) unat_minus_one)
   apply (simp add: word_less_nat_alt)
  apply (cases "unat x")
   apply (simp add: unat_eq_zero)
  apply arith
  done

lemma mod_mod_power:
  fixes k :: nat
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
proof (cases "m \<le> n")
  case True

  then have "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ m"
    apply -
    apply (subst mod_less [where n = "2 ^ n"])
    apply (rule order_less_le_trans [OF mod_less_divisor])
    apply simp+
    done
  also have "\<dots> = k mod  2 ^ (min m n)" using True by simp
  finally show ?thesis .
next
  case False
  then have "n < m" by simp
  then obtain d where md: "m = n + d"
    by (auto dest: less_imp_add_positive)
  then have "k mod 2 ^ m = 2 ^ n * (k div 2 ^ n mod 2 ^ d) + k mod 2 ^ n"
    by (simp add: mod_mult2_eq power_add)
  then have "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ n"
    by (simp add: mod_add_left_eq)
  then show ?thesis using False
    by simp
qed

lemma word_div_less:
  "m < n \<Longrightarrow> m div n = 0" for m :: "'a :: len word"
  by (simp add: unat_mono word_arith_nat_defs(6))

lemma word_must_wrap:
  "\<lbrakk> x \<le> n - 1; n \<le> x \<rbrakk> \<Longrightarrow> n = (0 :: 'a :: len word)"
  using dual_order.trans sub_wrap word_less_1 by blast

lemma range_subset_card:
  "\<lbrakk> {a :: 'a :: len word .. b} \<subseteq> {c .. d}; b \<ge> a \<rbrakk> \<Longrightarrow> d \<ge> c \<and> d - c \<ge> b - a"
  using word_sub_le word_sub_mono by fastforce

lemma less_1_simp:
  "n - 1 < m = (n \<le> (m :: 'a :: len word) \<and> n \<noteq> 0)"
  by unat_arith

lemma alignUp_div_helper:
  fixes a :: "'a::len word"
  assumes kv: "k < 2 ^ (LENGTH('a) - n)"
  and     xk: "x = 2 ^ n * of_nat k"
  and    le: "a \<le> x"
  and    sz: "n < LENGTH('a)"
  and   anz: "a mod 2 ^ n \<noteq> 0"
  shows "a div 2 ^ n < of_nat k"
proof -
  have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using xk kv sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst unat_power_lower, simp)
    apply (subst mult.commute)
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have "unat a div 2 ^ n * 2 ^ n \<noteq> unat a"
  proof -
    have "unat a = unat a div 2 ^ n * 2 ^ n + unat a mod 2 ^ n"
      by (simp add: div_mult_mod_eq)
    also have "\<dots> \<noteq> unat a div 2 ^ n * 2 ^ n" using sz anz
      by (simp add: unat_arith_simps)
    finally show ?thesis ..
  qed

  then have "a div 2 ^ n * 2 ^ n < a" using sz anz
    apply (subst word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (subst unat_div)
    apply simp
    apply (rule order_le_less_trans [OF mod_less_eq_dividend])
    apply (erule order_le_neq_trans [OF div_mult_le])
    done

  also from xk le have "\<dots> \<le> of_nat k * 2 ^ n" by (simp add: field_simps)
  finally show ?thesis using sz kv
    apply -
    apply (erule word_mult_less_dest [OF _ _ kn])
    apply (simp add: unat_div)
    apply (rule order_le_less_trans [OF div_mult_le])
    apply (rule unat_lt2p)
    done
qed

lemma nat_mod_power_lem:
  fixes a :: nat
  shows "1 < a \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  apply (clarsimp)
  apply (clarsimp simp add: le_iff_add power_add)
  done

lemma power_mod_div:
  fixes x :: "nat"
  shows "x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)" (is "?LHS = ?RHS")
proof (cases "n \<le> m")
  case True
  then have "?LHS = 0"
    apply -
    apply (rule div_less)
    apply (rule order_less_le_trans [OF mod_less_divisor]; simp)
    done
  also have "\<dots> = ?RHS" using True
    by simp
  finally show ?thesis .
next
  case False
  then have lt: "m < n" by simp
  then obtain q where nv: "n = m + q" and "0 < q"
    by (auto dest: less_imp_Suc_add)

  then have "x mod 2 ^ n = 2 ^ m * (x div 2 ^ m mod 2 ^ q) + x mod 2 ^ m"
    by (simp add: power_add mod_mult2_eq)

  then have "?LHS = x div 2 ^ m mod 2 ^ q"
    by (simp add: div_add1_eq)

  also have "\<dots> = ?RHS" using nv
    by simp

  finally show ?thesis .
qed

lemma word_power_mod_div:
  fixes x :: "'a::len word"
  shows "\<lbrakk> n < LENGTH('a); m < LENGTH('a)\<rbrakk>
  \<Longrightarrow> x mod 2 ^ n div 2 ^ m = x div 2 ^ m mod 2 ^ (n - m)"
  apply (simp add: word_arith_nat_div unat_mod power_mod_div)
  apply (subst unat_arith_simps(3))
  apply (subst unat_mod)
  apply (subst unat_of_nat)+
  apply (simp add: mod_mod_power min.commute)
  done

lemma word_range_minus_1':
  fixes a :: "'a :: len word"
  shows "a \<noteq> 0 \<Longrightarrow> {a - 1<..b} = {a..b}"
  by (simp add: greaterThanAtMost_def atLeastAtMost_def greaterThan_def atLeast_def less_1_simp)

lemma word_range_minus_1:
  fixes a :: "'a :: len word"
  shows "b \<noteq> 0 \<Longrightarrow> {a..b - 1} = {a..<b}"
  apply (simp add: atLeastLessThan_def atLeastAtMost_def atMost_def lessThan_def)
  apply (rule arg_cong [where f = "\<lambda>x. {a..} \<inter> x"])
  apply rule
   apply clarsimp
   apply (erule contrapos_pp)
   apply (simp add: linorder_not_less linorder_not_le word_must_wrap)
  apply (clarsimp)
  apply (drule word_le_minus_one_leq)
  apply (auto simp: word_less_sub_1)
  done

lemma ucast_nat_def:
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> 'b :: len word) x"
  by (simp add: ucast_def word_of_int_nat unat_def)

lemmas if_fun_split = if_apply_def2

lemma i_hate_words_helper:
  "i \<le> (j - k :: nat) \<Longrightarrow> i \<le> j"
  by simp

lemma i_hate_words:
  "unat (a :: 'a word) \<le> unat (b :: 'a :: len word) - Suc 0
    \<Longrightarrow> a \<noteq> -1"
  apply (frule i_hate_words_helper)
  apply (subst(asm) word_le_nat_alt[symmetric])
  apply (clarsimp simp only: word_minus_one_le)
  apply (simp only: linorder_not_less[symmetric])
  apply (erule notE)
  apply (rule diff_Suc_less)
  apply (subst neq0_conv[symmetric])
  apply (subst unat_eq_0)
  apply (rule notI, drule arg_cong[where f="(+) 1"])
  apply simp
  done

lemma overflow_plus_one_self:
  "(1 + p \<le> p) = (p = (-1 :: 'a :: len word))"
  apply (safe, simp_all)
  apply (rule ccontr)
  apply (drule plus_one_helper2)
   apply (rule notI)
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply (simp add: field_simps)
  done

lemma plus_1_less:
  "(x + 1 \<le> (x :: 'a :: len word)) = (x = -1)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (cut_tac plus_one_helper2[where x=x, OF order_refl])
    apply simp
   apply clarsimp
   apply (drule arg_cong[where f="\<lambda>x. x - 1"])
   apply simp
  apply simp
  done

lemma pos_mult_pos_ge:
  "[|x > (0::int); n>=0 |] ==> n * x >= n*1"
  apply (simp only: mult_left_mono)
  done

lemma If_eq_obvious:
  "x \<noteq> z \<Longrightarrow> ((if P then x else y) = z) = (\<not> P \<and> y = z)"
  by simp

lemma Some_to_the:
  "v = Some x \<Longrightarrow> x = the v"
  by simp

lemma dom_if_Some:
  "dom (\<lambda>x. if P x then Some (f x) else g x) = {x. P x} \<union> dom g"
  by fastforce

lemma dom_insert_absorb:
  "x \<in> dom f \<Longrightarrow> insert x (dom f) = dom f" by auto

lemma emptyE2:
  "\<lbrakk> S = {}; x \<in> S \<rbrakk> \<Longrightarrow> P"
  by simp

lemma mod_div_equality_div_eq:
  "a div b * b = (a - (a mod b) :: int)"
  by (simp add: field_simps)

lemma zmod_helper:
  "n mod m = k \<Longrightarrow> ((n :: int) + a) mod m = (k + a) mod m"
  by (metis add.commute mod_add_right_eq)

lemma int_div_sub_1:
  "\<lbrakk> m \<ge> 1 \<rbrakk> \<Longrightarrow> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)"
  apply (subgoal_tac "m = 0 \<or> (n - (1 :: int)) div m = (if m dvd n then (n div m) - 1 else n div m)")
   apply fastforce
  apply (subst mult_cancel_right[symmetric])
  apply (simp only: left_diff_distrib split: if_split)
  apply (simp only: mod_div_equality_div_eq)
  apply (clarsimp simp: field_simps)
  apply (clarsimp simp: dvd_eq_mod_eq_0)
  apply (cases "m = 1")
   apply simp
  apply (subst mod_diff_eq[symmetric], simp add: zmod_minus1)
  apply clarsimp
  apply (subst diff_add_cancel[where b=1, symmetric])
  apply (subst mod_add_eq[symmetric])
  apply (simp add: field_simps)
  apply (rule mod_pos_pos_trivial)
   apply (subst add_0_right[where a=0, symmetric])
   apply (rule add_mono)
    apply simp
   apply simp
  apply (cases "(n - 1) mod m = m - 1")
   apply (drule zmod_helper[where a=1])
   apply simp
  apply (subgoal_tac "1 + (n - 1) mod m \<le> m")
   apply simp
  apply (subst field_simps, rule zless_imp_add1_zle)
  apply simp
  done

lemma ptr_add_image_multI:
  "\<lbrakk> \<And>x y. (x * val = y * val') = (x * val'' = y); x * val'' \<in> S \<rbrakk> \<Longrightarrow>
     ptr_add ptr (x * val) \<in> (\<lambda>p. ptr_add ptr (p * val')) ` S"
  apply (simp add: image_def)
  apply (erule rev_bexI)
  apply (rule arg_cong[where f="ptr_add ptr"])
  apply simp
  done

lemma shift_times_fold:
  "(x :: 'a :: len word) * (2 ^ n) << m = x << (m + n)"
  by (simp add: shiftl_t2n ac_simps power_add)

lemma word_plus_strict_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>y < z; x \<le> x + z\<rbrakk> \<Longrightarrow> x + y < x + z"
  by unat_arith

lemma replicate_minus:
  "k < n \<Longrightarrow> replicate n False = replicate (n - k) False @ replicate k False"
  by (subst replicate_add [symmetric]) simp

lemmas map_prod_split_imageI'
  = map_prod_imageI[where f="case_prod f" and g="case_prod g"
                    and a="(a, b)" and b="(c, d)" for a b c d f g]
lemmas map_prod_split_imageI = map_prod_split_imageI'[simplified]

lemma word_div_mult:
  "0 < c \<Longrightarrow> a < b * c \<Longrightarrow> a div c < b" for a b c :: "'a::len word"
  by (rule classical)
     (use div_to_mult_word_lt [of b a c] in
      \<open>auto simp add: word_less_nat_alt word_le_nat_alt unat_div\<close>)

lemma word_less_power_trans_ofnat:
  "\<lbrakk>n < 2 ^ (m - k); k \<le> m; m < LENGTH('a)\<rbrakk>
   \<Longrightarrow> of_nat n * 2 ^ k < (2::'a::len word) ^ m"
  apply (subst mult.commute)
  apply (rule word_less_power_trans)
    apply (simp add: word_less_nat_alt)
    apply (subst unat_of_nat_eq)
     apply (erule order_less_trans)
     apply simp+
    done

lemma word_1_le_power:
  "n < LENGTH('a) \<Longrightarrow> (1 :: 'a :: len word) \<le> 2 ^ n"
  by (rule inc_le[where i=0, simplified], erule iffD2[OF p2_gt_0])

lemma enum_word_div:
  fixes v :: "'a :: len word" shows
  "\<exists>xs ys. enum = xs @ [v] @ ys
             \<and> (\<forall>x \<in> set xs. x < v)
             \<and> (\<forall>y \<in> set ys. v < y)"
  apply (simp only: enum_word_def)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule order_less_imp_le, simp)
  apply (simp add: upt_conv_Cons)
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a='a])
    apply simp
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (drule of_nat_mono_maybe[rotated, where 'a='a])
   apply simp
  apply simp
  done

lemma of_bool_nth:
  "of_bool (x !! v) = (x >> v) && 1"
  by (word_eqI cong: rev_conj_cong)

lemma unat_1_0:
  "1 \<le> (x::'a::len word) = (0 < unat x)"
  by (auto simp add: word_le_nat_alt)

lemma x_less_2_0_1':
  fixes x :: "'a::len word"
  shows "\<lbrakk>LENGTH('a) \<noteq> 1; x < 2\<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  apply (induct x)
   apply clarsimp+
  by (metis Suc_eq_plus1 add_lessD1 less_irrefl one_add_one unatSuc word_less_nat_alt)

lemmas word_add_le_iff2 = word_add_le_iff [folded no_olen_add_nat]

lemma of_nat_power:
  shows "\<lbrakk> p < 2 ^ x; x < len_of TYPE ('a) \<rbrakk> \<Longrightarrow> of_nat p < (2 :: 'a :: len word) ^ x"
  apply (rule order_less_le_trans)
   apply (rule of_nat_mono_maybe)
    apply (erule power_strict_increasing)
    apply simp
   apply assumption
  apply (simp add: word_unat_power)
  done

lemma of_nat_n_less_equal_power_2:
  "n < LENGTH('a::len) \<Longrightarrow> ((of_nat n)::'a word) < 2 ^ n"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (metis of_nat_power n_less_equal_power_2 of_nat_Suc power_Suc)
  done

lemma eq_mask_less:
  fixes w :: "'a::len word"
  assumes eqm: "w = w && mask n"
  and      sz: "n < len_of TYPE ('a)"
  shows "w < (2::'a word) ^ n"
  by (subst eqm, rule and_mask_less' [OF sz])

lemma of_nat_mono_maybe':
  fixes Y :: "nat"
  assumes xlt: "x < 2 ^ len_of TYPE ('a)"
  assumes ylt: "y < 2 ^ len_of TYPE ('a)"
  shows   "(y < x) = (of_nat y < (of_nat x :: 'a :: len word))"
  apply (subst word_less_nat_alt)
  apply (subst unat_of_nat)+
  apply (subst mod_less)
   apply (rule ylt)
  apply (subst mod_less)
   apply (rule xlt)
  apply simp
  done

lemma shiftr_mask_eq:
  "(x >> n) && mask (size x - n) = x >> n" for x :: "'a :: len word"
  by word_eqI_solve

lemma shiftr_mask_eq':
  "m = (size x - n) \<Longrightarrow> (x >> n) && mask m = x >> n" for x :: "'a :: len word"
  by (simp add: shiftr_mask_eq)

lemma dom_if:
  "dom (\<lambda>a. if a \<in> addrs then Some (f a) else g a)  = addrs \<union> dom g"
  by (auto simp: dom_def split: if_split)

lemma less_is_non_zero_p1:
  fixes a :: "'a :: len word"
  shows "a < k \<Longrightarrow> a + 1 \<noteq> 0"
  apply (erule contrapos_pn)
  apply (drule max_word_wrap)
  apply (simp add: not_less)
  done

lemma of_nat_mono_maybe_le:
  "\<lbrakk>x < 2 ^ LENGTH('a); y < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow>
  (y \<le> x) = ((of_nat y :: 'a :: len word) \<le> of_nat x)"
  apply (clarsimp simp: le_less)
  apply (rule disj_cong)
   apply (rule of_nat_mono_maybe', assumption+)
  apply (simp add: word_unat.norm_eq_iff [symmetric])
  done

lemma mask_AND_NOT_mask:
  "(w && ~~ (mask n)) && mask n = 0"
  by word_eqI

lemma AND_NOT_mask_plus_AND_mask_eq:
  "(w && ~~ (mask n)) + (w && mask n) = w"
  by (subst word_plus_and_or_coroll; word_eqI_solve)

lemma plus_mask_AND_NOT_mask_eq:
  "x && ~~mask n = x \<Longrightarrow> (x + mask n) && ~~mask n = x"
  by (subst word_plus_and_or_coroll; word_eqI_solve)

lemma mask_eqI:
  fixes x :: "'a :: len word"
  assumes m1: "x && mask n = y && mask n"
  and     m2: "x && ~~ (mask n) = y && ~~ (mask n)"
  shows "x = y"
proof (subst bang_eq, rule allI)
  fix m

  show "x !! m = y !! m"
  proof (cases "m < n")
    case True
    then have "x !! m = ((x && mask n) !! m)"
      by (simp add: word_size test_bit_conj_lt)
    also have "\<dots> = ((y && mask n) !! m)" using m1 by simp
    also have "\<dots> = y !! m" using True
      by (simp add: word_size test_bit_conj_lt)
    finally show ?thesis .
  next
    case False
    then have "x !! m = ((x && ~~ (mask n)) !! m)"
      by (simp add: neg_mask_test_bit test_bit_conj_lt)
    also have "\<dots> = ((y && ~~ (mask n)) !! m)" using m2 by simp
    also have "\<dots> = y !! m" using False
      by (simp add: neg_mask_test_bit test_bit_conj_lt)
    finally show ?thesis .
  qed
qed

lemma nat_less_power_trans2:
  fixes n :: nat
  shows "\<lbrakk>n < 2 ^ (m - k); k \<le> m\<rbrakk> \<Longrightarrow> n * 2 ^ k  < 2 ^ m"
  by (subst mult.commute, erule (1) nat_less_power_trans)

lemma nat_move_sub_le: "(a::nat) + b \<le> c \<Longrightarrow> a \<le> c - b" by arith

lemma neq_0_no_wrap:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<le> x + y; x \<noteq> 0 \<rbrakk> \<Longrightarrow> x + y \<noteq> 0"
  by clarsimp

lemma plus_minus_one_rewrite:
  "v + (- 1 :: ('a :: {ring, one, uminus})) \<equiv> v - 1"
  by (simp add: field_simps)

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  apply (induct a arbitrary: b)
   apply simp
  apply (erule le_SucE)
   apply (clarsimp simp:Suc_diff_le le_iff_add power_add)
  apply simp
  done

lemma two_pow_div_gt_le:
  "v < 2 ^ n div (2 ^ m :: nat) \<Longrightarrow> m \<le> n"
  by (clarsimp dest!: less_two_pow_divD)

lemma unatSuc2:
  fixes n :: "'a :: len word"
  shows "n + 1 \<noteq> 0 \<Longrightarrow> unat (n + 1) = Suc (unat n)"
  by (simp add: add.commute unatSuc)

lemma word_of_nat_less:
  "\<lbrakk> n < unat x \<rbrakk> \<Longrightarrow> of_nat n < x"
  apply (simp add: word_less_nat_alt)
  apply (erule order_le_less_trans[rotated])
  apply (simp add: unat_of_nat)
  done

lemma word_of_nat_le:
  "n \<le> unat x \<Longrightarrow> of_nat n \<le> x"
  apply (simp add: word_le_nat_alt unat_of_nat)
  apply (erule order_trans[rotated])
  apply simp
  done

lemma word_unat_less_le:
   "a \<le> of_nat b \<Longrightarrow> unat a \<le> b"
   by (metis eq_iff le_cases le_unat_uoi word_of_nat_le)

lemma and_eq_0_is_nth:
  fixes x :: "'a :: len word"
  shows "y = 1 << n \<Longrightarrow> ((x && y) = 0) = (\<not> (x !! n))"
  apply safe
   apply (drule_tac u="(x && (1 << n))" and x=n in word_eqD)
   apply (simp add: nth_w2p)
   apply (simp add: test_bit_bin)
  apply word_eqI
  done

lemmas arg_cong_Not = arg_cong [where f=Not]
lemmas and_neq_0_is_nth = arg_cong_Not [OF and_eq_0_is_nth, simplified]

lemma nth_is_and_neq_0:
  "(x::'a::len word) !! n = (x && 2 ^ n \<noteq> 0)"
  by (subst and_neq_0_is_nth; rule refl)

lemma mask_Suc_0 : "mask (Suc 0) = 1"
  by (simp add: mask_def)

lemma ucast_ucast_add:
  fixes x :: "'a :: len word"
  fixes y :: "'b :: len word"
  shows
  "LENGTH('b) \<ge> LENGTH('a) \<Longrightarrow>
    ucast (ucast x + y) = x + ucast y"
  apply (rule word_unat.Rep_eqD)
  apply (simp add: unat_ucast unat_word_ariths mod_mod_power
                   min.absorb2 unat_of_nat)
  apply (subst mod_add_left_eq[symmetric])
  apply (simp add: mod_mod_power min.absorb2)
  apply (subst mod_add_right_eq)
  apply simp
  done

lemma word_shift_zero:
  "\<lbrakk> x << n = 0; x \<le> 2^m; m + n < LENGTH('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) = 0"
  apply (rule ccontr)
  apply (drule (2) word_shift_nonzero)
  apply simp
  done

lemma bool_mask':
  fixes x :: "'a :: len word"
  shows "2 < LENGTH('a) \<Longrightarrow> (0 < x && 1) = (x && 1 = 1)"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (subgoal_tac "x && mask 1 < 2^1")
   prefer 2
   apply (rule and_mask_less_size)
   apply (simp add: word_size)
  apply (simp add: mask_def)
  apply (drule word_less_cases [where y=2])
  apply (erule disjE, simp)
  apply simp
  done

lemma sint_eq_uint:
  "\<not> msb x \<Longrightarrow> sint x = uint x"
  apply (rule word_uint.Abs_eqD, subst word_sint.Rep_inverse)
    apply simp_all
  apply (cut_tac x=x in word_sint.Rep)
  apply (clarsimp simp add: uints_num sints_num)
  apply (rule conjI)
   apply (rule ccontr)
   apply (simp add: linorder_not_le word_msb_sint[symmetric])
  apply (erule order_less_le_trans)
  apply simp
  done

lemma scast_eq_ucast:
  "\<not> msb x \<Longrightarrow> scast x = ucast x"
  by (simp add: scast_def ucast_def sint_eq_uint)

lemma lt1_neq0:
  fixes x :: "'a :: len word"
  shows "(1 \<le> x) = (x \<noteq> 0)" by unat_arith

lemma word_plus_one_nonzero:
  fixes x :: "'a :: len word"
  shows "\<lbrakk>x \<le> x + y; y \<noteq> 0\<rbrakk> \<Longrightarrow> x + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (erule word_random)
  apply (simp add: lt1_neq0)
  done

lemma word_sub_plus_one_nonzero:
  fixes n :: "'a :: len word"
  shows "\<lbrakk>n' \<le> n; n' \<noteq> 0\<rbrakk> \<Longrightarrow> (n - n') + 1 \<noteq> 0"
  apply (subst lt1_neq0 [symmetric])
  apply (subst olen_add_eqv [symmetric])
  apply (rule word_random [where x' = n'])
   apply simp
   apply (erule word_sub_le)
  apply (simp add: lt1_neq0)
  done

lemma word_le_minus_mono_right:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> z \<le> y; y \<le> x; z \<le> x \<rbrakk> \<Longrightarrow> x - y \<le> x - z"
  apply (rule word_sub_mono)
     apply simp
    apply assumption
   apply (erule word_sub_le)
  apply (erule word_sub_le)
  done

lemma drop_append_miracle:
  "n = length xs \<Longrightarrow> drop n (xs @ ys) = ys"
  by simp

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk> \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma nat_less_mult_monoish: "\<lbrakk> a < b; c < (d :: nat) \<rbrakk> \<Longrightarrow> (a + 1) * (c + 1) <= b * d"
  apply (drule Suc_leI)+
  apply (drule(1) mult_le_mono)
  apply simp
  done

lemma word_0_sle_from_less[unfolded word_size]:
  "\<lbrakk> x < 2 ^ (size x - 1) \<rbrakk>  \<Longrightarrow> 0 <=s x"
  apply (clarsimp simp: word_sle_msb_le)
  apply (simp add: word_msb_nth)
  apply (subst (asm) word_test_bit_def [symmetric])
  apply (drule less_mask_eq)
  apply (drule_tac x="size x - 1" in word_eqD)
  apply (simp add: word_size)
  done

lemma not_msb_from_less:
  "(v :: 'a word) < 2 ^ (LENGTH('a :: len) - 1) \<Longrightarrow> \<not> msb v"
  apply (clarsimp simp add: msb_nth)
  apply (drule less_mask_eq)
  apply (drule word_eqD, drule(1) iffD2)
  apply simp
  done

lemma distinct_lemma: "f x \<noteq> f y \<Longrightarrow> x \<noteq> y" by auto


lemma ucast_sub_ucast:
  fixes x :: "'a::len word"
  assumes "y \<le> x"
  assumes T: "LENGTH('a) \<le> LENGTH('b)"
  shows "ucast (x - y) = (ucast x - ucast y :: 'b::len word)"
proof -
  from T
  have P: "unat x < 2 ^ LENGTH('b)" "unat y < 2 ^ LENGTH('b)"
    by (fastforce intro!: less_le_trans[OF unat_lt2p])+
  then show ?thesis
    by (simp add: unat_arith_simps unat_ucast assms[simplified unat_arith_simps])
qed

lemma word_1_0:
  "\<lbrakk>a + (1::('a::len) word) \<le> b; a < of_nat x\<rbrakk> \<Longrightarrow> a < b"
  by unat_arith

lemma unat_of_nat_less:"\<lbrakk> a < b; unat b = c \<rbrakk> \<Longrightarrow> a < of_nat c"
  by fastforce

lemma word_le_plus_1: "\<lbrakk> (y::('a::len) word) < y + n; a < n \<rbrakk> \<Longrightarrow> y + a \<le> y + a + 1"
  by unat_arith

lemma word_le_plus:"\<lbrakk>(a::('a::len) word) < a + b; c < b\<rbrakk> \<Longrightarrow> a \<le> a + c"
by (metis order_less_imp_le word_random)

(*
 * Basic signed arithemetic properties.
 *)

lemma sint_minus1 [simp]: "(sint x = -1) = (x = -1)"
  by (metis sint_n1 word_sint.Rep_inverse')

lemma sint_0 [simp]: "(sint x = 0) = (x = 0)"
  by (metis sint_0 word_sint.Rep_inverse')

(* It is not always that case that "sint 1 = 1", because of 1-bit word sizes.
 * This lemma produces the different cases. *)
lemma sint_1_cases:
  "\<lbrakk> \<lbrakk> len_of TYPE ('a::len) = 1; (a::'a word) = 0; sint a = 0 \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> len_of TYPE ('a) = 1; a = 1; sint (1 :: 'a word) = -1 \<rbrakk> \<Longrightarrow> P;
      \<lbrakk> len_of TYPE ('a) > 1; sint (1 :: 'a word) = 1 \<rbrakk> \<Longrightarrow> P \<rbrakk>
                \<Longrightarrow> P"
   apply atomize_elim
  apply (case_tac "len_of TYPE ('a) = 1")
   apply clarsimp
   apply (subgoal_tac "(UNIV :: 'a word set) = {0, 1}")
    apply (metis UNIV_I insert_iff singletonE)
   apply (subst word_unat.univ)
   apply (clarsimp simp: unats_def image_def)
   apply (rule set_eqI, rule iffI)
    apply clarsimp
    apply (metis One_nat_def less_2_cases of_nat_1 semiring_1_class.of_nat_0)
   apply clarsimp
   apply (metis Abs_fnat_hom_0 Suc_1 lessI of_nat_1 zero_less_Suc)
  apply clarsimp
  apply (metis One_nat_def arith_is_1 le_def len_gt_0)
  done

lemma sint_int_min:
  "sint (- (2 ^ (LENGTH('a) - Suc 0)) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (subst word_sint.Abs_inverse' [where r="- (2 ^ (LENGTH('a) - Suc 0))"])
    apply (clarsimp simp: sints_num)
   apply (clarsimp simp: wi_hom_syms word_of_int_2p)
  apply clarsimp
  done

lemma sint_int_max_plus_1:
  "sint (2 ^ (LENGTH('a) - Suc 0) :: ('a::len) word) = - (2 ^ (LENGTH('a) - Suc 0))"
  apply (subst word_of_int_2p [symmetric])
  apply (subst int_word_sint)
  apply clarsimp
  apply (metis Suc_pred int_word_uint len_gt_0 power_Suc uint_eq_0 word_of_int_2p word_pow_0)
  done

lemma sbintrunc_eq_in_range:
  "(sbintrunc n x = x) = (x \<in> range (sbintrunc n))"
  "(x = sbintrunc n x) = (x \<in> range (sbintrunc n))"
  apply (simp_all add: image_def)
  apply (metis sbintrunc_sbintrunc)+
  done

lemma sbintrunc_If:
  "- 3 * (2 ^ n) \<le> x \<and> x < 3 * (2 ^ n)
    \<Longrightarrow> sbintrunc n x = (if x < - (2 ^ n) then x + 2 * (2 ^ n)
        else if x \<ge> 2 ^ n then x - 2 * (2 ^ n) else x)"
  apply (simp add: no_sbintr_alt2, safe)
   apply (simp add: mod_pos_geq)
  apply (subst mod_add_self1[symmetric], simp)
  done

lemma signed_arith_eq_checks_to_ord:
  "(sint a + sint b = sint (a + b ))
    = ((a <=s a + b) = (0 <=s b))"
  "(sint a - sint b = sint (a - b ))
    = ((0 <=s a - b) = (b <=s a))"
  "(- sint a = sint (- a)) = (0 <=s (- a) = (a <=s 0))"
  using sint_range'[where x=a] sint_range'[where x=b]
  by (simp_all add: sint_word_ariths word_sle_def word_sless_alt sbintrunc_If)

(* Basic proofs that signed word div/mod operations are
 * truncations of their integer counterparts. *)

lemma signed_div_arith:
    "sint ((a::('a::len) word) sdiv b) = sbintrunc (LENGTH('a) - 1) (sint a sdiv sint b)"
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (subst bin_sbin_eq_iff' [symmetric])
   apply simp
  apply (subst uint_sint [symmetric])
  apply (clarsimp simp: sdiv_int_def sdiv_word_def)
  apply (metis word_ubin.eq_norm)
  done

lemma signed_mod_arith:
    "sint ((a::('a::len) word) smod b) = sbintrunc (LENGTH('a) - 1) (sint a smod sint b)"
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (subst bin_sbin_eq_iff' [symmetric])
   apply simp
  apply (subst uint_sint [symmetric])
  apply (clarsimp simp: smod_int_def smod_word_def)
  apply (metis word_ubin.eq_norm)
  done

(* Signed word arithmetic overflow constraints. *)

lemma signed_arith_ineq_checks_to_eq:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a + sint b = sint (a + b ))"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a - sint b = sint (a - b))"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    = ((- sint a) = sint (- a))"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a * sint b = sint (a * b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a sdiv sint b = sint (a sdiv b))"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    = (sint a smod sint b = sint (a smod b))"
  by (auto simp: sint_word_ariths word_size signed_div_arith signed_mod_arith
                    sbintrunc_eq_in_range range_sbintrunc)

lemma signed_arith_sint:
  "((- (2 ^ (size a - 1)) \<le> (sint a + sint b)) \<and> (sint a + sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a + b) = (sint a + sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a - sint b)) \<and> (sint a - sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a - b) = (sint a - sint b)"
  "((- (2 ^ (size a - 1)) \<le> (- sint a)) \<and> (- sint a) \<le> (2 ^ (size a - 1) - 1))
    \<Longrightarrow> sint (- a) = (- sint a)"
  "((- (2 ^ (size a - 1)) \<le> (sint a * sint b)) \<and> (sint a * sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a * b) = (sint a * sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a sdiv sint b)) \<and> (sint a sdiv sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a sdiv b) = (sint a sdiv sint b)"
  "((- (2 ^ (size a - 1)) \<le> (sint a smod sint b)) \<and> (sint a smod sint b \<le> (2 ^ (size a - 1) - 1)))
    \<Longrightarrow> sint (a smod b) = (sint a smod sint b)"
  by (subst (asm) signed_arith_ineq_checks_to_eq; simp)+

lemma signed_mult_eq_checks_double_size:
  assumes mult_le: "(2 ^ (len_of TYPE ('a) - 1) + 1) ^ 2 \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
           and le: "2 ^ (LENGTH('a) - 1) \<le> (2 :: int) ^ (len_of TYPE ('b) - 1)"
  shows "(sint (a :: 'a :: len word) * sint b = sint (a * b))
       = (scast a * scast b = (scast (a * b) :: 'b :: len word))"
proof -
  have P: "sbintrunc (size a - 1) (sint a * sint b) \<in> range (sbintrunc (size a - 1))"
    by simp

  have abs: "!! x :: 'a word. abs (sint x) < 2 ^ (size a - 1) + 1"
    apply (cut_tac x=x in sint_range')
    apply (simp add: abs_le_iff word_size)
    done
  have abs_ab: "abs (sint a * sint b) < 2 ^ (LENGTH('b) - 1)"
    using abs_mult_less[OF abs[where x=a] abs[where x=b]] mult_le
    by (simp add: abs_mult power2_eq_square word_size)
  show ?thesis
    using P[unfolded range_sbintrunc] abs_ab le
    apply (simp add: sint_word_ariths scast_def)
    apply (simp add: wi_hom_mult)
    apply (subst word_sint.Abs_inject, simp_all)
     apply (simp add: sints_def range_sbintrunc abs_less_iff)
    apply clarsimp
    apply (simp add: sints_def range_sbintrunc word_size)
    apply (auto elim: order_less_le_trans order_trans[rotated])
    done
qed

(* Properties about signed division. *)

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  apply (auto simp: sdiv_int_def sgn_if)
  done

lemma sgn_div_eq_sgn_mult:
    "a div b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) div b) = sgn (a * b)"
  apply (clarsimp simp: sgn_if zero_le_mult_iff neg_imp_zdiv_nonneg_iff not_less)
  apply (metis less_le mult_le_0_iff neg_imp_zdiv_neg_iff not_less pos_imp_zdiv_neg_iff zdiv_eq_0_iff)
  done

lemma sgn_sdiv_eq_sgn_mult:
  "a sdiv b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) sdiv b) = sgn (a * b)"
  by (auto simp: sdiv_int_def sgn_div_eq_sgn_mult sgn_mult)

lemma int_sdiv_same_is_1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = a) = (b = 1)"
  apply (rule iffI)
   apply (clarsimp simp: sdiv_int_def)
   apply (subgoal_tac "b > 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if)
    apply (clarsimp simp: algebra_split_simps not_less)
    apply (metis int_div_same_is_1 le_neq_trans minus_minus neg_0_le_iff_le neg_equal_0_iff_equal)
   apply (case_tac "a > 0")
    apply (case_tac "b = 0")
     apply clarsimp
    apply (rule classical)
    apply (clarsimp simp: sgn_mult not_less)
    apply (metis le_less neg_0_less_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (rule classical)
   apply (clarsimp simp: algebra_split_simps sgn_mult not_less sgn_if split: if_splits)
   apply (metis antisym less_le neg_imp_zdiv_nonneg_iff)
  apply (clarsimp simp: sdiv_int_def sgn_if)
  done

lemma int_sdiv_negated_is_minus1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = - a) = (b = -1)"
  apply (clarsimp simp: sdiv_int_def)
  apply (rule iffI)
   apply (subgoal_tac "b < 0")
    apply (case_tac "a > 0")
     apply (clarsimp simp: sgn_if algebra_split_simps not_less)
    apply (case_tac "sgn (a * b) = -1")
     apply (clarsimp simp: not_less algebra_split_simps)
    apply (clarsimp simp: algebra_split_simps not_less)
   apply (rule classical)
   apply (case_tac "b = 0")
    apply (clarsimp simp: not_less sgn_mult)
   apply (case_tac "a > 0")
    apply (clarsimp simp: not_less sgn_mult)
    apply (metis less_le neg_less_0_iff_less not_less_iff_gr_or_eq pos_imp_zdiv_neg_iff)
   apply (clarsimp simp: not_less sgn_mult)
   apply (metis antisym_conv div_minus_right neg_imp_zdiv_nonneg_iff neg_le_0_iff_le not_less)
  apply (clarsimp simp: sgn_if)
  done

lemma sdiv_int_range:
    "(a :: int) sdiv b \<in> { - (abs a) .. (abs a) }"
  apply (unfold sdiv_int_def)
  apply (subgoal_tac "(abs a) div (abs b) \<le> (abs a)")
   apply (clarsimp simp: sgn_if)
   apply (meson abs_ge_zero neg_le_0_iff_le nonneg_mod_div order_trans)
  apply (metis abs_eq_0 abs_ge_zero div_by_0 zdiv_le_dividend zero_less_abs_iff)
  done

lemma word_sdiv_div1 [simp]:
    "(a :: ('a::len) word) sdiv 1 = a"
  apply (rule sint_1_cases [where a=a])
    apply (clarsimp simp: sdiv_word_def sdiv_int_def)
   apply (clarsimp simp: sdiv_word_def sdiv_int_def simp del: sint_minus1)
  apply (clarsimp simp: sdiv_word_def)
  done

lemma sdiv_int_div_0 [simp]:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: sdiv_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: sdiv_int_def)

lemma word_sdiv_div0 [simp]:
    "(a :: ('a::len) word) sdiv 0 = 0"
  apply (auto simp: sdiv_word_def sdiv_int_def sgn_if)
  done

lemma word_sdiv_div_minus1 [simp]:
    "(a :: ('a::len) word) sdiv -1 = -a"
  apply (auto simp: sdiv_word_def sdiv_int_def sgn_if)
  apply (metis wi_hom_neg word_sint.Rep_inverse')
  done

lemmas word_sdiv_0 = word_sdiv_div0

lemma sdiv_word_min:
    "- (2 ^ (size a - 1)) \<le> sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word)"
  apply (clarsimp simp: word_size)
  apply (cut_tac sint_range' [where x=a])
  apply (cut_tac sint_range' [where x=b])
  apply clarsimp
  apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: max_def abs_if split: if_split_asm)
  done

lemma sdiv_word_max:
    "(sint (a :: ('a::len) word) sdiv sint (b :: ('a::len) word) < (2 ^ (size a - 1))) =
          ((a \<noteq> - (2 ^ (size a - 1)) \<or> (b \<noteq> -1)))"
    (is "?lhs = (\<not> ?a_int_min \<or> \<not> ?b_minus1)")
proof (rule classical)
  assume not_thesis: "\<not> ?thesis"

  have not_zero: "b \<noteq> 0"
    using not_thesis
    by (clarsimp)

  have result_range: "sint a sdiv sint b \<in> (sints (size a)) \<union> {2 ^ (size a - 1)}"
    apply (cut_tac sdiv_int_range [where a="sint a" and b="sint b"])
    apply (erule rev_subsetD)
    using sint_range' [where x=a]  sint_range' [where x=b]
    apply (auto simp: max_def abs_if word_size sints_num)
    done

  have result_range_overflow: "(sint a sdiv sint b = 2 ^ (size a - 1)) = (?a_int_min \<and> ?b_minus1)"
    apply (rule iffI [rotated])
     apply (clarsimp simp: sdiv_int_def sgn_if word_size sint_int_min)
    apply (rule classical)
    apply (case_tac "?a_int_min")
     apply (clarsimp simp: word_size sint_int_min)
     apply (metis diff_0_right
              int_sdiv_negated_is_minus1 minus_diff_eq minus_int_code(2)
              power_eq_0_iff sint_minus1 zero_neq_numeral)
    apply (subgoal_tac "abs (sint a) < 2 ^ (size a - 1)")
     apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
     apply (clarsimp simp: word_size)
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])[1]
    apply (insert word_sint.Rep [where x="a"])[1]
    apply (clarsimp simp: minus_le_iff word_size abs_if sints_num split: if_split_asm)
    apply (metis minus_minus sint_int_min word_sint.Rep_inject)
    done

  have result_range_simple: "(sint a sdiv sint b \<in> (sints (size a))) \<Longrightarrow> ?thesis"
    apply (insert sdiv_int_range [where a="sint a" and b="sint b"])
    apply (clarsimp simp: word_size sints_num sint_int_min)
    done

  show ?thesis
    apply (rule UnE [OF result_range result_range_simple])
     apply simp
    apply (clarsimp simp: word_size)
    using result_range_overflow
    apply (clarsimp simp: word_size)
    done
qed

lemmas sdiv_word_min' = sdiv_word_min [simplified word_size, simplified]
lemmas sdiv_word_max' = sdiv_word_max [simplified word_size, simplified]

lemmas word_sdiv_numerals_lhs = sdiv_word_def[where a="numeral x" for x]
    sdiv_word_def[where a=0] sdiv_word_def[where a=1]

lemmas word_sdiv_numerals = word_sdiv_numerals_lhs[where b="numeral y" for y]
    word_sdiv_numerals_lhs[where b=0] word_sdiv_numerals_lhs[where b=1]

(*
 * Signed modulo properties.
 *)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  apply (clarsimp simp: smod_int_def sdiv_int_def)
  apply (clarsimp simp: minus_div_mult_eq_mod [symmetric] abs_sgn sgn_mult sgn_if algebra_split_simps)
  done

lemma smod_int_range:
  "b \<noteq> 0 \<Longrightarrow> (a::int) smod b \<in> { - abs b + 1 .. abs b - 1 }"
  apply (case_tac  "b > 0")
   apply (insert pos_mod_conj [where a=a and b=b])[1]
   apply (insert pos_mod_conj [where a="-a" and b=b])[1]
   apply (auto simp: smod_int_alt_def algebra_simps sgn_if
              abs_if not_less add1_zle_eq [simplified add.commute])[1]
    apply (metis add_nonneg_nonneg int_one_le_iff_zero_less le_less less_add_same_cancel2 not_le pos_mod_conj)
  apply (metis (full_types) add.inverse_inverse eucl_rel_int eucl_rel_int_iff le_less_trans neg_0_le_iff_le)
  apply (insert neg_mod_conj [where a=a and b="b"])[1]
  apply (insert neg_mod_conj [where a="-a" and b="b"])[1]
  apply (clarsimp simp: smod_int_alt_def algebra_simps sgn_if
            abs_if not_less add1_zle_eq [simplified add.commute])
  apply (metis neg_0_less_iff_less neg_mod_conj not_le not_less_iff_gr_or_eq order_trans pos_mod_conj)
  done

lemma smod_int_compares:
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b < b"
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> -b < (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b < - b"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> b \<le> (a :: int) smod b"
  apply (insert smod_int_range [where a=a and b=b])
  apply (auto simp: add1_zle_eq smod_int_alt_def sgn_if)
  done

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: smod_int_def)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma smod_word_mod_0 [simp]:
  "x smod (0 :: ('a::len) word) = x"
  by (clarsimp simp: smod_word_def)

lemma smod_word_0_mod [simp]:
  "0 smod (x :: ('a::len) word) = 0"
  by (clarsimp simp: smod_word_def)

lemma smod_word_max:
    "sint (a::'a word) smod sint (b::'a word) < 2 ^ (LENGTH('a::len) - Suc 0)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply (clarsimp)
  apply (insert word_sint.Rep [where x="b", simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if split: if_split_asm)
  done

lemma smod_word_min:
    "- (2 ^ (LENGTH('a::len) - Suc 0)) \<le> sint (a::'a word) smod sint (b::'a word)"
  apply (case_tac "b = 0")
   apply (insert word_sint.Rep [where x=a, simplified sints_num])[1]
   apply clarsimp
  apply (insert word_sint.Rep [where x=b, simplified sints_num])[1]
  apply (insert smod_int_range [where a="sint a" and b="sint b"])
  apply (clarsimp simp: abs_if add1_zle_eq split: if_split_asm)
  done

lemma smod_word_alt_def:
  "(a :: ('a::len) word) smod b = a - (a sdiv b) * b"
  apply (case_tac "a \<noteq> - (2 ^ (LENGTH('a) - 1)) \<or> b \<noteq> -1")
   apply (clarsimp simp: smod_word_def sdiv_word_def smod_int_def
             minus_word.abs_eq [symmetric] times_word.abs_eq [symmetric])
  apply (clarsimp simp: smod_word_def smod_int_def)
  done

lemmas word_smod_numerals_lhs = smod_word_def[where a="numeral x" for x]
    smod_word_def[where a=0] smod_word_def[where a=1]

lemmas word_smod_numerals = word_smod_numerals_lhs[where b="numeral y" for y]
    word_smod_numerals_lhs[where b=0] word_smod_numerals_lhs[where b=1]

lemma sint_of_int_eq:
  "\<lbrakk> - (2 ^ (LENGTH('a) - 1)) \<le> x; x < 2 ^ (LENGTH('a) - 1) \<rbrakk> \<Longrightarrow> sint (of_int x :: ('a::len) word) = x"
  apply (clarsimp simp: word_of_int int_word_sint)
  apply (subst int_mod_eq')
    apply simp
   apply (subst (2) power_minus_simp)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemma of_int_sint [simp]:
    "of_int (sint a) = a"
  apply (insert word_sint.Rep [where x=a])
  apply (clarsimp simp: word_of_int)
  done

lemma nth_w2p_scast [simp]:
  "((scast ((2::'a::len signed word) ^ n) :: 'a word) !! m)
         \<longleftrightarrow> ((((2::'a::len  word) ^ n) :: 'a word) !! m)"
  apply (subst nth_w2p)
  apply (case_tac "n \<ge> LENGTH('a)")
   apply (subst power_overflow, simp)
   apply clarsimp
  apply (metis nth_w2p scast_def test_bit_conj_lt
               len_signed nth_word_of_int word_sint.Rep_inverse)
  done

lemma scast_2_power [simp]: "scast ((2 :: 'a::len signed word) ^ x) = ((2 :: 'a word) ^ x)"
  by (clarsimp simp: word_eq_iff)

lemma scast_bit_test [simp]:
    "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by (clarsimp simp: word_eq_iff)

lemma ucast_nat_def':
  "of_nat (unat x) = (ucast :: 'a :: len word \<Rightarrow> ('b :: len) signed word) x"
  by (simp add: ucast_def word_of_int_nat unat_def)

lemma mod_mod_power_int:
  fixes k :: int
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
  by (metis bintrunc_bintrunc_min bintrunc_mod2p min.commute)

(* Normalise combinations of scast and ucast. *)

lemma ucast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (ucast :: 'a word \<Rightarrow> 'b word)"
  shows "ucast (M a b) = M' (ucast a) (ucast b)"
  apply (clarsimp simp: word_of_int ucast_def)
  apply (subst lift_M)
  apply (subst of_int_uint [symmetric], subst lift_M')
  apply (subst (1 2) int_word_uint)
  apply (subst word_of_int)
  apply (subst word.abs_eq_iff)
  apply (subst (1 2) bintrunc_mod2p)
  apply (insert is_down)
  apply (unfold is_down_def)
  apply (clarsimp simp: target_size source_size)
  apply (clarsimp simp: mod_mod_power_int min_def)
  apply (rule distrib [symmetric])
  done

lemma ucast_down_add:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) + b) = (ucast a + ucast b :: 'b::len word)"
  by (rule ucast_distrib [where L="(+)"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma ucast_down_minus:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) - b) = (ucast a - ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="(-)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_diff_left_eq mod_diff_right_eq)
  apply simp
  done

lemma ucast_down_mult:
    "is_down (ucast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  ucast ((a :: 'a::len word) * b) = (ucast a * ucast b :: 'b::len word)"
  apply (rule ucast_distrib [where L="(*)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_distrib:
  fixes M :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  fixes M' :: "'b::len word \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word"
  fixes L :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes lift_M: "\<And>x y. uint (M x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('a)"
  assumes lift_M': "\<And>x y. uint (M' x y) = L (uint x) (uint y)  mod 2 ^ LENGTH('b)"
  assumes distrib: "\<And>x y. (L (x mod (2 ^ LENGTH('b))) (y mod (2 ^ LENGTH('b)))) mod (2 ^ LENGTH('b))
                               = (L x y) mod (2 ^ LENGTH('b))"
  assumes is_down: "is_down (scast :: 'a word \<Rightarrow> 'b word)"
  shows "scast (M a b) = M' (scast a) (scast b)"
  apply (subst (1 2 3) down_cast_same [symmetric])
   apply (insert is_down)
   apply (clarsimp simp: is_down_def target_size source_size is_down)
  apply (rule ucast_distrib [where L=L, OF lift_M lift_M' distrib])
  apply (insert is_down)
  apply (clarsimp simp: is_down_def target_size source_size is_down)
  done

lemma scast_down_add:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) + b) = (scast a + scast b :: 'b::len word)"
  by (rule scast_distrib [where L="(+)"], (clarsimp simp: uint_word_ariths)+, presburger, simp)

lemma scast_down_minus:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) - b) = (scast a - scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="(-)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_diff_left_eq mod_diff_right_eq)
  apply simp
  done

lemma scast_down_mult:
    "is_down (scast:: 'a word \<Rightarrow> 'b word) \<Longrightarrow>  scast ((a :: 'a::len word) * b) = (scast a * scast b :: 'b::len word)"
  apply (rule scast_distrib [where L="(*)"], (clarsimp simp: uint_word_ariths)+)
  apply (metis mod_mult_eq)
  apply simp
  done

lemma scast_ucast_1:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_ucast_3:
  "\<lbrakk> is_down (ucast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_ucast_4:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma scast_scast_b:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def sint_up_scast)

lemma ucast_scast_1:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def ucast_down_wi)

lemma ucast_scast_3:
  "\<lbrakk> is_down (scast :: 'a word \<Rightarrow> 'c word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis scast_def ucast_down_wi)

lemma ucast_scast_4:
  "\<lbrakk> is_up (scast :: 'a word \<Rightarrow> 'b word); is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (metis down_cast_same scast_def sint_up_scast)

lemma ucast_ucast_a:
  "\<lbrakk> is_down (ucast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis down_cast_same ucast_def ucast_down_wi)

lemma ucast_ucast_b:
  "\<lbrakk> is_up (ucast :: 'a word \<Rightarrow> 'b word) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  by (metis ucast_up_ucast)

lemma scast_scast_a:
  "\<lbrakk> is_down (scast :: 'b word \<Rightarrow> 'c word) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  apply (clarsimp simp: scast_def)
  apply (metis down_cast_same is_up_down scast_def ucast_down_wi)
  done

lemma scast_down_wi [OF refl]:
  "uc = scast \<Longrightarrow> is_down uc \<Longrightarrow> uc (word_of_int x) = word_of_int x"
  by (metis down_cast_same is_up_down ucast_down_wi)

lemmas cast_simps =
  is_down is_up
  scast_down_add scast_down_minus scast_down_mult
  ucast_down_add ucast_down_minus ucast_down_mult
  scast_ucast_1 scast_ucast_3 scast_ucast_4
  ucast_scast_1 ucast_scast_3 ucast_scast_4
  ucast_ucast_a ucast_ucast_b
  scast_scast_a scast_scast_b
  ucast_down_bl
  ucast_down_wi scast_down_wi
  ucast_of_nat scast_of_nat
  uint_up_ucast sint_up_scast
  up_scast_surj up_ucast_surj

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

lemma nat_mult_power_less_eq:
  "b > 0 \<Longrightarrow> (a * b ^ n < (b :: nat) ^ m) = (a < b ^ (m - n))"
  using mult_less_cancel2[where m = a and k = "b ^ n" and n="b ^ (m - n)"]
        mult_less_cancel2[where m="a * b ^ (n - m)" and k="b ^ m" and n=1]
  apply (simp only: power_add[symmetric] nat_minus_add_max)
  apply (simp only: power_add[symmetric] nat_minus_add_max ac_simps)
  apply (simp add: max_def split: if_split_asm)
  done

lemma signed_shift_guard_to_word:
  "\<lbrakk> n < len_of TYPE ('a); n > 0 \<rbrakk>
    \<Longrightarrow> (unat (x :: 'a :: len word) * 2 ^ y < 2 ^ n)
    = (x = 0 \<or> x < (1 << n >> y))"
  apply (simp only: nat_mult_power_less_eq)
  apply (cases "y \<le> n")
   apply (simp only: shiftl_shiftr1)
   apply (subst less_mask_eq)
    apply (simp add: word_less_nat_alt word_size)
    apply (rule order_less_le_trans[rotated], rule power_increasing[where n=1])
      apply simp
     apply simp
    apply simp
   apply (simp add: nat_mult_power_less_eq word_less_nat_alt word_size)
   apply auto[1]
  apply (simp only: shiftl_shiftr2, simp add: unat_eq_0)
  done

lemma sint_ucast_eq_uint:
    "\<lbrakk> \<not> is_down (ucast :: ('a::len word \<Rightarrow> 'b::len word)) \<rbrakk>
            \<Longrightarrow> sint ((ucast :: ('a::len word \<Rightarrow> 'b::len word)) x) = uint x"
  apply (subst sint_eq_uint)
   apply (clarsimp simp: msb_nth nth_ucast is_down)
   apply (metis Suc_leI Suc_pred len_gt_0)
  apply (clarsimp simp: uint_up_ucast is_up is_down)
  done

lemma word_less_nowrapI':
  "(x :: 'a :: len0 word) \<le> z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  by uint_arith

lemma mask_plus_1:
  "mask n + 1 = 2 ^ n"
  by (clarsimp simp: mask_def)

lemma unat_inj: "inj unat"
  by (metis eq_iff injI word_le_nat_alt)

lemma unat_ucast_upcast:
  "is_up (ucast :: 'b word \<Rightarrow> 'a word)
      \<Longrightarrow> unat (ucast x :: ('a::len) word) = unat (x :: ('b::len) word)"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply (clarsimp simp: is_up)
  apply simp
  done

lemma ucast_mono:
  "\<lbrakk> (x :: 'b :: len word) < y; y < 2 ^ LENGTH('a) \<rbrakk>
   \<Longrightarrow> ucast x < ((ucast y) :: 'a :: len word)"
  apply (simp add: ucast_nat_def [symmetric])
  apply (rule of_nat_mono_maybe)
  apply (rule unat_less_helper)
  apply (simp add: Power.of_nat_power)
  apply (simp add: word_less_nat_alt)
  done

lemma ucast_mono_le:
  "\<lbrakk>x \<le> y; y < 2 ^ LENGTH('b)\<rbrakk> \<Longrightarrow> (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> ucast y"
  apply (simp add: ucast_nat_def [symmetric])
  apply (subst of_nat_mono_maybe_le[symmetric])
    apply (rule unat_less_helper)
    apply (simp add: Power.of_nat_power)
   apply (rule unat_less_helper)
   apply (erule le_less_trans)
   apply (simp add: Power.of_nat_power)
  apply (simp add: word_le_nat_alt)
  done

lemma ucast_mono_le':
  "\<lbrakk> unat y < 2 ^ LENGTH('b); LENGTH('b::len) < LENGTH('a::len); x \<le> y \<rbrakk>
   \<Longrightarrow> UCAST('a \<rightarrow> 'b) x \<le> UCAST('a \<rightarrow> 'b) y"
  by (auto simp: word_less_nat_alt intro: ucast_mono_le)

lemma zero_sle_ucast_up:
  "\<not> is_down (ucast :: 'a word \<Rightarrow> 'b signed word) \<Longrightarrow>
          (0 <=s ((ucast (b::('a::len) word)) :: ('b::len) signed word))"
  apply (subgoal_tac "\<not> msb (ucast b :: 'b signed word)")
   apply (clarsimp simp: word_sle_msb_le)
  apply (clarsimp simp: is_down not_le msb_nth nth_ucast)
  apply (subst (asm) test_bit_conj_lt [symmetric])
  apply clarsimp
  apply arith
  done

lemma word_le_ucast_sless:
  "\<lbrakk> x \<le> y; y \<noteq> -1; LENGTH('a) < LENGTH('b) \<rbrakk> \<Longrightarrow>
    UCAST (('a :: len) \<rightarrow> ('b :: len) signed) x <s ucast (y + 1)"
  by (clarsimp simp: word_le_make_less word_sless_alt sint_ucast_eq_uint is_down word_less_def)

lemma msb_ucast_eq:
    "LENGTH('a) = LENGTH('b) \<Longrightarrow>
         msb (ucast x :: ('a::len) word) = msb (x :: ('b::len) word)"
  apply (clarsimp simp: word_msb_alt)
  apply (subst ucast_down_drop [where n=0])
   apply (clarsimp simp: source_size_def target_size_def word_size)
  apply clarsimp
  done

lemma msb_big:
     "msb (a :: ('a::len) word) = (a \<ge> 2 ^ (LENGTH('a)  - Suc 0))"
  apply (rule iffI)
   apply (clarsimp simp: msb_nth)
   apply (drule bang_is_le)
   apply simp
  apply (rule ccontr)
  apply (subgoal_tac "a = a && mask (LENGTH('a) - Suc 0)")
   apply (cut_tac and_mask_less' [where w=a and n="LENGTH('a) - Suc 0"])
    apply (clarsimp simp: word_not_le [symmetric])
   apply clarsimp
  apply (rule sym, subst and_mask_eq_iff_shiftr_0)
  apply (clarsimp simp: msb_shift)
  done

lemma zero_sle_ucast:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b < 2 ^ (LENGTH('a) - 1))"
  apply (case_tac "msb b")
   apply (clarsimp simp: word_sle_msb_le not_less msb_ucast_eq del: notI)
   apply (clarsimp simp: msb_big word_le_def uint_2p_alt)
  apply (clarsimp simp: word_sle_msb_le not_less msb_ucast_eq del: notI)
  apply (clarsimp simp: msb_big word_le_def uint_2p_alt)
  done


(* to_bool / from_bool. *)

definition
  from_bool :: "bool \<Rightarrow> 'a::len word" where
  "from_bool b \<equiv> case b of True \<Rightarrow> of_nat 1
                         | False \<Rightarrow> of_nat 0"

lemma from_bool_0:
  "(from_bool x = 0) = (\<not> x)"
  by (simp add: from_bool_def split: bool.split)

definition
  to_bool :: "'a::len word \<Rightarrow> bool" where
  "to_bool \<equiv> (\<noteq>) 0"

lemma to_bool_and_1:
  "to_bool (x && 1) = (x !! 0)"
  apply (simp add: to_bool_def)
  apply (rule iffI)
   apply (rule classical, erule notE, word_eqI)
   apply (case_tac n; simp)
  apply (rule notI, drule word_eqD[where x=0])
  apply simp
  done

lemma to_bool_from_bool [simp]:
  "to_bool (from_bool r) = r"
  unfolding from_bool_def to_bool_def
  by (simp split: bool.splits)

lemma from_bool_neq_0 [simp]:
  "(from_bool b \<noteq> 0) = b"
  by (simp add: from_bool_def split: bool.splits)

lemma from_bool_mask_simp [simp]:
  "(from_bool r :: 'a::len word) && 1 = from_bool r"
  unfolding from_bool_def
  by (clarsimp split: bool.splits)

lemma from_bool_1 [simp]:
  "(from_bool P = 1) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma ge_0_from_bool [simp]:
  "(0 < from_bool P) = P"
  by (simp add: from_bool_def split: bool.splits)

lemma limited_and_from_bool:
  "limited_and (from_bool b) 1"
  by (simp add: from_bool_def limited_and_def split: bool.split)

lemma to_bool_1 [simp]: "to_bool 1" by (simp add: to_bool_def)
lemma to_bool_0 [simp]: "\<not>to_bool 0" by (simp add: to_bool_def)

lemma from_bool_eq_if:
  "(from_bool Q = (if P then 1 else 0)) = (P = Q)"
  by (simp add: case_bool_If from_bool_def split: if_split)

lemma to_bool_eq_0:
  "(\<not> to_bool x) = (x = 0)"
  by (simp add: to_bool_def)

lemma to_bool_neq_0:
  "(to_bool x) = (x \<noteq> 0)"
  by (simp add: to_bool_def)

lemma from_bool_all_helper:
  "(\<forall>bool. from_bool bool = val \<longrightarrow> P bool)
      = ((\<exists>bool. from_bool bool = val) \<longrightarrow> P (val \<noteq> 0))"
  by (auto simp: from_bool_0)

lemma from_bool_to_bool_iff:
  "w = from_bool b \<longleftrightarrow> to_bool w = b \<and> (w = 0 \<or> w = 1)"
  by (cases b) (auto simp: from_bool_def to_bool_def)

lemma from_bool_eqI:
  "from_bool x = from_bool y \<Longrightarrow> x = y"
  unfolding from_bool_def
  by (auto split: bool.splits)

lemma word_rsplit_upt:
  "\<lbrakk> size x = LENGTH('a :: len) * n; n \<noteq> 0 \<rbrakk>
    \<Longrightarrow> word_rsplit x = map (\<lambda>i. ucast (x >> i * len_of TYPE ('a)) :: 'a word) (rev [0 ..< n])"
  apply (subgoal_tac "length (word_rsplit x :: 'a word list) = n")
   apply (rule nth_equalityI, simp)
   apply (intro allI word_eqI impI)
   apply (simp add: test_bit_rsplit_alt word_size)
   apply (simp add: nth_ucast nth_shiftr nth_rev field_simps)
  apply (simp add: length_word_rsplit_exp_size)
  apply (metis mult.commute given_quot_alt word_size word_size_gt_0)
  done

lemma aligned_shift:
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> x + y >> n = y >> n"
  by (subst word_plus_and_or_coroll; word_eqI, blast)

lemma aligned_shift':
  "\<lbrakk>x < 2 ^ n; is_aligned (y :: 'a :: len word) n;n \<le> LENGTH('a)\<rbrakk>
   \<Longrightarrow> y + x >> n = y >> n"
  by (subst word_plus_and_or_coroll; word_eqI, blast)

lemma neg_mask_add_mask:
  "((x:: 'a :: len word) && ~~ (mask n)) + (2 ^ n - 1) = x || mask n"
  unfolding mask_2pm1[symmetric]
  by (subst word_plus_and_or_coroll; word_eqI_solve)

lemma subtract_mask:
  "p - (p && mask n) = (p && ~~ (mask n))"
  "p - (p && ~~ (mask n)) = (p && mask n)"
  by (simp add: field_simps word_plus_and_or_coroll2)+

lemma and_neg_mask_plus_mask_mono: "(p && ~~ (mask n)) + mask n \<ge> p"
  apply (rule word_le_minus_cancel[where x = "p && ~~ (mask n)"])
   apply (clarsimp simp: subtract_mask)
   using word_and_le1[where a = "mask n" and y = p]
   apply (clarsimp simp: mask_def word_le_less_eq)
  apply (rule is_aligned_no_overflow'[folded mask_2pm1])
  apply (clarsimp simp: is_aligned_neg_mask)
  done

lemma word_neg_and_le:
  "ptr \<le> (ptr && ~~ (mask n)) + (2 ^ n - 1)"
  by (simp add: and_neg_mask_plus_mask_mono mask_2pm1[symmetric])

lemma aligned_less_plus_1:
  "\<lbrakk> is_aligned x n; n > 0 \<rbrakk> \<Longrightarrow> x < x + 1"
  apply (rule plus_one_helper2)
   apply (rule order_refl)
  apply (clarsimp simp: field_simps)
  apply (drule arg_cong[where f="\<lambda>x. x - 1"])
  apply (clarsimp simp: is_aligned_mask)
  apply (drule word_eqD[where x=0])
  apply simp
  done

lemma aligned_add_offset_less:
  "\<lbrakk>is_aligned x n; is_aligned y n; x < y; z < 2 ^ n\<rbrakk> \<Longrightarrow> x + z < y"
  apply (cases "y = 0")
   apply simp
  apply (erule is_aligned_get_word_bits[where p=y], simp_all)
  apply (cases "z = 0", simp_all)
  apply (drule(2) aligned_at_least_t2n_diff[rotated -1])
  apply (drule plus_one_helper2)
   apply (rule less_is_non_zero_p1)
   apply (rule aligned_less_plus_1)
    apply (erule aligned_sub_aligned[OF _ _ order_refl],
           simp_all add: is_aligned_triv)[1]
   apply (cases n, simp_all)[1]
  apply (simp only: trans[OF diff_add_eq diff_diff_eq2[symmetric]])
  apply (drule word_less_add_right)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule aligned_small_is_0, erule order_less_trans)
    apply (clarsimp simp: power_overflow)
   apply simp
  apply (erule order_le_less_trans[rotated],
         rule word_plus_mono_right)
   apply (erule word_le_minus_one_leq)
  apply (simp add: is_aligned_no_wrap' is_aligned_no_overflow field_simps)
  done

lemma is_aligned_add_helper:
  "\<lbrakk> is_aligned p n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p + d && mask n = d) \<and> (p + d && (~~ (mask n)) = p)"
  apply (subst(asm) is_aligned_mask)
  apply (drule less_mask_eq)
  apply (rule context_conjI)
   apply (subst word_plus_and_or_coroll; word_eqI; blast)
  using word_plus_and_or_coroll2[where x="p + d" and w="mask n"] by simp

lemma is_aligned_sub_helper:
  "\<lbrakk> is_aligned (p - d) n; d < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p && mask n = d) \<and> (p && (~~ (mask n)) = p - d)"
  by (drule(1) is_aligned_add_helper, simp)

lemma mask_twice:
  "(x && mask n) && mask m = x && mask (min m n)"
  by word_eqI_solve

lemma is_aligned_after_mask:
  "\<lbrakk>is_aligned k m;m\<le> n\<rbrakk> \<Longrightarrow> is_aligned (k && mask n) m"
  by (rule is_aligned_andI1)

lemma and_mask_plus:
  "\<lbrakk>is_aligned ptr m; m \<le> n; a < 2 ^ m\<rbrakk>
   \<Longrightarrow> ptr + a && mask n = (ptr && mask n) + a"
  apply (rule mask_eqI[where n = m])
   apply (simp add:mask_twice min_def)
    apply (simp add:is_aligned_add_helper)
    apply (subst is_aligned_add_helper[THEN conjunct1])
      apply (erule is_aligned_after_mask)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "(ptr + a && mask n) && ~~ (mask m)
     = (ptr + a && ~~ (mask m) ) && mask n")
   apply (simp add:is_aligned_add_helper)
   apply (subst is_aligned_add_helper[THEN conjunct2])
     apply (simp add:is_aligned_after_mask)
    apply simp
   apply simp
  apply (simp add:word_bw_comms word_bw_lcs)
  done

lemma le_step_down_word:"\<lbrakk>(i::('a::len) word) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by unat_arith

lemma le_step_down_word_2:
  fixes x :: "'a::len word"
  shows "\<lbrakk>x \<le>  y; x \<noteq> y\<rbrakk> \<Longrightarrow> x \<le> y - 1"
  by (subst (asm) word_le_less_eq,
      clarsimp,
      simp add: word_le_minus_one_leq)

lemma NOT_mask_AND_mask[simp]: "(w && mask n) && ~~ (mask n) = 0"
  apply (clarsimp simp:mask_def)
  by (metis word_bool_alg.conj_cancel_right word_bool_alg.conj_zero_right word_bw_comms(1) word_bw_lcs(1))

lemma and_and_not[simp]:"(a && b) && ~~ b = 0"
  apply (subst word_bw_assocs(1))
  apply clarsimp
  done

lemma mask_shift_and_negate[simp]:"(w && mask n << m) && ~~ (mask n << m) = 0"
  apply (clarsimp simp:mask_def)
  by (metis (erased, hide_lams) mask_eq_x_eq_0 shiftl_over_and_dist word_bool_alg.conj_absorb word_bw_assocs(1))

lemma le_step_down_nat:"\<lbrakk>(i::nat) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma le_step_down_int:"\<lbrakk>(i::int) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma ex_mask_1[simp]: "(\<exists>x. mask x = 1)"
  apply (rule_tac x=1 in exI)
  apply (simp add:mask_def)
  done

lemma not_switch:"~~ a = x \<Longrightarrow> a = ~~ x"
  by auto

(* The seL4 bitfield generator produces functions containing mask and shift operations, such that
 * invoking two of them consecutively can produce something like the following.
 *)
lemma bitfield_op_twice:
  "(x && ~~ (mask n << m) || ((y && mask n) << m)) && ~~ (mask n << m) = x && ~~ (mask n << m)"
  by (induct n arbitrary: m) (auto simp: word_ao_dist)

lemma bitfield_op_twice'':
  "\<lbrakk>~~ a = b << c; \<exists>x. b = mask x\<rbrakk> \<Longrightarrow> (x && a || (y && b << c)) && a = x && a"
  apply clarsimp
  apply (cut_tac n=xa and m=c and x=x and y=y in bitfield_op_twice)
  apply (clarsimp simp:mask_def)
  apply (drule not_switch)
  apply clarsimp
  done

lemma bit_twiddle_min:
  "(y::'a::len word) xor (((x::'a::len word) xor y) && (if x < y then -1 else 0)) = min x y"
  by (metis (mono_tags) min_def word_bitwise_m1_simps(2) word_bool_alg.xor_left_commute
             word_bool_alg.xor_self word_bool_alg.xor_zero_right word_bw_comms(1)
             word_le_less_eq word_log_esimps(7))

lemma bit_twiddle_max:
  "(x::'a::len word) xor (((x::'a::len word) xor y) && (if x < y then -1 else 0)) = max x y"
  by (metis (mono_tags) max_def word_bitwise_m1_simps(2) word_bool_alg.xor_left_self
            word_bool_alg.xor_zero_right word_bw_comms(1) word_le_less_eq word_log_esimps(7))

lemma swap_with_xor:
  "\<lbrakk>(x::'a::len word) = a xor b; y = b xor x; z = x xor y\<rbrakk> \<Longrightarrow> z = b \<and> y = a"
  by (metis word_bool_alg.xor_assoc word_bool_alg.xor_commute word_bool_alg.xor_self
            word_bool_alg.xor_zero_right)

lemma scast_nop1:
  "((scast ((of_int x)::('a::len) word))::'a sword) = of_int x"
  apply (clarsimp simp:scast_def word_of_int)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemma scast_nop2:
  "((scast ((of_int x)::('a::len) sword))::'a word) = of_int x"
  apply (clarsimp simp:scast_def word_of_int)
  by (metis len_signed sint_sbintrunc' word_sint.Rep_inverse)

lemmas scast_nop[simp] = scast_nop1 scast_nop2 scast_id

lemma le_mask_imp_and_mask:
  "(x::'a::len word) \<le> mask n \<Longrightarrow> x && mask n = x"
  by (metis and_mask_eq_iff_le_mask)

lemma or_not_mask_nop:
  "((x::'a::len word) || ~~ (mask n)) && mask n = x && mask n"
  by (metis word_and_not word_ao_dist2 word_bw_comms(1) word_log_esimps(3))

lemma mask_subsume:
  "\<lbrakk>n \<le> m\<rbrakk> \<Longrightarrow> ((x::'a::len word) || y && mask n) && ~~ (mask m) = x && ~~ (mask m)"
  apply (subst word_ao_dist)
  apply (subgoal_tac "(y && mask n) && ~~ (mask m) = 0")
   apply simp
  by (metis (no_types, hide_lams) is_aligned_mask is_aligned_weaken word_and_not
            word_bool_alg.conj_zero_right word_bw_comms(1) word_bw_lcs(1))

lemma and_mask_0_iff_le_mask:
  fixes w :: "'a::len word"
  shows "(w && ~~(mask n) = 0) = (w \<le> mask n)"
  by (simp add: mask_eq_0_eq_x le_mask_imp_and_mask and_mask_eq_iff_le_mask)

lemma mask_twice2:
  "n \<le> m \<Longrightarrow> ((x::'a::len word) && mask m) && mask n = x && mask n"
  by (metis mask_twice min_def)

lemma uint_2_id:
  "LENGTH('a) \<ge> 2 \<Longrightarrow> uint (2::('a::len) word) = 2"
  apply clarsimp
  apply (subgoal_tac "2 \<in> uints (LENGTH('a))")
   apply (subst (asm) Word.word_ubin.set_iff_norm)
   apply simp
  apply (subst word_uint.set_iff_norm)
  apply clarsimp
  apply (rule int_mod_eq')
   apply simp
  apply (rule pow_2_gt)
  apply simp
  done

lemma bintrunc_id:
  "\<lbrakk>m \<le> of_nat n; 0 < m\<rbrakk> \<Longrightarrow> bintrunc n m = m"
  by (simp add: bintrunc_mod2p le_less_trans)

lemma shiftr1_unfold: "shiftr1 x = x >> 1"
  by (metis One_nat_def comp_apply funpow.simps(1) funpow.simps(2) id_apply shiftr_def)

lemma shiftr1_is_div_2: "(x::('a::len) word) >> 1 = x div 2"
  apply (case_tac "LENGTH('a) = 1")
   apply simp
 apply (subgoal_tac "x = 0 \<or> x = 1")
    apply (erule disjE)
     apply (clarsimp simp:word_div_def)+
   apply (metis One_nat_def less_irrefl_nat sint_1_cases)
  apply clarsimp
  apply (subst word_div_def)
  apply clarsimp
  apply (subst bintrunc_id)
    apply (subgoal_tac "2 \<le> LENGTH('a)")
     apply simp
    apply (metis (no_types) le_0_eq le_SucE lens_not_0(2) not_less_eq_eq numeral_2_eq_2)
   apply simp
  apply (subst bin_rest_def[symmetric])
  apply (subst shiftr1_def[symmetric])
  apply (clarsimp simp:shiftr1_unfold)
  done

lemma shiftl1_is_mult: "(x << 1) = (x :: 'a::len word) * 2"
  by (metis One_nat_def mult_2 mult_2_right one_add_one
        power_0 power_Suc shiftl_t2n)

lemma div_of_0_id[simp]:"(0::('a::len) word) div n = 0"
  by (simp add: word_div_def)

lemma degenerate_word:"LENGTH('a) = 1 \<Longrightarrow> (x::('a::len) word) = 0 \<or> x = 1"
  by (metis One_nat_def less_irrefl_nat sint_1_cases)

lemma div_by_0_word:"(x::('a::len) word) div 0 = 0"
  by (metis div_0 div_by_0 unat_0 word_arith_nat_defs(6) word_div_1)

lemma div_less_dividend_word:"\<lbrakk>x \<noteq> 0; n \<noteq> 1\<rbrakk> \<Longrightarrow> (x::('a::len) word) div n < x"
  apply (case_tac "n = 0")
   apply clarsimp
   apply (subst div_by_0_word)
   apply (simp add:word_neq_0_conv)
  apply (subst word_arith_nat_div)
  apply (rule word_of_nat_less)
  apply (rule div_less_dividend)
   apply (metis (poly_guards_query) One_nat_def less_one nat_neq_iff unat_eq_1(2) unat_eq_zero)
  apply (simp add:unat_gt_0)
  done

lemma shiftr1_lt:"x \<noteq> 0 \<Longrightarrow> (x::('a::len) word) >> 1 < x"
  apply (subst shiftr1_is_div_2)
  apply (rule div_less_dividend_word)
   apply simp+
  done

lemma word_less_div:
  fixes x :: "('a::len) word"
    and y :: "('a::len) word"
  shows "x div y = 0 \<Longrightarrow> y = 0 \<or> x < y"
  apply (case_tac "y = 0", clarsimp+)
  by (metis One_nat_def Suc_le_mono le0 le_div_geq not_less unat_0 unat_div unat_gt_0 word_less_nat_alt zero_less_one)

lemma not_degenerate_imp_2_neq_0:"LENGTH('a) > 1 \<Longrightarrow> (2::('a::len) word) \<noteq> 0"
  by (metis numerals(1) power_not_zero power_zero_numeral)

lemma shiftr1_0_or_1:"(x::('a::len) word) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x = 1"
  apply (subst (asm) shiftr1_is_div_2)
  apply (drule word_less_div)
  apply (case_tac "LENGTH('a) = 1")
   apply (simp add:degenerate_word)
  apply (erule disjE)
   apply (subgoal_tac "(2::'a word) \<noteq> 0")
    apply simp
   apply (rule not_degenerate_imp_2_neq_0)
   apply (subgoal_tac "LENGTH('a) \<noteq> 0")
    apply arith
   apply simp
  apply (rule x_less_2_0_1', simp+)
  done

lemma word_overflow:"(x::('a::len) word) + 1 > x \<or> x + 1 = 0"
  apply clarsimp
  by (metis diff_0 eq_diff_eq less_x_plus_1 max_word_max plus_1_less)

lemma word_overflow_unat:"unat ((x::('a::len) word) + 1) = unat x + 1 \<or> x + 1 = 0"
  by (metis Suc_eq_plus1 add.commute unatSuc)

lemma even_word_imp_odd_next:"even (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> odd (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma odd_word_imp_even_next:"odd (unat (x::('a::len) word)) \<Longrightarrow> x + 1 = 0 \<or> even (unat (x + 1))"
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  done

lemma overflow_imp_lsb:"(x::('a::len) word) + 1 = 0 \<Longrightarrow> x !! 0"
  by (metis add.commute add_left_cancel max_word_max not_less word_and_1 word_bool_alg.conj_one_right word_bw_comms(1) word_overflow zero_neq_one)

lemma word_lsb_nat:"lsb w = (unat w mod 2 = 1)"
  unfolding word_lsb_def bin_last_def
  by (metis (no_types, hide_lams) nat_mod_distrib nat_numeral not_mod_2_eq_1_eq_0 numeral_One uint_eq_0 uint_nonnegative unat_0 unat_def zero_le_numeral)

lemma odd_iff_lsb:"odd (unat (x::('a::len) word)) = x !! 0"
  apply (simp add:even_iff_mod_2_eq_zero)
  apply (subst word_lsb_nat[unfolded One_nat_def, symmetric])
  apply (rule word_lsb_alt)
  done

lemma of_nat_neq_iff_word:
      "x mod 2 ^ LENGTH('a) \<noteq> y mod 2 ^ LENGTH('a) \<Longrightarrow>
         (((of_nat x)::('a::len) word) \<noteq> of_nat y) = (x \<noteq> y)"
  apply (rule iffI)
   apply (case_tac "x = y")
   apply (subst (asm) of_nat_eq_iff[symmetric])
   apply simp+
  apply (case_tac "((of_nat x)::('a::len) word) = of_nat y")
   apply (subst (asm) word_unat.norm_eq_iff[symmetric])
   apply simp+
  done

lemma shiftr1_irrelevant_lsb:"(x::('a::len) word) !! 0 \<or> x >> 1 = (x + 1) >> 1"
  apply (case_tac "LENGTH('a) = 1")
   apply clarsimp
   apply (drule_tac x=x in degenerate_word[unfolded One_nat_def])
   apply (erule disjE)
    apply clarsimp+
  apply (subst (asm) shiftr1_is_div_2[unfolded One_nat_def])+
  apply (subst (asm) word_arith_nat_div)+
  apply clarsimp
  apply (subst (asm) bintrunc_id)
    apply (subgoal_tac "LENGTH('a) > 0")
     apply linarith
    apply clarsimp+
  apply (subst (asm) bintrunc_id)
    apply (subgoal_tac "LENGTH('a) > 0")
     apply linarith
    apply clarsimp+
  apply (case_tac "x + 1 = 0")
   apply (clarsimp simp:overflow_imp_lsb)
  apply (cut_tac x=x in word_overflow_unat)
  apply clarsimp
  apply (case_tac "even (unat x)")
   apply (subgoal_tac "unat x div 2 = Suc (unat x) div 2")
    apply metis
   apply (subst numeral_2_eq_2)+
   apply simp
  apply (simp add:odd_iff_lsb)
  done

lemma shiftr1_0_imp_only_lsb:"((x::('a::len) word) + 1) >> 1 = 0 \<Longrightarrow> x = 0 \<or> x + 1 = 0"
  by (metis One_nat_def shiftr1_0_or_1 word_less_1 word_overflow)

lemma shiftr1_irrelevant_lsb':"\<not>((x::('a::len) word) !! 0) \<Longrightarrow> x >> 1 = (x + 1) >> 1"
  by (metis shiftr1_irrelevant_lsb)

lemma lsb_this_or_next:"\<not>(((x::('a::len) word) + 1) !! 0) \<Longrightarrow> x !! 0"
  by (metis (poly_guards_query) even_word_imp_odd_next odd_iff_lsb overflow_imp_lsb)

(* Perhaps this one should be a simp lemma, but it seems a little dangerous. *)
lemma cast_chunk_assemble_id:
  "\<lbrakk>n = LENGTH('a::len); m = LENGTH('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((ucast (x::'b word))::'a word))::'b word) || (((ucast ((ucast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((ucast ((ucast (x >> n))::'a word))::'b word) = x >> n")
   apply clarsimp
   apply (subst and_not_mask[symmetric])
   apply (subst ucast_ucast_mask)
   apply (subst word_ao_dist2[symmetric])
   apply clarsimp
  apply (rule ucast_ucast_len)
  apply (rule shiftr_less_t2n')
   apply (subst and_mask_eq_iff_le_mask)
   apply (clarsimp simp:mask_def)
   apply (metis max_word_eq max_word_max mult_2_right)
  apply (metis add_diff_cancel_left' diff_less len_gt_0 mult_2_right)
  done

lemma cast_chunk_scast_assemble_id:
  "\<lbrakk>n = LENGTH('a::len); m = LENGTH('b::len); n * 2 = m\<rbrakk> \<Longrightarrow>
  (((ucast ((scast (x::'b word))::'a word))::'b word) ||
   (((ucast ((scast (x >> n))::'a word))::'b word) << n)) = x"
  apply (subgoal_tac "((scast x)::'a word) = ((ucast x)::'a word)")
   apply (subgoal_tac "((scast (x >> n))::'a word) = ((ucast (x >> n))::'a word)")
    apply (simp add:cast_chunk_assemble_id)
   apply (subst down_cast_same[symmetric], subst is_down, arith, simp)+
  done

lemma mask_or_not_mask:
  "x && mask n || x && ~~ (mask n) = x"
  apply (subst word_oa_dist, simp)
  apply (subst word_oa_dist2, simp)
  done

lemma is_aligned_add_not_aligned:
  "\<lbrakk>is_aligned (p::'a::len word) n; \<not> is_aligned (q::'a::len word) n\<rbrakk> \<Longrightarrow> \<not> is_aligned (p + q) n"
  by (metis is_aligned_addD1)

lemma word_gr0_conv_Suc: "(m::'a::len word) > 0 \<Longrightarrow> \<exists>n. m = n + 1"
  by (metis add.commute add_minus_cancel)

lemma neg_mask_add_aligned:
  "\<lbrakk> is_aligned p n; q < 2 ^ n \<rbrakk> \<Longrightarrow> (p + q) && ~~ (mask n) = p && ~~ (mask n)"
  by (metis is_aligned_add_helper is_aligned_neg_mask_eq)

lemma word_sless_sint_le:"x <s y \<Longrightarrow> sint x \<le> sint y - 1"
  by (metis word_sless_alt zle_diff1_eq)


lemma upper_trivial:
  fixes x :: "'a::len word"
  shows "x \<noteq> 2 ^ LENGTH('a) - 1 \<Longrightarrow> x < 2 ^ LENGTH('a) - 1"
  by (cut_tac n=x and 'a='a in max_word_max,
      clarsimp simp:max_word_def,
      simp add: less_le)

lemma constraint_expand:
  fixes x :: "'a::len word"
  shows "x \<in> {y. lower \<le> y \<and> y \<le> upper} = (lower \<le> x \<and> x \<le> upper)"
  by (rule mem_Collect_eq)

lemma card_map_elide:
  "card ((of_nat :: nat \<Rightarrow> 'a::len word) ` {0..<n}) = card {0..<n}"
    if "n \<le> CARD('a::len word)"
proof -
  let ?of_nat = "of_nat :: nat \<Rightarrow> 'a word"
  from word_unat.Abs_inj_on
  have "inj_on ?of_nat {i. i < CARD('a word)}"
    by (simp add: unats_def card_word)
  moreover have "{0..<n} \<subseteq> {i. i < CARD('a word)}"
    using that by auto
  ultimately have "inj_on ?of_nat {0..<n}"
    by (rule inj_on_subset)
  then show ?thesis
    by (simp add: card_image)
qed

lemma card_map_elide2:
  "n \<le> CARD('a::len word) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> 'a::len word) ` {0..<n}) = n"
  by (subst card_map_elide) clarsimp+

lemma le_max_word_ucast_id:
  assumes "(x::'a::len word) \<le> ucast (max_word::'b::len word)"
  shows "ucast ((ucast x)::'b word) = x"
proof -
  {
    assume a1: "x \<le> word_of_int (uint (word_of_int (2 ^ LENGTH('b) - 1)::'b word))"
    have f2: "((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
              \<not> (0::int) \<le> - 1 + 2 ^ LENGTH('b) \<or> (0::int) \<le> - 1 + 2 ^ LENGTH('b) + - 1 * 2 ^ LENGTH('b) \<or>
              (- (1::int) + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b) =
                - 1 + 2 ^ LENGTH('b)) = ((\<exists>i ia. (0::int) \<le> i \<and> \<not> 0 \<le> i + - 1 * ia \<and> i mod ia \<noteq> i) \<or>
              \<not> (1::int) \<le> 2 ^ LENGTH('b) \<or>
              2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)) = 1)"
      by force
    have f3: "\<forall>i ia. \<not> (0::int) \<le> i \<or> 0 \<le> i + - 1 * ia \<or> i mod ia = i"
      using mod_pos_pos_trivial by force
    have "(1::int) \<le> 2 ^ LENGTH('b)"
      by simp
    then have "2 ^ LENGTH('b) + - (1::int) * ((- 1 + 2 ^ LENGTH('b)) mod 2 ^ len_of TYPE ('b)) = 1"
      using f3 f2 by blast
    then have f4: "- (1::int) + 2 ^ LENGTH('b) = (- 1 + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)"
      by linarith
    have f5: "x \<le> word_of_int (uint (word_of_int (- 1 + 2 ^ LENGTH('b))::'b word))"
      using a1 by force
    have f6: "2 ^ LENGTH('b) + - (1::int) = - 1 + 2 ^ LENGTH('b)"
      by force
    have f7: "- (1::int) * 1 = - 1"
      by auto
    have "\<forall>x0 x1. (x1::int) - x0 = x1 + - 1 * x0"
      by force
    then have "x \<le> 2 ^ LENGTH('b) - 1"
      using f7 f6 f5 f4 by (metis uint_word_of_int wi_homs(2) word_arith_wis(8) word_of_int_2p)
  }
  with assms show ?thesis
    unfolding ucast_def
    apply (subst word_ubin.eq_norm)
    apply (subst and_mask_bintr[symmetric])
    apply (subst and_mask_eq_iff_le_mask)
    apply (clarsimp simp: max_word_def mask_def)
    done
qed

lemma remdups_enum_upto:
  fixes s::"'a::len word"
  shows "remdups [s .e. e] = [s .e. e]"
  by simp

lemma card_enum_upto:
  fixes s::"'a::len word"
  shows "card (set [s .e. e]) = Suc (unat e) - unat s"
  by (subst List.card_set) (simp add: remdups_enum_upto)

lemma unat_mask:
  "unat (mask n :: 'a :: len word) = 2 ^ (min n (LENGTH('a))) - 1"
  apply (subst min.commute)
  apply (simp add: mask_def not_less min_def  split: if_split_asm)
  apply (intro conjI impI)
   apply (simp add: unat_sub_if_size)
   apply (simp add: power_overflow word_size)
  apply (simp add: unat_sub_if_size)
  done

lemma word_shiftr_lt:
  fixes w :: "'a::len word"
  shows "unat (w >> n) < (2 ^ (LENGTH('a) - n))"
  apply (subst shiftr_div_2n')
  by (metis nat_mod_lem nat_zero_less_power_iff power_mod_div
      word_unat.Rep_inverse word_unat.eq_norm zero_less_numeral)

lemma complement_nth_w2p:
  shows "n' < LENGTH('a) \<Longrightarrow> (~~ (2 ^ n :: 'a::len word)) !! n' = (n' \<noteq> n)"
  by (fastforce simp: word_ops_nth_size word_size nth_w2p)

lemma word_unat_and_lt:
  "unat x < n \<or> unat y < n \<Longrightarrow> unat (x && y) < n"
  by (meson le_less_trans word_and_le1 word_and_le2 word_le_nat_alt)

lemma word_unat_mask_lt:
  "m \<le> size w \<Longrightarrow> unat ((w::'a::len word) && mask m) < 2 ^ m"
  by (rule word_unat_and_lt) (simp add: unat_mask word_size)

lemma unat_shiftr_less_t2n:
  fixes x :: "'a :: len word"
  shows "unat x < 2 ^ (n + m) \<Longrightarrow> unat (x >> n) < 2 ^ m"
  by (simp add: shiftr_div_2n' power_add mult.commute td_gal_lt)

lemma le_or_mask:
  "w \<le> w' \<Longrightarrow> w || mask x \<le> w' || mask x"
  by (metis neg_mask_add_mask add.commute le_word_or1 mask_2pm1 neg_mask_mono_le word_plus_mono_left)

lemma le_shiftr1':
  "\<lbrakk> shiftr1 u \<le> shiftr1 v ; shiftr1 u \<noteq> shiftr1 v \<rbrakk> \<Longrightarrow> u \<le> v"
  apply (unfold word_le_def shiftr1_def word_ubin.eq_norm)
  apply (unfold bin_rest_trunc_i
                trans [OF bintrunc_bintrunc_l word_ubin.norm_Rep,
                          unfolded word_ubin.norm_Rep,
                       OF order_refl [THEN le_SucI]])
  apply (case_tac "uint u" rule: bin_exhaust)
  apply (case_tac "uint v" rule: bin_exhaust)
  by (smt Bit_def bin_rest_BIT)

lemma le_shiftr':
  "\<lbrakk> u >> n \<le> v >> n ; u >> n \<noteq> v >> n \<rbrakk> \<Longrightarrow> (u::'a::len0 word) \<le> v"
  apply (induct n; simp add: shiftr_def)
  apply (case_tac "(shiftr1 ^^ n) u = (shiftr1 ^^ n) v", simp)
  apply (fastforce dest: le_shiftr1')
  done

lemma word_log2_nth_same:
  "w \<noteq> 0 \<Longrightarrow> w !! word_log2 w"
  unfolding word_log2_def
  using nth_length_takeWhile[where P=Not and xs="to_bl w"]
  apply (simp add: word_clz_def word_size to_bl_nth)
  apply (fastforce simp: linorder_not_less eq_zero_set_bl
                   dest: takeWhile_take_has_property)
  done

lemma word_log2_nth_not_set:
  "\<lbrakk> word_log2 w < i ; i < size w \<rbrakk> \<Longrightarrow> \<not> w !! i"
  unfolding word_log2_def word_clz_def
  using takeWhile_take_has_property_nth[where P=Not and xs="to_bl w" and n="size w - Suc i"]
  by (fastforce simp add: to_bl_nth word_size)

lemma word_log2_highest:
  assumes a: "w !! i"
  shows "i \<le> word_log2 w"
proof -
  from a have "i < size w" by - (rule test_bit_size)
  with a show ?thesis
    by - (rule ccontr, simp add: word_log2_nth_not_set)
qed

lemma word_log2_max:
  "word_log2 w < size w"
  unfolding word_log2_def word_clz_def
  by simp

lemma word_clz_0[simp]:
  "word_clz (0::'a::len word) = LENGTH('a)"
  unfolding word_clz_def
  by (simp add: takeWhile_replicate)

lemma word_clz_minus_one[simp]:
  "word_clz (-1::'a::len word) = 0"
  unfolding word_clz_def
  by (simp add: max_word_bl[simplified max_word_minus] takeWhile_replicate)

lemma word_add_no_overflow:"(x::'a::len word) < max_word \<Longrightarrow> x < x + 1"
  using less_x_plus_1 order_less_le by blast

lemma lt_plus_1_le_word:
  fixes x :: "'a::len word"
  assumes bound:"n < unat (maxBound::'a word)"
  shows "x < 1 + of_nat n = (x \<le> of_nat n)"
  by (metis add.commute bound max_word_max word_Suc_leq word_not_le word_of_nat_less)

lemma unat_ucast_up_simp:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "unat (ucast x :: 'b::len word) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial; simp?)
  apply (rule lt2p_lem)
  apply (simp add: assms)
  done

lemma unat_ucast_less_no_overflow:
  "\<lbrakk>n < 2 ^ LENGTH('a); unat f < n\<rbrakk> \<Longrightarrow> (f::('a::len) word) < of_nat n"
  by (erule (1)  order_le_less_trans[OF _ of_nat_mono_maybe,rotated]) simp

lemma unat_ucast_less_no_overflow_simp:
  "n < 2 ^ LENGTH('a) \<Longrightarrow> (unat f < n) = ((f::('a::len) word) < of_nat n)"
  using unat_less_helper unat_ucast_less_no_overflow by blast

lemma unat_ucast_no_overflow_le:
  assumes no_overflow: "unat b < (2 :: nat) ^ LENGTH('a)"
  and upward_cast: "LENGTH('a) < LENGTH('b)"
  shows "(ucast (f::'a::len word) < (b :: 'b :: len word)) = (unat f < unat b)"
proof -
  have LR: "ucast f < b \<Longrightarrow> unat f < unat b"
    apply (rule unat_less_helper)
    apply (simp add:ucast_nat_def)
    apply (rule_tac 'b1 = 'b in  ucast_less_ucast[OF order.strict_implies_order, THEN iffD1])
     apply (rule upward_cast)
    apply (simp add: ucast_ucast_mask less_mask_eq word_less_nat_alt
                     unat_power_lower[OF upward_cast] no_overflow)
    done
  have RL: "unat f < unat b \<Longrightarrow> ucast f < b"
  proof-
    assume ineq: "unat f < unat b"
    have "ucast (f::'a::len word) < ((ucast (ucast b ::'a::len word)) :: 'b :: len word)"
      apply (simp add: ucast_less_ucast[OF order.strict_implies_order] upward_cast)
      apply (simp add: ucast_nat_def[symmetric])
      apply (rule unat_ucast_less_no_overflow[OF no_overflow ineq])
      done
    then show ?thesis
      apply (rule order_less_le_trans)
      apply (simp add:ucast_ucast_mask word_and_le2)
      done
  qed
  then show ?thesis by (simp add:RL LR iffI)
qed

lemmas ucast_up_mono = ucast_less_ucast[THEN iffD2]

(* casting a long word to a shorter word and casting back to the long word
   is equal to the original long word -- if the word is small enough.
  'l is the longer word.
  's is the shorter word.
*)
lemma bl_cast_long_short_long_ingoreLeadingZero_generic:
  "\<lbrakk> length (dropWhile Not (to_bl w)) \<le> LENGTH('s); LENGTH('s) \<le> LENGTH('l) \<rbrakk> \<Longrightarrow>
   (of_bl :: _ \<Rightarrow> 'l::len word) (to_bl ((of_bl::_ \<Rightarrow> 's::len word) (to_bl w))) = w"
  by (rule word_uint_eqI) (simp add: uint_of_bl_is_bl_to_bin uint_of_bl_is_bl_to_bin_drop)

(*
 Casting between longer and shorter word.
  'l is the longer word.
  's is the shorter word.
 For example: 'l::len word is 128 word (full ipv6 address)
              's::len word is 16 word (address piece of ipv6 address in colon-text-representation)
*)
corollary ucast_short_ucast_long_ingoreLeadingZero:
  "\<lbrakk> length (dropWhile Not (to_bl w)) \<le> LENGTH('s); LENGTH('s) \<le> LENGTH('l) \<rbrakk> \<Longrightarrow>
   (ucast:: 's::len word \<Rightarrow> 'l::len word) ((ucast:: 'l::len word \<Rightarrow> 's::len word) w) = w"
  apply (subst Word.ucast_bl)+
  apply (rule bl_cast_long_short_long_ingoreLeadingZero_generic; simp)
  done

lemma length_drop_mask:
  fixes w::"'a::len word"
  shows "length (dropWhile Not (to_bl (w AND mask n))) \<le> n"
proof -
  have "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
    for ls n by(subst takeWhile_append2) simp+
  then show ?thesis
    unfolding bl_and_mask by (simp add: dropWhile_eq_drop)
qed

lemma minus_one_word:
  "(-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  by simp

lemma mask_exceed:
  "n \<ge> LENGTH('a) \<Longrightarrow> (x::'a::len word) && ~~ (mask n) = 0"
  by (simp add: and_not_mask shiftr_eq_0)

lemma two_power_strict_part_mono:
  "strict_part_mono {..LENGTH('a) - 1} (\<lambda>x. (2 :: 'a :: len word) ^ x)"
proof -
  { fix n
    have "n < LENGTH('a) \<Longrightarrow> strict_part_mono {..n} (\<lambda>x. (2 :: 'a :: len word) ^ x)"
    proof (induct n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      from Suc.prems
      have "2 ^ n < (2 :: 'a :: len word) ^ Suc n"
        using power_strict_increasing unat_power_lower word_less_nat_alt by fastforce
      with Suc
      show ?case by (subst strict_part_mono_by_steps) simp
    qed
  }
  then show ?thesis by simp
qed

lemma word_shift_by_2:
  "x * 4 = (x::'a::len word) << 2"
  by (simp add: shiftl_t2n)

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

lemma le_2p_upper_bits:
  "\<lbrakk> (p::'a::len word) \<le> 2^n - 1; n < LENGTH('a) \<rbrakk> \<Longrightarrow>
  \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> p !! n'"
  by (subst upper_bits_unset_is_l2p; simp)

lemma le2p_bits_unset:
  "p \<le> 2 ^ n - 1 \<Longrightarrow> \<forall>n'\<ge>n. n' < LENGTH('a) \<longrightarrow> \<not> (p::'a::len word) !! n'"
  using upper_bits_unset_is_l2p [where p=p]
  by (cases "n < LENGTH('a)") auto

lemma ucast_less_shiftl_helper:
  "\<lbrakk> LENGTH('b) + 2 < LENGTH('a); 2 ^ (LENGTH('b) + 2) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 2) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma word_power_nonzero:
  "\<lbrakk> (x :: 'a::len word) < 2 ^ (LENGTH('a) - n); n < LENGTH('a); x \<noteq> 0 \<rbrakk>
  \<Longrightarrow> x * 2 ^ n \<noteq> 0"
  by (metis and_mask_eq_iff_shiftr_0 less_mask_eq p2_gt_0 semiring_normalization_rules(7)
            shiftl_shiftr_id shiftl_t2n)

lemma less_1_helper:
  "n \<le> m \<Longrightarrow> (n - 1 :: int) < m"
  by arith

lemma div_power_helper:
  "\<lbrakk> x \<le> y; y < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 ^ y - 1) div (2 ^ x :: 'a::len word) = 2 ^ (y - x) - 1"
  apply (rule word_uint.Rep_eqD)
  apply (simp only: uint_word_ariths uint_div uint_power_lower)
  apply (subst mod_pos_pos_trivial, fastforce, fastforce)+
  apply (subst mod_pos_pos_trivial)
    apply (simp add: le_diff_eq uint_2p_alt)
   apply (rule less_1_helper)
   apply (rule power_increasing; simp)
  apply (subst mod_pos_pos_trivial)
    apply (simp add: uint_2p_alt)
   apply (rule less_1_helper)
   apply (rule power_increasing; simp)
  apply (subst int_div_sub_1; simp add: uint_2p_alt)
  apply (subst power_0[symmetric])
  apply (simp add: uint_2p_alt le_imp_power_dvd power_sub_int)
  done


lemma word_add_power_off:
  fixes a :: "'a :: len word"
  assumes ak: "a < k"
  and kw: "k < 2 ^ (LENGTH('a) - m)"
  and mw: "m < LENGTH('a)"
  and off: "off < 2 ^ m"
  shows "(a * 2 ^ m) + off < k * 2 ^ m"
proof (cases "m = 0")
  case True
  then show ?thesis using off ak by simp
next
  case False

  from ak have ak1: "a + 1 \<le> k" by (rule inc_le)
  then have "(a + 1) * 2 ^ m \<noteq> 0"
    apply -
    apply (rule word_power_nonzero)
    apply (erule order_le_less_trans  [OF _ kw])
    apply (rule mw)
    apply (rule less_is_non_zero_p1 [OF ak])
    done
  then have "(a * 2 ^ m) + off < ((a + 1) * 2 ^ m)" using kw mw
    apply -
    apply (simp add: distrib_right)
    apply (rule word_plus_strict_mono_right [OF off])
    apply (rule is_aligned_no_overflow'')
    apply (rule is_aligned_mult_triv2)
    apply assumption
    done
  also have "\<dots> \<le> k * 2 ^ m" using ak1 mw kw False
    apply -
    apply (erule word_mult_le_mono1)
    apply (simp add: p2_gt_0)
    apply (simp add: word_less_nat_alt)
    apply (rule nat_less_power_trans2[simplified])
    apply (simp add: word_less_nat_alt)
    apply simp
    done
  finally show ?thesis .
qed

lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::'a::len word) n; i > 0; i < 2 ^ n; n < LENGTH('a)\<rbrakk> \<Longrightarrow>
   \<not> is_aligned (p + of_nat i) n"
  apply (erule is_aligned_add_not_aligned)
  unfolding is_aligned_def
  by (metis le_unat_uoi nat_dvd_not_less order_less_imp_le unat_power_lower)

lemma length_upto_enum_one:
  fixes x :: "'a :: len word"
  assumes lt1: "x < y" and lt2: "z < y" and lt3: "x \<le> z"
  shows "[x , y .e. z] = [x]"
  unfolding upto_enum_step_def
proof (subst upto_enum_red, subst if_not_P [OF leD [OF lt3]], clarsimp, rule conjI)
  show "unat ((z - x) div (y - x)) = 0"
  proof (subst unat_div, rule div_less)
    have syx: "unat (y - x) = unat y - unat x"
      by (rule unat_sub [OF order_less_imp_le]) fact
    moreover have "unat (z - x) = unat z - unat x"
      by (rule unat_sub) fact

    ultimately show "unat (z - x) < unat (y - x)"
      using lt2 lt3 unat_mono word_less_minus_mono_left by blast
  qed

  then show "(z - x) div (y - x) * (y - x) = 0"
    by (metis mult_zero_left unat_0 word_unat.Rep_eqD)
qed

lemma max_word_mask:
  "(max_word :: 'a::len word) = mask LENGTH('a)"
  unfolding mask_def by (metis max_word_eq shiftl_1)

lemmas mask_len_max = max_word_mask[symmetric]

lemma is_aligned_alignUp[simp]:
  "is_aligned (alignUp p n) n"
  by (simp add: alignUp_def complement_def is_aligned_mask mask_def word_bw_assocs)

lemma alignUp_le[simp]:
  "alignUp p n \<le> p + 2 ^ n - 1"
  unfolding alignUp_def by (rule word_and_le2)

lemma complement_mask:
  "complement (2 ^ n - 1) = ~~ (mask n)"
  unfolding complement_def mask_def by simp

lemma alignUp_idem:
  fixes a :: "'a::len word"
  assumes "is_aligned a n" "n < LENGTH('a)"
  shows "alignUp a n = a"
  using assms unfolding alignUp_def
  by (metis complement_mask is_aligned_add_helper p_assoc_help power_2_ge_iff)

lemma alignUp_not_aligned_eq:
  fixes a :: "'a :: len word"
  assumes al: "\<not> is_aligned a n"
  and     sz: "n < LENGTH('a)"
  shows   "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
proof -
  have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz) fact+

  then have um: "unat (a mod 2 ^ n - 1) div 2 ^ n = 0" using sz
    by (meson Euclidean_Division.div_eq_0_iff le_m1_iff_lt measure_unat order_less_trans
              unat_less_power word_less_sub_le word_mod_less_divisor)

  have "a + 2 ^ n - 1 = (a div 2 ^ n) * 2 ^ n + (a mod 2 ^ n) + 2 ^ n - 1"
    by (simp add: word_mod_div_equality)
  also have "\<dots> = (a mod 2 ^ n - 1) + (a div 2 ^ n + 1) * 2 ^ n"
    by (simp add: field_simps)
  finally show "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" using sz
    unfolding alignUp_def
    apply (subst complement_mask)
    apply (erule ssubst)
    apply (subst neg_mask_is_div)
    apply (simp add: word_arith_nat_div)
    apply (subst unat_word_ariths(1) unat_word_ariths(2))+
    apply (subst uno_simps)
    apply (subst unat_1)
    apply (subst mod_add_right_eq)
    apply simp
    apply (subst power_mod_div)
    apply (subst div_mult_self1)
     apply simp
    apply (subst um)
    apply simp
    apply (subst mod_mod_power)
    apply simp
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst mult_mod_left)
    apply (subst power_add [symmetric])
    apply simp
    apply (subst Abs_fnat_hom_1)
    apply (subst Abs_fnat_hom_add)
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst word_unat.Rep_inverse[symmetric], subst Abs_fnat_hom_mult)
    apply simp
    done
qed

lemma alignUp_ge:
  fixes a :: "'a :: len word"
  assumes sz: "n < LENGTH('a)"
  and nowrap: "alignUp a n \<noteq> 0"
  shows "a \<le> alignUp a n"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz
    by (subst alignUp_idem, simp_all)
next
  case False

  have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
    by (metis shiftr_div_2n' word_shiftr_lt)

  have"2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans nat_less_le)
  moreover have "2 ^ n * (unat a div 2 ^ n + 1) \<noteq> 2 ^ LENGTH('a)" using nowrap sz
    apply -
    apply (erule contrapos_nn)
    apply (subst alignUp_not_aligned_eq [OF False sz])
    apply (subst unat_arith_simps)
    apply (subst unat_word_ariths)
    apply (subst unat_word_ariths)
    apply simp
    apply (subst mult_mod_left)
    apply (simp add: unat_div field_simps power_add[symmetric] mod_mod_power min.absorb2)
    done
  ultimately have lt: "2 ^ n * (unat a div 2 ^ n + 1) < 2 ^ LENGTH('a)" by simp

  have "a = a div 2 ^ n * 2 ^ n + a mod 2 ^ n" by (rule word_mod_div_equality [symmetric])
  also have "\<dots> < (a div 2 ^ n + 1) * 2 ^ n" using sz lt
    apply (simp add: field_simps)
    apply (rule word_add_less_mono1)
    apply (rule word_mod_less_divisor)
    apply (simp add: word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (simp add: unat_div)
    done
  also have "\<dots> =  alignUp a n"
    by (rule alignUp_not_aligned_eq [symmetric]) fact+
  finally show ?thesis by (rule order_less_imp_le)
qed

lemma alignUp_le_greater_al:
  fixes x :: "'a :: len word"
  assumes le: "a \<le> x"
  and     sz: "n < LENGTH('a)"
  and     al: "is_aligned x n"
  shows   "alignUp a n \<le> x"
proof (cases "is_aligned a n")
  case True
  then show ?thesis using sz le by (simp add: alignUp_idem)
next
  case False

  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)

  from al obtain k where xk: "x = 2 ^ n * of_nat k" and kv: "k < 2 ^ (LENGTH('a) - n)"
    by (auto elim!: is_alignedE)

  then have kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ LENGTH('a)"
    using sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst mult.commute)
    apply simp
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have au: "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
    by (rule alignUp_not_aligned_eq) fact+
  also have "\<dots> \<le> of_nat k * 2 ^ n"
  proof (rule word_mult_le_mono1 [OF inc_le _ kn])
    show "a div 2 ^ n < of_nat k" using kv xk le sz anz
      by (simp add: alignUp_div_helper)

    show "(0:: 'a word) < 2 ^ n" using sz by (simp add: p2_gt_0 sz)
  qed

  finally show ?thesis using xk by (simp add: field_simps)
qed

lemma alignUp_is_aligned_nz:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and     ax: "a \<le> x"
  and     az: "a \<noteq> 0"
  shows   "alignUp (a::'a :: len word) n \<noteq> 0"
proof (cases "is_aligned a n")
  case True
  then have "alignUp a n = a" using sz by (simp add: alignUp_idem)
  then show ?thesis using az by simp
next
  case False
  then have anz: "a mod 2 ^ n \<noteq> 0"
    by (rule not_aligned_mod_nz)

  {
    assume asm: "alignUp a n = 0"

    have lt0: "unat a div 2 ^ n < 2 ^ (LENGTH('a) - n)" using sz
      by (metis shiftr_div_2n' word_shiftr_lt)

    have leq: "2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ LENGTH('a)" using sz
      by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right lt0 nat_le_power_trans
                order_less_imp_le)

    from al obtain k where  kv: "k < 2 ^ (LENGTH('a) - n)" and xk: "x = 2 ^ n * of_nat k"
      by (auto elim!: is_alignedE)

    then have "a div 2 ^ n < of_nat k" using ax sz anz
      by (rule alignUp_div_helper)

    then have r: "unat a div 2 ^ n < k" using sz
      by (metis unat_div unat_less_helper unat_power_lower)

    have "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
      by (rule alignUp_not_aligned_eq) fact+

    then have "\<dots> = 0" using asm by simp
    then have "2 ^ LENGTH('a) dvd 2 ^ n * (unat a div 2 ^ n + 1)"
      using sz by (simp add: unat_arith_simps ac_simps)
                  (simp add: unat_word_ariths mod_simps mod_eq_0_iff_dvd)
    with leq have "2 ^ n * (unat a div 2 ^ n + 1) = 2 ^ LENGTH('a)"
      by (force elim!: le_SucE)
    then have "unat a div 2 ^ n = 2 ^ LENGTH('a) div 2 ^ n - 1"
      by (metis (no_types, hide_lams) Groups.add_ac(2) add.right_neutral
                add_diff_cancel_left' div_le_dividend div_mult_self4 gr_implies_not0
                le_neq_implies_less power_eq_0_iff unat_def zero_neq_numeral)
    then have "unat a div 2 ^ n = 2 ^ (LENGTH('a) - n) - 1"
      using sz by (simp add: power_sub)
    then have "2 ^ (LENGTH('a) - n) - 1 < k" using r
      by simp
    then have False using kv by simp
  } then show ?thesis by clarsimp
qed

lemma alignUp_ar_helper:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < LENGTH('a)"
  and    sub: "{x..x + 2 ^ n - 1} \<subseteq> {a..b}"
  and    anz: "a \<noteq> 0"
  shows "a \<le> alignUp a n \<and> alignUp a n + 2 ^ n - 1 \<le> b"
proof
  from al have xl: "x \<le> x + 2 ^ n - 1" by (simp add: is_aligned_no_overflow)

  from xl sub have ax: "a \<le> x"
    by (clarsimp elim!: range_subset_lower [where x = x])

  show "a \<le> alignUp a n"
  proof (rule alignUp_ge)
    show "alignUp a n \<noteq> 0" using al sz ax anz
      by (rule alignUp_is_aligned_nz)
  qed fact+

  show "alignUp a n + 2 ^ n - 1 \<le> b"
  proof (rule order_trans)
    from xl show tp: "x + 2 ^ n - 1 \<le> b" using sub
      by (clarsimp elim!: range_subset_upper [where x = x])

    from ax have "alignUp a n \<le> x"
      by (rule alignUp_le_greater_al) fact+
    then have "alignUp a n + (2 ^ n - 1) \<le> x + (2 ^ n - 1)"
      using xl al is_aligned_no_overflow' olen_add_eqv word_plus_mcs_3 by blast
    then show "alignUp a n + 2 ^ n - 1 \<le> x + 2 ^ n - 1"
      by (simp add: field_simps)
  qed
qed

lemma alignUp_def2:
  "alignUp a sz = a + 2 ^ sz - 1 && ~~ (mask sz)"
  unfolding alignUp_def[unfolded complement_def]
  by (simp add:mask_def[symmetric,unfolded shiftl_t2n,simplified])

lemma mask_out_first_mask_some:
  "\<lbrakk> x && ~~ (mask n) = y; n \<le> m \<rbrakk> \<Longrightarrow> x && ~~ (mask m) = y && ~~ (mask m)"
  by word_eqI_solve

lemma gap_between_aligned:
  "\<lbrakk>a < (b :: 'a ::len word); is_aligned a n; is_aligned b n; n < LENGTH('a) \<rbrakk>
  \<Longrightarrow> a + (2^n - 1) < b"
  by (simp add: aligned_add_offset_less)

lemma mask_out_add_aligned:
  assumes al: "is_aligned p n"
  shows "p + (q && ~~ (mask n)) = (p + q) && ~~ (mask n)"
  using mask_add_aligned [OF al]
  by (simp add: mask_out_sub_mask)

lemma alignUp_def3:
  "alignUp a sz = 2^ sz + (a - 1 && ~~ (mask sz))"
  by (simp add: alignUp_def2 is_aligned_triv field_simps mask_out_add_aligned)

lemma  alignUp_plus:
  "is_aligned w us \<Longrightarrow> alignUp (w + a) us  = w + alignUp a us"
  by (clarsimp simp: alignUp_def2 mask_out_add_aligned field_simps)

lemma mask_lower_twice:
  "n \<le> m \<Longrightarrow> (x && ~~ (mask n)) && ~~ (mask m) = x && ~~ (mask m)"
  by word_eqI_solve

lemma mask_lower_twice2:
  "(a && ~~ (mask n)) && ~~ (mask m) = a && ~~ (mask (max n m))"
  by word_eqI_solve

lemma ucast_and_neg_mask:
  "ucast (x && ~~ (mask n)) = ucast x && ~~ (mask n)"
  by word_eqI_solve

lemma ucast_and_mask:
  "ucast (x && mask n) = ucast x && mask n"
  by word_eqI_solve

lemma ucast_mask_drop:
  "LENGTH('a :: len) \<le> n \<Longrightarrow> (ucast (x && mask n) :: 'a word) = ucast x"
  by word_eqI

lemma alignUp_distance:
  "alignUp (q :: 'a :: len word) sz - q \<le> mask sz"
  by (metis (no_types) add.commute add_diff_cancel_left alignUp_def2 diff_add_cancel
                       mask_2pm1 subtract_mask(2) word_and_le1 word_sub_le_iff)

lemma is_aligned_diff_neg_mask:
  "is_aligned p sz \<Longrightarrow> (p - q && ~~ (mask sz)) = (p - ((alignUp q sz) && ~~ (mask sz)))"
  apply (clarsimp simp only:word_and_le2 diff_conv_add_uminus)
  apply (subst mask_out_add_aligned[symmetric]; simp)
  apply (rule sum_to_zero)
  apply (subst add.commute)
  by (simp add: alignUp_distance and_mask_0_iff_le_mask is_aligned_neg_mask_eq mask_out_add_aligned)

lemma map_bits_rev_to_bl:
  "map ((!!) x) [0..<size x] = rev (to_bl x)"
  by (auto simp: list_eq_iff_nth_eq test_bit_bl word_size)

(* negating a mask which has been shifted to the very left *)
lemma NOT_mask_shifted_lenword:
  "~~ (mask len << (LENGTH('a) - len) ::'a::len word) = mask (LENGTH('a) - len)"
  by (rule Word.word_bool_alg.compl_unique, simp) word_eqI_solve

(* Comparisons between different word sizes. *)

lemma eq_ucast_ucast_eq:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x = ucast y \<Longrightarrow> ucast x = y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (simp add: is_down ucast_id ucast_ucast_a)

lemma le_ucast_ucast_le:
  "x \<le> ucast y \<Longrightarrow> ucast x \<le> y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (smt le_unat_uoi linorder_not_less order_less_imp_le ucast_nat_def unat_arith_simps(1))

lemma less_ucast_ucast_less:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> x < ucast y \<Longrightarrow> ucast x < y"
  for x :: "'a::len word" and y :: "'b::len word"
  by (metis ucast_nat_def unat_mono unat_ucast_up_simp word_of_nat_less)

lemma ucast_le_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> (ucast x \<le> (ucast y::'b::len word)) = (x \<le> y)"
  for x :: "'a::len word"
  by (simp add: unat_arith_simps(1) unat_ucast_up_simp)

lemmas ucast_up_mono_le = ucast_le_ucast[THEN iffD2]

lemma ucast_le_ucast_eq:
  fixes x y :: "'a::len word"
  assumes x: "x < 2 ^ n"
  assumes y: "y < 2 ^ n"
  assumes n: "n = LENGTH('b::len)"
  shows "(UCAST('a \<rightarrow> 'b) x \<le> UCAST('a \<rightarrow> 'b) y) = (x \<le> y)"
  apply (rule iffI)
   apply (cases "LENGTH('b) < LENGTH('a)")
    apply (subst less_mask_eq[OF x, symmetric])
    apply (subst less_mask_eq[OF y, symmetric])
    apply (unfold n)
    apply (subst ucast_ucast_mask[symmetric])+
    apply (simp add: ucast_le_ucast)+
  apply (erule ucast_mono_le[OF _ y[unfolded n]])
  done

lemma word_le_not_less:
  "((b::'a::len word) \<le> a) = (\<not>(a < b))"
  by fastforce

lemma ucast_or_distrib:
  fixes x :: "'a::len word"
  fixes y :: "'a::len word"
  shows "(ucast (x || y) :: ('b::len) word) = ucast x || ucast y"
  unfolding ucast_def Word.bitOR_word.abs_eq uint_or
  by blast

lemma shiftr_less:
  "(w::'a::len word) < k \<Longrightarrow> w >> n < k"
  by (metis div_le_dividend le_less_trans shiftr_div_2n' unat_arith_simps(2))

lemma word_and_notzeroD:
  "w && w' \<noteq> 0 \<Longrightarrow> w \<noteq> 0 \<and> w' \<noteq> 0"
  by auto

lemma word_clz_max:
  "word_clz w \<le> size (w::'a::len word)"
  unfolding word_clz_def
  by (metis length_takeWhile_le word_size_bl)

lemma word_clz_nonzero_max:
  fixes w :: "'a::len word"
  assumes nz: "w \<noteq> 0"
  shows "word_clz w < size (w::'a::len word)"
proof -
  {
    assume a: "word_clz w = size (w::'a::len word)"
    hence "length (takeWhile Not (to_bl w)) = length (to_bl w)"
      by (simp add: word_clz_def word_size)
    hence allj: "\<forall>j\<in>set(to_bl w). \<not> j"
      by (metis a length_takeWhile_less less_irrefl_nat word_clz_def)
    hence "to_bl w = replicate (length (to_bl w)) False"
      by (fastforce intro!: list_of_false)
    hence "w = 0"
      by (metis to_bl_0 word_bl.Rep_eqD word_bl_Rep')
    with nz have False by simp
  }
  thus ?thesis using word_clz_max
    by (fastforce intro: le_neq_trans)
qed

lemma unat_add_lem':
  "(unat x + unat y < 2 ^ LENGTH('a)) \<Longrightarrow>
    (unat (x + y :: 'a :: len word) = unat x + unat y)"
  by (subst unat_add_lem[symmetric], assumption)

lemma from_bool_eq_if':
  "((if P then 1 else 0) = from_bool Q) = (P = Q)"
  by (simp add: case_bool_If from_bool_def split: if_split)

lemma word_exists_nth:
  "(w::'a::len word) \<noteq> 0 \<Longrightarrow> \<exists>i. w !! i"
  using word_log2_nth_same by blast

lemma shiftr_le_0:
  "unat (w::'a::len word) < 2 ^ n \<Longrightarrow> w >> n = (0::'a::len word)"
  by (rule word_unat.Rep_eqD) (simp add: shiftr_div_2n')

lemma of_nat_shiftl:
  "(of_nat x << n) = (of_nat (x * 2 ^ n) :: ('a::len) word)"
proof -
  have "(of_nat x::'a word) << n = of_nat (2 ^ n) * of_nat x"
    using shiftl_t2n by (metis word_unat_power)
  thus ?thesis by simp
qed

lemma shiftl_1_not_0:
  "n < LENGTH('a) \<Longrightarrow> (1::'a::len word) << n \<noteq> 0"
  by (simp add: shiftl_t2n)

lemma max_word_not_0[simp]:
  "max_word \<noteq> 0"
  by (simp add: max_word_minus)

lemma ucast_zero_is_aligned:
  "UCAST('a::len \<rightarrow> 'b::len) w = 0 \<Longrightarrow> n \<le> LENGTH('b) \<Longrightarrow> is_aligned w n"
  by (clarsimp simp: is_aligned_mask word_eq_iff word_size nth_ucast)

lemma unat_ucast_eq_unat_and_mask:
  "unat (UCAST('b::len \<rightarrow> 'a::len) w) = unat (w && mask LENGTH('a))"
  proof -
    have "unat (UCAST('b \<rightarrow> 'a) w) = unat (UCAST('a \<rightarrow> 'b) (UCAST('b \<rightarrow> 'a) w))"
      by (cases "LENGTH('a) < LENGTH('b)"; simp add: is_down ucast_ucast_a unat_ucast_up_simp)
    thus ?thesis using ucast_ucast_mask by simp
  qed

lemma unat_max_word_pos[simp]: "0 < unat max_word"
  by (auto simp: unat_gt_0)


(* Miscellaneous conditional injectivity rules. *)

lemma mult_pow2_inj:
  assumes ws: "m + n \<le> LENGTH('a)"
  assumes le: "x \<le> mask m" "y \<le> mask m"
  assumes eq: "x * 2^n = y * (2^n::'a::len word)"
  shows "x = y"
proof (cases n)
  case 0 thus ?thesis using eq by simp
next
  case (Suc n')
  have m_lt: "m < LENGTH('a)" using Suc ws by simp
  have xylt: "x < 2^m" "y < 2^m" using le m_lt unfolding mask_2pm1 by auto
  have lenm: "n \<le> LENGTH('a) - m" using ws by simp
  show ?thesis
    using eq xylt
    apply (fold shiftl_t2n[where n=n, simplified mult.commute])
    apply (simp only: word_bl.Rep_inject[symmetric] bl_shiftl)
    apply (erule ssubst[OF less_is_drop_replicate])+
    apply (clarsimp elim!: drop_eq_mono[OF lenm])
    done
qed

lemma word_of_nat_inj:
  assumes bounded: "x < 2 ^ LENGTH('a)" "y < 2 ^ LENGTH('a)"
  assumes of_nats: "of_nat x = (of_nat y :: 'a::len word)"
  shows "x = y"
  by (rule contrapos_pp[OF of_nats]; cases "x < y"; cases "y < x")
     (auto dest: bounded[THEN of_nat_mono_maybe])

(* Sign extension from bit n. *)

lemma sign_extend_bitwise_if:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> (if i < e then w !! i else w !! e)"
  by (simp add: sign_extend_def neg_mask_test_bit word_size)

lemma sign_extend_bitwise_disj:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> i \<le> e \<and> w !! i \<or> e \<le> i \<and> w !! e"
  by (auto simp: sign_extend_bitwise_if)

lemma sign_extend_bitwise_cases:
  "i < size w \<Longrightarrow> sign_extend e w !! i \<longleftrightarrow> (i \<le> e \<longrightarrow> w !! i) \<and> (e \<le> i \<longrightarrow> w !! e)"
  by (auto simp: sign_extend_bitwise_if)

lemmas sign_extend_bitwise_if'[word_eqI_simps] = sign_extend_bitwise_if[simplified word_size]
lemmas sign_extend_bitwise_disj' = sign_extend_bitwise_disj[simplified word_size]
lemmas sign_extend_bitwise_cases' = sign_extend_bitwise_cases[simplified word_size]

(* Often, it is easier to reason about an operation which does not overwrite
   the bit which determines which mask operation to apply. *)
lemma sign_extend_def':
  "sign_extend n w = (if w !! n then w || ~~ (mask (Suc n)) else w && mask (Suc n))"
  by word_eqI (auto dest: less_antisym)

lemma sign_extended_sign_extend:
  "sign_extended n (sign_extend n w)"
  by (clarsimp simp: sign_extended_def word_size sign_extend_bitwise_if')

lemma sign_extended_iff_sign_extend:
  "sign_extended n w \<longleftrightarrow> sign_extend n w = w"
  apply (rule iffI)
   apply (word_eqI, rename_tac i)
   apply (case_tac "n < i"; simp add: sign_extended_def word_size)
  apply (erule subst, rule sign_extended_sign_extend)
  done

lemma sign_extended_weaken:
  "sign_extended n w \<Longrightarrow> n \<le> m \<Longrightarrow> sign_extended m w"
  unfolding sign_extended_def by (cases "n < m") auto

lemma sign_extend_sign_extend_eq:
  "sign_extend m (sign_extend n w) = sign_extend (min m n) w"
  by word_eqI

lemma sign_extended_high_bits:
  "\<lbrakk> sign_extended e p; j < size p; e \<le> i; i < j \<rbrakk> \<Longrightarrow> p !! i = p !! j"
  by (drule (1) sign_extended_weaken; simp add: sign_extended_def)

lemma sign_extend_eq:
  "w && mask (Suc n) = v && mask (Suc n) \<Longrightarrow> sign_extend n w = sign_extend n v"
  by word_eqI_solve

lemma sign_extended_add:
  assumes p: "is_aligned p n"
  assumes f: "f < 2 ^ n"
  assumes e: "n \<le> e"
  assumes "sign_extended e p"
  shows "sign_extended e (p + f)"
proof (cases "e < size p")
  case True
  note and_or = is_aligned_add_or[OF p f]
  have "\<not> f !! e"
    using True e less_2p_is_upper_bits_unset[THEN iffD1, OF f]
    by (fastforce simp: word_size)
  hence i: "(p + f) !! e = p !! e"
    by (simp add: and_or)
  have fm: "f && mask e = f"
    by (fastforce intro: subst[where P="\<lambda>f. f && mask e = f", OF less_mask_eq[OF f]]
                  simp: mask_twice e)
  show ?thesis
    using assms
     apply (simp add: sign_extended_iff_sign_extend sign_extend_def i)
     apply (simp add: and_or word_bw_comms[of p f])
     apply (clarsimp simp: word_ao_dist fm word_bw_assocs split: if_splits)
    done
next
  case False thus ?thesis
    by (simp add: sign_extended_def word_size)
qed

lemma sign_extended_neq_mask:
  "\<lbrakk>sign_extended n ptr; m \<le> n\<rbrakk> \<Longrightarrow> sign_extended n (ptr && ~~ (mask m))"
  by (fastforce simp: sign_extended_def word_size neg_mask_test_bit)

(* Uints *)

lemma uints_mono_iff: "uints l \<subseteq> uints m \<longleftrightarrow> l \<le> m"
  using power_increasing_iff[of "2::int" l m]
  apply (auto simp: uints_num subset_iff simp del: power_increasing_iff)
  by (meson less_irrefl not_less zle2p)

lemmas uints_monoI = uints_mono_iff[THEN iffD2]

lemma Bit_in_uints_Suc: "w BIT c \<in> uints (Suc m)" if "w \<in> uints m"
  using that
  by (auto simp: uints_num Bit_def)

lemma Bit_in_uintsI: "w BIT c \<in> uints m" if "w \<in> uints (m - 1)" "m > 0"
  using Bit_in_uints_Suc[OF that(1)] that(2)
  by auto

lemma bin_cat_in_uintsI: "bin_cat a n b \<in> uints m" if "a \<in> uints l" "m \<ge> l + n"
  using that
proof (induction n arbitrary: b m)
  case 0
  then have "uints l \<subseteq> uints m"
    by (intro uints_monoI) auto
  then show ?case using 0 by auto
next
  case (Suc n)
  then show ?case
    by (auto intro!: Bit_in_uintsI)
qed

lemma bin_cat_cong: "bin_cat a n b = bin_cat c m d"
  if "n = m" "a = c" "bintrunc m b = bintrunc m d"
  using that(3) unfolding that(1,2)
proof (induction m arbitrary: b d)
  case (Suc m)
  show ?case
    using Suc.prems by (auto intro: Suc.IH)
qed simp

lemma bin_cat_eqD1: "bin_cat a n b = bin_cat c n d \<Longrightarrow> a = c"
  by (induction n arbitrary: b d) auto

lemma bin_cat_eqD2: "bin_cat a n b = bin_cat c n d \<Longrightarrow> bintrunc n b = bintrunc n d"
  by (induction n arbitrary: b d) auto

lemma bin_cat_inj: "(bin_cat a n b) = bin_cat c n d \<longleftrightarrow> a = c \<and> bintrunc n b = bintrunc n d"
  by (auto intro: bin_cat_cong bin_cat_eqD1 bin_cat_eqD2)

lemma word_of_int_bin_cat_eq_iff:
  "(word_of_int (bin_cat (uint a) LENGTH('b) (uint b))::'c::len0 word) =
  word_of_int (bin_cat (uint c) LENGTH('b) (uint d)) \<longleftrightarrow> b = d \<and> a = c"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len0 word" and b::"'b::len0 word"
  by (subst word_uint.Abs_inject)
     (auto simp: bin_cat_inj intro!: that bin_cat_in_uintsI)

lemma word_cat_inj: "(word_cat a b::'c::len0 word) = word_cat c d \<longleftrightarrow> a = c \<and> b = d"
  if "LENGTH('a) + LENGTH('b) \<le> LENGTH('c)"
  for a::"'a::len0 word" and b::"'b::len0 word"
  by (auto simp: word_cat_def word_uint.Abs_inject word_of_int_bin_cat_eq_iff that)

lemma p2_eq_1: "2 ^ n = (1::'a::len word) \<longleftrightarrow> n = 0"
proof -
  have "2 ^ n = (1::'a word) \<Longrightarrow> n = 0"
    by (metis One_nat_def not_less one_less_numeral_iff p2_eq_0 p2_gt_0 power_0 power_0
        power_inject_exp semiring_norm(76) unat_power_lower zero_neq_one)
  then show ?thesis by auto
qed

(* usually: x,y = (len_of TYPE ('a)) *)
lemma bitmagic_zeroLast_leq_or1Last:
  "(a::('a::len) word) AND (mask len << x - len) \<le> a OR mask (y - len)"
  by (meson le_word_or2 order_trans word_and_le2)


lemma zero_base_lsb_imp_set_eq_as_bit_operation:
  fixes base ::"'a::len word"
  assumes valid_prefix: "mask (LENGTH('a) - len) AND base = 0"
  shows "(base = NOT (mask (LENGTH('a) - len)) AND a) \<longleftrightarrow>
         (a \<in> {base .. base OR mask (LENGTH('a) - len)})"
proof
  have helper3: "x OR y = x OR y AND NOT x" for x y ::"'a::len word" by (simp add: word_oa_dist2)
  from assms show "base = NOT (mask (LENGTH('a) - len)) AND a \<Longrightarrow>
                    a \<in> {base..base OR mask (LENGTH('a) - len)}"
    apply(simp add: word_and_le1)
    apply(metis helper3 le_word_or2 word_bw_comms(1) word_bw_comms(2))
  done
next
  assume "a \<in> {base..base OR mask (LENGTH('a) - len)}"
  hence a: "base \<le> a \<and> a \<le> base OR mask (LENGTH('a) - len)" by simp
  show "base = NOT (mask (LENGTH('a) - len)) AND a"
  proof -
    have f2: "\<forall>x\<^sub>0. base AND NOT (mask x\<^sub>0) \<le> a AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f3: "\<forall>x\<^sub>0. a AND NOT (mask x\<^sub>0) \<le> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>0)"
      using a neg_mask_mono_le by blast
    have f4: "base = base AND NOT (mask (LENGTH('a) - len))"
      using valid_prefix by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f5: "\<forall>x\<^sub>6. (base OR x\<^sub>6) AND NOT (mask (LENGTH('a) - len)) =
                      base OR x\<^sub>6 AND NOT (mask (LENGTH('a) - len))"
      using word_ao_dist by (metis)
    have f6: "\<forall>x\<^sub>2 x\<^sub>3. a AND NOT (mask x\<^sub>2) \<le> x\<^sub>3 \<or>
                      \<not> (base OR mask (LENGTH('a) - len)) AND NOT (mask x\<^sub>2) \<le> x\<^sub>3"
      using f3 dual_order.trans by auto
    have "base = (base OR mask (LENGTH('a) - len)) AND NOT (mask (LENGTH('a) - len))"
      using f5 by auto
    hence "base = a AND NOT (mask (LENGTH('a) - len))"
      using f2 f4 f6 by (metis eq_iff)
    thus "base = NOT (mask (LENGTH('a) - len)) AND a"
      by (metis word_bw_comms(1))
  qed
qed

lemma unat_minus_one_word:
  "unat (-1 :: 'a :: len word) = 2 ^ LENGTH('a) - 1"
  by (subst minus_one_word)
     (subst unat_sub_if', clarsimp)

lemma of_nat_eq_signed_scast:
  "(of_nat x = (y :: ('a::len) signed word))
   = (of_nat x = (scast y :: 'a word))"
  by (metis scast_of_nat scast_scast_id(2))

lemma word_ctz_le:
  "word_ctz (w :: ('a::len word)) \<le> LENGTH('a)"
  apply (clarsimp simp: word_ctz_def)
  apply (rule nat_le_Suc_less_imp[where y="LENGTH('a) + 1" , simplified])
  apply (rule order_le_less_trans[OF List.length_takeWhile_le])
  apply simp
  done

lemma word_ctz_less:
  "w \<noteq> 0 \<Longrightarrow> word_ctz (w :: ('a::len word)) < LENGTH('a)"
  apply (clarsimp simp: word_ctz_def eq_zero_set_bl)
  apply (rule order_less_le_trans[OF length_takeWhile_less])
   apply fastforce+
  done

lemma word_ctz_not_minus_1:
  "1 < LENGTH('a) \<Longrightarrow> of_nat (word_ctz (w :: 'a :: len word)) \<noteq> (- 1 :: 'a::len word)"
  by (metis (mono_tags) One_nat_def add.right_neutral add_Suc_right le_diff_conv le_less_trans
                        n_less_equal_power_2 not_le suc_le_pow_2 unat_minus_one_word unat_of_nat_len
                        word_ctz_le)

lemma word_aligned_add_no_wrap_bounded:
  "\<lbrakk> w + 2^n \<le> x; w + 2^n \<noteq> 0; is_aligned w n \<rbrakk> \<Longrightarrow> (w::'a::len word) < x"
  by (blast dest: is_aligned_no_overflow le_less_trans word_leq_le_minus_one)

lemma mask_Suc:
  "mask (Suc n) = 2^n + mask n"
  by (simp add: mask_def)

lemma is_aligned_no_overflow_mask:
  "is_aligned x n \<Longrightarrow> x \<le> x + mask n"
  by (simp add: mask_def) (erule is_aligned_no_overflow')

lemma is_aligned_mask_offset_unat:
  fixes off :: "('a::len) word"
  and     x :: "'a word"
  assumes al: "is_aligned x sz"
  and   offv: "off \<le> mask sz"
  shows  "unat x + unat off < 2 ^ LENGTH('a)"
proof cases
  assume szv: "sz < LENGTH('a)"
  from al obtain k where xv: "x = 2 ^ sz * (of_nat k)"
    and kl: "k < 2 ^ (LENGTH('a) - sz)"
    by (auto elim: is_alignedE)

  from offv szv have offv': "unat off < 2 ^ sz"
    by (simp add: mask_2pm1 unat_less_power)

  show ?thesis using szv
    using al is_aligned_no_wrap''' offv' by blast
next
  assume "\<not> sz < LENGTH('a)"
  with al have "x = 0" by - word_eqI
  thus ?thesis by simp
qed

lemma of_bl_max:
  "(of_bl xs :: 'a::len word) \<le> mask (length xs)"
  apply (induct xs)
   apply simp
  apply (simp add: of_bl_Cons mask_Suc)
  apply (rule conjI; clarsimp)
   apply (erule word_plus_mono_right)
   apply (rule is_aligned_no_overflow_mask)
   apply (rule is_aligned_triv)
  apply (simp add: word_le_nat_alt)
  apply (subst unat_add_lem')
   apply (rule is_aligned_mask_offset_unat)
    apply (rule is_aligned_triv)
   apply (simp add: mask_def)
  apply simp
  done

lemma mask_over_length:
  "LENGTH('a) \<le> n \<Longrightarrow> mask n = (-1::'a::len word)"
  by (simp add: mask_def)

lemma is_aligned_over_length:
  "\<lbrakk> is_aligned p n; LENGTH('a) \<le> n \<rbrakk> \<Longrightarrow> (p::'a::len word) = 0"
  by (simp add: is_aligned_mask mask_over_length)

lemma Suc_2p_unat_mask:
  "n < LENGTH('a) \<Longrightarrow> Suc (2 ^ n * k + unat (mask n :: 'a::len word)) = 2 ^ n * (k+1)"
  by (simp add: unat_mask)

lemma is_aligned_add_step_le:
  "\<lbrakk> is_aligned (a::'a::len word) n; is_aligned b n; a < b; b \<le> a + mask n \<rbrakk> \<Longrightarrow> False"
  apply (simp flip: not_le)
  apply (erule notE)
  apply (cases "LENGTH('a) \<le> n")
   apply (drule (1) is_aligned_over_length)+
   apply (drule mask_over_length)
   apply clarsimp
  apply (clarsimp simp: word_le_nat_alt not_less)
  apply (subst (asm) unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)
  apply (clarsimp simp: is_aligned_def dvd_def word_le_nat_alt)
  apply (drule le_imp_less_Suc)
  apply (simp add: Suc_2p_unat_mask)
  by (metis Groups.mult_ac(2) Suc_leI linorder_not_less mult_le_mono order_refl times_nat.simps(2))

lemma power_2_mult_step_le:
  "\<lbrakk>n' \<le> n; 2 ^ n' * k' < 2 ^ n * k\<rbrakk> \<Longrightarrow> 2 ^ n' * (k' + 1) \<le> 2 ^ n * (k::nat)"
  apply (cases "n'=n", simp)
   apply (metis Suc_leI le_refl mult_Suc_right mult_le_mono semiring_normalization_rules(7))
  apply (drule (1) le_neq_trans)
  apply clarsimp
  apply (subgoal_tac "\<exists>m. n = n' + m")
   prefer 2
   apply (simp add: le_Suc_ex)
  apply (clarsimp simp: power_add)
  by (metis Suc_leI mult.assoc mult_Suc_right nat_mult_le_cancel_disj)

lemma aligned_mask_step:
  "\<lbrakk> n' \<le> n; p' \<le> p + mask n; is_aligned p n; is_aligned p' n' \<rbrakk> \<Longrightarrow>
   (p'::'a::len word) + mask n' \<le> p + mask n"
  apply (cases "LENGTH('a) \<le> n")
   apply (frule (1) is_aligned_over_length)
   apply (drule mask_over_length)
   apply clarsimp
  apply (simp add: not_le)
  apply (simp add: word_le_nat_alt unat_plus_simple)
  apply (subst unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)+
  apply (subst (asm) unat_plus_simple[THEN iffD1], erule is_aligned_no_overflow_mask)
  apply (clarsimp simp: is_aligned_def dvd_def)
  apply (rename_tac k k')
  apply (thin_tac "unat p = x" for p x)+
  apply (subst Suc_le_mono[symmetric])
  apply (simp only: Suc_2p_unat_mask)
  apply (drule le_imp_less_Suc, subst (asm) Suc_2p_unat_mask, assumption)
  apply (erule (1) power_2_mult_step_le)
  done

lemma mask_mono:
  "sz' \<le> sz \<Longrightarrow> mask sz' \<le> (mask sz :: 'a::len word)"
  by (simp add: le_mask_iff shiftr_mask_le)

lemma aligned_mask_disjoint:
  "\<lbrakk> is_aligned (a :: 'a :: len word) n; b \<le> mask n \<rbrakk> \<Longrightarrow> a && b = 0"
  by word_eqI_solve

lemma word_and_or_mask_aligned:
  "\<lbrakk> is_aligned a n; b \<le> mask n \<rbrakk> \<Longrightarrow> a + b = a || b"
  by (simp add: aligned_mask_disjoint word_plus_and_or_coroll)

lemmas word_and_or_mask_aligned2 =
  word_and_or_mask_aligned[where a=b and b=a for a b,
                           simplified add.commute word_bool_alg.disj.commute]

lemma is_aligned_ucastI:
  "is_aligned w n \<Longrightarrow> is_aligned (ucast w) n"
  by (clarsimp simp: word_eqI_simps)

lemma ucast_le_maskI:
  "a \<le> mask n \<Longrightarrow> UCAST('a::len \<rightarrow> 'b::len) a \<le> mask n"
  by (metis and_mask_eq_iff_le_mask ucast_and_mask)

lemma ucast_add_mask_aligned:
  "\<lbrakk> a \<le> mask n; is_aligned b n \<rbrakk> \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) (a + b) = ucast a + ucast b"
  by (metis is_aligned_ucastI ucast_le_maskI ucast_or_distrib word_and_or_mask_aligned2)

lemma ucast_shiftl:
  "LENGTH('b) \<le> LENGTH ('a) \<Longrightarrow> UCAST ('a::len \<rightarrow> 'b::len) x << n = ucast (x << n)"
  by word_eqI_solve

lemma ucast_leq_mask:
  "LENGTH('a) \<le> n \<Longrightarrow> ucast (x::'a::len0 word) \<le> mask n"
  by (clarsimp simp: le_mask_high_bits word_size nth_ucast)

lemma shiftl_inj:
  "\<lbrakk> x << n = y << n; x \<le> mask (LENGTH('a)-n); y \<le> mask (LENGTH('a)-n) \<rbrakk> \<Longrightarrow>
   x = (y :: 'a :: len word)"
  apply word_eqI
  apply (rename_tac n')
  apply (case_tac "LENGTH('a) - n \<le> n'", simp)
  by (metis add.commute add.right_neutral diff_add_inverse le_diff_conv linorder_not_less zero_order(1))

lemma distinct_word_add_ucast_shift_inj:
  "\<lbrakk> p + (UCAST('a::len \<rightarrow> 'b::len) off << n) = p' + (ucast off' << n);
     is_aligned p n'; is_aligned p' n'; n' = n + LENGTH('a); n' < LENGTH('b) \<rbrakk>
   \<Longrightarrow> p' = p \<and> off' = off"
  apply (simp add: word_and_or_mask_aligned le_mask_shiftl_le_mask[where n="LENGTH('a)"]
                   ucast_leq_mask)
  apply (simp add: is_aligned_nth)
  apply (rule conjI; word_eqI)
   apply (metis add.commute test_bit_conj_lt diff_add_inverse le_diff_conv nat_less_le)
  apply (rename_tac i)
  apply (erule_tac x="i+n" in allE)
  apply simp
  done

lemma aligned_add_mask_lessD:
  "\<lbrakk> x + mask n < y; is_aligned x n \<rbrakk> \<Longrightarrow> x < y" for y::"'a::len word"
  by (metis is_aligned_no_overflow' mask_2pm1 order_le_less_trans)

lemma aligned_add_mask_less_eq:
  "\<lbrakk> is_aligned x n; is_aligned y n;  n < LENGTH('a) \<rbrakk> \<Longrightarrow> (x + mask n < y) = (x < y)"
  for y::"'a::len word"
  using aligned_add_mask_lessD is_aligned_add_step_le word_le_not_less by blast

lemma word_upto_Nil:
  "y < x \<Longrightarrow> [x .e. y ::'a::len word] = []"
  by (simp add: upto_enum_red not_le word_less_nat_alt)

lemma word_enum_decomp_elem:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y"
proof -
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    using assms by (auto dest: arg_cong[where f=set])
  then show ?thesis by auto
qed

lemma max_word_not_less[simp]:
   "\<not> max_word < x"
  by (simp add: not_less)

lemma word_enum_prefix:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> as = (if x < a then [x .e. a - 1] else [])"
  apply (induct as arbitrary: x; clarsimp)
   apply (case_tac "x < y")
    prefer 2
    apply (case_tac "x = y", simp)
    apply (simp add: not_less)
    apply (drule (1) dual_order.not_eq_order_implies_strict)
    apply (simp add: word_upto_Nil)
   apply (simp add: word_upto_Cons_eq)
  apply (case_tac "x < y")
   prefer 2
   apply (case_tac "x = y", simp)
   apply (simp add: not_less)
   apply (drule (1) dual_order.not_eq_order_implies_strict)
   apply (simp add: word_upto_Nil)
  apply (clarsimp simp: word_upto_Cons_eq)
  apply (frule word_enum_decomp_elem)
  apply clarsimp
  apply (rule conjI)
   prefer 2
   apply (subst word_Suc_le[symmetric]; clarsimp)
  apply (drule meta_spec)
  apply (drule (1) meta_mp)
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (subst (2) word_upto_Cons_eq)
   apply unat_arith
  apply simp
  done

lemma word_enum_decomp_set:
  "[x .e. (y ::'a::len word)] = as @ a # bs \<Longrightarrow> a \<notin> set as"
  by (metis distinct_append distinct_enum_upto' not_distinct_conv_prefix)

lemma word_enum_decomp:
  assumes "[x .e. (y ::'a::len word)] = as @ a # bs"
  shows "x \<le> a \<and> a \<le> y \<and> a \<notin> set as \<and> (\<forall>z \<in> set as. x \<le> z \<and> z \<le> y)"
proof -
  from assms
  have "set as \<subseteq> set [x .e. y] \<and> a \<in> set [x .e. y]"
    by (auto dest: arg_cong[where f=set])
  with word_enum_decomp_set[OF assms]
  show ?thesis by auto
qed

lemma of_nat_unat_le_mask_ucast:
  "\<lbrakk>of_nat (unat t) = w; t \<le> mask LENGTH('a)\<rbrakk> \<Longrightarrow> t = UCAST('a::len \<rightarrow> 'b::len) w"
  by (clarsimp simp: ucast_nat_def ucast_ucast_mask simp flip: and_mask_eq_iff_le_mask)

lemma fold_eq_0_to_bool:
  "(v = 0) = (\<not> to_bool v)"
  by (simp add: to_bool_def)

lemma less_diff_gt0:
  "a < b \<Longrightarrow> (0 :: 'a :: len word) < b - a"
  by unat_arith

lemma unat_plus_gt:
  "unat ((a :: 'a :: len word) + b) \<le> unat a + unat b"
  by (clarsimp simp: unat_plus_if_size)

lemma const_less:
  "\<lbrakk> (a :: 'a :: len word) - 1 < b; a \<noteq> b \<rbrakk> \<Longrightarrow> a < b"
  by (metis less_1_simp word_le_less_eq)

lemma add_mult_aligned_neg_mask:
  "m && (2 ^ n - 1) = 0 \<Longrightarrow> (x + y * m) && ~~(mask n) = (x && ~~(mask n)) + y * m"
  by (metis Groups.add_ac(2) is_aligned_mask mask_def mask_eqs(5) mask_out_add_aligned
            mult_zero_right shiftl_1 word_bw_comms(1) word_log_esimps(1))

lemma unat_of_nat_minus_1:
  "\<lbrakk> n < 2 ^ LENGTH('a); n \<noteq> 0 \<rbrakk> \<Longrightarrow> unat ((of_nat n:: 'a :: len word) - 1) = n - 1"
  by (simp add: unat_eq_of_nat)

lemma word_eq_zeroI:
  "a \<le> a - 1 \<Longrightarrow> a = 0" for a :: "'a :: len word"
  by (simp add: word_must_wrap)

lemma word_add_format:
  "(-1 :: 'a :: len  word) + b + c = b + (c - 1)"
  by simp

lemma upto_enum_word_nth:
  "\<lbrakk> i \<le> j; k \<le> unat (j - i) \<rbrakk> \<Longrightarrow> [i .e. j] ! k = i + of_nat k"
  apply (clarsimp simp: upto_enum_def nth_append)
  apply (clarsimp simp: word_le_nat_alt[symmetric])
  apply (rule conjI, clarsimp)
   apply (subst toEnum_of_nat, unat_arith)
   apply unat_arith
  apply (clarsimp simp: not_less unat_sub[symmetric])
  apply unat_arith
  done

lemma upto_enum_step_nth:
  "\<lbrakk> a \<le> c; n \<le> unat ((c - a) div (b - a)) \<rbrakk>
   \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  by (clarsimp simp: upto_enum_step_def not_less[symmetric] upto_enum_word_nth)

lemma upto_enum_inc_1_len:
  "a < - 1 \<Longrightarrow> [(0 :: 'a :: len word) .e. 1 + a] = [0 .e. a] @ [1 + a]"
  apply (simp add: upto_enum_word)
  apply (subgoal_tac "unat (1+a) = 1 + unat a")
   apply simp
  apply (subst unat_plus_simple[THEN iffD1])
   apply (metis add.commute no_plus_overflow_neg olen_add_eqv)
  apply unat_arith
  done

lemma neg_mask_add:
  "y && mask n = 0 \<Longrightarrow> x + y && ~~(mask n) = (x && ~~(mask n)) + y"
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma shiftr_shiftl_shiftr[simp]:
  "(x :: 'a :: len word)  >> a << a >> a = x >> a"
  by word_eqI_solve

lemma add_right_shift:
  "\<lbrakk> x && mask n = 0; y && mask n = 0; x \<le> x + y \<rbrakk>
   \<Longrightarrow> (x + y :: ('a :: len) word) >> n = (x >> n) + (y >> n)"
  apply (simp add: no_olen_add_nat is_aligned_mask[symmetric])
  apply (simp add: unat_arith_simps shiftr_div_2n' split del: if_split)
  apply (subst if_P)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: add_mono)
  apply (simp add: shiftr_div_2n' is_aligned_def)
  done

lemma sub_right_shift:
  "\<lbrakk> x && mask n = 0; y && mask n = 0; y \<le> x \<rbrakk>
   \<Longrightarrow> (x - y) >> n = (x >> n :: 'a :: len word) - (y >> n)"
  using add_right_shift[where x="x - y" and y=y and n=n]
  by (simp add: aligned_sub_aligned is_aligned_mask[symmetric] word_sub_le)

lemma and_and_mask_simple:
  "y && mask n = mask n \<Longrightarrow> (x && y) && mask n = x && mask n"
  by (simp add: word_bool_alg.conj.assoc)

lemma and_and_mask_simple_not:
  "y && mask n = 0 \<Longrightarrow> (x && y) && mask n = 0"
  by (simp add: word_bool_alg.conj.assoc)

lemma word_and_le':
  "b \<le> c \<Longrightarrow> (a :: 'a :: len word) && b \<le> c"
  by (metis word_and_le1 order_trans)

lemma word_and_less':
  "b < c \<Longrightarrow> (a :: 'a :: len word) && b < c"
  by (metis word_and_le1 xtr7)

lemma shiftr_w2p:
  "x < LENGTH('a) \<Longrightarrow> 2 ^ x = (2 ^ (LENGTH('a) - 1) >> (LENGTH('a) - 1 - x) :: 'a :: len word)"
  by word_eqI_solve

lemma t2p_shiftr:
  "\<lbrakk> b \<le> a; a < LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ a >> b = 2 ^ (a - b)"
  by word_eqI_solve

lemma scast_1[simp]:
  "scast (1 :: 'a :: len signed word) = (1 :: 'a word)"
  by simp

lemma ucast_ucast_mask_eq:
  "\<lbrakk> UCAST('a::len \<rightarrow> 'b::len) x = y; x && mask LENGTH('b) = x \<rbrakk> \<Longrightarrow> x = ucast y"
  by word_eqI_solve

lemma ucast_up_eq:
  "\<lbrakk> ucast x = (ucast y::'b::len word); LENGTH('a) \<le> LENGTH ('b) \<rbrakk>
   \<Longrightarrow> ucast x = (ucast y::'a::len word)"
  by word_eqI_solve

lemma ucast_up_neq:
  "\<lbrakk> ucast x \<noteq> (ucast y::'b::len word); LENGTH('b) \<le> LENGTH ('a) \<rbrakk>
   \<Longrightarrow> ucast x \<noteq> (ucast y::'a::len word)"
  by (fastforce dest: ucast_up_eq)

lemma mask_AND_less_0:
  "\<lbrakk> x && mask n = 0; m \<le> n \<rbrakk> \<Longrightarrow> x && mask m = 0"
  by (metis mask_twice2 word_and_notzeroD)

lemma mask_len_id [simp]:
  "(x :: 'a :: len word) && mask LENGTH('a) = x"
  using uint_lt2p [of x] by (simp add: mask_eq_iff)

lemma scast_ucast_down_same:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow> SCAST('a \<rightarrow> 'b) = UCAST('a::len \<rightarrow> 'b::len)"
  by (simp add: down_cast_same is_down)

lemma word_aligned_0_sum:
  "\<lbrakk> a + b = 0; is_aligned (a :: 'a :: len word) n; b \<le> mask n; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> a = 0 \<and> b = 0"
  by (simp add: word_plus_and_or_coroll aligned_mask_disjoint word_or_zero)

lemma mask_eq1_nochoice:
  "\<lbrakk> LENGTH('a) > 1; (x :: 'a :: len word) && 1 = x \<rbrakk> \<Longrightarrow> x = 0 \<or> x = 1"
  by (metis word_and_1)

lemma pow_mono_leq_imp_lt:
  "x \<le> y \<Longrightarrow> x < 2 ^ y"
  by (simp add: le_less_trans)

lemma unat_of_nat_ctz_mw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len word) = word_ctz w"
  using word_ctz_le[where w=w, simplified] unat_of_nat_eq[where x="word_ctz w" and 'a="'a"]
        pow_mono_leq_imp_lt
  by simp

lemma unat_of_nat_ctz_smw:
  "unat (of_nat (word_ctz (w :: 'a :: len word)) :: 'a :: len sword) = word_ctz w"
  using word_ctz_le[where w=w, simplified] unat_of_nat_eq[where x="word_ctz w" and 'a="'a"]
        pow_mono_leq_imp_lt
  by (metis le_unat_uoi le_unat_uoi linorder_neqE_nat nat_less_le scast_of_nat
            word_unat.Rep_inverse)

lemma shiftr_and_eq_shiftl:
  "(w >> n) && x = y \<Longrightarrow> w && (x << n) = (y << n)" for y :: "'a:: len word"
  by (smt and_not_mask is_aligned_neg_mask_eq is_aligned_shift shift_over_ao_dists(4)
          word_bool_alg.conj_assoc word_bw_comms(1))

lemma neg_mask_combine:
  "~~(mask a) && ~~(mask b) = ~~(mask (max a b))"
  by (auto simp: word_ops_nth_size word_size intro!: word_eqI)

lemma neg_mask_twice:
  "x && ~~(mask n) && ~~(mask m) = x && ~~(mask (max n m))"
  by (metis neg_mask_combine)

lemma multiple_mask_trivia:
  "n \<ge> m \<Longrightarrow> (x && ~~(mask n)) + (x && mask n && ~~(mask m)) = x && ~~(mask m)"
  apply (rule trans[rotated], rule_tac w="mask n" in word_plus_and_or_coroll2)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs neg_mask_twice
                   max_absorb2)
  done

lemma add_mask_lower_bits':
  "\<lbrakk> len = LENGTH('a); is_aligned (x :: 'a :: len word) n;
     \<forall>n' \<ge> n. n' < len \<longrightarrow> \<not> p !! n' \<rbrakk>
   \<Longrightarrow> x + p && ~~(mask n) = x"
  using add_mask_lower_bits by auto

lemma neg_mask_in_mask_range:
  "is_aligned ptr bits \<Longrightarrow> (ptr' && ~~(mask bits) = ptr) = (ptr' \<in> mask_range ptr bits)"
  apply (erule is_aligned_get_word_bits)
   apply (rule iffI)
    apply (drule sym)
    apply (simp add: word_and_le2)
    apply (subst word_plus_and_or_coroll, word_eqI_solve)
    apply (metis le_word_or2 neg_mask_add_mask word_bool_alg.conj.right_idem)
   apply clarsimp
   apply (smt add.right_neutral eq_iff is_aligned_neg_mask_eq mask_out_add_aligned neg_mask_mono_le
              word_and_not)
  apply (simp add: power_overflow mask_def)
  done

lemma aligned_offset_in_range:
  "\<lbrakk> is_aligned (x :: 'a :: len word) m; y < 2 ^ m; is_aligned p n; n \<ge> m; n < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x + y \<in> {p .. p + mask n}) = (x \<in> mask_range p n)"
  apply (simp only: is_aligned_add_or flip: neg_mask_in_mask_range)
  by (metis less_mask_eq mask_subsume)

lemma mask_range_to_bl':
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) bits; bits < LENGTH('a) \<rbrakk>
   \<Longrightarrow> mask_range ptr bits
       = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (subgoal_tac "\<exists>y. x = ptr + y \<and> y < 2 ^ bits")
    apply clarsimp
    apply (subst is_aligned_add_conv)
       apply assumption
      apply simp
    apply simp
   apply (rule_tac x="x - ptr" in exI)
   apply (simp add: add_diff_eq[symmetric])
   apply (simp only: word_less_sub_le[symmetric])
   apply (rule word_diff_ls')
    apply (simp add: field_simps mask_def)
   apply assumption
  apply simp
  apply (subgoal_tac "\<exists>y. y < 2 ^ bits \<and> to_bl (ptr + y) = to_bl x")
   apply clarsimp
   apply (rule conjI)
    apply (erule(1) is_aligned_no_wrap')
   apply (simp only: add_diff_eq[symmetric] mask_def)
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (rule_tac x="of_bl (drop (LENGTH('a) - bits) (to_bl x))" in exI)
  apply (rule context_conjI)
   apply (rule order_less_le_trans [OF of_bl_length])
    apply simp
   apply simp
  apply (subst is_aligned_add_conv)
     apply assumption
    apply simp
  apply (drule sym)
  apply (simp add: word_rep_drop)
  done

lemma mask_range_to_bl:
  "is_aligned (ptr :: 'a :: len word) bits
   \<Longrightarrow> mask_range ptr bits
        = {x. take (LENGTH('a) - bits) (to_bl x) = take (LENGTH('a) - bits) (to_bl ptr)}"
  apply (erule is_aligned_get_word_bits)
   apply (erule(1) mask_range_to_bl')
  apply (rule set_eqI)
  apply (simp add: power_overflow mask_def)
  done

lemma aligned_mask_range_cases:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n' \<rbrakk>
   \<Longrightarrow> mask_range p n \<inter> mask_range p' n' = {} \<or>
       mask_range p n \<subseteq> mask_range p' n' \<or>
       mask_range p n \<supseteq> mask_range p' n'"
  apply (simp add: mask_range_to_bl)
  apply (rule Meson.disj_comm, rule disjCI)
  apply (erule nonemptyE)
  apply simp
  apply (subgoal_tac "(\<exists>n''. LENGTH('a) - n = (LENGTH('a) - n') + n'')
                    \<or> (\<exists>n''. LENGTH('a) - n' = (LENGTH('a) - n) + n'')")
   apply (fastforce simp: take_add)
  apply arith
  done

lemma aligned_mask_range_offset_subset:
  assumes al: "is_aligned (ptr :: 'a :: len word) sz" and al': "is_aligned x sz'"
  and szv: "sz' \<le> sz"
  and xsz: "x < 2 ^ sz"
  shows "mask_range (ptr+x) sz' \<subseteq> mask_range ptr sz"
  using al
proof (rule is_aligned_get_word_bits)
  assume p0: "ptr = 0" and szv': "LENGTH ('a) \<le> sz"
  then have "(2 ::'a word) ^ sz = 0" by simp
  show ?thesis using p0
    by (simp add: \<open>2 ^ sz = 0\<close> mask_def)
next
  assume szv': "sz < LENGTH('a)"

  hence blah: "2 ^ (sz - sz') < (2 :: nat) ^ LENGTH('a)"
    using szv by auto
  show ?thesis using szv szv'
    apply (intro range_subsetI)
     apply (rule is_aligned_no_wrap' [OF al xsz])
    apply (simp only: flip: add_diff_eq add_mask_fold)
    apply (subst add.assoc, rule word_plus_mono_right)
     using al' is_aligned_add_less_t2n xsz
     apply fastforce
    apply (simp add: field_simps szv al is_aligned_no_overflow)
    done
qed

lemma aligned_mask_diff:
  "\<lbrakk> is_aligned (dest :: 'a :: len word) bits; is_aligned (ptr :: 'a :: len word) sz;
     bits \<le> sz; sz < LENGTH('a); dest < ptr \<rbrakk>
   \<Longrightarrow> mask bits + dest < ptr"
  apply (frule_tac p' = ptr in aligned_mask_range_cases, assumption)
  apply (elim disjE)
    apply (drule_tac is_aligned_no_overflow_mask, simp)+
    apply (simp add: algebra_split_simps word_le_not_less)
   apply (drule is_aligned_no_overflow_mask; fastforce)
  by (simp add: aligned_add_mask_less_eq is_aligned_weaken algebra_split_simps)

lemma aligned_mask_ranges_disjoint:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n';
     p && ~~(mask n') \<noteq> p'; p' && ~~(mask n) \<noteq> p \<rbrakk>
   \<Longrightarrow> mask_range p n \<inter> mask_range p' n' = {}"
  using aligned_mask_range_cases
  by (auto simp: neg_mask_in_mask_range)

lemma aligned_mask_ranges_disjoint2:
  "\<lbrakk> is_aligned p n; is_aligned ptr bits; n \<ge> m; n < size p; m \<le> bits;
     (\<forall>y < 2 ^ (n - m). p + (y << m) \<notin> mask_range ptr bits) \<rbrakk>
   \<Longrightarrow> mask_range p n \<inter> mask_range ptr bits = {}"
  apply safe
  apply (simp only: flip: neg_mask_in_mask_range)
  apply (drule_tac x="x && mask n >> m" in spec)
  apply (clarsimp simp: shiftr_less_t2n and_mask_less_size wsst_TYs multiple_mask_trivia
                        word_bw_assocs neg_mask_twice max_absorb2 shiftr_shiftl1)
  done

lemma leq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) \<le> mask high_bits"
  by (simp add: le_mask_iff shiftr_shiftr)

lemma ucast_ucast_eq_mask_shift:
  "(x :: 'a :: len word) \<le> mask (low_bits + LENGTH('b))
   \<Longrightarrow> ucast((ucast (x >> low_bits)) :: 'b :: len word) = x >> low_bits"
  by (meson and_mask_eq_iff_le_mask eq_ucast_ucast_eq not_le_imp_less shiftr_less_t2n'
            ucast_ucast_len)

lemma const_le_unat:
  "\<lbrakk> b < 2 ^ LENGTH('a); of_nat b \<le> a \<rbrakk> \<Longrightarrow> b \<le> unat (a :: 'a :: len word)"
  by (clarsimp simp: word_le_def uint_nat of_nat_inverse)

lemma upt_enum_offset_trivial:
  "\<lbrakk> x < 2 ^ LENGTH('a) - 1 ; n \<le> unat x \<rbrakk>
   \<Longrightarrow> ([(0 :: 'a :: len word) .e. x] ! n) = of_nat n"
  apply (induct x arbitrary: n)
    apply simp
  by (simp add: upto_enum_word_nth)

lemma word_le_mask_out_plus_2sz:
  "x \<le> (x && ~~(mask sz)) + 2 ^ sz - 1"
  by (metis add_diff_eq word_neg_and_le)

lemma ucast_add:
  "ucast (a + (b :: 'a :: len word)) = ucast a + (ucast b :: ('a signed word))"
  apply (case_tac "LENGTH('a) = 1")
   apply (clarsimp simp: ucast_def)
   apply (metis (hide_lams, mono_tags) One_nat_def len_signed plus_word.abs_eq
                                       uint_word_arith_bintrs(1) word_ubin.Abs_norm)
  apply (clarsimp simp: ucast_def)
  apply (metis le_refl len_signed plus_word.abs_eq uint_word_arith_bintrs(1) wi_bintr)
  done

lemma ucast_minus:
  "ucast (a - (b :: 'a :: len word)) = ucast a - (ucast b :: ('a signed word))"
  apply (insert ucast_add[where a=a and b="-b"])
  apply (metis (no_types, hide_lams) add_diff_eq diff_add_cancel ucast_add)
  done

lemma scast_ucast_add_one [simp]:
  "scast (ucast (x :: 'a::len word) + (1 :: 'a signed word)) = x + 1"
  apply (subst ucast_1[symmetric])
  apply (subst ucast_add[symmetric])
  apply clarsimp
  done

lemma word_and_le_plus_one:
  "a > 0 \<Longrightarrow> (x :: 'a :: len word) && (a - 1) < a"
  by (simp add: gt0_iff_gem1 word_and_less')

lemma unat_of_ucast_then_shift_eq_unat_of_shift[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) >> n) = unat (x >> n)"
  by (simp add: shiftr_div_2n' unat_ucast_up_simp)

lemma unat_of_ucast_then_mask_eq_unat_of_mask[simp]:
  "LENGTH('b) \<ge> LENGTH('a)
   \<Longrightarrow> unat ((ucast (x :: 'a :: len word) :: 'b :: len word) && mask m) = unat (x && mask m)"
  by (metis ucast_and_mask unat_ucast_up_simp)

lemma small_powers_of_2:
  "x \<ge> 3 \<Longrightarrow> x < 2 ^ (x - 1)"
  by (induct x; simp add: suc_le_pow_2)

lemma word_clz_sint_upper[simp]:
  "LENGTH('a) \<ge> 3 \<Longrightarrow> sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a sword) \<le> LENGTH('a)"
  using small_powers_of_2
  by (smt One_nat_def diff_less le_less_trans len_gt_0 len_signed lessI n_less_equal_power_2
           not_msb_from_less of_nat_mono sint_eq_uint uint_nat unat_of_nat_eq unat_power_lower
           word_clz_max word_of_nat_less wsst_TYs(3))

lemma word_clz_sint_lower[simp]:
  "LENGTH('a) \<ge> 3
   \<Longrightarrow> - sint (of_nat (word_clz (w :: 'a :: len word)) :: 'a signed word) \<le> LENGTH('a)"
  apply (subst sint_eq_uint)
   using small_powers_of_2 uint_nat
   apply (simp add: order_le_less_trans[OF word_clz_max] not_msb_from_less word_of_nat_less
                    word_size)
  by (simp add: uint_nat)

lemma shiftr_less_t2n3:
  "\<lbrakk> (2 :: 'a word) ^ (n + m) = 0; m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> (x :: 'a :: len word) >> n < 2 ^ m"
  by (fastforce intro: shiftr_less_t2n' simp: mask_def power_overflow)

lemma unat_shiftr_le_bound:
  "\<lbrakk> 2 ^ (LENGTH('a :: len) - n) - 1 \<le> bnd; 0 < n \<rbrakk>
   \<Longrightarrow> unat ((x :: 'a word) >> n) \<le> bnd"
  using less_not_refl3 le_step_down_nat le_trans less_or_eq_imp_le word_shiftr_lt
  by (metis (no_types, lifting))

lemma shiftr_eqD:
  "\<lbrakk> x >> n = y >> n; is_aligned x n; is_aligned y n \<rbrakk>
   \<Longrightarrow> x = y"
  by (metis is_aligned_shiftr_shiftl)

lemma word_shiftr_shiftl_shiftr_eq_shiftr:
  "a \<ge> b \<Longrightarrow> (x :: 'a :: len word) >> a << b >> b = x >> a"
  by (simp add: mask_shift multi_shift_simps(5) shiftr_shiftr)

lemma of_int_uint_ucast:
   "of_int (uint (x :: 'a::len word)) = (ucast x :: 'b::len word)"
  by (simp add: ucast_def word_of_int)

lemma mod_mask_drop:
  "\<lbrakk> m = 2 ^ n; 0 < m; mask n && msk = mask n \<rbrakk>
   \<Longrightarrow> (x mod m) && msk = x mod m"
  by (simp add: word_mod_2p_is_mask word_bw_assocs)

lemma mask_eq_ucast_eq:
  "\<lbrakk> x && mask LENGTH('a) = (x :: ('c :: len word));
     LENGTH('a) \<le> LENGTH('b)\<rbrakk>
    \<Longrightarrow> ucast (ucast x :: ('a :: len word)) = (ucast x :: ('b :: len word))"
  by (metis ucast_and_mask ucast_id ucast_ucast_mask ucast_up_eq)

lemma of_nat_less_t2n:
  "of_nat i < (2 :: ('a :: len) word) ^ n \<Longrightarrow> n < LENGTH('a) \<and> unat (of_nat i :: 'a word) < 2 ^ n"
  by (metis order_less_trans p2_gt_0 unat_less_power word_neq_0_conv)

lemma two_power_increasing_less_1:
  "\<lbrakk> n \<le> m; m \<le> LENGTH('a) \<rbrakk> \<Longrightarrow> (2 :: 'a :: len word) ^ n - 1 \<le> 2 ^ m - 1"
  by (metis diff_diff_cancel le_m1_iff_lt less_imp_diff_less p2_gt_0 two_power_increasing
            word_1_le_power word_le_minus_mono_left word_less_sub_1)

lemma word_sub_mono4:
  "\<lbrakk> y + x \<le> z + x; y \<le> y + x; z \<le> z + x \<rbrakk> \<Longrightarrow> y \<le> z" for y :: "'a :: len word"
  by (simp add: word_add_le_iff2)

lemma eq_or_less_helperD:
  "\<lbrakk> n = unat (2 ^ m - 1 :: 'a :: len word) \<or> n < unat (2 ^ m - 1 :: 'a word); m < LENGTH('a) \<rbrakk>
   \<Longrightarrow> n < 2 ^ m"
  by (meson le_less_trans nat_less_le unat_less_power word_power_less_1)

lemma mask_sub:
  "n \<le> m \<Longrightarrow> mask m - mask n = mask m && ~~(mask n)"
  by (metis (no_types) AND_NOT_mask_plus_AND_mask_eq add_right_imp_eq diff_add_cancel
                       and_mask_eq_iff_shiftr_0 shiftr_mask_le word_bool_alg.conj.commute)

lemma neg_mask_diff_bound:
  "sz'\<le> sz \<Longrightarrow> (ptr && ~~(mask sz')) - (ptr && ~~(mask sz)) \<le> 2 ^ sz - 2 ^ sz'"
  (is "_ \<Longrightarrow> ?lhs \<le> ?rhs")
proof -
  assume lt: "sz' \<le> sz"
  hence "?lhs = ptr && (mask sz && ~~(mask sz'))"
    by (metis add_diff_cancel_left' multiple_mask_trivia)
  also have "\<dots> \<le> ?rhs" using lt
    by (metis (mono_tags) add_diff_eq diff_eq_eq eq_iff mask_2pm1 mask_sub word_and_le')
  finally show ?thesis by simp
qed

lemma mask_range_subsetD:
  "\<lbrakk> p' \<in> mask_range p n; x' \<in> mask_range p' n'; n' \<le> n; is_aligned p n; is_aligned p' n' \<rbrakk> \<Longrightarrow>
   x' \<in> mask_range p n"
  using aligned_mask_step by fastforce

lemma add_mult_in_mask_range:
  "\<lbrakk> is_aligned (base :: 'a :: len word) n; n < LENGTH('a); bits \<le> n; x < 2 ^ (n - bits) \<rbrakk>
   \<Longrightarrow> base + x * 2^bits \<in> mask_range base n"
  by (simp add: is_aligned_no_wrap' mask_2pm1 nasty_split_lt word_less_power_trans2
                word_plus_mono_right)

lemma of_bl_length2:
  "length xs + c < LENGTH('a) \<Longrightarrow> of_bl xs * 2^c < (2::'a::len word) ^ (length xs + c)"
  by (simp add: of_bl_length word_less_power_trans2)

lemma mask_out_eq_0:
  "\<lbrakk> idx < 2 ^ sz; sz < LENGTH('a) \<rbrakk> \<Longrightarrow> (of_nat idx :: 'a :: len word) && ~~(mask sz) = 0"
  by (simp add: Word_Lemmas.of_nat_power less_mask_eq mask_eq_0_eq_x)

lemma is_aligned_neg_mask_eq':
  "is_aligned ptr sz = (ptr && ~~(mask sz) = ptr)"
  using is_aligned_mask mask_eq_0_eq_x by blast

lemma neg_mask_mask_unat:
  "sz < LENGTH('a)
   \<Longrightarrow> unat ((ptr :: 'a :: len word) && ~~(mask sz)) + unat (ptr && mask sz) = unat ptr"
  by (metis AND_NOT_mask_plus_AND_mask_eq unat_plus_simple word_and_le2)

lemma unat_pow_le_intro:
  "LENGTH('a) \<le> n \<Longrightarrow> unat (x :: 'a :: len word) < 2 ^ n"
  by (metis lt2p_lem not_le of_nat_le_iff of_nat_numeral semiring_1_class.of_nat_power uint_nat)

lemma unat_shiftl_less_t2n:
  "\<lbrakk> unat (x :: 'a :: len word) < 2 ^ (m - n); m < LENGTH('a) \<rbrakk> \<Longrightarrow> unat (x << n) < 2 ^ m"
  by (metis (no_types) Word_Lemmas.of_nat_power diff_le_self le_less_trans shiftl_less_t2n
                       unat_less_power word_unat.Rep_inverse)

lemma unat_is_aligned_add:
  "\<lbrakk> is_aligned p n; unat d < 2 ^ n \<rbrakk>
   \<Longrightarrow> unat (p + d && mask n) = unat d \<and> unat (p + d && ~~(mask n)) = unat p"
  by (metis add.right_neutral and_mask_eq_iff_le_mask and_not_mask le_mask_iff mask_add_aligned
            mask_out_add_aligned mult_zero_right shiftl_t2n shiftr_le_0)

lemma unat_shiftr_shiftl_mask_zero:
  "\<lbrakk> c + a \<ge> LENGTH('a) + b ; c < LENGTH('a) \<rbrakk>
   \<Longrightarrow> unat (((q :: 'a :: len word) >> a << b) && ~~(mask c)) = 0"
  by (fastforce intro: unat_is_aligned_add[where p=0 and n=c, simplified, THEN conjunct2]
                       unat_shiftl_less_t2n unat_shiftr_less_t2n unat_pow_le_intro)

lemmas of_nat_ucast = ucast_of_nat[symmetric]

lemma shift_then_mask_eq_shift_low_bits:
  "x \<le> mask (low_bits + high_bits) \<Longrightarrow> (x >> low_bits) && mask high_bits = x >> low_bits"
  by (simp add: leq_mask_shift le_mask_imp_and_mask)

lemma leq_low_bits_iff_zero:
  "\<lbrakk> x \<le> mask (low bits + high bits); x >> low_bits = 0 \<rbrakk> \<Longrightarrow> (x && mask low_bits = 0) = (x = 0)"
  using and_mask_eq_iff_shiftr_0 by force

lemma unat_less_iff:
  "\<lbrakk> unat (a :: 'a :: len word) = b; c < 2 ^ LENGTH('a) \<rbrakk> \<Longrightarrow> (a < of_nat c) = (b < c)"
  using unat_ucast_less_no_overflow_simp by blast

lemma is_aligned_no_overflow3:
 "\<lbrakk> is_aligned (a :: 'a :: len word) n; n < LENGTH('a); b < 2 ^ n; c \<le> 2 ^ n; b < c \<rbrakk>
  \<Longrightarrow> a + b \<le> a + (c - 1)"
  by (meson is_aligned_no_wrap' le_m1_iff_lt not_le word_less_sub_1 word_plus_mono_right)

lemma mask_add_aligned_right:
  "is_aligned p n \<Longrightarrow> (q + p) && mask n = q && mask n"
  by (simp add: mask_add_aligned add.commute)

lemma leq_high_bits_shiftr_low_bits_leq_bits_mask:
  "x \<le> mask high_bits \<Longrightarrow> (x :: 'a :: len word) << low_bits \<le> mask (low_bits + high_bits)"
  by (metis le_mask_shiftl_le_mask)

lemma from_to_bool_last_bit:
  "from_bool (to_bool (x && 1)) = x && 1"
  by (metis from_bool_to_bool_iff word_and_1)

lemma word_two_power_neg_ineq:
  "2 ^ m \<noteq> (0 :: 'a word) \<Longrightarrow> 2 ^ n \<le> - (2 ^ m :: 'a :: len word)"
  apply (cases "n < LENGTH('a)"; simp add: power_overflow)
  apply (cases "m < LENGTH('a)"; simp add: power_overflow)
  apply (simp add: word_le_nat_alt unat_minus word_size)
  apply (cases "LENGTH('a)"; simp)
  apply (simp add: less_Suc_eq_le)
  apply (drule power_increasing[where a=2 and n=n] power_increasing[where a=2 and n=m], simp)+
  apply (drule(1) add_le_mono)
  apply simp
  done

lemma unat_shiftl_absorb:
  "\<lbrakk> x \<le> 2 ^ p; p + k < LENGTH('a) \<rbrakk> \<Longrightarrow> unat (x :: 'a :: len word) * 2 ^ k = unat (x * 2 ^ k)"
  by (smt add_diff_cancel_right' add_lessD1 le_add2 le_less_trans mult.commute nat_le_power_trans
          unat_lt2p unat_mult_lem unat_power_lower word_le_nat_alt)

lemma word_plus_mono_right_split:
  "\<lbrakk> unat ((x :: 'a :: len word) && mask sz) + unat z < 2 ^ sz; sz < LENGTH('a) \<rbrakk>
   \<Longrightarrow> x \<le> x + z"
  apply (subgoal_tac "(x && ~~(mask sz)) + (x && mask sz) \<le> (x && ~~(mask sz)) + ((x && mask sz) + z)")
   apply (simp add:word_plus_and_or_coroll2 field_simps)
  apply (rule word_plus_mono_right)
   apply (simp add: less_le_trans no_olen_add_nat)
  using Word_Lemmas.of_nat_power is_aligned_no_wrap' by force

lemma mul_not_mask_eq_neg_shiftl:
  "~~(mask n) = -1 << n"
  by (simp add: NOT_mask shiftl_t2n)

lemma shiftr_mul_not_mask_eq_and_not_mask:
  "(x >> n) * ~~(mask n) = - (x && ~~(mask n))"
  by (metis NOT_mask and_not_mask mult_minus_left semiring_normalization_rules(7) shiftl_t2n)

lemma mask_eq_n1_shiftr:
  "n \<le> LENGTH('a) \<Longrightarrow> (mask n :: 'a :: len word) = -1 >> (LENGTH('a) - n)"
  by (metis diff_diff_cancel eq_refl mask_full shiftr_mask2)

lemma is_aligned_mask_out_add_eq:
  "is_aligned p n \<Longrightarrow> (p + x) && ~~(mask n) = p + (x && ~~(mask n))"
  by (simp add: mask_out_sub_mask mask_add_aligned)

lemmas is_aligned_mask_out_add_eq_sub
    = is_aligned_mask_out_add_eq[where x="a - b" for a b, simplified field_simps]

lemma aligned_bump_down:
  "is_aligned x n \<Longrightarrow> (x - 1) && ~~(mask n) = x - 2 ^ n"
  by (drule is_aligned_mask_out_add_eq[where x="-1"]) (simp add: NOT_mask)

lemma unat_2tp_if:
  "unat (2 ^ n :: ('a :: len) word) = (if n < LENGTH ('a) then 2 ^ n else 0)"
  by (split if_split, simp_all add: power_overflow)

lemma mask_of_mask:
  "mask (n::nat) && mask (m::nat) = mask (min m n)"
  by word_eqI_solve

lemma unat_signed_ucast_less_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> unat (ucast (x :: 'a :: len word) :: 'b :: len signed word) = unat x"
  by (simp add: unat_ucast_up_simp)

lemma toEnum_of_ucast:
  "LENGTH('b) \<le> LENGTH('a) \<Longrightarrow>
   (toEnum (unat (b::'b :: len word))::'a :: len word) = of_nat (unat b)"
  by (simp add: unat_pow_le_intro)

lemmas unat_ucast_mask = unat_ucast_eq_unat_and_mask[where w=a for a]

lemma t2n_mask_eq_if:
  "2 ^ n && mask m = (if n < m then 2 ^ n else 0)"
  by (rule word_eqI, auto simp add: word_size nth_w2p split: if_split)

lemma unat_ucast_le:
  "unat (ucast (x :: 'a :: len word) :: 'b :: len word) \<le> unat x"
  by (simp add: ucast_nat_def word_unat_less_le)

lemma ucast_le_up_down_iff:
  "\<lbrakk> LENGTH('a) \<le> LENGTH('b); (x :: 'b :: len word) \<le> ucast (max_word :: 'a :: len word) \<rbrakk>
   \<Longrightarrow> (ucast x \<le> (y :: 'a word)) = (x \<le> ucast y)"
  using le_max_word_ucast_id ucast_le_ucast by metis

lemma ucast_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> ucast (ucast (p && mask a >> b) :: 'a :: len word) = p && mask a >> b"
  by (metis add.commute le_mask_iff shiftr_mask_le ucast_ucast_eq_mask_shift word_and_le')

lemma unat_ucast_mask_shift:
  "a \<le> LENGTH('a) + b
   \<Longrightarrow> unat (ucast (p && mask a >> b) :: 'a :: len word) = unat (p && mask a >> b)"
  by (metis linear ucast_ucast_mask_shift unat_ucast_up_simp)

lemma mask_overlap_zero:
  "a \<le> b \<Longrightarrow> (p && mask a) && ~~(mask b) = 0"
  by (metis NOT_mask_AND_mask mask_lower_twice2 max_def)

lemma mask_shifl_overlap_zero:
  "a + c \<le> b \<Longrightarrow> (p && mask a << c) && ~~(mask b) = 0"
  by (metis and_not_mask le_mask_iff mask_shiftl_decompose shiftl_0 shiftl_over_and_dist
            shiftr_mask_le word_and_le' word_bool_alg.conj_commute)

lemma mask_overlap_zero':
  "a \<ge> b \<Longrightarrow> (p && ~~(mask a)) && mask b = 0"
  using mask_AND_NOT_mask mask_AND_less_0 by blast

lemma mask_rshift_mult_eq_rshift_lshift:
  "((a :: 'a :: len word) >> b) * (1 << c) = (a >> b << c)"
  by (simp add: shiftl_t2n)

lemma shift_alignment:
  "a \<ge> b \<Longrightarrow> is_aligned (p >> a << a) b"
  using is_aligned_shift is_aligned_weaken by blast

lemma mask_split_sum_twice:
  "a \<ge> b \<Longrightarrow> (p && ~~(mask a)) + ((p && mask a) && ~~(mask b)) + (p && mask b) = p"
  by (simp add: add.commute multiple_mask_trivia word_bool_alg.conj_commute
                word_bool_alg.conj_left_commute word_plus_and_or_coroll2)

lemma mask_shift_eq_mask_mask:
  "(p && mask a >> b << b) = (p && mask a) && ~~(mask b)"
  by (simp add: and_not_mask)

lemma mask_shift_sum:
  "\<lbrakk> a \<ge> b; unat n = unat (p && mask b) \<rbrakk>
   \<Longrightarrow> (p && ~~(mask a)) + (p && mask a >> b) * (1 << b) + n = (p :: 'a :: len word)"
  by (metis and_not_mask mask_rshift_mult_eq_rshift_lshift mask_split_sum_twice word_unat.Rep_eqD)

lemma is_up_compose:
  "\<lbrakk> is_up uc; is_up uc' \<rbrakk> \<Longrightarrow> is_up (uc' \<circ> uc)"
  unfolding is_up_def by (simp add: Word.target_size Word.source_size)

lemma of_int_sint_scast:
  "of_int (sint (x :: 'a :: len word)) = (scast x :: 'b :: len word)"
  by (metis scast_def word_of_int)

lemma scast_of_nat_to_signed [simp]:
  "scast (of_nat x :: 'a :: len word) = (of_nat x :: 'a signed word)"
  by (metis cast_simps(23) scast_scast_id(2))

lemma scast_of_nat_signed_to_unsigned_add:
  "scast (of_nat x + of_nat y :: 'a :: len signed word) = (of_nat x + of_nat y :: 'a :: len word)"
  by (metis of_nat_add scast_of_nat)

lemma scast_of_nat_unsigned_to_signed_add:
  "(scast (of_nat x + of_nat y :: 'a :: len word)) = (of_nat x + of_nat y :: 'a :: len signed word)"
  by (metis Abs_fnat_hom_add scast_of_nat_to_signed)

lemma and_mask_cases:
  fixes x :: "'a :: len word"
  assumes len: "n < LENGTH('a)"
  shows "x && mask n \<in> of_nat ` set [0 ..< 2 ^ n]"
proof -
  have "x && mask n \<in> {0 .. 2 ^ n - 1}"
    by (simp add: mask_def word_and_le1)
  also
  have "... = of_nat ` {0 .. 2 ^ n - 1}"
    apply (rule set_eqI, rule iffI)
     apply (clarsimp simp: image_iff)
     apply (rule_tac x="unat x" in bexI; simp)
     using len
     apply (simp add: word_le_nat_alt unat_2tp_if unat_minus_one)
    using len
    apply (clarsimp simp: word_le_nat_alt unat_2tp_if unat_minus_one)
    apply (subst unat_of_nat_eq; simp add: nat_le_Suc_less)
    apply (erule less_le_trans)
    apply simp
    done
  also have "{0::nat .. 2^n - 1} = set [0 ..< 2^n]" by (auto simp: nat_le_Suc_less)
  finally show ?thesis .
qed

lemma sint_of_nat_ge_zero:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) \<ge> 0"
  by (simp add: Word_Lemmas.of_nat_power not_msb_from_less sint_eq_uint)

lemma sint_eq_uint_2pl:
  "\<lbrakk> (a :: 'a :: len word) < 2 ^ (LENGTH('a) - 1) \<rbrakk>
   \<Longrightarrow> sint a = uint a"
  by (simp add: not_msb_from_less sint_eq_uint word_2p_lem word_size)

lemma sint_of_nat_le:
  "\<lbrakk> b < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk>
   \<Longrightarrow> sint (of_nat a :: 'a :: len word) \<le> sint (of_nat b :: 'a :: len word)"
  by (smt Word_Lemmas.of_nat_power diff_less le_less_trans len_gt_0 len_of_numeral_defs(2)
          nat_power_minus_less of_nat_le_iff sint_eq_uint_2pl uint_nat unat_of_nat_len)

lemma int_eq_sint:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> sint (of_nat x :: 'a :: len word) = int x"
  by (smt Word_Lemmas.of_nat_power diff_less le_less_trans len_gt_0 len_of_numeral_defs(2)
          nat_less_le sint_eq_uint_2pl uint_nat unat_lt2p unat_of_nat_len unat_power_lower)

lemma sint_ctz:
  "LENGTH('a) > 2
   \<Longrightarrow> 0 \<le> sint (of_nat (word_ctz (x :: 'a :: len word)) :: 'a signed word)
        \<and> sint (of_nat (word_ctz x) :: 'a signed word) \<le> LENGTH('a)"
  apply (subgoal_tac "LENGTH('a) < 2 ^ (LENGTH('a) - 1)")
   apply (rule conjI)
    apply (metis len_signed order_le_less_trans sint_of_nat_ge_zero word_ctz_le)
   apply (metis int_eq_sint len_signed sint_of_nat_le word_ctz_le)
  by (rule small_powers_of_2, simp)

lemma pow_sub_less:
  "\<lbrakk> a + b \<le> LENGTH('a); unat (x :: 'a :: len word) = 2 ^ a \<rbrakk>
   \<Longrightarrow> unat (x * 2 ^ b - 1) < 2 ^ (a + b)"
  by (metis (mono_tags) eq_or_less_helperD not_less of_nat_numeral power_add
                        semiring_1_class.of_nat_power unat_pow_le_intro word_unat.Rep_inverse)

lemma sle_le_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a \<le> b \<rbrakk> \<Longrightarrow> a <=s b"
  by (simp add: not_msb_from_less word_sle_msb_le)

lemma sless_less_2pl:
  "\<lbrakk> (b :: 'a :: len word) < 2 ^ (LENGTH('a) - 1); a < b \<rbrakk> \<Longrightarrow> a <s b"
  using not_msb_from_less word_sless_msb_less by blast

lemma and_mask2:
  "w << n >> n = w && mask (size w - n)"
  by (cases "n \<le> size w"; clarsimp simp: word_and_le2 and_mask shiftl_zero_size)

lemma unat_of_nat_word_log2:
  "LENGTH('a) < 2 ^ LENGTH('b)
   \<Longrightarrow> unat (of_nat (word_log2 (n :: 'a :: len word)) :: 'b :: len word) = word_log2 n"
  by (metis less_trans unat_of_nat_eq word_log2_max word_size)

lemma aligned_sub_aligned_simple:
  "\<lbrakk> is_aligned a n; is_aligned b n \<rbrakk> \<Longrightarrow> is_aligned (a - b) n"
  by (simp add: aligned_sub_aligned)

lemma minus_one_shift:
  "- (1 << n) = (-1 << n :: 'a::len word)"
  by (simp add: mask_def NOT_eq flip: mul_not_mask_eq_neg_shiftl)

lemma ucast_eq_mask:
  "(UCAST('a::len \<rightarrow> 'b::len) x = UCAST('a \<rightarrow> 'b) y) =
   (x && mask LENGTH('b) = y && mask LENGTH('b))"
  by (rule iffI; word_eqI_solve)

context
  fixes w :: "'a::len word"
begin

private lemma sbintrunc_uint_ucast:
  assumes "Suc n = LENGTH('b::len)"
  shows "sbintrunc n (uint (ucast w :: 'b word)) = sbintrunc n (uint w)"
  by (metis assms sbintrunc_bintrunc ucast_def word_ubin.eq_norm)

private lemma test_bit_sbintrunc:
  assumes "i < LENGTH('a)"
  shows "(word_of_int (sbintrunc n (uint w)) :: 'a word) !! i
           = (if n < i then w !! n else w !! i)"
  using assms by (simp add: nth_sbintr)
                 (simp add: test_bit_bin)

private lemma test_bit_sbintrunc_ucast:
  assumes len_a: "i < LENGTH('a)"
  shows "(word_of_int (sbintrunc (LENGTH('b) - 1) (uint (ucast w :: 'b word))) :: 'a word) !! i
          = (if LENGTH('b::len) \<le> i then w !! (LENGTH('b) - 1) else w !! i)"
  apply (subst sbintrunc_uint_ucast)
   apply simp
  apply (subst test_bit_sbintrunc)
   apply (rule len_a)
  apply (rule if_cong[OF _ refl refl])
  using leD less_linear by fastforce

lemma scast_ucast_high_bits:
  "scast (ucast w :: 'b::len word) = w
     \<longleftrightarrow> (\<forall> i \<in> {LENGTH('b) ..< size w}. w !! i = w !! (LENGTH('b) - 1))"
  unfolding scast_def sint_uint word_size
  apply (subst word_eq_iff)
  apply (rule iffI)
   apply (rule ballI)
   apply (drule_tac x=i in spec)
   apply (subst (asm) test_bit_sbintrunc_ucast; simp)
  apply (rule allI)
  apply (case_tac "n < LENGTH('a)")
   apply (subst test_bit_sbintrunc_ucast)
    apply simp
   apply (case_tac "n \<ge> LENGTH('b)")
    apply (drule_tac x=n in bspec)
  by auto

lemma scast_ucast_mask_compare:
  "scast (ucast w :: 'b::len word) = w
   \<longleftrightarrow> (w \<le> mask (LENGTH('b) - 1) \<or> ~~(mask (LENGTH('b) - 1)) \<le> w)"
  apply (clarsimp simp: le_mask_high_bits neg_mask_le_high_bits scast_ucast_high_bits word_size)
  apply (rule iffI; clarsimp)
   apply (rename_tac i j; case_tac "i = LENGTH('b) - 1"; case_tac "j = LENGTH('b) - 1")
  by auto

lemma ucast_less_shiftl_helper':
  "\<lbrakk> LENGTH('b) + (a::nat) < LENGTH('a); 2 ^ (LENGTH('b) + a) \<le> n\<rbrakk>
   \<Longrightarrow> (ucast (x :: 'b::len word) << a) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

end

lemma ucast_ucast_mask2:
  "is_down (UCAST ('a \<rightarrow> 'b)) \<Longrightarrow>
   UCAST ('b::len \<rightarrow> 'c::len) (UCAST ('a::len \<rightarrow> 'b::len) x) = UCAST ('a \<rightarrow> 'c) (x && mask LENGTH('b))"
  by word_eqI_solve

lemma ucast_NOT:
  "ucast (~~x) = ~~(ucast x) && mask (LENGTH('a))" for x::"'a::len word"
  by word_eqI

lemma ucast_NOT_down:
  "is_down UCAST('a::len \<rightarrow> 'b::len) \<Longrightarrow> UCAST('a \<rightarrow> 'b) (~~x) = ~~(UCAST('a \<rightarrow> 'b) x)"
  by word_eqI

lemma of_bl_mult_and_not_mask_eq:
  "\<lbrakk>is_aligned (a :: 'a::len word) n; length b + m \<le> n\<rbrakk>
   \<Longrightarrow> a + of_bl b * (2^m) && ~~(mask n) = a"
  by (smt add.left_neutral add_diff_cancel_right' add_mask_lower_bits and_mask_plus is_aligned_mask
          is_aligned_weaken le_less_trans of_bl_length2 subtract_mask(1))

lemma bin_to_bl_of_bl_eq:
  "\<lbrakk>is_aligned (a::'a::len word) n; length b + c \<le> n; length b + c < LENGTH('a)\<rbrakk>
  \<Longrightarrow> bin_to_bl (length b) (uint ((a + of_bl b * 2^c) >> c)) = b"
  apply (subst word_plus_and_or_coroll)
   apply (erule is_aligned_get_word_bits)
    apply (rule is_aligned_AND_less_0)
     apply (simp add: is_aligned_mask)
    apply (rule order_less_le_trans)
     apply (rule of_bl_length2)
     apply simp
    apply (simp add: two_power_increasing)
   apply simp
  apply (rule nth_equalityI)
   apply (simp only: len_bin_to_bl)
  apply (clarsimp simp only: len_bin_to_bl nth_bin_to_bl word_test_bit_def[symmetric])
  apply (simp add: nth_shiftr nth_shiftl
                   shiftl_t2n[where n=c, simplified mult.commute, simplified, symmetric])
  apply (simp add: is_aligned_nth[THEN iffD1, rule_format] test_bit_of_bl nth_rev)
  apply arith
  done

end
