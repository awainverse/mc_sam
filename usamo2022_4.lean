import tactic
import data.nat.prime
import ring_theory.int.basic
import data.real.sqrt
open nat
open int

-- 2022 USAMO Problem 4
-- https://artofproblemsolving.com/community/c5h2808839p24774670
-- Based on solution 1 by The_Turtle (post #5)

noncomputable theory
open_locale classical

lemma x_mod3_either_012: ∀ x, (x ≡ 0 [ZMOD 3] ∨ x ≡ 1 [ZMOD 3] ∨ x ≡ 2 [ZMOD 3]) := begin
  rintro x,
  have hx : x % 3 < 3,
  {
    have goal := @int.mod_lt x 3,
    have zero_lt_3 : (3 : ℤ) ≠ 0, {linarith,},
    refine goal zero_lt_3,
  },
  have hy : x % 3 ≥ 0,
  {
    have goal := @int.mod_nonneg x 3,
    have three_neq_0 : (3 : ℤ) ≠ 0, {linarith,},
    refine goal three_neq_0,
  },
  interval_cases (x % 3) with h,
  { have zero_eq_0mod3 : 0 % 3 = (0 : ℤ), {norm_num,},
    rw← zero_eq_0mod3 at h,
    rw← int.modeq at h,
    left, refine h,
  },
  { have one_eq_1mod3 : (1 : ℤ) = 1 % 3, {norm_num,},
    have goal : x % 3 = 1 % 3, {rw h, refine one_eq_1mod3,},
    rw← int.modeq at goal,
    right, left, refine goal,},
  {have two_eq_2mod3 : 2 % 3 = (2 : ℤ), {norm_num,},
    rw← two_eq_2mod3 at h,
    rw← int.modeq at h,
    right, right, refine h,}
end

lemma square_mod3_not_2 : ∀ x, ¬ (x * x ≡ 2 [ZMOD 3]) := begin
by_contradiction h,
push_neg at h,
cases h with x hx,
have x_either_012 := x_mod3_either_012 x,
cases x_either_012 with x_0 rest,
{
  have xx_0 := int.modeq.mul x_0 x_0,
  ring_nf at xx_0,
  ring_nf at hx,
  have xx0_2 := int.modeq.symm xx_0,
  have zero_eq_2 := int.modeq.trans xx0_2 hx,
  rw int.modeq at zero_eq_2,
  norm_num at zero_eq_2,
},
{
  cases rest with x_1 x_2,
  {
    have xx_0 := int.modeq.mul x_1 x_1,
    ring_nf at xx_0,
    ring_nf at hx,
    have xx0_2 := int.modeq.symm xx_0,
    have zero_eq_2 := int.modeq.trans xx0_2 hx,
    rw int.modeq at zero_eq_2,
    norm_num at zero_eq_2,
  },{
    have xx_0 := int.modeq.mul x_2 x_2,
    ring_nf at xx_0,
    ring_nf at hx,
    have xx0_2 := int.modeq.symm xx_0,
    have zero_eq_2 := int.modeq.trans xx0_2 hx,
    rw int.modeq at zero_eq_2,
    norm_num at zero_eq_2,
  },
},
end

theorem usamo_2022_problem_4 : ∀ (p : ℤ), ∀ (q : ℤ), (p > 0 ∧ q > 0 ∧ prime p ∧ prime q ∧ (∃ (x : ℕ), ↑x * ↑x = p - q) ∧ (∃ (y : ℕ), ↑y * ↑y = p * q - q)) → (p = 3 ∧ q = 2) := begin
rintro p,
rintro q,
rintro hypothesis,
have zero_le_p : 0 ≤ p, {linarith,},
have zero_le_q : 0 ≤ q, {linarith,},
set pnat := p.nat_abs with pnat_def,
set qnat := q.nat_abs with qnat_def,
have p_eq_pnat : p = pnat,
  {rw pnat_def, apply int.eq_nat_abs_of_zero_le, refine zero_le_p,},
have q_eq_qnat : q = qnat,
  {rw qnat_def, apply int.eq_nat_abs_of_zero_le, refine zero_le_q,},
cases hypothesis with p_pos rest1,
cases rest1 with q_pos rest2,
cases rest2 with p_prime rest3,
cases rest3 with q_prime rest4,
have pnat_prime : nat.prime pnat,
{rw pnat_def, rw← int.prime_iff_nat_abs_prime, refine p_prime},
have qnat_prime : nat.prime qnat,
{rw qnat_def, rw← int.prime_iff_nat_abs_prime, refine q_prime},
cases rest4 with pq_square pqq_square,
have qeq2_or_not := em (q = 2),

have one_lt_q : 1 < q, {
  by_contradiction, push_neg at h,
  have q_eq_1 : q = 1, {linarith,},
  rw q_eq_1 at q_prime, norm_num at q_prime,
},

cases qeq2_or_not with qeq2 qneq2,
{
  rw qeq2 at pq_square,
  rw qeq2 at pqq_square,
  have p_mod3_cases := x_mod3_either_012 p,
  cases p_mod3_cases with p_0 rest,
  {
    have p_div_3 := int.modeq.dvd (int.modeq.symm p_0),
    have tmp : p - 0 = p, {simp,},
    have three_prime : nat.prime 3, {norm_num,},
    rw tmp at p_div_3,
    rw p_eq_pnat at p_div_3,
    norm_cast at p_div_3,
    rw nat.prime_dvd_prime_iff_eq three_prime pnat_prime at p_div_3,
    split, repeat {linarith,},
  },{
    cases rest with p_1 p_2,
    {
      cases pq_square with x xkey,
      have xsq_modeq_2 : x * x ≡ 2 [ZMOD 3],
      {
        rw xkey,
        refine int.modeq.sub_right 2 p_1,
      },
      exfalso,
      refine (square_mod3_not_2 x) xsq_modeq_2,
    },
    {
      cases pqq_square with y ykey,
      have ysq_modeq_2 : y * y ≡ 2 [ZMOD 3],
      {
        rw ykey,
        have twop_1 := int.modeq.sub_right 2 (int.modeq.mul_right 2 p_2),
        ring_nf at twop_1,
        ring_nf,
        refine twop_1,
      },
      exfalso,
      refine (square_mod3_not_2 y) ysq_modeq_2,
    },
  },
},
{
  cases pq_square with x xkey,
  cases pqq_square with y ykey,
  have y_plus_x_y_minus_x_eq_p_q_minus_1 : (↑y + ↑x) * (↑y - ↑x) = p * (q - 1),
  {
    ring_nf,
    repeat {rw sq,},
    rw xkey, rw ykey,
    ring_nf,
  },
  have p_div_diff_sq : p ∣ (↑y + ↑x) * (↑y - ↑x),
  {
    use q - 1,
    refine y_plus_x_y_minus_x_eq_p_q_minus_1,
  },
  have y_nonzero : y ≠ 0, {
    by_contradiction,
    rw h at ykey,
    norm_num at ykey,
    have ykey' : 1 * q = p * q, {linarith,},
    have q_nonzero : q ≠ 0, {linarith,},
    rw mul_left_inj' q_nonzero at ykey',
    rw← ykey' at p_prime,
    norm_num at p_prime,
  },
  have x_add_y_ge_p : ↑x + ↑y ≥ p, {
    rw p_eq_pnat at p_div_diff_sq,
    have p_div_either := prime.dvd_mul pnat_prime p_div_diff_sq,
    cases p_div_either with p_div_add p_div_sub,
    {
      norm_cast,
      norm_cast at p_div_add,
      cases p_div_add with pfactor p_div_key,
      have pfactor_ge : pfactor ≥ 1, {
        by_contradiction,
        push_neg at h,
        have pfactor_0 : pfactor = 0, {linarith,},
        rw pfactor_0 at p_div_key,
        ring_nf at p_div_key,
        have y_zero : y = 0, {linarith,},
        refine y_nonzero y_zero,
      },
      have p_pfactor_ge : pnat * pfactor ≥ pnat, {
        rw ge, rw ge at pfactor_ge,
        have zero_le_pnat : 0 ≤ pnat, {linarith,},
        refine le_mul_of_one_le_right zero_le_pnat pfactor_ge,
      },
      rw p_eq_pnat,
      norm_cast, linarith,
    },{
      have diff_pos : 0 < (y : ℤ) - (x : ℤ), {
        have zero_le_p_q_sub_1 : 0 < p * (q - 1), {
          rw mul_pos_iff, left, split,
          {refine gt.lt p_pos,}, {linarith,},
        },
        rw← y_plus_x_y_minus_x_eq_p_q_minus_1 at zero_le_p_q_sub_1,
        rw mul_pos_iff at zero_le_p_q_sub_1,
        cases zero_le_p_q_sub_1 with case1 case2,
        {
          cases case1 with tmp1 tmp2, refine tmp2,
        },{
          cases case2 with sum_neg unused,
          norm_cast at sum_neg,
          linarith,
        },
      },
      have diff_pos2 : (x : ℤ) ≤ (y : ℤ), {linarith,},
      norm_cast at diff_pos2,
      have diff_cast_eq_cast_diff : (y : ℤ) - (x : ℤ) = ↑(y - x), {
        have goal := int.coe_nat_sub diff_pos2, linarith,
      },
      rw diff_cast_eq_cast_diff at p_div_sub,
      norm_cast at p_div_sub,
      cases p_div_sub with pfactor p_div_key,

      have pfactor_ge : pfactor ≥ 1, {
        by_contradiction,
        push_neg at h,
        have pfactor_0 : pfactor = 0, {linarith,},
        rw pfactor_0 at p_div_key,
        ring_nf at p_div_key,
        have y_eq_x : y = x, {linarith,},
        rw y_eq_x at ykey,
        rw xkey at ykey,
        have ykey' : p * 1 = p * q, {linarith,},
        have p_nonzero : p ≠ 0, {linarith,},
        rw mul_right_inj' p_nonzero at ykey',
        rw← ykey' at q_prime,
        norm_num at q_prime,
      },
      have p_pfactor_ge : pnat * pfactor ≥ pnat, {
        rw ge, rw ge at pfactor_ge,
        have zero_le_pnat : 0 ≤ pnat, {linarith,},
        refine le_mul_of_one_le_right zero_le_pnat pfactor_ge,
      },
      rw p_eq_pnat,
      norm_cast, linarith,
    },
  },
  set p_real : ℝ := ↑p with p_real_def,
  set q_real : ℝ := ↑q with q_real_def,
  set x_real : ℝ := ↑x with x_real_def,
  set y_real : ℝ := ↑y with y_real_def,
  have sqrt_p_pos : 0 < real.sqrt p_real, {
    rw real.sqrt_pos, rw p_real_def, norm_cast, linarith,},
  have sqrt_p_not_zero : real.sqrt p_real ≠ 0, {linarith,},
      
  have p_real_nonneg : 0 ≤ p_real, {rw p_real_def, norm_cast, refine zero_le_p,},
  have q_real_nonneg : 0 ≤ q_real, {rw q_real_def, norm_cast, refine zero_le_q,},
  have x_real_nonneg : 0 ≤ x_real, {rw x_real_def, norm_cast, linarith,},
  have y_real_nonneg : 0 ≤ y_real, {rw y_real_def, norm_cast, linarith,},
  have q_neq_y : q ≠ y, {
    by_contradiction,
    rw h at ykey,
    have y_eqn : ↑y = p - 1, {
      ring_nf at ykey, rw sq at ykey,
      have y_nonzero' : ↑y ≠ (0 : ℤ), {norm_cast, refine y_nonzero,},
      rw mul_left_inj' y_nonzero' at ykey,
      refine ykey,
    },
    rw← h at y_eqn,
    have q_2_or_odd := nat.prime.eq_two_or_odd' qnat_prime,
    cases q_2_or_odd with q2 qodd,
    {
      have q2_new : q = (2 : ℤ), {linarith,},
      refine qneq2 q2_new,
    },
    {
      have p_eq_q_add_one : ↑pnat = ↑qnat + 1, {linarith,},
      norm_cast at p_eq_q_add_one,
      rw nat.succ_eq_one_add at p_eq_q_add_one,
      rw add_comm at p_eq_q_add_one,
      have pnat_even := odd.add_odd qodd odd_one,
      rw← p_eq_q_add_one at pnat_even,
      rw nat.prime.even_iff pnat_prime at pnat_even,
      have pnat_two : (↑pnat) = (2 : ℤ), {norm_cast, refine pnat_even},
      rw← p_eq_pnat at pnat_two,
      have q_eq_1 : q = 1, {linarith,},
      have q_neq_1 := prime.ne_one q_prime,
      refine q_neq_1 q_eq_1,
    },
  },
  have q_div_y : q ∣ y, {
    have q_div_ysq : q ∣ y ^ 2, {
      use p - 1,
      ring_nf,
      ring_nf at ykey,
      ring_nf,
      refine ykey,
    },
    refine prime.dvd_of_dvd_pow q_prime q_div_ysq,
  },
  have y_ge_2q : ↑y ≥ 2 * q, {
    cases q_div_y with qfactor q_div_key,
    have two_le_qfactor_or_not := em (2 ≤ qfactor),
    cases two_le_qfactor_or_not with two_le_qfactor qfactor_lt_two,
    {
      have goal := mul_le_mul_of_nonneg_left two_le_qfactor zero_le_q,
      rw mul_comm q 2 at goal, linarith,
    },{
      push_neg at qfactor_lt_two,
      have qfactor_nonpos : qfactor ≤ 0, {
        by_contradiction, push_neg at h,
        have qfactor_eq_1 : qfactor = 1, {linarith,},
        rw qfactor_eq_1 at q_div_key,
        ring_nf at q_div_key,
        refine q_neq_y q_div_key.symm,
      },
      have q_qfactor_nonpos : q * qfactor ≤ 0, {
        rw mul_nonpos_iff, left,
        split, repeat {linarith,},
      },
      have y_le_zero : ↑y ≤ 0, {linarith,},
      norm_cast at y_le_zero,
      have y_eq_zero : y = 0, {linarith,},
      exfalso, refine y_nonzero y_eq_zero,
    },
  },
  have p_sub_1_ge_4q : p - 1 ≥ 4 * q, {
    have twoq_le_y := ge.le y_ge_2q,
    have twoq_nonneg : 0 ≤ 2 * q, {linarith,},
    have y_nonneg : 0 ≤ (y : ℤ), {norm_cast, linarith,},
    have squared_ineq := mul_le_mul twoq_le_y twoq_le_y twoq_nonneg y_nonneg,
    rw ykey at squared_ineq,
    ring_nf at squared_ineq,
    have squared_ineq' : 4 * q * q ≤ (p - 1) * q, {ring_nf, refine squared_ineq},
    have q_pos' : 0 < q, {linarith,},
    by_contradiction,
    push_neg at h,
    have h2 := mul_lt_mul_of_pos_right h q_pos',
    linarith,
  },
  have step1' : (real.sqrt q_real) + 1 =
    ((real.sqrt (p_real * q_real)) + (real.sqrt p_real)) / (real.sqrt p_real),
  {
    rw div_add_same sqrt_p_not_zero,
    rw real.sqrt_mul p_real_nonneg,
    rw mul_comm,
    rw mul_div_cancel,
    refine sqrt_p_not_zero,
  },
  have step1 : (real.sqrt q_real) + 1 ≥
    ((real.sqrt (p_real * q_real)) + (real.sqrt p_real)) / (real.sqrt p_real), {linarith,},
  have step2 : ((real.sqrt (p_real * q_real)) + (real.sqrt p_real)) / (real.sqrt p_real)
    ≥ ((real.sqrt (p_real * q_real - q_real)) + (real.sqrt (p_real - q_real))) / (real.sqrt p_real),
    {
      have pqq_le_pq : p_real * q_real - q_real ≤ p_real * q_real,
      {linarith,},
      have sqrt_pqq_le_pq := real.sqrt_le_sqrt pqq_le_pq,
      have pminusq_le_p : p_real - q_real ≤ p_real, {linarith,},
      have sqrt_pminusq_le_p := real.sqrt_le_sqrt pminusq_le_p,
      have numer_ineq := add_le_add sqrt_pqq_le_pq sqrt_pminusq_le_p,
      rw← div_le_div_right sqrt_p_pos at numer_ineq,
      linarith,
    },
  have step3' : ((real.sqrt (p_real * q_real - q_real)) + (real.sqrt (p_real - q_real))) / (real.sqrt p_real)
    = (y_real + x_real) / (real.sqrt p_real), {
      have pq_sub_q_real : y_real * y_real = p_real * q_real - q_real, {
        rw p_real_def, rw q_real_def, rw y_real_def,
        norm_cast, refine ykey,
      },
      have p_sub_q_real : x_real * x_real = p_real - q_real, {
        rw p_real_def, rw q_real_def, rw x_real_def,
        norm_cast, refine xkey,
      },
      rw← pq_sub_q_real, rw← p_sub_q_real,
      rw real.sqrt_mul_self x_real_nonneg,
      rw real.sqrt_mul_self y_real_nonneg,
    },
  have step3 : ((real.sqrt (p_real * q_real - q_real)) + (real.sqrt (p_real - q_real))) / (real.sqrt p_real)
    ≥ (y_real + x_real) / (real.sqrt p_real), {linarith,},
  have step4 : (y_real + x_real) / (real.sqrt p_real) ≥ real.sqrt p_real, {
    rw ge,
    have p_real_le_x_y_real : p_real ≤ y_real + x_real, {
      rw x_real_def, rw y_real_def, rw p_real_def,
      norm_cast, norm_cast at x_add_y_ge_p,
      rw add_comm at x_add_y_ge_p,
      refine x_add_y_ge_p,
    },
    rw← div_le_div_right sqrt_p_pos at p_real_le_x_y_real,
    rw real.div_sqrt at p_real_le_x_y_real,
    refine p_real_le_x_y_real,
  },
  have step5 : real.sqrt p_real ≥ real.sqrt (4 * q_real + 1), {
    have core : p_real ≥ 4 * q_real + 1, {
      rw p_real_def, rw q_real_def,
      norm_cast, linarith,
    },
    rw ge, rw ge at core,
    refine real.sqrt_le_sqrt core,
  },
  have steps_combined := ge_trans (
    ge_trans (ge_trans (ge_trans step1 step2) step3) step4) step5,
  rw ge at steps_combined,
  have lhs_nonneg := real.sqrt_nonneg (4 * q_real + 1),
  have rhs_nonneg : 0 ≤ (real.sqrt q_real) + 1, {
    have q_real_nonneg := real.sqrt_nonneg q_real, linarith,
  },
  have squared_ineq := mul_le_mul steps_combined steps_combined lhs_nonneg rhs_nonneg,
  have zero_le_4q_1 : 0 ≤ 4 * q_real + 1, {linarith,},
  rw real.mul_self_sqrt zero_le_4q_1 at squared_ineq,
  ring_nf at squared_ineq,
  have squared_ineq_2 : 4 * q_real ≤ (real.sqrt q_real + 2) * (real.sqrt q_real),
  {linarith,},
  rw right_distrib at squared_ineq_2,
  rw real.mul_self_sqrt q_real_nonneg at squared_ineq_2,
  have squared_ineq_3 : 3 * q_real ≤ 2 * real.sqrt q_real, {linarith,},
  have ineq_4 : q_real ≤ real.sqrt q_real, {linarith,},
  rw real.le_sqrt q_real_nonneg q_real_nonneg at ineq_4,
  have q_real_pos : 0 < q_real, {rw q_real_def, norm_cast, linarith,},
  have q_real_nonzero : q_real ≠ 0, {linarith,},
  rw← div_le_div_right q_real_pos at ineq_4,
  have q_real_le_1 : q_real ≤ 1, {
    rw div_self q_real_nonzero at ineq_4,
    rw sq at ineq_4,
    rw mul_div_cancel q_real q_real_nonzero at ineq_4,
    refine ineq_4,
  },
  rw q_real_def at q_real_le_1,
  norm_cast at q_real_le_1,
  rw q_eq_qnat at q_real_le_1,
  norm_cast at q_real_le_1,
  have two_le_qnat := nat.prime.two_le qnat_prime,
  linarith,
},
end

