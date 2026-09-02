/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainDerivatives
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantitative first-derivative bounds for the zero-chain link

This file verifies the numerical estimates underlying the constant `23` in
the standard zero-chain gradient bound.  The proof is global, including the
flat junction of `psi`, and uses explicit rational upper bounds throughout.
-/

open scoped ContDiff Topology
open Filter Function Polynomial Real Set

namespace BilevelLowerBound

noncomputable section

theorem sqrt_exp_one_lt :
    Real.sqrt (Real.exp 1) < (1649 / 1000 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

theorem sqrt_two_pi_lt :
    Real.sqrt (Real.pi / (1 / 2 : ℝ)) < (2507 / 1000 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]
  calc
    Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
    _ < 2 * 3.1416 := mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
    _ < (2507 / 1000 : ℝ) ^ 2 := by norm_num

theorem phiBound_lt : phiBound < (207 / 50 : ℝ) := by
  unfold phiBound
  calc
    Real.sqrt (Real.exp 1) * Real.sqrt (Real.pi / (1 / 2 : ℝ))
        < (1649 / 1000 : ℝ) * (2507 / 1000 : ℝ) := by
          exact mul_lt_mul sqrt_exp_one_lt sqrt_two_pi_lt.le
            (Real.sqrt_pos.2 (by positivity)) (by norm_num)
    _ < 207 / 50 := by norm_num

theorem exp_mul_sqrt_exp_lt :
    Real.exp 1 * Real.sqrt (Real.exp 1) < (449 / 100 : ℝ) := by
  calc
    Real.exp 1 * Real.sqrt (Real.exp 1)
        < (2719 / 1000 : ℝ) * (1649 / 1000 : ℝ) := by
          apply mul_lt_mul
          · exact Real.exp_one_lt_d9.trans (by norm_num)
          · exact sqrt_exp_one_lt.le
          · positivity
          · norm_num
    _ < 449 / 100 := by norm_num

theorem expNegInvSqGlue_deriv (x : ℝ) :
    deriv expNegInvSqGlue x = 2 * x⁻¹ ^ 3 * expNegInvSqGlue x := by
  have h := (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue 1 x).deriv
  simpa [mul_assoc] using h

theorem psi_deriv (t : ℝ) :
    deriv psi t =
      4 * Real.exp 1 * (2 * t - 1)⁻¹ ^ 3 *
        expNegInvSqGlue (2 * t - 1) := by
  have h := psi_iteratedDeriv 1 t
  rw [iteratedDeriv_one, iteratedDeriv_one, expNegInvSqGlue_deriv] at h
  norm_num at h ⊢
  ring_nf at h ⊢
  exact h

theorem cubic_exp_bound (x : ℝ) (hx : 0 ≤ x) :
    x ^ 3 * Real.exp (-2 * x) ≤
      (27 / 8 : ℝ) * Real.exp (-3) := by
  let y : ℝ := (2 / 3 : ℝ) * x
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have h := Real.mul_exp_neg_le_exp_neg_one y
  have hpow := pow_le_pow_left₀ (mul_nonneg hy (Real.exp_pos _).le) h 3
  have hLeft : (y * Real.exp (-y)) ^ 3 =
      (8 / 27 : ℝ) * (x ^ 3 * Real.exp (-2 * x)) := by
    have hExponent : (3 : ℝ) * (-y) = -2 * x := by
      dsimp [y]
      ring
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [hExponent]
    dsimp [y]
    ring
  have hRight : Real.exp (-1) ^ 3 = Real.exp (-3) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hLeft, hRight] at hpow
  nlinarith [Real.exp_pos (-3)]

theorem abs_psi_deriv_le (t : ℝ) :
    |deriv psi t| ≤ (447 / 100 : ℝ) := by
  let u : ℝ := 2 * t - 1
  rw [psi_deriv]
  change |4 * Real.exp 1 * u⁻¹ ^ 3 * expNegInvSqGlue u| ≤ _
  by_cases hu : u ≤ 0
  · rw [expNegInvSqGlue_eq_zero_of_nonpos hu]
    norm_num
  · have huPos : 0 < u := lt_of_not_ge hu
    let x : ℝ := u⁻¹ ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hCubic := cubic_exp_bound x hx
    have hBump : expNegInvSqGlue u = Real.exp (-x) := by
      rw [expNegInvSqGlue_eq_exp_of_pos huPos]
    rw [hBump]
    have hInv : u⁻¹ ^ 6 = x ^ 3 := by
      dsimp [x]
      ring
    have hExp : Real.exp (-x) ^ 2 = Real.exp (-2 * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hSquare :
        (4 * Real.exp 1 * u⁻¹ ^ 3 * Real.exp (-x)) ^ 2 =
          16 * Real.exp 1 ^ 2 * (x ^ 3 * Real.exp (-2 * x)) := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul, hInv, hExp]
      ring
    have hScaled :
        16 * Real.exp 1 ^ 2 * (x ^ 3 * Real.exp (-2 * x)) ≤
          54 * Real.exp (-1) := by
      calc
        16 * Real.exp 1 ^ 2 * (x ^ 3 * Real.exp (-2 * x))
            ≤ 16 * Real.exp 1 ^ 2 *
                ((27 / 8 : ℝ) * Real.exp (-3)) := by
                  gcongr
        _ = 54 * Real.exp (-1) := by
          rw [show Real.exp 1 ^ 2 = Real.exp 2 by
            rw [← Real.exp_nat_mul]; norm_num]
          calc
            16 * Real.exp 2 * ((27 / 8 : ℝ) * Real.exp (-3)) =
                54 * (Real.exp 2 * Real.exp (-3)) := by ring
            _ = 54 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
    have hNumerical : 54 * Real.exp (-1) < (447 / 100 : ℝ) ^ 2 := by
      rw [Real.exp_neg]
      change 54 / Real.exp 1 < (447 / 100 : ℝ) ^ 2
      rw [div_lt_iff₀ (Real.exp_pos (1 : ℝ))]
      nlinarith [Real.exp_one_gt_d9]
    apply abs_le_of_sq_le_sq _ (by norm_num)
    rw [hSquare]
    exact hScaled.trans hNumerical.le

theorem chainQ_deriv_fst (a b : ℝ) :
    deriv (fun x ↦ chainQ x b) a =
      -deriv psi (-a) * phiZero (-b) - deriv psi a * phiZero b := by
  change deriv
    (fun x ↦ psi (-x) * phiZero (-b) - psi x * phiZero b) a = _
  have hNeg : DifferentiableAt ℝ (fun x : ℝ ↦ psi (-x)) a :=
    by
      have h : ContDiff ℝ ∞ (fun x : ℝ ↦ psi (-x)) := by
        simpa only [Function.comp_def, id_eq] using
          psi_contDiff.comp contDiff_id.neg
      exact ContDiffAt.differentiableAt (ContDiff.contDiffAt h) (by simp)
  have hPos : DifferentiableAt ℝ psi a :=
    ContDiffAt.differentiableAt psi_contDiff.contDiffAt (by simp)
  rw [deriv_fun_sub (hNeg.mul_const (phiZero (-b)))
      (hPos.mul_const (phiZero b)),
    deriv_mul_const_field, deriv_mul_const_field, deriv_comp_neg]

theorem chainQ_deriv_snd (a b : ℝ) :
    deriv (fun y ↦ chainQ a y) b =
      -psi (-a) * deriv phiZero (-b) - psi a * deriv phiZero b := by
  change deriv
    (fun y ↦ psi (-a) * phiZero (-y) - psi a * phiZero y) b = _
  have hNeg : DifferentiableAt ℝ (fun y : ℝ ↦ phiZero (-y)) b :=
    by
      have h : ContDiff ℝ ∞ (fun y : ℝ ↦ phiZero (-y)) := by
        simpa only [Function.comp_def, id_eq] using
          phiZero_contDiff.comp contDiff_id.neg
      exact ContDiffAt.differentiableAt (ContDiff.contDiffAt h) (by simp)
  have hPos : DifferentiableAt ℝ phiZero b :=
    ContDiffAt.differentiableAt phiZero_contDiff.contDiffAt (by simp)
  rw [deriv_fun_sub (hNeg.const_mul (psi (-a)))
      (hPos.const_mul (psi a)),
    deriv_const_mul_field, deriv_const_mul_field, deriv_comp_neg]
  ring

theorem abs_phiZero_deriv_le (t : ℝ) :
    |deriv phiZero t| ≤ Real.sqrt (Real.exp 1) := by
  rw [abs_of_nonneg (phiZero_deriv_nonneg t)]
  exact phiZero_deriv_le_sqrt_exp t

theorem abs_chainQ_deriv_fst_le (a b : ℝ) :
    |deriv (fun x ↦ chainQ x b) a| ≤
      (447 / 100 : ℝ) * (207 / 50 : ℝ) := by
  rw [chainQ_deriv_fst]
  rcases le_total a 0 with ha | ha
  · have hZero : deriv psi a = 0 :=
      psi_deriv_eq_zero_of_le_half (by linarith)
    rw [hZero, zero_mul, sub_zero, abs_mul, abs_neg]
    exact mul_le_mul (abs_psi_deriv_le (-a))
      (abs_phiZero_le_bound (-b) |>.trans phiBound_lt.le)
      (abs_nonneg _) (by norm_num)
  · have hZero : deriv psi (-a) = 0 :=
      psi_deriv_eq_zero_of_le_half (by linarith)
    rw [hZero, neg_zero, zero_mul, zero_sub, abs_neg, abs_mul]
    exact mul_le_mul (abs_psi_deriv_le a)
      (abs_phiZero_le_bound b |>.trans phiBound_lt.le)
      (abs_nonneg _) (by norm_num)

theorem abs_chainQ_deriv_snd_le (a b : ℝ) :
    |deriv (fun y ↦ chainQ a y) b| ≤ (449 / 100 : ℝ) := by
  rw [chainQ_deriv_snd]
  rcases le_total a 0 with ha | ha
  · have hZero : psi a = 0 := psi_eq_zero_of_le_half (by linarith)
    rw [hZero, zero_mul, sub_zero, abs_mul, abs_neg]
    calc
      |psi (-a)| * |deriv phiZero (-b)|
          ≤ Real.exp 1 * Real.sqrt (Real.exp 1) := by
            exact mul_le_mul (abs_psi_le_exp_one (-a))
              (abs_phiZero_deriv_le (-b)) (abs_nonneg _)
              (Real.exp_pos 1).le
      _ ≤ 449 / 100 := exp_mul_sqrt_exp_lt.le
  · have hZero : psi (-a) = 0 := psi_eq_zero_of_le_half (by linarith)
    rw [hZero, neg_zero, zero_mul, zero_sub, abs_neg, abs_mul]
    calc
      |psi a| * |deriv phiZero b|
          ≤ Real.exp 1 * Real.sqrt (Real.exp 1) := by
            exact mul_le_mul (abs_psi_le_exp_one a)
              (abs_phiZero_deriv_le b) (abs_nonneg _)
              (Real.exp_pos 1).le
      _ ≤ 449 / 100 := exp_mul_sqrt_exp_lt.le

/-- The two link contributions incident to one coordinate sum to less than `23`. -/
theorem chain_coordinate_bound_lt_twentyThree :
    (447 / 100 : ℝ) * (207 / 50 : ℝ) + 449 / 100 < 23 := by
  norm_num

theorem expNegInvSqGlue_nonneg (x : ℝ) : 0 ≤ expNegInvSqGlue x := by
  by_cases hx : x ≤ 0
  · rw [expNegInvSqGlue_eq_zero_of_nonpos hx]
  · rw [expNegInvSqGlue_eq_exp_of_pos (lt_of_not_ge hx)]
    exact (Real.exp_pos _).le

theorem psi_deriv_nonneg (t : ℝ) : 0 ≤ deriv psi t := by
  rw [psi_deriv]
  by_cases ht : 2 * t - 1 ≤ 0
  · rw [expNegInvSqGlue_eq_zero_of_nonpos ht]
    norm_num
  · have htPos : 0 < 2 * t - 1 := lt_of_not_ge ht
    have hInv : 0 ≤ (2 * t - 1)⁻¹ ^ 3 :=
      pow_nonneg (inv_pos.mpr htPos).le _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hInv)
      (expNegInvSqGlue_nonneg _)

theorem psi_one : psi 1 = 1 := by
  rw [psi_eq_exp_of_half_lt (by norm_num)]
  norm_num

theorem one_le_psi_of_one_le {t : ℝ} (ht : 1 ≤ t) : 1 ≤ psi t := by
  have hDiff : Differentiable ℝ psi :=
    ContDiff.differentiable psi_contDiff (by simp)
  have hMono : Monotone psi := monotone_of_deriv_nonneg hDiff psi_deriv_nonneg
  simpa only [psi_one] using hMono ht

theorem one_le_phiZero_deriv_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    1 ≤ deriv phiZero t := by
  have hsq : t ^ 2 ≤ 1 := by
    have := (sq_le_sq.mpr (by simpa using ht) : t ^ 2 ≤ (1 : ℝ) ^ 2)
    simpa using this
  have hSqrt : Real.sqrt (Real.exp 1) = Real.exp (1 / 2 : ℝ) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
    rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [phiZero_deriv, gaussianKernel, hSqrt, ← Real.exp_add,
    Real.one_le_exp_iff]
  nlinarith

theorem chainQ_deriv_fst_nonpos (a b : ℝ) :
    deriv (fun x ↦ chainQ x b) a ≤ 0 := by
  rw [chainQ_deriv_fst]
  have h₁ : 0 ≤ deriv psi (-a) * phiZero (-b) :=
    mul_nonneg (psi_deriv_nonneg (-a)) (phiZero_nonneg (-b))
  have h₂ : 0 ≤ deriv psi a * phiZero b :=
    mul_nonneg (psi_deriv_nonneg a) (phiZero_nonneg b)
  linarith

/-- The second-variable derivative of an active frontier link is at most `-1`. -/
theorem chainQ_deriv_snd_le_neg_one {a b : ℝ}
    (ha : 1 ≤ |a|) (hb : |b| ≤ 1) :
    deriv (fun y ↦ chainQ a y) b ≤ -1 := by
  rw [chainQ_deriv_snd]
  rcases le_abs.mp ha with haPos | haNeg
  · have hZero : psi (-a) = 0 := psi_eq_zero_of_le_half (by linarith)
    rw [hZero, neg_zero, zero_mul, zero_sub]
    have hProd : 1 ≤ psi a * deriv phiZero b :=
      by
        simpa only [one_mul] using
          mul_le_mul (one_le_psi_of_one_le haPos)
            (one_le_phiZero_deriv_of_abs_le_one hb) (by norm_num)
            (psi_nonneg a)
    linarith
  · have hZero : psi a = 0 := psi_eq_zero_of_le_half (by linarith)
    rw [hZero, zero_mul, sub_zero]
    have hbNeg : |-b| ≤ 1 := by simpa only [abs_neg] using hb
    have hProd : 1 ≤ psi (-a) * deriv phiZero (-b) :=
      by
        simpa only [one_mul] using
          mul_le_mul (one_le_psi_of_one_le haNeg)
            (one_le_phiZero_deriv_of_abs_le_one hbNeg) (by norm_num)
            (psi_nonneg (-a))
    linarith

/-- Directional derivative of one link along an arbitrary affine scalar line. -/
theorem chainQ_affine_deriv (a b ca cb : ℝ) :
    deriv (fun t ↦ chainQ (a + t * ca) (b + t * cb)) 0 =
      deriv (fun x ↦ chainQ x b) a * ca +
        deriv (fun y ↦ chainQ a y) b * cb := by
  have hPsi : Differentiable ℝ psi :=
    ContDiff.differentiable psi_contDiff (by simp)
  have hPhi : Differentiable ℝ phiZero := phiZero_differentiable
  have haLine := (hasDerivAt_id (0 : ℝ)).mul_const ca |>.const_add a
  have hbLine := (hasDerivAt_id (0 : ℝ)).mul_const cb |>.const_add b
  have hPsiNeg := hPsi.differentiableAt.hasDerivAt.comp 0 haLine.neg
  have hPsiPos := hPsi.differentiableAt.hasDerivAt.comp 0 haLine
  have hPhiNeg := hPhi.differentiableAt.hasDerivAt.comp 0 hbLine.neg
  have hPhiPos := hPhi.differentiableAt.hasDerivAt.comp 0 hbLine
  have h := (hPsiNeg.mul hPhiNeg).sub (hPsiPos.mul hPhiPos)
  have hFun :
      (psi ∘ (-fun t : ℝ ↦ a + t * ca)) *
          (phiZero ∘ (-fun t : ℝ ↦ b + t * cb)) -
        (psi ∘ fun t : ℝ ↦ a + t * ca) *
          (phiZero ∘ fun t : ℝ ↦ b + t * cb) =
        fun t ↦ chainQ (a + t * ca) (b + t * cb) := by
    funext t
    simp only [Function.comp_apply, Pi.neg_apply, Pi.mul_apply, Pi.sub_apply]
    rfl
  have hd := h.deriv
  simp only [id_eq] at hd
  rw [hFun] at hd
  simp only [Function.comp_apply, Pi.neg_apply, one_mul, zero_mul,
    add_zero] at hd
  rw [chainQ_deriv_fst, chainQ_deriv_snd]
  convert hd using 1
  all_goals ring

end

end BilevelLowerBound
