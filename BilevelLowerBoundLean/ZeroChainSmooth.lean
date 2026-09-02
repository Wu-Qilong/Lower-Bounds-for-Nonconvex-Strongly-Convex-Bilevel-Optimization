/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smoothness and flat jets of the zero-chain activation

The paper's activation is zero up to the threshold `1 / 2` and equals
`exp (1 - 1 / (2t - 1)^2)` above it.  Smoothness at the threshold is not a
consequence of the two branch formulas alone.  This file proves the required
flat-junction estimate, constructs the one-sided bump `exp (-1/x^2)`, proves
that it is `C^∞`, and transfers the result to `psi`.

In particular, every iterated derivative of `psi` vanishes throughout the
closed flat region.  This is the analytic statement used by the zero-chain
interface, not merely the value-level identity `psi t = 0`.
-/

open scoped ContDiff Topology
open Filter Function Polynomial Real Set

namespace BilevelLowerBound

noncomputable section

/-- A polynomial is dominated at `+∞` by the squared-exponential denominator. -/
theorem tendsto_div_exp_sq_atTop (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x / Real.exp (x ^ 2)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x ↦ norm_nonneg _) ?_
    (tendsto_zero_iff_norm_tendsto_zero.mp p.tendsto_div_exp_atTop)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  change ‖p.eval x / Real.exp (x ^ 2)‖ ≤ ‖p.eval x / Real.exp x‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (Real.exp_pos _)
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The one-sided flat bump `0` for `x ≤ 0` and `exp (-1/x²)` for `x > 0`. -/
noncomputable def expNegInvSqGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else Real.exp (-(x⁻¹) ^ 2)

@[simp]
theorem expNegInvSqGlue_zero : expNegInvSqGlue 0 = 0 := by
  simp [expNegInvSqGlue]

theorem expNegInvSqGlue_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    expNegInvSqGlue x = 0 := by
  simp [expNegInvSqGlue, hx]

theorem expNegInvSqGlue_eq_exp_of_pos {x : ℝ} (hx : 0 < x) :
    expNegInvSqGlue x = Real.exp (-(x⁻¹) ^ 2) := by
  simp [expNegInvSqGlue, hx.not_ge]

/-- The flat bump dominates every inverse polynomial at the junction. -/
theorem tendsto_polynomial_inv_mul_expNegInvSqGlue_zero (p : ℝ[X]) :
    Tendsto (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) (nhds 0) (nhds 0) := by
  simp only [expNegInvSqGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := tendsto_div_exp_sq_atTop p |>.comp tendsto_inv_nhdsGT_zero
  refine h.congr' <| mem_of_superset self_mem_nhdsWithin fun x hx ↦ ?_
  simp [exp_neg, div_eq_mul_inv]

/-- Derivative of the active exponent. -/
theorem hasDerivAt_neg_inv_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -((y⁻¹) ^ 2)) (2 * x⁻¹ ^ 3) x := by
  have hCoeff : -(2 * x⁻¹ * -(x ^ 2)⁻¹) = 2 * x⁻¹ ^ 3 := by
    field_simp
  rw [← hCoeff]
  change HasDerivAt (-(fun y : ℝ ↦ y⁻¹) ^ 2)
    (-(2 * x⁻¹ * -(x ^ 2)⁻¹)) x
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
    ((hasDerivAt_inv hx).pow 2).neg

/--
Differentiating `P(x⁻¹) exp (-1/x²)` again produces an expression of the
same form with another polynomial.  The theorem also covers the junction
`x = 0`, where the derivative is zero by the preceding limit.
-/
theorem hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue
    (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x)
      ((Polynomial.C 2 * Polynomial.X ^ 3 * p -
          Polynomial.X ^ 2 * Polynomial.derivative p).eval x⁻¹ *
        expNegInvSqGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [expNegInvSqGlue_eq_zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    simp [expNegInvSqGlue, hy.le]
  · simp only [expNegInvSqGlue, le_refl, ↓reduceIte, mul_zero,
      hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_expNegInvSqGlue_zero
      (p * Polynomial.X)).mono_left inf_le_left).congr fun x ↦ ?_
    rw [slope_def_field]
    by_cases hx0 : x ≤ 0
    · simp [expNegInvSqGlue, hx0]
    · simp [expNegInvSqGlue, hx0, div_eq_mul_inv, mul_right_comm]
  · have hp := (p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx.ne')
    have he := (hasDerivAt_neg_inv_sq hx.ne').exp
    have hprod := hp.mul he
    have hEq :
        (fun y ↦ p.eval y⁻¹ * expNegInvSqGlue y) =ᶠ[nhds x]
          ((fun y ↦ p.eval y) ∘ Inv.inv) *
            (fun y ↦ Real.exp (-(y⁻¹) ^ 2)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [expNegInvSqGlue, hy.not_ge]
    have hCoeff :
        (Polynomial.C 2 * Polynomial.X ^ 3 * p -
            Polynomial.X ^ 2 * Polynomial.derivative p).eval x⁻¹ *
          expNegInvSqGlue x =
          p.derivative.eval x⁻¹ * -(x ^ 2)⁻¹ * Real.exp (-(x⁻¹) ^ 2) +
            p.eval x⁻¹ * (Real.exp (-(x⁻¹) ^ 2) * (2 * x⁻¹ ^ 3)) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, expNegInvSqGlue, hx.not_ge,
        if_false]
      field_simp
      ring
    rw [hCoeff]
    simpa only [Function.comp_apply, Pi.mul_apply] using
      hprod.congr_of_eventuallyEq hEq

theorem differentiable_polynomial_eval_inv_mul_expNegInvSqGlue (p : ℝ[X]) :
    Differentiable ℝ (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) :=
  fun x ↦
    (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue p x).differentiableAt

theorem continuous_polynomial_eval_inv_mul_expNegInvSqGlue (p : ℝ[X]) :
    Continuous (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) :=
  (differentiable_polynomial_eval_inv_mul_expNegInvSqGlue p).continuous

/-- Every inverse-polynomial multiple of the bump is infinitely smooth. -/
theorem contDiff_polynomial_eval_inv_mul_expNegInvSqGlue {n : ℕ∞}
    (p : ℝ[X]) :
    ContDiff ℝ n (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
      exact contDiff_zero.2 <|
        continuous_polynomial_eval_inv_mul_expNegInvSqGlue _
  | succ m ihm =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2
      ⟨differentiable_polynomial_eval_inv_mul_expNegInvSqGlue _, by simp, ?_⟩
    convert! ihm (Polynomial.C 2 * Polynomial.X ^ 3 * p -
      Polynomial.X ^ 2 * Polynomial.derivative p) using 2
    exact (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue p _).deriv

/-- The one-sided squared-inverse bump is `C^∞`. -/
theorem expNegInvSqGlue_contDiff {n : ℕ∞} :
    ContDiff ℝ n expNegInvSqGlue := by
  simpa using
    contDiff_polynomial_eval_inv_mul_expNegInvSqGlue (n := n) 1

/-- Every iterated derivative of an inverse-polynomial bump is another such expression. -/
theorem exists_polynomial_iteratedDeriv_expNegInvSqGlue (n : ℕ) (p : ℝ[X]) :
    ∃ q : ℝ[X],
      iteratedDeriv n (fun x ↦ p.eval x⁻¹ * expNegInvSqGlue x) =
        fun x ↦ q.eval x⁻¹ * expNegInvSqGlue x := by
  induction n generalizing p with
  | zero => exact ⟨p, by simp only [iteratedDeriv_zero]⟩
  | succ n ihn =>
    obtain ⟨q, hq⟩ := ihn p
    refine ⟨Polynomial.C 2 * Polynomial.X ^ 3 * q -
      Polynomial.X ^ 2 * Polynomial.derivative q, ?_⟩
    rw [iteratedDeriv_succ, hq]
    funext x
    exact (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue q x).deriv

/-- All jets of the one-sided bump vanish at its junction. -/
theorem expNegInvSqGlue_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n expNegInvSqGlue 0 = 0 := by
  obtain ⟨q, hq⟩ := exists_polynomial_iteratedDeriv_expNegInvSqGlue n 1
  have hAt := congrFun hq 0
  have hOne :
      (fun x ↦ (1 : ℝ[X]).eval x⁻¹ * expNegInvSqGlue x) =
        expNegInvSqGlue := by
    funext x
    simp
  rw [hOne] at hAt
  simpa only [expNegInvSqGlue_zero, mul_zero] using hAt

/-- Exact factorization of the paper's `psi` through the flat bump. -/
theorem psi_factorization (t : ℝ) :
    psi t = Real.exp 1 * expNegInvSqGlue (2 * t - 1) := by
  by_cases ht : t ≤ 1 / 2
  · have hu : 2 * t - 1 ≤ 0 := by linarith
    rw [psi_eq_zero_of_le_half ht, expNegInvSqGlue_eq_zero_of_nonpos hu,
      mul_zero]
  · have ht' : 1 / 2 < t := lt_of_not_ge ht
    have hu : 0 < 2 * t - 1 := by linarith
    have hInv : 1 / (2 * t - 1) ^ 2 = ((2 * t - 1)⁻¹) ^ 2 := by
      field_simp
    rw [psi_eq_exp_of_half_lt ht']
    simp only [expNegInvSqGlue, hu.not_ge, if_false, hInv,
      Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

/-- The activation `psi` in the paper is globally `C^∞`. -/
theorem psi_contDiff : ContDiff ℝ ∞ psi := by
  have hEq : psi =
      fun t : ℝ ↦ Real.exp 1 * expNegInvSqGlue (2 * t - 1) := by
    funext t
    exact psi_factorization t
  rw [hEq]
  exact contDiff_const.mul
    (expNegInvSqGlue_contDiff.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const))

/-- Exact iterated-derivative scaling for the affine representation of `psi`. -/
theorem psi_iteratedDeriv (n : ℕ) (t : ℝ) :
    iteratedDeriv n psi t =
      Real.exp 1 * (2 : ℝ) ^ n *
        iteratedDeriv n expNegInvSqGlue (2 * t - 1) := by
  have hEq : psi =
      fun u : ℝ ↦ Real.exp 1 * expNegInvSqGlue (2 * u - 1) := by
    funext u
    exact psi_factorization u
  rw [hEq]
  rw [iteratedDeriv_const_mul_field]
  have hShift : ContDiff ℝ n (fun z : ℝ ↦ expNegInvSqGlue (z - 1)) :=
    expNegInvSqGlue_contDiff.comp (contDiff_id.sub contDiff_const)
  have hScale := iteratedDeriv_comp_const_mul hShift (2 : ℝ)
  have hScaleAt := congrFun hScale t
  have hTranslate := congrFun
    (iteratedDeriv_comp_sub_const n expNegInvSqGlue (1 : ℝ)) (2 * t)
  rw [hScaleAt, hTranslate]
  ring

/-- Every derivative of `psi`, including its value, vanishes on the closed flat region. -/
theorem psi_iteratedDeriv_eq_zero_of_le_half (n : ℕ) {t : ℝ}
    (ht : t ≤ 1 / 2) :
    iteratedDeriv n psi t = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [psi_iteratedDeriv]
    norm_num [expNegInvSqGlue_iteratedDeriv_zero]
  · have hLocal : psi =ᶠ[nhds t] (fun _ : ℝ ↦ 0) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact psi_eq_zero_of_le_half (le_of_lt hy)
    rw [hLocal.iteratedDeriv_eq n]
    exact iteratedDeriv_fun_const_zero

/-- First derivative of `psi` vanishes on its closed flat region. -/
theorem psi_deriv_eq_zero_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    deriv psi t = 0 := by
  rw [← iteratedDeriv_one]
  exact psi_iteratedDeriv_eq_zero_of_le_half 1 ht

end

end BilevelLowerBound
