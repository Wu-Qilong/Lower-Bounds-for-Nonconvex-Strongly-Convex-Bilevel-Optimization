/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractorDerivatives
import BilevelLowerBoundLean.HardInstance
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Analytic properties of the compensated hard instance

This module proves the global order properties of the compact cutoff and then
uses them to identify the unique population lower solution.  The minimization
argument is value based: it does not merely show stationarity at the proposed
point, and it does not need a local convexity assumption.
-/

open scoped ContDiff RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

theorem cutoffTransition_nonneg (t : ℝ) :
    0 ≤ cutoffTransition t := by
  unfold cutoffTransition
  exact div_nonneg (expNegInvGlue.nonneg _) (cutoffTransition_denom_pos t).le

theorem cutoffTransition_le_one (t : ℝ) :
    cutoffTransition t ≤ 1 := by
  unfold cutoffTransition
  exact (div_le_one (cutoffTransition_denom_pos t)).2
    (le_add_of_nonneg_right (expNegInvGlue.nonneg _))

/-- The even compact cutoff takes values in the unit interval. -/
theorem cutoffWeight_nonneg (t : ℝ) : 0 ≤ cutoffWeight t := by
  rcases le_total 0 t with ht | ht
  · have hneg : -t ≤ 1 := by linarith
    unfold cutoffWeight
    rw [cutoffTransition_eq_zero_of_le_one hneg]
    linarith [cutoffTransition_le_one t]
  · have hself : t ≤ 1 := by linarith
    unfold cutoffWeight
    rw [cutoffTransition_eq_zero_of_le_one hself]
    linarith [cutoffTransition_le_one (-t)]

theorem cutoffWeight_le_one (t : ℝ) : cutoffWeight t ≤ 1 := by
  unfold cutoffWeight
  linarith [cutoffTransition_nonneg t, cutoffTransition_nonneg (-t)]

theorem abs_cutoffWeight_le_one (t : ℝ) : |cutoffWeight t| ≤ 1 := by
  rw [abs_of_nonneg (cutoffWeight_nonneg t)]
  exact cutoffWeight_le_one t

/-- The primitive used in the upper objective has the cutoff as its exact
derivative. -/
theorem cutoffPrimitive_hasDerivAt (v : ℝ) :
    HasDerivAt cutoffPrimitive (cutoffWeight v) v := by
  unfold cutoffPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (cutoffWeight_contDiff.continuous.intervalIntegrable 0 v)
    cutoffWeight_contDiff.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    cutoffWeight_contDiff.continuous.continuousAt

theorem cutoffPrimitive_deriv (v : ℝ) :
    deriv cutoffPrimitive v = cutoffWeight v :=
  (cutoffPrimitive_hasDerivAt v).deriv

/-- The bounded primitive is globally smooth. -/
theorem cutoffPrimitive_contDiff : ContDiff ℝ ∞ cutoffPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun v ↦ (cutoffPrimitive_hasDerivAt v).differentiableAt, ?_⟩
  have hDeriv : deriv cutoffPrimitive = cutoffWeight := by
    funext v
    exact cutoffPrimitive_deriv v
  rw [hDeriv]
  exact cutoffWeight_contDiff

theorem abs_cutoffPrimitive_deriv_le_one (v : ℝ) :
    |deriv cutoffPrimitive v| ≤ 1 := by
  rw [cutoffPrimitive_deriv]
  exact abs_cutoffWeight_le_one v

/-- The compact identity preserves the sign of its argument and cannot
increase its absolute value. -/
theorem abs_compactIdentity_le (η v : ℝ) :
    |compactIdentity η v| ≤ |v| := by
  unfold compactIdentity
  rw [abs_mul]
  have hw : |cutoffWeight (v / η)| ≤ 1 :=
    abs_cutoffWeight_le_one (v / η)
  nlinarith [abs_nonneg v]

theorem compactIdentity_mul_nonneg (η v : ℝ) :
    0 ≤ v * compactIdentity η v := by
  unfold compactIdentity
  rw [← mul_assoc, ← sq]
  exact mul_nonneg (sq_nonneg v) (cutoffWeight_nonneg (v / η))

/-- Radial soft projection is globally smooth whenever the radius is
nonzero.  The proof uses smoothness of the squared norm rather than of the
norm at the origin. -/
theorem softProjection_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (_hR : R ≠ 0) :
    ContDiff ℝ ∞ (softProjection R : E → E) := by
  have hRadicand : ContDiff ℝ ∞
      (fun z : E ↦ 1 + ‖z‖ ^ 2 / R ^ 2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).div_const (R ^ 2))
  have hPos : ∀ z : E, 1 + ‖z‖ ^ 2 / R ^ 2 ≠ 0 := by
    intro z
    have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  unfold softProjection
  exact ((hRadicand.sqrt hPos).inv (fun z ↦
    (Real.sqrt_pos.2 (by
      have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 :=
        div_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith)).ne')).smul contDiff_id

/-- The pseudo-Huber regularizer is globally smooth for nonzero radius. -/
theorem pseudoHuber_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam R : ℝ} (_hR : R ≠ 0) :
    ContDiff ℝ ∞ (pseudoHuber lam R : E → ℝ) := by
  have hRadicand : ContDiff ℝ ∞
      (fun z : E ↦ 1 + ‖z‖ ^ 2 / R ^ 2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).div_const (R ^ 2))
  have hPos : ∀ z : E, 1 + ‖z‖ ^ 2 / R ^ 2 ≠ 0 := by
    intro z
    have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  unfold pseudoHuber
  exact contDiff_const.mul ((hRadicand.sqrt hPos).sub contDiff_const)

/-- The compensated block is globally smooth when the frontier map is. -/
theorem compensatedBlock_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : η ≠ 0) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (fun p : E × ℝ ↦ compensatedBlock η θ p.1 p.2) := by
  unfold compensatedBlock
  have hTheta : ContDiff ℝ ∞ (fun p : E × ℝ ↦ θ p.1) :=
    hθ.comp contDiff_fst
  have hPsi : ContDiff ℝ ∞ (fun p : E × ℝ ↦ compactIdentity η p.2) :=
    (compactIdentity_contDiff hη).comp contDiff_snd
  exact (contDiff_const.mul (hTheta.pow 2)).sub (hTheta.mul hPsi)

/-- The entire scalar lower block is globally nonnegative. -/
theorem compensatedScalar_nonneg (η θ v : ℝ) :
    0 ≤ (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * θ ^ 2 -
      θ * compactIdentity η v := by
  let w := cutoffWeight (v / η)
  have hw0 : 0 ≤ w := cutoffWeight_nonneg (v / η)
  have hw1 : w ≤ 1 := cutoffWeight_le_one (v / η)
  change 0 ≤ (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * θ ^ 2 -
    θ * (v * w)
  by_cases hsign : 0 ≤ θ * v
  · have hprod : θ * v * w ≤ θ * v := by nlinarith
    nlinarith [sq_nonneg (v - θ)]
  · have hprod : θ * v * w ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hw0
    nlinarith [sq_nonneg v, sq_nonneg θ]

/-- Zero is attained by the scalar block only at `v = theta`. -/
theorem compensatedScalar_eq_zero_imp (η θ v : ℝ)
    (hzero : (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * θ ^ 2 -
      θ * compactIdentity η v = 0) :
    v = θ := by
  let w := cutoffWeight (v / η)
  have hw0 : 0 ≤ w := cutoffWeight_nonneg (v / η)
  have hw1 : w ≤ 1 := cutoffWeight_le_one (v / η)
  change (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * θ ^ 2 -
    θ * (v * w) = 0 at hzero
  by_cases hsign : 0 ≤ θ * v
  · have hprod : θ * v * w ≤ θ * v := by nlinarith
    have hsquare : (v - θ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (v - θ)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · have hprod : θ * v * w ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hw0
    have hv : v = 0 := by
      have : v ^ 2 = 0 := by
        nlinarith [sq_nonneg v, sq_nonneg θ]
      exact sq_eq_zero_iff.mp this
    have hθ : θ = 0 := by
      have : θ ^ 2 = 0 := by
        nlinarith [sq_nonneg v, sq_nonneg θ]
      exact sq_eq_zero_iff.mp this
    rw [hv, hθ]

/-- For a small frontier value, the scalar block has the unique minimizer
`v = theta` and minimum value zero. -/
theorem compensatedScalar_eq_zero_iff {η θ v : ℝ}
    (hη : 0 < η) (hθ : |θ| ≤ η) :
    (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * θ ^ 2 -
        θ * compactIdentity η v = 0 ↔ v = θ := by
  constructor
  · exact compensatedScalar_eq_zero_imp η θ v
  · intro hv
    subst v
    rw [compactIdentity_eq_self hη hθ]
    ring

/-- Completing the square separates the population lower objective into the
strong quadratic `z` block and the nonnegative compensated scalar block. -/
theorem populationLower_complete_square
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ η : ℝ} (hκ : κ ≠ 0) (θ : E → ℝ) (x z : E) (v : ℝ) :
    populationLower κ η θ x z v =
      -(κ / 2) * ‖x‖ ^ 2 + ‖z - κ • x‖ ^ 2 / (2 * κ) +
        ((1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * (θ z) ^ 2 -
          θ z * compactIdentity η v) := by
  unfold populationLower compensatedBlock
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_right, mul_pow, sq_abs, real_inner_comm x z]
  field_simp
  ring

/-- The proposed lower solution is a global minimizer. -/
theorem populationLower_minimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) (θ : E → ℝ) (x z : E) (v : ℝ)
    (hθ : |θ (κ • x)| ≤ η) :
    populationLower κ η θ x (κ • x) (θ (κ • x)) ≤
      populationLower κ η θ x z v := by
  rw [populationLower_at_proposed_solution hκ.ne' hη θ x hθ,
    populationLower_complete_square hκ.ne' θ x z v]
  have hquad : 0 ≤ ‖z - κ • x‖ ^ 2 / (2 * κ) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hscalar := compensatedScalar_nonneg η (θ z) v
  linarith

/-- The minimizer of the population lower objective is exactly
`(kappa * x, theta (kappa * x))`. -/
theorem populationLower_unique_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) (θ : E → ℝ) (x z : E) (v : ℝ)
    (hθ : |θ (κ • x)| ≤ η)
    (hmin : populationLower κ η θ x z v =
      populationLower κ η θ x (κ • x) (θ (κ • x))) :
    z = κ • x ∧ v = θ (κ • x) := by
  rw [populationLower_complete_square hκ.ne' θ x z v,
    populationLower_at_proposed_solution hκ.ne' hη θ x hθ] at hmin
  have hquad : 0 ≤ ‖z - κ • x‖ ^ 2 / (2 * κ) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hscalar := compensatedScalar_nonneg η (θ z) v
  have hquadZero : ‖z - κ • x‖ ^ 2 / (2 * κ) = 0 := by linarith
  have hnormZero : ‖z - κ • x‖ = 0 := by
    have hden : (2 * κ) ≠ 0 := by positivity
    have hsquare : ‖z - κ • x‖ ^ 2 = 0 :=
      (div_eq_zero_iff.mp hquadZero).resolve_right hden
    exact sq_eq_zero_iff.mp hsquare
  have hz : z = κ • x := sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  have hscalarZero :
      (1 / 2 : ℝ) * v ^ 2 + (1 / 2 : ℝ) * (θ z) ^ 2 -
        θ z * compactIdentity η v = 0 := by linarith
  have hv : v = θ z := compensatedScalar_eq_zero_imp η (θ z) v hscalarZero
  exact ⟨hz, hz ▸ hv⟩

end

end BilevelLowerBound
