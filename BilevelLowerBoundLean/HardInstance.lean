/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Analytic definitions of the bilevel hard instance

This module formalizes the exact value-level identities after the frontier
split: the compact identity cutoff, the soft projection and pseudo-Huber
regularizer, the compensated lower block, its Bernoulli population identity,
and the exact population hyper-objective after substituting the proposed lower
solution.

The hidden-coordinate map is kept abstract (`q : E -> ChainVector T`).  The
later Haar module will instantiate it with `U^T rho_R` without changing any of
the algebra proved here.
-/

open scoped ContDiff Interval
open MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- The transition `gamma_(1,2)`. -/
def cutoffTransition (t : ℝ) : ℝ :=
  expNegInvGlue (t - 1) /
    (expNegInvGlue (t - 1) + expNegInvGlue (2 - t))

theorem cutoffTransition_denom_pos (t : ℝ) :
    0 < expNegInvGlue (t - 1) + expNegInvGlue (2 - t) := by
  by_cases ht : 1 < t
  · exact add_pos_of_pos_of_nonneg
      (expNegInvGlue.pos_of_pos (by linarith))
      (expNegInvGlue.nonneg _)
  · exact add_pos_of_nonneg_of_pos
      (expNegInvGlue.nonneg _)
      (expNegInvGlue.pos_of_pos (by linarith))

@[simp]
theorem cutoffTransition_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) :
    cutoffTransition t = 0 := by
  unfold cutoffTransition
  rw [expNegInvGlue.zero_of_nonpos (by linarith), zero_div]

@[simp]
theorem cutoffTransition_eq_one_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    cutoffTransition t = 1 := by
  unfold cutoffTransition
  have hzero : expNegInvGlue (2 - t) = 0 :=
    expNegInvGlue.zero_of_nonpos (by linarith)
  rw [hzero, add_zero]
  exact div_self (ne_of_gt (expNegInvGlue.pos_of_pos (by linarith)))

theorem cutoffTransition_contDiff : ContDiff ℝ ∞ cutoffTransition := by
  unfold cutoffTransition
  exact (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).div
    ((expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).add
      (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)))
    (fun t ↦ (cutoffTransition_denom_pos t).ne')

/-- The paper's even cutoff `omega(t) = 1 - gamma_(1,2)(|t|)`. -/
def cutoffWeight (t : ℝ) : ℝ :=
  1 - (cutoffTransition t + cutoffTransition (-t))

theorem cutoffWeight_contDiff : ContDiff ℝ ∞ cutoffWeight := by
  unfold cutoffWeight
  exact contDiff_const.sub
    (cutoffTransition_contDiff.add
      (cutoffTransition_contDiff.comp contDiff_id.neg))

@[simp]
theorem cutoffWeight_eq_one_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    cutoffWeight t = 1 := by
  have htUpper : t ≤ 1 := (le_abs_self t).trans ht
  have htLower : -t ≤ 1 := by
    have hBounds := abs_le.mp ht
    linarith
  unfold cutoffWeight
  rw [cutoffTransition_eq_zero_of_le_one htUpper,
    cutoffTransition_eq_zero_of_le_one htLower]
  ring

/-- The cutoff is flat, including at the boundary of its identity region. -/
theorem cutoffWeight_deriv_eq_zero_of_abs_le_one {t : ℝ}
    (ht : |t| ≤ 1) :
    deriv cutoffWeight t = 0 := by
  let Z : Set ℝ := {u | deriv cutoffWeight u = 0}
  have hDerivContinuous : Continuous (deriv cutoffWeight) :=
    cutoffWeight_contDiff.continuous_deriv (by norm_num)
  have hZClosed : IsClosed Z :=
    isClosed_eq hDerivContinuous continuous_const
  have hInterior : Set.Ioo (-1 : ℝ) 1 ⊆ Z := by
    intro u hu
    have hLocal : cutoffWeight =ᶠ[nhds u] (fun _ : ℝ ↦ 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy
      exact cutoffWeight_eq_one_of_abs_le_one
        (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
    change deriv cutoffWeight u = 0
    rw [hLocal.deriv_eq]
    simp
  have hClosure : closure (Set.Ioo (-1 : ℝ) 1) ⊆ Z :=
    closure_minimal hInterior hZClosed
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp ht
  exact hClosure (by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact htIcc)

@[simp]
theorem cutoffWeight_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    cutoffWeight t = 0 := by
  rcases le_total 0 t with hpos | hneg
  · have htwo : 2 ≤ t := by simpa [abs_of_nonneg hpos] using ht
    have hnegOne : -t ≤ 1 := by linarith
    unfold cutoffWeight
    rw [cutoffTransition_eq_one_of_two_le htwo,
      cutoffTransition_eq_zero_of_le_one hnegOne]
    ring
  · have htwo : 2 ≤ -t := by simpa [abs_of_nonpos hneg] using ht
    have htOne : t ≤ 1 := by linarith
    unfold cutoffWeight
    rw [cutoffTransition_eq_zero_of_le_one htOne,
      cutoffTransition_eq_one_of_two_le htwo]
    ring

/-- The compact identity `psi_eta(v)`. -/
def compactIdentity (η v : ℝ) : ℝ :=
  v * cutoffWeight (v / η)

theorem compactIdentity_contDiff {η : ℝ} (_hη : η ≠ 0) :
    ContDiff ℝ ∞ (compactIdentity η) := by
  unfold compactIdentity
  exact contDiff_id.mul
    (cutoffWeight_contDiff.comp (contDiff_id.div_const η))

/-- The derivative of the compact identity is exactly one throughout the
closed identity region. -/
theorem compactIdentity_deriv_eq_one {η v : ℝ} (hη : 0 < η)
    (hv : |v| ≤ η) :
    deriv (compactIdentity η) v = 1 := by
  have hScaled : |v / η| ≤ 1 := by
    rw [abs_div, abs_of_pos hη]
    exact (div_le_one hη).2 hv
  have hwVal : cutoffWeight (v / η) = 1 :=
    cutoffWeight_eq_one_of_abs_le_one hScaled
  have hwDiff : DifferentiableAt ℝ cutoffWeight (v / η) :=
    cutoffWeight_contDiff.differentiable (by norm_num) (v / η)
  have hInnerDiff : DifferentiableAt ℝ (fun y : ℝ ↦ y / η) v :=
    (hasDerivAt_id v |>.div_const η).differentiableAt
  have hCompDiff :
      DifferentiableAt ℝ (fun y : ℝ ↦ cutoffWeight (y / η)) v :=
    show DifferentiableAt ℝ (cutoffWeight ∘ fun y : ℝ ↦ y / η) v from
      hwDiff.comp v hInnerDiff
  unfold compactIdentity
  have hMul := deriv_mul differentiableAt_id hCompDiff
  change deriv (fun y : ℝ ↦ y * cutoffWeight (y / η)) v =
    deriv id v * cutoffWeight (v / η) +
      id v * deriv (fun y : ℝ ↦ cutoffWeight (y / η)) v at hMul
  rw [hMul]
  have hCompDeriv :
      deriv (fun y : ℝ ↦ cutoffWeight (y / η)) v = 0 := by
    have hChain := deriv_comp v hwDiff hInnerDiff
    change deriv (fun y : ℝ ↦ cutoffWeight (y / η)) v =
      deriv cutoffWeight (v / η) *
        deriv (fun y : ℝ ↦ y / η) v at hChain
    rw [hChain, cutoffWeight_deriv_eq_zero_of_abs_le_one hScaled]
    ring
  rw [hCompDeriv, hwVal]
  simp

@[simp]
theorem compactIdentity_eq_self {η v : ℝ} (hη : 0 < η)
    (hv : |v| ≤ η) :
    compactIdentity η v = v := by
  unfold compactIdentity
  have hScaled : |v / η| ≤ 1 := by
    rw [abs_div, abs_of_pos hη]
    exact (div_le_one hη).2 hv
  rw [cutoffWeight_eq_one_of_abs_le_one hScaled, mul_one]

@[simp]
theorem compactIdentity_eq_zero {η v : ℝ} (hη : 0 < η)
    (hv : 2 * η ≤ |v|) :
    compactIdentity η v = 0 := by
  unfold compactIdentity
  have hScaled : 2 ≤ |v / η| := by
    rw [abs_div, abs_of_pos hη]
    exact (le_div_iff₀ hη).2 (by nlinarith)
  rw [cutoffWeight_eq_zero_of_two_le_abs hScaled, mul_zero]

/-- The bounded primitive `ell(v) = integral_0^v omega(s) ds`. -/
def cutoffPrimitive (v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..v, cutoffWeight s

@[simp]
theorem cutoffPrimitive_zero : cutoffPrimitive 0 = 0 := by
  simp [cutoffPrimitive]

/-- On `[-1,1]`, the primitive is exactly the identity. -/
theorem cutoffPrimitive_eq_self {v : ℝ} (hv : |v| ≤ 1) :
    cutoffPrimitive v = v := by
  unfold cutoffPrimitive
  have hEq :
      (∫ s in (0 : ℝ)..v, cutoffWeight s) =
        ∫ _s in (0 : ℝ)..v, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply cutoffWeight_eq_one_of_abs_le_one
    have hsBounds := Set.mem_uIcc.mp hs
    rcases hsBounds with hs | hs
    · rw [abs_of_nonneg hs.1]
      exact hs.2.trans ((le_abs_self v).trans hv)
    · have hv0 : v ≤ 0 := hs.1
          |>.trans hs.2
      rw [abs_of_nonpos hs.2]
      have hnegv : -v ≤ 1 := by
        simpa [abs_of_nonpos hv0] using hv
      linarith
  rw [hEq, intervalIntegral.integral_const]
  simp

/-- Radial soft projection into the open ball of radius `R`. -/
def softProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (z : E) : E :=
  (Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2))⁻¹ • z

@[simp]
theorem softProjection_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) :
    softProjection R (0 : E) = 0 := by
  simp [softProjection]

/-- Every soft-projected vector lies strictly inside the radius-`R` ball. -/
theorem norm_softProjection_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖softProjection R z‖ < R := by
  let s : ℝ := Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2)
  have hArg : 0 < 1 + ‖z‖ ^ 2 / R ^ 2 := by
    have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hs : 0 < s := Real.sqrt_pos.2 hArg
  have hsSq : s ^ 2 = 1 + ‖z‖ ^ 2 / R ^ 2 :=
    Real.sq_sqrt hArg.le
  have hRsSq : (R * s) ^ 2 = R ^ 2 + ‖z‖ ^ 2 := by
    rw [mul_pow, hsSq]
    field_simp
  have hSq : ‖z‖ ^ 2 < (R * s) ^ 2 := by
    rw [hRsSq]
    nlinarith [sq_pos_of_pos hR]
  have hRaw : ‖z‖ < R * s :=
    (sq_lt_sq₀ (norm_nonneg z) (mul_nonneg hR.le hs.le)).mp hSq
  unfold softProjection
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
  change s⁻¹ * ‖z‖ < R
  rw [inv_mul_eq_div, div_lt_iff₀ hs]
  exact hRaw

theorem norm_softProjection_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖softProjection R z‖ ≤ R :=
  (norm_softProjection_lt hR z).le

/-- The pseudo-Huber regularizer used to keep the output probe bounded. -/
def pseudoHuber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam R : ℝ) (z : E) : ℝ :=
  lam * R ^ 2 * (Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2) - 1)

@[simp]
theorem pseudoHuber_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam R : ℝ) :
    pseudoHuber lam R (0 : E) = 0 := by
  simp [pseudoHuber]

theorem pseudoHuber_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam R : ℝ} (hlam : 0 ≤ lam) (z : E) :
    0 ≤ pseudoHuber lam R z := by
  unfold pseudoHuber
  have hRad : 1 ≤ Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2) := by
    have hArg : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 / R ^ 2 :=
      le_add_of_nonneg_right
        (div_nonneg (sq_nonneg ‖z‖) (sq_nonneg R))
    have hSqrt := Real.sqrt_le_sqrt hArg
    simpa using hSqrt
  exact mul_nonneg (mul_nonneg hlam (sq_nonneg R)) (sub_nonneg.mpr hRad)

/-- The compensated block `R_U(z,v)`. -/
def compensatedBlock {E : Type*} (η : ℝ) (θ : E → ℝ) (z : E) (v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (θ z) ^ 2 - θ z * compactIdentity η v

/-- In the identity region, the quadratic `v` term and compensation cancel
exactly at `v = theta(z)`. -/
theorem compensatedBlock_cancels {E : Type*} {η : ℝ} {θ : E → ℝ}
    (hη : 0 < η) (z : E) (hθ : |θ z| ≤ η) :
    (1 / 2 : ℝ) * (θ z) ^ 2 + compensatedBlock η θ z (θ z) = 0 := by
  rw [compensatedBlock, compactIdentity_eq_self hη hθ]
  ring

/-- The compensated scalar block is stationary at `v = theta(z)`. -/
theorem compensatedSlice_deriv_at_frontier {E : Type*} {η : ℝ}
    {θ : E → ℝ} (hη : 0 < η) (z : E) (hθ : |θ z| ≤ η) :
    deriv (fun v : ℝ ↦
      (1 / 2 : ℝ) * v ^ 2 + compensatedBlock η θ z v) (θ z) = 0 := by
  have hPsiDiff : DifferentiableAt ℝ (compactIdentity η) (θ z) :=
    (compactIdentity_contDiff hη.ne').differentiable (by norm_num) (θ z)
  have hPsiDeriv : deriv (compactIdentity η) (θ z) = 1 :=
    compactIdentity_deriv_eq_one hη hθ
  have hSquareDiff : DifferentiableAt ℝ (fun v : ℝ ↦ v ^ 2) (θ z) := by
    fun_prop
  have hLeft := deriv_const_mul (c := (1 / 2 : ℝ)) hSquareDiff
  have hRight := deriv_const_mul (c := θ z) hPsiDiff
  have hLeftDiff : DifferentiableAt ℝ
      (fun v : ℝ ↦ (1 / 2 : ℝ) * v ^ 2) (θ z) := by
    fun_prop
  have hRightDiff : DifferentiableAt ℝ
      (fun v : ℝ ↦ θ z * compactIdentity η v) (θ z) := by
    fun_prop
  have hSub : DifferentiableAt ℝ
      (fun v : ℝ ↦ (1 / 2 : ℝ) * (θ z) ^ 2 -
        θ z * compactIdentity η v) (θ z) := by
    fun_prop
  unfold compensatedBlock
  have hAdd := deriv_add hLeftDiff hSub
  change deriv (fun v : ℝ ↦ (1 / 2 : ℝ) * v ^ 2 +
      ((1 / 2 : ℝ) * (θ z) ^ 2 - θ z * compactIdentity η v)) (θ z) =
    deriv (fun v : ℝ ↦ (1 / 2 : ℝ) * v ^ 2) (θ z) +
      deriv (fun v : ℝ ↦ (1 / 2 : ℝ) * (θ z) ^ 2 -
        θ z * compactIdentity η v) (θ z) at hAdd
  rw [hAdd, hLeft]
  have hConst : DifferentiableAt ℝ
      (fun _v : ℝ ↦ (1 / 2 : ℝ) * (θ z) ^ 2) (θ z) :=
    differentiableAt_const _
  have hSubtract := deriv_sub hConst hRightDiff
  change deriv (fun v : ℝ ↦ (1 / 2 : ℝ) * (θ z) ^ 2 -
      θ z * compactIdentity η v) (θ z) =
    deriv (fun _v : ℝ ↦ (1 / 2 : ℝ) * (θ z) ^ 2) (θ z) -
      deriv (fun v : ℝ ↦ θ z * compactIdentity η v) (θ z) at hSubtract
  rw [hSubtract, hRight, hPsiDeriv]
  simp

/-- Population lower objective, with the hidden frontier represented by
`theta`. -/
def populationLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ η : ℝ) (θ : E → ℝ) (x z : E) (v : ℝ) : ℝ :=
  ‖z‖ ^ 2 / (2 * κ) - inner ℝ x z +
    (1 / 2 : ℝ) * v ^ 2 + compensatedBlock η θ z v

/-- Sample lower objective: only the compensated frontier is multiplied by
`xi/p`. -/
def sampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ η p ξ : ℝ) (θ : E → ℝ) (x z : E) (v : ℝ) : ℝ :=
  ‖z‖ ^ 2 / (2 * κ) - inner ℝ x z +
    (1 / 2 : ℝ) * v ^ 2 + (ξ / p) * compensatedBlock η θ z v

/-- The Bernoulli sample objective averages exactly to the population lower
objective. -/
theorem sampleLower_bernoulli_population
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ η p : ℝ} (hp : p ≠ 0) (θ : E → ℝ) (x z : E) (v : ℝ) :
    p * sampleLower κ η p 1 θ x z v +
        (1 - p) * sampleLower κ η p 0 θ x z v =
      populationLower κ η θ x z v := by
  unfold sampleLower populationLower
  field_simp
  ring

/-- Value of the population lower objective at the proposed exact solution.
The remaining optimization proof will show this stationary pair is the unique
minimizer once the small-Hessian estimate is available. -/
theorem populationLower_at_proposed_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ η : ℝ} (_hκ : κ ≠ 0) (hη : 0 < η) (θ : E → ℝ) (x : E)
    (hθ : |θ (κ • x)| ≤ η) :
    populationLower κ η θ x (κ • x) (θ (κ • x)) =
      -(κ / 2) * ‖x‖ ^ 2 := by
  unfold populationLower
  unfold compensatedBlock
  rw [compactIdentity_eq_self hη hθ]
  simp only [norm_smul, Real.norm_eq_abs]
  have habs : |κ| ^ 2 = κ ^ 2 := sq_abs κ
  rw [mul_pow, habs, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Upper objective before minimizing the lower level. -/
def hardUpper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (η lam R : ℝ) (q : E → ChainVector T)
    (z : E) (v : ℝ) : ℝ :=
  visibleChain η (q z) + cutoffPrimitive v + pseudoHuber lam R z

/-- The exact population hyper-objective identity `A + b = H` at the proposed
lower solution. -/
theorem hardUpper_at_proposed_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {η κ lam R : ℝ} (_hη : 0 < η) (q : E → ChainVector T)
    (x : E) (hSmallEta : η ≤ 1)
    (hFrontier : |frontierExtractor η (q (κ • x))| ≤ η) :
    hardUpper η lam R q (κ • x) (frontierExtractor η (q (κ • x))) =
      scaledChain η (q (κ • x)) + pseudoHuber lam R (κ • x) := by
  unfold hardUpper visibleChain
  rw [cutoffPrimitive_eq_self
    (hFrontier.trans hSmallEta)]
  ring

end

end BilevelLowerBound
