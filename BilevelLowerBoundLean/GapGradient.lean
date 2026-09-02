/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ProgressBound
import BilevelLowerBoundLean.ConditionWitness
import BilevelLowerBoundLean.HardObjectiveRegularity

/-!
# Initial gap and amplified gradient

This module formalizes Lemma `gap-gradient`.  The proof is normalized to the
unit-scale zero chain.  In the central ball, one hidden frontier component
cannot be cancelled by the radial correction or regularizer.  Outside that
ball, the pseudo-Huber gradient dominates the contracted chain gradient.
-/

open Filter Function Real Set
open InnerProductSpace
open scoped BigOperators ContDiff Gradient InnerProductSpace
  RealInnerProductSpace Topology

namespace BilevelLowerBound

noncomputable section

/-! ## Frontier coordinate selected by unfinished progress -/

theorem exists_unscaled_frontier_of_progress_quarter_lt
    {T : ℕ} {q : ChainVector T}
    (hunfinished : progress (1 / 4 : ℝ) q < T) :
    ∃ j : Fin T,
      |q j| ≤ 1 ∧
      gradient (unscaledChain : ChainVector T → ℝ) q j ≤ -1 := by
  have hprog : progress 1 q < T :=
    lt_of_le_of_lt
      (progress_anti_threshold (c₁ := (1 / 4 : ℝ))
        (c₂ := 1) (by norm_num))
      hunfinished
  let j : Fin T := ⟨progress 1 q, hprog⟩
  refine ⟨j, ?_, unscaledChain_frontier_gradient_le q j rfl⟩
  exact abs_le_threshold_of_progress_le (le_refl (progress 1 q)) j
    (by simp [j])

/-! ## Sharper first-derivative and radial estimates -/

/-- The Jacobian of the soft projection has norm at most its radial scale
`1/s`. -/
theorem norm_fderiv_softProjection_le_softScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖fderiv ℝ (softProjection R : E → E) z‖ ≤ softScale R z := by
  let a : ℝ := softScale R z
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact (softScale_pos hR.ne' z).le
  apply ContinuousLinearMap.opNorm_le_bound _ ha0
  intro h
  rw [fderiv_softProjection_apply hR.ne' z h]
  let c : ℝ := a ^ 3 / R ^ 2 * inner ℝ z h
  change ‖a • h - c • z‖ ≤ a * ‖h‖
  have haz : a * ‖z‖ ≤ R := by
    dsimp [a]
    exact softScale_mul_norm_le hR z
  have hazsq : a ^ 2 * ‖z‖ ^ 2 ≤ R ^ 2 := by
    have hsquare : (a * ‖z‖) ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (mul_nonneg ha0 (norm_nonneg z)) hR.le).2 haz
    nlinarith
  have hcoef : 0 ≤
      2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4 := by
    rw [show 2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4 =
      (a ^ 4 / R ^ 4) *
        (2 * R ^ 2 - a ^ 2 * ‖z‖ ^ 2) by
          field_simp [hR.ne']]
    exact mul_nonneg (by positivity) (by nlinarith [sq_nonneg R])
  have hsquared : ‖a • h - c • z‖ ^ 2 ≤ (a * ‖h‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm z h]
    rw [show (|c| * ‖z‖) ^ 2 = c ^ 2 * ‖z‖ ^ 2 by
      rw [mul_pow, sq_abs]]
    dsimp [c]
    have hdrop := mul_nonneg hcoef (sq_nonneg (inner ℝ z h))
    calc
      _ = a ^ 2 * ‖h‖ ^ 2 -
          (2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4) *
            (inner ℝ z h) ^ 2 := by
        field_simp [hR.ne']
        ring
      _ ≤ a ^ 2 * ‖h‖ ^ 2 := sub_le_self _ hdrop
      _ = (a * ‖h‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha0 (norm_nonneg h))).1
    hsquared

theorem norm_softProjection_le_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    ‖softProjection R z‖ ≤ ‖z‖ := by
  rw [softProjection_eq_softScale_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (softScale_pos hR z)]
  exact mul_le_of_le_one_left (norm_nonneg z)
    (softScale_le_one hR z)

/-- In the central half-ball, `1/s >= 5/6`.  This rational estimate is
slightly weaker than the paper's exact `2/sqrt(5)` and is sufficient for the
same final constant. -/
theorem five_sixths_le_softScale_of_norm_le_half
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {z : E} (hz : ‖z‖ ≤ R / 2) :
    5 / 6 ≤ softScale R z := by
  let s : ℝ := Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = 1 + ‖z‖ ^ 2 / R ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hzsq : ‖z‖ ^ 2 ≤ R ^ 2 / 4 := by
    have := (sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ R / 2)).2 hz
    nlinarith
  have hratio : ‖z‖ ^ 2 / R ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith
  have hsle : s ≤ 6 / 5 := by
    apply (sq_le_sq₀ hspos.le (by norm_num)).1
    rw [hsq]
    nlinarith
  unfold softScale
  change 5 / 6 ≤ s⁻¹
  rw [inv_eq_one_div, le_div_iff₀ hspos]
  nlinarith

/-- Outside the central half-ball, `1/s < 9/10`. -/
theorem softScale_lt_nine_tenths_of_half_lt_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {z : E} (hz : R / 2 < ‖z‖) :
    softScale R z < 9 / 10 := by
  let s : ℝ := Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = 1 + ‖z‖ ^ 2 / R ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hzsq : R ^ 2 / 4 < ‖z‖ ^ 2 := by
    have := (sq_lt_sq₀ (by positivity : 0 ≤ R / 2) (norm_nonneg z)).2 hz
    nlinarith
  have hratio : 1 / 4 < ‖z‖ ^ 2 / R ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hR)).2
    nlinarith
  have hslarge : 10 / 9 < s := by
    apply (sq_lt_sq₀ (by norm_num) hspos.le).1
    rw [hsq]
    nlinarith
  unfold softScale
  change s⁻¹ < 9 / 10
  rw [inv_eq_one_div, div_lt_iff₀ hspos]
  nlinarith

/-- Outside the central half-ball, the soft-projected radius is larger than
`2R/5`. -/
theorem two_fifths_mul_lt_norm_softProjection_of_half_lt_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {z : E} (hz : R / 2 < ‖z‖) :
    2 * R / 5 < ‖softProjection R z‖ := by
  let s : ℝ := Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = 1 + ‖z‖ ^ 2 / R ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hzsq : R ^ 2 / 4 < ‖z‖ ^ 2 := by
    have := (sq_lt_sq₀ (by positivity : 0 ≤ R / 2) (norm_nonneg z)).2 hz
    nlinarith
  have hcrossSq : (2 * R * s) ^ 2 < (5 * ‖z‖) ^ 2 := by
    have hid : 4 * R ^ 2 * s ^ 2 =
        4 * R ^ 2 + 4 * ‖z‖ ^ 2 := by
      rw [hsq]
      field_simp [hR.ne']
    nlinarith [sq_pos_of_pos hR]
  have hcross : 2 * R * s < 5 * ‖z‖ := by
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp (by
      simpa [mul_pow] using hcrossSq)
  rw [softProjection_eq_softScale_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (softScale_pos hR.ne' z)]
  change 2 * R / 5 < s⁻¹ * ‖z‖
  rw [inv_mul_eq_div]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5) hspos).2
  nlinarith

/-! ## Normalized hyper-objective and its exact gradient -/

theorem real_inner_fderiv_softProjection_comm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z x y : E) :
    inner ℝ (fderiv ℝ (softProjection R : E → E) z x) y =
      inner ℝ x (fderiv ℝ (softProjection R : E → E) z y) := by
  rw [fderiv_softProjection_apply hR, fderiv_softProjection_apply hR]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm z x]
  ring

theorem real_inner_frame_eq_transpose
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (J : ChainVector T →ₗᵢ[ℝ] E) (q : ChainVector T) (z : E) :
    inner ℝ (J q) z = inner ℝ q (hiddenFrameTranspose J z) := by
  simpa [hiddenFrameTranspose] using
    (J.toContinuousLinearMap.adjoint_inner_right q z).symm

theorem hiddenFrameTranspose_coordinate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (J : ChainVector T →ₗᵢ[ℝ] E) (z : E) (j : Fin T) :
    hiddenFrameTranspose J z j =
      inner ℝ (J (EuclideanSpace.single j 1)) z := by
  have hframe := real_inner_frame_eq_transpose J
    (EuclideanSpace.single j (1 : ℝ)) z
  rw [EuclideanSpace.inner_single_left] at hframe
  simpa using hframe.symm

/-- Unit-scale hyper-objective after normalizing `kappa x = eta w`. -/
def normalizedHardObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (lam R : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) (w : E) : ℝ :=
  unscaledChain (hiddenFrameTranspose J (softProjection R w)) +
    pseudoHuber lam R w

/-- The vector formula `J_rho^T U grad F + lam r`; symmetry of the radial
Jacobian lets us write it without an explicit adjoint. -/
def normalizedHardGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (lam R : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) (w : E) : E :=
  let r := softProjection R w
  let q := hiddenFrameTranspose J r
  fderiv ℝ (softProjection R : E → E) w
      (J (gradient (unscaledChain : ChainVector T → ℝ) q)) +
    lam • r

theorem gradient_normalizedHardObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {R : ℝ} (hR : R ≠ 0)
    (lam : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) (w : E) :
    gradient (normalizedHardObjective lam R J) w =
      normalizedHardGradient lam R J w := by
  let innerMap : E → ChainVector T :=
    fun y ↦ hiddenFrameTranspose J (softProjection R y)
  let chainMap : E → ℝ :=
    (unscaledChain : ChainVector T → ℝ) ∘ innerMap
  let r : E := softProjection R w
  let q : ChainVector T := innerMap w
  let g : ChainVector T :=
    gradient (unscaledChain : ChainVector T → ℝ) q
  have hrDiff : DifferentiableAt ℝ (softProjection R : E → E) w :=
    (softProjection_contDiff hR).differentiable (by simp) w
  have hinnerDiff : DifferentiableAt ℝ innerMap w :=
    (hiddenFrameTranspose J).differentiableAt.comp w hrDiff
  have houterDiff : DifferentiableAt ℝ
      (unscaledChain : ChainVector T → ℝ) q :=
    ContDiffAt.differentiableAt
      (unscaledChain_contDiff (T := T)).contDiffAt (by simp)
  have hchainDiff : DifferentiableAt ℝ chainMap w :=
    houterDiff.comp w hinnerDiff
  have hhuberDiff : DifferentiableAt ℝ (pseudoHuber lam R : E → ℝ) w :=
    (pseudoHuber_contDiff hR).differentiable (by simp) w
  have hinnerFderiv :
      fderiv ℝ innerMap w =
        (hiddenFrameTranspose J).comp
          (fderiv ℝ (softProjection R : E → E) w) := by
    exact ((hiddenFrameTranspose J).hasFDerivAt.comp w
      hrDiff.hasFDerivAt).fderiv
  have hchainFderiv :
      fderiv ℝ chainMap w =
        (fderiv ℝ (unscaledChain : ChainVector T → ℝ) q).comp
          (fderiv ℝ innerMap w) := by
    exact (houterDiff.hasFDerivAt.comp w hinnerDiff.hasFDerivAt).fderiv
  apply (toDual ℝ E).injective
  rw [toDual_gradient]
  ext h
  change fderiv ℝ (chainMap + (pseudoHuber lam R : E → ℝ)) w h =
    inner ℝ (normalizedHardGradient lam R J w) h
  rw [fderiv_add hchainDiff hhuberDiff]
  rw [hchainFderiv, hinnerFderiv, fderiv_pseudoHuber hR]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply]
  rw [← toDual_gradient]
  change inner ℝ g
      (hiddenFrameTranspose J
        (fderiv ℝ (softProjection R : E → E) w h)) +
      lam * inner ℝ r h =
    inner ℝ
      (fderiv ℝ (softProjection R : E → E) w (J g) + lam • r) h
  rw [inner_add_left, inner_smul_left]
  rw [real_inner_fderiv_softProjection_comm hR]
  rw [real_inner_frame_eq_transpose]
  simp

theorem real_inner_normalizedHardGradient_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {R : ℝ} (hR : R ≠ 0)
    (lam : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) (w : E)
    (j : Fin T) :
    let r := softProjection R w
    let q := hiddenFrameTranspose J r
    let g := gradient (unscaledChain : ChainVector T → ℝ) q
    let a := softScale R w
    let u := J (EuclideanSpace.single j (1 : ℝ))
    inner ℝ u (normalizedHardGradient lam R J w) =
      a * g j -
        (a / R ^ 2 * inner ℝ r (J g) * q j) +
        lam * q j := by
  dsimp only
  unfold normalizedHardGradient
  dsimp only
  rw [fderiv_softProjection_apply hR]
  simp only [inner_add_right, inner_sub_right, inner_smul_right]
  rw [J.inner_map_map]
  rw [EuclideanSpace.inner_single_left]
  rw [hiddenFrameTranspose_coordinate]
  rw [softProjection_eq_softScale_smul]
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-! ## The central-ball lower bound -/

theorem norm_normalizedHardGradient_gt_half_of_norm_le_half
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (w : E)
    (hunfinished :
      progress (1 / 4 : ℝ)
        (hiddenFrameTranspose J
          (softProjection (230 * Real.sqrt T) w)) < T)
    (hw : ‖w‖ ≤ (230 * Real.sqrt T) / 2) :
    1 / 2 <
      ‖normalizedHardGradient (1 / 4) (230 * Real.sqrt T) J w‖ := by
  let R : ℝ := 230 * Real.sqrt T
  let r : E := softProjection R w
  let q : ChainVector T := hiddenFrameTranspose J r
  let g : ChainVector T :=
    gradient (unscaledChain : ChainVector T → ℝ) q
  let a : ℝ := softScale R w
  have hsqrt : 0 < Real.sqrt T := by
    exact lt_of_lt_of_le (by norm_num) (one_le_sqrt_nat hT)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hfront : ∃ j : Fin T, |q j| ≤ 1 ∧ g j ≤ -1 := by
    apply exists_unscaled_frontier_of_progress_quarter_lt
    simpa [R, r, q] using hunfinished
  obtain ⟨j, hqj, hgj⟩ := hfront
  let u : E := J (EuclideanSpace.single j (1 : ℝ))
  let corr : ℝ := a / R ^ 2 * inner ℝ r (J g) * q j
  have ha0 : 0 ≤ a := (softScale_pos hR.ne' w).le
  have ha1 : a ≤ 1 := softScale_le_one hR.ne' w
  have haLower : 5 / 6 ≤ a := by
    apply five_sixths_le_softScale_of_norm_le_half hR
    simpa [R] using hw
  have hrnorm : ‖r‖ ≤ R / 2 := by
    calc
      ‖r‖ ≤ ‖w‖ := by
        dsimp [r]
        exact norm_softProjection_le_norm hR.ne' w
      _ ≤ R / 2 := by simpa [R] using hw
  have hgnorm : ‖g‖ ≤ 23 * Real.sqrt T := by
    dsimp [g]
    exact norm_unscaledChain_gradient_le q
  have hJgnorm : ‖J g‖ ≤ 23 * Real.sqrt T := by
    rw [J.norm_map]
    exact hgnorm
  have hinner :
      |inner ℝ r (J g)| ≤ (R / 2) * (23 * Real.sqrt T) := by
    calc
      |inner ℝ r (J g)| ≤ ‖r‖ * ‖J g‖ :=
        abs_real_inner_le_norm r (J g)
      _ ≤ (R / 2) * (23 * Real.sqrt T) := by
        exact mul_le_mul hrnorm hJgnorm (norm_nonneg _) (by positivity)
  have hcoef : |a / R ^ 2| ≤ 1 / R ^ 2 := by
    rw [abs_div, abs_pow, abs_of_nonneg ha0, abs_of_pos hR]
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 ha1
  have hcorr : |corr| ≤ 1 / 20 := by
    dsimp [corr]
    rw [abs_mul, abs_mul]
    calc
      |a / R ^ 2| * |inner ℝ r (J g)| * |q j|
          ≤ (1 / R ^ 2) * ((R / 2) * (23 * Real.sqrt T)) * 1 := by
            gcongr
      _ = 1 / 20 := by
        dsimp [R]
        field_simp [hsqrt.ne']
        ring
  have hfrontTerm : a ≤ |a * g j| := by
    have hmul : a * g j ≤ a * (-1) :=
      mul_le_mul_of_nonneg_left hgj ha0
    have hneg : a ≤ -(a * g j) := by
      nlinarith
    exact hneg.trans (neg_le_abs (a * g j))
  have hregTerm : |(1 / 4 : ℝ) * q j| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    nlinarith
  have hcomponent :
      inner ℝ u
          (normalizedHardGradient (1 / 4) R J w) =
        a * g j - corr + (1 / 4) * q j := by
    simpa [u, corr, r, q, g, a] using
      (real_inner_normalizedHardGradient_frontier
        hR.ne' (1 / 4) J w j)
  have htriangle :
      |a * g j| ≤
        |a * g j - corr + (1 / 4) * q j| +
          |corr| + |(1 / 4) * q j| := by
    calc
      |a * g j| =
          |(a * g j - corr + (1 / 4) * q j) + corr -
            (1 / 4) * q j| := by ring_nf
      _ ≤ |(a * g j - corr + (1 / 4) * q j) + corr| +
          |(1 / 4) * q j| := abs_sub _ _
      _ ≤ (|a * g j - corr + (1 / 4) * q j| + |corr|) +
          |(1 / 4) * q j| := by
            gcongr
            exact abs_add_le _ _
      _ = |a * g j - corr + (1 / 4) * q j| +
          |corr| + |(1 / 4) * q j| := by ring
  have habsComponent :
      1 / 2 < |a * g j - corr + (1 / 4) * q j| := by
    nlinarith
  have huNorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [J.norm_map, PiLp.norm_single]
    norm_num
  have hinnerLower :
      1 / 2 <
        |inner ℝ u (normalizedHardGradient (1 / 4) R J w)| := by
    rw [hcomponent]
    exact habsComponent
  have hCauchy :=
    abs_real_inner_le_norm u
      (normalizedHardGradient (1 / 4) R J w)
  rw [huNorm, one_mul] at hCauchy
  exact lt_of_lt_of_le hinnerLower hCauchy

/-! ## The exterior lower bound -/

theorem norm_normalizedHardGradient_gt_half_of_half_lt_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (w : E)
    (hw : (230 * Real.sqrt T) / 2 < ‖w‖) :
    1 / 2 <
      ‖normalizedHardGradient (1 / 4) (230 * Real.sqrt T) J w‖ := by
  let R : ℝ := 230 * Real.sqrt T
  let r : E := softProjection R w
  let q : ChainVector T := hiddenFrameTranspose J r
  let g : ChainVector T :=
    gradient (unscaledChain : ChainVector T → ℝ) q
  let a : ℝ := softScale R w
  let D : E →L[ℝ] E := fderiv ℝ (softProjection R : E → E) w
  let chainPart : E := D (J g)
  let radialPart : E := (1 / 4 : ℝ) • r
  have hsqrtOne : 1 ≤ Real.sqrt T := one_le_sqrt_nat hT
  have hsqrt : 0 < Real.sqrt T := lt_of_lt_of_le (by norm_num) hsqrtOne
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hwR : R / 2 < ‖w‖ := by simpa [R] using hw
  have haUpper : a < 9 / 10 := by
    dsimp [a]
    exact softScale_lt_nine_tenths_of_half_lt_norm hR hwR
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact (softScale_pos hR.ne' w).le
  have hrLower : 2 * R / 5 < ‖r‖ := by
    dsimp [r]
    exact two_fifths_mul_lt_norm_softProjection_of_half_lt_norm hR hwR
  have hDnorm : ‖D‖ ≤ a := by
    dsimp [D, a]
    exact norm_fderiv_softProjection_le_softScale hR w
  have hgnorm : ‖g‖ ≤ 23 * Real.sqrt T := by
    dsimp [g]
    exact norm_unscaledChain_gradient_le q
  have hJgnorm : ‖J g‖ ≤ 23 * Real.sqrt T := by
    rw [J.norm_map]
    exact hgnorm
  have hchainLe : ‖chainPart‖ ≤ a * (23 * Real.sqrt T) := by
    calc
      ‖chainPart‖ ≤ ‖D‖ * ‖J g‖ := by
        dsimp [chainPart]
        exact D.le_opNorm (J g)
      _ ≤ a * (23 * Real.sqrt T) := by
        exact mul_le_mul hDnorm hJgnorm (norm_nonneg _) ha0
  have hchainLt :
      ‖chainPart‖ < (9 / 10) * (23 * Real.sqrt T) := by
    exact hchainLe.trans_lt
      (mul_lt_mul_of_pos_right haUpper (by positivity))
  have hradialLower : 23 * Real.sqrt T < ‖radialPart‖ := by
    dsimp [radialPart]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    dsimp [R] at hrLower
    nlinarith
  have hdecomposition :
      normalizedHardGradient (1 / 4) R J w =
        chainPart + radialPart := by
    simp [normalizedHardGradient, chainPart, radialPart, D, g, q, r]
  have hreverse :
      ‖radialPart‖ ≤
        ‖normalizedHardGradient (1 / 4) R J w‖ +
          ‖chainPart‖ := by
    calc
      ‖radialPart‖ =
          ‖normalizedHardGradient (1 / 4) R J w - chainPart‖ := by
            rw [hdecomposition]
            congr 1
            abel
      _ ≤ ‖normalizedHardGradient (1 / 4) R J w‖ +
          ‖chainPart‖ := norm_sub_le _ _
  nlinarith

/-! ## Uniform normalized gradient gap -/

theorem norm_normalizedHardGradient_gt_half
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (w : E)
    (hunfinished :
      progress (1 / 4 : ℝ)
        (hiddenFrameTranspose J
          (softProjection (230 * Real.sqrt T) w)) < T) :
    1 / 2 <
      ‖normalizedHardGradient (1 / 4) (230 * Real.sqrt T) J w‖ := by
  rcases le_or_gt ‖w‖ ((230 * Real.sqrt T) / 2) with hw | hw
  · exact norm_normalizedHardGradient_gt_half_of_norm_le_half
      hT J w hunfinished hw
  · exact norm_normalizedHardGradient_gt_half_of_half_lt_norm
      hT J w hw

theorem norm_gradient_normalizedHardObjective_gt_half
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (w : E)
    (hunfinished :
      progress (1 / 4 : ℝ)
        (hiddenFrameTranspose J
          (softProjection (230 * Real.sqrt T) w)) < T) :
    1 / 2 <
      ‖gradient
        (normalizedHardObjective (1 / 4) (230 * Real.sqrt T) J) w‖ := by
  rw [gradient_normalizedHardObjective (by
    have := one_le_sqrt_nat hT
    positivity)]
  exact norm_normalizedHardGradient_gt_half hT J w hunfinished

/-! ## Scaling back to the bilevel hyper-objective -/

theorem softScale_mul_radius_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {eta R : ℝ} (heta : 0 < eta) (hR : R ≠ 0) (z : E) :
    softScale (eta * R) (eta • z) = softScale R z := by
  unfold softScale
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos heta]
  field_simp [heta.ne', hR]

theorem softProjection_mul_radius_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {eta R : ℝ} (heta : 0 < eta) (hR : R ≠ 0) (z : E) :
    softProjection (eta * R) (eta • z) =
      eta • softProjection R z := by
  rw [softProjection_eq_softScale_smul,
    softProjection_eq_softScale_smul,
    softScale_mul_radius_smul heta hR]
  simp only [smul_smul]
  congr 1
  ring

theorem pseudoHuber_mul_radius_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta R lam : ℝ} (heta : 0 < eta) (hR : R ≠ 0) (z : E) :
    pseudoHuber lam (eta * R) (eta • z) =
      eta ^ 2 * pseudoHuber lam R z := by
  unfold pseudoHuber
  have hrad :
      1 + ‖eta • z‖ ^ 2 / (eta * R) ^ 2 =
        1 + ‖z‖ ^ 2 / R ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos heta]
    field_simp [heta.ne', hR]
  rw [hrad]
  ring

theorem scaledChain_smul_scale
    {T : ℕ} {eta : ℝ} (heta : eta ≠ 0) (q : ChainVector T) :
    scaledChain eta (eta • q) =
      eta ^ 2 * unscaledChain q := by
  rw [scaledChain_eq_scaled_unscaled, normalize_eq_inv_smul]
  rw [smul_smul, inv_mul_cancel₀ heta, one_smul]

/-- The population hyper-objective produced by the hard bilevel instance. -/
def hardHyperObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (eta kappa : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) : ℝ :=
  let z := kappa • x
  scaledChain eta
      (hiddenFrameTranspose J (softProjection (hardRadius eta T) z)) +
    pseudoHuber (1 / 4) (hardRadius eta T) z

theorem hardHyperObjective_eq_normalized
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    {eta kappa : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) :
    hardHyperObjective eta kappa J x =
      eta ^ 2 *
        normalizedHardObjective (1 / 4) (230 * Real.sqrt T) J
          ((kappa / eta) • x) := by
  let w : E := (kappa / eta) • x
  have hz : kappa • x = eta • w := by
    dsimp [w]
    rw [smul_smul]
    congr 1
    field_simp [heta.ne']
  have hRadius : hardRadius eta T = eta * (230 * Real.sqrt T) := by
    unfold hardRadius
    ring
  unfold hardHyperObjective
  dsimp only
  rw [hz, hRadius]
  rw [softProjection_mul_radius_smul heta (by
    have := one_le_sqrt_nat hT
    positivity)]
  rw [map_smul, scaledChain_smul_scale heta.ne']
  rw [pseudoHuber_mul_radius_smul heta (by
    have := one_le_sqrt_nat hT
    positivity)]
  unfold normalizedHardObjective
  dsimp [w]
  ring

theorem normalizedHardObjective_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {R : ℝ} (hR : R ≠ 0)
    (lam : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E) :
    ContDiff ℝ ∞ (normalizedHardObjective lam R J) := by
  unfold normalizedHardObjective
  exact
    ((unscaledChain_contDiff (T := T)).comp
      ((hiddenFrameTranspose J).contDiff.comp
        (softProjection_contDiff hR))).add
      (pseudoHuber_contDiff hR)

theorem gradient_const_mul_comp_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {phi : E → ℝ} {A c : ℝ} {x : E}
    (hphi : DifferentiableAt ℝ phi (c • x)) :
    gradient (fun y : E ↦ A * phi (c • y)) x =
      (A * c) • gradient phi (c • x) := by
  have hinner : HasFDerivAt (fun y : E ↦ c • y)
      (c • ContinuousLinearMap.id ℝ E) x := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul c
    change HasFDerivAt (fun y : E ↦ c • y)
      (c • ContinuousLinearMap.id ℝ E) x at h
    exact h
  have hcomp : HasFDerivAt (fun y : E ↦ phi (c • y))
      ((fderiv ℝ phi (c • x)).comp
        (c • ContinuousLinearMap.id ℝ E)) x := by
    have h := hphi.hasFDerivAt.comp x hinner
    change HasFDerivAt (fun y : E ↦ phi (c • y))
      ((fderiv ℝ phi (c • x)).comp
        (c • ContinuousLinearMap.id ℝ E)) x at h
    exact h
  have htotal := hcomp.const_mul A
  apply (toDual ℝ E).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  rw [htotal.fderiv]
  ext h
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul,
    smul_eq_mul]
  ring

theorem gradient_hardHyperObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    {eta kappa : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) :
    gradient (hardHyperObjective eta kappa J) x =
      (eta * kappa) •
        gradient
          (normalizedHardObjective (1 / 4) (230 * Real.sqrt T) J)
          ((kappa / eta) • x) := by
  have hfun : hardHyperObjective eta kappa J =
      fun y : E ↦ eta ^ 2 *
        normalizedHardObjective (1 / 4) (230 * Real.sqrt T) J
          ((kappa / eta) • y) := by
    funext y
    exact hardHyperObjective_eq_normalized heta hT J y
  rw [hfun]
  rw [gradient_const_mul_comp_smul]
  · congr 1
    field_simp [heta.ne']
  · exact
      (normalizedHardObjective_contDiff (by
        have := one_le_sqrt_nat hT
        positivity) (1 / 4) J).differentiable (by simp) _

theorem norm_gradient_hardHyperObjective_gt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    {eta kappa : ℝ} (heta : 0 < eta) (hkappa : 0 < kappa)
    (hT : 0 < T) (J : ChainVector T →ₗᵢ[ℝ] E) (x : E)
    (hunfinished :
      progress (eta / 4)
        (hiddenFrameTranspose J
          (softProjection (hardRadius eta T) (kappa • x))) < T) :
    eta * kappa / 2 <
      ‖gradient (hardHyperObjective eta kappa J) x‖ := by
  let w : E := (kappa / eta) • x
  let Rbar : ℝ := 230 * Real.sqrt T
  have hRbar : Rbar ≠ 0 := by
    dsimp [Rbar]
    have := one_le_sqrt_nat hT
    positivity
  have hz : kappa • x = eta • w := by
    dsimp [w]
    rw [smul_smul]
    congr 1
    field_simp [heta.ne']
  have hRadius : hardRadius eta T = eta * Rbar := by
    unfold hardRadius
    dsimp [Rbar]
    ring
  have hprobe :
      hiddenFrameTranspose J
          (softProjection (hardRadius eta T) (kappa • x)) =
        eta •
          hiddenFrameTranspose J (softProjection Rbar w) := by
    rw [hz, hRadius, softProjection_mul_radius_smul heta hRbar,
      map_smul]
  have hnormalizedProgress :
      progress (1 / 4 : ℝ)
        (hiddenFrameTranspose J (softProjection Rbar w)) < T := by
    have hrescale := progress_quarter_rescaling
      (hiddenFrameTranspose J
        (softProjection (hardRadius eta T) (kappa • x))) eta heta
    have hdivide : chainVectorOfFun (fun i ↦
        hiddenFrameTranspose J
          (softProjection (hardRadius eta T) (kappa • x)) i / eta) =
        hiddenFrameTranspose J (softProjection Rbar w) := by
      rw [hprobe]
      ext i
      simp only [chainVectorOfFun_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [heta.ne']
    rw [hdivide] at hrescale
    rw [hrescale]
    simpa [Rbar] using hunfinished
  have hnormalized := norm_gradient_normalizedHardObjective_gt_half
    hT J w (by simpa [Rbar] using hnormalizedProgress)
  rw [gradient_hardHyperObjective heta hT]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos heta hkappa)]
  nlinarith [mul_pos heta hkappa]

/-! ## Initial hyper-objective gap -/

theorem hardHyperObjective_gap_pointwise
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) :
    hardHyperObjective eta kappa J 0 -
        hardHyperObjective eta kappa J x ≤
      eta ^ 2 *
        (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := by
  let z : E := kappa • x
  let q : ChainVector T :=
    hiddenFrameTranspose J (softProjection (hardRadius eta T) z)
  have hchain := scaledChain_gap_pointwise eta q
  have hradial :
      0 ≤ pseudoHuber (1 / 4) (hardRadius eta T) z :=
    pseudoHuber_nonneg (by norm_num) z
  have h :
      scaledChain eta (0 : ChainVector T) -
        (scaledChain eta q +
          pseudoHuber (1 / 4) (hardRadius eta T) z) ≤
        eta ^ 2 *
          (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := by
    linarith
  simpa [hardHyperObjective, z, q] using h

theorem hardHyperObjective_range_bddBelow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    BddBelow (Set.range (hardHyperObjective eta kappa J)) := by
  let C : ℝ := eta ^ 2 *
    (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound)))
  refine ⟨hardHyperObjective eta kappa J 0 - C, ?_⟩
  rintro y ⟨x, rfl⟩
  have hgap := hardHyperObjective_gap_pointwise eta kappa J x
  dsimp only [C]
  linarith

theorem hardHyperObjective_initial_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    hardHyperObjective eta kappa J 0 -
        sInf (Set.range (hardHyperObjective eta kappa J)) ≤
      eta ^ 2 *
        (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := by
  let C : ℝ := eta ^ 2 *
    (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound)))
  have hLower :
      hardHyperObjective eta kappa J 0 - C ≤
        sInf (Set.range (hardHyperObjective eta kappa J)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    have hgap := hardHyperObjective_gap_pointwise eta kappa J x
    dsimp only [C]
    linarith
  dsimp only [C] at hLower ⊢
  linarith

end

end BilevelLowerBound
