/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FullPopulationRegularity

/-!
# Concrete regularity of the hard population objectives

This module substitutes the concrete quadratic, cutoff, pseudo-Huber, and
compensated-frontier components into the aggregation lemmas proved in
`FullPopulationRegularity`.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Pseudo-Huber Hessian -/

theorem fderiv_pseudoHuber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam R : ℝ} (hR : R ≠ 0) (z : E) :
    fderiv ℝ (pseudoHuber lam R : E → ℝ) z =
      lam • innerSL ℝ (softProjection R z) := by
  have hpos : 0 < 1 + ‖z‖ ^ 2 / R ^ 2 := by positivity
  have hsqrt0 : Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2)
      (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hdiv : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ z)) z := by
    simpa only [div_eq_mul_inv] using hnorm.mul_const (R ^ 2)⁻¹
  have hrad : HasFDerivAt (fun y : E ↦ 1 + ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    hdiv.const_add 1
  have hsqrt := hrad.sqrt hpos.ne'
  have hsub := hsqrt.sub_const 1
  have hmul := hsub.mul_const (lam * R ^ 2)
  have hfun : (pseudoHuber lam R : E → ℝ) = fun y ↦
      (Real.sqrt (1 + ‖y‖ ^ 2 / R ^ 2) - 1) * (lam * R ^ 2) := by
    funext y
    unfold pseudoHuber
    ring
  rw [hfun, hmul.fderiv]
  ext h
  unfold softProjection
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    innerSL_apply_apply, real_inner_smul_left]
  field_simp [hR, hsqrt0, Real.sq_sqrt hpos.le]
  ring

theorem norm_iteratedFDeriv_pseudoHuber_two_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 2 (pseudoHuber lam R : E → ℝ) z‖ ≤ lam := by
  let K : E →L[ℝ] (E →L[ℝ] ℝ) := lam • (innerSL ℝ (E := E))
  have hfd : fderiv ℝ (pseudoHuber lam R : E → ℝ) =
      K ∘ (softProjection R : E → E) := by
    funext y
    rw [fderiv_pseudoHuber hR.ne']
    rfl
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  have hcomp :
      ‖iteratedFDeriv ℝ 1 (K ∘ softProjection R) z‖ ≤
        ‖K‖ * ‖iteratedFDeriv ℝ 1 (softProjection R : E → E) z‖ :=
    K.norm_iteratedFDeriv_comp_left
      ((softProjection_contDiff hR.ne').contDiffAt)
      (show (1 : ℕ) ≤ (∞ : ℕ∞ω) by simp)
  have hK : ‖K‖ ≤ lam := by
    apply ContinuousLinearMap.opNorm_le_bound K hlam
    intro x
    dsimp [K]
    change ‖lam • (innerSL ℝ x)‖ ≤ lam * ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam,
      innerSL_apply_norm]
  calc
    ‖iteratedFDeriv ℝ 1 (K ∘ softProjection R) z‖ ≤
        ‖K‖ * ‖iteratedFDeriv ℝ 1 (softProjection R : E → E) z‖ := hcomp
    _ ≤ lam * 1 := by
      apply mul_le_mul
      · exact hK
      · rw [norm_iteratedFDeriv_one]
        exact norm_fderiv_softProjection_le_one hR z
      · exact norm_nonneg _
      · exact hlam
    _ = lam := mul_one _

/-! ## Cutoff-primitive Hessian -/

theorem eventually_iteratedFDeriv_cutoffWeight_eq_zero_atTop (n : ℕ) :
    (fun v : ℝ ↦ iteratedFDeriv ℝ n cutoffWeight v) =ᶠ[atTop]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with v hv
  have hLocal : cutoffWeight =ᶠ[nhds v] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < v by linarith)] with y hy
    change (2 : ℝ) < y at hy
    exact cutoffWeight_eq_zero_of_two_le_abs
      (by rw [abs_of_pos (by linarith)]; linarith)
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hJet.eq_of_nhds

theorem eventually_iteratedFDeriv_cutoffWeight_eq_zero_atBot (n : ℕ) :
    (fun v : ℝ ↦ iteratedFDeriv ℝ n cutoffWeight v) =ᶠ[atBot]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_le_atBot (-3 : ℝ)] with v hv
  have hLocal : cutoffWeight =ᶠ[nhds v] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Iio_mem_nhds (show v < (-2 : ℝ) by linarith)] with y hy
    change y < (-2 : ℝ) at hy
    exact cutoffWeight_eq_zero_of_two_le_abs
      (by rw [abs_of_neg (by linarith)]; linarith)
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hJet.eq_of_nhds

theorem isBounded_range_iteratedFDeriv_cutoffWeight (n : ℕ) :
    Bornology.IsBounded
      (Set.range (fun v : ℝ ↦ iteratedFDeriv ℝ n cutoffWeight v)) := by
  have hCont : Continuous (fun v : ℝ ↦
      iteratedFDeriv ℝ n cutoffWeight v) :=
    cutoffWeight_contDiff.continuous_iteratedFDeriv
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
  apply hCont.isBounded_range_iff_isBigO_atTop_atBot.mpr
  constructor
  · have hTendsto : Tendsto
        (fun v : ℝ ↦ iteratedFDeriv ℝ n cutoffWeight v) atTop
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_cutoffWeight_eq_zero_atTop n).symm
    exact hTendsto.isBigO_one ℝ
  · have hTendsto : Tendsto
        (fun v : ℝ ↦ iteratedFDeriv ℝ n cutoffWeight v) atBot
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_cutoffWeight_eq_zero_atBot n).symm
    exact hTendsto.isBigO_one ℝ

theorem exists_cutoffPrimitive_second_bound :
    ∃ Cell : ℝ, 0 ≤ Cell ∧ ∀ v : ℝ,
      ‖iteratedFDeriv ℝ 2 cutoffPrimitive v‖ ≤ Cell := by
  have hBounded := isBounded_range_iteratedFDeriv_cutoffWeight 1
  rw [isBounded_iff_forall_norm_le] at hBounded
  obtain ⟨C, hC⟩ := hBounded
  let Cell := max C 0
  refine ⟨Cell, le_max_right _ _, fun v ↦ ?_⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : fderiv ℝ cutoffPrimitive =
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ) ∘ cutoffWeight := by
    funext y
    rw [← toSpanSingleton_deriv, cutoffPrimitive_deriv]
    rfl
  rw [hfd]
  rw [(ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).norm_iteratedFDeriv_comp_left
    cutoffWeight v 1]
  exact (hC _ ⟨v, rfl⟩).trans (le_max_left C 0)

/-! ## Elementary quadratic derivatives -/

theorem iteratedFDeriv_norm_sq_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ 2) z m =
      2 * inner ℝ (m 0) (m 1) := by
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2)) z) (m 0))
    (m 1) = _
  rw [fderiv_norm_sq]
  let K : E →L[ℝ] (E →L[ℝ] ℝ) := 2 • (innerSL ℝ (E := E))
  change ((fderiv ℝ (K : E → E →L[ℝ] ℝ) z) (m 0)) (m 1) = _
  rw [K.fderiv]
  simp [K, innerSL_apply_apply ℝ]

theorem norm_iteratedFDeriv_norm_sq_two_le_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) :
    ‖iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ 2) z‖ ≤ 2 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  rw [Real.norm_eq_abs, iteratedFDeriv_norm_sq_two_apply]
  calc
    |2 * inner ℝ (m 0) (m 1)| = 2 * |inner ℝ (m 0) (m 1)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ 2 * (‖m 0‖ * ‖m 1‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = 2 * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_two]

theorem iteratedFDeriv_norm_sq_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) :
    iteratedFDeriv ℝ 3 (fun y : E ↦ ‖y‖ ^ 2) z = 0 := by
  have hD2Diff : DifferentiableAt ℝ
      (iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ 2)) z :=
    (contDiff_norm_sq ℝ).contDiffAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2)
  ext m
  rw [hD2Diff.iteratedFDeriv_succ_apply_left']
  have hfun :
      (fun y : E ↦ iteratedFDeriv ℝ 2 (fun w : E ↦ ‖w‖ ^ 2) y
        (Fin.tail m)) =
      fun _ : E ↦ 2 * inner ℝ (m 1) (m 2) := by
    funext y
    rw [iteratedFDeriv_norm_sq_two_apply]
    rfl
  rw [hfun]
  simp

def mixedInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) : ℝ :=
  inner ℝ p.1 p.2

theorem mixedInner_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (mixedInner : E × E → ℝ) := by
  exact contDiff_fst.inner ℝ contDiff_snd

theorem fderiv_mixedInner_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p h : E × E) :
    fderiv ℝ (mixedInner : E × E → ℝ) p h =
      inner ℝ p.1 h.2 + inner ℝ h.1 p.2 := by
  unfold mixedInner
  have hfst : HasFDerivAt (fun y : E × E ↦ y.1)
      (ContinuousLinearMap.fst ℝ E E) p :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : E × E ↦ y.2)
      (ContinuousLinearMap.snd ℝ E E) p :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hderiv := (hfst.inner ℝ hsnd).fderiv
  have happly := congrArg (fun L : (E × E) →L[ℝ] ℝ ↦ L h) hderiv
  simpa [innerSL_apply_apply ℝ] using happly

theorem iteratedFDeriv_mixedInner_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) (m : Fin 2 → E × E) :
    iteratedFDeriv ℝ 2 (mixedInner : E × E → ℝ) p m =
      inner ℝ (m 0).1 (m 1).2 + inner ℝ (m 1).1 (m 0).2 := by
  rw [iteratedFDeriv_two_apply]
  let c : (E × E) → (E × E →L[ℝ] ℝ) :=
    fun y ↦ fderiv ℝ (mixedInner : E × E → ℝ) y
  have hc : DifferentiableAt ℝ c p :=
    ((contDiff_infty_iff_fderiv.mp mixedInner_contDiff).2.differentiable
      (by simp)) p
  have hu : DifferentiableAt ℝ (fun _ : E × E ↦ m 1) p :=
    differentiableAt_const (m 1)
  have heval := fderiv_clm_apply hc hu
  have hevalAt := congrArg (fun L : (E × E) →L[ℝ] ℝ ↦ L (m 0)) heval
  simp at hevalAt
  have hfun : (fun y : E × E ↦ c y (m 1)) = fun y ↦
      inner ℝ y.1 (m 1).2 + inner ℝ (m 1).1 y.2 := by
    funext y
    exact fderiv_mixedInner_apply y (m 1)
  have hfst : HasFDerivAt (fun y : E × E ↦ y.1)
      (ContinuousLinearMap.fst ℝ E E) p :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : E × E ↦ y.2)
      (ContinuousLinearMap.snd ℝ E E) p :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hA : HasFDerivAt (fun y : E × E ↦ inner ℝ y.1 (m 1).2)
      ((fderivInnerCLM ℝ (p.1, (m 1).2)).comp
        ((ContinuousLinearMap.fst ℝ E E).prod 0)) p :=
    hfst.inner ℝ (hasFDerivAt_const (m 1).2 p)
  have hB : HasFDerivAt (fun y : E × E ↦ inner ℝ (m 1).1 y.2)
      ((fderivInnerCLM ℝ ((m 1).1, p.2)).comp
        ((0 : (E × E) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E E))) p :=
    (hasFDerivAt_const (m 1).1 p).inner ℝ hsnd
  have hsum := (hA.add hB).fderiv
  have hsumAt := congrArg (fun L : (E × E) →L[ℝ] ℝ ↦ L (m 0)) hsum
  change ((fderiv ℝ c p) (m 0)) (m 1) = _
  rw [← hevalAt, hfun]
  have hsumfun :
      ((fun y : E × E ↦ inner ℝ y.1 (m 1).2) +
        fun y ↦ inner ℝ (m 1).1 y.2) =
      (fun y ↦ inner ℝ y.1 (m 1).2 + inner ℝ (m 1).1 y.2) := by
    rfl
  rw [← hsumfun]
  simpa [innerSL_apply_apply ℝ] using hsumAt

theorem norm_iteratedFDeriv_mixedInner_two_le_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) :
    ‖iteratedFDeriv ℝ 2 (mixedInner : E × E → ℝ) p‖ ≤ 2 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  rw [Real.norm_eq_abs, iteratedFDeriv_mixedInner_two_apply]
  let M0 := ‖m 0‖
  let M1 := ‖m 1‖
  have hx0 : ‖(m 0).1‖ ≤ M0 := le_max_left _ _
  have hz0 : ‖(m 0).2‖ ≤ M0 := le_max_right _ _
  have hx1 : ‖(m 1).1‖ ≤ M1 := le_max_left _ _
  have hz1 : ‖(m 1).2‖ ≤ M1 := le_max_right _ _
  have hA : |inner ℝ (m 0).1 (m 1).2| ≤ M0 * M1 :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hx0 hz1 (norm_nonneg _) (norm_nonneg _))
  have hB : |inner ℝ (m 1).1 (m 0).2| ≤ M0 * M1 := by
    calc
      |inner ℝ (m 1).1 (m 0).2| ≤ ‖(m 1).1‖ * ‖(m 0).2‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ M1 * M0 := mul_le_mul hx1 hz0 (norm_nonneg _) (norm_nonneg _)
      _ = M0 * M1 := mul_comm _ _
  calc
    |inner ℝ (m 0).1 (m 1).2 + inner ℝ (m 1).1 (m 0).2| ≤
        |inner ℝ (m 0).1 (m 1).2| + |inner ℝ (m 1).1 (m 0).2| :=
      abs_add_le _ _
    _ ≤ 2 * (M0 * M1) := by linarith
    _ = 2 * ∏ i, ‖m i‖ := by simp [M0, M1, Fin.prod_univ_two]

theorem iteratedFDeriv_mixedInner_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) :
    iteratedFDeriv ℝ 3 (mixedInner : E × E → ℝ) p = 0 := by
  have hD2Diff : DifferentiableAt ℝ
      (iteratedFDeriv ℝ 2 (mixedInner : E × E → ℝ)) p :=
    mixedInner_contDiff.contDiffAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2)
  ext m
  rw [hD2Diff.iteratedFDeriv_succ_apply_left']
  have hfun :
      (fun y : E × E ↦ iteratedFDeriv ℝ 2
        (mixedInner : E × E → ℝ) y (Fin.tail m)) =
      fun _ ↦ inner ℝ (m 1).1 (m 2).2 + inner ℝ (m 2).1 (m 1).2 := by
    funext y
    rw [iteratedFDeriv_mixedInner_two_apply]
    rfl
  rw [hfun]
  simp

def scaledNormSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (z : E) : ℝ :=
  ‖z‖ ^ 2 / (2 * κ)

theorem scaledNormSq_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) :
    ContDiff ℝ ∞ (scaledNormSq κ : E → ℝ) := by
  unfold scaledNormSq
  exact (contDiff_norm_sq ℝ).div_const (2 * κ)

theorem norm_iteratedFDeriv_scaledNormSq_two_le_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : 1 ≤ κ) (z : E) :
    ‖iteratedFDeriv ℝ 2 (scaledNormSq κ : E → ℝ) z‖ ≤ 2 := by
  have hkpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hfun : (scaledNormSq κ : E → ℝ) =
      (2 * κ)⁻¹ • (fun y : E ↦ ‖y‖ ^ 2) := by
    funext y
    simp [scaledNormSq, div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt), norm_smul]
  have hcoef : ‖(2 * κ)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (mul_pos (by norm_num) hkpos)]
    exact (inv_le_one₀ (mul_pos (by norm_num) hkpos)).2 (by nlinarith)
  calc
    ‖(2 * κ)⁻¹‖ * ‖iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ 2) z‖ ≤
        1 * 2 := mul_le_mul hcoef
      (norm_iteratedFDeriv_norm_sq_two_le_two z) (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

theorem iteratedFDeriv_scaledNormSq_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (z : E) :
    iteratedFDeriv ℝ 3 (scaledNormSq κ : E → ℝ) z = 0 := by
  have hfun : (scaledNormSq κ : E → ℝ) =
      (2 * κ)⁻¹ • (fun y : E ↦ ‖y‖ ^ 2) := by
    funext y
    simp [scaledNormSq, div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
    iteratedFDeriv_norm_sq_three_eq_zero, smul_zero]

def negativeMixedInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) : ℝ :=
  -mixedInner p

theorem negativeMixedInner_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (negativeMixedInner : E × E → ℝ) :=
  mixedInner_contDiff.neg

theorem norm_iteratedFDeriv_negativeMixedInner_two_le_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) :
    ‖iteratedFDeriv ℝ 2 (negativeMixedInner : E × E → ℝ) p‖ ≤ 2 := by
  have hfun : (negativeMixedInner : E × E → ℝ) =
      (-1 : ℝ) • (mixedInner : E × E → ℝ) := by
    funext y
    simp [negativeMixedInner]
  rw [hfun, iteratedFDeriv_const_smul_apply
    ((mixedInner_contDiff.of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt), norm_smul]
  norm_num
  exact norm_iteratedFDeriv_mixedInner_two_le_two p

theorem iteratedFDeriv_negativeMixedInner_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E × E) :
    iteratedFDeriv ℝ 3 (negativeMixedInner : E × E → ℝ) p = 0 := by
  have hfun : (negativeMixedInner : E × E → ℝ) =
      (-1 : ℝ) • (mixedInner : E × E → ℝ) := by
    funext y
    simp [negativeMixedInner]
  rw [hfun, iteratedFDeriv_const_smul_apply
    ((mixedInner_contDiff.of_le
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
    iteratedFDeriv_mixedInner_three_eq_zero, smul_zero]

def halfSquare (v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * v ^ 2

theorem halfSquare_contDiff : ContDiff ℝ ∞ halfSquare := by
  unfold halfSquare
  fun_prop

theorem norm_iteratedFDeriv_halfSquare_two_le_one (v : ℝ) :
    ‖iteratedFDeriv ℝ 2 halfSquare v‖ ≤ 1 := by
  have hfun : halfSquare = (1 / 2 : ℝ) • (fun y : ℝ ↦ ‖y‖ ^ 2) := by
    funext y
    simp [halfSquare, Real.norm_eq_abs, sq_abs]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt), norm_smul]
  norm_num
  have h : ‖iteratedFDeriv ℝ 2 (fun x : ℝ ↦ x ^ 2) v‖ ≤ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using
      norm_iteratedFDeriv_norm_sq_two_le_two v
  linarith

theorem iteratedFDeriv_halfSquare_three_eq_zero (v : ℝ) :
    iteratedFDeriv ℝ 3 halfSquare v = 0 := by
  have hfun : halfSquare = (1 / 2 : ℝ) • (fun y : ℝ ↦ ‖y‖ ^ 2) := by
    funext y
    simp [halfSquare, Real.norm_eq_abs, sq_abs]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
    iteratedFDeriv_norm_sq_three_eq_zero, smul_zero]

/-! ## The complete base quadratic on `(x, z, v)` -/

def fullZProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × ℝ)) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E ℝ).comp
    (ContinuousLinearMap.snd ℝ E (E × ℝ))

def fullXZProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × ℝ)) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E (E × ℝ)).prod fullZProjection

def fullVProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ E ℝ).comp
    (ContinuousLinearMap.snd ℝ E (E × ℝ))

@[simp] theorem fullZProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × ℝ)) :
    fullZProjection p = p.2.1 := rfl

@[simp] theorem fullXZProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × ℝ)) :
    fullXZProjection p = (p.1, p.2.1) := rfl

@[simp] theorem fullVProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × ℝ)) :
    fullVProjection p = p.2.2 := rfl

theorem norm_fullZProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(fullZProjection : (E × (E × ℝ)) →L[ℝ] E)‖ ≤ 1 := by
  calc
    ‖(fullZProjection : (E × (E × ℝ)) →L[ℝ] E)‖ ≤
        ‖ContinuousLinearMap.fst ℝ E ℝ‖ *
          ‖ContinuousLinearMap.snd ℝ E (E × ℝ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_fst_le ℝ E ℝ)
      (ContinuousLinearMap.norm_snd_le ℝ E (E × ℝ))
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

theorem norm_fullXZProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(fullXZProjection : (E × (E × ℝ)) →L[ℝ] (E × E))‖ ≤ 1 := by
  rw [fullXZProjection, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le
    (ContinuousLinearMap.norm_fst_le ℝ E (E × ℝ))
    (norm_fullZProjection_le_one (E := E))

theorem norm_fullVProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(fullVProjection : (E × (E × ℝ)) →L[ℝ] ℝ)‖ ≤ 1 := by
  calc
    ‖(fullVProjection : (E × (E × ℝ)) →L[ℝ] ℝ)‖ ≤
        ‖ContinuousLinearMap.snd ℝ E ℝ‖ *
          ‖ContinuousLinearMap.snd ℝ E (E × ℝ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_snd_le ℝ E ℝ)
      (ContinuousLinearMap.norm_snd_le ℝ E (E × ℝ))
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

def fullScaledNormSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) : E × (E × ℝ) → ℝ :=
  (scaledNormSq κ) ∘ fullZProjection

def fullNegativeMixedInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E × (E × ℝ) → ℝ :=
  negativeMixedInner ∘ fullXZProjection

def fullHalfSquare
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E × (E × ℝ) → ℝ :=
  halfSquare ∘ fullVProjection

def fullBaseQuadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) : E × (E × ℝ) → ℝ :=
  fullScaledNormSq κ + fullNegativeMixedInner + fullHalfSquare

@[simp] theorem fullBaseQuadratic_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (p : E × (E × ℝ)) :
    fullBaseQuadratic κ p =
      ‖p.2.1‖ ^ 2 / (2 * κ) - inner ℝ p.1 p.2.1 +
        (1 / 2 : ℝ) * p.2.2 ^ 2 := by
  rfl

theorem fullBaseQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) :
    ContDiff ℝ ∞ (fullBaseQuadratic κ : E × (E × ℝ) → ℝ) := by
  have hA : ContDiff ℝ ∞
      (fullScaledNormSq κ : E × (E × ℝ) → ℝ) :=
    (scaledNormSq_contDiff κ).comp
      (fullZProjection (E := E)).contDiff
  have hB : ContDiff ℝ ∞
      (fullNegativeMixedInner : E × (E × ℝ) → ℝ) :=
    negativeMixedInner_contDiff.comp
      (fullXZProjection (E := E)).contDiff
  have hC : ContDiff ℝ ∞
      (fullHalfSquare : E × (E × ℝ) → ℝ) :=
    halfSquare_contDiff.comp (fullVProjection (E := E)).contDiff
  exact (hA.add hB).add hC

set_option maxHeartbeats 800000 in
-- Elaborating the three product-space compositions requires a larger budget.
theorem norm_iteratedFDeriv_fullBaseQuadratic_two_le_five
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : 1 ≤ κ) (p : E × (E × ℝ)) :
    ‖iteratedFDeriv ℝ 2 (fullBaseQuadratic κ) p‖ ≤ 5 := by
  have hA : ContDiff ℝ ∞
      (fullScaledNormSq κ : E × (E × ℝ) → ℝ) :=
    (scaledNormSq_contDiff κ).comp
      (fullZProjection (E := E)).contDiff
  have hB : ContDiff ℝ ∞
      (fullNegativeMixedInner : E × (E × ℝ) → ℝ) :=
    negativeMixedInner_contDiff.comp
      (fullXZProjection (E := E)).contDiff
  have hC : ContDiff ℝ ∞
      (fullHalfSquare : E × (E × ℝ) → ℝ) :=
    halfSquare_contDiff.comp (fullVProjection (E := E)).contDiff
  have hA2 : ‖iteratedFDeriv ℝ 2
      (fullScaledNormSq κ : E × (E × ℝ) → ℝ) p‖ ≤ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (scaledNormSq_contDiff κ) (fullZProjection (E := E))
      (norm_fullZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_scaledNormSq_two_le_two hκ p.2.1)
  have hB2 : ‖iteratedFDeriv ℝ 2
      (fullNegativeMixedInner : E × (E × ℝ) → ℝ) p‖ ≤ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      negativeMixedInner_contDiff (fullXZProjection (E := E))
      (norm_fullXZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_negativeMixedInner_two_le_two (p.1, p.2.1))
  have hC2 : ‖iteratedFDeriv ℝ 2
      (fullHalfSquare : E × (E × ℝ) → ℝ) p‖ ≤ 1 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      halfSquare_contDiff (fullVProjection (E := E))
      (norm_fullVProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_halfSquare_two_le_one p.2.2)
  change ‖iteratedFDeriv ℝ 2
    ((fullScaledNormSq κ + fullNegativeMixedInner) + fullHalfSquare) p‖ ≤ 5
  exact (norm_iteratedFDeriv_three_sum_le hA hB hC 2 p
    hA2 hB2 hC2).trans_eq (by norm_num)

set_option maxHeartbeats 800000 in
-- Elaborating the three product-space third derivatives requires a larger budget.
theorem iteratedFDeriv_fullBaseQuadratic_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (p : E × (E × ℝ)) :
    iteratedFDeriv ℝ 3 (fullBaseQuadratic κ) p = 0 := by
  have hA : ‖iteratedFDeriv ℝ 3
      (fullScaledNormSq κ : E × (E × ℝ) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (scaledNormSq_contDiff κ) (fullZProjection (E := E))
      (norm_fullZProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_scaledNormSq_three_eq_zero, norm_zero])
  have hB : ‖iteratedFDeriv ℝ 3
      (fullNegativeMixedInner : E × (E × ℝ) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      negativeMixedInner_contDiff (fullXZProjection (E := E))
      (norm_fullXZProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_negativeMixedInner_three_eq_zero, norm_zero])
  have hC : ‖iteratedFDeriv ℝ 3
      (fullHalfSquare : E × (E × ℝ) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      halfSquare_contDiff (fullVProjection (E := E))
      (norm_fullVProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_halfSquare_three_eq_zero, norm_zero])
  have hsA : ContDiff ℝ ∞
      (fullScaledNormSq κ : E × (E × ℝ) → ℝ) :=
    (scaledNormSq_contDiff κ).comp
      (fullZProjection (E := E)).contDiff
  have hsB : ContDiff ℝ ∞
      (fullNegativeMixedInner : E × (E × ℝ) → ℝ) :=
    negativeMixedInner_contDiff.comp
      (fullXZProjection (E := E)).contDiff
  have hsC : ContDiff ℝ ∞
      (fullHalfSquare : E × (E × ℝ) → ℝ) :=
    halfSquare_contDiff.comp (fullVProjection (E := E)).contDiff
  have hsum : ‖iteratedFDeriv ℝ 3
      ((fullScaledNormSq κ + fullNegativeMixedInner) + fullHalfSquare) p‖ ≤ 0 :=
    by
      simpa using (norm_iteratedFDeriv_three_sum_le
        hsA hsB hsC 3 p hA hB hC)
  change iteratedFDeriv ℝ 3
    ((fullScaledNormSq κ + fullNegativeMixedInner) + fullHalfSquare) p = 0
  exact norm_eq_zero.mp (le_antisymm hsum (norm_nonneg _))

/-! ## Concrete population lower objective -/

def fullLowerProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × ℝ)) →L[ℝ] (E × ℝ) :=
  ContinuousLinearMap.snd ℝ E (E × ℝ)

@[simp] theorem fullLowerProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × ℝ)) :
    fullLowerProjection p = p.2 := rfl

theorem norm_fullLowerProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(fullLowerProjection : (E × (E × ℝ)) →L[ℝ] (E × ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.norm_snd_le ℝ E (E × ℝ)

def fullCompensatedPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (θ : E → ℝ) : E × (E × ℝ) → ℝ :=
  (compensatedPair η θ) ∘ fullLowerProjection

theorem fullCompensatedPair_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : η ≠ 0) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (fullCompensatedPair η θ) :=
  (compensatedPair_contDiff hη hθ).comp
    (fullLowerProjection (E := E)).contDiff

def fullPopulationLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (κ η : ℝ) (L : E →L[ℝ] ChainVector T) :
    E × (E × ℝ) → ℝ :=
  lowerPopulationSum (fullBaseQuadratic κ)
    (fullCompensatedPair η (hardFrontierMap η L))

@[simp] theorem fullPopulationLower_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (κ η : ℝ) (L : E →L[ℝ] ChainVector T)
    (p : E × (E × ℝ)) :
    fullPopulationLower κ η L p =
      populationLower κ η (hardFrontierMap η L) p.1 p.2.1 p.2.2 := by
  rfl

theorem fullPopulationLower_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (κ : ℝ) (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (fullPopulationLower κ η L) := by
  exact lowerPopulationSum_contDiff (fullBaseQuadratic_contDiff κ)
    (fullCompensatedPair_contDiff hη.ne'
      (hardFrontierMap_contDiff hη hT L))

set_option maxHeartbeats 800000 in
-- The quantified certificate expands several product-space compositions.
/-- Uniform global regularity bounds for the actual population lower
objective after substituting the hidden frontier map.  The constants are
independent of `T`, `E`, `kappa`, `eta`, and the hidden contraction.

The larger heartbeat budget is needed to elaborate the bundled quantified
certificate and its several product-space compositions. -/
theorem exists_fullPopulationLower_regularities :
    ∃ CHess Cthird : ℝ, 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {κ η : ℝ}, 1 ≤ κ → 0 < η → η ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ p : E × (E × ℝ),
          ‖iteratedFDeriv ℝ 2 (fullPopulationLower κ η L) p‖ ≤
            5 + CHess * η) ∧
        (∀ p : E × (E × ℝ),
          ‖iteratedFDeriv ℝ 3 (fullPopulationLower κ η L) p‖ ≤
            Cthird) ∧
        (∀ p q : E × (E × ℝ),
          ‖fderiv ℝ (fullPopulationLower κ η L) q -
              fderiv ℝ (fullPopulationLower κ η L) p‖ ≤
            (5 + CHess * η) * ‖q - p‖) ∧
        (∀ p q : E × (E × ℝ),
          ‖iteratedFDeriv ℝ 2 (fullPopulationLower κ η L) q -
              iteratedFDeriv ℝ 2 (fullPopulationLower κ η L) p‖ ≤
            Cthird * ‖q - p‖) := by
  obtain ⟨CHess, Cthird, hCHess, hCthird, hregular⟩ :=
    exists_hard_compensated_pair_regularities
  refine ⟨CHess, Cthird, hCHess, hCthird, ?_⟩
  intro E _ _ T κ η hκ hη hη1 hT L hL
  let θ : E → ℝ := hardFrontierMap η L
  let perturbation : E × (E × ℝ) → ℝ :=
    fullCompensatedPair η θ
  have hθ : ContDiff ℝ ∞ θ := hardFrontierMap_contDiff hη hT L
  have hpert : ContDiff ℝ ∞ perturbation :=
    fullCompensatedPair_contDiff hη.ne' hθ
  have hraw (p : E × (E × ℝ)) :=
    hregular hη hη1 hT hL p.2
  have hpert2 (p : E × (E × ℝ)) :
      ‖iteratedFDeriv ℝ 2 perturbation p‖ ≤ CHess * η :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compensatedPair_contDiff hη.ne' hθ)
      (fullLowerProjection (E := E))
      (norm_fullLowerProjection_le_one (E := E)) 2 p).trans (hraw p).1
  have hpert3 (p : E × (E × ℝ)) :
      ‖iteratedFDeriv ℝ 3 perturbation p‖ ≤ Cthird :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compensatedPair_contDiff hη.ne' hθ)
      (fullLowerProjection (E := E))
      (norm_fullLowerProjection_le_one (E := E)) 3 p).trans (hraw p).2
  have hbase := fullBaseQuadratic_contDiff (E := E) κ
  have hbase2 (p : E × (E × ℝ)) :=
    norm_iteratedFDeriv_fullBaseQuadratic_two_le_five hκ p
  have hbase3 (p : E × (E × ℝ)) :=
    iteratedFDeriv_fullBaseQuadratic_three_eq_zero κ p
  change
    (∀ p, ‖iteratedFDeriv ℝ 2
      (lowerPopulationSum (fullBaseQuadratic κ) perturbation) p‖ ≤
        5 + CHess * η) ∧ _
  refine ⟨lowerPopulationSum_second_bound hbase hpert hbase2 hpert2, ?_⟩
  refine ⟨lowerPopulationSum_third_bound hbase hpert hbase3 hpert3, ?_⟩
  refine ⟨lowerPopulationSum_gradient_lipschitz
    hbase hpert hbase2 hpert2, ?_⟩
  exact lowerPopulationSum_hessian_lipschitz
    hbase hpert hbase3 hpert3

/-! ## Concrete population upper objective -/

def hardVisibleMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η : ℝ) (L : E →L[ℝ] ChainVector T) : E → ℝ :=
  (visibleChain η : ChainVector T → ℝ) ∘
    hiddenProbe (hardRadius η T) L

theorem hardVisibleMap_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (hardVisibleMap η L) :=
  (visibleChain_contDiff η).comp
    (hiddenProbe_contDiff (hardRadius_pos hη hT).ne' L)

def fullHardVisible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η : ℝ) (L : E →L[ℝ] ChainVector T) :
    E × (E × ℝ) → ℝ :=
  (hardVisibleMap η L) ∘ fullZProjection

def fullCutoffPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E × (E × ℝ) → ℝ :=
  cutoffPrimitive ∘ fullVProjection

def fullPseudoHuber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam R : ℝ) : E × (E × ℝ) → ℝ :=
  (pseudoHuber lam R) ∘ fullZProjection

def fullHardUpper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η lam R : ℝ) (L : E →L[ℝ] ChainVector T) :
    E × (E × ℝ) → ℝ :=
  upperPopulationSum (fullHardVisible η L)
    fullCutoffPrimitive (fullPseudoHuber lam R)

@[simp] theorem fullHardUpper_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η lam R : ℝ) (L : E →L[ℝ] ChainVector T)
    (p : E × (E × ℝ)) :
    fullHardUpper η lam R L p =
      hardUpper η lam R
        (hiddenProbe (hardRadius η T) L) p.2.1 p.2.2 := by
  rfl

theorem fullHardUpper_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η R : ℝ} (hη : 0 < η) (hT : 0 < T)
    (hR : R ≠ 0) (lam : ℝ) (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (fullHardUpper η lam R L) := by
  exact upperPopulationSum_contDiff
    ((hardVisibleMap_contDiff hη hT L).comp
      (fullZProjection (E := E)).contDiff)
    (cutoffPrimitive_contDiff.comp (fullVProjection (E := E)).contDiff)
    ((pseudoHuber_contDiff hR).comp
      (fullZProjection (E := E)).contDiff)

set_option maxHeartbeats 800000 in
-- The quantified certificate expands all three upper components.
/-- Uniform Hessian and gradient-Lipschitz bounds for the actual upper hard
objective.  `Ca` and `Cell` are universal constants; the radial term
contributes exactly its coefficient `lam`.

The larger heartbeat budget is needed to elaborate the bundled quantified
certificate and all three upper components. -/
theorem exists_fullHardUpper_second_regularities :
    ∃ Ca Cell : ℝ, 0 ≤ Ca ∧ 0 ≤ Cell ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {η lam R : ℝ}, 0 < η → 0 < T → 0 ≤ lam → 0 < R →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ p : E × (E × ℝ),
          ‖iteratedFDeriv ℝ 2 (fullHardUpper η lam R L) p‖ ≤
            Ca + Cell + lam) ∧
        (∀ p q : E × (E × ℝ),
          ‖fderiv ℝ (fullHardUpper η lam R L) q -
              fderiv ℝ (fullHardUpper η lam R L) p‖ ≤
            (Ca + Cell + lam) * ‖q - p‖) := by
  obtain ⟨Ca, hCa, hvisible⟩ := exists_visible_hidden_composition_scales
  obtain ⟨Cell, hCell, hcutoff⟩ := exists_cutoffPrimitive_second_bound
  refine ⟨Ca, Cell, hCa, hCell, ?_⟩
  intro E _ _ T η lam R hη hT hlam hR L hL
  have hA : ContDiff ℝ ∞ (fullHardVisible η L) :=
    (hardVisibleMap_contDiff hη hT L).comp
      (fullZProjection (E := E)).contDiff
  have hell : ContDiff ℝ ∞
      (fullCutoffPrimitive : E × (E × ℝ) → ℝ) :=
    cutoffPrimitive_contDiff.comp (fullVProjection (E := E)).contDiff
  have hhub : ContDiff ℝ ∞ (fullPseudoHuber lam R) :=
    (pseudoHuber_contDiff hR.ne').comp
      (fullZProjection (E := E)).contDiff
  have hAB (p : E × (E × ℝ)) :
      ‖iteratedFDeriv ℝ 2 (fullHardVisible η L) p‖ ≤ Ca :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (hardVisibleMap_contDiff hη hT L) (fullZProjection (E := E))
      (norm_fullZProjection_le_one (E := E)) 2 p).trans
        (hvisible hη hT hL p.2.1).2.1
  have hellB (p : E × (E × ℝ)) :
      ‖iteratedFDeriv ℝ 2
        (fullCutoffPrimitive : E × (E × ℝ) → ℝ) p‖ ≤ Cell :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      cutoffPrimitive_contDiff (fullVProjection (E := E))
      (norm_fullVProjection_le_one (E := E)) 2 p).trans (hcutoff p.2.2)
  have hhubB (p : E × (E × ℝ)) :
      ‖iteratedFDeriv ℝ 2 (fullPseudoHuber lam R) p‖ ≤ lam :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (pseudoHuber_contDiff hR.ne') (fullZProjection (E := E))
      (norm_fullZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_pseudoHuber_two_le hlam hR p.2.1)
  exact ⟨upperPopulationSum_second_bound hA hell hhub hAB hellB hhubB,
    upperPopulationSum_gradient_lipschitz hA hell hhub hAB hellB hhubB⟩

end

end BilevelLowerBound
