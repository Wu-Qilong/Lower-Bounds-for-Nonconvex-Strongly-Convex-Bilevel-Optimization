/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.SoftProjectionQuantitative
import Mathlib.Analysis.Convex.Strong

/-!
# Quantitative population regularity

This module verifies the analytic core of the paper's uniform-population-
regularity lemma.  It first proves the exact cutoff scaling
`psi_eta(v) = eta psi_1(v / eta)`.  It then derives global derivative bounds
through order three and combines them with the already verified hidden
frontier scales.  The resulting estimates control the full compensated block
on the product space, including every mixed derivative:

* `norm (D^2 R) <= C_Hess eta`;
* `norm (D^3 R) <= C_third`.

The final directional-Hessian theorem is the quantitative certificate behind
the `(2 kappa)^{-1}` lower-level strong-convexity claim.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Uniform cutoff constants and exact scaling -/

theorem eventually_iteratedFDeriv_compactIdentity_one_eq_zero_atTop
    (n : ℕ) :
    (fun v : ℝ ↦ iteratedFDeriv ℝ n (compactIdentity 1) v) =ᶠ[atTop]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with v hv
  have hLocal : compactIdentity 1 =ᶠ[nhds v] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < v by linarith)] with y hy
    change (2 : ℝ) < y at hy
    exact compactIdentity_eq_zero (by norm_num)
      (by rw [abs_of_pos (by linarith)]; norm_num; exact hy.le)
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hAt

theorem eventually_iteratedFDeriv_compactIdentity_one_eq_zero_atBot
    (n : ℕ) :
    (fun v : ℝ ↦ iteratedFDeriv ℝ n (compactIdentity 1) v) =ᶠ[atBot]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_le_atBot (-3 : ℝ)] with v hv
  have hLocal : compactIdentity 1 =ᶠ[nhds v] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Iio_mem_nhds (show v < (-2 : ℝ) by linarith)] with y hy
    change y < (-2 : ℝ) at hy
    exact compactIdentity_eq_zero (by norm_num)
      (by rw [abs_of_neg (by linarith)]; norm_num; linarith)
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hAt

theorem isBounded_range_iteratedFDeriv_compactIdentity_one (n : ℕ) :
    Bornology.IsBounded
      (Set.range (fun v : ℝ ↦
        iteratedFDeriv ℝ n (compactIdentity 1) v)) := by
  have hCont : Continuous (fun v : ℝ ↦
      iteratedFDeriv ℝ n (compactIdentity 1) v) :=
    (compactIdentity_contDiff (by norm_num : (1 : ℝ) ≠ 0)).continuous_iteratedFDeriv
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
  apply hCont.isBounded_range_iff_isBigO_atTop_atBot.mpr
  constructor
  · have hTendsto : Tendsto
        (fun v : ℝ ↦ iteratedFDeriv ℝ n (compactIdentity 1) v) atTop
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_compactIdentity_one_eq_zero_atTop n).symm
    exact hTendsto.isBigO_one ℝ
  · have hTendsto : Tendsto
        (fun v : ℝ ↦ iteratedFDeriv ℝ n (compactIdentity 1) v) atBot
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_compactIdentity_one_eq_zero_atBot n).symm
    exact hTendsto.isBigO_one ℝ

theorem exists_bound_compactIdentity_one_iteratedFDeriv (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ C := by
  have hBounded := isBounded_range_iteratedFDeriv_compactIdentity_one n
  rw [isBounded_iff_forall_norm_le] at hBounded
  obtain ⟨C, hC⟩ := hBounded
  refine ⟨max C 0, le_max_right _ _, fun v ↦ ?_⟩
  exact (hC _ ⟨v, rfl⟩).trans (le_max_left C 0)

theorem exists_common_bound_compactIdentity_one_three :
    ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ := by
  obtain ⟨C0, hC00, hC0⟩ :=
    exists_bound_compactIdentity_one_iteratedFDeriv 0
  obtain ⟨C1, hC10, hC1⟩ :=
    exists_bound_compactIdentity_one_iteratedFDeriv 1
  obtain ⟨C2, hC20, hC2⟩ :=
    exists_bound_compactIdentity_one_iteratedFDeriv 2
  obtain ⟨C3, hC30, hC3⟩ :=
    exists_bound_compactIdentity_one_iteratedFDeriv 3
  refine ⟨C0 + C1 + C2 + C3, by positivity, fun n hn v ↦ ?_⟩
  interval_cases n
  · exact (hC0 v).trans (by linarith)
  · exact (hC1 v).trans (by linarith)
  · exact (hC2 v).trans (by linarith)
  · exact (hC3 v).trans (by linarith)

def scalarNormalizeCLM (η : ℝ) : ℝ →L[ℝ] ℝ :=
  η⁻¹ • ContinuousLinearMap.id ℝ ℝ

@[simp]
theorem scalarNormalizeCLM_apply (η v : ℝ) :
    scalarNormalizeCLM η v = v / η := by
  simp [scalarNormalizeCLM, div_eq_mul_inv, mul_comm]

theorem norm_scalarNormalizeCLM_le_inv {η : ℝ} (hη : 0 < η) :
    ‖scalarNormalizeCLM η‖ ≤ η⁻¹ := by
  unfold scalarNormalizeCLM
  calc
    ‖η⁻¹ • ContinuousLinearMap.id ℝ ℝ‖ =
        ‖η⁻¹‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ := norm_smul _ _
    _ ≤ η⁻¹ * 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hη.le)]
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = η⁻¹ := mul_one _

theorem compactIdentity_scaling {η : ℝ} (hη : η ≠ 0) (v : ℝ) :
    compactIdentity η v =
      η * compactIdentity 1 (scalarNormalizeCLM η v) := by
  unfold compactIdentity
  rw [scalarNormalizeCLM_apply]
  field_simp [hη]

theorem norm_iteratedFDeriv_comp_clm_le_of_bound
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤
      ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)]
  calc
    ‖(iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ ↦ L)‖ ≤
        ‖iteratedFDeriv ℝ n f (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * 1 := by
      gcongr
      apply Finset.prod_le_one
      · intro i _hi
        exact norm_nonneg _
      · intro i _hi
        exact hL
    _ = ‖iteratedFDeriv ℝ n f (L x)‖ := mul_one _

theorem norm_iteratedFDeriv_compactIdentity_le
    {η Cψ : ℝ} (hη : 0 < η) (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (n : ℕ) (hn : n ≤ 3) (v : ℝ) :
    ‖iteratedFDeriv ℝ n (compactIdentity η) v‖ ≤
      Cψ * η * (η⁻¹) ^ n := by
  have hSmooth : ContDiff ℝ ∞
      ((compactIdentity 1) ∘ scalarNormalizeCLM η) :=
    (compactIdentity_contDiff (by norm_num : (1 : ℝ) ≠ 0)).comp
      (scalarNormalizeCLM η).contDiff
  have hFun : compactIdentity η =
      η • ((compactIdentity 1) ∘ scalarNormalizeCLM η) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, comp_apply]
    exact compactIdentity_scaling hη.ne' y
  rw [hFun]
  rw [iteratedFDeriv_const_smul_apply
    ((hSmooth.of_le (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
    norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos hη]
  rw [(scalarNormalizeCLM η).iteratedFDeriv_comp_right
    (compactIdentity_contDiff (by norm_num : (1 : ℝ) ≠ 0)) v
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)]
  calc
    η * ‖(iteratedFDeriv ℝ n (compactIdentity 1)
        (scalarNormalizeCLM η v)).compContinuousLinearMap
          (fun _ ↦ scalarNormalizeCLM η)‖ ≤
        η * (‖iteratedFDeriv ℝ n (compactIdentity 1)
          (scalarNormalizeCLM η v)‖ *
            ∏ _ : Fin n, ‖scalarNormalizeCLM η‖) := by
      gcongr
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ η * (Cψ * ∏ _ : Fin n, η⁻¹) := by
      gcongr
      · exact hCψ n hn _
      · exact norm_scalarNormalizeCLM_le_inv hη
    _ = Cψ * η * (η⁻¹) ^ n := by
      rw [Fin.prod_const]
      ring

theorem norm_compactIdentity_value_le
    {η Cψ : ℝ} (hη : 0 < η) (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (v : ℝ) : |compactIdentity η v| ≤ Cψ * η := by
  have h := norm_iteratedFDeriv_compactIdentity_le
    hη hCψ0 hCψ 0 (by norm_num) v
  simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h

theorem norm_iteratedFDeriv_compactIdentity_one_le
    {η Cψ : ℝ} (hη : 0 < η) (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (v : ℝ) :
    ‖iteratedFDeriv ℝ 1 (compactIdentity η) v‖ ≤ Cψ := by
  have h := norm_iteratedFDeriv_compactIdentity_le
    hη hCψ0 hCψ 1 (by norm_num) v
  norm_num at h ⊢
  field_simp [hη.ne'] at h
  simpa [mul_comm] using h

theorem norm_iteratedFDeriv_compactIdentity_two_le
    {η Cψ : ℝ} (hη : 0 < η) (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (v : ℝ) :
    ‖iteratedFDeriv ℝ 2 (compactIdentity η) v‖ ≤ Cψ / η := by
  have h := norm_iteratedFDeriv_compactIdentity_le
    hη hCψ0 hCψ 2 (by norm_num) v
  norm_num at h ⊢
  field_simp [hη.ne'] at h ⊢
  nlinarith

theorem norm_iteratedFDeriv_compactIdentity_three_le
    {η Cψ : ℝ} (hη : 0 < η) (hCψ0 : 0 ≤ Cψ)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (v : ℝ) :
    ‖iteratedFDeriv ℝ 3 (compactIdentity η) v‖ ≤ Cψ / η ^ 2 := by
  have h := norm_iteratedFDeriv_compactIdentity_le
    hη hCψ0 hCψ 3 (by norm_num) v
  norm_num at h ⊢
  field_simp [hη.ne'] at h ⊢
  nlinarith

/-! ## Product estimates through order three -/

theorem norm_iteratedFDeriv_mul_two_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {F0 F1 F2 G0 G1 G2 : ℝ} (x : E)
    (hf0 : ‖iteratedFDeriv ℝ 0 f x‖ ≤ F0)
    (hf1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ F1)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ F2)
    (hg0 : ‖iteratedFDeriv ℝ 0 g x‖ ≤ G0)
    (hg1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ G1)
    (hg2 : ‖iteratedFDeriv ℝ 2 g x‖ ≤ G2) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ f y * g y) x‖ ≤
      F0 * G2 + 2 * F1 * G1 + F2 * G0 := by
  calc
    ‖iteratedFDeriv ℝ 2 (fun y ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ((2 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (2 - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)
    _ ≤ F0 * G2 + 2 * F1 * G1 + F2 * G0 := by
      have hf0' : |f x| ≤ F0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hf0
      have hf1' : ‖fderiv ℝ f x‖ ≤ F1 := by
        simpa [norm_iteratedFDeriv_one] using hf1
      have hg0' : |g x| ≤ G0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg0
      have hg1' : ‖fderiv ℝ g x‖ ≤ G1 := by
        simpa [norm_iteratedFDeriv_one] using hg1
      have hF0 : 0 ≤ F0 := (abs_nonneg (f x)).trans hf0'
      have hF1 : 0 ≤ F1 := (norm_nonneg _).trans hf1'
      have hF2 : 0 ≤ F2 := (norm_nonneg _).trans hf2
      have hG0 : 0 ≤ G0 := (abs_nonneg (g x)).trans hg0'
      have hG1 : 0 ≤ G1 := (norm_nonneg _).trans hg1'
      have hG2 : 0 ≤ G2 := (norm_nonneg _).trans hg2
      norm_num [Finset.sum_range_succ]
      gcongr

theorem norm_iteratedFDeriv_mul_three_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {F0 F1 F2 F3 G0 G1 G2 G3 : ℝ} (x : E)
    (hf0 : ‖iteratedFDeriv ℝ 0 f x‖ ≤ F0)
    (hf1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ F1)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ F2)
    (hf3 : ‖iteratedFDeriv ℝ 3 f x‖ ≤ F3)
    (hg0 : ‖iteratedFDeriv ℝ 0 g x‖ ≤ G0)
    (hg1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ G1)
    (hg2 : ‖iteratedFDeriv ℝ 2 g x‖ ≤ G2)
    (hg3 : ‖iteratedFDeriv ℝ 3 g x‖ ≤ G3) :
    ‖iteratedFDeriv ℝ 3 (fun y ↦ f y * g y) x‖ ≤
      F0 * G3 + 3 * F1 * G2 + 3 * F2 * G1 + F3 * G0 := by
  calc
    ‖iteratedFDeriv ℝ 3 (fun y ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (3 + 1),
          ((3 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (3 - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)
    _ ≤ F0 * G3 + 3 * F1 * G2 + 3 * F2 * G1 + F3 * G0 := by
      have hf0' : |f x| ≤ F0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hf0
      have hf1' : ‖fderiv ℝ f x‖ ≤ F1 := by
        simpa [norm_iteratedFDeriv_one] using hf1
      have hg0' : |g x| ≤ G0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg0
      have hg1' : ‖fderiv ℝ g x‖ ≤ G1 := by
        simpa [norm_iteratedFDeriv_one] using hg1
      have hF0 : 0 ≤ F0 := (abs_nonneg (f x)).trans hf0'
      have hF1 : 0 ≤ F1 := (norm_nonneg _).trans hf1'
      have hF2 : 0 ≤ F2 := (norm_nonneg _).trans hf2
      have hF3 : 0 ≤ F3 := (norm_nonneg _).trans hf3
      have hG0 : 0 ≤ G0 := (abs_nonneg (g x)).trans hg0'
      have hG1 : 0 ≤ G1 := (norm_nonneg _).trans hg1'
      have hG2 : 0 ≤ G2 := (norm_nonneg _).trans hg2
      have hG3 : 0 ≤ G3 := (norm_nonneg _).trans hg3
      norm_num [Finset.sum_range_succ]
      gcongr

def compensatedPair {E : Type*} (η : ℝ) (θ : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ compensatedBlock η θ p.1 p.2

theorem compensatedPair_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : η ≠ 0) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (compensatedPair η θ) := by
  change ContDiff ℝ ∞ (fun p : E × ℝ ↦
    compensatedBlock η θ p.1 p.2)
  exact compensatedBlock_contDiff hη hθ

/-- The complete compensated block has the precise `O(eta)` Hessian and
`O(1)` third derivative needed by the population regularity lemma.  Since the
estimate is made on `E × R` directly, it includes all `zz`, `zv`, and `vv`
blocks and all third-order mixed permutations. -/
theorem compensatedPair_second_third_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η Cθ Cψ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hCψ0 : 0 ≤ Cψ)
    {θ : E → ℝ} (hθSmooth : ContDiff ℝ ∞ θ)
    (hθ0 : ∀ z : E, |θ z| ≤ Cθ * η ^ 2)
    (hθ1 : ∀ z : E,
      ‖iteratedFDeriv ℝ 1 θ z‖ ≤ Cθ * η)
    (hθ2 : ∀ z : E,
      ‖iteratedFDeriv ℝ 2 θ z‖ ≤ Cθ)
    (hθ3 : ∀ z : E,
      ‖iteratedFDeriv ℝ 3 θ z‖ ≤ Cθ / η)
    (hCψ : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cψ)
    (p : E × ℝ) :
    ‖iteratedFDeriv ℝ 2 (compensatedPair η θ) p‖ ≤
        2 * Cθ * (Cθ + 2 * Cψ) * η ∧
      ‖iteratedFDeriv ℝ 3 (compensatedPair η θ) p‖ ≤
        4 * Cθ * (Cθ + 2 * Cψ) := by
  let Lz : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let Lv : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let Θ : E × ℝ → ℝ := θ ∘ Lz
  let Ψ : E × ℝ → ℝ := (compactIdentity η) ∘ Lv
  let TT : E × ℝ → ℝ := fun y ↦ Θ y * Θ y
  let TP : E × ℝ → ℝ := fun y ↦ Θ y * Ψ y
  let TH : E × ℝ → ℝ := fun y ↦ (2 : ℝ)⁻¹ * TT y
  have hLz : ‖Lz‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ E ℝ
  have hLv : ‖Lv‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ E ℝ
  have hΘSmooth : ContDiff ℝ ∞ Θ := hθSmooth.comp Lz.contDiff
  have hΨSmooth : ContDiff ℝ ∞ Ψ :=
    (compactIdentity_contDiff hη.ne').comp Lv.contDiff
  have hΘ0 : ‖iteratedFDeriv ℝ 0 Θ p‖ ≤ Cθ * η ^ 2 := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hθ0 p.1
  have hΘ1 : ‖iteratedFDeriv ℝ 1 Θ p‖ ≤ Cθ * η :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound hθSmooth Lz hLz 1 p).trans
      (hθ1 p.1)
  have hΘ2 : ‖iteratedFDeriv ℝ 2 Θ p‖ ≤ Cθ :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound hθSmooth Lz hLz 2 p).trans
      (hθ2 p.1)
  have hΘ3 : ‖iteratedFDeriv ℝ 3 Θ p‖ ≤ Cθ / η :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound hθSmooth Lz hLz 3 p).trans
      (hθ3 p.1)
  have hΨ0 : ‖iteratedFDeriv ℝ 0 Ψ p‖ ≤ Cψ * η := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact norm_compactIdentity_value_le hη hCψ0 hCψ p.2
  have hΨ1 : ‖iteratedFDeriv ℝ 1 Ψ p‖ ≤ Cψ :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff hη.ne') Lv hLv 1 p).trans
        (norm_iteratedFDeriv_compactIdentity_one_le hη hCψ0 hCψ p.2)
  have hΨ2 : ‖iteratedFDeriv ℝ 2 Ψ p‖ ≤ Cψ / η :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff hη.ne') Lv hLv 2 p).trans
        (norm_iteratedFDeriv_compactIdentity_two_le hη hCψ0 hCψ p.2)
  have hΨ3 : ‖iteratedFDeriv ℝ 3 Ψ p‖ ≤ Cψ / η ^ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff hη.ne') Lv hLv 3 p).trans
        (norm_iteratedFDeriv_compactIdentity_three_le hη hCψ0 hCψ p.2)
  have hTT2 : ‖iteratedFDeriv ℝ 2 TT p‖ ≤
      4 * Cθ ^ 2 * η ^ 2 := by
    have h := norm_iteratedFDeriv_mul_two_le hΘSmooth hΘSmooth p
      hΘ0 hΘ1 hΘ2 hΘ0 hΘ1 hΘ2
    refine h.trans ?_
    ring_nf
    exact le_rfl
  have hTP2 : ‖iteratedFDeriv ℝ 2 TP p‖ ≤
      4 * Cθ * Cψ * η := by
    have h := norm_iteratedFDeriv_mul_two_le hΘSmooth hΨSmooth p
      hΘ0 hΘ1 hΘ2 hΨ0 hΨ1 hΨ2
    refine h.trans ?_
    field_simp [hη.ne']
    ring_nf
    exact le_rfl
  have hTT3 : ‖iteratedFDeriv ℝ 3 TT p‖ ≤
      8 * Cθ ^ 2 * η := by
    have h := norm_iteratedFDeriv_mul_three_le hΘSmooth hΘSmooth p
      hΘ0 hΘ1 hΘ2 hΘ3 hΘ0 hΘ1 hΘ2 hΘ3
    refine h.trans ?_
    field_simp [hη.ne']
    ring_nf
    exact le_rfl
  have hTP3 : ‖iteratedFDeriv ℝ 3 TP p‖ ≤
      8 * Cθ * Cψ := by
    have h := norm_iteratedFDeriv_mul_three_le hΘSmooth hΨSmooth p
      hΘ0 hΘ1 hΘ2 hΘ3 hΨ0 hΨ1 hΨ2 hΨ3
    refine h.trans ?_
    field_simp [hη.ne']
    ring_nf
    exact le_rfl
  have hTTSmooth : ContDiff ℝ ∞ TT := hΘSmooth.mul hΘSmooth
  have hTPSmooth : ContDiff ℝ ∞ TP := hΘSmooth.mul hΨSmooth
  have hTHSmooth : ContDiff ℝ ∞ TH := contDiff_const.mul hTTSmooth
  have hTHFun : TH = (2 : ℝ)⁻¹ • TT := by
    funext y
    rfl
  have hFun : compensatedPair η θ = TH - TP := by
    funext y
    simp only [Pi.sub_apply]
    simp [compensatedPair, compensatedBlock, TH, TT, TP, Θ, Ψ, Lz, Lv]
    ring
  have hHalf2 : ‖iteratedFDeriv ℝ 2 TH p‖ ≤
      2 * Cθ ^ 2 * η ^ 2 := by
    rw [hTHFun]
    rw [iteratedFDeriv_const_smul_apply
      ((hTTSmooth.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
      norm_smul]
    norm_num
    linarith
  have hHalf3 : ‖iteratedFDeriv ℝ 3 TH p‖ ≤
      4 * Cθ ^ 2 * η := by
    rw [hTHFun]
    rw [iteratedFDeriv_const_smul_apply
      ((hTTSmooth.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
      norm_smul]
    norm_num
    linarith
  rw [hFun]
  constructor
  · rw [iteratedFDeriv_sub_apply
      ((hTHSmooth.of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt))
      ((hTPSmooth.of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
    calc
      ‖iteratedFDeriv ℝ 2 TH p -
          iteratedFDeriv ℝ 2 TP p‖ ≤
          ‖iteratedFDeriv ℝ 2 TH p‖ +
            ‖iteratedFDeriv ℝ 2 TP p‖ := norm_sub_le _ _
      _ ≤ 2 * Cθ ^ 2 * η ^ 2 + 4 * Cθ * Cψ * η :=
        add_le_add hHalf2 hTP2
      _ ≤ 2 * Cθ * (Cθ + 2 * Cψ) * η := by
        nlinarith [mul_nonneg (sq_nonneg Cθ)
            (mul_nonneg hη.le (sub_nonneg.mpr hη1))]
  · rw [iteratedFDeriv_sub_apply
      ((hTHSmooth.of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt))
      ((hTPSmooth.of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
    calc
      ‖iteratedFDeriv ℝ 3 TH p -
          iteratedFDeriv ℝ 3 TP p‖ ≤
          ‖iteratedFDeriv ℝ 3 TH p‖ +
            ‖iteratedFDeriv ℝ 3 TP p‖ := norm_sub_le _ _
      _ ≤ 4 * Cθ ^ 2 * η + 8 * Cθ * Cψ :=
        add_le_add hHalf3 hTP3
      _ ≤ 4 * Cθ * (Cθ + 2 * Cψ) := by
        nlinarith [mul_nonneg (sq_nonneg Cθ) (sub_nonneg.mpr hη1)]

def hardFrontierMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η : ℝ) (L : E →L[ℝ] ChainVector T) : E → ℝ :=
  (frontierExtractor η : ChainVector T → ℝ) ∘
    hiddenProbe (hardRadius η T) L

theorem hardFrontierMap_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (hardFrontierMap η L) := by
  exact (frontierExtractor_contDiff η).comp
    (hiddenProbe_contDiff (hardRadius_pos hη hT).ne' L)

/-- Uniform compensated-block constants for the actual hidden hard instance.
They are independent of the chain length, ambient dimension, scaling
parameter, and hidden contraction. -/
theorem exists_hard_compensated_pair_regularities :
    ∃ CHess Cthird : ℝ, 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {η : ℝ}, 0 < η → η ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 → ∀ p : E × ℝ,
        ‖iteratedFDeriv ℝ 2
            (compensatedPair η (hardFrontierMap η L)) p‖ ≤ CHess * η ∧
        ‖iteratedFDeriv ℝ 3
            (compensatedPair η (hardFrontierMap η L)) p‖ ≤ Cthird := by
  obtain ⟨Cθ, hCθ0, hθ⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨Cψ, hCψ0, hψ⟩ :=
    exists_common_bound_compactIdentity_one_three
  let CHess : ℝ := 2 * Cθ * (Cθ + 2 * Cψ)
  let Cthird : ℝ := 4 * Cθ * (Cθ + 2 * Cψ)
  refine ⟨CHess, Cthird, by dsimp [CHess]; positivity,
    by dsimp [Cthird]; positivity, ?_⟩
  intro E _ _ T η hη hη1 hT L hL p
  have hθAll := hθ hη hT hL
  have hθSmooth : ContDiff ℝ ∞ (hardFrontierMap η L) :=
    hardFrontierMap_contDiff hη hT L
  have hbounds := compensatedPair_second_third_bounds
    hη hη1 hCψ0 hθSmooth
    (fun z ↦ (hθAll z).1)
    (fun z ↦ (hθAll z).2.1)
    (fun z ↦ (hθAll z).2.2.1)
    (fun z ↦ (hθAll z).2.2.2)
    hψ p
  simpa [CHess, Cthird] using hbounds

/-! ## Strong-convexity perturbation certificate -/

/-- A second-order perturbation whose operator norm is at most `C eta` can
reduce a diagonal Hessian by at most `C eta * norm(w)^2`.  This is the exact
Weyl-type step used in the paper; it is stated for arbitrary normed spaces
and therefore does not hide a finite-dimensional spectral assumption. -/
theorem diagonal_hessian_lower_bound_of_perturbation
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {κ C η : ℝ} (hκ : 0 < κ) (hCη : C * η ≤ 1 / (2 * κ))
    (B R : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ F) ℝ)
    (hB : ∀ w : F,
      (1 / κ) * ‖w‖ ^ 2 ≤ B (fun _ ↦ w))
    (hR : ‖R‖ ≤ C * η) (w : F) :
    (1 / (2 * κ)) * ‖w‖ ^ 2 ≤ (B + R) (fun _ ↦ w) := by
  have hRapply := R.le_opNorm (fun _ : Fin 2 ↦ w)
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at hRapply
  have hRabs : |R (fun _ : Fin 2 ↦ w)| ≤ C * η * ‖w‖ ^ 2 := by
    calc
      |R (fun _ : Fin 2 ↦ w)| ≤ ‖R‖ * (‖w‖ * ‖w‖) := hRapply
      _ ≤ (C * η) * (‖w‖ * ‖w‖) := by
        gcongr
      _ = C * η * ‖w‖ ^ 2 := by ring
  have hRlower : -(C * η * ‖w‖ ^ 2) ≤ R (fun _ : Fin 2 ↦ w) :=
    (abs_le.mp hRabs).1
  have hsmall : C * η * ‖w‖ ^ 2 ≤
      (1 / (2 * κ)) * ‖w‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right hCη (sq_nonneg ‖w‖)
  have hsplit : 1 / κ = 2 * (1 / (2 * κ)) := by
    field_simp [hκ.ne']
  have hBase := hB w
  rw [hsplit] at hBase
  simp only [add_apply]
  linarith

/-- Specialization of the preceding perturbation principle to the actual
hidden compensated block.  The map `B` is the Hessian of the unperturbed
quadratic lower objective; its elementary diagonal bound is kept explicit so
that this theorem can later be reused with either the paper's Euclidean
product convention or Mathlib's product norm. -/
theorem exists_hard_lower_strong_convexity_certificate :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {η κ : ℝ}, 0 < η → η ≤ 1 → 0 < κ → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        CHess * η ≤ 1 / (2 * κ) →
        ∀ (p : E × ℝ)
          (B : ContinuousMultilinearMap ℝ
            (fun _ : Fin 2 ↦ E × ℝ) ℝ),
          (∀ w : E × ℝ,
            (1 / κ) * ‖w‖ ^ 2 ≤ B (fun _ ↦ w)) →
          ∀ w : E × ℝ,
          (1 / (2 * κ)) * ‖w‖ ^ 2 ≤
            (B + iteratedFDeriv ℝ 2
              (compensatedPair η (hardFrontierMap η L)) p)
                (fun _ ↦ w) := by
  obtain ⟨CHess, Cthird, hCHess0, hCthird0, hreg⟩ :=
    exists_hard_compensated_pair_regularities
  refine ⟨CHess, hCHess0, ?_⟩
  intro E _ _ T η κ hη hη1 hκ hT L hL hsmall p B hB w
  have hR := (hreg hη hη1 hT hL p).1
  exact diagonal_hessian_lower_bound_of_perturbation
    hκ hsmall B
      (iteratedFDeriv ℝ 2
        (compensatedPair η (hardFrontierMap η L)) p)
      hB hR w

end

end BilevelLowerBound
