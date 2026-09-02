/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractorDerivatives

/-!
# Localization of the frontier-extractor jet

This file proves that, at every point and at every derivative order, the full
jet of the frontier extractor is carried by at most one summand.  This is the
structural input that removes a factor depending on the chain length from the
quantitative derivative estimates.
-/

open scoped ContDiff
open Filter Set

namespace BilevelLowerBound

noncomputable section

/-- The predecessor of a positive finite index. -/
def finPred {T : ℕ} (i : Fin T) (hi : 0 < i.val) : Fin T :=
  ⟨i.val - 1, by omega⟩

/-- The continuous linear map extracting and normalizing the two coordinates
used by a noninitial chain link. -/
def chainPairCLM {T : ℕ} (η : ℝ) (i : Fin T) (hi : 0 < i.val) :
    ChainVector T →L[ℝ] ℝ × ℝ :=
  ((η⁻¹) • PiLp.proj 2 (fun _ : Fin T ↦ ℝ) (finPred i hi)).prod
    ((η⁻¹) • PiLp.proj 2 (fun _ : Fin T ↦ ℝ) i)

@[simp]
theorem chainPairCLM_apply {T : ℕ} (η : ℝ) (i : Fin T)
    (hi : 0 < i.val) (z : ChainVector T) :
    chainPairCLM η i hi z = (z (finPred i hi) / η, z i / η) := by
  ext <;> simp [chainPairCLM, div_eq_mul_inv, mul_comm]

theorem chainLink_eq_comp_pair {T : ℕ} (η : ℝ) (i : Fin T)
    (hi : 0 < i.val) :
    (chainLink η · i) = chainQ.uncurry ∘ chainPairCLM η i hi := by
  funext z
  rw [Function.comp_apply, chainPairCLM_apply]
  unfold chainLink normalize withInitialOne
  simp only [chainVectorOfFun_apply, Function.uncurry_apply_pair]
  congr 2
  · rw [show i.castSucc = Fin.succ (finPred i hi) by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ, finPred]
      omega]
    simp

theorem iteratedFDeriv_chainLink_eq_zero_of_abs_pred_le_half
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (i : Fin T) (hi : 0 < i.val)
    (hpred : |z (finPred i hi)| ≤ η / 2) :
    iteratedFDeriv ℝ r (chainLink η · i) z = 0 := by
  rw [chainLink_eq_comp_pair η i hi]
  have hBase : iteratedFDeriv ℝ r (fun w : ℝ × ℝ ↦ chainQ w.1 w.2)
      (chainPairCLM η i hi z) = 0 := by
    apply iteratedFDeriv_chainQ_eq_zero_of_abs_fst_le_half
    have hs : |z (finPred i hi) / η| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hη]
      apply (div_le_iff₀ hη).2
      nlinarith
    simpa [chainPairCLM, div_eq_mul_inv, mul_comm] using hs
  change iteratedFDeriv ℝ r
    ((fun w : ℝ × ℝ ↦ chainQ w.1 w.2) ∘ chainPairCLM η i hi) z = 0
  rw [(chainPairCLM η i hi).iteratedFDeriv_comp_right
    chainQ_contDiff z (i := r)
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)]
  rw [chainPairCLM_apply] at hBase
  rw [chainPairCLM_apply]
  rw [hBase]
  rfl

theorem eventually_frontierLinkGate_eq_zero_of_index_lt_progress
    {T : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : i.val < progress (η / 2) z) :
    (fun y : ChainVector T ↦ frontierLinkGate η y i) =ᶠ[nhds z]
      (fun _ ↦ (0 : ℝ)) := by
  have hmpos : 0 < progress (η / 2) z := by omega
  obtain ⟨j, hjlarge, hjindex⟩ :=
    exists_coordinate_at_progress (c := η / 2) (z := z) hmpos
  have hij : i.val ≤ j.val := by omega
  have hCont : ContinuousAt (fun y : ChainVector T ↦ |y j|) z :=
    (continuous_abs.comp
      (PiLp.continuous_apply 2 (fun _ : Fin T ↦ ℝ) j)).continuousAt
  have hEventually : ∀ᶠ y in nhds z, η / 2 < |y j| :=
    hCont.tendsto.eventually (Ioi_mem_nhds hjlarge)
  filter_upwards [hEventually] with y hy
  have hjhalf : 1 / 2 ≤ |y j / η| := by
    rw [abs_div, abs_of_pos hη]
    apply le_of_lt
    apply (lt_div_iff₀ hη).2
    nlinarith
  exact frontierLinkGate_eq_zero_of_tail_coordinate_one η y i j hij
    (coordinateGate_eq_one_of_half_le_abs hjhalf)

theorem iteratedFDeriv_frontierSummand_eq_zero_of_index_lt_progress
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : i.val < progress (η / 2) z) :
    iteratedFDeriv ℝ r (frontierSummand η · i) z = 0 := by
  have hLocalGate :=
    eventually_frontierLinkGate_eq_zero_of_index_lt_progress hη z i hi
  have hLocalSummand :
      (frontierSummand η · i) =ᶠ[nhds z] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hLocalGate] with y hy
    simp [frontierSummand, hy]
  have hJet := hLocalSummand.iteratedFDeriv (𝕜 := ℝ) r
  simpa using hJet.eq_of_nhds

theorem iteratedFDeriv_frontierSummand_eq_zero_of_progress_lt_index
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : progress (η / 2) z < i.val) :
    iteratedFDeriv ℝ r (frontierSummand η · i) z = 0 := by
  have hiPos : 0 < i.val := by omega
  have hPredIndex : progress (η / 2) z ≤ (finPred i hiPos).val := by
    simp only [finPred]
    omega
  have hPredSmall : |z (finPred i hiPos)| ≤ η / 2 :=
    abs_le_threshold_of_progress_le (le_refl _) _ hPredIndex
  have hLinkJets : ∀ s : ℕ,
      iteratedFDeriv ℝ s (chainLink η · i) z = 0 := fun s ↦
    iteratedFDeriv_chainLink_eq_zero_of_abs_pred_le_half
      hη z i hiPos hPredSmall
  let product : ChainVector T → ℝ := fun y ↦
    frontierLinkGate η y i * chainLink η y i
  have hProductSmooth : ContDiff ℝ ∞ product :=
    (frontierLinkGate_contDiff η i).mul (chainLink_contDiff η i)
  have hProductNorm := norm_iteratedFDeriv_mul_le
    (frontierLinkGate_contDiff η i) (chainLink_contDiff η i) z
    (n := r) (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  simp_rw [hLinkJets] at hProductNorm
  simp only [norm_zero, mul_zero, Finset.sum_const_zero] at hProductNorm
  have hProductZero : iteratedFDeriv ℝ r product z = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm hProductNorm (norm_nonneg _)
  change iteratedFDeriv ℝ r (fun y ↦ η ^ 2 * product y) z = 0
  rw [show (fun y ↦ η ^ 2 * product y) = (η ^ 2) • product by
    funext y
    simp [smul_eq_mul]]
  calc
    iteratedFDeriv ℝ r ((η ^ 2) • product) z =
        η ^ 2 • iteratedFDeriv ℝ r product z :=
      iteratedFDeriv_const_smul_apply
        ((hProductSmooth.of_le
          (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
    _ = 0 := by rw [hProductZero, smul_zero]

theorem iteratedFDeriv_frontierSummand_zero_unless_frontier
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hne : i.val ≠ progress (η / 2) z) :
    iteratedFDeriv ℝ r (frontierSummand η · i) z = 0 := by
  rcases lt_or_gt_of_ne hne with hi | hi
  · exact iteratedFDeriv_frontierSummand_eq_zero_of_index_lt_progress
      hη z i hi
  · exact iteratedFDeriv_frontierSummand_eq_zero_of_progress_lt_index
      hη z i hi

/-- At every point the complete extractor jet is carried by at most one
summand, namely the link whose zero-based index is the `eta/2` progress. -/
theorem iteratedFDeriv_frontierExtractor_eq_frontier_summand
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hm : progress (η / 2) z < T) :
    iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) z =
      iteratedFDeriv ℝ r
        (frontierSummand η · (⟨progress (η / 2) z, hm⟩ : Fin T)) z := by
  unfold frontierExtractor
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_eq_single
    · intro i _hi hne
      apply iteratedFDeriv_frontierSummand_zero_unless_frontier hη z i
      intro heq
      apply hne
      apply Fin.ext
      exact heq
    · intro hnotmem
      exact (hnotmem (Finset.mem_univ _)).elim
  · intro i _hi
    exact (frontierSummand_contDiff η i).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt

/-- Once all chain coordinates have crossed the half-scale threshold, every
derivative of the extractor vanishes. -/
theorem iteratedFDeriv_frontierExtractor_eq_zero_of_full_progress
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hfull : progress (η / 2) z = T) :
    iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) z = 0 := by
  unfold frontierExtractor
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_eq_zero
    intro i _hi
    apply iteratedFDeriv_frontierSummand_eq_zero_of_index_lt_progress hη z i
    rw [hfull]
    exact i.isLt
  · intro i _hi
    exact (frontierSummand_contDiff η i).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt

end

end BilevelLowerBound
