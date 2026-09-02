/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractorDerivatives

/-!
# Prefix cylinders for the visible chain

The stochastic frontier has a cylinder through coordinate `k+1`.  The
complementary visible chain must satisfy the sharper cylinder through
coordinate `k`; this is the fact that prevents a failed oracle call from
revealing the next hidden direction.  This file proves both the value and the
all-order jet identities, including points on the closed `eta/4` threshold.
-/

open scoped ContDiff Topology
open Filter Set

namespace BilevelLowerBound

noncomputable section

/-- One summand of the part of the scaled chain left after removing the
frontier extractor. -/
def visibleSummand {T : ℕ} (η : ℝ) (z : ChainVector T) (i : Fin T) : ℝ :=
  η ^ 2 * ((1 - frontierLinkGate η z i) * chainLink η z i)

/-- The visible chain is the sum of its visible summands. -/
theorem visibleChain_eq_sum_visibleSummand {T : ℕ} (η : ℝ)
    (z : ChainVector T) :
    visibleChain η z = ∑ i : Fin T, visibleSummand η z i := by
  unfold visibleChain visibleSummand frontierExtractor frontierSummand
  rw [scaledChain_eq_link_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Under progress at most `k`, truncation to `k` leaves every tail gate
unchanged: all removed coordinates lie in the flat zero region of the gate. -/
theorem tailActivation_truncate_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T) :
    tailActivation η (truncate k z) i = tailActivation η z i := by
  ext j
  by_cases hij : i.val ≤ j.val
  · rw [tailActivation_apply_of_le (truncate k z) i j hij,
      tailActivation_apply_of_le z i j hij]
    by_cases hjk : j.val < k
    · rw [truncate_apply_of_lt z j hjk]
    · have hkj : k ≤ j.val := Nat.le_of_not_gt hjk
      have hjSmall : |z j| ≤ η / 4 :=
        abs_le_threshold_of_progress_le hk j hkj
      have hNormSmall : |z j / η| ≤ 1 / 4 := by
        rw [abs_div, abs_of_pos hη]
        exact (div_le_iff₀ hη).2 (by
          simpa [div_eq_mul_inv, mul_comm] using hjSmall)
      rw [truncate_apply_of_le z j hkj, zero_div,
        coordinateGate_eq_zero_of_abs_le_quarter (by norm_num),
        coordinateGate_eq_zero_of_abs_le_quarter hNormSmall]
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    rw [tailActivation_apply_of_lt (truncate k z) i j hji,
      tailActivation_apply_of_lt z i j hji]

theorem frontierLinkGate_truncate_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T) :
    frontierLinkGate η (truncate k z) i = frontierLinkGate η z i := by
  unfold frontierLinkGate
  rw [tailActivation_truncate_of_progress_le hη z hk i]

/-- A link whose current coordinate lies inside the retained prefix is
unchanged by truncation to that prefix. -/
theorem chainLink_truncate_eq_of_index_lt {T k : ℕ} {η : ℝ}
    (z : ChainVector T) (i : Fin T) (hi : i.val < k) :
    chainLink η (truncate k z) i = chainLink η z i := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
      cases i using Fin.cases with
      | zero =>
          have hk0 : 0 < k := by omega
          simp [chainLink, normalize, withInitialOne, truncate, hk0]
      | succ j =>
          unfold chainLink
          rw [withInitialOne_castSucc_eq_of_index
              (normalize η (truncate k z)) j.castSucc j.succ (by rfl),
            withInitialOne_castSucc_eq_of_index
              (normalize η z) j.castSucc j.succ (by rfl)]
          unfold normalize
          simp only [chainVectorOfFun_apply]
          have hjcast : j.castSucc.val < k := by
            change j.val < k
            change j.val + 1 < k at hi
            omega
          rw [truncate_apply_of_lt z j.castSucc hjcast,
            truncate_apply_of_lt z j.succ hi]

/-- The visible summand at the boundary index `k` is zero because its entire
tail lies below the quarter threshold, so its frontier gate equals one. -/
theorem visibleSummand_eq_zero_of_index_eq_progress_bound
    {T k : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T) (hi : i.val = k) :
    visibleSummand η z i = 0 := by
  have hTail : ∀ j : Fin T, i.val ≤ j.val → |z j| ≤ η / 4 := by
    intro j hij
    exact abs_le_threshold_of_progress_le hk j (by omega)
  rw [visibleSummand,
    frontierLinkGate_eq_one_of_tail_small hη z i hTail]
  ring

/-- Value-cylinder identity for the already visible part of the chain. -/
theorem visibleChain_truncate_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) :
    visibleChain η (truncate k z) = visibleChain η z := by
  rw [visibleChain_eq_sum_visibleSummand,
    visibleChain_eq_sum_visibleSummand]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hik : i.val < k
  · unfold visibleSummand
    rw [frontierLinkGate_truncate_of_progress_le hη z hk i,
      chainLink_truncate_eq_of_index_lt z i hik]
  · have hki : k ≤ i.val := Nat.le_of_not_gt hik
    rcases hki.eq_or_lt with hEq | hLt
    · have hiEq : i.val = k := hEq.symm
      rw [visibleSummand_eq_zero_of_index_eq_progress_bound hη z hk i hiEq]
      have hTruncProgress : progress (η / 4) (truncate k z) ≤ k :=
        progress_truncate_le (by positivity) z
      rw [visibleSummand_eq_zero_of_index_eq_progress_bound hη
        (truncate k z) hTruncProgress i hiEq]
    · have hikSucc : k + 1 ≤ i.val := by omega
      have hActualZero :=
        chainLink_eq_zero_of_progress_le_index hη z hk i hikSucc
      have hTruncProgress : progress (η / 4) (truncate k z) ≤ k :=
        progress_truncate_le (by positivity) z
      have hTruncZero := chainLink_eq_zero_of_progress_le_index hη
        (truncate k z) hTruncProgress i hikSucc
      simp [visibleSummand, hActualZero, hTruncZero]

/-- Strict-tail version of the all-order visible-chain jet cylinder. -/
theorem iteratedFDeriv_visibleChain_strict_cylinder
    {T k r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hTail : ∀ i : Fin T, k ≤ i.val → |z i| < η / 4) :
    iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k z))
        (fun _ : Fin r ↦ truncateCLM k) := by
  have hEventually := eventually_progress_le_of_strict_tail z hTail
  have hEq :
      (visibleChain η : ChainVector T → ℝ) =ᶠ[nhds z]
        (fun y ↦ visibleChain η (truncate k y)) := by
    filter_upwards [hEventually] with y hy
    exact (visibleChain_truncate_of_progress_le hη y hy).symm
  have hWithin :
      (visibleChain η : ChainVector T → ℝ) =ᶠ[nhdsWithin z Set.univ]
        (fun y ↦ visibleChain η (truncate k y)) :=
    hEq.filter_mono inf_le_left
  have hJet := hWithin.iteratedFDerivWithin_eq (𝕜 := ℝ) hEq.eq_of_nhds r
  rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hJet
  rw [hJet]
  have hSmooth : ContDiff ℝ r
      (visibleChain η : ChainVector T → ℝ) :=
    (visibleChain_contDiff η).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hComp := (truncateCLM k).iteratedFDeriv_comp_right
    hSmooth z (i := r) le_rfl
  rw [truncateCLM_apply] at hComp
  exact hComp

/-- The visible-chain jet cylinder extends to points on the closed threshold
boundary by the same radial approximation used for the frontier extractor. -/
theorem iteratedFDeriv_visibleChain_cylinder_of_progress_le
    {T k r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hprog : progress (η / 4) z ≤ k) :
    iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k z))
        (fun _ : Fin r ↦ truncateCLM k) := by
  let zApprox : ℕ → ChainVector T := fun n ↦ strictApproxCoeff n • z
  have hStrict : ∀ n : ℕ, ∀ i : Fin T, k ≤ i.val →
      |zApprox n i| < η / 4 := by
    intro n i hik
    have hzi : |z i| ≤ η / 4 :=
      abs_le_threshold_of_progress_le hprog i hik
    have hc0 : 0 ≤ strictApproxCoeff n := strictApproxCoeff_nonneg n
    have hc1 : strictApproxCoeff n < 1 := strictApproxCoeff_lt_one n
    change |strictApproxCoeff n * z i| < η / 4
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      strictApproxCoeff n * |z i| ≤
          strictApproxCoeff n * (η / 4) :=
        mul_le_mul_of_nonneg_left hzi hc0
      _ < 1 * (η / 4) :=
        mul_lt_mul_of_pos_right hc1 (by positivity)
      _ = η / 4 := one_mul _
  have hApproxTendsto : Tendsto zApprox atTop (nhds z) := by
    simpa only [zApprox, one_smul] using tendsto_strictApproxCoeff.smul_const z
  have hTruncateTendsto :
      Tendsto (fun n ↦ truncate k (zApprox n)) atTop
        (nhds (truncate k z)) := by
    change Tendsto ((truncateCLM (T := T) k) ∘ zApprox) atTop
      (nhds (truncateCLM k z))
    exact (truncateCLM (T := T) k).continuous.continuousAt.tendsto.comp
      hApproxTendsto
  have hJetContinuous : Continuous
      (fun y : ChainVector T ↦
        iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ) y) :=
    (visibleChain_contDiff η).continuous_iteratedFDeriv
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hLeftTendsto := hJetContinuous.continuousAt.tendsto.comp hApproxTendsto
  let pullback :
      ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ ChainVector T) ℝ →
        ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ ChainVector T) ℝ :=
    fun M ↦ M.compContinuousLinearMap (fun _ : Fin r ↦ truncateCLM k)
  have hPullbackContinuous : Continuous pullback :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin r ↦ truncateCLM k)).continuous
  have hBaseTendsto :
      Tendsto (fun n ↦ iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k (zApprox n))) atTop
        (nhds (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k z))) :=
    hJetContinuous.continuousAt.tendsto.comp hTruncateTendsto
  have hRightTendsto :
      Tendsto (fun n ↦ pullback
          (iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ)
            (truncate k (zApprox n)))) atTop
        (nhds (pullback (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k z)))) :=
    hPullbackContinuous.continuousAt.tendsto.comp hBaseTendsto
  have hPointwise : ∀ n : ℕ,
      iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ) (zApprox n) =
        pullback (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k (zApprox n))) := by
    intro n
    exact iteratedFDeriv_visibleChain_strict_cylinder hη
      (zApprox n) (hStrict n)
  have hRightAsLeft :
      Tendsto (fun n ↦ iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (zApprox n)) atTop
        (nhds (pullback (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ) (truncate k z)))) :=
    hRightTendsto.congr' (Eventually.of_forall fun n ↦ (hPointwise n).symm)
  exact tendsto_nhds_unique hLeftTendsto hRightAsLeft

/-- Closed jet-cylinder identity at the actual visible prefix. -/
theorem iteratedFDeriv_visibleChain_progress_cylinder
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) :
    iteratedFDeriv ℝ r (visibleChain η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (visibleChain η : ChainVector T → ℝ)
          (truncate (progress (η / 4) z) z))
        (fun _ : Fin r ↦ truncateCLM (progress (η / 4) z)) := by
  exact iteratedFDeriv_visibleChain_cylinder_of_progress_le hη z le_rfl

end

end BilevelLowerBound
