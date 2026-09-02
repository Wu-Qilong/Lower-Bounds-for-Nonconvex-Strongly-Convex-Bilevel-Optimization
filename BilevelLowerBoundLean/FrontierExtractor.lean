/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainHigher
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth frontier extractor

This module formalizes the extractor used to split the scaled zero chain into
an already visible part and one frontier link.  The paper writes
`vartheta(t) = Gamma(|t|)`.  We use the pointwise equal smooth expression
`Gamma(t) + Gamma(-t)`; `coordinateGate_eq_transition_abs` verifies that the
two definitions agree exactly.

The main structural statements proved here are the threshold identities, the
one-active-summand property, the zero extractor at full progress, and the
value-level cylinder identity through `P_(k+1)`.  These are the algebraic
facts on which the rotated hard instance and the stochastic frontier depend.
-/

open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

/-- The paper's transition `Gamma = gamma_(1/4,1/2)`. -/
def frontierTransition (t : ℝ) : ℝ :=
  expNegInvGlue (t - 1 / 4) /
    (expNegInvGlue (t - 1 / 4) + expNegInvGlue (1 / 2 - t))

/-- The smooth even coordinate gate.  This equals `Gamma (|t|)`. -/
def coordinateGate (t : ℝ) : ℝ :=
  frontierTransition t + frontierTransition (-t)

/-- Tail vector `V_i^eta(z)`, represented in the ambient `T` coordinates
with zeros before the index `i`. -/
def tailActivation {T : ℕ} (η : ℝ) (z : ChainVector T) (i : Fin T) :
    ChainVector T :=
  chainVectorOfFun fun j ↦
    if i.val ≤ j.val then coordinateGate (z j / η) else 0

/-- The gate multiplying the `i`-th link. -/
def frontierLinkGate {T : ℕ} (η : ℝ) (z : ChainVector T) (i : Fin T) : ℝ :=
  frontierTransition (1 - ‖tailActivation η z i‖)

/-- One summand of the frontier extractor. -/
def frontierSummand {T : ℕ} (η : ℝ) (z : ChainVector T) (i : Fin T) : ℝ :=
  η ^ 2 * (frontierLinkGate η z i * chainLink η z i)

/-- The stochastic frontier `b_(eta,T)`. -/
def frontierExtractor {T : ℕ} (η : ℝ) (z : ChainVector T) : ℝ :=
  ∑ i : Fin T, frontierSummand η z i

/-- The already visible part `A_(eta,T) = H_(eta,T) - b_(eta,T)`. -/
def visibleChain {T : ℕ} (η : ℝ) (z : ChainVector T) : ℝ :=
  scaledChain η z - frontierExtractor η z

theorem frontierTransition_denom_pos (t : ℝ) :
    0 < expNegInvGlue (t - 1 / 4) + expNegInvGlue (1 / 2 - t) := by
  by_cases ht : 1 / 4 < t
  · exact add_pos_of_pos_of_nonneg
      (expNegInvGlue.pos_of_pos (by linarith))
      (expNegInvGlue.nonneg _)
  · exact add_pos_of_nonneg_of_pos
      (expNegInvGlue.nonneg _)
      (expNegInvGlue.pos_of_pos (by linarith))

@[simp]
theorem frontierTransition_eq_zero_of_le_quarter {t : ℝ}
    (ht : t ≤ 1 / 4) :
    frontierTransition t = 0 := by
  unfold frontierTransition
  rw [expNegInvGlue.zero_of_nonpos (by linarith), zero_div]

@[simp]
theorem frontierTransition_eq_one_of_half_le {t : ℝ}
    (ht : 1 / 2 ≤ t) :
    frontierTransition t = 1 := by
  unfold frontierTransition
  have hzero : expNegInvGlue (1 / 2 - t) = 0 :=
    expNegInvGlue.zero_of_nonpos (by linarith)
  rw [hzero, add_zero]
  exact div_self (ne_of_gt (expNegInvGlue.pos_of_pos (by linarith)))

theorem frontierTransition_nonneg (t : ℝ) :
    0 ≤ frontierTransition t := by
  unfold frontierTransition
  exact div_nonneg (expNegInvGlue.nonneg _) (frontierTransition_denom_pos t).le

theorem frontierTransition_le_one (t : ℝ) :
    frontierTransition t ≤ 1 := by
  unfold frontierTransition
  exact (div_le_one (frontierTransition_denom_pos t)).2
    (le_add_of_nonneg_right (expNegInvGlue.nonneg _))

theorem frontierTransition_contDiff :
    ContDiff ℝ ∞ frontierTransition := by
  unfold frontierTransition
  exact (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).div
    ((expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).add
      (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)))
    (fun t ↦ (frontierTransition_denom_pos t).ne')

/-- The even implementation is exactly the absolute-value formula in the
paper. -/
theorem coordinateGate_eq_transition_abs (t : ℝ) :
    coordinateGate t = frontierTransition |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    unfold coordinateGate
    rw [frontierTransition_eq_zero_of_le_quarter (t := -t) (by linarith)]
    ring
  · rw [abs_of_nonpos ht]
    unfold coordinateGate
    rw [frontierTransition_eq_zero_of_le_quarter (t := t) (by linarith)]
    ring

theorem coordinateGate_contDiff : ContDiff ℝ ∞ coordinateGate := by
  unfold coordinateGate
  exact frontierTransition_contDiff.add
    (frontierTransition_contDiff.comp contDiff_id.neg)

@[simp]
theorem coordinateGate_eq_zero_of_abs_le_quarter {t : ℝ}
    (ht : |t| ≤ 1 / 4) :
    coordinateGate t = 0 := by
  rw [coordinateGate_eq_transition_abs]
  exact frontierTransition_eq_zero_of_le_quarter ht

@[simp]
theorem coordinateGate_eq_one_of_half_le_abs {t : ℝ}
    (ht : 1 / 2 ≤ |t|) :
    coordinateGate t = 1 := by
  rw [coordinateGate_eq_transition_abs]
  exact frontierTransition_eq_one_of_half_le ht

theorem coordinateGate_nonneg (t : ℝ) : 0 ≤ coordinateGate t := by
  rw [coordinateGate_eq_transition_abs]
  exact frontierTransition_nonneg _

theorem coordinateGate_le_one (t : ℝ) : coordinateGate t ≤ 1 := by
  rw [coordinateGate_eq_transition_abs]
  exact frontierTransition_le_one _

@[simp]
theorem tailActivation_apply_of_le {T : ℕ} {η : ℝ}
    (z : ChainVector T) (i j : Fin T) (hij : i.val ≤ j.val) :
    tailActivation η z i j = coordinateGate (z j / η) := by
  unfold tailActivation
  simp only [chainVectorOfFun_apply]
  rw [if_pos hij]

@[simp]
theorem tailActivation_apply_of_lt {T : ℕ} {η : ℝ}
    (z : ChainVector T) (i j : Fin T) (hji : j.val < i.val) :
    tailActivation η z i j = 0 := by
  unfold tailActivation
  simp only [chainVectorOfFun_apply]
  rw [if_neg (Nat.not_le.mpr hji)]

theorem frontierLinkGate_nonneg {T : ℕ} (η : ℝ)
    (z : ChainVector T) (i : Fin T) :
    0 ≤ frontierLinkGate η z i :=
  frontierTransition_nonneg _

theorem frontierLinkGate_le_one {T : ℕ} (η : ℝ)
    (z : ChainVector T) (i : Fin T) :
    frontierLinkGate η z i ≤ 1 :=
  frontierTransition_le_one _

/-- A unit coordinate in the tail closes the corresponding link gate. -/
theorem frontierLinkGate_eq_zero_of_tail_coordinate_one {T : ℕ}
    (η : ℝ) (z : ChainVector T) (i j : Fin T)
    (hij : i.val ≤ j.val)
    (hj : coordinateGate (z j / η) = 1) :
    frontierLinkGate η z i = 0 := by
  have hcoord : tailActivation η z i j = 1 := by
    rw [tailActivation_apply_of_le z i j hij, hj]
  have hnorm : 1 ≤ ‖tailActivation η z i‖ := by
    have h := PiLp.norm_apply_le (tailActivation η z i) j
    simpa [hcoord] using h
  unfold frontierLinkGate
  apply frontierTransition_eq_zero_of_le_quarter
  linarith

/-- If an entire tail is below the lower threshold, its activation vector is
exactly zero. -/
theorem tailActivation_eq_zero_of_tail_small {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hTail : ∀ j : Fin T, i.val ≤ j.val → |z j| ≤ η / 4) :
    tailActivation η z i = 0 := by
  ext j
  by_cases hij : i.val ≤ j.val
  · rw [tailActivation_apply_of_le z i j hij]
    apply coordinateGate_eq_zero_of_abs_le_quarter
    rw [abs_div, abs_of_pos hη]
    exact (div_le_iff₀ hη).2 (by
      simpa [div_eq_mul_inv, mul_comm] using hTail j hij)
  · rw [tailActivation_apply_of_lt z i j (Nat.lt_of_not_ge hij)]
    rfl

/-- A completely inactive tail leaves the link gate fully open. -/
theorem frontierLinkGate_eq_one_of_tail_small {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hTail : ∀ j : Fin T, i.val ≤ j.val → |z j| ≤ η / 4) :
    frontierLinkGate η z i = 1 := by
  rw [frontierLinkGate, tailActivation_eq_zero_of_tail_small hη z i hTail,
    norm_zero, sub_zero]
  exact frontierTransition_eq_one_of_half_le (by norm_num)

/-- Every summand at or before the `eta/2` progress index has a closed gate. -/
theorem frontierSummand_eq_zero_of_index_le_progress {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : i.val + 1 ≤ progress (η / 2) z) :
    frontierSummand η z i = 0 := by
  have hmpos : 0 < progress (η / 2) z := lt_of_lt_of_le (by omega) hi
  obtain ⟨j, hjlarge, hjindex⟩ :=
    exists_coordinate_at_progress (c := η / 2) (z := z) hmpos
  have hij : i.val ≤ j.val := by omega
  have hjhalf : 1 / 2 ≤ |z j / η| := by
    rw [abs_div, abs_of_pos hη]
    apply le_of_lt
    apply (lt_div_iff₀ hη).2
    nlinarith
  have hjgate : coordinateGate (z j / η) = 1 :=
    coordinateGate_eq_one_of_half_le_abs hjhalf
  unfold frontierSummand
  rw [frontierLinkGate_eq_zero_of_tail_coordinate_one η z i j hij hjgate]
  ring

/-- Every summand strictly after the next frontier link is killed by the flat
predecessor coordinate of the zero chain. -/
theorem frontierSummand_eq_zero_of_progress_succ_lt_index {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : progress (η / 2) z + 1 < i.val + 1) :
    frontierSummand η z i = 0 := by
  have hiPos : 0 < i.val := by omega
  obtain ⟨jval, hjval⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hiPos)
  have hjBound : jval < T := by omega
  let j : Fin T := ⟨jval, hjBound⟩
  have hji : j.val + 1 = i.val := by simp [j, hjval]
  have hmj : progress (η / 2) z ≤ j.val := by omega
  have hjSmall : |z j| ≤ η / 2 :=
    abs_le_threshold_of_progress_le (le_refl _) j hmj
  have hLink : chainLink η z i = 0 := by
    unfold chainLink
    rw [withInitialOne_castSucc_eq_of_index (normalize η z) j i hji]
    exact chainQ_normalized_eq_zero hη hjSmall
  unfold frontierSummand
  rw [hLink]
  ring

/-- Any nonzero extractor summand must be the unique link immediately after
the current `eta/2` progress index. -/
theorem frontierSummand_nonzero_index {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (i : Fin T)
    (hi : frontierSummand η z i ≠ 0) :
    i.val + 1 = progress (η / 2) z + 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hi (frontierSummand_eq_zero_of_index_le_progress hη z i (by omega))
  · exact hi (frontierSummand_eq_zero_of_progress_succ_lt_index hη z i hgt)

/-- At full progress every extractor summand vanishes. -/
theorem frontierSummand_eq_zero_of_full_progress {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hfull : progress (η / 2) z = T) (i : Fin T) :
    frontierSummand η z i = 0 := by
  apply frontierSummand_eq_zero_of_index_le_progress hη z i
  rw [hfull]
  omega

/-- The frontier extractor itself is zero at full progress. -/
theorem frontierExtractor_eq_zero_of_full_progress {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hfull : progress (η / 2) z = T) :
    frontierExtractor η z = 0 := by
  unfold frontierExtractor
  apply Finset.sum_eq_zero
  intro i _hi
  exact frontierSummand_eq_zero_of_full_progress hη z hfull i

/-- A numerical value bound for one extractor summand. -/
theorem abs_frontierSummand_le {T : ℕ} {η : ℝ} (hη : 0 < η)
    (z : ChainVector T) (i : Fin T) :
    |frontierSummand η z i| ≤
      η ^ 2 * (2 * Real.exp 1 * phiBound) := by
  unfold frontierSummand chainLink
  rw [abs_mul, abs_pow, abs_of_pos hη]
  have hGateAbs : |frontierLinkGate η z i| = frontierLinkGate η z i :=
    abs_of_nonneg (frontierLinkGate_nonneg η z i)
  rw [abs_mul, hGateAbs]
  have hGate := frontierLinkGate_le_one η z i
  have hLink := abs_chainQ_le
    (withInitialOne (normalize η z) i.castSucc) (normalize η z i)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
  calc
    frontierLinkGate η z i *
          |chainQ (withInitialOne (normalize η z) i.castSucc)
            (normalize η z i)|
        ≤ 1 * |chainQ (withInitialOne (normalize η z) i.castSucc)
            (normalize η z i)| :=
      mul_le_mul_of_nonneg_right hGate (abs_nonneg _)
    _ ≤ 2 * Real.exp 1 * phiBound := by simpa using hLink

/-- The whole extractor has magnitude `O(eta^2)` with a constant independent
of the chain length. -/
theorem abs_frontierExtractor_le {T : ℕ} {η : ℝ} (hη : 0 < η)
    (z : ChainVector T) :
    |frontierExtractor η z| ≤
      η ^ 2 * (2 * Real.exp 1 * phiBound) := by
  let m := progress (η / 2) z
  rcases lt_or_eq_of_le (progress_le_dim (η / 2) z) with hm | hm
  · let i0 : Fin T := ⟨m, hm⟩
    have hSum : frontierExtractor η z = frontierSummand η z i0 := by
      unfold frontierExtractor
      apply Finset.sum_eq_single i0
      · intro j _hj hji
        by_contra hjNonzero
        have hjIndex := frontierSummand_nonzero_index hη z j hjNonzero
        apply hji
        apply Fin.ext
        change j.val = m
        change j.val + 1 = m + 1 at hjIndex
        omega
      · intro hi0
        simp at hi0
    rw [hSum]
    exact abs_frontierSummand_le hη z i0
  · have hFull : progress (η / 2) z = T := hm
    rw [frontierExtractor_eq_zero_of_full_progress hη z hFull, abs_zero]
    exact mul_nonneg (sq_nonneg η)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
        phiBound_nonneg)

/-- Below the `eta/4` progress threshold, truncating after `k+1` leaves every
tail activation vector unchanged. -/
theorem tailActivation_truncate_succ_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T) :
    tailActivation η (truncate (k + 1) z) i = tailActivation η z i := by
  ext j
  by_cases hij : i.val ≤ j.val
  · rw [tailActivation_apply_of_le (truncate (k + 1) z) i j hij,
      tailActivation_apply_of_le z i j hij]
    by_cases hjk : j.val < k + 1
    · rw [truncate_apply_of_lt z j hjk]
    · have hkj : k ≤ j.val := by omega
      have hjSmall : |z j| ≤ η / 4 :=
        abs_le_threshold_of_progress_le hk j hkj
      have hNormSmall : |z j / η| ≤ 1 / 4 := by
        rw [abs_div, abs_of_pos hη]
        exact (div_le_iff₀ hη).2 (by
          simpa [div_eq_mul_inv, mul_comm] using hjSmall)
      rw [truncate_apply_of_le z j (by omega), zero_div,
        coordinateGate_eq_zero_of_abs_le_quarter (by norm_num),
        coordinateGate_eq_zero_of_abs_le_quarter hNormSmall]
  · have hji : j.val < i.val := Nat.lt_of_not_ge hij
    rw [tailActivation_apply_of_lt (truncate (k + 1) z) i j hji,
      tailActivation_apply_of_lt z i j hji]

theorem frontierLinkGate_truncate_succ_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T) :
    frontierLinkGate η (truncate (k + 1) z) i = frontierLinkGate η z i := by
  unfold frontierLinkGate
  rw [tailActivation_truncate_succ_of_progress_le hη z hk i]

/-- A link through coordinate `k+1` is unchanged by `P_(k+1)`. -/
theorem chainLink_truncate_succ_eq_of_index_lt {T k : ℕ} {η : ℝ}
    (z : ChainVector T) (i : Fin T) (hi : i.val < k + 1) :
    chainLink η (truncate (k + 1) z) i = chainLink η z i := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
      cases i using Fin.cases with
      | zero => simp [chainLink, normalize, withInitialOne, truncate]
      | succ j =>
          unfold chainLink
          rw [withInitialOne_castSucc_eq_of_index
              (normalize η (truncate (k + 1) z)) j.castSucc j.succ (by rfl),
            withInitialOne_castSucc_eq_of_index
              (normalize η z) j.castSucc j.succ (by rfl)]
          unfold normalize
          simp only [chainVectorOfFun_apply]
          have hjcast : j.castSucc.val < k + 1 := by
            change j.val < k + 1
            change j.val + 1 < k + 1 at hi
            omega
          rw [truncate_apply_of_lt z j.castSucc hjcast,
            truncate_apply_of_lt z j.succ hi]

/-- A link after coordinate `k+1` is zero when progress at threshold
`eta/4` is at most `k`. -/
theorem chainLink_eq_zero_of_progress_le_index {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) (i : Fin T)
    (hi : k + 1 ≤ i.val) :
    chainLink η z i = 0 := by
  have hiPos : 0 < i.val := by omega
  obtain ⟨jval, hjval⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hiPos)
  have hjBound : jval < T := by omega
  let j : Fin T := ⟨jval, hjBound⟩
  have hji : j.val + 1 = i.val := by simp [j, hjval]
  have hkj : k ≤ j.val := by omega
  have hjSmallQuarter : |z j| ≤ η / 4 :=
    abs_le_threshold_of_progress_le hk j hkj
  have hjSmallHalf : |z j| ≤ η / 2 := by linarith
  unfold chainLink
  rw [withInitialOne_castSucc_eq_of_index (normalize η z) j i hji]
  exact chainQ_normalized_eq_zero hη hjSmallHalf

/-- The value-level cylinder identity for the stochastic frontier. -/
theorem frontierExtractor_truncate_succ_of_progress_le {T k : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T)
    (hk : progress (η / 4) z ≤ k) :
    frontierExtractor η (truncate (k + 1) z) = frontierExtractor η z := by
  unfold frontierExtractor
  apply Finset.sum_congr rfl
  intro i _hi
  unfold frontierSummand
  rw [frontierLinkGate_truncate_succ_of_progress_le hη z hk i]
  by_cases hi : i.val < k + 1
  · rw [chainLink_truncate_succ_eq_of_index_lt z i hi]
  · have hik : k + 1 ≤ i.val := Nat.le_of_not_gt hi
    rw [chainLink_eq_zero_of_progress_le_index hη z hk i hik]
    have hTruncProgress : progress (η / 4) (truncate (k + 1) z) ≤ k := by
      apply progress_le_of_tail_bound
      intro j hkj
      by_cases hj : j.val < k + 1
      · rw [truncate_apply_of_lt z j hj]
        exact abs_le_threshold_of_progress_le hk j hkj
      · rw [truncate_apply_of_le z j (Nat.le_of_not_gt hj), abs_zero]
        positivity
    have hTruncLink : chainLink η (truncate (k + 1) z) i = 0 :=
      chainLink_eq_zero_of_progress_le_index hη (truncate (k + 1) z)
        hTruncProgress i hik
    rw [hTruncLink]

theorem frontierExtractor_progress_cylinder {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) :
    frontierExtractor η z =
      frontierExtractor η (truncate (progress (η / 4) z + 1) z) := by
  symm
  exact frontierExtractor_truncate_succ_of_progress_le hη z (le_refl _)

end

end BilevelLowerBound
