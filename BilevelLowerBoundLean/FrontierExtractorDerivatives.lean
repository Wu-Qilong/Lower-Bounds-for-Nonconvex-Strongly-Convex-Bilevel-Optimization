/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractor
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smoothness and jets of the frontier extractor

The radial gate contains a norm and therefore requires a separate argument at
points where its tail activation vector is zero.  There the outer transition
is locally constant.  Away from zero, the Euclidean norm is smooth.  This
module makes that split explicit before deriving jets of the finite extractor.
-/

open scoped ContDiff Topology
open Filter Set

namespace BilevelLowerBound

noncomputable section

/-- The coordinatewise tail activation is globally smooth. -/
theorem tailActivation_contDiff {T : ℕ} (η : ℝ) (i : Fin T) :
    ContDiff ℝ ∞ (fun z : ChainVector T ↦ tailActivation η z i) := by
  rw [contDiff_piLp]
  intro j
  unfold tailActivation
  simp only [chainVectorOfFun_apply]
  split
  · exact coordinateGate_contDiff.comp
      ((contDiff_piLp_apply 2).div_const η)
  · exact contDiff_const

/-- The apparent nonsmoothness of the norm at a zero tail is removed by the
flat, locally constant outer transition. -/
theorem frontierLinkGate_contDiff {T : ℕ} (η : ℝ) (i : Fin T) :
    ContDiff ℝ ∞ (fun z : ChainVector T ↦ frontierLinkGate η z i) := by
  have hV : ContDiff ℝ ∞
      (fun z : ChainVector T ↦ tailActivation η z i) :=
    tailActivation_contDiff η i
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : tailActivation η z i = 0
  · have hNormCont : ContinuousAt
        (fun y : ChainVector T ↦ ‖tailActivation η y i‖) z :=
      hV.continuous.continuousAt.norm
    have hNormZero : ‖tailActivation η z i‖ = 0 := by
      rw [hz, norm_zero]
    have hEventually :
        ∀ᶠ y in nhds z, ‖tailActivation η y i‖ < 1 / 2 := by
      exact hNormCont.tendsto.eventually (Iio_mem_nhds (by
        rw [hNormZero]
        norm_num))
    have hLocal :
        (fun y : ChainVector T ↦ frontierLinkGate η y i) =ᶠ[nhds z]
          (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hEventually] with y hy
      unfold frontierLinkGate
      exact frontierTransition_eq_one_of_half_le (by linarith)
    exact (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : ChainVector T ↦ (1 : ℝ)) z)
        |>.congr_of_eventuallyEq hLocal
  · unfold frontierLinkGate
    exact frontierTransition_contDiff.contDiffAt.comp z
      (contDiffAt_const.sub (hV.contDiffAt.norm ℝ hz))

/-- Every normalized chain link is globally smooth. -/
theorem chainLink_contDiff {T : ℕ} (η : ℝ) (i : Fin T) :
    ContDiff ℝ ∞ (fun z : ChainVector T ↦ chainLink η z i) := by
  have hNormalize : ContDiff ℝ ∞
      (normalize η : ChainVector T → ChainVector T) := by
    change ContDiff ℝ ∞ (fun z : ChainVector T ↦ normalize η z)
    simpa only [normalize_eq_inv_smul, id_eq] using
      (contDiff_id : ContDiff ℝ ∞ (id : ChainVector T → ChainVector T))
        |>.const_smul η⁻¹
  unfold chainLink
  exact chainQ_comp_contDiff
    ((withInitialOne_coord_contDiff i).comp hNormalize)
    ((contDiff_piLp_apply 2).comp hNormalize)

theorem frontierSummand_contDiff {T : ℕ} (η : ℝ) (i : Fin T) :
    ContDiff ℝ ∞ (fun z : ChainVector T ↦ frontierSummand η z i) := by
  unfold frontierSummand
  exact contDiff_const.mul
    ((frontierLinkGate_contDiff η i).mul (chainLink_contDiff η i))

/-- The complete stochastic frontier is globally `C-infinity`. -/
theorem frontierExtractor_contDiff {T : ℕ} (η : ℝ) :
    ContDiff ℝ ∞ (frontierExtractor η : ChainVector T → ℝ) := by
  unfold frontierExtractor
  exact ContDiff.sum fun i _hi ↦ frontierSummand_contDiff η i

theorem visibleChain_contDiff {T : ℕ} (η : ℝ) :
    ContDiff ℝ ∞ (visibleChain η : ChainVector T → ℝ) := by
  unfold visibleChain
  exact (scaledChain_contDiff η).sub (frontierExtractor_contDiff η)

/-- Coordinate truncation as a linear map. -/
def truncateLM {T : ℕ} (k : ℕ) :
    ChainVector T →ₗ[ℝ] ChainVector T where
  toFun := truncate k
  map_add' x y := by
    ext i
    by_cases hi : i.val < k <;> simp [truncate, hi]
  map_smul' c x := by
    ext i
    by_cases hi : i.val < k <;> simp [truncate, hi]

/-- Coordinate truncation is a contraction. -/
def truncateCLM {T : ℕ} (k : ℕ) :
    ChainVector T →L[ℝ] ChainVector T :=
  (truncateLM k).mkContinuous 1 (fun z ↦ by
    rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    gcongr with i
    by_cases hi : i.val < k <;> simp [truncateLM, truncate, hi])

@[simp]
theorem truncateCLM_apply {T k : ℕ} (z : ChainVector T) :
    truncateCLM k z = truncate k z := by
  rfl

/-- Strict tail control is stable under small perturbations. -/
theorem eventually_progress_le_of_strict_tail {T k : ℕ} {η : ℝ}
    (z : ChainVector T)
    (hTail : ∀ i : Fin T, k ≤ i.val → |z i| < η / 4) :
    ∀ᶠ y in nhds z, progress (η / 4) y ≤ k := by
  have hAll : ∀ᶠ y in nhds z,
      ∀ i : Fin T, k ≤ i.val → |y i| < η / 4 := by
    apply Filter.eventually_all.2
    intro i
    by_cases hik : k ≤ i.val
    · have hCont : ContinuousAt (fun y : ChainVector T ↦ |y i|) z :=
        (continuous_abs.comp
          (PiLp.continuous_apply 2 (fun _ : Fin T ↦ ℝ) i)).continuousAt
      exact (hCont.eventually_lt continuousAt_const (hTail i hik)).mono
        (fun y hy _hik ↦ hy)
    · exact Eventually.of_forall fun _y hki ↦ (hik hki).elim
  filter_upwards [hAll] with y hy
  apply progress_le_of_tail_bound
  intro i hik
  exact (hy i hik).le

/-- Away from the threshold boundary, the frontier jet depends only on the
first `k+1` coordinates. -/
theorem iteratedFDeriv_frontierExtractor_strict_cylinder
    {T k r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hTail : ∀ i : Fin T, k ≤ i.val → |z i| < η / 4) :
    iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ) (truncate (k + 1) z))
        (fun _ : Fin r ↦ truncateCLM (k + 1)) := by
  have hEventually := eventually_progress_le_of_strict_tail z hTail
  have hEq :
      (frontierExtractor η : ChainVector T → ℝ) =ᶠ[nhds z]
        (fun y ↦ frontierExtractor η (truncate (k + 1) y)) := by
    filter_upwards [hEventually] with y hy
    exact (frontierExtractor_truncate_succ_of_progress_le hη y hy).symm
  have hWithin :
      (frontierExtractor η : ChainVector T → ℝ) =ᶠ[nhdsWithin z Set.univ]
        (fun y ↦ frontierExtractor η (truncate (k + 1) y)) :=
    hEq.filter_mono inf_le_left
  have hJet := hWithin.iteratedFDerivWithin_eq (𝕜 := ℝ) hEq.eq_of_nhds r
  rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hJet
  rw [hJet]
  have hSmooth : ContDiff ℝ r
      (frontierExtractor η : ChainVector T → ℝ) :=
    (frontierExtractor_contDiff η).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hComp := (truncateCLM (k + 1)).iteratedFDeriv_comp_right
    hSmooth z (i := r) le_rfl
  rw [truncateCLM_apply] at hComp
  exact hComp

/-- Coefficients used to approach a threshold point from the strict side. -/
def strictApproxCoeff (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

theorem strictApproxCoeff_nonneg (n : ℕ) : 0 ≤ strictApproxCoeff n := by
  unfold strictApproxCoeff
  positivity

theorem strictApproxCoeff_lt_one (n : ℕ) : strictApproxCoeff n < 1 := by
  unfold strictApproxCoeff
  exact (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 (by linarith)

theorem tendsto_strictApproxCoeff :
    Tendsto strictApproxCoeff atTop (nhds 1) := by
  change Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1)
  simpa only using
    (tendsto_natCast_div_add_atTop (1 : ℝ))

/-- The jet cylinder extends to the closed threshold boundary.  The proof
scales the point by `n/(n+1)`, applies the strict-cylinder theorem, and then
passes to the limit using continuity of the complete iterated Fréchet jet. -/
theorem iteratedFDeriv_frontierExtractor_cylinder_of_progress_le
    {T k r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T)
    (hprog : progress (η / 4) z ≤ k) :
    iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ) (truncate (k + 1) z))
        (fun _ : Fin r ↦ truncateCLM (k + 1)) := by
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
      Tendsto (fun n ↦ truncate (k + 1) (zApprox n)) atTop
        (nhds (truncate (k + 1) z)) := by
    change Tendsto
      ((truncateCLM (T := T) (k + 1)) ∘ zApprox) atTop
        (nhds (truncateCLM (k + 1) z))
    exact (truncateCLM (T := T) (k + 1)).continuous.continuousAt.tendsto.comp
      hApproxTendsto
  have hJetContinuous : Continuous
      (fun y : ChainVector T ↦
        iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) y) :=
    (frontierExtractor_contDiff η).continuous_iteratedFDeriv
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hLeftTendsto := hJetContinuous.continuousAt.tendsto.comp hApproxTendsto
  let pullback :
      ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ ChainVector T) ℝ →
        ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ ChainVector T) ℝ :=
    fun M ↦ M.compContinuousLinearMap
      (fun _ : Fin r ↦ truncateCLM (k + 1))
  have hPullbackContinuous : Continuous pullback :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin r ↦ truncateCLM (k + 1))).continuous
  have hBaseTendsto :
      Tendsto (fun n ↦ iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ)
          (truncate (k + 1) (zApprox n))) atTop
        (nhds (iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ)
          (truncate (k + 1) z))) :=
    hJetContinuous.continuousAt.tendsto.comp hTruncateTendsto
  have hRightTendsto :
      Tendsto (fun n ↦ pullback
          (iteratedFDeriv ℝ r
            (frontierExtractor η : ChainVector T → ℝ)
            (truncate (k + 1) (zApprox n)))) atTop
        (nhds (pullback
          (iteratedFDeriv ℝ r
            (frontierExtractor η : ChainVector T → ℝ)
            (truncate (k + 1) z)))) :=
    hPullbackContinuous.continuousAt.tendsto.comp hBaseTendsto
  have hPointwise : ∀ n : ℕ,
      iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ)
          (zApprox n) =
        pullback (iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ)
          (truncate (k + 1) (zApprox n))) := by
    intro n
    exact iteratedFDeriv_frontierExtractor_strict_cylinder
      hη (zApprox n) (hStrict n)
  have hRightAsLeft :
      Tendsto (fun n ↦ iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ) (zApprox n)) atTop
        (nhds (pullback
          (iteratedFDeriv ℝ r
            (frontierExtractor η : ChainVector T → ℝ)
            (truncate (k + 1) z)))) :=
    hRightTendsto.congr' (Eventually.of_forall fun n ↦ (hPointwise n).symm)
  exact tendsto_nhds_unique hLeftTendsto hRightAsLeft

/-- Closed jet-cylinder identity at the actual `eta/4` progress prefix. -/
theorem iteratedFDeriv_frontierExtractor_progress_cylinder
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (z : ChainVector T) :
    iteratedFDeriv ℝ r (frontierExtractor η : ChainVector T → ℝ) z =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ r
          (frontierExtractor η : ChainVector T → ℝ)
          (truncate (progress (η / 4) z + 1) z))
        (fun _ : Fin r ↦ truncateCLM (progress (η / 4) z + 1)) := by
  exact iteratedFDeriv_frontierExtractor_cylinder_of_progress_le
    hη z le_rfl

end

end BilevelLowerBound
