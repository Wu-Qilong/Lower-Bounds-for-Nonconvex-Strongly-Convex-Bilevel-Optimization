/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractorJets

/-!
# Quantitative reduction for the frontier extractor

This module establishes the dimension-free scalar constants, the exact
scaled link bounds, and the scaled Leibniz estimate used by the frontier
extractor.  Its final theorem reduces the complete extractor estimate to the
single remaining analytic input: a dimension-free bound for the radial link
gate.  No chain-length factor is introduced in this reduction.
-/

open Filter Function Real Set
open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

theorem eventually_iteratedFDeriv_frontierTransition_eq_const_atTop (n : ℕ) :
    (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t) =ᶠ[atTop]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hLocal : frontierTransition =ᶠ[nhds t] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < t by linarith)] with y hy
    exact frontierTransition_eq_one_of_half_le hy.le
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  have hConstPoint :
      iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) t =
        iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0 := by
    cases n with
    | zero =>
        apply ContinuousMultilinearMap.ext
        intro m
        simp
    | succ n =>
        rw [show n + 1 = n + 1 from rfl,
          iteratedFDeriv_succ_const]
        simp
  exact hAt.trans hConstPoint

theorem eventually_iteratedFDeriv_frontierTransition_eq_const_atBot (n : ℕ) :
    (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t) =ᶠ[atBot]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  have hLocal : frontierTransition =ᶠ[nhds t] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds (show t < (1 / 4 : ℝ) by linarith)] with y hy
    exact frontierTransition_eq_zero_of_le_quarter hy.le
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hAt

theorem isBounded_range_iteratedFDeriv_frontierTransition (n : ℕ) :
    Bornology.IsBounded
      (Set.range (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t)) := by
  have hCont : Continuous
      (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t) :=
    frontierTransition_contDiff.continuous_iteratedFDeriv
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
  apply hCont.isBounded_range_iff_isBigO_atTop_atBot.mpr
  constructor
  · have hTendsto : Tendsto
        (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t) atTop
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_frontierTransition_eq_const_atTop n).symm
    exact hTendsto.isBigO_one ℝ
  · have hTendsto : Tendsto
        (fun t : ℝ ↦ iteratedFDeriv ℝ n frontierTransition t) atBot
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_frontierTransition_eq_const_atBot n).symm
    exact hTendsto.isBigO_one ℝ

theorem exists_bound_frontierTransition_iteratedFDeriv (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n frontierTransition t‖ ≤ C := by
  have hBounded := isBounded_range_iteratedFDeriv_frontierTransition n
  rw [isBounded_iff_forall_norm_le] at hBounded
  obtain ⟨C, hC⟩ := hBounded
  refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
  exact (hC _ ⟨t, rfl⟩).trans (le_max_left C 0)

theorem exists_common_bound_frontierTransition_three :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n frontierTransition t‖ ≤ C := by
  obtain ⟨C0, hC00, hC0⟩ := exists_bound_frontierTransition_iteratedFDeriv 0
  obtain ⟨C1, hC10, hC1⟩ := exists_bound_frontierTransition_iteratedFDeriv 1
  obtain ⟨C2, hC20, hC2⟩ := exists_bound_frontierTransition_iteratedFDeriv 2
  obtain ⟨C3, hC30, hC3⟩ := exists_bound_frontierTransition_iteratedFDeriv 3
  refine ⟨C0 + C1 + C2 + C3, by positivity, fun n hn t ↦ ?_⟩
  interval_cases n
  · exact (hC0 t).trans (by linarith)
  · exact (hC1 t).trans (by linarith)
  · exact (hC2 t).trans (by linarith)
  · exact (hC3 t).trans (by linarith)

theorem exists_common_bound_coordinateGate_three :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n coordinateGate t‖ ≤ C := by
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := exists_common_bound_frontierTransition_three
  let Lneg : ℝ →L[ℝ] ℝ := -(ContinuousLinearMap.id ℝ ℝ)
  have hLneg : ‖Lneg‖ ≤ 1 := by
    simp [Lneg]
  have hNegBound : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n (frontierTransition ∘ Lneg) t‖ ≤ CΓ := by
    intro n hn t
    exact norm_iteratedFDeriv_comp_clm_le frontierTransition_contDiff
      CΓ hCΓ0 hCΓ Lneg hLneg n hn t
  refine ⟨2 * CΓ, by positivity, fun n hn t ↦ ?_⟩
  have hPosSmooth : ContDiffAt ℝ n frontierTransition t :=
    (frontierTransition_contDiff.of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hNegSmooth : ContDiffAt ℝ n (frontierTransition ∘ Lneg) t :=
    ((frontierTransition_contDiff.comp Lneg.contDiff).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hFun : coordinateGate =
      frontierTransition + (frontierTransition ∘ Lneg) := by
    funext y
    simp [coordinateGate, Lneg]
  rw [hFun, iteratedFDeriv_add_apply hPosSmooth hNegSmooth]
  exact (norm_add_le _ _).trans (by
    have hp := hCΓ n hn t
    have hm := hNegBound n hn t
    linarith)

/-- Scalar profile of the radial frontier gate, expressed through the
squared radius.  This representation isolates all dimension dependence in
the squared-norm map. -/
def frontierRadialProfile (s : ℝ) : ℝ :=
  frontierTransition (1 - Real.sqrt s)

theorem frontierRadialProfile_contDiff :
    ContDiff ℝ ∞ frontierRadialProfile := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : 0 < s
  · unfold frontierRadialProfile
    exact frontierTransition_contDiff.contDiffAt.comp s
      (contDiffAt_const.sub (contDiffAt_id.sqrt hs.ne'))
  · have hslt : s < (1 / 4 : ℝ) := by linarith
    have hLocal : frontierRadialProfile =ᶠ[nhds s] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hslt] with y hy
      unfold frontierRadialProfile
      apply frontierTransition_eq_one_of_half_le
      have hy' : y < (1 / 4 : ℝ) := hy
      have hsqrt : Real.sqrt y < 1 / 2 := by
        apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).2
        norm_num
        exact hy'
      linarith
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ)) s)
      |>.congr_of_eventuallyEq hLocal

theorem frontierLinkGate_eq_radialProfile_norm_sq
    {T : ℕ} (η : ℝ) (z : ChainVector T) (i : Fin T) :
    frontierLinkGate η z i =
      frontierRadialProfile (‖tailActivation η z i‖ ^ 2) := by
  unfold frontierLinkGate frontierRadialProfile
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Squared norm of the coordinatewise tail activation. -/
def tailActivationNormSq {T : ℕ} (η : ℝ) (i : Fin T)
    (z : ChainVector T) : ℝ :=
  ‖tailActivation η z i‖ ^ 2

theorem tailActivationNormSq_contDiff {T : ℕ} (η : ℝ) (i : Fin T) :
    ContDiff ℝ ∞ (tailActivationNormSq η i) := by
  unfold tailActivationNormSq
  exact (contDiff_norm_sq ℝ).comp (tailActivation_contDiff η i)

theorem frontierLinkGate_eq_radialProfile_comp_tailActivationNormSq
    {T : ℕ} (η : ℝ) (i : Fin T) :
    (frontierLinkGate η · i) =
      frontierRadialProfile ∘ tailActivationNormSq η i := by
  funext z
  exact frontierLinkGate_eq_radialProfile_norm_sq η z i

theorem frontierRadialProfile_eq_zero_of_nine_sixteenths_le
    {s : ℝ} (hs : 9 / 16 ≤ s) :
    frontierRadialProfile s = 0 := by
  unfold frontierRadialProfile
  apply frontierTransition_eq_zero_of_le_quarter
  have hs0 : 0 ≤ s := by linarith
  have hsq := Real.sq_sqrt hs0
  have hsqrt : 3 / 4 ≤ Real.sqrt s := by
    nlinarith [Real.sqrt_nonneg s]
  linarith

/-- Above the active squared-radius annulus, every radial-profile jet is
zero.  This is the support fact needed to keep the squared-norm derivatives
dimension free. -/
theorem iteratedFDeriv_frontierRadialProfile_eq_zero_of_nine_sixteenths_lt
    {n : ℕ} {s : ℝ} (hs : 9 / 16 < s) :
    iteratedFDeriv ℝ n frontierRadialProfile s = 0 := by
  have hLocal : frontierRadialProfile =ᶠ[nhds s] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact frontierRadialProfile_eq_zero_of_nine_sixteenths_le hy.le
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hJet.eq_of_nhds

theorem eventually_iteratedFDeriv_frontierRadialProfile_eq_const_atTop
    (n : ℕ) :
    (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s) =ᶠ[atTop]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  have hLocal : frontierRadialProfile =ᶠ[nhds s] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < s by linarith)] with y hy
    unfold frontierRadialProfile
    apply frontierTransition_eq_zero_of_le_quarter
    have hy' : (1 : ℝ) < y := hy
    have hsqrt : 1 < Real.sqrt y := by
      have hy0 : 0 ≤ y := le_trans (by norm_num) hy'.le
      have hsq := Real.sq_sqrt hy0
      nlinarith [Real.sqrt_nonneg y]
    linarith
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hAt

theorem eventually_iteratedFDeriv_frontierRadialProfile_eq_const_atBot
    (n : ℕ) :
    (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s) =ᶠ[atBot]
      (fun _ ↦ iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0) := by
  filter_upwards [eventually_le_atBot (-1 : ℝ)] with s hs
  have hLocal : frontierRadialProfile =ᶠ[nhds s] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds (show s < (0 : ℝ) by linarith)] with y hy
    unfold frontierRadialProfile
    rw [Real.sqrt_eq_zero_of_nonpos hy.le, sub_zero]
    exact frontierTransition_eq_one_of_half_le (by norm_num)
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) n
  have hAt := hJet.eq_of_nhds
  have hConstPoint :
      iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) s =
        iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0 := by
    cases n with
    | zero =>
        apply ContinuousMultilinearMap.ext
        intro m
        simp
    | succ n =>
        rw [show n + 1 = n + 1 from rfl, iteratedFDeriv_succ_const]
        simp
  exact hAt.trans hConstPoint

theorem isBounded_range_iteratedFDeriv_frontierRadialProfile (n : ℕ) :
    Bornology.IsBounded
      (Set.range (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s)) := by
  have hCont : Continuous
      (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s) :=
    frontierRadialProfile_contDiff.continuous_iteratedFDeriv
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
  apply hCont.isBounded_range_iff_isBigO_atTop_atBot.mpr
  constructor
  · have hTendsto : Tendsto
        (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s) atTop
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (0 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_frontierRadialProfile_eq_const_atTop n).symm
    exact hTendsto.isBigO_one ℝ
  · have hTendsto : Tendsto
        (fun s : ℝ ↦ iteratedFDeriv ℝ n frontierRadialProfile s) atBot
        (nhds (iteratedFDeriv ℝ n (fun _ : ℝ ↦ (1 : ℝ)) 0)) :=
      tendsto_const_nhds.congr'
        (eventually_iteratedFDeriv_frontierRadialProfile_eq_const_atBot n).symm
    exact hTendsto.isBigO_one ℝ

theorem exists_common_bound_frontierRadialProfile_three :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ 3 → ∀ s : ℝ,
      ‖iteratedFDeriv ℝ n frontierRadialProfile s‖ ≤ C := by
  have hBound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ,
      ‖iteratedFDeriv ℝ n frontierRadialProfile s‖ ≤ C := by
    intro n
    have hBounded := isBounded_range_iteratedFDeriv_frontierRadialProfile n
    rw [isBounded_iff_forall_norm_le] at hBounded
    obtain ⟨C, hC⟩ := hBounded
    exact ⟨max C 0, le_max_right _ _, fun s ↦
      (hC _ ⟨s, rfl⟩).trans (le_max_left C 0)⟩
  obtain ⟨C0, hC00, hC0⟩ := hBound 0
  obtain ⟨C1, hC10, hC1⟩ := hBound 1
  obtain ⟨C2, hC20, hC2⟩ := hBound 2
  obtain ⟨C3, hC30, hC3⟩ := hBound 3
  refine ⟨C0 + C1 + C2 + C3, by positivity, fun n hn s ↦ ?_⟩
  interval_cases n
  · exact (hC0 s).trans (by linarith)
  · exact (hC1 s).trans (by linarith)
  · exact (hC2 s).trans (by linarith)
  · exact (hC3 s).trans (by linarith)

def normalizeCLM {T : ℕ} (η : ℝ) : ChainVector T →L[ℝ] ChainVector T :=
  η⁻¹ • ContinuousLinearMap.id ℝ (ChainVector T)

@[simp]
theorem normalizeCLM_apply {T : ℕ} (η : ℝ) (z : ChainVector T) :
    normalizeCLM η z = normalize η z := by
  rw [normalize_eq_inv_smul]
  rfl

theorem norm_normalizeCLM_le_inv {T : ℕ} {η : ℝ} (hη : 0 < η) :
    ‖normalizeCLM (T := T) η‖ ≤ η⁻¹ := by
  unfold normalizeCLM
  calc
    ‖η⁻¹ • ContinuousLinearMap.id ℝ (ChainVector T)‖ =
        ‖η⁻¹‖ * ‖ContinuousLinearMap.id ℝ (ChainVector T)‖ := by
      rw [norm_smul]
    _ ≤ η⁻¹ * 1 := by
      gcongr
      · simp [Real.norm_eq_abs, abs_of_pos hη]
      · exact ContinuousLinearMap.norm_id_le
    _ = η⁻¹ := mul_one _

theorem chainLink_eq_unscaledLink_comp_normalizeCLM
    {T : ℕ} (η : ℝ) (i : Fin T) :
    (chainLink η · i) = unscaledLink i ∘ normalizeCLM η := by
  funext z
  simp [chainLink, unscaledLink]

theorem norm_iteratedFDeriv_unscaledLink_le
    {T n : ℕ} (Cq : ℝ) (hCq0 : 0 ≤ Cq)
    (hCq : ∀ r : ℕ, r ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ r (fun z : ℝ × ℝ ↦ chainQ z.1 z.2) w‖ ≤ Cq)
    (hn : n ≤ 3) (i : Fin T) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ n (unscaledLink i) z‖ ≤ Cq := by
  apply ContinuousMultilinearMap.opNorm_le_bound hCq0
  intro m
  rw [iteratedFDeriv_unscaledLink_apply]
  calc
    ‖iteratedFDeriv ℝ n (fun w : ℝ × ℝ ↦ chainQ w.1 w.2)
        (withInitialOne z i.castSucc, z i)
        (fun j ↦ linkDirectionCLM i (m j))‖ ≤
      ‖iteratedFDeriv ℝ n (fun w : ℝ × ℝ ↦ chainQ w.1 w.2)
        (withInitialOne z i.castSucc, z i)‖ *
          ∏ j : Fin n, ‖linkDirectionCLM i (m j)‖ :=
      (iteratedFDeriv ℝ n (fun w : ℝ × ℝ ↦ chainQ w.1 w.2)
        (withInitialOne z i.castSucc, z i)).le_opNorm _
    _ ≤ Cq * ∏ j : Fin n, ‖m j‖ := by
      gcongr
      · exact hCq n hn _
      · exact linkDirection_norm_le i (m j)

theorem norm_iteratedFDeriv_chainLink_le
    {T n : ℕ} {η : ℝ} (hη : 0 < η)
    (Cq : ℝ) (hCq0 : 0 ≤ Cq)
    (hCq : ∀ r : ℕ, r ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ r (fun z : ℝ × ℝ ↦ chainQ z.1 z.2) w‖ ≤ Cq)
    (hn : n ≤ 3) (i : Fin T) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ n (chainLink η · i) z‖ ≤
      Cq * (η⁻¹) ^ n := by
  rw [chainLink_eq_unscaledLink_comp_normalizeCLM]
  rw [(normalizeCLM (T := T) η).iteratedFDeriv_comp_right
    (unscaledLink_contDiff i) z
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)]
  calc
    ‖( iteratedFDeriv ℝ n (unscaledLink i) (normalizeCLM η z)).compContinuousLinearMap
        (fun _ ↦ normalizeCLM η)‖ ≤
      ‖iteratedFDeriv ℝ n (unscaledLink i) (normalizeCLM η z)‖ *
        ∏ _ : Fin n, ‖normalizeCLM (T := T) η‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ Cq * ∏ _ : Fin n, η⁻¹ := by
      gcongr
      · exact norm_iteratedFDeriv_unscaledLink_le Cq hCq0 hCq hn i _
      · exact norm_normalizeCLM_le_inv hη
    _ = Cq * (η⁻¹) ^ n := by simp

theorem norm_iteratedFDeriv_mul_scaled_le_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D a : ℝ} (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) (ha0 : 0 ≤ a)
    (hC : ∀ r : ℕ, r ≤ 3 → ∀ x : E,
      ‖iteratedFDeriv ℝ r f x‖ ≤ C * a ^ r)
    (hD : ∀ r : ℕ, r ≤ 3 → ∀ x : E,
      ‖iteratedFDeriv ℝ r g x‖ ≤ D * a ^ r)
    (n : ℕ) (hn : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f y * g y) x‖ ≤
      8 * C * D * a ^ n := by
  calc
    ‖iteratedFDeriv ℝ n (fun y ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (C * a ^ i) * (D * a ^ (n - i)) := by
      gcongr with i hi
      · exact hC i (by
          have hi' := Finset.mem_range.1 hi
          omega) x
      · exact hD (n - i) (by omega) x
    _ = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * C * D * a ^ n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := by
        have := Finset.mem_range.1 hi
        omega
      calc
        (n.choose i : ℝ) * (C * a ^ i) * (D * a ^ (n - i)) =
            (n.choose i : ℝ) * C * D * (a ^ i * a ^ (n - i)) := by ring
        _ = (n.choose i : ℝ) * C * D * a ^ n := by
          rw [← pow_add, Nat.add_sub_of_le hin]
    _ ≤ 8 * C * D * a ^ n := by
      interval_cases n <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith [mul_nonneg hC0 hD0, pow_nonneg ha0 0,
          pow_nonneg ha0 1, pow_nonneg ha0 2, pow_nonneg ha0 3]

theorem norm_iteratedFDeriv_frontierSummand_le
    {T n : ℕ} {η Cg Cq : ℝ} (hη : 0 < η)
    (hCg0 : 0 ≤ Cg) (hCq0 : 0 ≤ Cq)
    (hGate : ∀ r : ℕ, r ≤ 3 → ∀ (j : Fin T) (y : ChainVector T),
      ‖iteratedFDeriv ℝ r (frontierLinkGate η · j) y‖ ≤
        Cg * (η⁻¹) ^ r)
    (hLink : ∀ r : ℕ, r ≤ 3 → ∀ (j : Fin T) (y : ChainVector T),
      ‖iteratedFDeriv ℝ r (chainLink η · j) y‖ ≤
        Cq * (η⁻¹) ^ r)
    (hn : n ≤ 3) (i : Fin T) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ n (frontierSummand η · i) z‖ ≤
      8 * Cg * Cq * η ^ 2 * (η⁻¹) ^ n := by
  let product : ChainVector T → ℝ := fun y ↦
    frontierLinkGate η y i * chainLink η y i
  have hProductSmooth : ContDiff ℝ ∞ product :=
    (frontierLinkGate_contDiff η i).mul (chainLink_contDiff η i)
  have hProductBound :
      ‖iteratedFDeriv ℝ n product z‖ ≤
        8 * Cg * Cq * (η⁻¹) ^ n := by
    exact norm_iteratedFDeriv_mul_scaled_le_eight
      (frontierLinkGate_contDiff η i) (chainLink_contDiff η i)
      hCg0 hCq0 (inv_nonneg.mpr hη.le)
      (fun r hr y ↦ hGate r hr i y)
      (fun r hr y ↦ hLink r hr i y) n hn z
  change ‖iteratedFDeriv ℝ n (fun y ↦ η ^ 2 * product y) z‖ ≤ _
  rw [show (fun y ↦ η ^ 2 * product y) = (η ^ 2) • product by
    funext y
    simp [smul_eq_mul]]
  rw [iteratedFDeriv_const_smul_apply
    ((hProductSmooth.of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt), norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
  calc
    η ^ 2 * ‖iteratedFDeriv ℝ n product z‖ ≤
        η ^ 2 * (8 * Cg * Cq * (η⁻¹) ^ n) := by
      gcongr
    _ = 8 * Cg * Cq * η ^ 2 * (η⁻¹) ^ n := by ring

theorem norm_iteratedFDeriv_frontierExtractor_le_of_gate_bound
    {T n : ℕ} {η Cg Cq : ℝ} (hη : 0 < η)
    (hCg0 : 0 ≤ Cg) (hCq0 : 0 ≤ Cq)
    (hGate : ∀ r : ℕ, r ≤ 3 → ∀ (j : Fin T) (y : ChainVector T),
      ‖iteratedFDeriv ℝ r (frontierLinkGate η · j) y‖ ≤
        Cg * (η⁻¹) ^ r)
    (hLink : ∀ r : ℕ, r ≤ 3 → ∀ (j : Fin T) (y : ChainVector T),
      ‖iteratedFDeriv ℝ r (chainLink η · j) y‖ ≤
        Cq * (η⁻¹) ^ r)
    (hn : n ≤ 3) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ n (frontierExtractor η : ChainVector T → ℝ) z‖ ≤
      8 * Cg * Cq * η ^ 2 * (η⁻¹) ^ n := by
  by_cases hm : progress (η / 2) z < T
  · rw [iteratedFDeriv_frontierExtractor_eq_frontier_summand hη z hm]
    exact norm_iteratedFDeriv_frontierSummand_le hη hCg0 hCq0
      hGate hLink hn _ z
  · have hfull : progress (η / 2) z = T := by
      have hle := progress_le_dim (η / 2) z
      omega
    rw [iteratedFDeriv_frontierExtractor_eq_zero_of_full_progress hη z hfull,
      norm_zero]
    positivity

end
end BilevelLowerBound
