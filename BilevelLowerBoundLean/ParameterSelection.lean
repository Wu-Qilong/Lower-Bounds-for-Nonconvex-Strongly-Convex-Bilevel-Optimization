/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.GapGradient
import Mathlib.MeasureTheory.Integral.Average

/-!
# Final parameter selection and deterministic-frame extraction

This module formalizes the scalar calculation in the proof of the main
theorem.  It chooses `eta = 4 epsilon / kappa`, rounds the real chain length
down to a natural number, substitutes the reveal probability, and proves the
`T / (8p)` call budget.  The last section records the first-moment argument
which turns an average over random frames into one deterministic hard frame.
-/

open Filter Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

/-! ## Accuracy scale and rounded chain length -/

def finalEta (epsilon kappa : ℝ) : ℝ :=
  4 * epsilon / kappa

def finalChainScale (Delta CDelta epsilon kappa : ℝ) : ℝ :=
  Delta / (2 * CDelta * (finalEta epsilon kappa) ^ 2)

def finalChainLength (Delta CDelta epsilon kappa : ℝ) : ℕ :=
  ⌊finalChainScale Delta CDelta epsilon kappa⌋₊

def finalAccuracyConstant (CDelta creg : ℝ) : ℝ :=
  min 1 (min (creg / 4) (1 / (16 * Real.sqrt CDelta)))

def finalLowerBoundConstant (CDelta Cvar : ℝ) : ℝ :=
  1 / (512 * CDelta * max 1 (256 * Cvar))

theorem finalEta_pos
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon) (hkappa : 0 < kappa) :
    0 < finalEta epsilon kappa := by
  unfold finalEta
  positivity

theorem finalEta_sq
    {epsilon kappa : ℝ} (hkappa : kappa ≠ 0) :
    (finalEta epsilon kappa) ^ 2 =
      16 * epsilon ^ 2 / kappa ^ 2 := by
  unfold finalEta
  field_simp [hkappa]
  ring

theorem finalChainScale_eq
    {Delta CDelta epsilon kappa : ℝ}
    (hCDelta : CDelta ≠ 0) (hepsilon : epsilon ≠ 0)
    (hkappa : kappa ≠ 0) :
    finalChainScale Delta CDelta epsilon kappa =
      Delta * kappa ^ 2 / (32 * CDelta * epsilon ^ 2) := by
  unfold finalChainScale finalEta
  field_simp [hCDelta, hepsilon, hkappa]
  ring

theorem finalAccuracyConstant_pos
    {CDelta creg : ℝ} (hCDelta : 0 < CDelta) (hcreg : 0 < creg) :
    0 < finalAccuracyConstant CDelta creg := by
  unfold finalAccuracyConstant
  apply lt_min (by norm_num)
  apply lt_min <;> positivity

theorem finalAccuracyConstant_le_one (CDelta creg : ℝ) :
    finalAccuracyConstant CDelta creg ≤ 1 := by
  exact min_le_left _ _

theorem finalAccuracyConstant_le_reg_div_four (CDelta creg : ℝ) :
    finalAccuracyConstant CDelta creg ≤ creg / 4 := by
  exact (min_le_right 1 _).trans (min_le_left _ _)

theorem finalAccuracyConstant_le_gap_scale (CDelta creg : ℝ) :
    finalAccuracyConstant CDelta creg ≤
      1 / (16 * Real.sqrt CDelta) := by
  exact (min_le_right 1 _).trans (min_le_right _ _)

/-- Rounding `X` down loses at most a factor two once `X >= 2`. -/
theorem natFloor_two_sided {X : ℝ} (hX : 2 ≤ X) :
    X / 2 ≤ (⌊X⌋₊ : ℝ) ∧ (⌊X⌋₊ : ℝ) ≤ X := by
  have hX0 : 0 ≤ X := by linarith
  constructor
  · have hfloor := (Nat.sub_one_lt_floor X).le
    linarith
  · exact Nat.floor_le hX0

theorem natFloor_pos_of_two_le {X : ℝ} (hX : 2 ≤ X) :
    0 < ⌊X⌋₊ := by
  rw [Nat.floor_pos]
  linarith

theorem finalChainLength_two_sided
    {Delta CDelta epsilon kappa : ℝ}
    (hX : 2 ≤ finalChainScale Delta CDelta epsilon kappa) :
    finalChainScale Delta CDelta epsilon kappa / 2 ≤
        (finalChainLength Delta CDelta epsilon kappa : ℝ) ∧
      (finalChainLength Delta CDelta epsilon kappa : ℝ) ≤
        finalChainScale Delta CDelta epsilon kappa := by
  exact natFloor_two_sided hX

theorem finalChainLength_pos
    {Delta CDelta epsilon kappa : ℝ}
    (hX : 2 ≤ finalChainScale Delta CDelta epsilon kappa) :
    0 < finalChainLength Delta CDelta epsilon kappa := by
  exact natFloor_pos_of_two_le hX

/-! ## Consequences of the theorem's accuracy range -/

theorem finalEta_le_reg_div_kappa
    {Delta CDelta creg epsilon kappa : ℝ}
    (hCDelta : 0 < CDelta) (hcreg : 0 < creg)
    (_hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (_hepsilon : 0 < epsilon)
    (haccuracy :
      epsilon ≤ finalAccuracyConstant CDelta creg *
        min 1 (Real.sqrt Delta)) :
    finalEta epsilon kappa ≤ creg / kappa := by
  have hcpos := finalAccuracyConstant_pos hCDelta hcreg
  have hminOne : min 1 (Real.sqrt Delta) ≤ 1 := min_le_left _ _
  have hepsC : epsilon ≤ finalAccuracyConstant CDelta creg := by
    exact haccuracy.trans
      (mul_le_of_le_one_right hcpos.le hminOne)
  have hfour : 4 * epsilon ≤ creg := by
    have hC := finalAccuracyConstant_le_reg_div_four CDelta creg
    nlinarith
  unfold finalEta
  exact (div_le_div_iff_of_pos_right hkappa).2 hfour

theorem finalChainScale_ge_thirtyTwo
    {Delta CDelta creg epsilon kappa : ℝ}
    (hCDelta : 0 < CDelta) (hcreg : 0 < creg)
    (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon)
    (haccuracy :
      epsilon ≤ finalAccuracyConstant CDelta creg *
        min 1 (Real.sqrt Delta)) :
    32 ≤ finalChainScale Delta CDelta epsilon kappa := by
  have hcpos := finalAccuracyConstant_pos hCDelta hcreg
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hsqrtDelta0 : 0 ≤ Real.sqrt Delta := Real.sqrt_nonneg Delta
  have hminSqrt : min 1 (Real.sqrt Delta) ≤ Real.sqrt Delta :=
    min_le_right _ _
  have hepsSqrt :
      epsilon ≤ finalAccuracyConstant CDelta creg * Real.sqrt Delta := by
    exact haccuracy.trans
      (mul_le_mul_of_nonneg_left hminSqrt hcpos.le)
  have hconst := finalAccuracyConstant_le_gap_scale CDelta creg
  have hepsGap :
      epsilon ≤ (1 / (16 * Real.sqrt CDelta)) * Real.sqrt Delta := by
    exact hepsSqrt.trans
      (mul_le_mul_of_nonneg_right hconst hsqrtDelta0)
  have hsqrtC : 0 < Real.sqrt CDelta := Real.sqrt_pos.2 hCDelta
  have hscaled :
      16 * Real.sqrt CDelta * epsilon ≤ Real.sqrt Delta := by
    have hden : 0 < 16 * Real.sqrt CDelta := by positivity
    have hmul := mul_le_mul_of_nonneg_left hepsGap hden.le
    field_simp [hsqrtC.ne'] at hmul
    simpa [mul_assoc] using hmul
  have hscaled0 : 0 ≤ 16 * Real.sqrt CDelta * epsilon := by
    positivity
  have hsquare := (sq_le_sq₀ hscaled0 hsqrtDelta0).2 hscaled
  have hsqrtCSq : (Real.sqrt CDelta) ^ 2 = CDelta :=
    Real.sq_sqrt hCDelta.le
  have hsqrtDeltaSq : (Real.sqrt Delta) ^ 2 = Delta :=
    Real.sq_sqrt hDelta.le
  have hgap : 256 * CDelta * epsilon ^ 2 ≤ Delta := by
    rw [mul_pow, mul_pow, hsqrtCSq, hsqrtDeltaSq] at hsquare
    norm_num at hsquare ⊢
    nlinarith
  have hkSq : 4 ≤ kappa ^ 2 := by nlinarith [sq_nonneg (kappa - 2)]
  rw [finalChainScale_eq hCDelta.ne' hepsilon.ne' hkpos.ne']
  apply (le_div_iff₀ (by positivity : 0 < 32 * CDelta * epsilon ^ 2)).2
  have hprod := mul_le_mul hgap hkSq (by positivity) hDelta.le
  nlinarith

theorem final_parameters_basic
    {Delta CDelta creg epsilon kappa : ℝ}
    (hCDelta : 0 < CDelta) (hcreg : 0 < creg)
    (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon)
    (haccuracy :
      epsilon ≤ finalAccuracyConstant CDelta creg *
        min 1 (Real.sqrt Delta)) :
    let eta := finalEta epsilon kappa
    let T := finalChainLength Delta CDelta epsilon kappa
    0 < eta ∧
      eta ≤ creg / kappa ∧
      0 < T ∧
      Delta / (4 * CDelta * eta ^ 2) ≤ (T : ℝ) ∧
      (T : ℝ) ≤ Delta / (2 * CDelta * eta ^ 2) := by
  dsimp only
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have heta : 0 < finalEta epsilon kappa :=
    finalEta_pos hepsilon hkpos
  have hX32 := finalChainScale_ge_thirtyTwo hCDelta hcreg hDelta
    hkappa hepsilon haccuracy
  have hX2 : 2 ≤ finalChainScale Delta CDelta epsilon kappa :=
    hX32.trans' (by norm_num)
  have hTbounds := finalChainLength_two_sided hX2
  refine ⟨heta,
    finalEta_le_reg_div_kappa hCDelta hcreg hDelta hkpos
      hepsilon haccuracy,
    finalChainLength_pos hX2, ?_, ?_⟩
  · calc
      Delta / (4 * CDelta * (finalEta epsilon kappa) ^ 2) =
          finalChainScale Delta CDelta epsilon kappa / 2 := by
            unfold finalChainScale
            field_simp [hCDelta.ne', heta.ne']
            ring
      _ ≤ (finalChainLength Delta CDelta epsilon kappa : ℝ) :=
        hTbounds.1
  · simpa [finalChainScale] using hTbounds.2

theorem final_initial_gap_le_half
    {Delta CDelta eta : ℝ} {T : ℕ}
    (hCDelta : 0 < CDelta) (heta : 0 < eta)
    (hTupper : (T : ℝ) ≤ Delta / (2 * CDelta * eta ^ 2)) :
    CDelta * eta ^ 2 * T ≤ Delta / 2 := by
  have hden : 0 < 2 * CDelta * eta ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hTupper
    (mul_nonneg hCDelta.le (sq_nonneg eta))
  field_simp [hCDelta.ne', heta.ne'] at hmul
  nlinarith

theorem final_amplified_gradient_scale
    {epsilon kappa : ℝ} (hkappa : kappa ≠ 0) :
    kappa * finalEta epsilon kappa / 2 = 2 * epsilon := by
  unfold finalEta
  field_simp [hkappa]
  ring

/-! ## Reveal probability and the `T / (8p)` budget -/

theorem max_one_div_comparison
    {a beta : ℝ} (ha : 0 ≤ a) (hbeta : 0 < beta) :
    (1 / max 1 beta) * max 1 a ≤ max 1 (a / beta) := by
  by_cases hbetaOne : 1 ≤ beta
  · rw [max_eq_right hbetaOne]
    rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ (1 / beta : ℝ))]
    apply max_le
    · have hone : 1 / beta ≤ 1 := by
        exact (div_le_one hbeta).2 hbetaOne
      simpa using hone.trans (le_max_left 1 (a / beta))
    · simpa [div_eq_mul_inv, mul_comm] using
        (le_max_right 1 (a / beta))
  · have hbetaLe : beta ≤ 1 := le_of_not_ge hbetaOne
    rw [max_eq_left hbetaLe]
    simp only [div_one, one_mul]
    apply max_le_max le_rfl
    exact (le_div_iff₀ hbeta).2 (by
      simpa only [mul_comm] using mul_le_of_le_one_right ha hbetaLe)

theorem finalEta_fourth
    {epsilon kappa : ℝ} (hkappa : kappa ≠ 0) :
    (finalEta epsilon kappa) ^ 4 =
      256 * epsilon ^ 4 / kappa ^ 4 := by
  have hsq := finalEta_sq (epsilon := epsilon) hkappa
  calc
    (finalEta epsilon kappa) ^ 4 =
        ((finalEta epsilon kappa) ^ 2) ^ 2 := by ring
    _ = (16 * epsilon ^ 2 / kappa ^ 2) ^ 2 := by rw [hsq]
    _ = 256 * epsilon ^ 4 / kappa ^ 4 := by
      field_simp [hkappa]
      ring

theorem final_call_scale_identity
    {Delta CDelta Cvar epsilon kappa sigma : ℝ}
    (hCDelta : CDelta ≠ 0) (hCvar : Cvar ≠ 0)
    (hepsilon : epsilon ≠ 0) (hkappa : kappa ≠ 0) :
    Delta / (32 * CDelta * (finalEta epsilon kappa) ^ 2) *
        max 1
          (sigma ^ 2 /
            (Cvar * (finalEta epsilon kappa) ^ 4)) =
      Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
        max 1
          (sigma ^ 2 * kappa ^ 4 /
            (256 * Cvar * epsilon ^ 4)) := by
  rw [finalEta_sq hkappa, finalEta_fourth hkappa]
  congr 1
  · field_simp [hCDelta, hepsilon, hkappa]
    ring
  · congr 1
    field_simp [hCvar, hepsilon, hkappa]

theorem final_T_over_p_raw
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {T : ℕ}
    (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma)
    (hTlower :
      Delta / (4 * CDelta * (finalEta epsilon kappa) ^ 2) ≤ (T : ℝ)) :
    Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
        max 1
          (sigma ^ 2 * kappa ^ 4 /
            (256 * Cvar * epsilon ^ 4)) ≤
      (T : ℝ) /
        (8 * revealProbability Cvar (finalEta epsilon kappa) sigma) := by
  let eta := finalEta epsilon kappa
  let prob := revealProbability Cvar eta sigma
  have heta : 0 < eta := finalEta_pos hepsilon hkappa
  have hprob : 0 < prob := revealProbability_pos hCvar heta
  have hinv : 1 / prob =
      max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
    exact one_div_revealProbability hCvar heta hsigma
  have hTdiv :
      Delta / (32 * CDelta * eta ^ 2) ≤ (T : ℝ) / 8 := by
    calc
      Delta / (32 * CDelta * eta ^ 2) =
          (Delta / (4 * CDelta * eta ^ 2)) / 8 := by ring
      _ ≤ (T : ℝ) / 8 := by
        exact div_le_div_of_nonneg_right (by simpa [eta] using hTlower)
          (by norm_num)
  have hscale0 : 0 ≤ 1 / prob := by positivity
  calc
    Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
          max 1
            (sigma ^ 2 * kappa ^ 4 /
              (256 * Cvar * epsilon ^ 4)) =
        Delta / (32 * CDelta * eta ^ 2) *
          max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
            symm
            simpa [eta] using final_call_scale_identity
              hCDelta.ne' hCvar.ne' hepsilon.ne' hkappa.ne'
    _ = Delta / (32 * CDelta * eta ^ 2) * (1 / prob) := by
      rw [hinv]
    _ ≤ ((T : ℝ) / 8) * (1 / prob) :=
      mul_le_mul_of_nonneg_right hTdiv hscale0
    _ = (T : ℝ) / (8 * prob) := by
      field_simp [hprob.ne']
    _ = (T : ℝ) /
        (8 * revealProbability Cvar (finalEta epsilon kappa) sigma) := by
      rfl

theorem final_T_over_p_main_scale
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {T : ℕ}
    (hDelta : 0 ≤ Delta) (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma)
    (hTlower :
      Delta / (4 * CDelta * (finalEta epsilon kappa) ^ 2) ≤ (T : ℝ)) :
    finalLowerBoundConstant CDelta Cvar *
        (Delta * kappa ^ 2 / epsilon ^ 2 *
          max 1 (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4)) ≤
      (T : ℝ) /
        (8 * revealProbability Cvar (finalEta epsilon kappa) sigma) := by
  have hraw := final_T_over_p_raw hCDelta hCvar hepsilon hkappa hsigma hTlower
  let a : ℝ := sigma ^ 2 * kappa ^ 4 / epsilon ^ 4
  let beta : ℝ := 256 * Cvar
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hmax := max_one_div_comparison ha hbeta
  have hbase : 0 ≤ Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) := by
    positivity
  calc
    finalLowerBoundConstant CDelta Cvar *
          (Delta * kappa ^ 2 / epsilon ^ 2 * max 1 a) =
        (Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2)) *
          ((1 / max 1 beta) * max 1 a) := by
            unfold finalLowerBoundConstant
            dsimp [beta]
            field_simp [hCDelta.ne', hepsilon.ne']
    _ ≤ (Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2)) *
          max 1 (a / beta) :=
      mul_le_mul_of_nonneg_left hmax hbase
    _ = Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
          max 1
            (sigma ^ 2 * kappa ^ 4 /
              (256 * Cvar * epsilon ^ 4)) := by
      congr 2
      dsimp [a, beta]
      field_simp [hCvar.ne', hepsilon.ne']
    _ ≤ (T : ℝ) /
        (8 * revealProbability Cvar (finalEta epsilon kappa) sigma) := hraw

theorem final_call_budget_implies_progress_condition
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {N T : ℕ}
    (hDelta : 0 ≤ Delta) (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma) (hT : 0 < T)
    (hTlower :
      Delta / (4 * CDelta * (finalEta epsilon kappa) ^ 2) ≤ (T : ℝ))
    (hN : (N : ℝ) ≤
      finalLowerBoundConstant CDelta Cvar *
        (Delta * kappa ^ 2 / epsilon ^ 2 *
          max 1 (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4))) :
    (N : ℝ) * revealProbability Cvar (finalEta epsilon kappa) sigma /
        T ≤ 1 / 8 := by
  let prob := revealProbability Cvar (finalEta epsilon kappa) sigma
  have heta := finalEta_pos hepsilon hkappa
  have hprob : 0 < prob := revealProbability_pos hCvar heta
  have hbudget : (N : ℝ) ≤ (T : ℝ) / (8 * prob) :=
    hN.trans (final_T_over_p_main_scale hDelta hCDelta hCvar
      hepsilon hkappa hsigma hTlower)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hmul := mul_le_mul_of_nonneg_right hbudget hprob.le
  have hNp : (N : ℝ) * prob ≤ (T : ℝ) / 8 := by
    calc
      (N : ℝ) * prob ≤ ((T : ℝ) / (8 * prob)) * prob := hmul
      _ = (T : ℝ) / 8 := by field_simp [hprob.ne']
  change (N : ℝ) * prob / T ≤ 1 / 8
  apply (div_le_iff₀ hTreal).2
  calc
    (N : ℝ) * prob ≤ (T : ℝ) / 8 := hNp
    _ = (1 / 8 : ℝ) * T := by ring

/-! ## Existence of a sufficiently large finite dimension -/

def requiredHaarDimension (CH : ℝ) (n T : ℕ) : ℝ :=
  T + CH * (230 ^ 2 * T) * n *
    Real.log (16 * n ^ 2 * T)

theorem exists_dimension_choice (CH : ℝ) (n T : ℕ) :
    ∃ d : ℕ, requiredHaarDimension CH n T ≤ d := by
  exact exists_nat_ge (requiredHaarDimension CH n T)

theorem dimension_choice_event_budget_positive
    {n T : ℕ} (hn : 0 < n) (hT : 0 < T) :
    0 < (n : ℝ) ^ 2 * T := by
  positivity

/-! ## From a random proof frame to one deterministic hard frame -/

section FixedFrame

variable {Frame Omega : Type*}
  {mFrame : MeasurableSpace Frame} {mOmega : MeasurableSpace Omega}
  {nu : @Measure Frame mFrame} {mu : @Measure Omega mOmega}
  [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]

/-- A loss which is at least `2 epsilon` on an event of probability at least
`3/4` has expectation at least `3 epsilon / 2`. -/
theorem integral_ge_three_halves_of_good_event
    {loss : Frame × Omega → ℝ} {good : Set (Frame × Omega)}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hloss : Integrable loss (nu.prod mu))
    (hgoodMeas : MeasurableSet good)
    (hgoodProb : 3 / 4 ≤ (nu.prod mu).real good)
    (hlossNonneg : ∀ z, 0 ≤ loss z)
    (hlossGood : ∀ z ∈ good, 2 * epsilon ≤ loss z) :
    3 / 2 * epsilon ≤ ∫ z, loss z ∂(nu.prod mu) := by
  let baseline : Frame × Omega → ℝ :=
    good.indicator (fun _ ↦ 2 * epsilon)
  have hbaseline : Integrable baseline (nu.prod mu) := by
    dsimp [baseline]
    exact (integrable_const (2 * epsilon)).indicator hgoodMeas
  have hpoint : ∀ z, baseline z ≤ loss z := by
    intro z
    by_cases hz : z ∈ good
    · simp only [baseline, Set.indicator_of_mem hz]
      exact hlossGood z hz
    · simp only [baseline, Set.indicator_of_notMem hz]
      exact hlossNonneg z
  have hintegral :
      ∫ z, baseline z ∂(nu.prod mu) ≤
        ∫ z, loss z ∂(nu.prod mu) :=
    integral_mono_ae hbaseline hloss
      (ae_of_all (nu.prod mu) hpoint)
  have hbaselineValue :
      ∫ z, baseline z ∂(nu.prod mu) =
        (nu.prod mu).real good * (2 * epsilon) := by
    dsimp [baseline]
    rw [integral_indicator_const (2 * epsilon) hgoodMeas]
    simp only [smul_eq_mul]
  rw [hbaselineValue] at hintegral
  have hscale : 0 ≤ 2 * epsilon := by positivity
  have hprobScaled := mul_le_mul_of_nonneg_right hgoodProb hscale
  nlinarith

/-- Fubini plus the first-moment method: the random-frame proof distribution
produces one deterministic frame whose conditional risk exceeds `epsilon`. -/
theorem exists_fixed_frame_of_joint_good_event
    {loss : Frame × Omega → ℝ} {good : Set (Frame × Omega)}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hloss : Integrable loss (nu.prod mu))
    (hgoodMeas : MeasurableSet good)
    (hgoodProb : 3 / 4 ≤ (nu.prod mu).real good)
    (hlossNonneg : ∀ z, 0 ≤ loss z)
    (hlossGood : ∀ z ∈ good, 2 * epsilon ≤ loss z) :
    ∃ U0 : Frame, epsilon < ∫ omega, loss (U0, omega) ∂mu := by
  have haverage := integral_ge_three_halves_of_good_event
    hepsilon hloss hgoodMeas hgoodProb hlossNonneg hlossGood
  rw [integral_prod loss hloss] at haverage
  have hriskIntegrable :
      Integrable (fun U ↦ ∫ omega, loss (U, omega) ∂mu) nu :=
    hloss.integral_prod_left
  obtain ⟨U0, hmean⟩ := exists_integral_le hriskIntegrable
  refine ⟨U0, ?_⟩
  nlinarith

/-- Concrete specialization to the hard hyper-objective.  The algorithmic
output may depend jointly on the proof frame and all remaining randomness.
Once unfinished progress has product probability at least `3/4`, one fixed
orthonormal frame has conditional expected gradient norm larger than
`epsilon`. -/
theorem exists_fixed_hard_frame_of_unfinished_probability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {mFrame : MeasurableSpace (ChainVector T →ₗᵢ[ℝ] E)}
    {nu : @Measure (ChainVector T →ₗᵢ[ℝ] E) mFrame}
    [IsProbabilityMeasure nu]
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (output : (ChainVector T →ₗᵢ[ℝ] E) × Omega → E)
    (hloss : Integrable
      (fun z ↦
        ‖gradient
          (hardHyperObjective (finalEta epsilon kappa) kappa z.1)
          (output z)‖)
      (nu.prod mu))
    (hgoodMeas : MeasurableSet
      {z | progress (finalEta epsilon kappa / 4)
        (hiddenFrameTranspose z.1
          (softProjection (hardRadius (finalEta epsilon kappa) T)
            (kappa • output z))) < T})
    (hgoodProb : 3 / 4 ≤ (nu.prod mu).real
      {z | progress (finalEta epsilon kappa / 4)
        (hiddenFrameTranspose z.1
          (softProjection (hardRadius (finalEta epsilon kappa) T)
            (kappa • output z))) < T}) :
    ∃ U0 : ChainVector T →ₗᵢ[ℝ] E,
      epsilon < ∫ omega,
        ‖gradient
          (hardHyperObjective (finalEta epsilon kappa) kappa U0)
          (output (U0, omega))‖ ∂mu := by
  let eta := finalEta epsilon kappa
  let loss : (ChainVector T →ₗᵢ[ℝ] E) × Omega → ℝ :=
    fun z ↦ ‖gradient (hardHyperObjective eta kappa z.1) (output z)‖
  let good : Set ((ChainVector T →ₗᵢ[ℝ] E) × Omega) :=
    {z | progress (eta / 4)
      (hiddenFrameTranspose z.1
        (softProjection (hardRadius eta T) (kappa • output z))) < T}
  have heta : 0 < eta := finalEta_pos hepsilon hkappa
  have hlossNonneg : ∀ z, 0 ≤ loss z := fun z ↦ norm_nonneg _
  have hlossGood : ∀ z ∈ good, 2 * epsilon ≤ loss z := by
    intro z hz
    have hgrad := norm_gradient_hardHyperObjective_gt
      heta hkappa hT z.1 (output z) hz
    have hscale := final_amplified_gradient_scale
      (epsilon := epsilon) hkappa.ne'
    dsimp [loss]
    nlinarith
  have hfixed := exists_fixed_frame_of_joint_good_event
    (nu := nu) (mu := mu) hepsilon
    (by simpa [loss, eta] using hloss)
    (by simpa [good, eta] using hgoodMeas)
    (by simpa [good, eta] using hgoodProb)
    hlossNonneg hlossGood
  simpa [loss, eta] using hfixed

end FixedFrame

end

end BilevelLowerBound
