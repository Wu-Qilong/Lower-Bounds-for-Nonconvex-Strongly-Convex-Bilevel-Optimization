/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ParameterSelection

/-!
# Assembly of the stochastic bilevel lower bound

This module joins the checked analytic, oracle, progress, and parameter
layers.  The cited conditional-Haar input is supplied as one conditional cap
bound for every fixed padded triple.  `adaptiveHaarConnection` constructs the
single Haar-good event and its progress implication, so the main theorem does
not assume that event or implication separately.

For completely arbitrary randomized algorithms the output need not have a
finite first or second moment.  We therefore state moment failure as the
mathematically exhaustive alternative: either the corresponding nonnegative
loss is not integrable, or its (finite) expectation is larger than the target.
When the moments are integrable, the usual expectation inequalities follow
immediately.
-/

open Filter Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

/-! ## Final scalar scale and condition-number replacement -/

def mainComplexityScale
    (Delta epsilon kappa sigma : ℝ) : ℝ :=
  Delta * kappa ^ 2 / epsilon ^ 2 *
    max 1 (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4)

/-- The explicit universal coefficient in the zero-chain gap estimate. -/
def chainGapConstant : ℝ :=
  4 * Real.exp 1 * phiBound

/-- A universal scale which turns `eta <= c_reg / kappa` into both
`eta <= 1` and the Hessian-perturbation smallness condition. -/
def constructionRegularityScale (CHess : ℝ) : ℝ :=
  1 / (2 * (1 + CHess))

theorem chainGapConstant_pos : 0 < chainGapConstant := by
  unfold chainGapConstant
  have hfirst : 0 < Real.sqrt (Real.exp 1) :=
    Real.sqrt_pos.2 (Real.exp_pos 1)
  have hsecond : 0 < Real.sqrt (Real.pi / (1 / 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos Real.pi_pos (by norm_num))
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
    (mul_pos hfirst hsecond)

theorem constructionRegularityScale_pos
    {CHess : ℝ} (hCHess : 0 ≤ CHess) :
    0 < constructionRegularityScale CHess := by
  unfold constructionRegularityScale
  positivity

theorem constructionRegularityScale_le_one
    {CHess : ℝ} (hCHess : 0 ≤ CHess) :
    constructionRegularityScale CHess ≤ 1 := by
  unfold constructionRegularityScale
  apply (div_le_one (by positivity : 0 < 2 * (1 + CHess))).2
  linarith

theorem constructionRegularityScale_hessian
    {CHess : ℝ} (hCHess : 0 ≤ CHess) :
    CHess * constructionRegularityScale CHess ≤ 1 / 2 := by
  unfold constructionRegularityScale
  rw [one_div, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + CHess))).2
  nlinarith

theorem final_scale_implies_regularities
    {CHess eta kappa : ℝ} (hCHess : 0 ≤ CHess)
    (hkappa : 1 ≤ kappa) (_heta : 0 ≤ eta)
    (hetaSmall :
      eta ≤ constructionRegularityScale CHess / kappa) :
    eta ≤ 1 ∧ CHess * eta ≤ 1 / (2 * kappa) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hregPos := constructionRegularityScale_pos hCHess
  have hregOne := constructionRegularityScale_le_one hCHess
  have hetaOne : eta ≤ 1 := by
    calc
      eta ≤ constructionRegularityScale CHess / kappa := hetaSmall
      _ ≤ constructionRegularityScale CHess :=
        (div_le_self hregPos.le hkappa)
      _ ≤ 1 := hregOne
  have hmul := mul_le_mul_of_nonneg_left hetaSmall hCHess
  have hregHess := constructionRegularityScale_hessian hCHess
  constructor
  · exact hetaOne
  · calc
      CHess * eta ≤
          CHess * (constructionRegularityScale CHess / kappa) := hmul
      _ = (CHess * constructionRegularityScale CHess) / kappa := by ring
      _ ≤ (1 / 2) / kappa :=
        div_le_div_of_nonneg_right hregHess hkpos.le
      _ = 1 / (2 * kappa) := by ring

theorem hardHyperObjective_initial_gap_le_chainGapConstant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    hardHyperObjective eta kappa J 0 -
        sInf (Set.range (hardHyperObjective eta kappa J)) ≤
      chainGapConstant * eta ^ 2 * T := by
  have hgap := hardHyperObjective_initial_gap eta kappa J
  unfold chainGapConstant
  calc
    hardHyperObjective eta kappa J 0 -
          sInf (Set.range (hardHyperObjective eta kappa J)) ≤
        eta ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := hgap
    _ = (4 * Real.exp 1 * phiBound) * eta ^ 2 * T := by ring

theorem mainComplexityScale_nonneg
    {Delta epsilon kappa sigma : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : epsilon ≠ 0) :
    0 ≤ mainComplexityScale Delta epsilon kappa sigma := by
  unfold mainComplexityScale
  positivity

/-- Replacing the construction parameter by a comparable actual condition
number loses at most the sixth power of the comparison constant. -/
theorem condition_number_scale_comparison
    {Delta epsilon kappa kappaY sigma Ckappa : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (_hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (_hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hupper : kappaY ≤ Ckappa * kappa) :
    mainComplexityScale Delta epsilon kappaY sigma /
        Ckappa ^ 6 ≤
      mainComplexityScale Delta epsilon kappa sigma := by
  have hC0 : 0 ≤ Ckappa := hCkappa.trans' (by norm_num)
  have hkSq : kappaY ^ 2 ≤ Ckappa ^ 2 * kappa ^ 2 := by
    nlinarith [sq_nonneg (Ckappa * kappa - kappaY)]
  have hkFour : kappaY ^ 4 ≤ Ckappa ^ 4 * kappa ^ 4 := by
    nlinarith [sq_nonneg (Ckappa ^ 2 * kappa ^ 2 - kappaY ^ 2)]
  let aY : ℝ := sigma ^ 2 * kappaY ^ 4 / epsilon ^ 4
  let aK : ℝ := sigma ^ 2 * kappa ^ 4 / epsilon ^ 4
  have haY : 0 ≤ aY := by dsimp [aY]; positivity
  have haK : 0 ≤ aK := by dsimp [aK]; positivity
  have haComp : aY ≤ Ckappa ^ 4 * aK := by
    dsimp [aY, aK]
    apply (div_le_iff₀ (by positivity : 0 < epsilon ^ 4)).2
    have hmul := mul_le_mul_of_nonneg_left hkFour (sq_nonneg sigma)
    calc
      sigma ^ 2 * kappaY ^ 4 ≤
          sigma ^ 2 * (Ckappa ^ 4 * kappa ^ 4) := hmul
      _ = Ckappa ^ 4 *
          (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4) * epsilon ^ 4 := by
        field_simp [hepsilon.ne']
  have hCfour : 1 ≤ Ckappa ^ 4 := by
    nlinarith [sq_nonneg Ckappa, sq_nonneg (Ckappa ^ 2 - 1)]
  have hmax : max 1 aY ≤ Ckappa ^ 4 * max 1 aK := by
    apply max_le
    · calc
        1 ≤ Ckappa ^ 4 := hCfour
        _ = Ckappa ^ 4 * 1 := by ring
        _ ≤ Ckappa ^ 4 * max 1 aK :=
          mul_le_mul_of_nonneg_left (le_max_left 1 aK) (by positivity)
    · exact haComp.trans
        (mul_le_mul_of_nonneg_left (le_max_right 1 aK) (by positivity))
  have hbase :
      Delta * kappaY ^ 2 / epsilon ^ 2 ≤
        Ckappa ^ 2 * (Delta * kappa ^ 2 / epsilon ^ 2) := by
    apply (div_le_iff₀ (by positivity : 0 < epsilon ^ 2)).2
    have hmul := mul_le_mul_of_nonneg_left hkSq hDelta
    calc
      Delta * kappaY ^ 2 ≤
          Delta * (Ckappa ^ 2 * kappa ^ 2) := hmul
      _ = Ckappa ^ 2 *
          (Delta * kappa ^ 2 / epsilon ^ 2) * epsilon ^ 2 := by
        field_simp [hepsilon.ne']
  have hprod := mul_le_mul hbase hmax
    (by exact le_max_left 1 aY |>.trans' (by norm_num))
    (by positivity)
  have hCpos : 0 < Ckappa ^ 6 := by positivity
  unfold mainComplexityScale
  dsimp [aY, aK] at hprod ⊢
  apply (div_le_iff₀ hCpos).2
  calc
    (Delta * kappaY ^ 2 / epsilon ^ 2) *
          max 1 (sigma ^ 2 * kappaY ^ 4 / epsilon ^ 4) ≤
        (Ckappa ^ 2 * (Delta * kappa ^ 2 / epsilon ^ 2)) *
          (Ckappa ^ 4 *
            max 1 (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4)) := hprod
    _ = (Delta * kappa ^ 2 / epsilon ^ 2 *
          max 1 (sigma ^ 2 * kappa ^ 4 / epsilon ^ 4)) *
        Ckappa ^ 6 := by ring

theorem condition_number_call_budget_transfer
    {N : ℕ} {Delta epsilon kappa kappaY sigma Ckappa cLB : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hcLB : 0 ≤ cLB) (hupper : kappaY ≤ Ckappa * kappa)
    (hN : (N : ℝ) ≤
      (cLB / Ckappa ^ 6) *
        mainComplexityScale Delta epsilon kappaY sigma) :
    (N : ℝ) ≤
      cLB * mainComplexityScale Delta epsilon kappa sigma := by
  have hscale := condition_number_scale_comparison hDelta hepsilon
    hkappa hkappaY hsigma hCkappa hupper
  calc
    (N : ℝ) ≤
        (cLB / Ckappa ^ 6) *
          mainComplexityScale Delta epsilon kappaY sigma := hN
    _ = cLB *
        (mainComplexityScale Delta epsilon kappaY sigma / Ckappa ^ 6) := by
      ring
    _ ≤ cLB * mainComplexityScale Delta epsilon kappa sigma :=
      mul_le_mul_of_nonneg_left hscale hcLB

/-- The complete complexity scale is comparable in both directions when
`kappa <= kappaY <= Ckappa * kappa`. -/
theorem condition_number_scale_sandwich
    {Delta epsilon kappa kappaY sigma Ckappa : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hlower : kappa ≤ kappaY) (hupper : kappaY ≤ Ckappa * kappa) :
    mainComplexityScale Delta epsilon kappa sigma ≤
        mainComplexityScale Delta epsilon kappaY sigma ∧
      mainComplexityScale Delta epsilon kappaY sigma /
          Ckappa ^ 6 ≤
        mainComplexityScale Delta epsilon kappa sigma := by
  constructor
  · have hmono := condition_number_scale_comparison
      (kappa := kappaY) (kappaY := kappa) (Ckappa := 1)
      hDelta hepsilon hkappaY hkappa hsigma (by norm_num) (by simpa using hlower)
    simpa using hmono
  · exact condition_number_scale_comparison hDelta hepsilon
      hkappa hkappaY hsigma hCkappa hupper

/-! The scalar universal constants really can be chosen simultaneously. -/
theorem exists_main_scalar_constants :
    ∃ CDelta Cvar CHess creg cEpsilon cLB Ckappa : ℝ,
      0 < CDelta ∧ 0 < Cvar ∧ 0 ≤ CHess ∧ 0 < creg ∧
      0 < cEpsilon ∧ 0 < cLB ∧ 1 ≤ Ckappa ∧
      CDelta = chainGapConstant ∧
      creg = constructionRegularityScale CHess ∧
      cEpsilon = finalAccuracyConstant CDelta creg ∧
      cLB = finalLowerBoundConstant CDelta Cvar ∧
      Ckappa = 2 * (2 + CHess) := by
  obtain ⟨Cvar, hCvar, _horacle⟩ :=
    exists_fullSampleLower_oracle_properties
  obtain ⟨CHess, hCHess, _hcondition⟩ :=
    exists_orthonormalFrame_hardLower_condition_number_comparison
  let CDelta := chainGapConstant
  let creg := constructionRegularityScale CHess
  let cEpsilon := finalAccuracyConstant CDelta creg
  let cLB := finalLowerBoundConstant CDelta Cvar
  let Ckappa := 2 * (2 + CHess)
  have hCDelta : 0 < CDelta := chainGapConstant_pos
  have hcreg : 0 < creg := constructionRegularityScale_pos hCHess
  have hcEpsilon : 0 < cEpsilon :=
    finalAccuracyConstant_pos hCDelta hcreg
  have hcLB : 0 < cLB := by
    dsimp [cLB]
    unfold finalLowerBoundConstant
    positivity
  have hCkappa : 1 ≤ Ckappa := by
    dsimp [Ckappa]
    linarith
  exact ⟨CDelta, Cvar, CHess, creg, cEpsilon, cLB, Ckappa,
    hCDelta, hCvar, hCHess, hcreg, hcEpsilon, hcLB, hCkappa,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The final regularity scale plugs directly into the sharp lower-level
condition-number certificate. -/
theorem exists_final_scale_condition_number_comparison :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {kappa eta : ℝ},
        1 ≤ kappa → 0 < eta → 0 < T →
        eta ≤ constructionRegularityScale CHess / kappa →
        ∀ (J : ChainVector T →ₗᵢ[ℝ] E) (muGAct Ly : ℝ),
        IsSharpLowerHessianModulus
            (hardLowerSlice kappa eta (hiddenFrameTranspose J)) muGAct →
        IsSharpLowerHessianUpperBound
            (hardLowerSlice kappa eta (hiddenFrameTranspose J)) Ly →
        kappa ≤ Ly / muGAct ∧
          Ly / muGAct ≤ 2 * (2 + CHess) * kappa := by
  obtain ⟨CHess, hCHess, hcondition⟩ :=
    exists_orthonormalFrame_hardLower_condition_number_comparison
  refine ⟨CHess, hCHess, ?_⟩
  intro E _ _ _ T kappa eta hkappa heta hT hetaSmall J muGAct Ly
    hmuGAct hLy
  have hreg := final_scale_implies_regularities hCHess hkappa heta.le
    hetaSmall
  exact hcondition hkappa heta hreg.1 hT J hreg.2 muGAct Ly hmuGAct hLy

/-! ## Fixed sections and moment failure -/

/-- A product event of probability at least `3/4` has one deterministic
first coordinate whose section has indicator expectation at least `3/4`.
This is the fixed-frame step without any moment assumption on the loss. -/
theorem exists_fixed_section_of_product_event
    {Frame Omega : Type*}
    {mFrame : MeasurableSpace Frame} {mOmega : MeasurableSpace Omega}
    {nu : @Measure Frame mFrame} {mu : @Measure Omega mOmega}
    [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]
    {good : Set (Frame × Omega)}
    (hgoodMeas : MeasurableSet good)
    (hgoodProb : 3 / 4 ≤ (nu.prod mu).real good) :
    ∃ U0 : Frame, 3 / 4 ≤
      ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) (U0, omega) ∂mu := by
  let indicator : Frame × Omega → ℝ :=
    good.indicator (fun _ ↦ 1)
  have hindicator : Integrable indicator (nu.prod mu) := by
    dsimp [indicator]
    exact (integrable_const (1 : ℝ)).indicator hgoodMeas
  have hvalue :
      ∫ z, indicator z ∂(nu.prod mu) = (nu.prod mu).real good := by
    dsimp [indicator]
    simpa using integral_indicator_const (1 : ℝ) hgoodMeas
  have hsections :
      Integrable (fun U ↦ ∫ omega, indicator (U, omega) ∂mu) nu :=
    hindicator.integral_prod_left
  obtain ⟨U0, hmean⟩ := exists_integral_le hsections
  refine ⟨U0, ?_⟩
  have hFubini :
      ∫ U, ∫ omega, indicator (U, omega) ∂mu ∂nu =
        (nu.prod mu).real good := by
    rw [← integral_prod indicator hindicator, hvalue]
  rw [hFubini] at hmean
  exact hgoodProb.trans hmean

/-- For a nonnegative loss which is larger than `2 epsilon` on a section
of probability at least `3/4`, either the first moment is infinite/not
Bochner-integrable or its expectation is larger than `epsilon`; the same
alternative holds for the second moment. -/
theorem moment_failure_of_large_event
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {good : Set Omega} {loss : Omega → ℝ} {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hgoodMeas : MeasurableSet good)
    (hgoodProb : 3 / 4 ≤
      ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu)
    (hlossNonneg : ∀ omega, 0 ≤ loss omega)
    (hlossGood : ∀ omega ∈ good, 2 * epsilon < loss omega) :
    (¬ Integrable loss mu ∨ epsilon < ∫ omega, loss omega ∂mu) ∧
      (¬ Integrable (fun omega ↦ loss omega ^ 2) mu ∨
        epsilon ^ 2 < ∫ omega, loss omega ^ 2 ∂mu) := by
  constructor
  · by_cases hlossInt : Integrable loss mu
    · right
      let baseline : Omega → ℝ :=
        good.indicator (fun _ ↦ 2 * epsilon)
      have hbaseInt : Integrable baseline mu := by
        dsimp [baseline]
        exact (integrable_const (2 * epsilon)).indicator hgoodMeas
      have hpoint : ∀ omega, baseline omega ≤ loss omega := by
        intro omega
        by_cases hmem : omega ∈ good
        · simp only [baseline, Set.indicator_of_mem hmem]
          exact (hlossGood omega hmem).le
        · simp only [baseline, Set.indicator_of_notMem hmem]
          exact hlossNonneg omega
      have hmono := integral_mono_ae hbaseInt hlossInt
        (ae_of_all mu hpoint)
      have hbaseValue :
          ∫ omega, baseline omega ∂mu =
            (2 * epsilon) *
              ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu := by
        dsimp [baseline]
        rw [integral_indicator_const (2 * epsilon) hgoodMeas,
          integral_indicator_const (1 : ℝ) hgoodMeas]
        simp only [smul_eq_mul, mul_one]
        ring
      rw [hbaseValue] at hmono
      have hscale := mul_le_mul_of_nonneg_left hgoodProb
        (by positivity : 0 ≤ 2 * epsilon)
      nlinarith
    · exact Or.inl hlossInt
  · by_cases hlossSqInt : Integrable (fun omega ↦ loss omega ^ 2) mu
    · right
      let baselineSq : Omega → ℝ :=
        good.indicator (fun _ ↦ (2 * epsilon) ^ 2)
      have hbaseSqInt : Integrable baselineSq mu := by
        dsimp [baselineSq]
        exact (integrable_const ((2 * epsilon) ^ 2)).indicator hgoodMeas
      have hpointSq : ∀ omega, baselineSq omega ≤ loss omega ^ 2 := by
        intro omega
        by_cases hmem : omega ∈ good
        · simp only [baselineSq, Set.indicator_of_mem hmem]
          exact (sq_le_sq₀ (by positivity) (hlossNonneg omega)).2
            (hlossGood omega hmem).le
        · simp only [baselineSq, Set.indicator_of_notMem hmem]
          positivity
      have hmono := integral_mono_ae hbaseSqInt hlossSqInt
        (ae_of_all mu hpointSq)
      have hbaseSqValue :
          ∫ omega, baselineSq omega ∂mu =
            (2 * epsilon) ^ 2 *
              ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu := by
        dsimp [baselineSq]
        rw [integral_indicator_const ((2 * epsilon) ^ 2) hgoodMeas,
          integral_indicator_const (1 : ℝ) hgoodMeas]
        simp only [smul_eq_mul, mul_one]
        ring
      rw [hbaseSqValue] at hmono
      have hscale := mul_le_mul_of_nonneg_left hgoodProb
        (by positivity : 0 ≤ (2 * epsilon) ^ 2)
      nlinarith [sq_pos_of_pos hepsilon]
    · exact Or.inl hlossSqInt

/-- Sharp constant-margin version of `moment_failure_of_large_event`.  A loss
strictly larger than `2 * epsilon` on an event of probability at least `3/4`
has first moment strictly larger than `3 * epsilon / 2`.  Its second moment is
at least `3 * epsilon^2`, which in particular is strictly larger than
`9 * epsilon^2 / 4`.  As in the weaker statement, nonintegrability is retained
as an explicit alternative. -/
theorem moment_failure_of_large_event_with_margin
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {good : Set Omega} {loss : Omega → ℝ} {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hgoodMeas : MeasurableSet good)
    (hgoodProb : 3 / 4 ≤
      ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu)
    (hlossNonneg : ∀ omega, 0 ≤ loss omega)
    (hlossGood : ∀ omega ∈ good, 2 * epsilon < loss omega) :
    (¬ Integrable loss mu ∨
        3 * epsilon / 2 < ∫ omega, loss omega ∂mu) ∧
      (¬ Integrable (fun omega ↦ loss omega ^ 2) mu ∨
        9 * epsilon ^ 2 / 4 < ∫ omega, loss omega ^ 2 ∂mu) := by
  constructor
  · by_cases hlossInt : Integrable loss mu
    · right
      let baseline : Omega → ℝ :=
        good.indicator (fun _ ↦ 2 * epsilon)
      have hbaseInt : Integrable baseline mu := by
        dsimp [baseline]
        exact (integrable_const (2 * epsilon)).indicator hgoodMeas
      have hpoint : ∀ omega, baseline omega ≤ loss omega := by
        intro omega
        by_cases hmem : omega ∈ good
        · simp only [baseline, Set.indicator_of_mem hmem]
          exact (hlossGood omega hmem).le
        · simp only [baseline, Set.indicator_of_notMem hmem]
          exact hlossNonneg omega
      let residual : Omega → ℝ := fun omega ↦ loss omega - baseline omega
      have hresInt : Integrable residual mu := hlossInt.sub hbaseInt
      have hresNonneg : ∀ omega, 0 ≤ residual omega := by
        intro omega
        exact sub_nonneg.mpr (hpoint omega)
      have hgoodReal : 0 < mu.real good := by
        have hone :
            (∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu) =
              mu.real good := by
          simpa using integral_indicator_const (1 : ℝ) hgoodMeas
        rw [hone] at hgoodProb
        linarith
      have hgoodMeasure : 0 < mu good :=
        (ENNReal.toReal_pos_iff.mp hgoodReal).1
      have hgoodSupport : good ⊆ Function.support residual := by
        intro omega hmem
        have hstrict : 0 < residual omega := by
          dsimp [residual, baseline]
          simp only [Set.indicator_of_mem hmem]
          linarith [hlossGood omega hmem]
        exact hstrict.ne'
      have hsupport : 0 < mu (Function.support residual) :=
        hgoodMeasure.trans_le (measure_mono hgoodSupport)
      have hresPos : 0 < ∫ omega, residual omega ∂mu :=
        (integral_pos_iff_support_of_nonneg hresNonneg hresInt).2 hsupport
      have hbaseValue :
          ∫ omega, baseline omega ∂mu =
            (2 * epsilon) *
              ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu := by
        dsimp [baseline]
        rw [integral_indicator_const (2 * epsilon) hgoodMeas,
          integral_indicator_const (1 : ℝ) hgoodMeas]
        simp only [smul_eq_mul, mul_one]
        ring
      have hbaseLower : 3 * epsilon / 2 ≤
          ∫ omega, baseline omega ∂mu := by
        rw [hbaseValue]
        have hscale := mul_le_mul_of_nonneg_left hgoodProb
          (by positivity : 0 ≤ 2 * epsilon)
        nlinarith
      have hresValue :
          ∫ omega, residual omega ∂mu =
            (∫ omega, loss omega ∂mu) -
              ∫ omega, baseline omega ∂mu := by
        exact integral_sub hlossInt hbaseInt
      rw [hresValue] at hresPos
      linarith
    · exact Or.inl hlossInt
  · by_cases hlossSqInt : Integrable (fun omega ↦ loss omega ^ 2) mu
    · right
      let baselineSq : Omega → ℝ :=
        good.indicator (fun _ ↦ (2 * epsilon) ^ 2)
      have hbaseSqInt : Integrable baselineSq mu := by
        dsimp [baselineSq]
        exact (integrable_const ((2 * epsilon) ^ 2)).indicator hgoodMeas
      have hpointSq : ∀ omega, baselineSq omega ≤ loss omega ^ 2 := by
        intro omega
        by_cases hmem : omega ∈ good
        · simp only [baselineSq, Set.indicator_of_mem hmem]
          exact (sq_le_sq₀ (by positivity) (hlossNonneg omega)).2
            (hlossGood omega hmem).le
        · simp only [baselineSq, Set.indicator_of_notMem hmem]
          positivity
      have hmono := integral_mono_ae hbaseSqInt hlossSqInt
        (ae_of_all mu hpointSq)
      have hbaseSqValue :
          ∫ omega, baselineSq omega ∂mu =
            (2 * epsilon) ^ 2 *
              ∫ omega, good.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu := by
        dsimp [baselineSq]
        rw [integral_indicator_const ((2 * epsilon) ^ 2) hgoodMeas,
          integral_indicator_const (1 : ℝ) hgoodMeas]
        simp only [smul_eq_mul, mul_one]
        ring
      rw [hbaseSqValue] at hmono
      have hscale := mul_le_mul_of_nonneg_left hgoodProb
        (by positivity : 0 ≤ (2 * epsilon) ^ 2)
      nlinarith [sq_pos_of_pos hepsilon]
    · exact Or.inl hlossSqInt

/-! ## End-to-end assembly -/

/-- The final choices simultaneously satisfy the rounding, gap, dimension,
and Markov-call conditions. -/
theorem final_parameter_dimension_certificate
    {N : ℕ} {Delta CDelta creg Cvar epsilon kappa sigma CH : ℝ}
    (hCDelta : 0 < CDelta) (hcreg : 0 < creg)
    (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon) (hsigma : 0 ≤ sigma)
    (hCvar : 0 < Cvar)
    (haccuracy :
      epsilon ≤ finalAccuracyConstant CDelta creg *
        min 1 (Real.sqrt Delta))
    (hN : (N : ℝ) ≤
      finalLowerBoundConstant CDelta Cvar *
        mainComplexityScale Delta epsilon kappa sigma) :
    let eta := finalEta epsilon kappa
    let T := finalChainLength Delta CDelta epsilon kappa
    let prob := revealProbability Cvar eta sigma
    0 < eta ∧ eta ≤ creg / kappa ∧ 0 < T ∧
      CDelta * eta ^ 2 * T ≤ Delta / 2 ∧
      (N : ℝ) * prob / T ≤ 1 / 8 ∧
      ∃ d : ℕ, requiredHaarDimension CH (N + 1) T ≤ d := by
  dsimp only
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  rcases hparams with ⟨heta, hetaSmall, hT, hTlower, hTupper⟩
  have hgap := final_initial_gap_le_half hCDelta heta hTupper
  have hcalls := final_call_budget_implies_progress_condition
    hDelta.le hCDelta hCvar hepsilon
    (lt_of_lt_of_le (by norm_num) hkappa) hsigma hT hTlower
    (by simpa [mainComplexityScale] using hN)
  obtain ⟨d, hd⟩ := exists_dimension_choice CH (N + 1)
    (finalChainLength Delta CDelta epsilon kappa)
  exact ⟨heta, hetaSmall, hT, hgap, hcalls, d, hd⟩

/-- Fully assembled failure statement for the formalized hard interaction.

The external geometric input is stated at its cited interface: each fixed
padded cap event satisfies a conditional probability bound.  The deterministic
geometry gives `hnoCapProgress`.  `adaptiveHaarConnection` turns these inputs
into the measurable Haar-good event, its `1/8` failure bound, and the pointwise
progress statement.  Final parameter selection, the fresh bits and Markov
inequality, fixed-frame selection, and the gap-gradient argument are internal.
-/
theorem main_lower_bound_assembly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T N : ℕ}
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {mFrame : MeasurableSpace (ChainVector T →ₗᵢ[ℝ] E)}
    {nu : @Measure (ChainVector T →ₗᵢ[ℝ] E) mFrame}
    [IsProbabilityMeasure nu]
    {Delta CDelta creg Cvar epsilon kappa sigma q : ℝ}
    (hCDelta : 0 < CDelta) (hchainGap : chainGapConstant ≤ CDelta)
    (hcreg : 0 < creg) (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon) (hsigma : 0 ≤ sigma)
    (hCvar : 0 < Cvar)
    (haccuracy :
      epsilon ≤ finalAccuracyConstant CDelta creg *
        min 1 (Real.sqrt Delta))
    (hTdef : T = finalChainLength Delta CDelta epsilon kappa)
    (hN : (N : ℝ) ≤
      finalLowerBoundConstant CDelta Cvar *
        mainComplexityScale Delta epsilon kappa sigma)
    (past : Fin N → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (success : Fin N → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hfresh : ∀ t,
      FreshBernoulliEvent
        (mFrame.prod mOmega) (nu.prod mu) (past t) (success t)
        (revealProbability Cvar (finalEta epsilon kappa) sigma))
    (output : (ChainVector T →ₗᵢ[ℝ] E) × Omega → E)
    (capInfo : PaddedCapIndex (N + 1) T → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (capEvent : PaddedCapIndex (N + 1) T → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hcap : ∀ i, ConditionalEventBound (nu.prod mu)
      (capInfo i) (capEvent i) q)
    (hcapBudget : ((((N + 1) ^ 2 * T : ℕ) : ℝ) * q ≤ 1 / 8))
    (hnoCapProgress : ∀ z, (∀ i, z ∉ capEvent i) →
      progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) ≤
        min T (successCountNat success z))
    (hunfMeas : MeasurableSet
      {z | progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) < T}) :
    ∃ U0 : ChainVector T →ₗᵢ[ℝ] E,
      hardHyperObjective (finalEta epsilon kappa) kappa U0 0 -
          sInf (Set.range
            (hardHyperObjective (finalEta epsilon kappa) kappa U0)) ≤
        Delta ∧
      (¬ Integrable
          (fun omega ↦
            ‖gradient
              (hardHyperObjective (finalEta epsilon kappa) kappa U0)
              (output (U0, omega))‖) mu ∨
        3 * epsilon / 2 < ∫ omega,
          ‖gradient
            (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ∂mu) ∧
      (¬ Integrable
          (fun omega ↦
            ‖gradient
              (hardHyperObjective (finalEta epsilon kappa) kappa U0)
              (output (U0, omega))‖ ^ 2) mu ∨
        9 * epsilon ^ 2 / 4 < ∫ omega,
          ‖gradient
            (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ^ 2 ∂mu) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  rcases hparams with ⟨heta, _hetaSmall, hTfinal, hTlower, hTupper⟩
  have hT : 0 < T := by simpa [hTdef] using hTfinal
  have hTlower' :
      Delta /
          (4 * CDelta * (finalEta epsilon kappa) ^ 2) ≤ (T : ℝ) := by
    simpa [hTdef] using hTlower
  have hTupper' :
      (T : ℝ) ≤
        Delta / (2 * CDelta * (finalEta epsilon kappa) ^ 2) := by
    simpa [hTdef] using hTupper
  have hcalls :
      (N : ℝ) * revealProbability Cvar (finalEta epsilon kappa) sigma /
          T ≤ 1 / 8 :=
    final_call_budget_implies_progress_condition
      hDelta.le hCDelta hCvar hepsilon hkpos hsigma hT hTlower'
        (by simpa [mainComplexityScale] using hN)
  obtain ⟨haarGood, hhaarMeas, hhaarFail, hhaar⟩ :=
    adaptiveHaarConnection
      (μ := nu.prod mu) capInfo capEvent hcap hcapBudget
      (fun z ↦ progress (finalEta epsilon kappa / 4)
        (hiddenFrameTranspose z.1
          (softProjection (hardRadius (finalEta epsilon kappa) T)
            (kappa • output z))))
      (successCountNat success) hnoCapProgress
  let unfinished : Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega) :=
    {z | progress (finalEta epsilon kappa / 4)
      (hiddenFrameTranspose z.1
        (softProjection (hardRadius (finalEta epsilon kappa) T)
          (kappa • output z))) < T}
  have hunfinishedProb : 3 / 4 ≤ (nu.prod mu).real unfinished := by
    apply output_unfinished_probability
      (μ := nu.prod mu) past success hfresh hT haarGood hhaarMeas
        hhaarFail
      (fun z ↦ progress (finalEta epsilon kappa / 4)
        (hiddenFrameTranspose z.1
          (softProjection (hardRadius (finalEta epsilon kappa) T)
            (kappa • output z))))
      hhaar hcalls
  have hunfinishedMeas : MeasurableSet unfinished := by
    simpa [unfinished] using hunfMeas
  obtain ⟨U0, hsection⟩ := exists_fixed_section_of_product_event
    (nu := nu) (mu := mu) hunfinishedMeas hunfinishedProb
  let goodSection : Set Omega :=
    {omega | progress (finalEta epsilon kappa / 4)
      (hiddenFrameTranspose U0
        (softProjection (hardRadius (finalEta epsilon kappa) T)
          (kappa • output (U0, omega)))) < T}
  let loss : Omega → ℝ := fun omega ↦
    ‖gradient
      (hardHyperObjective (finalEta epsilon kappa) kappa U0)
      (output (U0, omega))‖
  have hsectionMeas : MeasurableSet goodSection := by
    exact measurable_prodMk_left hunfinishedMeas
  have hsectionProb : 3 / 4 ≤
      ∫ omega, goodSection.indicator (fun _ ↦ (1 : ℝ)) omega ∂mu := by
    simpa only [unfinished, goodSection, Set.indicator, Set.mem_ofPred_eq]
      using hsection
  have hlossGood : ∀ omega ∈ goodSection, 2 * epsilon < loss omega := by
    intro omega homega
    have hgrad := norm_gradient_hardHyperObjective_gt
      heta hkpos hT U0 (output (U0, omega)) homega
    have hscale := final_amplified_gradient_scale
      (epsilon := epsilon) hkpos.ne'
    dsimp [loss]
    nlinarith
  have hmoments := moment_failure_of_large_event_with_margin
    hepsilon hsectionMeas hsectionProb
    (fun omega ↦ norm_nonneg _) hlossGood
  have hgapRaw := hardHyperObjective_initial_gap_le_chainGapConstant
    (finalEta epsilon kappa) kappa U0
  have hgapConstant :
      chainGapConstant * (finalEta epsilon kappa) ^ 2 * T ≤
        CDelta * (finalEta epsilon kappa) ^ 2 * T := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hchainGap (sq_nonneg _))
      (by positivity)
  have hgapHalf := final_initial_gap_le_half hCDelta heta hTupper'
  have hhalf : Delta / 2 ≤ Delta := by linarith
  refine ⟨U0, ?_, ?_, ?_⟩
  · exact hgapRaw.trans (hgapConstant.trans (hgapHalf.trans hhalf))
  · simpa [loss] using hmoments.1
  · simpa [loss] using hmoments.2

end

end BilevelLowerBound
