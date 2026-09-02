/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperInteraction

/-!
# Paper-level main theorem and its sole cited Haar boundary

`CitedAdaptiveHaarRun` is the explicit boundary of the formalization.  Its
conditional cap estimates and residual certificates are supplied by the
adaptive random-rotation lemma cited in the paper.  Crucially, its `output`
is required to be the output of the concrete recursive interaction from
`PaperInteraction.lean`; it is not an unrelated random variable.

All deductions from this interface--finite padding, union bound, Bernoulli
success count, fixed-frame selection, population and oracle membership,
condition-number comparison, integrability, and expectation lower bounds--
are checked by Lean.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

/-! ## Monotonicity and slice identification -/

/-- Membership is preserved when upper bounds are enlarged, the certified
strong-convexity modulus is decreased, and the gap allowance is enlarged. -/
theorem PaperPopulationClassMember.mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : PaperPopulationProblem E}
    {Lf Lg rho Cf muG Delta Lf' Lg' rho' Cf' muG' Delta' : ℝ}
    (h : PaperPopulationClassMember P Lf Lg rho Cf muG Delta)
    (hLf : Lf ≤ Lf') (hLg : Lg ≤ Lg') (hrho : rho ≤ rho')
    (hCf : Cf ≤ Cf') (hmuG : muG' ≤ muG) (hDelta : Delta ≤ Delta') :
    PaperPopulationClassMember P Lf' Lg' rho' Cf' muG' Delta' := by
  refine
    { upper_gradient_lipschitz := ⟨h.upper_gradient_lipschitz.1, ?_⟩
      lower_gradient_lipschitz := ⟨h.lower_gradient_lipschitz.1, ?_⟩
      lower_strongly_convex := ?_
      lower_hessian_lipschitz := ⟨h.lower_hessian_lipschitz.1, ?_⟩
      upper_lower_derivative_bounded := ?_
      hyper_bddBelow := h.hyper_bddBelow
      initial_gap := h.initial_gap.trans hDelta }
  · intro x y
    exact h.upper_gradient_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hLf (norm_nonneg _))
  · intro x y
    exact h.lower_gradient_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hLg (norm_nonneg _))
  · intro x y w
    exact (mul_le_mul_of_nonneg_right hmuG (sq_nonneg ‖w‖)).trans
      (h.lower_strongly_convex x y w)
  · intro x y
    exact h.lower_hessian_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hrho (norm_nonneg _))
  · intro x y
    exact (h.upper_lower_derivative_bounded x y).trans hCf

/-- A universal lower-gradient Lipschitz constant used in the final theorem. -/
def paperUniversalLowerGradientConstant (CHess : ℝ) : ℝ :=
  5 + CHess

/-- The only final population-class constant allowed to depend on the initial
gap.  It bounds the paper's `C_a eta sqrt(T)` term and the pseudo-Huber
radius term using `C_Delta eta^2 T <= Delta`. -/
def paperGapUpperLowerDerivativeConstant
    (Ca CDelta Delta : ℝ) : ℝ :=
  1 + (Ca + 230 / 4) * Real.sqrt (Delta / CDelta)

/-- Replace the construction-dependent `eta,T` bounds by the fixed constants
appearing in the statement of the paper's theorem. -/
theorem PaperPopulationClassMember.to_final_uniform_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : PaperPopulationProblem E} {T : ℕ}
    {eta Delta CDelta Ca Cell CHess Cthird muG : ℝ}
    (hCDelta : 0 < CDelta) (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hDelta : 0 ≤ Delta) (hCa : 0 ≤ Ca) (hCHess : 0 ≤ CHess)
    (hgap : CDelta * eta ^ 2 * T ≤ Delta)
    (h : PaperPopulationClassMember P
      (Ca + Cell + 1 / 4) (5 + CHess * eta) Cthird
      (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
      muG Delta) :
    PaperPopulationClassMember P
      (Ca + Cell + 1 / 4) (paperUniversalLowerGradientConstant CHess)
      Cthird (paperGapUpperLowerDerivativeConstant Ca CDelta Delta)
      muG Delta := by
  have hscale : eta * Real.sqrt T ≤ Real.sqrt (Delta / CDelta) :=
    eta_mul_sqrt_le_sqrt_div_of_gap hCDelta heta hDelta hgap
  have hLg : 5 + CHess * eta ≤ paperUniversalLowerGradientConstant CHess := by
    unfold paperUniversalLowerGradientConstant
    nlinarith
  have hcoef : 0 ≤ Ca + 230 / 4 := by positivity
  have hCfScale := mul_le_mul_of_nonneg_left hscale hcoef
  have hCf :
      Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T ≤
        paperGapUpperLowerDerivativeConstant Ca CDelta Delta := by
    unfold hardRadius paperGapUpperLowerDerivativeConstant
    nlinarith
  exact h.mono le_rfl hLg le_rfl hCf le_rfl le_rfl

/-- Freezing the upper variable in the concrete full lower objective gives
exactly the lower slice used in the sharp-condition-number proof. -/
theorem paperHardPopulationProblem_lower_slice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {eta kappa : ℝ}
    (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hkappa : 0 < kappa)
    (hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta) :
    (fun x y ↦
      (paperHardPopulationProblem eta kappa J heta hetaOne hkappa hfrontier).lower
        (x, y)) =
      hardLowerSlice kappa eta (hiddenFrameTranspose J) := by
  funext x y
  rfl

/-! ## Simultaneous concrete certification -/

set_option maxHeartbeats 1600000 in
-- Several independent universal analytic certificates are combined here.
/-- One common set of universal constants certifies the population pair, its
actual sharp condition number, and its fresh Bernoulli SFO. -/
theorem exists_simultaneous_paper_hard_certificates :
    ∃ Ctheta CHess Cthird Ca Cell Cvar : ℝ,
      0 ≤ Ctheta ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      0 ≤ Ca ∧ 0 ≤ Cell ∧ 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa Delta sigma : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 1 ≤ kappa) → (hT : 0 < T) →
        (hsigma : 0 ≤ sigma) → (hthetaSmall : Ctheta * eta ≤ 1) →
        (hHessSmall : CHess * eta ≤ 1 / (2 * kappa)) →
        (hgap : populationChainGapConstant * eta ^ 2 * T ≤ Delta) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ hfrontier : ∀ x : E,
            |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta,
          let P := paperHardPopulationProblem eta kappa J
            (by assumption) (by assumption)
            (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hkappa) hfrontier
          let O := paperHardBernoulliSFO Cvar eta kappa sigma J
            (by assumption) (by assumption)
            (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hkappa) hfrontier
          PaperPopulationClassMember P
              (Ca + Cell + 1 / 4) (5 + CHess * eta) Cthird
              (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
              (1 / (2 * kappa)) Delta ∧
            PaperBernoulliSFOMember O sigma ∧
            ∃ data : PaperLowerConditionData P,
              kappa ≤ data.kappaY ∧
                data.kappaY ≤ 2 * (2 + CHess) * kappa := by
  obtain ⟨CthetaP, CHessP, Cthird, Ca, Cell,
    hCthetaP, hCHessP, hCthird, hCa, hCell, hpopulation⟩ :=
      exists_paperHardPopulationClassMember
  obtain ⟨CthetaK, CHessK, hCthetaK, hCHessK, hcondition⟩ :=
    exists_orthonormalFrame_sharp_lower_constants
  obtain ⟨Cvar, hCvar, horacle⟩ :=
    exists_paperHardBernoulliSFOMember
  let Ctheta := max CthetaP CthetaK
  let CHess := max CHessP CHessK
  refine ⟨Ctheta, CHess, Cthird, Ca, Cell, Cvar,
    hCthetaP.trans (le_max_left _ _),
    hCHessP.trans (le_max_left _ _), hCthird, hCa, hCell, hCvar, ?_⟩
  intro E _ _ _ T eta kappa Delta sigma heta hetaOne hkappa hT
    hsigma hthetaSmall hHessSmall hgap J
  have hthetaP : CthetaP * eta ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right (le_max_left CthetaP CthetaK)
      heta.le).trans hthetaSmall
  have hthetaK : CthetaK * eta ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right (le_max_right CthetaP CthetaK)
      heta.le).trans hthetaSmall
  have hHessP : CHessP * eta ≤ 1 / (2 * kappa) := by
    exact (mul_le_mul_of_nonneg_right (le_max_left CHessP CHessK)
      heta.le).trans hHessSmall
  have hHessK : CHessK * eta ≤ 1 / (2 * kappa) := by
    exact (mul_le_mul_of_nonneg_right (le_max_right CHessP CHessK)
      heta.le).trans hHessSmall
  obtain ⟨hfrontier, hpopRaw⟩ :=
    hpopulation heta hetaOne hkappa hT hthetaP hHessP hgap J
  obtain ⟨_hfrontierK, muGAct, Ly, hmuGActPos, hmuGAct, hLy,
      hkLower, hkUpperRaw⟩ :=
    hcondition hkappa heta hetaOne hT J hthetaK hHessK
  let P := paperHardPopulationProblem eta kappa J heta hetaOne
    (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  have hslice := paperHardPopulationProblem_lower_slice J heta hetaOne
    (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  have hmuGActP : IsSharpLowerHessianModulus
      (fun x y ↦ P.lower (x, y)) muGAct := by
    rw [hslice]
    exact hmuGAct
  have hLyP : IsSharpLowerHessianUpperBound (fun x y ↦ P.lower (x, y)) Ly := by
    rw [hslice]
    exact hLy
  let data : PaperLowerConditionData P :=
    { muGAct := muGAct
      Ly := Ly
      muGAct_pos := hmuGActPos
      muGAct_sharp := hmuGActP
      Ly_sharp := hLyP }
  have hpop : PaperPopulationClassMember P
      (Ca + Cell + 1 / 4) (5 + CHess * eta) Cthird
      (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
      (1 / (2 * kappa)) Delta := by
    apply hpopRaw.mono le_rfl _ le_rfl le_rfl le_rfl le_rfl
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_right (le_max_left CHessP CHessK) heta.le) 5
  let O := paperHardBernoulliSFO Cvar eta kappa sigma J heta hetaOne
    (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  have hO : PaperBernoulliSFOMember O sigma :=
    (horacle heta hetaOne (lt_of_lt_of_le (by norm_num) hkappa)
      hT hsigma J hfrontier).1
  have hkUpper : Ly / muGAct ≤ 2 * (2 + CHess) * kappa := by
    calc
      Ly / muGAct ≤ 2 * (2 + CHessK) * kappa := hkUpperRaw
      _ ≤ 2 * (2 + CHess) * kappa := by
        gcongr
        exact le_max_right CHessP CHessK
  exact ⟨hfrontier, hpop, hO, data,
    by simpa [PaperLowerConditionData.kappaY, data] using hkLower,
    by simpa [PaperLowerConditionData.kappaY, data] using hkUpper⟩

/-- The ambient Euclidean space in dimension `d`. -/
abbrev PaperEuclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A randomized adaptive algorithm with its seed type and measurable
structure packaged existentially. -/
structure PackedPaperAlgorithm (N d : ℕ) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  algorithm : @PaperAdaptiveAlgorithm N (PaperEuclidean d) Seed
    inferInstance inferInstance inferInstance seedMeasurable

/-- The exact output interface of the paper's adaptive-Haar lifting lemma for
one concrete algorithm.  The current project treats construction of this
entire interface from Haar measure as its declared external boundary.  Every
field used after that boundary is nevertheless stated explicitly here. -/
structure CitedAdaptiveHaarRun
    {N d T : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @PaperAdaptiveAlgorithm N (PaperEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    (Cvar eta kappa sigma q : ℝ)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hkappa : 0 < kappa)
    (hT : 0 < T)
    (hfrontier : ∀ (U : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d)
      (x : PaperEuclidean d),
      |hardFrontierMap eta (hiddenFrameTranspose U) (kappa • x)| ≤ eta) where
  Omega : Type
  omegaMeasurable : MeasurableSpace Omega
  omegaMeasure : @Measure Omega omegaMeasurable
  omegaProbability : IsProbabilityMeasure omegaMeasure
  frameMeasurable :
    MeasurableSpace (ChainVector T →ₗᵢ[ℝ] PaperEuclidean d)
  frameMeasure :
    @Measure (ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) frameMeasurable
  frameProbability : IsProbabilityMeasure frameMeasure
  seed : Omega → Seed
  seed_measurable :
    @Measurable Omega Seed omegaMeasurable mSeed seed
  seed_law :
    Measure.map seed omegaMeasure = A.seedMeasure
  bits : Omega → Fin N → Bool
  output :
    (ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega →
      PaperEuclidean d
  output_eq_run : ∀ U omega,
    output (U, omega) =
      paperRunOutput A
        (paperHardBernoulliSFO Cvar eta kappa sigma U
          heta hetaOne hkappa (hfrontier U))
        (seed omega) (bits omega)
  output_section_measurable : ∀ U,
    @Measurable Omega (PaperEuclidean d) omegaMeasurable inferInstance
      (fun omega ↦ output (U, omega))
  past : Fin N → MeasurableSpace
    ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
  past_eq_actual_run : ∀ t,
    past t =
      paperJointRunPastMeasurableSpace frameMeasurable
        (fun U ↦ paperHardPopulationProblem eta kappa U
          heta hetaOne hkappa (hfrontier U)) A
        (fun U ↦ paperHardBernoulliSFO Cvar eta kappa sigma U
          heta hetaOne hkappa (hfrontier U))
        seed bits t
  success : Fin N → Set
    ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
  success_eq_bit : ∀ t U omega,
    (U, omega) ∈ success t ↔ bits omega t = true
  fresh : ∀ t,
    @FreshBernoulliEvent
      ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
      (frameMeasurable.prod omegaMeasurable)
      (frameMeasure.prod omegaMeasure) (past t) (success t)
      (revealProbability Cvar eta sigma)
  sectionFresh : ∀ U t,
    @FreshBernoulliEvent Omega omegaMeasurable omegaMeasure
      (paperRunPastMeasurableSpace A
        (paperHardBernoulliSFO Cvar eta kappa sigma U
          heta hetaOne hkappa (hfrontier U))
        seed bits t)
      (paperRunSuccessEvent bits t)
      (revealProbability Cvar eta sigma)
  capInfo : PaddedCapIndex (N + 1) T → MeasurableSpace
    ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
  capEvent : PaddedCapIndex (N + 1) T → Set
    ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
  conditionalCap : ∀ i,
    @ConditionalEventBound
      ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
      (frameMeasurable.prod omegaMeasurable)
      (frameMeasure.prod omegaMeasure) (capInfo i) (capEvent i) q
  capBudget : ((((N + 1) ^ 2 * T : ℕ) : ℝ) * q ≤ 1 / 8)
  residualGeometry :
    @AdaptiveNoCapGeometry (PaperEuclidean d)
      ((ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) × Omega)
      inferInstance inferInstance inferInstance
      (frameMeasurable.prod omegaMeasurable) T (N + 1)
      eta (230 * Real.sqrt T)
      (fun z ↦ z.1)
      (fun z ↦ eta⁻¹ •
        softProjection (hardRadius eta T) (kappa • output z))
      (fun z ↦ min T (successCountNat success z)) capEvent

/-- One-algorithm paper theorem.  The only hypothesis not proved in this
repository is the explicitly named adaptive-Haar realization. -/
theorem paper_main_for_one_algorithm
    {N d T : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @PaperAdaptiveAlgorithm N (PaperEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    {Delta epsilon kappa sigma CDelta Cvar Ctheta CHess
      Cthird Ca Cell creg q : ℝ}
    (hDelta : 0 < Delta) (hepsilon : 0 < epsilon) (hkappa : 2 ≤ kappa)
    (hsigma : 0 ≤ sigma) (hCDelta : 0 < CDelta)
    (hCDeltaDef : CDelta = populationChainGapConstant)
    (hCvar : 0 < Cvar)
    (hconstants : 0 ≤ Ctheta ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      0 ≤ Ca ∧ 0 ≤ Cell)
    (hcregDef : creg = paperConstructionRegularityScale Ctheta CHess)
    (haccuracy : epsilon ≤ finalAccuracyConstant CDelta creg *
      min 1 (Real.sqrt Delta))
    (hTdef : T = finalChainLength Delta CDelta epsilon kappa)
    (hN : (N : ℝ) ≤ finalLowerBoundConstant CDelta Cvar *
      mainComplexityScale Delta epsilon kappa sigma)
    (hframeCertificate : ∀ (U : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d),
      ∃ hfrontier : ∀ x : PaperEuclidean d,
          |hardFrontierMap (finalEta epsilon kappa)
            (hiddenFrameTranspose U) (kappa • x)| ≤ finalEta epsilon kappa,
        let P := paperHardPopulationProblem (finalEta epsilon kappa) kappa U
            (by
              have hp := final_parameters_basic hCDelta
                (hcregDef ▸ paperConstructionRegularityScale_pos
                  hconstants.1 hconstants.2.1)
                hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
              exact hp.1)
            (by
              have hp := final_parameters_basic hCDelta
                (hcregDef ▸ paperConstructionRegularityScale_pos
                  hconstants.1 hconstants.2.1)
                hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
              have hr := paper_final_scale_implies_regularities
                hconstants.1 hconstants.2.1
                (le_trans (by norm_num) hkappa) hp.1.le
                (by simpa [hcregDef] using hp.2.1)
              exact hr.1)
            (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
        let O := paperHardBernoulliSFO Cvar (finalEta epsilon kappa) kappa sigma U
          (by
            have hp := final_parameters_basic hCDelta
              (hcregDef ▸ paperConstructionRegularityScale_pos
                hconstants.1 hconstants.2.1)
              hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
            exact hp.1)
          (by
            have hp := final_parameters_basic hCDelta
              (hcregDef ▸ paperConstructionRegularityScale_pos
                hconstants.1 hconstants.2.1)
              hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
            exact (paper_final_scale_implies_regularities
              hconstants.1 hconstants.2.1
              (le_trans (by norm_num) hkappa) hp.1.le
              (by simpa [hcregDef] using hp.2.1)).1)
          (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
        PaperPopulationClassMember P
            (Ca + Cell + 1 / 4) (5 + CHess * finalEta epsilon kappa)
            Cthird
            (Ca * finalEta epsilon kappa * Real.sqrt T + 1 +
              (1 / 4) * hardRadius (finalEta epsilon kappa) T)
            (1 / (2 * kappa)) Delta ∧
          PaperBernoulliSFOMember O sigma ∧
          ∃ data : PaperLowerConditionData P,
            kappa ≤ data.kappaY ∧
              data.kappaY ≤ 2 * (2 + CHess) * kappa)
    (hhaar :
      let eta := finalEta epsilon kappa
      let hparams := final_parameters_basic hCDelta
        (hcregDef ▸ paperConstructionRegularityScale_pos
          hconstants.1 hconstants.2.1)
        hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
      let hreg := paper_final_scale_implies_regularities
        hconstants.1 hconstants.2.1
        (le_trans (by norm_num) hkappa) hparams.1.le
        (by simpa [hcregDef] using hparams.2.1)
      let hfrontier : ∀ (U : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d)
          (x : PaperEuclidean d),
          |hardFrontierMap eta (hiddenFrameTranspose U) (kappa • x)| ≤ eta :=
        fun U x ↦ (hframeCertificate U).choose x
      CitedAdaptiveHaarRun A Cvar eta kappa sigma q
        hparams.1 hreg.1 (lt_of_lt_of_le (by norm_num) hkappa)
        (by simpa [hTdef] using hparams.2.2.1) hfrontier) :
    ∃ (U0 : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d)
      (hfrontier : ∀ x : PaperEuclidean d,
        |hardFrontierMap (finalEta epsilon kappa)
          (hiddenFrameTranspose U0) (kappa • x)| ≤ finalEta epsilon kappa),
      let P := paperHardPopulationProblem (finalEta epsilon kappa) kappa U0
        (by
          have hp := final_parameters_basic hCDelta
            (hcregDef ▸ paperConstructionRegularityScale_pos
              hconstants.1 hconstants.2.1)
            hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
          exact hp.1)
        (by
          have hp := final_parameters_basic hCDelta
            (hcregDef ▸ paperConstructionRegularityScale_pos
              hconstants.1 hconstants.2.1)
            hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
          exact (paper_final_scale_implies_regularities
            hconstants.1 hconstants.2.1
            (le_trans (by norm_num) hkappa) hp.1.le
            (by simpa [hcregDef] using hp.2.1)).1)
        (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
      let O := paperHardBernoulliSFO Cvar (finalEta epsilon kappa) kappa sigma
        U0
        (by
          have hp := final_parameters_basic hCDelta
            (hcregDef ▸ paperConstructionRegularityScale_pos
              hconstants.1 hconstants.2.1)
            hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
          exact hp.1)
        (by
          have hp := final_parameters_basic hCDelta
            (hcregDef ▸ paperConstructionRegularityScale_pos
              hconstants.1 hconstants.2.1)
            hDelta hkappa hepsilon (by simpa [hcregDef] using haccuracy)
          exact (paper_final_scale_implies_regularities
            hconstants.1 hconstants.2.1
            (le_trans (by norm_num) hkappa) hp.1.le
            (by simpa [hcregDef] using hp.2.1)).1)
        (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
      PaperPopulationClassMember P
          (Ca + Cell + 1 / 4) (5 + CHess * finalEta epsilon kappa)
          Cthird
          (Ca * finalEta epsilon kappa * Real.sqrt T + 1 +
            (1 / 4) * hardRadius (finalEta epsilon kappa) T)
          (1 / (2 * kappa)) Delta ∧
        PaperBernoulliSFOMember O sigma ∧
        ∃ data : PaperLowerConditionData P,
          kappa ≤ data.kappaY ∧
          data.kappaY ≤ 2 * (2 + CHess) * kappa ∧
          epsilon < ∫ omega,
            ‖gradient P.hyperObjective
              (paperRunOutput A O (hhaar.seed omega) (hhaar.bits omega))‖
              ∂hhaar.omegaMeasure ∧
          epsilon ^ 2 < ∫ omega,
            ‖gradient P.hyperObjective
              (paperRunOutput A O (hhaar.seed omega) (hhaar.bits omega))‖ ^ 2
              ∂hhaar.omegaMeasure := by
  have hcreg : 0 < creg := by
    rw [hcregDef]
    exact paperConstructionRegularityScale_pos hconstants.1 hconstants.2.1
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  have hreg := paper_final_scale_implies_regularities
    hconstants.1 hconstants.2.1 (le_trans (by norm_num) hkappa)
    hparams.1.le (by simpa [hcregDef] using hparams.2.1)
  let H := hhaar
  letI : MeasurableSpace H.Omega := H.omegaMeasurable
  letI : IsProbabilityMeasure H.omegaMeasure := H.omegaProbability
  letI : MeasurableSpace
      (ChainVector T →ₗᵢ[ℝ] PaperEuclidean d) := H.frameMeasurable
  letI : IsProbabilityMeasure H.frameMeasure := H.frameProbability
  obtain ⟨U0, hgap, hmean, hmeanSq⟩ :=
    main_lower_bound_expectation_from_residual_geometry
      hCDelta (by simpa [hCDeltaDef, populationChainGapConstant,
        chainGapConstant]) hcreg hDelta hkappa hepsilon hsigma hCvar
      haccuracy hTdef hN H.past H.success H.fresh H.output
      H.output_section_measurable H.capInfo H.capEvent H.conditionalCap
      H.capBudget H.residualGeometry
  obtain ⟨hfrontier, hpop, hO, data, hcondLower, hcondUpper⟩ :=
    hframeCertificate U0
  refine ⟨U0, hfrontier, hpop, hO, data, hcondLower, hcondUpper, ?_, ?_⟩
  · simpa [paperHardPopulationProblem, H.output_eq_run U0,
      PaperPopulationProblem.hyperObjective_eq] using hmean
  · simpa [paperHardPopulationProblem, H.output_eq_run U0,
      PaperPopulationProblem.hyperObjective_eq] using hmeanSq

end

end BilevelLowerBound
