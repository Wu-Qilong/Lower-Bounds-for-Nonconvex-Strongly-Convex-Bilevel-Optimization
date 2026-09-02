/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperMainTheorem

/-!
# Concrete outer quantifiers for the paper theorem

This file closes the logical packaging left abstract in
`WorstCaseQuantifiers.lean`.  The problem and oracle are the concrete paper
types, their class-membership proofs occur inside the same existential
statement, and the random output is the output of the exact recursive
algorithm--oracle interaction.  The seed has the algorithm's prescribed law
and every Bernoulli bit is fresh relative to the actual pre-query transcript.

The only remaining external input is `CitedAdaptiveHaarPrinciple`, the Lean
interface for the paper's complete adaptive-Haar lifting lemma.  In accordance
with the formalization boundary chosen for this project, that lemma is not
reproved from a Haar measure on the Stiefel manifold.  Its interface exposes
the exact seed law, fresh-sample filtration, padded cap events, residual
geometry, and actual recursive output that every later theorem uses.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

/-- The stationarity-failure certificate for one *fixed deterministic*
population problem and one admissible Bernoulli SFO.  This packages the exact
probability law used in the two expectations in the theorem. -/
structure PaperRunFailure
    {N d : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @PaperAdaptiveAlgorithm N (PaperEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    (P : PaperPopulationProblem (PaperEuclidean d))
    (O : PaperBernoulliSFO P)
    (epsilon kappa Ckappa : ℝ) where
  conditionData : PaperLowerConditionData P
  conditionLower : kappa ≤ conditionData.kappaY
  conditionUpper : conditionData.kappaY ≤ Ckappa * kappa
  Omega : Type
  omegaMeasurable : MeasurableSpace Omega
  omegaMeasure : @Measure Omega omegaMeasurable
  omegaProbability : IsProbabilityMeasure omegaMeasure
  seed : Omega → Seed
  seed_measurable :
    @Measurable Omega Seed omegaMeasurable mSeed seed
  seed_law : Measure.map seed omegaMeasure = A.seedMeasure
  bits : Omega → Fin N → Bool
  fresh : ∀ t,
    @FreshBernoulliEvent Omega omegaMeasurable omegaMeasure
      (paperRunPastMeasurableSpace A O seed bits t)
      (paperRunSuccessEvent bits t) O.probability
  firstMomentFailure :
    epsilon < ∫ omega,
      ‖gradient P.hyperObjective
        (paperRunOutput A O (seed omega) (bits omega))‖ ∂omegaMeasure
  secondMomentFailure :
    epsilon ^ 2 < ∫ omega,
      ‖gradient P.hyperObjective
        (paperRunOutput A O (seed omega) (bits omega))‖ ^ 2 ∂omegaMeasure

/-- The paper's final quantifier order, now specialized to its concrete
algorithm, population-problem, and SFO types.  Expanding the definition gives
`exists d, forall A, exists (f,g), exists O`, followed by both membership
certificates and the two expectation failures. -/
def ConcretePaperLowerBound
    (N T : ℕ) (CH : ℝ)
    (Delta epsilon kappa sigma Lf Lg rho Cf muG Ckappa : ℝ) : Prop :=
  ∃ d : ℕ, requiredHaarDimension CH (N + 1) T ≤ d ∧
    ∀ A : PackedPaperAlgorithm N d,
      ∃ P : PaperPopulationProblem (PaperEuclidean d),
        PaperPopulationClassMember P Lf Lg rho Cf muG Delta ∧
        ∃ O : PaperBernoulliSFO P,
          PaperBernoulliSFOMember O sigma ∧
          Nonempty
            (@PaperRunFailure N d A.Seed A.seedMeasurable A.algorithm
              P O epsilon kappa Ckappa)

/-- The sole external principle: the complete adaptive-Haar lifting lemma in
the exact form required by the paper.  It constructs the proof distribution
and all certificates once the dimension inequality holds.  The contents of
those certificates are exposed by `CitedAdaptiveHaarRun`; no downstream
theorem assumes an additional transcript, freshness, cap, or progress fact.

This principle is intentionally a theorem premise rather than a Lean axiom.
An independent formalization of conditional Haar measure on the Stiefel
manifold could later be used to discharge it without changing the remainder
of the development. -/
def CitedAdaptiveHaarPrinciple (CH : ℝ) : Prop :=
    ∀ {N d T : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @PaperAdaptiveAlgorithm N (PaperEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    {Cvar eta kappa sigma : ℝ}
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hkappa : 0 < kappa)
    (hT : 0 < T)
    (hfrontier : ∀ (U : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d)
      (x : PaperEuclidean d),
      |hardFrontierMap eta (hiddenFrameTranspose U) (kappa • x)| ≤ eta)
    (_hdimension : requiredHaarDimension CH (N + 1) T ≤ d),
    ∃ q : ℝ,
      Nonempty (CitedAdaptiveHaarRun A Cvar eta kappa sigma q
        heta hetaOne hkappa hT hfrontier)

/-- Convert the fixed-frame conclusion of `paper_main_for_one_algorithm`
into the literal `exists problem, exists oracle` form.  It also replaces the
intermediate `eta,T` population bounds by the uniform constants stated in the
paper and records the correct seed law and fixed-frame freshness protocol. -/
theorem paper_failure_for_one_algorithm
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
              exact (paper_final_scale_implies_regularities
                hconstants.1 hconstants.2.1
                (le_trans (by norm_num) hkappa) hp.1.le
                (by simpa [hcregDef] using hp.2.1)).1)
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
    ∃ P : PaperPopulationProblem (PaperEuclidean d),
      PaperPopulationClassMember P
          (Ca + Cell + 1 / 4) (paperUniversalLowerGradientConstant CHess)
          Cthird (paperGapUpperLowerDerivativeConstant Ca CDelta Delta)
          (1 / (2 * kappa)) Delta ∧
      ∃ O : PaperBernoulliSFO P,
        PaperBernoulliSFOMember O sigma ∧
        Nonempty
          (@PaperRunFailure N d Seed mSeed A P O epsilon kappa
            (2 * (2 + CHess))) := by
  have hcreg : 0 < creg := by
    rw [hcregDef]
    exact paperConstructionRegularityScale_pos hconstants.1 hconstants.2.1
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  have hreg := paper_final_scale_implies_regularities
    hconstants.1 hconstants.2.1 (le_trans (by norm_num) hkappa)
    hparams.1.le (by simpa [hcregDef] using hparams.2.1)
  let H := hhaar
  obtain ⟨U0, _hfrontierResult, _hpopResult, _hOResult, _dataResult,
      _hconditionLowerResult, _hconditionUpperResult, hmean, hmeanSq⟩ :=
    paper_main_for_one_algorithm A hDelta hepsilon hkappa hsigma hCDelta
      hCDeltaDef hCvar hconstants hcregDef haccuracy hTdef hN
      hframeCertificate hhaar
  let hfrontier : ∀ x : PaperEuclidean d,
      |hardFrontierMap (finalEta epsilon kappa)
        (hiddenFrameTranspose U0) (kappa • x)| ≤ finalEta epsilon kappa :=
    (hframeCertificate U0).choose
  let P := paperHardPopulationProblem (finalEta epsilon kappa) kappa U0
    hparams.1 hreg.1 (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  let O := paperHardBernoulliSFO Cvar (finalEta epsilon kappa) kappa sigma U0
    hparams.1 hreg.1 (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  obtain ⟨hpopRaw, hO, data, hconditionLower, hconditionUpper⟩ :=
    (hframeCertificate U0).choose_spec
  have hgapHalf :
      CDelta * (finalEta epsilon kappa) ^ 2 * T ≤ Delta / 2 := by
    apply final_initial_gap_le_half hCDelta hparams.1
    simpa [hTdef] using hparams.2.2.2.2
  have hgap :
      CDelta * (finalEta epsilon kappa) ^ 2 * T ≤ Delta :=
    hgapHalf.trans (by linarith)
  have hpop : PaperPopulationClassMember P
      (Ca + Cell + 1 / 4) (paperUniversalLowerGradientConstant CHess)
      Cthird (paperGapUpperLowerDerivativeConstant Ca CDelta Delta)
      (1 / (2 * kappa)) Delta := by
    apply PaperPopulationClassMember.to_final_uniform_bounds
      hCDelta hparams.1.le hreg.1 hDelta.le hconstants.2.2.2.1
        hconstants.2.1 hgap
    simpa [P] using hpopRaw
  refine ⟨P, hpop, O, ?_, ⟨?_⟩⟩
  · simpa [O, P] using hO
  · refine
      { conditionData := by simpa [P] using data
        conditionLower := by simpa [P] using hconditionLower
        conditionUpper := by simpa [P] using hconditionUpper
        Omega := H.Omega
        omegaMeasurable := H.omegaMeasurable
        omegaMeasure := H.omegaMeasure
        omegaProbability := H.omegaProbability
        seed := H.seed
        seed_measurable := H.seed_measurable
        seed_law := H.seed_law
        bits := H.bits
        fresh := by
          intro t
          change @FreshBernoulliEvent H.Omega H.omegaMeasurable H.omegaMeasure
            (paperRunPastMeasurableSpace A O H.seed H.bits t)
            (paperRunSuccessEvent H.bits t) O.probability
          convert H.sectionFresh U0 t using 1
          rfl
        firstMomentFailure := by
          simpa [O, P, hfrontier] using hmean
        secondMomentFailure := by
          simpa [O, P, hfrontier] using hmeanSq }

/-- The concrete main theorem with the same quantifier order and fixed
population-class constants as the LaTeX statement.  The only external premise
is the explicitly named adaptive-Haar lifting principle above. -/
theorem concrete_paper_main_theorem
    (CH : ℝ) (hHaar : CitedAdaptiveHaarPrinciple CH) :
    ∃ cLB cEpsilon Lf Lg rho Ckappa : ℝ,
      0 < cLB ∧ 0 < cEpsilon ∧ 0 < Lf ∧ 0 < Lg ∧
      0 < rho ∧ 0 < Ckappa ∧
      ∀ Delta : ℝ, 0 < Delta →
        ∃ Cf : ℝ, 0 < Cf ∧
          ∀ (kappa sigma epsilon : ℝ) (N : ℕ),
            2 ≤ kappa → 0 ≤ sigma → 0 < epsilon →
            epsilon ≤ cEpsilon * min 1 (Real.sqrt Delta) →
            (N : ℝ) ≤ cLB *
              mainComplexityScale Delta epsilon kappa sigma →
            ConcretePaperLowerBound N
              (finalChainLength Delta populationChainGapConstant
                epsilon kappa)
              CH Delta epsilon kappa sigma Lf Lg rho Cf
              (1 / (2 * kappa)) Ckappa := by
  obtain ⟨Ctheta, CHess, Cthird, Ca, Cell, Cvar,
      hCtheta, hCHess, hCthird, hCa, hCell, hCvar, hcert⟩ :=
    exists_simultaneous_paper_hard_certificates
  let CDelta := populationChainGapConstant
  let creg := paperConstructionRegularityScale Ctheta CHess
  let cLB := finalLowerBoundConstant CDelta Cvar
  let cEpsilon := finalAccuracyConstant CDelta creg
  let Lf := Ca + Cell + 1 / 4
  let Lg := paperUniversalLowerGradientConstant CHess
  let rho := Cthird + 1
  let Ckappa := 2 * (2 + CHess)
  have hCDelta : 0 < CDelta := by
    simpa [CDelta, populationChainGapConstant, chainGapConstant] using
      chainGapConstant_pos
  have hcreg : 0 < creg := by
    exact paperConstructionRegularityScale_pos hCtheta hCHess
  have hcLB : 0 < cLB := by
    unfold cLB finalLowerBoundConstant
    positivity
  have hcEpsilon : 0 < cEpsilon :=
    finalAccuracyConstant_pos hCDelta hcreg
  have hLf : 0 < Lf := by
    dsimp [Lf]
    positivity
  have hLg : 0 < Lg := by
    dsimp [Lg, paperUniversalLowerGradientConstant]
    linarith
  have hrho : 0 < rho := by
    dsimp [rho]
    linarith
  have hCkappa : 0 < Ckappa := by
    dsimp [Ckappa]
    positivity
  refine ⟨cLB, cEpsilon, Lf, Lg, rho, Ckappa, hcLB, hcEpsilon,
    hLf, hLg, hrho, hCkappa, ?_⟩
  intro Delta hDelta
  let Cf := paperGapUpperLowerDerivativeConstant Ca CDelta Delta
  have hCf : 0 < Cf := by
    dsimp [Cf, paperGapUpperLowerDerivativeConstant]
    have hsqrt : 0 ≤ Real.sqrt (Delta / CDelta) := Real.sqrt_nonneg _
    have hcoef : 0 ≤ Ca + 230 / 4 := by positivity
    nlinarith [mul_nonneg hcoef hsqrt]
  refine ⟨Cf, hCf, ?_⟩
  intro kappa sigma epsilon N hkappa hsigma hepsilon haccuracy hN
  let T := finalChainLength Delta CDelta epsilon kappa
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  have hreg := paper_final_scale_implies_regularities hCtheta hCHess
    (le_trans (by norm_num) hkappa) hparams.1.le hparams.2.1
  have hT : 0 < T := hparams.2.2.1
  have hgapHalf : CDelta * (finalEta epsilon kappa) ^ 2 * T ≤
      Delta / 2 :=
    final_initial_gap_le_half hCDelta hparams.1 hparams.2.2.2.2
  have hgap : populationChainGapConstant *
      (finalEta epsilon kappa) ^ 2 * T ≤ Delta := by
    change CDelta * (finalEta epsilon kappa) ^ 2 * T ≤ Delta
    exact hgapHalf.trans (by linarith)
  obtain ⟨d, hdimension⟩ := exists_dimension_choice CH (N + 1) T
  unfold ConcretePaperLowerBound
  refine ⟨d, hdimension, ?_⟩
  intro packedA
  let A := packedA.algorithm
  have hframeCertificate :
      ∀ (U : ChainVector T →ₗᵢ[ℝ] PaperEuclidean d),
        ∃ hfrontier : ∀ x : PaperEuclidean d,
            |hardFrontierMap (finalEta epsilon kappa)
              (hiddenFrameTranspose U) (kappa • x)| ≤ finalEta epsilon kappa,
          let P := paperHardPopulationProblem (finalEta epsilon kappa) kappa U
            hparams.1 hreg.1 (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
          let O := paperHardBernoulliSFO Cvar (finalEta epsilon kappa)
            kappa sigma U hparams.1 hreg.1
            (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
          PaperPopulationClassMember P
              (Ca + Cell + 1 / 4)
              (5 + CHess * finalEta epsilon kappa) Cthird
              (Ca * finalEta epsilon kappa * Real.sqrt T + 1 +
                (1 / 4) * hardRadius (finalEta epsilon kappa) T)
              (1 / (2 * kappa)) Delta ∧
            PaperBernoulliSFOMember O sigma ∧
            ∃ data : PaperLowerConditionData P,
              kappa ≤ data.kappaY ∧
                data.kappaY ≤ 2 * (2 + CHess) * kappa := by
    intro U
    exact hcert hparams.1 hreg.1 (le_trans (by norm_num) hkappa) hT
      hsigma hreg.2.1 hreg.2.2 hgap U
  unfold CitedAdaptiveHaarPrinciple at hHaar
  obtain ⟨q, ⟨hrun⟩⟩ :=
    @hHaar N d T packedA.Seed packedA.seedMeasurable A
      Cvar (finalEta epsilon kappa) kappa sigma
      hparams.1 hreg.1 (lt_of_lt_of_le (by norm_num) hkappa) hT
      (fun U x ↦ (hframeCertificate U).choose x) hdimension
  obtain ⟨P, hpop, O, hO, hfailure⟩ :=
    paper_failure_for_one_algorithm A hDelta hepsilon hkappa hsigma
      hCDelta (by rfl) hCvar
      ⟨hCtheta, hCHess, hCthird, hCa, hCell⟩ (by rfl)
      haccuracy (by rfl) hN hframeCertificate hrun
  have hpopFinal : PaperPopulationClassMember P Lf Lg rho Cf
      (1 / (2 * kappa)) Delta := by
    apply hpop.mono le_rfl le_rfl _ le_rfl le_rfl le_rfl
    dsimp [rho]
    linarith
  exact ⟨P, hpopFinal, O, hO, by simpa [Ckappa] using hfailure⟩

end

end BilevelLowerBound
