/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightAssemblyBridge
import BilevelLowerBoundLean.KappaEightInteraction
import BilevelLowerBoundLean.PaperExpectation

/-!
# Adaptive-Haar boundary and fixed-frame theorem for the amplified hard pair

The analytic, Bernoulli, progress, and expectation calculations of the
`kappa^8` construction are proved in the preceding modules.  The structure
`KappaEightCitedAdaptiveHaarRun` records the sole external mathematical input:
an adaptive random-rotation realization.  It is tied definitionally to the
new two-coordinate lower variable and to the exact recursive interaction in
`KappaEightInteraction`; in particular, its output is not an unrelated random
variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

/-- Ambient finite-dimensional Euclidean space used by the random rotation. -/
abbrev KappaEightEuclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Use the normed-space structure induced by the inner product throughout
the amplified Euclidean specialization.  Declaring this instance explicitly
avoids the otherwise ambiguous diamond between `PiLp.normedSpace` and
`InnerProductSpace.toNormedSpace`. -/
instance (priority := 2000) kappaEightEuclideanNormedSpace (d : ℕ) :
    NormedSpace ℝ (KappaEightEuclidean d) :=
  InnerProductSpace.toNormedSpace

/-- A randomized adaptive algorithm together with its seed space. -/
structure PackedKappaEightAlgorithm (N d : ℕ) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  algorithm : @KappaEightAdaptiveAlgorithm N (KappaEightEuclidean d) Seed
    inferInstance inferInstance inferInstance seedMeasurable

/-- Exact interface supplied by the cited adaptive-Haar lemma for one
algorithm and one frame-indexed amplified hard family.  Every probabilistic
and transcript fact consumed downstream is an explicit field. -/
structure KappaEightCitedAdaptiveHaarRun
    {N d T : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @KappaEightAdaptiveAlgorithm N (KappaEightEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    (P : (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) →
      KappaEightPopulationProblem (KappaEightEuclidean d))
    (O : ∀ U, KappaEightBernoulliSFO (P U))
    (Cvar eta kappa sigma q : ℝ) where
  Omega : Type
  omegaMeasurable : MeasurableSpace Omega
  omegaMeasure : @Measure Omega omegaMeasurable
  omegaProbability : IsProbabilityMeasure omegaMeasure
  frameMeasurable :
    MeasurableSpace (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d)
  frameMeasure :
    @Measure (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) frameMeasurable
  frameProbability : IsProbabilityMeasure frameMeasure
  seed : Omega → Seed
  seed_measurable : @Measurable Omega Seed omegaMeasurable mSeed seed
  seed_law : Measure.map seed omegaMeasure = A.seedMeasure
  bits : Omega → Fin N → Bool
  output :
    (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega →
      KappaEightEuclidean d
  output_eq_run : ∀ U omega,
    output (U, omega) =
      kappaEightRunOutput A (O U) (seed omega) (bits omega)
  output_section_measurable : ∀ U,
    @Measurable Omega (KappaEightEuclidean d) omegaMeasurable inferInstance
      (fun omega ↦ output (U, omega))
  past : Fin N → MeasurableSpace
    ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
  past_eq_actual_run : ∀ t,
    past t =
      kappaEightJointRunPastMeasurableSpace frameMeasurable P A O seed bits t
  success : Fin N → Set
    ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
  success_eq_bit : ∀ t U omega,
    (U, omega) ∈ success t ↔ bits omega t = true
  fresh : ∀ t,
    @FreshBernoulliEvent
      ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
      (frameMeasurable.prod omegaMeasurable)
      (frameMeasure.prod omegaMeasure) (past t) (success t)
      (kappaEightRevealProbability Cvar eta kappa sigma)
  sectionFresh : ∀ U t,
    @FreshBernoulliEvent Omega omegaMeasurable omegaMeasure
      (kappaEightRunPastMeasurableSpace A (O U) seed bits t)
      (kappaEightRunSuccessEvent bits t)
      (kappaEightRevealProbability Cvar eta kappa sigma)
  capInfo : PaddedCapIndex (N + 1) T → MeasurableSpace
    ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
  capEvent : PaddedCapIndex (N + 1) T → Set
    ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
  conditionalCap : ∀ i,
    @ConditionalEventBound
      ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
      (frameMeasurable.prod omegaMeasurable)
      (frameMeasure.prod omegaMeasure) (capInfo i) (capEvent i) q
  capBudget : ((((N + 1) ^ 2 * T : ℕ) : ℝ) * q ≤ 1 / 8)
  residualGeometry :
    @AdaptiveNoCapGeometry (KappaEightEuclidean d)
      ((ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) × Omega)
      inferInstance inferInstance inferInstance
      (frameMeasurable.prod omegaMeasurable) T (N + 1)
      eta (230 * Real.sqrt T)
      (fun z ↦ z.1)
      (fun z ↦ eta⁻¹ •
        softProjection (hardRadius eta T) (kappa • output z))
      (fun z ↦ min T (successCountNat success z)) capEvent

/-- The fully checked fixed-frame consequence of the cited run.  This theorem
uses the amplified reveal probability and therefore the `kappa^8` call scale.
Global boundedness of the hard hyper-gradient removes both non-integrability
alternatives returned by the generic probability assembly. -/
theorem kappaEight_expectation_from_cited_run
    {N d T : ℕ} {Seed : Type} {mSeed : MeasurableSpace Seed}
    (A : @KappaEightAdaptiveAlgorithm N (KappaEightEuclidean d) Seed
      inferInstance inferInstance inferInstance mSeed)
    (P : (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) →
      KappaEightPopulationProblem (KappaEightEuclidean d))
    (O : ∀ U, KappaEightBernoulliSFO (P U))
    {Delta CDelta creg Cvar epsilon kappa sigma q : ℝ}
    (hCDelta : 0 < CDelta) (hchainGap : chainGapConstant ≤ CDelta)
    (hcreg : 0 < creg) (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon) (hsigma : 0 ≤ sigma)
    (hCvar : 0 < Cvar)
    (haccuracy : epsilon ≤ finalAccuracyConstant CDelta creg *
      min 1 (Real.sqrt Delta))
    (hTdef : T = kappaEightFinalChainLength Delta CDelta epsilon kappa)
    (hN : (N : ℝ) ≤ kappaEightLowerBoundConstant CDelta Cvar *
      kappaEightComplexityScale Delta epsilon kappa sigma)
    (H : KappaEightCitedAdaptiveHaarRun A P O Cvar
      (kappaEightFinalEta epsilon kappa) kappa sigma q) :
    ∃ U0 : ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d,
      hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0 0 -
          sInf (Set.range
            (hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0)) ≤
        Delta ∧
      3 * epsilon / 2 < ∫ omega,
        ‖gradient
          (hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0)
          (H.output (U0, omega))‖ ∂H.omegaMeasure ∧
      9 * epsilon ^ 2 / 4 < ∫ omega,
        ‖gradient
          (hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0)
          (H.output (U0, omega))‖ ^ 2 ∂H.omegaMeasure := by
  letI : MeasurableSpace H.Omega := H.omegaMeasurable
  letI : IsProbabilityMeasure H.omegaMeasure := H.omegaProbability
  letI : MeasurableSpace
      (ChainVector T →ₗᵢ[ℝ] KappaEightEuclidean d) := H.frameMeasurable
  letI : IsProbabilityMeasure H.frameMeasure := H.frameProbability
  have hTold : T = finalChainLength Delta CDelta epsilon kappa := by
    calc
      T = kappaEightFinalChainLength Delta CDelta epsilon kappa := hTdef
      _ = finalChainLength Delta CDelta epsilon kappa :=
        kappaEightFinalChainLength_eq_finalChainLength _ _ _ _
  have hT : 0 < T := by
    rw [hTold]
    exact (final_parameters_basic hCDelta hcreg hDelta hkappa
      hepsilon haccuracy).2.2.1
  have hnoCapProgress : ∀ z, (∀ i, z ∉ H.capEvent i) →
      progress (kappaEightFinalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (kappaEightFinalEta epsilon kappa) T)
              (kappa • H.output z))) ≤
        min T (successCountNat H.success z) := by
    intro z hnoCap
    exact noCapProgress_of_residual_geometry
      (frame := fun z ↦ z.1)
      (rawProbe := fun z ↦
        softProjection (hardRadius (kappaEightFinalEta epsilon kappa) T)
          (kappa • H.output z))
      (prefixLength := fun z ↦ min T (successCountNat H.success z))
      (capEvent := H.capEvent)
      H.residualGeometry.eta_pos H.residualGeometry z hnoCap
  have hunfinished : MeasurableSet
      {z | progress (kappaEightFinalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (kappaEightFinalEta epsilon kappa) T)
              (kappa • H.output z))) < T} := by
    apply measurableSet_progress_lt_dim hT
    exact rawAnalysis_measurable_of_residual_geometry
      H.residualGeometry.eta_pos
      (fun z ↦ z.1)
      (fun z ↦ softProjection
        (hardRadius (kappaEightFinalEta epsilon kappa) T)
        (kappa • H.output z))
      (fun z ↦ min T (successCountNat H.success z)) H.capEvent
      H.residualGeometry
  obtain ⟨U0, hgap, hfirst, hsecond⟩ :=
    kappaEight_main_lower_bound_assembly
      (nu := H.frameMeasure) (mu := H.omegaMeasure)
      hCDelta hchainGap hcreg hDelta hkappa hepsilon hsigma hCvar
      haccuracy hTdef hN H.past H.success H.fresh H.output
      H.capInfo H.capEvent H.conditionalCap H.capBudget
      hnoCapProgress hunfinished
  have heta : 0 < kappaEightFinalEta epsilon kappa :=
    kappaEightFinalEta_pos hepsilon (lt_of_lt_of_le (by norm_num) hkappa)
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  obtain ⟨hloss, hlossSq⟩ := hardHyperGradient_moments_integrable
    (mu := H.omegaMeasure) heta hkpos hT U0
      (fun omega ↦ H.output (U0, omega)) (H.output_section_measurable U0)
  have hfirstBound : 3 * epsilon / 2 < ∫ omega,
      ‖gradient
        (hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0)
        (H.output (U0, omega))‖ ∂H.omegaMeasure := by
    rcases hfirst with hnot | hlarge
    · exact False.elim (hnot hloss)
    · exact hlarge
  have hsecondBound : 9 * epsilon ^ 2 / 4 < ∫ omega,
      ‖gradient
        (hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0)
        (H.output (U0, omega))‖ ^ 2 ∂H.omegaMeasure := by
    rcases hsecond with hnot | hlarge
    · exact False.elim (hnot hlossSq)
    · exact hlarge
  exact ⟨U0, hgap, hfirstBound, hsecondBound⟩

end

end BilevelLowerBound
