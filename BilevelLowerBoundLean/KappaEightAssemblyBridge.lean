/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightParameterSelection
import BilevelLowerBoundLean.MainTheorem

/-!
# Bridge to the generic one-frontier probability assembly

The adaptive-Haar, fresh-Bernoulli, Markov, fixed-frame, and gap-gradient
assembly is independent of how the reveal probability was generated.  This
file proves that the new attenuated probability is exactly the generic
probability with effective noise scale `sigma * kappa`.  Consequently the
already checked generic assembly specializes *definitionally* to the new
`kappa^8` scale; no old scalar hard instance is used in this reduction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

theorem kappaEightFinalEta_eq_finalEta (epsilon kappa : ℝ) :
    kappaEightFinalEta epsilon kappa = finalEta epsilon kappa := by
  rfl

theorem kappaEightFinalChainScale_eq_finalChainScale
    (Delta CDelta epsilon kappa : ℝ) :
    kappaEightFinalChainScale Delta CDelta epsilon kappa =
      finalChainScale Delta CDelta epsilon kappa := by
  rfl

theorem kappaEightFinalChainLength_eq_finalChainLength
    (Delta CDelta epsilon kappa : ℝ) :
    kappaEightFinalChainLength Delta CDelta epsilon kappa =
      finalChainLength Delta CDelta epsilon kappa := by
  rfl

theorem kappaEightLowerBoundConstant_eq_finalLowerBoundConstant
    (CDelta Cvar : ℝ) :
    kappaEightLowerBoundConstant CDelta Cvar =
      finalLowerBoundConstant CDelta Cvar := by
  rfl

/-- The new reveal probability is the generic one at effective noise
`sigma * kappa`. -/
theorem kappaEightRevealProbability_eq_revealProbability_mul
    {Cvar eta kappa sigma : ℝ} (hkappa : kappa ≠ 0) :
    kappaEightRevealProbability Cvar eta kappa sigma =
      revealProbability Cvar eta (sigma * kappa) := by
  unfold kappaEightRevealProbability revealProbability
  by_cases hsigma : sigma = 0
  · simp [hsigma]
  · have hprod : sigma * kappa ≠ 0 := mul_ne_zero hsigma hkappa
    rw [if_neg hsigma, if_neg hprod]
    congr 2
    field_simp [hkappa]

/-- The old generic scalar expression at effective noise `sigma*kappa` is
exactly the new `kappa^8` expression. -/
theorem mainComplexityScale_mul_eq_kappaEightComplexityScale
    (Delta epsilon kappa sigma : ℝ) :
    mainComplexityScale Delta epsilon kappa (sigma * kappa) =
      kappaEightComplexityScale Delta epsilon kappa sigma := by
  unfold mainComplexityScale kappaEightComplexityScale
  congr 2
  congr 1
  ring

/-- Specialization of the fully checked one-frontier probability assembly to
the two-dimensional amplifier reveal probability and complexity scale. -/
theorem kappaEight_main_lower_bound_assembly
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
    (haccuracy : epsilon ≤ finalAccuracyConstant CDelta creg *
      min 1 (Real.sqrt Delta))
    (hTdef : T = kappaEightFinalChainLength Delta CDelta epsilon kappa)
    (hN : (N : ℝ) ≤
      kappaEightLowerBoundConstant CDelta Cvar *
        kappaEightComplexityScale Delta epsilon kappa sigma)
    (past : Fin N → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (success : Fin N → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hfresh : ∀ t,
      FreshBernoulliEvent
        (mFrame.prod mOmega) (nu.prod mu) (past t) (success t)
        (kappaEightRevealProbability Cvar
          (kappaEightFinalEta epsilon kappa) kappa sigma))
    (output : (ChainVector T →ₗᵢ[ℝ] E) × Omega → E)
    (capInfo : PaddedCapIndex (N + 1) T → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (capEvent : PaddedCapIndex (N + 1) T → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hcap : ∀ i, ConditionalEventBound (nu.prod mu)
      (capInfo i) (capEvent i) q)
    (hcapBudget : ((((N + 1) ^ 2 * T : ℕ) : ℝ) * q ≤ 1 / 8))
    (hnoCapProgress : ∀ z, (∀ i, z ∉ capEvent i) →
      progress (kappaEightFinalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (kappaEightFinalEta epsilon kappa) T)
              (kappa • output z))) ≤
        min T (successCountNat success z))
    (hunfMeas : MeasurableSet
      {z | progress (kappaEightFinalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection
              (hardRadius (kappaEightFinalEta epsilon kappa) T)
              (kappa • output z))) < T}) :
    ∃ U0 : ChainVector T →ₗᵢ[ℝ] E,
      hardHyperObjective (kappaEightFinalEta epsilon kappa) kappa U0 0 -
          sInf (Set.range
            (hardHyperObjective
              (kappaEightFinalEta epsilon kappa) kappa U0)) ≤ Delta ∧
      (¬ Integrable
          (fun omega ↦
            ‖gradient
              (hardHyperObjective
                (kappaEightFinalEta epsilon kappa) kappa U0)
              (output (U0, omega))‖) mu ∨
        3 * epsilon / 2 < ∫ omega,
          ‖gradient
            (hardHyperObjective
              (kappaEightFinalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ∂mu) ∧
      (¬ Integrable
          (fun omega ↦
            ‖gradient
              (hardHyperObjective
                (kappaEightFinalEta epsilon kappa) kappa U0)
              (output (U0, omega))‖ ^ 2) mu ∨
        9 * epsilon ^ 2 / 4 < ∫ omega,
          ‖gradient
            (hardHyperObjective
              (kappaEightFinalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ^ 2 ∂mu) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hprob : kappaEightRevealProbability Cvar
      (kappaEightFinalEta epsilon kappa) kappa sigma =
      revealProbability Cvar (finalEta epsilon kappa) (sigma * kappa) := by
    rw [← kappaEightFinalEta_eq_finalEta]
    exact kappaEightRevealProbability_eq_revealProbability_mul hkpos.ne'
  have hsigmaEff : 0 ≤ sigma * kappa := mul_nonneg hsigma hkpos.le
  have hTold : T = finalChainLength Delta CDelta epsilon kappa := by
    rw [← kappaEightFinalChainLength_eq_finalChainLength]
    exact hTdef
  have hNold : (N : ℝ) ≤
      finalLowerBoundConstant CDelta Cvar *
        mainComplexityScale Delta epsilon kappa (sigma * kappa) := by
    rw [← kappaEightLowerBoundConstant_eq_finalLowerBoundConstant,
      mainComplexityScale_mul_eq_kappaEightComplexityScale]
    exact hN
  have hfreshOld : ∀ t,
      FreshBernoulliEvent
        (mFrame.prod mOmega) (nu.prod mu) (past t) (success t)
        (revealProbability Cvar (finalEta epsilon kappa)
          (sigma * kappa)) := by
    intro t
    rw [← hprob]
    exact hfresh t
  have hnoCapOld : ∀ z, (∀ i, z ∉ capEvent i) →
      progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) ≤
        min T (successCountNat success z) := by
    simpa only [← kappaEightFinalEta_eq_finalEta] using hnoCapProgress
  have hunfOld : MeasurableSet
      {z | progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) < T} := by
    simpa only [← kappaEightFinalEta_eq_finalEta] using hunfMeas
  have hresult := main_lower_bound_assembly
    (nu := nu) (mu := mu) hCDelta hchainGap hcreg hDelta hkappa
      hepsilon hsigmaEff hCvar haccuracy hTold hNold past success
      hfreshOld output capInfo capEvent hcap hcapBudget hnoCapOld hunfOld
  simpa only [← kappaEightFinalEta_eq_finalEta] using hresult

end

end BilevelLowerBound
