/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightOracle
import BilevelLowerBoundLean.KappaEightPaperHardInstance
import BilevelLowerBoundLean.KappaEightHardOracleInterface
import BilevelLowerBoundLean.FreshSample

/-!
# Concrete fresh-sample oracle for the amplified paper instance

This module packages the analytic two-point identities from
`KappaEightOracle` in the literal amplified SFO class.  The upper response is
exact.  The lower response is unbiased and has conditional squared variance
at most `sigma^2`; its reveal probability is the one whose reciprocal carries
the additional `kappa^2` factor.
-/

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

theorem kappaEightBernoulliAverage_same
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (value : V) :
    bernoulliAverage p value value = value := by
  unfold bernoulliAverage
  module

/-- Bernoulli SFO attached to the concrete amplified population problem. -/
def kappaEightPaperHardBernoulliSFO
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (Cvar eta kappa sigma : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta) :
    KappaEightBernoulliSFO
      (kappaEightPaperPopulationProblem eta kappa J heta hkappa hsmall) where
  probability := kappaEightRevealProbability Cvar eta kappa sigma
  response b a :=
    (fderiv ℝ
        (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a,
      fderiv ℝ
        (kappaEightFullSampleLower kappa eta
          (kappaEightRevealProbability Cvar eta kappa sigma)
          (if b then 1 else 0) (hiddenFrameTranspose J)) a)

/-- A failed concrete paper-oracle response is the failed branch of the
one-frontier response interface. -/
theorem kappaEightPaperHardBernoulliSFO_response_false
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (Cvar eta kappa sigma : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta)
    (a : KappaEightQueryPoint E) :
    (kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
        heta hkappa hsmall).response false a =
      kappaEightHardJointGradientResponse kappa eta
        (kappaEightRevealProbability Cvar eta kappa sigma) 0 (1 / 4)
        (hardRadius eta T) (hiddenFrameTranspose J) a := by
  change
    (fderiv ℝ
        (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a,
      fderiv ℝ
        (kappaEightFullSampleLower kappa eta
          (kappaEightRevealProbability Cvar eta kappa sigma) 0
          (hiddenFrameTranspose J)) a) = _
  symm
  exact kappaEightHardJointGradientResponse_eq_paperResponse
    kappa eta (kappaEightRevealProbability Cvar eta kappa sigma)
      0 (1 / 4) (hiddenFrameTranspose J) a

/-- A successful concrete paper-oracle response is the successful branch of
the one-frontier response interface. -/
theorem kappaEightPaperHardBernoulliSFO_response_true
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (Cvar eta kappa sigma : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta)
    (a : KappaEightQueryPoint E) :
    (kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
        heta hkappa hsmall).response true a =
      kappaEightHardJointGradientResponse kappa eta
        (kappaEightRevealProbability Cvar eta kappa sigma) 1 (1 / 4)
        (hardRadius eta T) (hiddenFrameTranspose J) a := by
  change
    (fderiv ℝ
        (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a,
      fderiv ℝ
        (kappaEightFullSampleLower kappa eta
          (kappaEightRevealProbability Cvar eta kappa sigma) 1
          (hiddenFrameTranspose J)) a) = _
  symm
  exact kappaEightHardJointGradientResponse_eq_paperResponse
    kappa eta (kappaEightRevealProbability Cvar eta kappa sigma)
      1 (1 / 4) (hiddenFrameTranspose J) a

set_option maxHeartbeats 1000000 in
-- The proof instantiates all pointwise derivative and variance identities.
/-- The concrete amplified oracle belongs to the prescribed SFO class. -/
theorem exists_kappaEightPaperHardBernoulliSFOMember :
    ∃ Cvar : ℝ, 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa sigma : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 2 ≤ kappa) → (hT : 0 < T) →
        (hsigma : 0 ≤ sigma) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∀ hsmall : ∀ x : E,
          |amplifierDiag kappa * attenuatedFrontier kappa
            (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta,
        let O := kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
          heta (by linarith) hsmall
        KappaEightBernoulliSFOMember O sigma ∧
          1 / O.probability =
            max 1 (sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4)) := by
  obtain ⟨Cvar, hCvar, horacle⟩ :=
    exists_kappaEightFullSampleLower_oracle_properties
  refine ⟨Cvar, hCvar, ?_⟩
  intro E _ _ _ T eta kappa sigma heta hetaOne hkappa hT hsigma J
    hsmall
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  let prob := kappaEightRevealProbability Cvar eta kappa sigma
  let O := kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
    heta (by linarith) hsmall
  have hproperties (a : KappaEightQueryPoint E) :=
    horacle heta hetaOne hkappa hT hsigma hL a
  have hprob : 0 < prob := (hproperties 0).1
  have hprobOne : prob ≤ 1 := (hproperties 0).2.1
  refine ⟨?_, ?_⟩
  · refine
      { probability_pos := hprob
        probability_le_one := hprobOne
        upper_mean := ?_
        lower_mean := ?_
        upper_variance := ?_
        lower_variance := ?_ }
    · intro a
      change bernoulliAverage prob
        (fderiv ℝ
          (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J)) a)
        (fderiv ℝ
          (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J)) a) = _
      exact kappaEightBernoulliAverage_same _ _
    · intro a
      change bernoulliAverage prob
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0
          (hiddenFrameTranspose J)) a) =
        fderiv ℝ (kappaEightFullPopulationLower kappa eta
          (hiddenFrameTranspose J)) a
      simpa [prob] using (hproperties a).2.2.1
    · intro a
      change bernoulliSquaredNoise prob
        (fderiv ℝ
          (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J)) a)
        (fderiv ℝ
          (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J)) a)
        (fderiv ℝ
          (kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J)) a) ≤ sigma ^ 2
      rw [exactResponse_bernoulliSquaredNoise]
      positivity
    · intro a
      change bernoulliSquaredNoise prob
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (kappaEightFullPopulationLower kappa eta
          (hiddenFrameTranspose J)) a) ≤ sigma ^ 2
      simpa [prob] using (hproperties a).2.2.2.1
  · simpa [O, kappaEightPaperHardBernoulliSFO, prob] using
      (hproperties 0).2.2.2.2

/-! ## Fresh adaptive conditional law -/

/-- Conditional lower-oracle law at one arbitrary adaptive call. -/
structure KappaEightAdaptiveHardLowerCallLaw
    {Omega V : Type*} {mOmega : MeasurableSpace Omega}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : @Measure Omega mOmega) (past : MeasurableSpace Omega)
    (sample population : Omega → V) (noise : Omega → ℝ)
    (sigma : ℝ) : Prop where
  conditionalMean : mu[sample | past] =ᵐ[mu] population
  conditionalSquaredNoise :
    ∀ᵐ omega ∂mu, mu[noise | past] omega ≤ sigma ^ 2

/-- A fresh Bernoulli bit upgrades the pointwise two-branch calculation to
the conditional law required for an adaptive SFO call. -/
theorem kappaEightAdaptiveHardLowerCallLaw_of_fresh
    {Omega V : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {past : MeasurableSpace Omega} {success : Set Omega} {p : ℝ}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hp : 0 < p) (hpOne : p ≤ 1)
    (hfresh : FreshBernoulliEvent mOmega mu past success p)
    {base frontier : Omega → V}
    (hbaseMeas : StronglyMeasurable[past] base)
    (hfrontierMeas : StronglyMeasurable[past] frontier)
    (hbaseInt : Integrable base mu)
    (hfrontierInt : Integrable frontier mu)
    (hfrontierSqInt : Integrable (fun omega ↦ ‖frontier omega‖ ^ 2) mu)
    {sigma : ℝ}
    (hvariance : ∀ omega,
      ((1 - p) / p) * ‖frontier omega‖ ^ 2 ≤ sigma ^ 2) :
    KappaEightAdaptiveHardLowerCallLaw mu past
      (freshImportanceResponse p success base frontier)
      (fun omega ↦ base omega + frontier omega)
      (freshImportanceSquaredNoise p success base frontier) sigma := by
  refine ⟨?_, ?_⟩
  · exact hfresh.condExp_freshImportanceResponse hp.ne'
      hbaseMeas hfrontierMeas hbaseInt hfrontierInt
  · have hnoise := hfresh.condExp_freshImportanceSquaredNoise
      hp hpOne hbaseMeas hfrontierMeas hfrontierSqInt
    filter_upwards [hnoise] with omega homega
    rw [homega]
    exact hvariance omega

end

end BilevelLowerBound
