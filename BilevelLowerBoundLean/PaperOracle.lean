/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperHardInstance
import BilevelLowerBoundLean.FreshSample

/-!
# The concrete fresh-sample oracle used by the paper

The pointwise oracle below returns the exact upper derivative and one of the
two importance-weighted lower derivatives.  We prove membership in the
paper's bounded-variance SFO class, including the exact reveal probability.
The final section records the adaptive conditional law obtained when the bit
is sampled freshly after an arbitrary past transcript.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

theorem bernoulliAverage_same
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (value : V) :
    bernoulliAverage p value value = value := by
  unfold bernoulliAverage
  module

/-- The Bernoulli oracle associated with the concrete hard population pair. -/
def paperHardBernoulliSFO
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (Cvar eta kappa sigma : ℝ) (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hkappa : 0 < kappa)
    (hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta) :
    PaperBernoulliSFO
      (paperHardPopulationProblem eta kappa J
        heta hetaOne hkappa hfrontier) where
  probability := revealProbability Cvar eta sigma
  response b a :=
    (fderiv ℝ
        (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a,
      fderiv ℝ
        (fullSampleLower kappa eta
          (revealProbability Cvar eta sigma)
          (if b then 1 else 0) (hiddenFrameTranspose J)) a)

set_option maxHeartbeats 1000000 in
-- The proof instantiates all pointwise oracle identities simultaneously.
/-- The concrete hard oracle is an element of the paper's SFO class.  In
particular, the upper response is exact, the lower response is unbiased, and
both squared deviations are globally bounded by `sigma^2`. -/
theorem exists_paperHardBernoulliSFOMember :
    ∃ Cvar : ℝ, 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa sigma : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 0 < kappa) → (hT : 0 < T) → (hsigma : 0 ≤ sigma) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∀ hfrontier : ∀ x : E,
          |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta,
        let O := paperHardBernoulliSFO Cvar eta kappa sigma J
          heta hetaOne hkappa hfrontier
        PaperBernoulliSFOMember O sigma ∧
          1 / O.probability =
            max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
  obtain ⟨Cvar, hCvar, horacle⟩ :=
    exists_fullSampleLower_oracle_properties
  refine ⟨Cvar, hCvar, ?_⟩
  intro E _ _ _ T eta kappa sigma heta hetaOne hkappa hT hsigma J
    hfrontier
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  let prob := revealProbability Cvar eta sigma
  let O := paperHardBernoulliSFO Cvar eta kappa sigma J
    heta hetaOne hkappa hfrontier
  have hproperties (a : PaperQueryPoint E) :=
    horacle heta hetaOne hT hsigma hL kappa a
  have hprob : 0 < prob := (hproperties (0, (0, 0))).1
  have hprobOne : prob ≤ 1 := (hproperties (0, (0, 0))).2.1
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
        (fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a) =
        fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a
      exact bernoulliAverage_same _ _
    · intro a
      change bernoulliAverage prob
        (fderiv ℝ (fullSampleLower kappa eta prob 1
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullSampleLower kappa eta prob 0
          (hiddenFrameTranspose J)) a) =
        fderiv ℝ (fullPopulationLower kappa eta
          (hiddenFrameTranspose J)) a
      simpa [prob] using
        (hproperties a).2.2.1
    · intro a
      change bernoulliSquaredNoise prob
        (fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J)) a) ≤ sigma ^ 2
      rw [exactResponse_bernoulliSquaredNoise]
      positivity
    · intro a
      change bernoulliSquaredNoise prob
        (fderiv ℝ (fullSampleLower kappa eta prob 1
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullSampleLower kappa eta prob 0
          (hiddenFrameTranspose J)) a)
        (fderiv ℝ (fullPopulationLower kappa eta
          (hiddenFrameTranspose J)) a) ≤ sigma ^ 2
      simpa [prob] using
        (hproperties a).2.2.2.1
  · simpa [O, paperHardBernoulliSFO, prob] using
      (hproperties (0, (0, 0))).2.2.2.2

/-! ## Adaptive conditional law -/

/-- Conditional lower-oracle laws at one arbitrary adaptive query.  The
query-dependent base and frontier are allowed to depend on the complete past;
only the new Bernoulli event is fresh. -/
structure AdaptiveHardLowerCallLaw
    {Omega V : Type*} {mOmega : MeasurableSpace Omega}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : @Measure Omega mOmega) (past : MeasurableSpace Omega)
    (sample population : Omega → V) (noise : Omega → ℝ)
    (sigma : ℝ) : Prop where
  conditionalMean : mu[sample | past] =ᵐ[mu] population
  conditionalSquaredNoise :
    ∀ᵐ omega ∂mu, mu[noise | past] omega ≤ sigma ^ 2

/-- Fresh sampling upgrades the pointwise two-branch oracle calculation to
the conditional law required by the paper's adaptive SFO definition. -/
theorem adaptiveHardLowerCallLaw_of_fresh
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
    (hvariance : ∀ omega, ((1 - p) / p) * ‖frontier omega‖ ^ 2 ≤ sigma ^ 2) :
    AdaptiveHardLowerCallLaw mu past
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
