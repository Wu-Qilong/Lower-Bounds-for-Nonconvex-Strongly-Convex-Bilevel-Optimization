/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPaperClasses
import BilevelLowerBoundLean.KappaEightParameterSelection
import BilevelLowerBoundLean.KappaEightPopulationRegularity

/-!
# Stochastic oracle for the two-coordinate amplifier

This module constructs the Bernoulli first-order oracle for the independent
`kappa^8` hard instance.  Its lower response is the derivative of the exact
sample objective: the public quadratic is always returned, while the complete
attenuated compensated frontier is importance weighted.  We prove the exact
population identity, conditional-unbiased two-point identity, and the global
variance bound at the new reveal probability.
-/

open Function Real
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Exact sample objective -/

/-- Exact sample lower objective on the full joint query. -/
def kappaEightFullSampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi : ℝ)
    (L : E →L[ℝ] ChainVector T) : KappaEightQueryPoint E → ℝ :=
  lowerPopulationSum (kappaEightFullBaseQuadratic kappa)
    ((xi / prob) •
      kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L))

@[simp]
theorem kappaEightFullSampleLower_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi : ℝ)
    (L : E →L[ℝ] ChainVector T) (p : KappaEightQueryPoint E) :
    kappaEightFullSampleLower kappa eta prob xi L p =
      kappaEightSampleLower kappa eta prob xi (hardFrontierMap eta L)
        p.1 p.2.1 p.2.2 := by
  unfold kappaEightFullSampleLower lowerPopulationSum
    kappaEightSampleLower
  change kappaEightFullBaseQuadratic kappa p +
      (xi / prob) *
        kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L) p = _
  rw [kappaEightFullBaseQuadratic_apply]
  rfl

theorem kappaEightFullPopulationLower_eq_base_add_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta : ℝ) (L : E →L[ℝ] ChainVector T) :
    kappaEightFullPopulationLower kappa eta L =
      lowerPopulationSum (kappaEightFullBaseQuadratic kappa)
        (kappaEightFullCompensatedPair eta kappa
          (hardFrontierMap eta L)) := by
  rfl

/-- The two sample objectives average to the exact full population lower
objective, before taking any derivative. -/
theorem kappaEightFullSampleLower_bernoulli_population
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {prob : ℝ} (hprob : prob ≠ 0)
    (kappa eta : ℝ) (L : E →L[ℝ] ChainVector T)
    (p : KappaEightQueryPoint E) :
    prob * kappaEightFullSampleLower kappa eta prob 1 L p +
        (1 - prob) * kappaEightFullSampleLower kappa eta prob 0 L p =
      kappaEightFullPopulationLower kappa eta L p := by
  rw [kappaEightFullSampleLower_apply, kappaEightFullSampleLower_apply,
    kappaEightFullPopulationLower_apply]
  exact kappaEightSampleLower_bernoulli_population hprob
    (hardFrontierMap eta L) p.1 p.2.1 p.2.2

/-! ## Exact derivative and expectation identities -/

theorem fderiv_kappaEightFullSampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (kappa prob xi : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    fderiv ℝ (kappaEightFullSampleLower kappa eta prob xi L) a =
      importanceSample prob xi
        (fderiv ℝ (kappaEightFullBaseQuadratic kappa) a)
        (fderiv ℝ
          (kappaEightFullCompensatedPair eta kappa
            (hardFrontierMap eta L)) a) := by
  let R : KappaEightQueryPoint E → ℝ :=
    kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L)
  have hbase : DifferentiableAt ℝ (kappaEightFullBaseQuadratic kappa) a :=
    (kappaEightFullBaseQuadratic_contDiff kappa).differentiable (by norm_num) a
  have hR : DifferentiableAt ℝ R a :=
    (kappaEightFullCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L)).differentiable (by norm_num) a
  change fderiv ℝ
      (lowerPopulationSum (kappaEightFullBaseQuadratic kappa)
        ((xi / prob) • R)) a = _
  unfold lowerPopulationSum importanceSample
  rw [fderiv_add hbase (hR.const_smul (xi / prob)),
    fderiv_const_smul hR]

theorem fderiv_kappaEightFullPopulationLower_as_base_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (kappa : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a =
      fderiv ℝ (kappaEightFullBaseQuadratic kappa) a +
        fderiv ℝ
          (kappaEightFullCompensatedPair eta kappa
            (hardFrontierMap eta L)) a := by
  have hbase : DifferentiableAt ℝ (kappaEightFullBaseQuadratic kappa) a :=
    (kappaEightFullBaseQuadratic_contDiff kappa).differentiable (by norm_num) a
  have hR : DifferentiableAt ℝ
      (kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L)) a :=
    (kappaEightFullCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L)).differentiable (by norm_num) a
  rw [kappaEightFullPopulationLower_eq_base_add_frontier]
  exact fderiv_add hbase hR

theorem kappaEightFullSampleLower_bernoulli_gradient_unbiased
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta prob : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (hprob : prob ≠ 0)
    (kappa : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    bernoulliAverage prob
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a)
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a) =
      fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a := by
  rw [fderiv_kappaEightFullSampleLower heta hT,
    fderiv_kappaEightFullSampleLower heta hT,
    bernoulliAverage_importanceSample hprob,
    fderiv_kappaEightFullPopulationLower_as_base_frontier heta hT]

/-- Exact conditional second moment of the amplified Bernoulli correction. -/
theorem kappaEightFullSampleLower_bernoulli_gradient_squaredNoise
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta prob : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (hprob : 0 < prob)
    (hprobOne : prob ≤ 1) (kappa : ℝ)
    (L : E →L[ℝ] ChainVector T) (a : KappaEightQueryPoint E) :
    bernoulliSquaredNoise prob
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a)
        (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a)
        (fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a) =
      ((1 - prob) / prob) *
        ‖fderiv ℝ
          (kappaEightFullCompensatedPair eta kappa
            (hardFrontierMap eta L)) a‖ ^ 2 := by
  rw [fderiv_kappaEightFullSampleLower heta hT,
    fderiv_kappaEightFullSampleLower heta hT,
    fderiv_kappaEightFullPopulationLower_as_base_frontier heta hT]
  exact bernoulliSquaredNoise_importanceSample hprob hprobOne _ _

/-! ## Uniform frontier-gradient and variance estimates -/

theorem exists_kappaEightFullCompensatedPair_gradient_bound :
    ∃ Cnoise : ℝ, 0 < Cnoise ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta kappa : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ a : KappaEightQueryPoint E,
        ‖fderiv ℝ
          (kappaEightFullCompensatedPair eta kappa
            (hardFrontierMap eta L)) a‖ ≤
          Cnoise * eta ^ 2 / kappa := by
  obtain ⟨Cnoise, CHess, Cthird, hCnoise, _hCHess, _hCthird, hbound⟩ :=
    exists_kappaEight_hard_compensated_pair_regularities
  refine ⟨Cnoise, hCnoise, ?_⟩
  intro E _ _ T eta kappa heta hetaOne hkappa hT L hL a
  have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
    (f := kappaEightCompensatedPair eta kappa (hardFrontierMap eta L))
    (kappaEightCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L))
    (kappaEightFullLowerProjection (E := E))
    (norm_kappaEightFullLowerProjection_le_one (E := E)) 1 a
  rw [norm_iteratedFDeriv_one] at hcomp
  exact hcomp.trans (by
    simpa [kappaEightFullLowerProjection] using
      (hbound heta hetaOne hkappa hT hL a.2).1)

set_option maxHeartbeats 800000 in
-- Elaborating the fully quantified variance certificate requires extra reduction.
/-- Complete analytic certificate for the amplified stochastic lower oracle. -/
theorem exists_kappaEightFullSampleLower_oracle_properties :
    ∃ Cvar : ℝ, 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta kappa sigma : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T → 0 ≤ sigma →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ a : KappaEightQueryPoint E,
        let prob := kappaEightRevealProbability Cvar eta kappa sigma
        0 < prob ∧ prob ≤ 1 ∧
        bernoulliAverage prob
            (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a)
            (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a) =
          fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a ∧
        bernoulliSquaredNoise prob
            (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a)
            (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a)
            (fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a) ≤
          sigma ^ 2 ∧
        1 / prob =
          max 1 (sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4)) := by
  obtain ⟨Cnoise, hCnoise, hnoise⟩ :=
    exists_kappaEightFullCompensatedPair_gradient_bound
  let Cvar : ℝ := Cnoise ^ 2
  have hCvar : 0 < Cvar := by dsimp [Cvar]; positivity
  refine ⟨Cvar, hCvar, ?_⟩
  intro E _ _ T eta kappa sigma heta hetaOne hkappa hT hsigma L hL a
  let prob := kappaEightRevealProbability Cvar eta kappa sigma
  have hkappaPos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hprob : 0 < prob :=
    kappaEightRevealProbability_pos hCvar heta hkappaPos
  have hprobOne : prob ≤ 1 :=
    kappaEightRevealProbability_le_one _ _ _ _
  have hunbiased := kappaEightFullSampleLower_bernoulli_gradient_unbiased
    heta hT hprob.ne' kappa L a
  let base := fderiv ℝ (kappaEightFullBaseQuadratic kappa) a
  let frontier := fderiv ℝ
    (kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L)) a
  have hfrontier : ‖frontier‖ ≤ Cnoise * eta ^ 2 / kappa :=
    hnoise heta hetaOne hkappa hT hL a
  have hfrontierSq : ‖frontier‖ ^ 2 ≤ Cvar * eta ^ 4 / kappa ^ 2 := by
    have hright : 0 ≤ Cnoise * eta ^ 2 / kappa := by positivity
    calc
      ‖frontier‖ ^ 2 ≤ (Cnoise * eta ^ 2 / kappa) ^ 2 := by
        nlinarith [norm_nonneg frontier]
      _ = Cvar * eta ^ 4 / kappa ^ 2 := by
        dsimp [Cvar]
        field_simp [hkappaPos.ne']
  have hsampleOne :
      fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a =
        importanceSample prob 1 base frontier :=
    fderiv_kappaEightFullSampleLower heta hT kappa prob 1 L a
  have hsampleZero :
      fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a =
        importanceSample prob 0 base frontier :=
    fderiv_kappaEightFullSampleLower heta hT kappa prob 0 L a
  have hpopulation :
      fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a =
        base + frontier :=
    fderiv_kappaEightFullPopulationLower_as_base_frontier heta hT kappa L a
  have hvariance :
      bernoulliSquaredNoise prob
          (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 1 L) a)
          (fderiv ℝ (kappaEightFullSampleLower kappa eta prob 0 L) a)
          (fderiv ℝ (kappaEightFullPopulationLower kappa eta L) a) ≤
        sigma ^ 2 := by
    rw [hsampleOne, hsampleZero, hpopulation]
    exact kappaEightBernoulliSquaredNoise_le hCvar heta hkappaPos hsigma
      base frontier hfrontierSq
  refine ⟨hprob, hprobOne, hunbiased, hvariance, ?_⟩
  exact one_div_kappaEightRevealProbability hCvar heta hkappaPos hsigma

end

end BilevelLowerBound
