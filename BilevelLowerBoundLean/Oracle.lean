/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ConditionWitness
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Stochastic-oracle identities and variance bounds

This module verifies the analytic content of the paper's
`oracle-properties` lemma.  The only randomized part of the lower oracle is
the compensated frontier derivative, multiplied by the Bernoulli importance
weight `xi / p`.  We first prove the relevant two-point expectation and
second-moment identities in an arbitrary real normed space.  We then bound
the concrete compensated-frontier derivative by `C eta^2` and specialize the
generic identities to the hard lower objective.

The two-point averages below are the conditional expectations after fixing
the pre-query transcript.  Freshness is used precisely to say that the next
bit has weights `p` and `1-p` after that conditioning; no query-independence
is assumed or needed in the pointwise analytic estimates.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Bernoulli importance weighting -/

def importanceSample
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p xi : ℝ) (base frontier : V) : V :=
  base + (xi / p) • frontier

def bernoulliAverage
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (valueOne valueZero : V) : V :=
  p • valueOne + (1 - p) • valueZero

theorem bernoulliAverage_importanceSample
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p : ℝ} (hp : p ≠ 0) (base frontier : V) :
    bernoulliAverage p
        (importanceSample p 1 base frontier)
        (importanceSample p 0 base frontier) =
      base + frontier := by
  unfold bernoulliAverage importanceSample
  simp only [one_div, zero_div, zero_smul, add_zero, smul_add, smul_smul]
  rw [mul_inv_cancel₀ hp]
  module

theorem importanceSample_sub_population
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p xi : ℝ) (base frontier : V) :
    importanceSample p xi base frontier - (base + frontier) =
      (xi / p - 1) • frontier := by
  unfold importanceSample
  module

def bernoulliSquaredNoise
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : ℝ) (valueOne valueZero population : V) : ℝ :=
  p * ‖valueOne - population‖ ^ 2 +
    (1 - p) * ‖valueZero - population‖ ^ 2

theorem bernoulliSquaredNoise_importanceSample
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (base frontier : V) :
    bernoulliSquaredNoise p
        (importanceSample p 1 base frontier)
        (importanceSample p 0 base frontier)
        (base + frontier) =
      ((1 - p) / p) * ‖frontier‖ ^ 2 := by
  unfold bernoulliSquaredNoise
  rw [show importanceSample p 1 base frontier - (base + frontier) =
      (1 / p - 1) • frontier from
        importanceSample_sub_population p 1 base frontier,
    show importanceSample p 0 base frontier - (base + frontier) =
      (0 / p - 1) • frontier from
        importanceSample_sub_population p 0 base frontier]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hnonneg : 0 ≤ 1 / p - 1 := by
    rw [div_sub_one hp.ne']
    exact div_nonneg (sub_nonneg.mpr hp1) hp.le
  rw [abs_of_nonneg hnonneg]
  simp only [zero_div, zero_sub, abs_neg, abs_one, one_mul]
  field_simp [hp.ne']
  ring

theorem bernoulliSquaredNoise_importanceSample_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p C eta : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hC : 0 ≤ C) (frontier : V)
    (hfrontier : ‖frontier‖ ≤ C * eta ^ 2) (base : V) :
    bernoulliSquaredNoise p
        (importanceSample p 1 base frontier)
        (importanceSample p 0 base frontier)
        (base + frontier) ≤
      C ^ 2 * eta ^ 4 * ((1 - p) / p) := by
  rw [bernoulliSquaredNoise_importanceSample hp hp1]
  have hratio : 0 ≤ (1 - p) / p := div_nonneg (sub_nonneg.mpr hp1) hp.le
  have hbound0 : 0 ≤ C * eta ^ 2 := mul_nonneg hC (sq_nonneg eta)
  have hsquare : ‖frontier‖ ^ 2 ≤ (C * eta ^ 2) ^ 2 := by
    nlinarith [norm_nonneg frontier]
  calc
    (1 - p) / p * ‖frontier‖ ^ 2 ≤
        (1 - p) / p * (C * eta ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hratio
    _ = C ^ 2 * eta ^ 4 * ((1 - p) / p) := by ring

/-! ## Reveal probability -/

def revealProbability (Cvar eta sigma : ℝ) : ℝ :=
  if sigma = 0 then 1 else min 1 (Cvar * eta ^ 4 / sigma ^ 2)

theorem revealProbability_pos
    {Cvar eta sigma : ℝ} (hCvar : 0 < Cvar) (heta : 0 < eta) :
    0 < revealProbability Cvar eta sigma := by
  unfold revealProbability
  split_ifs with hsigma
  · norm_num
  · apply lt_min (by norm_num)
    positivity

theorem revealProbability_le_one (Cvar eta sigma : ℝ) :
    revealProbability Cvar eta sigma ≤ 1 := by
  unfold revealProbability
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem revealProbability_variance_le
    {Cvar eta sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hsigma : 0 ≤ sigma) :
    Cvar * eta ^ 4 *
        ((1 - revealProbability Cvar eta sigma) /
          revealProbability Cvar eta sigma) ≤
      sigma ^ 2 := by
  by_cases hs0 : sigma = 0
  · simp [revealProbability, hs0]
  · have hspos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hs0)
    let a : ℝ := Cvar * eta ^ 4 / sigma ^ 2
    have ha : 0 < a := by dsimp [a]; positivity
    rw [revealProbability, if_neg hs0]
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1]
      simp only [sub_self, div_one, mul_zero]
      exact sq_nonneg sigma
    · have halt : a < 1 := lt_of_not_ge ha1
      rw [min_eq_right halt.le]
      dsimp [a]
      field_simp [hs0]
      nlinarith [sq_nonneg sigma, mul_pos hCvar (pow_pos heta 4)]

theorem one_div_revealProbability
    {Cvar eta sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hsigma : 0 ≤ sigma) :
    1 / revealProbability Cvar eta sigma =
      max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
  by_cases hs0 : sigma = 0
  · simp [revealProbability, hs0]
  · have hspos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hs0)
    let a : ℝ := Cvar * eta ^ 4 / sigma ^ 2
    have ha : 0 < a := by dsimp [a]; positivity
    rw [revealProbability, if_neg hs0]
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1]
      have hquot : sigma ^ 2 / (Cvar * eta ^ 4) ≤ 1 := by
        dsimp [a] at ha1
        have hnum : sigma ^ 2 ≤ Cvar * eta ^ 4 := by
          simpa using (le_div_iff₀ (sq_pos_of_pos hspos)).mp ha1
        apply (div_le_one (mul_pos hCvar (pow_pos heta 4))).2
        exact hnum
      simp [max_eq_left hquot]
    · have halt : a < 1 := lt_of_not_ge ha1
      rw [min_eq_right halt.le]
      have hinv : 1 / a = sigma ^ 2 / (Cvar * eta ^ 4) := by
        dsimp [a]
        field_simp [hCvar.ne', heta.ne', hs0]
      have hquot : 1 ≤ sigma ^ 2 / (Cvar * eta ^ 4) := by
        rw [← hinv]
        rw [one_div]
        exact (one_le_inv₀ ha).2 halt.le
      rw [hinv, max_eq_right hquot]

/-! ## Size of the concrete frontier derivative -/

theorem norm_fderiv_mul_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x)
    {F0 F1 G0 G1 : ℝ}
    (hF0 : 0 ≤ F0) (_hF1 : 0 ≤ F1)
    (hG0 : 0 ≤ G0) (_hG1 : 0 ≤ G1)
    (hf0 : |f x| ≤ F0) (hf1 : ‖fderiv ℝ f x‖ ≤ F1)
    (hg0 : |g x| ≤ G0) (hg1 : ‖fderiv ℝ g x‖ ≤ G1) :
    ‖fderiv ℝ (fun y ↦ f y * g y) x‖ ≤ F0 * G1 + G0 * F1 := by
  rw [fderiv_fun_mul hf hg]
  calc
    ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖ ≤
        ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ :=
      norm_add_le _ _
    _ = |f x| * ‖fderiv ℝ g x‖ +
        |g x| * ‖fderiv ℝ f x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ F0 * G1 + G0 * F1 := by
      exact add_le_add
        (mul_le_mul hf0 hg1 (norm_nonneg _) hF0)
        (mul_le_mul hg0 hf1 (norm_nonneg _) hG0)

/-- A direct first-order companion to `compensatedPair_second_third_bounds`.
The product norm used in the analytic modules gives a conservative universal
constant; its `eta^2` scale is the quantity needed for stochastic variance. -/
theorem compensatedPair_first_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta Ctheta Cpsi : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hCtheta : 0 ≤ Ctheta) (hCpsi : 0 ≤ Cpsi)
    {theta : E → ℝ} (hthetaSmooth : ContDiff ℝ ∞ theta)
    (htheta0 : ∀ z : E, |theta z| ≤ Ctheta * eta ^ 2)
    (htheta1 : ∀ z : E,
      ‖iteratedFDeriv ℝ 1 theta z‖ ≤ Ctheta * eta)
    (hpsi0 : ∀ v : ℝ, |compactIdentity eta v| ≤ Cpsi * eta)
    (hpsi1 : ∀ v : ℝ,
      ‖iteratedFDeriv ℝ 1 (compactIdentity eta) v‖ ≤ Cpsi)
    (p : E × ℝ) :
    ‖fderiv ℝ (compensatedPair eta theta) p‖ ≤
      Ctheta * (Ctheta + 2 * Cpsi) * eta ^ 2 := by
  let Lz : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let Lv : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let Theta : E × ℝ → ℝ := theta ∘ Lz
  let Psi : E × ℝ → ℝ := (compactIdentity eta) ∘ Lv
  let TT : E × ℝ → ℝ := fun y ↦ Theta y * Theta y
  let TP : E × ℝ → ℝ := fun y ↦ Theta y * Psi y
  let TH : E × ℝ → ℝ := (2 : ℝ)⁻¹ • TT
  have hLz : ‖Lz‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ E ℝ
  have hLv : ‖Lv‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ E ℝ
  have hThetaSmooth : ContDiff ℝ ∞ Theta := hthetaSmooth.comp Lz.contDiff
  have hPsiSmooth : ContDiff ℝ ∞ Psi :=
    (compactIdentity_contDiff heta.ne').comp Lv.contDiff
  have hTheta0 : |Theta p| ≤ Ctheta * eta ^ 2 := htheta0 p.1
  have hTheta1 : ‖fderiv ℝ Theta p‖ ≤ Ctheta * eta := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      hthetaSmooth Lz hLz 1 p
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (by
      simpa [norm_iteratedFDeriv_one, Lz] using htheta1 p.1)
  have hPsi0 : |Psi p| ≤ Cpsi * eta := hpsi0 p.2
  have hPsi1 : ‖fderiv ℝ Psi p‖ ≤ Cpsi := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff heta.ne') Lv hLv 1 p
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (by
      simpa [norm_iteratedFDeriv_one, Lv] using hpsi1 p.2)
  have hTheta0nonneg : 0 ≤ Ctheta * eta ^ 2 :=
    mul_nonneg hCtheta (sq_nonneg eta)
  have hTheta1nonneg : 0 ≤ Ctheta * eta :=
    mul_nonneg hCtheta heta.le
  have hPsi0nonneg : 0 ≤ Cpsi * eta := mul_nonneg hCpsi heta.le
  have hTT : ‖fderiv ℝ TT p‖ ≤ 2 * Ctheta ^ 2 * eta ^ 3 := by
    have hraw := norm_fderiv_mul_le
      (hThetaSmooth.differentiable (by norm_num) p)
      (hThetaSmooth.differentiable (by norm_num) p)
      hTheta0nonneg hTheta1nonneg hTheta0nonneg hTheta1nonneg
      hTheta0 hTheta1 hTheta0 hTheta1
    dsimp [TT]
    calc
      ‖fderiv ℝ (fun y ↦ Theta y * Theta y) p‖ ≤
          (Ctheta * eta ^ 2) * (Ctheta * eta) +
            (Ctheta * eta ^ 2) * (Ctheta * eta) := hraw
      _ = 2 * Ctheta ^ 2 * eta ^ 3 := by ring
  have hTP : ‖fderiv ℝ TP p‖ ≤ 2 * Ctheta * Cpsi * eta ^ 2 := by
    have hraw := norm_fderiv_mul_le
      (hThetaSmooth.differentiable (by norm_num) p)
      (hPsiSmooth.differentiable (by norm_num) p)
      hTheta0nonneg hTheta1nonneg hPsi0nonneg hCpsi
      hTheta0 hTheta1 hPsi0 hPsi1
    dsimp [TP]
    calc
      ‖fderiv ℝ (fun y ↦ Theta y * Psi y) p‖ ≤
          (Ctheta * eta ^ 2) * Cpsi +
            (Cpsi * eta) * (Ctheta * eta) := hraw
      _ = 2 * Ctheta * Cpsi * eta ^ 2 := by ring
  have hTHSmooth : ContDiff ℝ ∞ TH :=
    contDiff_const.smul (hThetaSmooth.mul hThetaSmooth)
  have hTPSmooth : ContDiff ℝ ∞ TP := hThetaSmooth.mul hPsiSmooth
  have hTH : ‖fderiv ℝ TH p‖ ≤ Ctheta ^ 2 * eta ^ 3 := by
    dsimp [TH]
    rw [fderiv_const_smul
      ((hThetaSmooth.mul hThetaSmooth).differentiable (by norm_num) p),
      norm_smul]
    norm_num
    linarith
  have hfun : compensatedPair eta theta = TH - TP := by
    funext y
    simp [compensatedPair, compensatedBlock, TH, TT, TP, Theta, Psi, Lz, Lv]
    ring
  rw [hfun, fderiv_sub
    (hTHSmooth.differentiable (by norm_num) p)
    (hTPSmooth.differentiable (by norm_num) p)]
  calc
    ‖fderiv ℝ TH p - fderiv ℝ TP p‖ ≤
        ‖fderiv ℝ TH p‖ + ‖fderiv ℝ TP p‖ := norm_sub_le _ _
    _ ≤ Ctheta ^ 2 * eta ^ 3 +
        2 * Ctheta * Cpsi * eta ^ 2 := add_le_add hTH hTP
    _ ≤ Ctheta * (Ctheta + 2 * Cpsi) * eta ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg Ctheta)
        (mul_nonneg (sq_nonneg eta) (sub_nonneg.mpr heta1))]

/-- The actual hidden compensated block has a dimension-free first derivative
bound of order `eta^2`.  We enlarge the universal constant by one so that it
is strictly positive, which makes the reveal-probability formula total. -/
theorem exists_hard_compensatedPair_first_bound :
    ∃ Cnoise : ℝ, 0 < Cnoise ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta : ℝ}, 0 < eta → eta ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ p : E × ℝ,
        ‖fderiv ℝ
          (compensatedPair eta (hardFrontierMap eta L)) p‖ ≤
          Cnoise * eta ^ 2 := by
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨Cpsi, hCpsi, hpsi⟩ :=
    exists_common_bound_compactIdentity_one_three
  let Cnoise : ℝ := 1 + Ctheta * (Ctheta + 2 * Cpsi)
  have hbase : 0 ≤ Ctheta * (Ctheta + 2 * Cpsi) := by positivity
  refine ⟨Cnoise, by dsimp [Cnoise]; linarith, ?_⟩
  intro E _ _ T eta heta heta1 hT L hL p
  have hthetaAll := htheta heta hT hL
  have hpsi0 (v : ℝ) : |compactIdentity eta v| ≤ Cpsi * eta :=
    norm_compactIdentity_value_le heta hCpsi hpsi v
  have hpsi1 (v : ℝ) :
      ‖iteratedFDeriv ℝ 1 (compactIdentity eta) v‖ ≤ Cpsi :=
    norm_iteratedFDeriv_compactIdentity_one_le heta hCpsi hpsi v
  have hraw := compensatedPair_first_bound heta heta1 hCtheta hCpsi
    (hardFrontierMap_contDiff heta hT L)
    (fun z ↦ (hthetaAll z).1)
    (fun z ↦ (hthetaAll z).2.1)
    hpsi0 hpsi1 p
  calc
    ‖fderiv ℝ (compensatedPair eta (hardFrontierMap eta L)) p‖ ≤
        Ctheta * (Ctheta + 2 * Cpsi) * eta ^ 2 := hraw
    _ ≤ Cnoise * eta ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg eta)
      dsimp [Cnoise]
      linarith

/-! ## The concrete stochastic lower oracle -/

def fullSampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi : ℝ)
    (L : E →L[ℝ] ChainVector T) : E × (E × ℝ) → ℝ :=
  lowerPopulationSum (fullBaseQuadratic kappa)
    ((xi / prob) •
      fullCompensatedPair eta (hardFrontierMap eta L))

@[simp] theorem fullSampleLower_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi : ℝ)
    (L : E →L[ℝ] ChainVector T) (a : E × (E × ℝ)) :
    fullSampleLower kappa eta prob xi L a =
      sampleLower kappa eta prob xi (hardFrontierMap eta L)
        a.1 a.2.1 a.2.2 := by
  rfl

theorem fderiv_fullSampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (kappa prob xi : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : E × (E × ℝ)) :
    fderiv ℝ (fullSampleLower kappa eta prob xi L) a =
      importanceSample prob xi
        (fderiv ℝ (fullBaseQuadratic kappa) a)
        (fderiv ℝ
          (fullCompensatedPair eta (hardFrontierMap eta L)) a) := by
  let R : E × (E × ℝ) → ℝ :=
    fullCompensatedPair eta (hardFrontierMap eta L)
  have hbase : DifferentiableAt ℝ (fullBaseQuadratic kappa) a :=
    (fullBaseQuadratic_contDiff kappa).differentiable (by norm_num) a
  have hR : DifferentiableAt ℝ R a :=
    (fullCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L)).differentiable (by norm_num) a
  change fderiv ℝ
      (lowerPopulationSum (fullBaseQuadratic kappa)
        ((xi / prob) • R)) a = _
  unfold lowerPopulationSum importanceSample
  rw [fderiv_add hbase (hR.const_smul (xi / prob)),
    fderiv_const_smul hR]

theorem fderiv_fullPopulationLower_as_base_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (kappa : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : E × (E × ℝ)) :
    fderiv ℝ (fullPopulationLower kappa eta L) a =
      fderiv ℝ (fullBaseQuadratic kappa) a +
        fderiv ℝ
          (fullCompensatedPair eta (hardFrontierMap eta L)) a := by
  have hbase : DifferentiableAt ℝ (fullBaseQuadratic kappa) a :=
    (fullBaseQuadratic_contDiff kappa).differentiable (by norm_num) a
  have hR : DifferentiableAt ℝ
      (fullCompensatedPair eta (hardFrontierMap eta L)) a :=
    (fullCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L)).differentiable (by norm_num) a
  unfold fullPopulationLower lowerPopulationSum
  exact fderiv_add hbase hR

theorem fullSampleLower_bernoulli_gradient_unbiased
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta prob : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (hprob : prob ≠ 0)
    (kappa : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : E × (E × ℝ)) :
    bernoulliAverage prob
        (fderiv ℝ (fullSampleLower kappa eta prob 1 L) a)
        (fderiv ℝ (fullSampleLower kappa eta prob 0 L) a) =
      fderiv ℝ (fullPopulationLower kappa eta L) a := by
  rw [fderiv_fullSampleLower heta hT,
    fderiv_fullSampleLower heta hT,
    bernoulliAverage_importanceSample hprob,
    fderiv_fullPopulationLower_as_base_frontier heta hT]

theorem exists_fullCompensatedPair_gradient_bound :
    ∃ Cnoise : ℝ, 0 < Cnoise ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta : ℝ}, 0 < eta → eta ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ a : E × (E × ℝ),
        ‖fderiv ℝ
          (fullCompensatedPair eta (hardFrontierMap eta L)) a‖ ≤
          Cnoise * eta ^ 2 := by
  obtain ⟨Cnoise, hCnoise, hbound⟩ :=
    exists_hard_compensatedPair_first_bound
  refine ⟨Cnoise, hCnoise, ?_⟩
  intro E _ _ T eta heta heta1 hT L hL a
  have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
    (compensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L))
    (fullLowerProjection (E := E))
    (norm_fullLowerProjection_le_one (E := E)) 1 a
  rw [norm_iteratedFDeriv_one] at hcomp
  exact hcomp.trans (by
    simpa [fullLowerProjection] using
      hbound heta heta1 hT hL a.2)

theorem exactResponse_bernoulliSquaredNoise
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : ℝ) (value : V) :
    bernoulliSquaredNoise p value value value = 0 := by
  simp [bernoulliSquaredNoise]

set_option maxHeartbeats 800000 in
-- Elaborating the fully quantified oracle certificate requires extra reduction.
/-- Complete analytic oracle certificate.  The upper oracle is exact.  The
lower oracle is conditionally unbiased for a fresh Bernoulli bit, has global
variance at most `sigma^2`, and its reveal probability has the exact inverse
formula used in the lower-bound scaling. -/
theorem exists_fullSampleLower_oracle_properties :
    ∃ Cvar : ℝ, 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta sigma : ℝ},
        0 < eta → eta ≤ 1 → 0 < T → 0 ≤ sigma →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ (kappa : ℝ) (a : E × (E × ℝ)),
        let prob := revealProbability Cvar eta sigma
        0 < prob ∧ prob ≤ 1 ∧
        bernoulliAverage prob
            (fderiv ℝ (fullSampleLower kappa eta prob 1 L) a)
            (fderiv ℝ (fullSampleLower kappa eta prob 0 L) a) =
          fderiv ℝ (fullPopulationLower kappa eta L) a ∧
        bernoulliSquaredNoise prob
            (fderiv ℝ (fullSampleLower kappa eta prob 1 L) a)
            (fderiv ℝ (fullSampleLower kappa eta prob 0 L) a)
            (fderiv ℝ (fullPopulationLower kappa eta L) a) ≤
          sigma ^ 2 ∧
        1 / prob = max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
  obtain ⟨Cnoise, hCnoise, hnoise⟩ :=
    exists_fullCompensatedPair_gradient_bound
  let Cvar : ℝ := Cnoise ^ 2
  have hCvar : 0 < Cvar := by dsimp [Cvar]; positivity
  refine ⟨Cvar, hCvar, ?_⟩
  intro E _ _ T eta sigma heta heta1 hT hsigma L hL kappa a
  let prob := revealProbability Cvar eta sigma
  have hprob : 0 < prob := revealProbability_pos hCvar heta
  have hprob1 : prob ≤ 1 := revealProbability_le_one _ _ _
  have hunbiased := fullSampleLower_bernoulli_gradient_unbiased
    heta hT hprob.ne' kappa L a
  let base := fderiv ℝ (fullBaseQuadratic kappa) a
  let frontier := fderiv ℝ
    (fullCompensatedPair eta (hardFrontierMap eta L)) a
  have hfrontier : ‖frontier‖ ≤ Cnoise * eta ^ 2 :=
    hnoise heta heta1 hT hL a
  have hsampleOne :
      fderiv ℝ (fullSampleLower kappa eta prob 1 L) a =
        importanceSample prob 1 base frontier :=
    fderiv_fullSampleLower heta hT kappa prob 1 L a
  have hsampleZero :
      fderiv ℝ (fullSampleLower kappa eta prob 0 L) a =
        importanceSample prob 0 base frontier :=
    fderiv_fullSampleLower heta hT kappa prob 0 L a
  have hpopulation :
      fderiv ℝ (fullPopulationLower kappa eta L) a =
        base + frontier :=
    fderiv_fullPopulationLower_as_base_frontier heta hT kappa L a
  have hvarianceRaw := bernoulliSquaredNoise_importanceSample_le
    hprob hprob1 hCnoise.le frontier hfrontier base
  have hvariance :
      bernoulliSquaredNoise prob
          (fderiv ℝ (fullSampleLower kappa eta prob 1 L) a)
          (fderiv ℝ (fullSampleLower kappa eta prob 0 L) a)
          (fderiv ℝ (fullPopulationLower kappa eta L) a) ≤
        sigma ^ 2 := by
    rw [hsampleOne, hsampleZero, hpopulation]
    exact hvarianceRaw.trans (by
      change Cvar * eta ^ 4 * ((1 - prob) / prob) ≤ sigma ^ 2
      exact revealProbability_variance_le hCvar heta hsigma)
  refine ⟨hprob, hprob1, hunbiased, hvariance, ?_⟩
  exact one_div_revealProbability hCvar heta hsigma

/-! ## Euclidean-gradient interpretation -/

abbrev LowerEuclideanSpace (E : Type*) := WithLp 2 (E × ℝ)

abbrev FullEuclideanSpace (E : Type*) :=
  WithLp 2 (E × LowerEuclideanSpace E)

def lowerEuclideanToProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LowerEuclideanSpace E →L[ℝ] E × ℝ :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap

@[simp] theorem lowerEuclideanToProduct_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : LowerEuclideanSpace E) :
    lowerEuclideanToProduct y = (y.fst, y.snd) := by
  rfl

set_option maxHeartbeats 800000 in
-- The generic `WithLp` operator-norm instance requires deeper typeclass reduction.
theorem norm_lowerEuclideanToProduct_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(lowerEuclideanToProduct : LowerEuclideanSpace E →L[ℝ] E × ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (lowerEuclideanToProduct (E := E)) (by norm_num)
  intro y
  rw [lowerEuclideanToProduct_apply, Prod.norm_def, one_mul]
  exact max_le
    (WithLp.norm_fst_le (α := E) (β := ℝ) y)
    (WithLp.norm_snd_le (α := E) (β := ℝ) y)

def compensatedPairEuclidean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : ℝ) (theta : E → ℝ) : LowerEuclideanSpace E → ℝ :=
  (compensatedPair eta theta) ∘ lowerEuclideanToProduct

theorem compensatedPairEuclidean_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta : ℝ} (heta : eta ≠ 0) {theta : E → ℝ}
    (htheta : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (compensatedPairEuclidean eta theta) :=
  (compensatedPair_contDiff heta htheta).comp
    (lowerEuclideanToProduct (E := E)).contDiff

theorem norm_gradient_eq_norm_fderiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (x : F) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ F).symm.norm_map _

theorem exists_compensatedPairEuclidean_gradient_bound :
    ∃ Cnoise : ℝ, 0 < Cnoise ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta : ℝ},
        0 < eta → eta ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ y : LowerEuclideanSpace E,
        ‖gradient
          (compensatedPairEuclidean eta (hardFrontierMap eta L)) y‖ ≤
          Cnoise * eta ^ 2 := by
  obtain ⟨Cnoise, hCnoise, hbound⟩ :=
    exists_hard_compensatedPair_first_bound
  refine ⟨Cnoise, hCnoise, ?_⟩
  intro E _ _ _ T eta heta heta1 hT L hL y
  rw [norm_gradient_eq_norm_fderiv]
  have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
    (compensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L))
    (lowerEuclideanToProduct (E := E))
    (norm_lowerEuclideanToProduct_le_one (E := E)) 1 y
  rw [norm_iteratedFDeriv_one] at hcomp
  have hbound' :
      ‖iteratedFDeriv ℝ 1
        (compensatedPair eta (hardFrontierMap eta L))
          (lowerEuclideanToProduct y)‖ ≤ Cnoise * eta ^ 2 := by
    simpa [norm_iteratedFDeriv_one] using
      hbound heta heta1 hT hL (lowerEuclideanToProduct y)
  exact hcomp.trans hbound'

def fullEuclideanFrontierGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta : ℝ)
    (L : E →L[ℝ] ChainVector T) (y : LowerEuclideanSpace E) :
    FullEuclideanSpace E :=
  WithLp.toLp 2
    (0, gradient
      (compensatedPairEuclidean eta (hardFrontierMap eta L)) y)

theorem norm_fullEuclideanFrontierGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta : ℝ)
    (L : E →L[ℝ] ChainVector T) (y : LowerEuclideanSpace E) :
    ‖fullEuclideanFrontierGradient eta L y‖ =
      ‖gradient
        (compensatedPairEuclidean eta (hardFrontierMap eta L)) y‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [fullEuclideanFrontierGradient]

/-- Euclidean-vector version of the oracle certificate.  The first component
of the frontier vector is exactly zero because the randomized block does not
depend on `x`; the remaining two components use the paper's L2 product norm. -/
theorem exists_euclidean_frontier_oracle_properties :
    ∃ Cvar : ℝ, 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta sigma : ℝ},
        0 < eta → eta ≤ 1 → 0 < T → 0 ≤ sigma →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ (y : LowerEuclideanSpace E) (base : FullEuclideanSpace E),
        let prob := revealProbability Cvar eta sigma
        let frontier := fullEuclideanFrontierGradient eta L y
        bernoulliAverage prob
            (importanceSample prob 1 base frontier)
            (importanceSample prob 0 base frontier) = base + frontier ∧
        bernoulliSquaredNoise prob
            (importanceSample prob 1 base frontier)
            (importanceSample prob 0 base frontier)
            (base + frontier) ≤ sigma ^ 2 ∧
        1 / prob = max 1 (sigma ^ 2 / (Cvar * eta ^ 4)) := by
  obtain ⟨Cnoise, hCnoise, hnoise⟩ :=
    exists_compensatedPairEuclidean_gradient_bound
  let Cvar : ℝ := Cnoise ^ 2
  have hCvar : 0 < Cvar := by dsimp [Cvar]; positivity
  refine ⟨Cvar, hCvar, ?_⟩
  intro E _ _ _ T eta sigma heta heta1 hT hsigma L hL y base
  let prob := revealProbability Cvar eta sigma
  let frontier := fullEuclideanFrontierGradient eta L y
  have hprob : 0 < prob := revealProbability_pos hCvar heta
  have hprob1 : prob ≤ 1 := revealProbability_le_one _ _ _
  have hfrontier : ‖frontier‖ ≤ Cnoise * eta ^ 2 := by
    rw [norm_fullEuclideanFrontierGradient]
    exact hnoise heta heta1 hT hL y
  refine ⟨bernoulliAverage_importanceSample hprob.ne' base frontier, ?_, ?_⟩
  · have hraw := bernoulliSquaredNoise_importanceSample_le
      hprob hprob1 hCnoise.le frontier hfrontier base
    exact hraw.trans (by
      change Cvar * eta ^ 4 * ((1 - prob) / prob) ≤ sigma ^ 2
      exact revealProbability_variance_le hCvar heta hsigma)
  · exact one_div_revealProbability hCvar heta hsigma

end

end BilevelLowerBound
