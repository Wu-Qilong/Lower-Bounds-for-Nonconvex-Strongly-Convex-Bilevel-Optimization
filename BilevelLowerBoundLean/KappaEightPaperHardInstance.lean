/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPaperClasses
import BilevelLowerBoundLean.KappaEightPopulationRegularity
import BilevelLowerBoundLean.GapGradient

/-!
# Concrete population problem for the amplified hard pair

This module packages the new upper objective, the independently defined full
population lower objective, the exact lower solution, and the common hard
hyper-objective into the literal problem type used by the final theorem.  In
particular, the lower solution is proved globally minimal and unique by the
value-level amplifier theorem.
-/

open Function MeasureTheory Set
open scoped ContDiff ENNReal MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- Full upper objective.  Its auxiliary readout is exactly `v2`. -/
def kappaEightFullHardUpper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta lam R : ℝ) (L : E →L[ℝ] ChainVector T) :
    KappaEightQueryPoint E → ℝ :=
  fun p ↦ kappaEightHardUpper eta lam R
    (hiddenProbe R L) p.2.1 p.2.2

@[simp]
theorem kappaEightFullHardUpper_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta lam R : ℝ) (L : E →L[ℝ] ChainVector T)
    (p : KappaEightQueryPoint E) :
    kappaEightFullHardUpper eta lam R L p =
      kappaEightHardUpper eta lam R (hiddenProbe R L) p.2.1 p.2.2 := rfl

/-- Exact amplified lower solution. -/
def kappaEightPaperLowerSolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta kappa : ℝ) (L : E →L[ℝ] ChainVector T) (x : E) :
    KappaEightLowerPoint E :=
  (kappa • x,
    kappaEightAuxSolution kappa
      (hardFrontierMap eta L (kappa • x)))

/-- A scaled frontier bound places the inverse-amplified first coordinate in
the cutoff identity region. -/
theorem kappaEightCandidateFirst_le_eta_of_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa Ctheta : ℝ} (heta : 0 < eta) (hkappa : 2 ≤ kappa)
    (hCtheta : 0 ≤ Ctheta) (hscale : 3 * Ctheta * eta ≤ 1)
    {theta : E → ℝ}
    (hvalue : ∀ z, |theta z| ≤ Ctheta * eta ^ 2) (z : E) :
    |amplifierDiag kappa * attenuatedFrontier kappa (theta z)| ≤ eta := by
  have hspos : 0 < amplifierOffDiag kappa :=
    amplifierOffDiag_pos (by linarith)
  have hdpos : 0 < amplifierDiag kappa := amplifierDiag_pos (by linarith)
  have hratio : 0 ≤ amplifierDiag kappa / amplifierOffDiag kappa := by
    exact div_nonneg hdpos.le hspos.le
  have hratioThree := amplifierDiag_div_offDiag_le_three hkappa
  rw [amplified_proposed_first_coordinate (by linarith)]
  rw [abs_mul]
  have habsRatio : |amplifierDiag kappa / amplifierOffDiag kappa| =
      amplifierDiag kappa / amplifierOffDiag kappa :=
    abs_of_nonneg hratio
  rw [habsRatio]
  calc
    amplifierDiag kappa / amplifierOffDiag kappa * |theta z| ≤
        3 * (Ctheta * eta ^ 2) :=
      mul_le_mul hratioThree (hvalue z) (abs_nonneg _) (by norm_num)
    _ = (3 * Ctheta * eta) * eta := by ring
    _ ≤ 1 * eta := mul_le_mul_of_nonneg_right hscale heta.le
    _ = eta := one_mul eta

/-- The upper objective at the exact amplified solution is the same hard
hyper-objective used by the zero-chain gap and gradient lemmas. -/
theorem kappaEightFullHardUpper_at_lowerSolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {eta kappa : ℝ}
    (hkappa : 1 < kappa) (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) :
    kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
        (hiddenFrameTranspose J)
        (x, kappaEightPaperLowerSolution eta kappa
          (hiddenFrameTranspose J) x) =
      hardHyperObjective eta kappa J x := by
  rw [kappaEightFullHardUpper_apply]
  change kappaEightHardUpper eta (1 / 4) (hardRadius eta T)
      (hiddenProbe (hardRadius eta T) (hiddenFrameTranspose J))
      (kappa • x)
      (kappaEightAuxSolution kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))) = _
  rw [kappaEightHardUpper_at_proposed_solution hkappa
    (hiddenProbe (hardRadius eta T) (hiddenFrameTranspose J))
    (hardFrontierMap eta (hiddenFrameTranspose J)) x rfl]
  rfl

/-- The concrete amplified problem.  The only value smallness input is the
cutoff-region certificate for the inverse-amplified first coordinate. -/
def kappaEightPaperPopulationProblem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta) :
    KappaEightPopulationProblem E where
  upper := kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
    (hiddenFrameTranspose J)
  lower := kappaEightFullPopulationLower kappa eta
    (hiddenFrameTranspose J)
  lowerSolution := kappaEightPaperLowerSolution eta kappa
    (hiddenFrameTranspose J)
  hyperObjective := hardHyperObjective eta kappa J
  lowerSolution_minimizes := by
    intro x y
    rcases y with ⟨z, v⟩
    simpa only [kappaEightFullPopulationLower_apply,
      kappaEightPaperLowerSolution] using
        kappaEightPopulationLower_minimum hkappa heta
          (hardFrontierMap eta (hiddenFrameTranspose J)) x z v (hsmall x)
  lowerSolution_unique := by
    intro x y hmin
    rcases y with ⟨z, v⟩
    have hmin' :
        kappaEightPopulationLower kappa eta
            (hardFrontierMap eta (hiddenFrameTranspose J)) x z v =
          kappaEightPopulationLower kappa eta
            (hardFrontierMap eta (hiddenFrameTranspose J)) x (kappa • x)
            (kappaEightAuxSolution kappa
              (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))) := by
      simpa only [kappaEightFullPopulationLower_apply,
        kappaEightPaperLowerSolution] using hmin
    have hpair := kappaEightPopulationLower_unique_minimizer hkappa heta
      (hardFrontierMap eta (hiddenFrameTranspose J)) x z v
      (hsmall x) hmin'
    rcases hpair with ⟨hz, hv⟩
    exact Prod.ext hz hv
  hyperObjective_eq := by
    intro x
    symm
    exact kappaEightFullHardUpper_at_lowerSolution hkappa J x

/-- One universal frontier-scale certificate supplies the cutoff-region
hypothesis uniformly over all orthonormal frames. -/
theorem exists_kappaEightPaperPopulationProblem :
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T →
        3 * Ctheta * eta ≤ 1 →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ P : KappaEightPopulationProblem E,
          P.upper = kappaEightFullHardUpper eta (1 / 4)
            (hardRadius eta T) (hiddenFrameTranspose J) ∧
          P.lower = kappaEightFullPopulationLower kappa eta
            (hiddenFrameTranspose J) ∧
          P.lowerSolution = kappaEightPaperLowerSolution eta kappa
            (hiddenFrameTranspose J) ∧
          P.hyperObjective = hardHyperObjective eta kappa J := by
  obtain ⟨Ctheta, hCtheta, hbounds⟩ :=
    exists_frontier_hidden_composition_scales
  refine ⟨Ctheta, hCtheta, ?_⟩
  intro E _ _ _ T eta kappa heta _hetaOne hkappa hT hscale J
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  have hvalue : ∀ z : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) z| ≤
        Ctheta * eta ^ 2 := by
    intro z
    exact (hbounds heta hT hL z).1
  have hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta := by
    intro x
    exact kappaEightCandidateFirst_le_eta_of_scale heta hkappa hCtheta
      hscale hvalue _
  let P := kappaEightPaperPopulationProblem eta kappa J heta
    (by linarith) hsmall
  exact ⟨P, rfl, rfl, rfl, rfl⟩

end

end BilevelLowerBound
