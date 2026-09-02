/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightAmplifier

/-!
# The amplified two-coordinate bilevel hard pair

This module defines a new hard pair, independent of the scalar auxiliary hard
pair used for the earlier `kappa^6` result.  It proves the Bernoulli population
identity, the exact global lower solution, uniqueness of that solution, and
the exact population hyper-objective identity.
-/

open scoped ContDiff RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-- The compensated frontier term as a function of the lower pair `(z,v)`. -/
def kappaEightCompensatedPair
    {E : Type*} (eta kappa : ℝ) (theta : E → ℝ)
    (p : E × AmplifierAux) : ℝ :=
  amplifiedCompensation eta kappa (theta p.1) p.2

/-- Population lower objective of the amplified hard pair. -/
def kappaEightPopulationLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa eta : ℝ) (theta : E → ℝ) (x z : E)
    (v : AmplifierAux) : ℝ :=
  ‖z‖ ^ 2 / (2 * kappa) - inner ℝ x z +
    amplifiedScalarBlock eta kappa (theta z) v

/-- Sample lower objective.  The complete compensated frontier block is
importance weighted; the base quadratic is always visible. -/
def kappaEightSampleLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa eta prob xi : ℝ) (theta : E → ℝ) (x z : E)
    (v : AmplifierAux) : ℝ :=
  ‖z‖ ^ 2 / (2 * kappa) - inner ℝ x z +
    amplifierQuadratic kappa v +
      (xi / prob) * amplifiedCompensation eta kappa (theta z) v

/-- The upper objective reads the second amplified coordinate linearly. -/
def kappaEightHardUpper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (eta lam R : ℝ) (q : E → ChainVector T)
    (z : E) (v : AmplifierAux) : ℝ :=
  visibleChain eta (q z) + v.2 + pseudoHuber lam R z

/-- Exact expectation of the Bernoulli sample lower objective. -/
theorem kappaEightSampleLower_bernoulli_population
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta prob : ℝ} (hprob : prob ≠ 0)
    (theta : E → ℝ) (x z : E) (v : AmplifierAux) :
    prob * kappaEightSampleLower kappa eta prob 1 theta x z v +
        (1 - prob) * kappaEightSampleLower kappa eta prob 0 theta x z v =
      kappaEightPopulationLower kappa eta theta x z v := by
  unfold kappaEightSampleLower kappaEightPopulationLower
    amplifiedScalarBlock
  field_simp [hprob]
  ring

/-- Completing the square separates the upper-to-lower coupling from the
globally nonnegative two-coordinate auxiliary block. -/
theorem kappaEightPopulationLower_complete_square
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : kappa ≠ 0)
    (theta : E → ℝ) (x z : E) (v : AmplifierAux) :
    kappaEightPopulationLower kappa eta theta x z v =
      -(kappa / 2) * ‖x‖ ^ 2 +
        ‖z - kappa • x‖ ^ 2 / (2 * kappa) +
          amplifiedScalarBlock eta kappa (theta z) v := by
  unfold kappaEightPopulationLower
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_right, mul_pow, sq_abs, real_inner_comm x z]
  field_simp [hkappa]
  ring

/-- The exact amplified auxiliary solution at a scalar frontier value. -/
def kappaEightAuxSolution (kappa theta : ℝ) : AmplifierAux :=
  (amplifierDiag kappa * attenuatedFrontier kappa theta,
    amplifierOffDiag kappa * attenuatedFrontier kappa theta)

@[simp]
theorem kappaEightAuxSolution_fst (kappa theta : ℝ) :
    (kappaEightAuxSolution kappa theta).1 =
      amplifierDiag kappa * attenuatedFrontier kappa theta := rfl

@[simp]
theorem kappaEightAuxSolution_snd
    {kappa theta : ℝ} (hkappa : 1 < kappa) :
    (kappaEightAuxSolution kappa theta).2 = theta := by
  exact amplified_proposed_second_coordinate hkappa

/-- Value of the population lower objective at the proposed exact solution. -/
theorem kappaEightPopulationLower_at_proposed_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 < kappa) (heta : 0 < eta)
    (theta : E → ℝ) (x : E)
    (hsmall :
      |amplifierDiag kappa *
        attenuatedFrontier kappa (theta (kappa • x))| ≤ eta) :
    kappaEightPopulationLower kappa eta theta x (kappa • x)
        (kappaEightAuxSolution kappa (theta (kappa • x))) =
      -(kappa / 2) * ‖x‖ ^ 2 := by
  rw [kappaEightPopulationLower_complete_square (by linarith) theta]
  have haux : amplifiedScalarBlock eta kappa (theta (kappa • x))
      (kappaEightAuxSolution kappa (theta (kappa • x))) = 0 := by
    simpa [kappaEightAuxSolution] using
      (amplifiedScalarBlock_at_proposed heta hkappa hsmall)
  rw [haux]
  simp

/-- The proposed lower point is a global minimizer. -/
theorem kappaEightPopulationLower_minimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 < kappa) (heta : 0 < eta)
    (theta : E → ℝ) (x z : E) (v : AmplifierAux)
    (hsmall :
      |amplifierDiag kappa *
        attenuatedFrontier kappa (theta (kappa • x))| ≤ eta) :
    kappaEightPopulationLower kappa eta theta x (kappa • x)
        (kappaEightAuxSolution kappa (theta (kappa • x))) ≤
      kappaEightPopulationLower kappa eta theta x z v := by
  rw [kappaEightPopulationLower_at_proposed_solution hkappa heta theta x hsmall,
    kappaEightPopulationLower_complete_square (by linarith) theta]
  have hquad : 0 ≤ ‖z - kappa • x‖ ^ 2 / (2 * kappa) := by
    positivity
  have haux := amplifiedScalarBlock_nonneg
    (eta := eta) (theta := theta z) hkappa v
  linarith

/-- Equality with the proposed value forces both lower components to equal
the exact solution. -/
theorem kappaEightPopulationLower_unique_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 < kappa) (heta : 0 < eta)
    (theta : E → ℝ) (x z : E) (v : AmplifierAux)
    (hsmall :
      |amplifierDiag kappa *
        attenuatedFrontier kappa (theta (kappa • x))| ≤ eta)
    (hmin : kappaEightPopulationLower kappa eta theta x z v =
      kappaEightPopulationLower kappa eta theta x (kappa • x)
        (kappaEightAuxSolution kappa (theta (kappa • x)))) :
    z = kappa • x ∧
      v = kappaEightAuxSolution kappa (theta (kappa • x)) := by
  rw [kappaEightPopulationLower_complete_square (by linarith) theta,
    kappaEightPopulationLower_at_proposed_solution hkappa heta theta x hsmall]
      at hmin
  have hquad : 0 ≤ ‖z - kappa • x‖ ^ 2 / (2 * kappa) := by
    positivity
  have haux := amplifiedScalarBlock_nonneg
    (eta := eta) (theta := theta z) hkappa v
  have hquadZero : ‖z - kappa • x‖ ^ 2 / (2 * kappa) = 0 := by
    linarith
  have hnormZero : ‖z - kappa • x‖ = 0 := by
    have hden : (2 * kappa) ≠ 0 := by positivity
    have hsquare : ‖z - kappa • x‖ ^ 2 = 0 :=
      (div_eq_zero_iff.mp hquadZero).resolve_right hden
    exact sq_eq_zero_iff.mp hsquare
  have hz : z = kappa • x :=
    sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  have hauxZero : amplifiedScalarBlock eta kappa (theta z) v = 0 := by
    linarith
  have hvFirst := amplifiedScalarBlock_eq_zero_imp_first hkappa hauxZero
  have hvSecond := amplifiedScalarBlock_eq_zero_imp_second hkappa hauxZero
  refine ⟨hz, ?_⟩
  apply Prod.ext
  · simpa [kappaEightAuxSolution, hz] using hvFirst
  · simpa [kappaEightAuxSolution, hz] using hvSecond

/-- Substituting the exact lower solution restores the unattenuated frontier
in the upper objective. -/
theorem kappaEightHardUpper_at_proposed_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {eta kappa lam R : ℝ} (hkappa : 1 < kappa)
    (q : E → ChainVector T) (theta : E → ℝ) (x : E)
    (hsplit : theta (kappa • x) =
      frontierExtractor eta (q (kappa • x))) :
    kappaEightHardUpper eta lam R q (kappa • x)
        (kappaEightAuxSolution kappa (theta (kappa • x))) =
      scaledChain eta (q (kappa • x)) + pseudoHuber lam R (kappa • x) := by
  unfold kappaEightHardUpper visibleChain
  rw [kappaEightAuxSolution_snd hkappa, hsplit]
  ring

end

end BilevelLowerBound
