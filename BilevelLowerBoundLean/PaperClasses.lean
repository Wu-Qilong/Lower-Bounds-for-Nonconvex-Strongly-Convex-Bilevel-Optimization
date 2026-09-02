/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FreshSample
import BilevelLowerBoundLean.FullPopulationRegularity

/-!
# Concrete problem, oracle, and algorithm classes used by the paper

This file replaces the abstract placeholders used by the first version of the
outer-quantifier wrapper.  The definitions below are direct Frechet-derivative
versions of the paper's population NC--SC class, two-point fresh stochastic
first-order oracle, and randomized adaptive first-order algorithm.

The hard lower bound only needs a Bernoulli oracle.  This is a subclass of the
paper's general fresh-sample SFO class: pointwise two-point mean and variance
identities are lifted to adaptive conditional identities in `FreshSample.lean`.
-/

open Function MeasureTheory Set
open scoped ContDiff ENNReal MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- The paper uses an upper variable `x : E` and lower variables `(z,v)`. -/
abbrev PaperLowerPoint (E : Type*) := E × ℝ

/-- A joint bilevel query `(x,z,v)`. -/
abbrev PaperQueryPoint (E : Type*) := E × PaperLowerPoint E

/-- First-order responses are represented by Frechet derivatives.  In a real
Hilbert space these are canonically equivalent to the gradient vectors used in
the paper. -/
abbrev PaperGradientResponse (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (PaperQueryPoint E →L[ℝ] ℝ) × (PaperQueryPoint E →L[ℝ] ℝ)

/-- A population bilevel problem together with its exact lower solution and
the resulting hyper-objective.  The two identity fields prevent a purported
certificate from silently using a different lower solution or objective. -/
structure PaperPopulationProblem
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  upper : PaperQueryPoint E → ℝ
  lower : PaperQueryPoint E → ℝ
  lowerSolution : E → PaperLowerPoint E
  hyperObjective : E → ℝ
  lowerSolution_minimizes : ∀ x y,
    lower (x, lowerSolution x) ≤ lower (x, y)
  lowerSolution_unique : ∀ x y,
    lower (x, y) = lower (x, lowerSolution x) → y = lowerSolution x
  hyperObjective_eq : ∀ x,
    hyperObjective x = upper (x, lowerSolution x)

/-- Global Lipschitz continuity of the gradient of a scalar function. -/
def HasGloballyLipschitzGradient
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : F → ℝ) (L : ℝ) : Prop :=
  ContDiff ℝ 1 h ∧
    ∀ x y, ‖fderiv ℝ h y - fderiv ℝ h x‖ ≤ L * ‖y - x‖

/-- Global Lipschitz continuity of the full Hessian. -/
def HasGloballyLipschitzHessian
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : F → ℝ) (rho : ℝ) : Prop :=
  ContDiff ℝ 2 h ∧
    ∀ x y,
      ‖iteratedFDeriv ℝ 2 h y - iteratedFDeriv ℝ 2 h x‖ ≤
        rho * ‖y - x‖

/-- Directional-Hessian form of strong convexity in the lower variables. -/
def HasUniformLowerStrongConvexity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : PaperQueryPoint E → ℝ) (muG : ℝ) : Prop :=
  ∀ x y w,
    muG * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2 (fun u : PaperLowerPoint E ↦ g (x, u)) y
        (fun _ ↦ w)

/-- The paper's bounded `nabla_y f` condition. -/
def HasBoundedUpperLowerDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : PaperQueryPoint E → ℝ) (C : ℝ) : Prop :=
  ∀ x y, ‖fderiv ℝ (fun u : PaperLowerPoint E ↦ f (x, u)) y‖ ≤ C

/-- Membership in the population NC--SC class from Definition 3.1 of the
paper.  The lower-solution and hyper-objective identities are part of
`PaperPopulationProblem`, so the gap condition refers to the actual bilevel
hyper-objective. -/
structure PaperPopulationClassMember
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : PaperPopulationProblem E)
    (Lf Lg rho Cf muG Delta : ℝ) : Prop where
  upper_gradient_lipschitz : HasGloballyLipschitzGradient P.upper Lf
  lower_gradient_lipschitz : HasGloballyLipschitzGradient P.lower Lg
  lower_strongly_convex : HasUniformLowerStrongConvexity P.lower muG
  lower_hessian_lipschitz : HasGloballyLipschitzHessian P.lower rho
  upper_lower_derivative_bounded : HasBoundedUpperLowerDerivative P.upper Cf
  hyper_bddBelow : BddBelow (Set.range P.hyperObjective)
  initial_gap :
    P.hyperObjective 0 - sInf (Set.range P.hyperObjective) ≤ Delta

/-- Sharp intrinsic lower-level modulus and smoothness data used to define the
actual condition number `kappa_y`. -/
structure PaperLowerConditionData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : PaperPopulationProblem E) where
  muGAct : ℝ
  Ly : ℝ
  muGAct_pos : 0 < muGAct
  muGAct_sharp :
    IsSharpLowerHessianModulus
      (fun x y ↦ P.lower (x, y)) muGAct
  Ly_sharp :
    IsSharpLowerHessianUpperBound
      (fun x y ↦ P.lower (x, y)) Ly

/-- The intrinsic lower-level condition number. -/
def PaperLowerConditionData.kappaY
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : PaperPopulationProblem E} (data : PaperLowerConditionData P) : ℝ :=
  data.Ly / data.muGAct

/-- Definition 3.2's compatibility inequality: the certified class modulus
`muG` cannot exceed the actual sharp lower curvature `muGAct`. -/
theorem PaperPopulationClassMember.muG_le_muGAct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : PaperPopulationProblem E}
    {Lf Lg rho Cf muG Delta : ℝ}
    (h : PaperPopulationClassMember P Lf Lg rho Cf muG Delta)
    (data : PaperLowerConditionData P) :
    muG ≤ data.muGAct := by
  apply data.muGAct_sharp.2 muG
  intro x y w
  exact h.lower_strongly_convex x y w

/-! ## Concrete Bernoulli fresh-SFO class -/

/-- A two-point stochastic first-order oracle for a fixed population problem.
The branch `true` is the successful Bernoulli response. -/
structure PaperBernoulliSFO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : PaperPopulationProblem E) where
  probability : ℝ
  response : Bool → PaperQueryPoint E → PaperGradientResponse E

/-- Pointwise oracle membership.  Fresh independent sampling lifts these
identities to the conditional laws at every adaptive random query. -/
structure PaperBernoulliSFOMember
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : PaperPopulationProblem E}
    (O : PaperBernoulliSFO P) (sigma : ℝ) : Prop where
  probability_pos : 0 < O.probability
  probability_le_one : O.probability ≤ 1
  upper_mean : ∀ a,
    bernoulliAverage O.probability
        (O.response true a).1 (O.response false a).1 =
      fderiv ℝ P.upper a
  lower_mean : ∀ a,
    bernoulliAverage O.probability
        (O.response true a).2 (O.response false a).2 =
      fderiv ℝ P.lower a
  upper_variance : ∀ a,
    bernoulliSquaredNoise O.probability
        (O.response true a).1 (O.response false a).1
        (fderiv ℝ P.upper a) ≤ sigma ^ 2
  lower_variance : ∀ a,
    bernoulliSquaredNoise O.probability
        (O.response true a).2 (O.response false a).2
        (fderiv ℝ P.lower a) ≤ sigma ^ 2

/-! ## Randomized adaptive algorithms -/

/-- Original query--response transcript.  Using lists gives one common
standard-Borel carrier; the recursion invariant records the exact length. -/
abbrev PaperOriginalTranscript
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  List (PaperQueryPoint E × PaperGradientResponse E)

/-- The product sigma-algebra generated by the two coordinate projections.
It is written explicitly because the transcript sigma-algebra is data of the
algorithm rather than a globally installed typeclass instance. -/
@[instance_reducible]
def explicitProductMeasurableSpace
    {α β : Type*} (mα : MeasurableSpace α) (mβ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  MeasurableSpace.comap Prod.fst mα ⊔
    MeasurableSpace.comap Prod.snd mβ

/-- Measurability with explicitly supplied domain and codomain
sigma-algebras. -/
def MeasurableWith
    {α β : Type*} (mα : MeasurableSpace α) (mβ : MeasurableSpace β)
    (f : α → β) : Prop :=
  @Measurable α β mα mβ f

/-- A randomized adaptive first-order algorithm with a fixed master-seed
space.  This is the paper's Borel query/output-map definition. -/
structure PaperAdaptiveAlgorithm
    (N : ℕ) (E Seed : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed] where
  seedMeasure : Measure Seed
  seedProbability : IsProbabilityMeasure seedMeasure
  transcriptMeasurableSpace : MeasurableSpace (PaperOriginalTranscript E)
  query : Fin N → Seed → PaperOriginalTranscript E → PaperQueryPoint E
  output : Seed → PaperOriginalTranscript E → E
  query_measurable : ∀ t,
    MeasurableWith
      (explicitProductMeasurableSpace
        (inferInstance : MeasurableSpace Seed)
        transcriptMeasurableSpace)
      (inferInstance : MeasurableSpace (PaperQueryPoint E))
      (Function.uncurry (query t))
  output_measurable :
    MeasurableWith
      (explicitProductMeasurableSpace
        (inferInstance : MeasurableSpace Seed)
        transcriptMeasurableSpace)
      (inferInstance : MeasurableSpace E)
      (Function.uncurry output)

end

end BilevelLowerBound
