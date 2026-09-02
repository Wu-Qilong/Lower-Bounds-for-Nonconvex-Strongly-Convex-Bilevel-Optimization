/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightHardInstance
import BilevelLowerBoundLean.PaperClasses

/-!
# Concrete classes for the two-coordinate amplified hard pair

These definitions deliberately live in a separate namespace of declarations
from the scalar-auxiliary project.  The lower point is `E × (R × R)`, so a
compiled theorem in this file cannot accidentally be discharged by the old
one-coordinate hard instance.
-/

open Function MeasureTheory Set
open scoped ContDiff ENNReal MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- Lower variable `(z,(v1,v2))` of the amplified hard pair. -/
abbrev KappaEightLowerPoint (E : Type*) := E × AmplifierAux

/-- Joint query `(x,z,v1,v2)`. -/
abbrev KappaEightQueryPoint (E : Type*) := E × KappaEightLowerPoint E

/-- Paired upper- and lower-gradient responses. -/
abbrev KappaEightGradientResponse (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (KappaEightQueryPoint E →L[ℝ] ℝ) ×
    (KappaEightQueryPoint E →L[ℝ] ℝ)

/-- A concrete amplified population bilevel problem, including proof that
the recorded lower solution and hyper-objective are the actual ones. -/
structure KappaEightPopulationProblem
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  upper : KappaEightQueryPoint E → ℝ
  lower : KappaEightQueryPoint E → ℝ
  lowerSolution : E → KappaEightLowerPoint E
  hyperObjective : E → ℝ
  lowerSolution_minimizes : ∀ x y,
    lower (x, lowerSolution x) ≤ lower (x, y)
  lowerSolution_unique : ∀ x y,
    lower (x, y) = lower (x, lowerSolution x) → y = lowerSolution x
  hyperObjective_eq : ∀ x,
    hyperObjective x = upper (x, lowerSolution x)

/-- Directional-Hessian lower strong-convexity certificate for the amplified
lower variable. -/
def KappaEightHasUniformLowerStrongConvexity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : KappaEightQueryPoint E → ℝ) (muG : ℝ) : Prop :=
  ∀ x y w,
    muG * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2
        (fun u : KappaEightLowerPoint E ↦ g (x, u)) y
        (fun _ ↦ w)

/-- Bounded lower-variable derivative of the upper population objective. -/
def KappaEightHasBoundedUpperLowerDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : KappaEightQueryPoint E → ℝ) (C : ℝ) : Prop :=
  ∀ x y,
    ‖fderiv ℝ (fun u : KappaEightLowerPoint E ↦ f (x, u)) y‖ ≤ C

/-- Population NC--SC class for the two-coordinate hard pair. -/
structure KappaEightPopulationClassMember
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : KappaEightPopulationProblem E)
    (Lf Lg rho Cf muG Delta : ℝ) : Prop where
  upper_gradient_lipschitz : HasGloballyLipschitzGradient P.upper Lf
  lower_gradient_lipschitz : HasGloballyLipschitzGradient P.lower Lg
  lower_strongly_convex :
    KappaEightHasUniformLowerStrongConvexity P.lower muG
  lower_hessian_lipschitz : HasGloballyLipschitzHessian P.lower rho
  upper_lower_derivative_bounded :
    KappaEightHasBoundedUpperLowerDerivative P.upper Cf
  hyper_bddBelow : BddBelow (Set.range P.hyperObjective)
  initial_gap :
    P.hyperObjective 0 - sInf (Set.range P.hyperObjective) ≤ Delta

/-- Sharp lower Hessian modulus for a two-coordinate lower point. -/
def KappaEightIsSharpLowerHessianModulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → KappaEightLowerPoint E → ℝ) (muGAct : ℝ) : Prop :=
  0 < muGAct ∧
    (∀ x y w,
      muGAct * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (g x) y (fun _ ↦ w)) ∧
    ∀ muGAct' : ℝ,
      (∀ x y w,
        muGAct' * ‖w‖ ^ 2 ≤
          iteratedFDeriv ℝ 2 (g x) y (fun _ ↦ w)) →
      muGAct' ≤ muGAct

/-- Sharp global Hessian upper bound for a two-coordinate lower point. -/
def KappaEightIsSharpLowerHessianUpperBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → KappaEightLowerPoint E → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 (g x) y‖ ≤ L) ∧
    ∀ L' : ℝ,
      (∀ x y, ‖iteratedFDeriv ℝ 2 (g x) y‖ ≤ L') →
      L ≤ L'

/-- Intrinsic condition data for the actual lower population objective. -/
structure KappaEightLowerConditionData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : KappaEightPopulationProblem E) where
  muGAct : ℝ
  Ly : ℝ
  muGAct_pos : 0 < muGAct
  muGAct_sharp : KappaEightIsSharpLowerHessianModulus
    (fun x y ↦ P.lower (x, y)) muGAct
  Ly_sharp : KappaEightIsSharpLowerHessianUpperBound
    (fun x y ↦ P.lower (x, y)) Ly

def KappaEightLowerConditionData.kappaY
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : KappaEightPopulationProblem E}
    (data : KappaEightLowerConditionData P) : ℝ :=
  data.Ly / data.muGAct

/-- Definition 3.2's compatibility inequality: the certified class modulus
`muG` cannot exceed the actual sharp lower curvature `muGAct`. -/
theorem KappaEightPopulationClassMember.muG_le_muGAct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : KappaEightPopulationProblem E}
    {Lf Lg rho Cf muG Delta : ℝ}
    (h : KappaEightPopulationClassMember P Lf Lg rho Cf muG Delta)
    (data : KappaEightLowerConditionData P) :
    muG ≤ data.muGAct := by
  apply data.muGAct_sharp.2.2 muG
  intro x y w
  exact h.lower_strongly_convex x y w

/-! ## Two-point fresh stochastic first-order oracle -/

structure KappaEightBernoulliSFO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : KappaEightPopulationProblem E) where
  probability : ℝ
  response : Bool → KappaEightQueryPoint E → KappaEightGradientResponse E

structure KappaEightBernoulliSFOMember
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : KappaEightPopulationProblem E}
    (O : KappaEightBernoulliSFO P) (sigma : ℝ) : Prop where
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

/-! ## Randomized adaptive first-order algorithms -/

abbrev KappaEightOriginalTranscript
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  List (KappaEightQueryPoint E × KappaEightGradientResponse E)

/-- Borel adaptive algorithm on the amplified query and response spaces. -/
structure KappaEightAdaptiveAlgorithm
    (N : ℕ) (E Seed : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed] where
  seedMeasure : Measure Seed
  seedProbability : IsProbabilityMeasure seedMeasure
  transcriptMeasurableSpace :
    MeasurableSpace (KappaEightOriginalTranscript E)
  query : Fin N → Seed → KappaEightOriginalTranscript E →
    KappaEightQueryPoint E
  output : Seed → KappaEightOriginalTranscript E → E
  query_measurable : ∀ t,
    MeasurableWith
      (explicitProductMeasurableSpace
        (inferInstance : MeasurableSpace Seed)
        transcriptMeasurableSpace)
      (inferInstance : MeasurableSpace (KappaEightQueryPoint E))
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
