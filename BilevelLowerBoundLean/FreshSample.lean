/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.Oracle
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Fresh Bernoulli samples and conditional oracle laws

This module supplies the measure-theoretic wrapper omitted from the
pointwise calculations in `Oracle`.  The pre-query transcript is represented
by a sub-`sigma`-algebra `past`.  A success event is fresh when the
`sigma`-algebra it generates is independent of `past`.  We prove that its
zero-one indicator has conditional mean `p`, and then prove the full
two-point conditional law for branch values that are measurable with respect
to the past.

The final theorem specializes the two-point law to the paper's compensated
importance-weighted response.  Consequently, even when the query and both
branch responses depend adaptively on the entire past transcript, the next
fresh bit makes the conditional oracle mean equal to the population response.
-/

open Filter Function Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

variable {Ω V : Type*} {mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
  {past : MeasurableSpace Ω}

/-! ## Fresh events and their conditional Bernoulli bit -/

/-- Data expressing that `success` is a Bernoulli event of probability `p`
which is fresh relative to the pre-query information `past`. -/
structure FreshBernoulliEvent
    (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (past : MeasurableSpace Ω)
    (success : Set Ω) (p : ℝ) : Prop where
  past_le : past ≤ mΩ
  measurable_success : MeasurableSet[mΩ] success
  independent : Indep (MeasurableSpace.generateFrom {success}) past μ
  probability : μ.real success = p

/-- The real-valued zero-one bit associated with a success event. -/
def bernoulliBit (success : Set Ω) : Ω → ℝ :=
  success.indicator (fun _ ↦ 1)

theorem bernoulliBit_eq_one {success : Set Ω} {ω : Ω}
    (hω : ω ∈ success) : bernoulliBit success ω = 1 := by
  simp [bernoulliBit, hω]

theorem bernoulliBit_eq_zero {success : Set Ω} {ω : Ω}
    (hω : ω ∉ success) : bernoulliBit success ω = 0 := by
  simp [bernoulliBit, hω]

theorem stronglyMeasurable_bernoulliBit_generated
    (success : Set Ω) :
    StronglyMeasurable[MeasurableSpace.generateFrom {success}]
      (bernoulliBit success) := by
  exact stronglyMeasurable_const.indicator
    (MeasurableSpace.measurableSet_generateFrom (by simp))

theorem integrable_bernoulliBit
    {success : Set Ω} (hsuccess : MeasurableSet[mΩ] success) :
    Integrable (bernoulliBit success) μ := by
  exact (integrable_const (1 : ℝ)).indicator hsuccess

/-- Independence of the new success event from the past turns its ordinary
probability into its conditional probability given the past. -/
theorem FreshBernoulliEvent.condExp_bernoulliBit
    {success : Set Ω} {p : ℝ}
    (hfresh : FreshBernoulliEvent mΩ μ past success p) :
    μ[bernoulliBit success | past] =ᵐ[μ] fun _ ↦ p := by
  have hgenerated_le :
      MeasurableSpace.generateFrom {success} ≤ mΩ := by
    exact MeasurableSpace.generateFrom_le (by
      rintro s rfl
      exact hfresh.measurable_success)
  have hcond := condExp_indep_eq hgenerated_le hfresh.past_le
    (stronglyMeasurable_bernoulliBit_generated success)
    hfresh.independent
  have hintegral : ∫ ω, bernoulliBit success ω ∂μ = μ.real success := by
    simp [bernoulliBit, integral_indicator_const, hfresh.measurable_success]
  rw [hintegral, hfresh.probability] at hcond
  exact hcond

/-! ## Conditional law of a past-measurable two-point response -/

/-- Select the successful or failed response according to the fresh event. -/
def bernoulliSelect
    [AddCommGroup V] [Module ℝ V]
    (success : Set Ω) (valueOne valueZero : Ω → V) : Ω → V :=
  fun ω ↦
    bernoulliBit success ω • valueOne ω +
      (1 - bernoulliBit success ω) • valueZero ω

theorem bernoulliSelect_eq_weighted_sum
    [AddCommGroup V] [Module ℝ V]
    (success : Set Ω) (valueOne valueZero : Ω → V) :
    bernoulliSelect success valueOne valueZero =
      fun ω ↦
        bernoulliBit success ω • valueOne ω +
          (1 - bernoulliBit success ω) • valueZero ω := by
  rfl

omit [IsProbabilityMeasure μ] in
theorem integrable_bernoulliBit_smul
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {success : Set Ω} (hsuccess : MeasurableSet[mΩ] success)
    {value : Ω → V} (hvalue : Integrable value μ) :
    Integrable (fun ω ↦ bernoulliBit success ω • value ω) μ := by
  have hindicator := hvalue.indicator hsuccess
  exact hindicator.congr (by
    filter_upwards with ω
    by_cases hω : ω ∈ success <;>
      simp [bernoulliBit, hω])

omit [IsProbabilityMeasure μ] in
theorem integrable_one_sub_bernoulliBit_smul
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {success : Set Ω} (hsuccess : MeasurableSet[mΩ] success)
    {value : Ω → V} (hvalue : Integrable value μ) :
    Integrable
      (fun ω ↦ (1 - bernoulliBit success ω) • value ω) μ := by
  have hindicator := hvalue.indicator hsuccess.compl
  exact hindicator.congr (by
    filter_upwards with ω
    by_cases hω : ω ∈ success <;>
      simp [bernoulliBit, hω])

theorem FreshBernoulliEvent.condExp_one_sub_bernoulliBit
    {success : Set Ω} {p : ℝ}
    (hfresh : FreshBernoulliEvent mΩ μ past success p) :
    μ[fun ω ↦ 1 - bernoulliBit success ω | past] =ᵐ[μ]
      fun _ ↦ 1 - p := by
  change μ[(fun _ : Ω ↦ (1 : ℝ)) - bernoulliBit success | past] =ᵐ[μ]
    fun _ ↦ 1 - p
  have hbitInt := integrable_bernoulliBit
    (μ := μ) hfresh.measurable_success
  have hsub := condExp_sub (integrable_const (1 : ℝ)) hbitInt past
  have hbit := hfresh.condExp_bernoulliBit
  filter_upwards [hsub, hbit] with ω hsubω hbitω
  rw [hsubω, condExp_const hfresh.past_le]
  simp only [Pi.sub_apply]
  rw [hbitω]

/-- The conditional distribution of a fresh Bernoulli branch remains
`(p, 1-p)` after conditioning on an arbitrary adaptive past.  The branch
values themselves may be random, as long as they are determined by that
past. -/
theorem FreshBernoulliEvent.condExp_bernoulliSelect
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {success : Set Ω} {p : ℝ}
    (hfresh : FreshBernoulliEvent mΩ μ past success p)
    {valueOne valueZero : Ω → V}
    (honeMeas : StronglyMeasurable[past] valueOne)
    (hzeroMeas : StronglyMeasurable[past] valueZero)
    (honeInt : Integrable valueOne μ)
    (hzeroInt : Integrable valueZero μ) :
    μ[bernoulliSelect success valueOne valueZero | past] =ᵐ[μ]
      fun ω ↦ p • valueOne ω + (1 - p) • valueZero ω := by
  let bit : Ω → ℝ := bernoulliBit success
  let notBit : Ω → ℝ := fun ω ↦ 1 - bit ω
  let onePart : Ω → V := fun ω ↦ bit ω • valueOne ω
  let zeroPart : Ω → V := fun ω ↦ notBit ω • valueZero ω
  have hbitInt : Integrable bit μ := by
    exact integrable_bernoulliBit (μ := μ) hfresh.measurable_success
  have hnotBitInt : Integrable notBit μ := by
    exact (integrable_const (1 : ℝ)).sub hbitInt
  have honePartInt : Integrable onePart μ := by
    exact integrable_bernoulliBit_smul
      (μ := μ) hfresh.measurable_success honeInt
  have hzeroPartInt : Integrable zeroPart μ := by
    exact integrable_one_sub_bernoulliBit_smul
      (μ := μ) hfresh.measurable_success hzeroInt
  have honePull :
      μ[onePart | past] =ᵐ[μ]
        fun ω ↦ (μ[bit | past]) ω • valueOne ω := by
    exact condExp_smul_of_aestronglyMeasurable_right hbitInt
      honePartInt honeMeas.aestronglyMeasurable
  have hzeroPull :
      μ[zeroPart | past] =ᵐ[μ]
        fun ω ↦ (μ[notBit | past]) ω • valueZero ω := by
    exact condExp_smul_of_aestronglyMeasurable_right hnotBitInt
      hzeroPartInt hzeroMeas.aestronglyMeasurable
  have hbitCond : μ[bit | past] =ᵐ[μ] fun _ ↦ p := by
    simpa [bit] using hfresh.condExp_bernoulliBit
  have hnotBitCond : μ[notBit | past] =ᵐ[μ] fun _ ↦ 1 - p := by
    simpa [notBit, bit] using hfresh.condExp_one_sub_bernoulliBit
  rw [bernoulliSelect_eq_weighted_sum success valueOne valueZero]
  exact (condExp_add honePartInt hzeroPartInt past).trans <| by
    filter_upwards [honePull, hzeroPull, hbitCond, hnotBitCond] with
      ω honeω hzeroω hbitω hnotBitω
    simp only [Pi.add_apply]
    rw [honeω, hzeroω, hbitω, hnotBitω]

/-! ## Specialization to the importance-weighted hard oracle -/

/-- The adaptive response obtained by feeding a fresh bit into
`importanceSample`. -/
def freshImportanceResponse
    [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (success : Set Ω) (base frontier : Ω → V) : Ω → V :=
  bernoulliSelect success
    (fun ω ↦ importanceSample p 1 (base ω) (frontier ω))
    (fun ω ↦ importanceSample p 0 (base ω) (frontier ω))

theorem freshImportanceResponse_eq_bit
    [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (success : Set Ω) (base frontier : Ω → V) :
    freshImportanceResponse p success base frontier =
      fun ω ↦ importanceSample p (bernoulliBit success ω)
        (base ω) (frontier ω) := by
  funext ω
  by_cases hω : ω ∈ success <;>
    simp [freshImportanceResponse, bernoulliSelect, bernoulliBit, hω]

/-- Freshness justifies the pointwise two-point average used in `Oracle`:
conditional on the complete adaptive past, the importance-weighted sample
has mean `base + frontier`. -/
theorem FreshBernoulliEvent.condExp_freshImportanceResponse
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {success : Set Ω} {p : ℝ} (hp : p ≠ 0)
    (hfresh : FreshBernoulliEvent mΩ μ past success p)
    {base frontier : Ω → V}
    (hbaseMeas : StronglyMeasurable[past] base)
    (hfrontierMeas : StronglyMeasurable[past] frontier)
    (hbaseInt : Integrable base μ)
    (hfrontierInt : Integrable frontier μ) :
    μ[freshImportanceResponse p success base frontier | past] =ᵐ[μ]
      fun ω ↦ base ω + frontier ω := by
  let valueOne : Ω → V := fun ω ↦
    importanceSample p 1 (base ω) (frontier ω)
  let valueZero : Ω → V := fun ω ↦
    importanceSample p 0 (base ω) (frontier ω)
  have honeMeas : StronglyMeasurable[past] valueOne := by
    exact hbaseMeas.add (hfrontierMeas.const_smul (1 / p))
  have hzeroMeas : StronglyMeasurable[past] valueZero := by
    simpa [valueZero, importanceSample] using hbaseMeas
  have honeInt : Integrable valueOne μ := by
    exact hbaseInt.add (hfrontierInt.smul (1 / p))
  have hzeroInt : Integrable valueZero μ := by
    simpa [valueZero, importanceSample] using hbaseInt
  have hselect := hfresh.condExp_bernoulliSelect
    honeMeas hzeroMeas honeInt hzeroInt
  exact hselect.trans <| by
    filter_upwards with ω
    exact bernoulliAverage_importanceSample hp (base ω) (frontier ω)

/-! ## Conditional squared-noise identity -/

theorem norm_sq_importanceSample_sub_population
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p xi : ℝ) (base frontier : V) :
    ‖importanceSample p xi base frontier - (base + frontier)‖ ^ 2 =
      |xi / p - 1| ^ 2 * ‖frontier‖ ^ 2 := by
  rw [importanceSample_sub_population]
  rw [norm_smul, Real.norm_eq_abs]
  ring

/-- Squared deviation of the fresh importance-weighted response from its
population response. -/
def freshImportanceSquaredNoise
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : ℝ) (success : Set Ω) (base frontier : Ω → V) : Ω → ℝ :=
  fun ω ↦
    ‖freshImportanceResponse p success base frontier ω -
      (base ω + frontier ω)‖ ^ 2

/-- The exact conditional second moment of the adaptive stochastic oracle.
The assumption on `norm frontier ^ 2` is the natural square-integrability
condition; in the hard instance it follows from the global `O(eta^2)`
frontier bound already proved in `Oracle`. -/
theorem FreshBernoulliEvent.condExp_freshImportanceSquaredNoise
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {success : Set Ω} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hfresh : FreshBernoulliEvent mΩ μ past success p)
    {base frontier : Ω → V}
    (hbaseMeas : StronglyMeasurable[past] base)
    (hfrontierMeas : StronglyMeasurable[past] frontier)
    (hfrontierSqInt : Integrable (fun ω ↦ ‖frontier ω‖ ^ 2) μ) :
    μ[freshImportanceSquaredNoise p success base frontier | past] =ᵐ[μ]
      fun ω ↦ ((1 - p) / p) * ‖frontier ω‖ ^ 2 := by
  let population : Ω → V := fun ω ↦ base ω + frontier ω
  let valueOne : Ω → V := fun ω ↦
    importanceSample p 1 (base ω) (frontier ω)
  let valueZero : Ω → V := fun ω ↦
    importanceSample p 0 (base ω) (frontier ω)
  let noiseOne : Ω → ℝ := fun ω ↦ ‖valueOne ω - population ω‖ ^ 2
  let noiseZero : Ω → ℝ := fun ω ↦ ‖valueZero ω - population ω‖ ^ 2
  have hpopulationMeas : StronglyMeasurable[past] population :=
    hbaseMeas.add hfrontierMeas
  have hvalueOneMeas : StronglyMeasurable[past] valueOne := by
    exact hbaseMeas.add (hfrontierMeas.const_smul (1 / p))
  have hvalueZeroMeas : StronglyMeasurable[past] valueZero := by
    simpa [valueZero, importanceSample] using hbaseMeas
  have hnoiseOneMeas : StronglyMeasurable[past] noiseOne :=
    (hvalueOneMeas.sub hpopulationMeas).norm.pow 2
  have hnoiseZeroMeas : StronglyMeasurable[past] noiseZero :=
    (hvalueZeroMeas.sub hpopulationMeas).norm.pow 2
  have hnoiseOneInt : Integrable noiseOne μ := by
    have hscaled := hfrontierSqInt.const_mul (|(1 : ℝ) / p - 1| ^ 2)
    exact hscaled.congr <| Eventually.of_forall fun ω ↦ by
      symm
      exact norm_sq_importanceSample_sub_population
        p 1 (base ω) (frontier ω)
  have hnoiseZeroInt : Integrable noiseZero μ := by
    have hscaled := hfrontierSqInt.const_mul (|(0 : ℝ) / p - 1| ^ 2)
    exact hscaled.congr <| Eventually.of_forall fun ω ↦ by
      symm
      exact norm_sq_importanceSample_sub_population
        p 0 (base ω) (frontier ω)
  have hnoiseSelect :
      freshImportanceSquaredNoise p success base frontier =
        bernoulliSelect success noiseOne noiseZero := by
    funext ω
    by_cases hω : ω ∈ success <;>
      simp [freshImportanceSquaredNoise, freshImportanceResponse,
        bernoulliSelect, bernoulliBit, population, valueOne, valueZero,
        noiseOne, noiseZero, hω]
  rw [hnoiseSelect]
  have hselect := hfresh.condExp_bernoulliSelect
    hnoiseOneMeas hnoiseZeroMeas hnoiseOneInt hnoiseZeroInt
  exact hselect.trans <| by
    filter_upwards with ω
    simpa [noiseOne, noiseZero, population, valueOne, valueZero,
      bernoulliSquaredNoise, smul_eq_mul] using
      bernoulliSquaredNoise_importanceSample hp hp1
        (base ω) (frontier ω)

end

end BilevelLowerBound
