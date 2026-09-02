/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.HaarGeometry
import Mathlib.Probability.ConditionalExpectation

/-!
# Probability bookkeeping for the adaptive Haar argument

The paper imports two genuinely geometric facts from the adaptive
random-rotation literature: conditional Haar invariance of an unexposed
column and the corresponding spherical-cap estimate.  This module does not
silently turn those cited inputs into axioms.  Instead, `ConditionalEventBound`
records exactly the conditional estimate which the cited result must supply.

Lean then verifies the remaining probability argument: integrating removes
the conditioning, a finite union costs at most the sum of the individual
probabilities, and an inclusion of the Haar failure event in that union gives
the claimed global failure budget.
-/

open Filter Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]

/-- The output required from a conditional spherical-cap argument for one
bad event.  The field `conditional_le` is a pointwise-a.e. upper bound on its
conditional probability given the information available before the still
unexposed Haar direction is sampled. -/
structure ConditionalEventBound
    (μ : @Measure Ω mΩ) (info : MeasurableSpace Ω)
    (event : Set Ω) (q : ℝ) : Prop where
  info_le : info ≤ mΩ
  measurable_event : MeasurableSet[mΩ] event
  conditional_le :
    μ[event.indicator (fun _ ↦ (1 : ℝ)) | info] ≤ᵐ[μ]
      fun _ ↦ q

/-- Law of total probability: a conditional cap bound implies the same
unconditional probability bound. -/
theorem ConditionalEventBound.measureReal_le
    {info : MeasurableSpace Ω} {event : Set Ω} {q : ℝ}
    (h : ConditionalEventBound μ info event q) :
    μ.real event ≤ q := by
  have hmono :
      (∫ ω, (μ[event.indicator (fun _ ↦ (1 : ℝ)) | info]) ω ∂μ) ≤
        ∫ _ω, q ∂μ :=
    integral_mono_ae integrable_condExp (integrable_const q)
      h.conditional_le
  rw [integral_condExp h.info_le] at hmono
  have hindicator :
      (∫ ω, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) =
        μ.real event := by
    simpa using
      (integral_indicator_const (μ := μ) (1 : ℝ) h.measurable_event)
  rw [hindicator] at hmono
  simpa using hmono

/-! ## Finite unions of cap events -/

/-- Fixed padding index for the adaptive cap events.  The three coordinates
represent the probe index, the padded residual-basis index, and the hidden
frame-column index.  Inactive triples are represented by empty events. -/
abbrev PaddedCapIndex (n T : ℕ) := Fin n × Fin n × Fin T

@[simp]
theorem card_paddedCapIndex (n T : ℕ) :
    Fintype.card (PaddedCapIndex n T) = n ^ 2 * T := by
  simp [PaddedCapIndex, pow_two, mul_assoc]

/- The probability of a finite union of events, each of probability at most
`q`, is at most `card(I) * q`.  No independence between the cap events is
needed. -/
omit [IsProbabilityMeasure μ] in
theorem measureReal_iUnion_le_card_mul
    {I : Type*} [Fintype I] (event : I → Set Ω) {q : ℝ}
    (hevent : ∀ i, μ.real (event i) ≤ q) :
    μ.real (⋃ i, event i) ≤ (Fintype.card I : ℝ) * q := by
  calc
    μ.real (⋃ i, event i) ≤ ∑ i, μ.real (event i) :=
      measureReal_iUnion_fintype_le event
    _ ≤ ∑ _i : I, q := Finset.sum_le_sum fun i _ ↦ hevent i
    _ = (Fintype.card I : ℝ) * q := by simp

/-- Conditional cap bounds may use a different pre-column information
sigma-algebra for each event.  After removing every conditioning, the same
finite-union estimate applies. -/
theorem measureReal_iUnion_le_of_conditionalEventBounds
    {I : Type*} [Fintype I]
    (info : I → MeasurableSpace Ω) (event : I → Set Ω) {q : ℝ}
    (hcap : ∀ i, ConditionalEventBound μ (info i) (event i) q) :
    μ.real (⋃ i, event i) ≤ (Fintype.card I : ℝ) * q := by
  apply measureReal_iUnion_le_card_mul event
  intro i
  exact (hcap i).measureReal_le

/-- Complete union-bound wrapper for Step 5 of the Haar proof.  The
geometric argument only has to show that `failure` is contained in the union
of the indexed cap events and that the resulting cardinality-times-cap
probability fits inside `delta`. -/
theorem measureReal_failure_le_of_conditional_cap_union
    {I : Type*} [Fintype I]
    (info : I → MeasurableSpace Ω) (event : I → Set Ω)
    (failure : Set Ω) {q δ : ℝ}
    (hfailure : failure ⊆ ⋃ i, event i)
    (hcap : ∀ i, ConditionalEventBound μ (info i) (event i) q)
    (hbudget : (Fintype.card I : ℝ) * q ≤ δ) :
    μ.real failure ≤ δ := by
  calc
    μ.real failure ≤ μ.real (⋃ i, event i) :=
      measureReal_mono hfailure
    _ ≤ (Fintype.card I : ℝ) * q :=
      measureReal_iUnion_le_of_conditionalEventBounds info event hcap
    _ ≤ δ := hbudget

/-! ## Failure and success probabilities -/

/-- Under a probability measure, a failure bound by `delta` gives success
probability at least `1-delta`. -/
theorem measureReal_compl_ge_one_sub
    {failure : Set Ω} (hfailure : MeasurableSet[mΩ] failure)
    {δ : ℝ} (hδ : μ.real failure ≤ δ) :
    1 - δ ≤ μ.real failureᶜ := by
  rw [measureReal_compl hfailure]
  rw [probReal_univ]
  exact sub_le_sub_left hδ 1

/-- Final probability wrapper in the form used by the paper: outside the
union of all cap events the deterministic geometry proves the desired Haar
conclusion, hence that conclusion holds with probability at least
`1-delta`. -/
theorem measureReal_good_ge_one_sub_of_conditional_cap_union
    {I : Type*} [Fintype I]
    (info : I → MeasurableSpace Ω) (event : I → Set Ω)
    (failure : Set Ω) {q δ : ℝ}
    (hfailureMeas : MeasurableSet[mΩ] failure)
    (hfailure : failure ⊆ ⋃ i, event i)
    (hcap : ∀ i, ConditionalEventBound μ (info i) (event i) q)
    (hbudget : (Fintype.card I : ℝ) * q ≤ δ) :
    1 - δ ≤ μ.real failureᶜ := by
  apply measureReal_compl_ge_one_sub hfailureMeas
  exact measureReal_failure_le_of_conditional_cap_union
    info event failure hfailure hcap hbudget

/-! ## Connection to the Haar progress event -/

/-- The connection theorem used by the main lower-bound assembly.

The cited conditional-Haar and spherical-cap estimate supplies one
`ConditionalEventBound` for every fixed padded triple `(t,s,j)`.  The
deterministic geometric part of the proof supplies `hprogress`: if none of
these cap events occurs, then the output progress is bounded by the capped
success count.  This theorem constructs the single event `haarGood`, proves
its failure probability bound by a fixed finite union, and returns exactly
the pointwise progress implication needed by `output_unfinished_probability`.
-/
theorem adaptiveHaarConnection
    {n T : ℕ}
    (info : PaddedCapIndex n T → MeasurableSpace Ω)
    (event : PaddedCapIndex n T → Set Ω) {q δ : ℝ}
    (hcap : ∀ i, ConditionalEventBound μ (info i) (event i) q)
    (hbudget : ((n ^ 2 * T : ℕ) : ℝ) * q ≤ δ)
    (outputProgress successCount : Ω → ℕ)
    (hprogress : ∀ ω, (∀ i, ω ∉ event i) →
      outputProgress ω ≤ min T (successCount ω)) :
    ∃ haarGood : Set Ω,
      MeasurableSet[mΩ] haarGood ∧
      μ.real haarGoodᶜ ≤ δ ∧
      ∀ ω ∈ haarGood,
        outputProgress ω ≤ min T (successCount ω) := by
  let failure : Set Ω := ⋃ i, event i
  have hfailureMeas : MeasurableSet[mΩ] failure := by
    dsimp only [failure]
    exact MeasurableSet.iUnion fun i ↦ (hcap i).measurable_event
  have hbudget' :
      (Fintype.card (PaddedCapIndex n T) : ℝ) * q ≤ δ := by
    simpa only [card_paddedCapIndex] using hbudget
  have hfailure : μ.real failure ≤ δ := by
    apply measureReal_failure_le_of_conditional_cap_union
      info event failure (q := q)
    · exact Set.Subset.rfl
    · exact hcap
    · exact hbudget'
  refine ⟨failureᶜ, hfailureMeas.compl, ?_, ?_⟩
  · simpa only [compl_compl] using hfailure
  · intro ω hω
    apply hprogress ω
    intro i hi
    exact hω (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-! ## The scalar dimension-to-cap calculation -/

/-- Exponentiating a lower bound by `log(2 K / delta)` gives the cap
probability `delta / K`. -/
theorem two_mul_exp_neg_le_div_of_log_le
    {a K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hlog : Real.log (2 * K / δ) ≤ a) :
    2 * Real.exp (-a) ≤ δ / K := by
  have hx : 0 < 2 * K / δ := by positivity
  have hexp :
      Real.exp (-a) ≤ Real.exp (-Real.log (2 * K / δ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hlog)
  calc
    2 * Real.exp (-a) ≤
        2 * Real.exp (-Real.log (2 * K / δ)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = δ / K := by
      rw [Real.exp_neg, Real.exp_log hx]
      field_simp

/-- Exact square of the scalar threshold used in the Haar proof. -/
theorem capThreshold_sq
    {R n : ℝ} (hR : 0 < R) (hn : 0 < n) :
    (1 / (4 * R * Real.sqrt n)) ^ 2 =
      1 / (16 * R ^ 2 * n) := by
  have hsqrt : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  field_simp [hR.ne', (Real.sqrt_pos.2 hn).ne']
  nlinarith

/-- The concrete dimension margin in Step 5 makes the spherical-cap
exponent at least `log(2 K / delta)`. -/
theorem capExponent_ge_log_of_dimension
    {c R n D K δ : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hn : 0 < n)
    (hdimension :
      (16 / c) * R ^ 2 * n * Real.log (2 * K / δ) ≤ D) :
    Real.log (2 * K / δ) ≤
      c * D * (1 / (4 * R * Real.sqrt n)) ^ 2 := by
  have hscale : 0 ≤ c / (16 * R ^ 2 * n) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdimension hscale
  rw [capThreshold_sq hR hn]
  have hcne : c ≠ 0 := hc.ne'
  have hRne : R ≠ 0 := hR.ne'
  have hnne : n ≠ 0 := hn.ne'
  calc
    Real.log (2 * K / δ) =
        (c / (16 * R ^ 2 * n)) *
          ((16 / c) * R ^ 2 * n * Real.log (2 * K / δ)) := by
      field_simp
    _ ≤ (c / (16 * R ^ 2 * n)) * D := hmul
    _ = c * D * (1 / (16 * R ^ 2 * n)) := by ring

/-- Dimension choice plus `C_H >= 16/c_cap` implies the paper's individual
cap-event budget.  Here `K` is the event-count budget, instantiated in the
paper by `n^2 T`. -/
theorem capProbability_le_of_dimension_choice
    {c C R n D K δ : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hn : 0 < n)
    (hK : 0 < K) (hδ : 0 < δ)
    (hlogNonneg : 0 ≤ Real.log (2 * K / δ))
    (hC : 16 / c ≤ C)
    (hdimension :
      C * R ^ 2 * n * Real.log (2 * K / δ) ≤ D) :
    2 * Real.exp
        (-c * D * (1 / (4 * R * Real.sqrt n)) ^ 2) ≤
      δ / K := by
  have hfactor :
      0 ≤ R ^ 2 * n * Real.log (2 * K / δ) := by positivity
  have hdimension' :
      (16 / c) * R ^ 2 * n * Real.log (2 * K / δ) ≤ D := by
    calc
      (16 / c) * R ^ 2 * n * Real.log (2 * K / δ) =
          (16 / c) *
            (R ^ 2 * n * Real.log (2 * K / δ)) := by ring
      _ ≤ C * (R ^ 2 * n * Real.log (2 * K / δ)) :=
        mul_le_mul_of_nonneg_right hC hfactor
      _ = C * R ^ 2 * n * Real.log (2 * K / δ) := by ring
      _ ≤ D := hdimension
  have hbound := two_mul_exp_neg_le_div_of_log_le
    (a := c * D * (1 / (4 * R * Real.sqrt n)) ^ 2)
    hK hδ (capExponent_ge_log_of_dimension hc hR hn hdimension')
  simpa only [neg_mul, mul_assoc] using hbound

/-- In the usual parameter range `K >= 1` and `delta <= 1`, the logarithm
appearing in the dimension condition is automatically nonnegative. -/
theorem log_two_mul_div_nonneg
    {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    0 ≤ Real.log (2 * K / δ) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hδ]
  nlinarith

/-- Radius substitution used in Proposition `T-over-p`. -/
theorem haarRadius_sq (T : ℕ) :
    (230 * Real.sqrt T) ^ 2 = 230 ^ 2 * T := by
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)]

/-- With `delta=1/8`, the logarithmic event budget becomes `16 K`. -/
theorem two_mul_div_one_eighth (K : ℝ) :
    2 * K / (1 / 8) = 16 * K := by
  ring

end

end BilevelLowerBound
