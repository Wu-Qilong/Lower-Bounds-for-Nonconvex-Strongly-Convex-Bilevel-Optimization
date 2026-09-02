/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FreshSample
import BilevelLowerBoundLean.HaarProbability
import BilevelLowerBoundLean.HardInstance

/-!
# The `T/p` progress argument

This module formalizes the probability and deterministic bookkeeping in
Proposition `T-over-p`.  Fresh conditional Bernoulli laws give the exact
expectation `E S_N = N p`; Markov's inequality controls `S_N >= T`; and the
intersection of that event with the adaptive-Haar event leaves the output
progress strictly below `T` with probability at least `3/4`.
-/

open Filter Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

namespace BilevelLowerBound

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]

/-! ## Counting fresh successes -/

/-- The natural-valued number of successful calls among `N` fresh events. -/
noncomputable def successCountNat
    {N : ℕ} (success : Fin N → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact ∑ t, if ω ∈ success t then 1 else 0

/-- The real-valued version used for expectations and Markov's inequality. -/
def successCountReal {N : ℕ} (success : Fin N → Set Ω) (ω : Ω) : ℝ :=
  successCountNat success ω

theorem successCountReal_eq_sum_bernoulliBit
    {N : ℕ} (success : Fin N → Set Ω) (ω : Ω) :
    successCountReal success ω =
      ∑ t, bernoulliBit (success t) ω := by
  classical
  change ((∑ t, if ω ∈ success t then 1 else 0 : ℕ) : ℝ) =
    ∑ t, bernoulliBit (success t) ω
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hω : ω ∈ success t <;>
    simp [bernoulliBit, hω]

theorem successCountReal_nonneg
    {N : ℕ} (success : Fin N → Set Ω) (ω : Ω) :
    0 ≤ successCountReal success ω := by
  change (0 : ℝ) ≤ (successCountNat success ω : ℝ)
  positivity

theorem measurable_successCountReal
    {N : ℕ} {success : Fin N → Set Ω}
    (hsuccess : ∀ t, MeasurableSet[mΩ] (success t)) :
    Measurable (successCountReal success) := by
  have hbit : ∀ t, Measurable (bernoulliBit (success t)) := by
    intro t
    exact measurable_const.indicator (hsuccess t)
  have hsum : Measurable (fun ω ↦ ∑ t, bernoulliBit (success t) ω) := by
    exact Finset.measurable_fun_sum Finset.univ fun t _ ↦ hbit t
  rw [show successCountReal success =
      (fun ω ↦ ∑ t, bernoulliBit (success t) ω) from
    funext fun ω ↦ successCountReal_eq_sum_bernoulliBit success ω]
  exact hsum

theorem integrable_successCountReal
    {N : ℕ} {success : Fin N → Set Ω}
    (hsuccess : ∀ t, MeasurableSet[mΩ] (success t)) :
    Integrable (successCountReal success) μ := by
  have hsum :
      Integrable (fun ω ↦ ∑ t, bernoulliBit (success t) ω) μ := by
    exact integrable_finsetSum Finset.univ fun t _ ↦
      integrable_bernoulliBit (μ := μ) (hsuccess t)
  exact hsum.congr (ae_of_all μ fun ω ↦
    (successCountReal_eq_sum_bernoulliBit success ω).symm)

/-- The tower-property step for one fresh bit. -/
theorem FreshBernoulliEvent.integral_bernoulliBit
    {past : MeasurableSpace Ω} {success : Set Ω} {p : ℝ}
    (hfresh : FreshBernoulliEvent mΩ μ past success p) :
    ∫ ω, bernoulliBit success ω ∂μ = p := by
  calc
    ∫ ω, bernoulliBit success ω ∂μ =
        ∫ ω, (μ[bernoulliBit success | past]) ω ∂μ :=
      (integral_condExp hfresh.past_le).symm
    _ = ∫ _ω, p ∂μ :=
      integral_congr_ae hfresh.condExp_bernoulliBit
    _ = p := by simp

/-- Freshness at every adaptive call gives exactly `E S_N = N p`.  The
pre-call sigma-algebra may depend on the call index. -/
theorem integral_successCountReal_eq
    {N : ℕ} (past : Fin N → MeasurableSpace Ω)
    (success : Fin N → Set Ω) {p : ℝ}
    (hfresh : ∀ t,
      FreshBernoulliEvent mΩ μ (past t) (success t) p) :
    ∫ ω, successCountReal success ω ∂μ = (N : ℝ) * p := by
  have hInt : ∀ t,
      Integrable (bernoulliBit (success t)) μ := by
    intro t
    exact integrable_bernoulliBit (μ := μ)
      (hfresh t).measurable_success
  calc
    ∫ ω, successCountReal success ω ∂μ =
        ∫ ω, ∑ t, bernoulliBit (success t) ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all μ fun ω ↦
        successCountReal_eq_sum_bernoulliBit success ω
    _ = ∑ t, ∫ ω, bernoulliBit (success t) ω ∂μ := by
      simpa only [Finset.sum_apply] using
        integral_finsetSum Finset.univ
          (fun t _ ↦ hInt t)
    _ = ∑ _t : Fin N, p := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hfresh t).integral_bernoulliBit
    _ = (N : ℝ) * p := by simp

/-- Markov's inequality in the exact form used in Step 4. -/
theorem measureReal_successCountReal_ge_le
    {N : ℕ} (past : Fin N → MeasurableSpace Ω)
    (success : Fin N → Set Ω) {p threshold : ℝ}
    (hfresh : ∀ t,
      FreshBernoulliEvent mΩ μ (past t) (success t) p)
    (hthreshold : 0 < threshold) :
    μ.real {ω | threshold ≤ successCountReal success ω} ≤
      (N : ℝ) * p / threshold := by
  have hInt : Integrable (successCountReal success) μ :=
    integrable_successCountReal fun t ↦ (hfresh t).measurable_success
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω ↦ successCountReal_nonneg success ω)
    hInt threshold
  rw [integral_successCountReal_eq past success hfresh] at hMarkov
  apply (le_div_iff₀ hthreshold).2
  simpa [mul_comm] using hMarkov

/-- Natural-count version of Markov's inequality. -/
theorem measureReal_successCountNat_ge_le
    {N T : ℕ} (past : Fin N → MeasurableSpace Ω)
    (success : Fin N → Set Ω) {p : ℝ}
    (hfresh : ∀ t,
      FreshBernoulliEvent mΩ μ (past t) (success t) p)
    (hT : 0 < T) :
    μ.real {ω | T ≤ successCountNat success ω} ≤
      (N : ℝ) * p / T := by
  have hset :
      {ω | T ≤ successCountNat success ω} =
        {ω | (T : ℝ) ≤ successCountReal success ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, successCountReal]
    exact_mod_cast Iff.rfl
  rw [hset]
  exact measureReal_successCountReal_ge_le
    past success hfresh (by exact_mod_cast hT)

/-! ## Combining the Haar and Bernoulli good events -/

/-- Two good events whose failure probabilities are bounded by `deltaA` and
`deltaB` intersect with probability at least `1-(deltaA+deltaB)`. -/
theorem measureReal_inter_ge_one_sub_add
    {A B : Set Ω} (hA : MeasurableSet[mΩ] A)
    (hB : MeasurableSet[mΩ] B) {δA δB : ℝ}
    (hAfail : μ.real Aᶜ ≤ δA) (hBfail : μ.real Bᶜ ≤ δB) :
    1 - (δA + δB) ≤ μ.real (A ∩ B) := by
  have hUnion : μ.real (Aᶜ ∪ Bᶜ) ≤ δA + δB :=
    (measureReal_union_le Aᶜ Bᶜ).trans (add_le_add hAfail hBfail)
  have hGood := measureReal_compl_ge_one_sub
    (hA.compl.union hB.compl) hUnion
  simpa only [compl_union, compl_compl] using hGood

/-- On the Haar event, fewer than `T` successful reveals force output
progress to remain strictly below the end of the chain. -/
theorem outputProgress_lt_of_haar_and_few_successes
    {T S P : ℕ} (hhaar : P ≤ min T S) (hfew : S < T) :
    P < T := by
  exact lt_of_le_of_lt (hhaar.trans (min_le_right T S)) hfew

/-- Abstract, fully checked probability conclusion of Proposition `T-over-p`.
The only Haar-specific premise is `hhaar`: on `haarGood`, output progress is
at most the capped number of successful reveals. -/
theorem output_unfinished_probability
    {N T : ℕ} (past : Fin N → MeasurableSpace Ω)
    (success : Fin N → Set Ω) {p : ℝ}
    (hfresh : ∀ t,
      FreshBernoulliEvent mΩ μ (past t) (success t) p)
    (hT : 0 < T)
    (haarGood : Set Ω) (hhaarMeas : MeasurableSet[mΩ] haarGood)
    (hhaarFail : μ.real haarGoodᶜ ≤ 1 / 8)
    (outputProgress : Ω → ℕ)
    (hhaar : ∀ ω ∈ haarGood,
      outputProgress ω ≤ min T (successCountNat success ω))
    (hCalls : (N : ℝ) * p / T ≤ 1 / 8) :
    3 / 4 ≤ μ.real {ω | outputProgress ω < T} := by
  let few : Set Ω := {ω | successCountReal success ω < T}
  have hcountMeas : Measurable (successCountReal success) :=
    measurable_successCountReal fun t ↦ (hfresh t).measurable_success
  have hfewMeas : MeasurableSet[mΩ] few :=
    hcountMeas measurableSet_Iio
  have hMarkov :
      μ.real {ω | (T : ℝ) ≤ successCountReal success ω} ≤ 1 / 8 :=
    (measureReal_successCountReal_ge_le past success hfresh
      (by exact_mod_cast hT)).trans hCalls
  have hfewFail : μ.real fewᶜ ≤ 1 / 8 := by
    simpa only [few, compl_ofPred, not_lt] using hMarkov
  have hinter : 3 / 4 ≤ μ.real (haarGood ∩ few) := by
    have h := measureReal_inter_ge_one_sub_add
      hhaarMeas hfewMeas hhaarFail hfewFail
    norm_num at h ⊢
    exact h
  have hsubset : haarGood ∩ few ⊆
      {ω | outputProgress ω < T} := by
    intro ω hω
    have hNat : successCountNat success ω < T := by
      have hreal : successCountReal success ω < (T : ℝ) := hω.2
      change (successCountNat success ω : ℝ) < (T : ℝ) at hreal
      exact_mod_cast hreal
    exact outputProgress_lt_of_haar_and_few_successes
      (hhaar ω hω.1) hNat
  exact hinter.trans (measureReal_mono hsubset)

/-! ## Bounded response-free output probes and threshold rescaling -/

/-- Dividing a soft-projected query by a positive scale preserves the paper's
uniform radius bound. -/
theorem norm_inv_smul_softProjection_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (z : E) :
    ‖η⁻¹ • softProjection R z‖ ≤ R / η := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη]
  have hproj := (norm_softProjection_lt hR z).le
  calc
    η⁻¹ * ‖softProjection R z‖ ≤ η⁻¹ * R :=
      mul_le_mul_of_nonneg_left hproj (inv_nonneg.mpr hη.le)
    _ = R / η := by rw [div_eq_mul_inv, mul_comm]

/-- Specialization to `R=230 eta sqrt(T)`. -/
theorem norm_inv_smul_softProjection_le_haarRadius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R η : ℝ} {T : ℕ} (hη : 0 < η) (hT : 0 < T)
    (hR : R = 230 * η * Real.sqrt T) (z : E) :
    ‖η⁻¹ • softProjection R z‖ ≤ 230 * Real.sqrt T := by
  subst R
  have hsqrt : 0 < Real.sqrt (T : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hRpos : 0 < 230 * η * Real.sqrt T := by
    positivity
  have hbound := norm_inv_smul_softProjection_le hRpos hη z
  calc
    ‖η⁻¹ • softProjection (230 * η * Real.sqrt T) z‖ ≤
        (230 * η * Real.sqrt T) / η := hbound
    _ = 230 * Real.sqrt T := by field_simp

end

end BilevelLowerBound
