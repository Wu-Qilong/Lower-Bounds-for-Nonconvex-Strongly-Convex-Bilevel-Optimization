/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.Transcript

/-!
# Coupled-process recursion

This module formalizes the deterministic recursion used in Step 2 and Step 7
of the adaptive Haar proof.  It separates three facts which are easy to blur
in an informal transcript argument:

* the capped number of exposed columns obeys the one-frontier recurrence;
* a process built from Borel update maps remains measurable at every time;
* if the actual and coupled update maps agree on every preceding good event,
  then the two processes agree up to their first progress violation.

No Haar-distribution statement is used here.
-/

open Finset

namespace BilevelLowerBound

/-! ## Success counts and exposed prefixes -/

/-- Number of successful bits before time `t`. -/
def cumulativeSuccess (xi : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, xi s

/-- Number of hidden columns exposed before time `t`, capped by `T`. -/
def exposedPrefix (T : ℕ) (xi : ℕ → ℕ) (t : ℕ) : ℕ :=
  min T (cumulativeSuccess xi t)

@[simp] theorem cumulativeSuccess_zero (xi : ℕ → ℕ) :
    cumulativeSuccess xi 0 = 0 := by
  simp [cumulativeSuccess]

theorem cumulativeSuccess_succ (xi : ℕ → ℕ) (t : ℕ) :
    cumulativeSuccess xi (t + 1) = cumulativeSuccess xi t + xi t := by
  simp [cumulativeSuccess, Finset.sum_range_succ]

@[simp] theorem exposedPrefix_zero (T : ℕ) (xi : ℕ → ℕ) :
    exposedPrefix T xi 0 = 0 := by
  simp [exposedPrefix]

theorem exposedPrefix_le_chain (T : ℕ) (xi : ℕ → ℕ) (t : ℕ) :
    exposedPrefix T xi t ≤ T := by
  exact min_le_left _ _

/-- Exact one-frontier recurrence.  It is valid for arbitrary natural
increments; Bernoulli bits specialize the increment to zero or one. -/
theorem exposedPrefix_succ (T : ℕ) (xi : ℕ → ℕ) (t : ℕ) :
    exposedPrefix T xi (t + 1) =
      min T (exposedPrefix T xi t + xi t) := by
  rw [exposedPrefix, cumulativeSuccess_succ, exposedPrefix]
  omega

theorem exposedPrefix_succ_of_failure
    {T : ℕ} {xi : ℕ → ℕ} {t : ℕ} (hxi : xi t = 0) :
    exposedPrefix T xi (t + 1) = exposedPrefix T xi t := by
  rw [exposedPrefix_succ, hxi, add_zero]
  exact min_eq_right (exposedPrefix_le_chain T xi t)

theorem exposedPrefix_succ_of_success
    {T : ℕ} {xi : ℕ → ℕ} {t : ℕ} (hxi : xi t = 1) :
    exposedPrefix T xi (t + 1) =
      min T (exposedPrefix T xi t + 1) := by
  simpa [hxi] using exposedPrefix_succ T xi t

theorem exposedPrefix_mono
    (T : ℕ) (xi : ℕ → ℕ) : Monotone (exposedPrefix T xi) := by
  intro s t hst
  unfold exposedPrefix
  apply min_le_min le_rfl
  unfold cumulativeSuccess
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hst) (by simp)

/-! ## Borel recursive processes -/

/-- A discrete-time process obtained from an initial random state and Borel
state-update maps.  The current outcome is explicitly passed to the update,
so all public randomness and exposed-prefix data can be included in `Ω`. -/
def recursiveProcess
    {Ω State : Type*}
    (initial : Ω → State) (step : ℕ → State × Ω → State) :
    ℕ → Ω → State
  | 0 => initial
  | t + 1 => fun ω ↦ step t (recursiveProcess initial step t ω, ω)

@[simp] theorem recursiveProcess_zero
    {Ω State : Type*}
    (initial : Ω → State) (step : ℕ → State × Ω → State) :
    recursiveProcess initial step 0 = initial := rfl

@[simp] theorem recursiveProcess_succ
    {Ω State : Type*}
    (initial : Ω → State) (step : ℕ → State × Ω → State)
    (t : ℕ) (ω : Ω) :
    recursiveProcess initial step (t + 1) ω =
      step t (recursiveProcess initial step t ω, ω) := rfl

/-- Borel measurability propagates through the coupled recursion. -/
theorem measurable_recursiveProcess
    {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    {initial : Ω → State} {step : ℕ → State × Ω → State}
    (hinitial : Measurable initial)
    (hstep : ∀ t, Measurable (step t)) :
    ∀ t, Measurable (recursiveProcess initial step t) := by
  intro t
  induction t with
  | zero => exact hinitial
  | succ t iht =>
      exact (hstep t).comp (iht.prodMk measurable_id)

/-! ## Agreement up to the first bad event -/

/-- Actual and coupled processes agree at every time up to `n` if their
updates agree on every preceding good event.  Crucially, `good t` is an event
defined for the coupled continuation on every outcome; no conditioning on
previous good events occurs in this deterministic induction. -/
theorem recursiveProcess_agree_of_good
    {Ω State : Type*}
    {initial : Ω → State}
    {actualStep coupledStep : ℕ → State × Ω → State}
    {good : ℕ → Ω → Prop} {n : ℕ}
    (hstep : ∀ t < n, ∀ ω s, good t ω →
      actualStep t (s, ω) = coupledStep t (s, ω))
    (hgood : ∀ t < n, ∀ ω, good t ω) :
    ∀ t ≤ n, ∀ ω,
      recursiveProcess initial actualStep t ω =
        recursiveProcess initial coupledStep t ω := by
  intro t htn
  induction t with
  | zero => intro ω; rfl
  | succ t iht =>
      intro ω
      have ht : t < n := by omega
      rw [recursiveProcess_succ, recursiveProcess_succ]
      rw [iht (by omega) ω]
      exact hstep t ht ω _ (hgood t ht ω)

/-- Once the two terminal transcripts agree, extending the same original
output map by projection produces exactly the same response-free output
probe. -/
theorem coupledOutput_eq_actualOutput
    {Seed Original Sample Column Output : Type*}
    (output : Seed → Original → Output) (seed : Seed)
    (actual coupled : AugmentedTranscript Original Sample Column)
    (hagree : actual = coupled) :
    extendOutput output seed actual = extendOutput output seed coupled := by
  rw [hagree]

end BilevelLowerBound
