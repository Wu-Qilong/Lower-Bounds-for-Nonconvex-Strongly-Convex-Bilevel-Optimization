/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import Mathlib

/-!
# Basic finite-dimensional definitions

This file formalizes the coordinate truncation and progress operator used
throughout the paper.  Coordinates are indexed by `Fin T`; the paper's
one-based progress index is represented by `i.val + 1`.
-/

namespace BilevelLowerBound

/-- A real vector with exactly `T` coordinates and the Euclidean `ℓ²` norm. -/
abbrev ChainVector (T : ℕ) := EuclideanSpace ℝ (Fin T)

/-- Package a coordinate function as a Euclidean chain vector. -/
def chainVectorOfFun {T : ℕ} (f : Fin T → ℝ) : ChainVector T :=
  WithLp.toLp 2 f

@[simp]
theorem chainVectorOfFun_apply {T : ℕ} (f : Fin T → ℝ) (i : Fin T) :
    chainVectorOfFun f i = f i := rfl

/-- Coordinate truncation onto the first `k` coordinates. -/
def truncate {T : ℕ} (k : ℕ) (z : ChainVector T) : ChainVector T :=
  chainVectorOfFun fun i ↦ if i.val < k then z i else 0

@[simp]
theorem truncate_apply_of_lt {T k : ℕ} (z : ChainVector T) (i : Fin T)
    (hi : i.val < k) :
    truncate k z i = z i := by
  simp [truncate, hi]

@[simp]
theorem truncate_apply_of_le {T k : ℕ} (z : ChainVector T) (i : Fin T)
    (hi : k ≤ i.val) :
    truncate k z i = 0 := by
  simp [truncate, Nat.not_lt.mpr hi]

@[simp]
theorem truncate_zero {T k : ℕ} :
    truncate k (0 : ChainVector T) = 0 := by
  ext i
  simp [truncate]

theorem truncate_eq_self_of_dim_le {T k : ℕ} (z : ChainVector T)
    (hTk : T ≤ k) :
    truncate k z = z := by
  ext i
  simp [truncate, lt_of_lt_of_le i.isLt hTk]

/--
The paper's progress operator:
the largest one-based coordinate index whose magnitude exceeds `c`,
or zero if no such coordinate exists.
-/
noncomputable def progress {T : ℕ} (c : ℝ) (z : ChainVector T) : ℕ :=
  (Finset.univ.filter fun i : Fin T ↦ c < |z i|).sup fun i ↦ i.val + 1

theorem progress_le_iff {T k : ℕ} {c : ℝ} {z : ChainVector T} :
    progress c z ≤ k ↔
      ∀ i : Fin T, c < |z i| → i.val + 1 ≤ k := by
  simp [progress, Finset.sup_le_iff]

theorem progress_le_dim {T : ℕ} (c : ℝ) (z : ChainVector T) :
    progress c z ≤ T := by
  rw [progress_le_iff]
  intro i _
  omega

/-- If progress is positive, its maximal coordinate is attained by an
actually active coordinate. -/
theorem exists_coordinate_at_progress {T : ℕ} {c : ℝ} {z : ChainVector T}
    (hpos : 0 < progress c z) :
    ∃ i : Fin T, c < |z i| ∧ i.val + 1 = progress c z := by
  let s : Finset (Fin T) :=
    Finset.univ.filter fun i : Fin T ↦ c < |z i|
  have hs : s.Nonempty := by
    by_contra hempty
    have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : progress c z = 0 := by
      unfold progress
      change s.sup (fun i ↦ i.val + 1) = 0
      simp [hsEmpty]
    omega
  obtain ⟨i, hi, heq⟩ :=
    Finset.exists_mem_eq_sup s hs (fun i ↦ i.val + 1)
  refine ⟨i, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hi).2
  · change i.val + 1 = s.sup (fun i ↦ i.val + 1)
    exact heq.symm

/-- Every coordinate strictly after an upper bound on progress is small. -/
theorem abs_le_threshold_of_progress_le {T k : ℕ} {c : ℝ}
    {z : ChainVector T} (hprog : progress c z ≤ k) (i : Fin T)
    (hik : k ≤ i.val) :
    |z i| ≤ c := by
  by_contra hsmall
  have hlarge : c < |z i| := lt_of_not_ge hsmall
  have hindex := (progress_le_iff.mp hprog) i hlarge
  omega

/-- If every coordinate after a prefix is small, progress stays in that prefix. -/
theorem progress_le_of_tail_bound {T k : ℕ} {c : ℝ} {z : ChainVector T}
    (hTail : ∀ i : Fin T, k ≤ i.val → |z i| ≤ c) :
    progress c z ≤ k := by
  rw [progress_le_iff]
  intro i hlarge
  by_contra hindex
  have hik : k ≤ i.val := by omega
  exact (not_lt_of_ge (hTail i hik)) hlarge

/-- Raising the threshold cannot increase progress. -/
theorem progress_anti_threshold {T : ℕ} {c₁ c₂ : ℝ} {z : ChainVector T}
    (hc : c₁ ≤ c₂) :
    progress c₂ z ≤ progress c₁ z := by
  rw [progress_le_iff]
  intro i hi
  unfold progress
  exact Finset.le_sup (f := fun j : Fin T ↦ j.val + 1) (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_lt hc hi)

/-- A truncation has no progress beyond its retained prefix. -/
theorem progress_truncate_le {T k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (z : ChainVector T) :
    progress c (truncate k z) ≤ k := by
  rw [progress_le_iff]
  intro i hi
  by_contra hindex
  have hik : k ≤ i.val := by omega
  rw [truncate_apply_of_le z i hik, abs_zero] at hi
  exact (not_lt_of_ge hc) hi

/-- At threshold zero, bounded progress is equivalent to exact support truncation. -/
theorem truncate_eq_self_of_progress_zero_le {T k : ℕ} {z : ChainVector T}
    (hprog : progress 0 z ≤ k) :
    truncate k z = z := by
  ext i
  by_cases hi : i.val < k
  · exact truncate_apply_of_lt z i hi
  · have hik : k ≤ i.val := Nat.le_of_not_gt hi
    have habs : |z i| ≤ 0 := abs_le_threshold_of_progress_le hprog i hik
    have hz : z i = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    simp [truncate, hi, hz]

/-- Dividing a probe by a positive scale rescales the progress threshold. -/
theorem progress_div {T : ℕ} (z : ChainVector T) (c η : ℝ) (hη : 0 < η) :
    progress c (chainVectorOfFun fun i ↦ z i / η) = progress (η * c) z := by
  simp [progress, abs_div, abs_of_pos hη, lt_div_iff₀ hη, mul_comm]

/-- The exact rescaling identity used in Proposition `T-over-p`. -/
theorem progress_quarter_rescaling {T : ℕ} (z : ChainVector T) (η : ℝ)
    (hη : 0 < η) :
    progress (1 / 4 : ℝ) (chainVectorOfFun fun i ↦ z i / η) =
      progress (η / 4) z := by
  simpa [div_eq_mul_inv] using progress_div z (1 / 4 : ℝ) η hη

end BilevelLowerBound
