/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.Basic
import BilevelLowerBoundLean.CoupledProcess
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Deterministic geometry in the adaptive Haar argument

This module formalizes Steps 4 and 6 of the paper's Haar proof.  Conditional
Haar invariance and the spherical-cap probability are not asserted here;
they enter only by supplying coordinate bounds of the form
`abs <u_j,w_s> <= tau`.  From those bounds, everything below is deterministic:
orthogonal projection removes the exposed component, an orthonormal residual
basis preserves the coefficient norm, Cauchy--Schwarz yields the hidden
coordinate bound, and the tail bound implies the required progress bound.
-/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Orthogonal residuals -/

def residualProbe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (r : E) : E :=
  r - U.starProjection r

theorem residualProbe_mem_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (r : E) :
    residualProbe U r ∈ Uᗮ := by
  exact U.sub_starProjection_mem_orthogonal r

theorem norm_residualProbe_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (r : E) :
    ‖residualProbe U r‖ ≤ ‖r‖ := by
  change ‖r - U.starProjection r‖ ≤ ‖r‖
  rw [← U.starProjection_orthogonal_val r]
  exact Uᗮ.norm_starProjection_apply_le r

/-- A direction orthogonal to the exposed frame has the same inner product
with a probe and with its residual component. -/
theorem real_inner_residualProbe_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    {u r : E} (hu : u ∈ Uᗮ) :
    ⟪u, residualProbe U r⟫_ℝ = ⟪u, r⟫_ℝ := by
  have hproj : U.starProjection r ∈ U := U.starProjection_apply_mem r
  have hzero : ⟪u, U.starProjection r⟫_ℝ = 0 := by
    simpa [real_inner_comm] using hu _ hproj
  simp [residualProbe, inner_sub_right, hzero]

/-! ## Euclidean coefficient estimates -/

/-- Coordinatewise cap bounds imply the Euclidean `sqrt(m) tau` bound. -/
theorem norm_chainVector_le_sqrt_mul_of_coordinate_le
    {m : ℕ} {beta : ChainVector m} {tau : ℝ}
    (htau : 0 ≤ tau)
    (hcoord : ∀ s : Fin m, |beta s| ≤ tau) :
    ‖beta‖ ≤ Real.sqrt m * tau := by
  have hsq : ∀ s : Fin m, (beta s) ^ 2 ≤ tau ^ 2 := by
    intro s
    nlinarith [hcoord s, abs_nonneg (beta s), le_abs_self (beta s),
      neg_abs_le (beta s)]
  have hsum :
      ∑ s : Fin m, (beta s) ^ 2 ≤ (m : ℝ) * tau ^ 2 := by
    calc
      ∑ s : Fin m, (beta s) ^ 2 ≤ ∑ _s : Fin m, tau ^ 2 :=
        Finset.sum_le_sum fun s _ ↦ hsq s
      _ = (m : ℝ) * tau ^ 2 := by simp
  have hnormsq : ‖beta‖ ^ 2 ≤ (m : ℝ) * tau ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hsum
  have hsqrt : (Real.sqrt m) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [← sq_le_sq₀ (norm_nonneg beta)
    (mul_nonneg (Real.sqrt_nonneg (m : ℝ)) htau)]
  rw [mul_pow, hsqrt]
  exact hnormsq

/-- An orthonormal synthesis preserves the Euclidean norm of its coefficient
vector. -/
theorem norm_sum_smul_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℝ w)
    (alpha : ChainVector m) :
    ‖∑ s : Fin m, alpha s • w s‖ = ‖alpha‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖∑ s : Fin m, alpha s • w s‖ ^ 2 =
        ∑ s : Fin m, (alpha s) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      rw [hw.inner_sum alpha alpha Finset.univ]
      simp [pow_two]
    _ = ‖alpha‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq alpha).symm

/-- Inner product with a residual-basis expansion is the Euclidean inner
product of its coefficient vector and the cap-coordinate vector. -/
theorem real_inner_sum_smul_eq_chain_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (u : E) (w : Fin m → E) (alpha : ChainVector m) :
    ⟪u, ∑ s : Fin m, alpha s • w s⟫_ℝ =
      ⟪alpha,
        chainVectorOfFun (fun s : Fin m ↦ ⟪u, w s⟫_ℝ)⟫_ℝ := by
  simp [PiLp.inner_apply, inner_sum, real_inner_smul_right, mul_comm]

/-! ## Hidden-coordinate bound -/

/-- Abstract Cauchy--Schwarz step: a coefficient vector of norm at most `R`
paired with `m` cap coordinates of size at most `tau` is bounded by
`R sqrt(n) tau` whenever `m <= n`. -/
theorem abs_chain_inner_le_radius_sqrt_mul
    {m n : ℕ} {R tau : ℝ}
    (hR : 0 ≤ R) (htau : 0 ≤ tau) (hmn : m ≤ n)
    {alpha beta : ChainVector m}
    (halpha : ‖alpha‖ ≤ R)
    (hbeta : ∀ s : Fin m, |beta s| ≤ tau) :
    |⟪alpha, beta⟫_ℝ| ≤ R * Real.sqrt n * tau := by
  have hbetaNorm : ‖beta‖ ≤ Real.sqrt m * tau :=
    norm_chainVector_le_sqrt_mul_of_coordinate_le htau hbeta
  have hsqrt : Real.sqrt m ≤ Real.sqrt n := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hbetaNorm' : ‖beta‖ ≤ Real.sqrt n * tau := by
    exact hbetaNorm.trans (mul_le_mul_of_nonneg_right hsqrt htau)
  calc
    |⟪alpha, beta⟫_ℝ| ≤ ‖alpha‖ * ‖beta‖ :=
      abs_real_inner_le_norm alpha beta
    _ ≤ R * (Real.sqrt n * tau) :=
      mul_le_mul halpha hbetaNorm' (norm_nonneg beta) hR
    _ = R * Real.sqrt n * tau := by ring

/-- The paper's choice `tau = 1/(4 R sqrt(n))` gives the threshold `1/4`. -/
theorem abs_chain_inner_le_quarter_of_cap
    {m n : ℕ} {R : ℝ} (hR : 0 < R) (hn : 0 < n) (hmn : m ≤ n)
    {alpha beta : ChainVector m}
    (halpha : ‖alpha‖ ≤ R)
    (hbeta : ∀ s : Fin m,
      |beta s| ≤ 1 / (4 * R * Real.sqrt n)) :
    |⟪alpha, beta⟫_ℝ| ≤ 1 / 4 := by
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have htau : 0 ≤ 1 / (4 * R * Real.sqrt n) := by positivity
  have hbound := abs_chain_inner_le_radius_sqrt_mul
    hR.le htau hmn halpha hbeta
  calc
    |⟪alpha, beta⟫_ℝ| ≤
        R * Real.sqrt n * (1 / (4 * R * Real.sqrt n)) := hbound
    _ = 1 / 4 := by field_simp [hR.ne', hsqrtn.ne']

/-- Full deterministic Step 6.  The hypotheses are exactly the output of
Step 4 (orthogonal residual expansion and coefficient norm bound) and the
complement of all cap events from Step 5. -/
theorem hiddenCoordinate_le_quarter_of_no_cap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m n : ℕ} {R : ℝ} (hR : 0 < R) (hn : 0 < n) (hmn : m ≤ n)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    {u r : E} (hu : u ∈ Uᗮ) (hr : ‖r‖ ≤ R)
    {w : Fin m → E} (hw : Orthonormal ℝ w)
    (alpha : ChainVector m)
    (hexpand : residualProbe U r = ∑ s : Fin m, alpha s • w s)
    (hcap : ∀ s : Fin m,
      |⟪u, w s⟫_ℝ| ≤ 1 / (4 * R * Real.sqrt n)) :
    |⟪u, r⟫_ℝ| ≤ 1 / 4 := by
  let beta : ChainVector m :=
    chainVectorOfFun fun s : Fin m ↦ ⟪u, w s⟫_ℝ
  have halpha : ‖alpha‖ ≤ R := by
    rw [← norm_sum_smul_orthonormal hw alpha, ← hexpand]
    exact (norm_residualProbe_le U r).trans hr
  have hbeta : ∀ s : Fin m,
      |beta s| ≤ 1 / (4 * R * Real.sqrt n) := by
    intro s
    exact hcap s
  have hinner : ⟪u, r⟫_ℝ = ⟪alpha, beta⟫_ℝ := by
    rw [← real_inner_residualProbe_eq U hu, hexpand]
    exact real_inner_sum_smul_eq_chain_inner u w alpha
  rw [hinner]
  exact abs_chain_inner_le_quarter_of_cap hR hn hmn halpha hbeta

/-! ## From hidden-coordinate control to progress -/

theorem progress_quarter_le_of_hidden_coordinates
    {T J : ℕ} {q : ChainVector T}
    (hhidden : ∀ j : Fin T, J ≤ j.val → |q j| ≤ 1 / 4) :
    progress (1 / 4 : ℝ) q ≤ J := by
  exact progress_le_of_tail_bound hhidden

/-! ## Counting all cap events -/

/-- The number of triples `(t,s,j)` is at most `n^2 T` once every residual
dimension is at most `n`.  This is the slightly coarser count used in the
paper's union bound. -/
theorem sum_cap_event_count_le
    {n T : ℕ} {m J : Fin n → ℕ}
    (hm : ∀ t, m t ≤ n) :
    ∑ t : Fin n, m t * (T - J t) ≤ n ^ 2 * T := by
  calc
    ∑ t : Fin n, m t * (T - J t) ≤
        ∑ _t : Fin n, n * T := by
      exact Finset.sum_le_sum fun t _ ↦
        Nat.mul_le_mul (hm t) (Nat.sub_le T (J t))
    _ = n ^ 2 * T := by simp [pow_two, mul_assoc]

end

end BilevelLowerBound
