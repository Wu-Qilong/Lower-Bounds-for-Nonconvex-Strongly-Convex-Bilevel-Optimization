/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.Basic

/-!
# The smooth zero-chain: definitions and algebraic structure

This module formalizes the functions `Psi`, `Phi0`, `Q`, the unscaled chain
`F_T`, and the scaled chain `H_{η,T}` from the paper.  It also checks the
zero region of `Psi`, the corresponding vanishing of a link, and the exact
value-level scaling identity.

The quantitative first-derivative and frontier estimates are proved downstream
in `ZeroChainBounds.lean` and `ZeroChainGradient.lean`.  The higher-order
operator-norm bounds are tracked separately in `FORMALIZATION_STATUS.md`.
-/

open MeasureTheory

namespace BilevelLowerBound

/-- The flat activation `Ψ` used in the zero-chain. -/
noncomputable def psi (t : ℝ) : ℝ :=
  if t ≤ (1 / 2 : ℝ) then 0
  else Real.exp (1 - 1 / (2 * t - 1) ^ 2)

/-- The Gaussian primitive `Φ₀` used in the zero-chain. -/
noncomputable def phiZero (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) *
    ∫ s in Set.Iic t, Real.exp (-(s ^ 2) / 2)

/-- A single unscaled zero-chain link. -/
noncomputable def chainQ (a b : ℝ) : ℝ :=
  psi (-a) * phiZero (-b) - psi a * phiZero b

/--
Adjoin the paper's fixed initial coordinate `a₀ = 1` to a chain vector.
The coordinate `i.castSucc` is the predecessor of the paper's `(i+1)`-st link.
-/
def withInitialOne {T : ℕ} (a : ChainVector T) : Fin (T + 1) → ℝ :=
  Fin.cases 1 a

/-- The unscaled chain `F_T`. -/
noncomputable def unscaledChain {T : ℕ} (a : ChainVector T) : ℝ :=
  ∑ i : Fin T, chainQ (withInitialOne a i.castSucc) (a i)

/-- Coordinatewise normalization by `η`. -/
noncomputable def normalize {T : ℕ} (η : ℝ) (z : ChainVector T) : ChainVector T :=
  chainVectorOfFun fun i ↦ z i / η

/-- The paper's individual scaled-coordinate link `ℒᵢη(z)`. -/
noncomputable def chainLink {T : ℕ} (η : ℝ) (z : ChainVector T)
    (i : Fin T) : ℝ :=
  chainQ
    (withInitialOne (normalize η z) i.castSucc)
    (normalize η z i)

/-- The scaled chain `H_{η,T}(z) = η² F_T(z/η)`. -/
noncomputable def scaledChain {T : ℕ} (η : ℝ) (z : ChainVector T) : ℝ :=
  η ^ 2 * unscaledChain (normalize η z)

@[simp]
theorem psi_eq_zero_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    psi t = 0 := by
  rw [psi, if_pos]
  simpa [one_div] using ht

@[simp]
theorem psi_eq_exp_of_half_lt {t : ℝ} (ht : 1 / 2 < t) :
    psi t = Real.exp (1 - 1 / (2 * t - 1) ^ 2) := by
  rw [psi, if_neg]
  exact not_le.mpr (by simpa [one_div] using ht)

theorem psi_eq_zero_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) :
    psi t = 0 := by
  apply psi_eq_zero_of_le_half
  exact (le_abs_self t).trans ht

theorem psi_neg_eq_zero_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) :
    psi (-t) = 0 := by
  apply psi_eq_zero_of_abs_le_half
  simpa only [abs_neg] using ht

/-- A chain link vanishes whenever its first coordinate lies in the flat zone. -/
theorem chainQ_eq_zero_of_abs_left_le_half {a b : ℝ}
    (ha : |a| ≤ 1 / 2) :
    chainQ a b = 0 := by
  rw [chainQ, psi_neg_eq_zero_of_abs_le_half ha,
    psi_eq_zero_of_abs_le_half ha]
  ring

/-- Simultaneously changing the signs of both link variables negates the link. -/
theorem chainQ_neg_neg (a b : ℝ) :
    chainQ (-a) (-b) = -chainQ a b := by
  simp only [chainQ, neg_neg]
  ring

/-- The sum-of-links form of the unscaled chain. -/
theorem unscaledChain_eq_sum {T : ℕ} (a : ChainVector T) :
    unscaledChain a =
      ∑ i : Fin T, chainQ (withInitialOne a i.castSucc) (a i) := rfl

/-- The first predecessor is exactly the fixed value `a₀ = 1`. -/
@[simp]
theorem withInitialOne_first {T : ℕ} (a : ChainVector (T + 1)) :
    withInitialOne a (0 : Fin (T + 2)) = 1 := rfl

/-- The exact value-level scaling identity in the definition of `H_{η,T}`. -/
theorem scaledChain_eq_scaled_unscaled {T : ℕ} (η : ℝ)
    (z : ChainVector T) :
    scaledChain η z = η ^ 2 * unscaledChain (normalize η z) := rfl

/-- The scaled chain is `η²` times the sum of its normalized links. -/
theorem scaledChain_eq_link_sum {T : ℕ} (η : ℝ) (z : ChainVector T) :
    scaledChain η z = η ^ 2 * ∑ i : Fin T, chainLink η z i := by
  rfl

/-- A raw predecessor bounded by `η/2` normalizes into the flat zone. -/
theorem normalized_abs_le_half {a η : ℝ} (hη : 0 < η)
    (ha : |a| ≤ η / 2) :
    |a / η| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hη]
  exact (div_le_iff₀ hη).2 (by
    simpa [div_eq_mul_inv, mul_comm] using ha)

/-- The value part of the paper's flat-link assertion after scaling. -/
theorem chainQ_normalized_eq_zero {a b η : ℝ} (hη : 0 < η)
    (ha : |a| ≤ η / 2) :
    chainQ (a / η) (b / η) = 0 := by
  apply chainQ_eq_zero_of_abs_left_le_half
  exact normalized_abs_le_half hη ha

end BilevelLowerBound
