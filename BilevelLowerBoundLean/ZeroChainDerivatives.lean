/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainSmooth

/-!
# Smoothness and derivative scaling of the zero chain

This file lifts the one-dimensional smoothness of `psi` and `phiZero` to the
two-variable link, the finite chain, and its scaled version.  It also proves
the exact Fréchet-derivative scaling identity in a form valid for every order:

`D^r H(z) = (η² (η⁻¹)^r) • D^r F(z / η)`.

For positive `η`, this coefficient is the paper's `η^(2-r)`.  The inverse
form avoids truncated natural-number subtraction and remains meaningful for
all derivative orders.
-/

open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

/-- Smoothness of a chain link after substitution of two smooth scalar maps. -/
theorem chainQ_comp_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ chainQ (a x) (b x)) := by
  unfold chainQ
  exact ((psi_contDiff.comp ha.neg).mul (phiZero_contDiff.comp hb.neg)).sub
    ((psi_contDiff.comp ha).mul (phiZero_contDiff.comp hb))

/-- The two-variable link is globally `C^∞`. -/
theorem chainQ_contDiff :
    ContDiff ℝ ∞ (fun w : ℝ × ℝ ↦ chainQ w.1 w.2) := by
  exact chainQ_comp_contDiff contDiff_fst contDiff_snd

/--
Every Fréchet jet of a link vanishes when its first coordinate is in the
closed flat zone.  The boundary cases are obtained from continuity of the
iterated derivative and density of the open flat strip.
-/
theorem iteratedFDeriv_chainQ_eq_zero_of_abs_fst_le_half
    (r : ℕ) {a b : ℝ} (ha : |a| ≤ 1 / 2) :
    iteratedFDeriv ℝ r (fun w : ℝ × ℝ ↦ chainQ w.1 w.2) (a, b) = 0 := by
  let qPair : ℝ × ℝ → ℝ := fun w ↦ chainQ w.1 w.2
  let S : Set (ℝ × ℝ) := Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.univ
  let Z := {w : ℝ × ℝ | iteratedFDeriv ℝ r qPair w = 0}
  have hQSmooth : ContDiff ℝ ∞ qPair := chainQ_contDiff
  have hDerivativeContinuous :
      Continuous (fun w ↦ iteratedFDeriv ℝ r qPair w) :=
    hQSmooth.continuous_iteratedFDeriv
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hZClosed : IsClosed Z := by
    exact isClosed_eq hDerivativeContinuous continuous_const
  have hSOpen : IsOpen S := isOpen_Ioo.prod isOpen_univ
  have hSZ : S ⊆ Z := by
    intro w hw
    have hLocal : qPair =ᶠ[nhds w] (fun _ : ℝ × ℝ ↦ 0) := by
      filter_upwards [hSOpen.mem_nhds hw] with y hy
      have hyAbs : |y.1| ≤ 1 / 2 := by
        apply le_of_lt
        apply abs_lt.mpr
        have hyLeft : (-1 / 2 : ℝ) < y.1 := hy.1.1
        have hyRight : y.1 < (1 / 2 : ℝ) := hy.1.2
        constructor <;> linarith
      exact chainQ_eq_zero_of_abs_left_le_half hyAbs
    have hWithin :
        qPair =ᶠ[nhdsWithin w Set.univ] (fun _ : ℝ × ℝ ↦ 0) :=
      hLocal.filter_mono inf_le_left
    have hJet :
        iteratedFDerivWithin ℝ r qPair Set.univ w =
          iteratedFDerivWithin ℝ r (fun _ : ℝ × ℝ ↦ 0) Set.univ w :=
      hWithin.iteratedFDerivWithin_eq (𝕜 := ℝ) hLocal.eq_of_nhds r
    change iteratedFDeriv ℝ r qPair w = 0
    rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hJet
    simpa using hJet
  have hClosureSZ : closure S ⊆ Z := closure_minimal hSZ hZClosed
  have haIcc : a ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    change (-1 / 2 : ℝ) ≤ a ∧ a ≤ 1 / 2
    have haBounds := abs_le.mp ha
    constructor <;> linarith
  have hwClosure : (a, b) ∈ closure S := by
    change (a, b) ∈ closure
      (Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.univ)
    rw [closure_prod_eq, closure_Ioo (by norm_num :
      (-1 / 2 : ℝ) ≠ 1 / 2), closure_univ]
    exact ⟨haIcc, Set.mem_univ b⟩
  exact hClosureSZ hwClosure

/-- Each predecessor coordinate used by the finite chain is a smooth map. -/
theorem withInitialOne_coord_contDiff {T : ℕ} (i : Fin T) :
    ContDiff ℝ ∞ (fun a : ChainVector T ↦ withInitialOne a i.castSucc) := by
  unfold withInitialOne
  generalize i.castSucc = k
  cases k using Fin.cases with
  | zero =>
      simpa using
        (contDiff_const : ContDiff ℝ ∞ (fun _a : ChainVector T ↦ (1 : ℝ)))
  | succ j =>
      simpa using
        (by fun_prop : ContDiff ℝ ∞ (fun a : ChainVector T ↦ a j))

/-- The unscaled finite zero chain is globally `C^∞`. -/
theorem unscaledChain_contDiff {T : ℕ} :
    ContDiff ℝ ∞ (unscaledChain : ChainVector T → ℝ) := by
  unfold unscaledChain
  apply ContDiff.sum
  intro i _hi
  exact chainQ_comp_contDiff (withInitialOne_coord_contDiff i) (by fun_prop)

/-- Coordinatewise division is scalar multiplication by the inverse. -/
theorem normalize_eq_inv_smul {T : ℕ} (η : ℝ) (z : ChainVector T) :
    normalize η z = η⁻¹ • z := by
  ext i
  simp [normalize, div_eq_mul_inv, mul_comm]

/-- Every scaled finite zero chain is globally `C^∞`. -/
theorem scaledChain_contDiff {T : ℕ} (η : ℝ) :
    ContDiff ℝ ∞ (scaledChain η : ChainVector T → ℝ) := by
  have hFun :
      (scaledChain η : ChainVector T → ℝ) =
        fun z ↦ η ^ 2 * unscaledChain (η⁻¹ • z) := by
    funext z
    rw [scaledChain, normalize_eq_inv_smul]
  rw [hFun]
  exact contDiff_const.mul
    (unscaledChain_contDiff.comp (contDiff_id.const_smul η⁻¹))

/-- Exact all-order Fréchet-derivative scaling of the finite zero chain. -/
theorem iteratedFDeriv_scaledChain {T r : ℕ} (η : ℝ)
    (z : ChainVector T) :
    iteratedFDeriv ℝ r (scaledChain η : ChainVector T → ℝ) z =
      (η ^ 2 * (η⁻¹) ^ r) •
        iteratedFDeriv ℝ r (unscaledChain : ChainVector T → ℝ)
          (normalize η z) := by
  have hFun :
      (scaledChain η : ChainVector T → ℝ) =
        η ^ 2 • (fun w : ChainVector T ↦ unscaledChain (η⁻¹ • w)) := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, scaledChain]
    rw [normalize_eq_inv_smul]
  rw [hFun]
  have hUnscaled :
      ContDiff ℝ r (unscaledChain : ChainVector T → ℝ) :=
    (unscaledChain_contDiff (T := T)).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hInner :
      ContDiff ℝ r (fun w : ChainVector T ↦ unscaledChain (η⁻¹ • w)) :=
    hUnscaled.comp (contDiff_id.const_smul η⁻¹)
  rw [iteratedFDeriv_const_smul_apply]
  · rw [congrFun (iteratedFDeriv_comp_const_smul (η⁻¹) hUnscaled) z]
    rw [normalize_eq_inv_smul]
    simp only [smul_smul]
  · exact hInner.contDiffAt

/-- First derivatives acquire one factor of `η`. -/
theorem iteratedFDeriv_scaledChain_one {T : ℕ} {η : ℝ} (η_ne : η ≠ 0)
    (z : ChainVector T) :
    iteratedFDeriv ℝ 1 (scaledChain η : ChainVector T → ℝ) z =
      η • iteratedFDeriv ℝ 1 (unscaledChain : ChainVector T → ℝ)
        (normalize η z) := by
  rw [iteratedFDeriv_scaledChain]
  congr 1
  field_simp

/-- Second derivatives are invariant under the paper's scaling. -/
theorem iteratedFDeriv_scaledChain_two {T : ℕ} {η : ℝ} (η_ne : η ≠ 0)
    (z : ChainVector T) :
    iteratedFDeriv ℝ 2 (scaledChain η : ChainVector T → ℝ) z =
      iteratedFDeriv ℝ 2 (unscaledChain : ChainVector T → ℝ)
        (normalize η z) := by
  rw [iteratedFDeriv_scaledChain]
  have hCoeff : η ^ 2 * (η⁻¹) ^ 2 = 1 := by
    field_simp
  rw [hCoeff, one_smul]

/-- Third derivatives acquire the factor `η⁻¹`. -/
theorem iteratedFDeriv_scaledChain_three {T : ℕ} {η : ℝ} (η_ne : η ≠ 0)
    (z : ChainVector T) :
    iteratedFDeriv ℝ 3 (scaledChain η : ChainVector T → ℝ) z =
      η⁻¹ • iteratedFDeriv ℝ 3 (unscaledChain : ChainVector T → ℝ)
        (normalize η z) := by
  rw [iteratedFDeriv_scaledChain]
  congr 1
  field_simp

end

end BilevelLowerBound
