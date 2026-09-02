/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChain
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Analytic facts for the zero-chain components

This file begins the analytic verification of the paper's standard zero-chain
lemma.  It proves global elementary bounds for `psi`, integrability and
smoothness of the Gaussian kernel, the fundamental-theorem-of-calculus formula
for `phiZero`, and infinite differentiability of `phiZero`.
-/

open MeasureTheory
open scoped ContDiff Topology

namespace BilevelLowerBound

/-- The Gaussian density without its normalizing constant. -/
noncomputable def gaussianKernel (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / 2)

theorem gaussianKernel_pos (t : ℝ) : 0 < gaussianKernel t := by
  simp only [gaussianKernel]
  positivity

theorem gaussianKernel_nonneg (t : ℝ) : 0 ≤ gaussianKernel t :=
  (gaussianKernel_pos t).le

theorem gaussianKernel_le_one (t : ℝ) : gaussianKernel t ≤ 1 := by
  rw [gaussianKernel, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg t]

theorem gaussianKernel_continuous : Continuous gaussianKernel := by
  unfold gaussianKernel
  fun_prop

theorem gaussianKernel_contDiff : ContDiff ℝ ∞ gaussianKernel := by
  unfold gaussianKernel
  fun_prop

theorem gaussianKernel_integrable : Integrable gaussianKernel := by
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have hFunction :
      gaussianKernel = fun x : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x
    rw [gaussianKernel]
    congr 1
    ring
  rw [hFunction]
  exact h

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  rw [psi]
  split
  · rfl
  · positivity

theorem psi_le_exp_one (t : ℝ) : psi t ≤ Real.exp 1 := by
  rw [psi]
  split
  · exact (Real.exp_pos 1).le
  · apply Real.exp_le_exp.mpr
    have hnonneg : 0 ≤ 1 / (2 * t - 1) ^ 2 := by positivity
    linarith

theorem abs_psi_le_exp_one (t : ℝ) : |psi t| ≤ Real.exp 1 := by
  rw [abs_of_nonneg (psi_nonneg t)]
  exact psi_le_exp_one t

/-- Express the improper integral in `phiZero` using a fixed base point. -/
theorem integral_Iic_gaussian_eq_const_add_interval (t : ℝ) :
    (∫ s in Set.Iic t, gaussianKernel s) =
      (∫ s in Set.Iic (0 : ℝ), gaussianKernel s) +
        ∫ s in (0 : ℝ)..t, gaussianKernel s := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (f := gaussianKernel) (a := (0 : ℝ)) (b := t)
    gaussianKernel_integrable.integrableOn
    gaussianKernel_integrable.integrableOn
  linarith

theorem phiZero_eq_const_add_interval (t : ℝ) :
    phiZero t =
      Real.sqrt (Real.exp 1) *
        ((∫ s in Set.Iic (0 : ℝ), gaussianKernel s) +
          ∫ s in (0 : ℝ)..t, gaussianKernel s) := by
  rw [phiZero, ← integral_Iic_gaussian_eq_const_add_interval t]
  rfl

theorem phiZero_hasDerivAt (t : ℝ) :
    HasDerivAt phiZero
      (Real.sqrt (Real.exp 1) * gaussianKernel t) t := by
  have hInterval :
      HasDerivAt
        (fun u : ℝ ↦ ∫ s in (0 : ℝ)..u, gaussianKernel s)
        (gaussianKernel t) t :=
    intervalIntegral.integral_hasDerivAt_right
      gaussianKernel_integrable.intervalIntegrable
      (gaussianKernel_continuous.stronglyMeasurableAtFilter volume (nhds t))
      gaussianKernel_continuous.continuousAt
  have hRight :
      HasDerivAt
        (fun u : ℝ ↦
          Real.sqrt (Real.exp 1) *
            ((∫ s in Set.Iic (0 : ℝ), gaussianKernel s) +
              ∫ s in (0 : ℝ)..u, gaussianKernel s))
        (Real.sqrt (Real.exp 1) * gaussianKernel t) t := by
    let C : ℝ := ∫ s in Set.Iic (0 : ℝ), gaussianKernel s
    have hAdd :
        HasDerivAt
          (fun u : ℝ ↦ C + ∫ s in (0 : ℝ)..u, gaussianKernel s)
          (gaussianKernel t) t :=
      hInterval.const_add C
    simpa only [C] using hAdd.const_mul (Real.sqrt (Real.exp 1))
  convert hRight using 1
  funext u
  exact phiZero_eq_const_add_interval u

theorem phiZero_deriv (t : ℝ) :
    deriv phiZero t = Real.sqrt (Real.exp 1) * gaussianKernel t :=
  (phiZero_hasDerivAt t).deriv

theorem phiZero_differentiable : Differentiable ℝ phiZero :=
  fun t ↦ (phiZero_hasDerivAt t).differentiableAt

theorem phiZero_contDiff : ContDiff ℝ ∞ phiZero := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨phiZero_differentiable, ?_⟩
  have hDeriv :
      deriv phiZero = fun t : ℝ ↦ Real.sqrt (Real.exp 1) * gaussianKernel t := by
    funext t
    exact phiZero_deriv t
  rw [hDeriv]
  exact contDiff_const.mul gaussianKernel_contDiff

theorem phiZero_strictMono : StrictMono phiZero := by
  apply strictMono_of_deriv_pos
  intro t
  rw [phiZero_deriv]
  exact mul_pos (Real.sqrt_pos.2 (Real.exp_pos 1)) (gaussianKernel_pos t)

theorem phiZero_nonneg (t : ℝ) : 0 ≤ phiZero t := by
  rw [phiZero]
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun s ↦ gaussianKernel_nonneg s

theorem phiZero_le_full_gaussian (t : ℝ) :
    phiZero t ≤
      Real.sqrt (Real.exp 1) * ∫ s : ℝ, gaussianKernel s := by
  rw [phiZero]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact setIntegral_le_integral gaussianKernel_integrable
    (Filter.Eventually.of_forall fun s ↦ gaussianKernel_nonneg s)

theorem integral_gaussianKernel :
    (∫ s : ℝ, gaussianKernel s) = Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
  have hFunction :
      gaussianKernel = fun x : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    funext x
    rw [gaussianKernel]
    congr 1
    ring
  rw [hFunction]
  exact integral_gaussian (1 / 2 : ℝ)

theorem phiZero_le_explicit (t : ℝ) :
    phiZero t ≤
      Real.sqrt (Real.exp 1) * Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
  rw [← integral_gaussianKernel]
  exact phiZero_le_full_gaussian t

/-- A convenient explicit global bound for `phiZero`. -/
noncomputable def phiBound : ℝ :=
  Real.sqrt (Real.exp 1) * Real.sqrt (Real.pi / (1 / 2 : ℝ))

theorem phiBound_nonneg : 0 ≤ phiBound := by
  unfold phiBound
  positivity

theorem phiZero_le_bound (t : ℝ) : phiZero t ≤ phiBound :=
  phiZero_le_explicit t

theorem abs_phiZero_le_bound (t : ℝ) : |phiZero t| ≤ phiBound := by
  rw [abs_of_nonneg (phiZero_nonneg t)]
  exact phiZero_le_bound t

theorem phiZero_deriv_nonneg (t : ℝ) : 0 ≤ deriv phiZero t := by
  rw [phiZero_deriv]
  exact mul_nonneg (Real.sqrt_nonneg _) (gaussianKernel_nonneg t)

theorem phiZero_deriv_le_sqrt_exp (t : ℝ) :
    deriv phiZero t ≤ Real.sqrt (Real.exp 1) := by
  rw [phiZero_deriv]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (gaussianKernel_le_one t) (Real.sqrt_nonneg _)

/-- Every individual unscaled link has a dimension-free absolute bound. -/
theorem abs_chainQ_le (a b : ℝ) :
    |chainQ a b| ≤ 2 * Real.exp 1 * phiBound := by
  rw [chainQ]
  calc
    |psi (-a) * phiZero (-b) - psi a * phiZero b|
        ≤ |psi (-a) * phiZero (-b)| + |psi a * phiZero b| := abs_sub _ _
    _ = |psi (-a)| * |phiZero (-b)| + |psi a| * |phiZero b| := by
      rw [abs_mul, abs_mul]
    _ ≤ Real.exp 1 * phiBound + Real.exp 1 * phiBound := by
      apply add_le_add
      · exact mul_le_mul (abs_psi_le_exp_one (-a))
          (abs_phiZero_le_bound (-b)) (abs_nonneg _) (Real.exp_pos 1).le
      · exact mul_le_mul (abs_psi_le_exp_one a)
          (abs_phiZero_le_bound b) (abs_nonneg _) (Real.exp_pos 1).le
    _ = 2 * Real.exp 1 * phiBound := by ring

/-- The magnitude of the unscaled chain grows at most linearly with its length. -/
theorem abs_unscaledChain_le {T : ℕ} (a : ChainVector T) :
    |unscaledChain a| ≤
      (T : ℝ) * (2 * Real.exp 1 * phiBound) := by
  rw [unscaledChain]
  calc
    |∑ i : Fin T, chainQ (withInitialOne a i.castSucc) (a i)|
        ≤ ∑ i : Fin T, |chainQ (withInitialOne a i.castSucc) (a i)| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun i : Fin T ↦ chainQ (withInitialOne a i.castSucc) (a i)) Finset.univ
    _ ≤ ∑ _i : Fin T, 2 * Real.exp 1 * phiBound := by
      exact Finset.sum_le_sum fun i _ ↦ abs_chainQ_le _ _
    _ = (T : ℝ) * (2 * Real.exp 1 * phiBound) := by simp

/-- A pointwise form of the standard chain's initial-gap estimate. -/
theorem unscaledChain_gap_pointwise {T : ℕ} (a : ChainVector T) :
    unscaledChain (0 : ChainVector T) - unscaledChain a ≤
      2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound)) := by
  have hZero := abs_unscaledChain_le (0 : ChainVector T)
  have hA := abs_unscaledChain_le a
  have hFirst :
      unscaledChain (0 : ChainVector T) - unscaledChain a ≤
        |unscaledChain (0 : ChainVector T)| + |unscaledChain a| := by
    linarith [le_abs_self (unscaledChain (0 : ChainVector T)),
      neg_le_abs (unscaledChain a)]
  linarith

/-- The corresponding `O(η²T)` pointwise gap bound for the scaled chain. -/
theorem scaledChain_gap_pointwise {T : ℕ} (η : ℝ) (z : ChainVector T) :
    scaledChain η (0 : ChainVector T) - scaledChain η z ≤
      η ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := by
  have hNormalizeZero : normalize η (0 : ChainVector T) = 0 := by
    ext i
    simp [normalize]
  have hGap := unscaledChain_gap_pointwise (normalize η z)
  rw [scaledChain, scaledChain, hNormalizeZero]
  have hScaled := mul_le_mul_of_nonneg_left hGap (sq_nonneg η)
  rw [mul_sub] at hScaled
  exact hScaled

/-- The range of every finite scaled chain is bounded below. -/
theorem scaledChain_range_bddBelow {T : ℕ} (η : ℝ) :
    BddBelow (Set.range (scaledChain η : ChainVector T → ℝ)) := by
  let C : ℝ := η ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound)))
  refine ⟨scaledChain η (0 : ChainVector T) - C, ?_⟩
  rintro y ⟨z, rfl⟩
  have hGap := scaledChain_gap_pointwise η z
  change scaledChain η (0 : ChainVector T) - C ≤ scaledChain η z
  dsimp only [C]
  linarith

/--
The exact `H(0) - inf H = O(η²T)` statement, with an explicit universal
constant, obtained from the pointwise estimate above.
-/
theorem scaledChain_initial_gap {T : ℕ} (η : ℝ) :
    scaledChain η (0 : ChainVector T) -
        sInf (Set.range (scaledChain η : ChainVector T → ℝ)) ≤
      η ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := by
  let C : ℝ := η ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound)))
  have hLower :
      scaledChain η (0 : ChainVector T) - C ≤
        sInf (Set.range (scaledChain η : ChainVector T → ℝ)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨z, rfl⟩
    have hGap := scaledChain_gap_pointwise η z
    change scaledChain η (0 : ChainVector T) - C ≤ scaledChain η z
    dsimp only [C]
    linarith
  dsimp only [C] at hLower ⊢
  linarith

end BilevelLowerBound
