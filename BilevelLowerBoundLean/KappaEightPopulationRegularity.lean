/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightHardInstance
import BilevelLowerBoundLean.KappaEightRegularity
import BilevelLowerBoundLean.FullPopulationRegularity
import BilevelLowerBoundLean.HardObjectiveRegularity

/-!
# Population regularity of the two-coordinate amplifier

This file is the analytic base layer for the independent `kappa^8`
construction.  It computes, rather than postulates, the complete Hessian of
the two-dimensional amplifier and of the lower quadratic slice.  It also
proves that the quadratic has zero third derivative, a global lower spectral
bound `1 / kappa`, and a uniform Hessian upper bound.  The last section gives
the perturbation theorem used to combine these exact calculations with the
compensated-frontier estimates from `KappaEightRegularity`.
-/

open Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Exact derivatives of the amplifier quadratic -/

def amplifierFirstSquare (v : AmplifierAux) : ℝ :=
  v.1 ^ 2

def amplifierSecondSquare (v : AmplifierAux) : ℝ :=
  v.2 ^ 2

theorem amplifierFirstSquare_contDiff :
    ContDiff ℝ ∞ amplifierFirstSquare := by
  unfold amplifierFirstSquare
  fun_prop

theorem amplifierSecondSquare_contDiff :
    ContDiff ℝ ∞ amplifierSecondSquare := by
  unfold amplifierSecondSquare
  fun_prop

theorem amplifierQuadratic_contDiff (kappa : ℝ) :
    ContDiff ℝ ∞ (amplifierQuadratic kappa) := by
  unfold amplifierQuadratic amplifierDiag amplifierOffDiag
  fun_prop

theorem iteratedFDeriv_amplifierFirstSquare_two_apply
    (v : AmplifierAux) (m : Fin 2 → AmplifierAux) :
    iteratedFDeriv ℝ 2 amplifierFirstSquare v m =
      2 * (m 0).1 * (m 1).1 := by
  let L : AmplifierAux →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hfun : amplifierFirstSquare =
      (fun y : ℝ ↦ ‖y‖ ^ 2) ∘ L := by
    funext y
    simp [amplifierFirstSquare, L, Real.norm_eq_abs, sq_abs]
  rw [hfun, L.iteratedFDeriv_comp_right (contDiff_norm_sq ℝ) v
    (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_norm_sq_two_apply]
  simp [L]
  ring

theorem iteratedFDeriv_amplifierSecondSquare_two_apply
    (v : AmplifierAux) (m : Fin 2 → AmplifierAux) :
    iteratedFDeriv ℝ 2 amplifierSecondSquare v m =
      2 * (m 0).2 * (m 1).2 := by
  let L : AmplifierAux →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfun : amplifierSecondSquare =
      (fun y : ℝ ↦ ‖y‖ ^ 2) ∘ L := by
    funext y
    simp [amplifierSecondSquare, L, Real.norm_eq_abs, sq_abs]
  rw [hfun, L.iteratedFDeriv_comp_right (contDiff_norm_sq ℝ) v
    (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_norm_sq_two_apply]
  simp [L]
  ring

theorem iteratedFDeriv_amplifierFirstSquare_three_eq_zero
    (v : AmplifierAux) :
    iteratedFDeriv ℝ 3 amplifierFirstSquare v = 0 := by
  let L : AmplifierAux →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hfun : amplifierFirstSquare =
      (fun y : ℝ ↦ ‖y‖ ^ 2) ∘ L := by
    funext y
    simp [amplifierFirstSquare, L, Real.norm_eq_abs, sq_abs]
  rw [hfun, L.iteratedFDeriv_comp_right (contDiff_norm_sq ℝ) v
    (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top),
    iteratedFDeriv_norm_sq_three_eq_zero]
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem iteratedFDeriv_amplifierSecondSquare_three_eq_zero
    (v : AmplifierAux) :
    iteratedFDeriv ℝ 3 amplifierSecondSquare v = 0 := by
  let L : AmplifierAux →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfun : amplifierSecondSquare =
      (fun y : ℝ ↦ ‖y‖ ^ 2) ∘ L := by
    funext y
    simp [amplifierSecondSquare, L, Real.norm_eq_abs, sq_abs]
  rw [hfun, L.iteratedFDeriv_comp_right (contDiff_norm_sq ℝ) v
    (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top),
    iteratedFDeriv_norm_sq_three_eq_zero]
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem amplifierQuadratic_function_identity (kappa : ℝ) :
    amplifierQuadratic kappa =
      (amplifierDiag kappa / (2 * kappa)) •
          (amplifierFirstSquare + amplifierSecondSquare) -
        (amplifierOffDiag kappa / kappa) •
          (mixedInner : AmplifierAux → ℝ) := by
  funext v
  simp [amplifierQuadratic, amplifierFirstSquare,
    amplifierSecondSquare, mixedInner]
  ring

set_option maxHeartbeats 800000 in
-- Expanding the second derivative of three scalar quadratic pieces is costly.
theorem iteratedFDeriv_amplifierQuadratic_two_apply
    (kappa : ℝ) (v : AmplifierAux) (m : Fin 2 → AmplifierAux) :
    iteratedFDeriv ℝ 2 (amplifierQuadratic kappa) v m =
      amplifierHessianForm kappa (m 0) (m 1) := by
  let A : AmplifierAux → ℝ :=
    amplifierFirstSquare + amplifierSecondSquare
  let C : AmplifierAux → ℝ := mixedInner
  have hA : ContDiff ℝ ∞ A :=
    amplifierFirstSquare_contDiff.add amplifierSecondSquare_contDiff
  have hC : ContDiff ℝ ∞ C := mixedInner_contDiff
  have hAAt : ContDiffAt ℝ 2 A v :=
    (hA.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hCAt : ContDiffAt ℝ 2 C v :=
    (hC.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  rw [amplifierQuadratic_function_identity]
  change (iteratedFDeriv ℝ 2
    ((fun y ↦ (amplifierDiag kappa / (2 * kappa)) • A y) -
      fun y ↦ (amplifierOffDiag kappa / kappa) • C y) v) m = _
  rw [iteratedFDeriv_sub_apply
      ((hA.const_smul (amplifierDiag kappa / (2 * kappa))).of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
      ((hC.const_smul (amplifierOffDiag kappa / kappa)).of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)]
  change ((iteratedFDeriv ℝ 2
      ((amplifierDiag kappa / (2 * kappa)) • A) v -
    iteratedFDeriv ℝ 2
      ((amplifierOffDiag kappa / kappa) • C) v) m) = _
  rw [
    iteratedFDeriv_const_smul_apply hAAt,
    iteratedFDeriv_const_smul_apply hCAt]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [show iteratedFDeriv ℝ 2 A v =
      iteratedFDeriv ℝ 2 amplifierFirstSquare v +
        iteratedFDeriv ℝ 2 amplifierSecondSquare v by
      exact iteratedFDeriv_add_apply
        ((amplifierFirstSquare_contDiff.of_le
          (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
        ((amplifierSecondSquare_contDiff.of_le
          (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
  simp only [add_apply]
  rw [iteratedFDeriv_amplifierFirstSquare_two_apply,
    iteratedFDeriv_amplifierSecondSquare_two_apply,
    iteratedFDeriv_mixedInner_two_apply]
  rw [Real.inner_apply, Real.inner_apply]
  unfold amplifierHessianForm
  ring

set_option maxHeartbeats 800000 in
-- The corresponding third-derivative cancellation traverses the same sum.
theorem iteratedFDeriv_amplifierQuadratic_three_eq_zero
    (kappa : ℝ) (v : AmplifierAux) :
    iteratedFDeriv ℝ 3 (amplifierQuadratic kappa) v = 0 := by
  let A : AmplifierAux → ℝ :=
    amplifierFirstSquare + amplifierSecondSquare
  let C : AmplifierAux → ℝ := mixedInner
  have hA : ContDiff ℝ ∞ A :=
    amplifierFirstSquare_contDiff.add amplifierSecondSquare_contDiff
  have hC : ContDiff ℝ ∞ C := mixedInner_contDiff
  have hAAt : ContDiffAt ℝ 3 A v :=
    (hA.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hCAt : ContDiffAt ℝ 3 C v :=
    (hC.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  rw [amplifierQuadratic_function_identity]
  change iteratedFDeriv ℝ 3
    ((fun y ↦ (amplifierDiag kappa / (2 * kappa)) • A y) -
      fun y ↦ (amplifierOffDiag kappa / kappa) • C y) v = _
  rw [iteratedFDeriv_sub_apply
      ((hA.const_smul (amplifierDiag kappa / (2 * kappa))).of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
      ((hC.const_smul (amplifierOffDiag kappa / kappa)).of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)]
  change iteratedFDeriv ℝ 3
      ((amplifierDiag kappa / (2 * kappa)) • A) v -
    iteratedFDeriv ℝ 3
      ((amplifierOffDiag kappa / kappa) • C) v = _
  rw [
    iteratedFDeriv_const_smul_apply hAAt,
    iteratedFDeriv_const_smul_apply hCAt]
  rw [show iteratedFDeriv ℝ 3 A v =
      iteratedFDeriv ℝ 3 amplifierFirstSquare v +
        iteratedFDeriv ℝ 3 amplifierSecondSquare v by
      exact iteratedFDeriv_add_apply
        ((amplifierFirstSquare_contDiff.of_le
          (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
        ((amplifierSecondSquare_contDiff.of_le
          (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
  rw [iteratedFDeriv_amplifierFirstSquare_three_eq_zero,
    iteratedFDeriv_amplifierSecondSquare_three_eq_zero,
    iteratedFDeriv_mixedInner_three_eq_zero]
  simp

/-! ## Uniform spectral estimates for the amplifier -/

theorem amplifierHessianForm_norm_coercive
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (v : AmplifierAux) :
    (1 / kappa) * ‖v‖ ^ 2 ≤ amplifierHessianForm kappa v v := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hraw := amplifierHessianForm_coercive hkappa v
  rw [Prod.norm_def]
  rcases max_cases ‖v.1‖ ‖v.2‖ with hfirst | hsecond
  · rw [hfirst.1]
    calc
      (1 / kappa) * ‖v.1‖ ^ 2 =
          (1 / kappa) * v.1 ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (1 / kappa) * (v.1 ^ 2 + v.2 ^ 2) := by
        gcongr
        nlinarith [sq_nonneg v.2]
      _ ≤ amplifierHessianForm kappa v v := hraw
  · rw [hsecond.1]
    calc
      (1 / kappa) * ‖v.2‖ ^ 2 =
          (1 / kappa) * v.2 ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (1 / kappa) * (v.1 ^ 2 + v.2 ^ 2) := by
        gcongr
        nlinarith [sq_nonneg v.1]
      _ ≤ amplifierHessianForm kappa v v := hraw

theorem norm_iteratedFDeriv_amplifierQuadratic_two_le_four
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (v : AmplifierAux) :
    ‖iteratedFDeriv ℝ 2 (amplifierQuadratic kappa) v‖ ≤ 4 := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hd0 : 0 ≤ amplifierDiag kappa / kappa :=
    div_nonneg (amplifierDiag_pos hkpos).le hkpos.le
  have hd1 : amplifierDiag kappa / kappa ≤ 1 := by
    exact (div_le_one hkpos).2 (amplifierDiag_le_kappa hkappa)
  have hs0 : 0 ≤ amplifierOffDiag kappa / kappa := by
    have hs : 0 ≤ amplifierOffDiag kappa := by
      unfold amplifierOffDiag
      linarith
    exact div_nonneg hs hkpos.le
  have hs1 : amplifierOffDiag kappa / kappa ≤ 1 := by
    apply (div_le_one hkpos).2
    unfold amplifierOffDiag
    linarith
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  rw [Real.norm_eq_abs,
    iteratedFDeriv_amplifierQuadratic_two_apply]
  unfold amplifierHessianForm
  have hcoord (i : Fin 2) (j : Fin 2) :
      |(m i).1 * (m j).1| ≤ ‖m i‖ * ‖m j‖ := by
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
      (norm_nonneg _) (norm_nonneg _)
  have hcross (i : Fin 2) (j : Fin 2) :
      |(m i).1 * (m j).2| ≤ ‖m i‖ * ‖m j‖ := by
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _)
      (norm_nonneg _) (norm_nonneg _)
  have hsecond (i : Fin 2) (j : Fin 2) :
      |(m i).2 * (m j).2| ≤ ‖m i‖ * ‖m j‖ := by
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
      (norm_nonneg _) (norm_nonneg _)
  have hA :
      |amplifierDiag kappa / kappa *
          ((m 0).1 * (m 1).1 + (m 0).2 * (m 1).2)| ≤
        2 * (‖m 0‖ * ‖m 1‖) := by
    rw [abs_mul, abs_of_nonneg hd0]
    calc
      amplifierDiag kappa / kappa *
          |(m 0).1 * (m 1).1 + (m 0).2 * (m 1).2| ≤
          1 * (|(m 0).1 * (m 1).1| +
            |(m 0).2 * (m 1).2|) := by
              gcongr
              exact abs_add_le _ _
      _ ≤ 2 * (‖m 0‖ * ‖m 1‖) := by
        have h1 := hcoord 0 1
        have h2 := hsecond 0 1
        linarith
  have hB :
      |amplifierOffDiag kappa / kappa *
          ((m 0).1 * (m 1).2 + (m 0).2 * (m 1).1)| ≤
        2 * (‖m 0‖ * ‖m 1‖) := by
    rw [abs_mul, abs_of_nonneg hs0]
    calc
      amplifierOffDiag kappa / kappa *
          |(m 0).1 * (m 1).2 + (m 0).2 * (m 1).1| ≤
          1 * (|(m 0).1 * (m 1).2| +
            |(m 0).2 * (m 1).1|) := by
              gcongr
              exact abs_add_le _ _
      _ ≤ 2 * (‖m 0‖ * ‖m 1‖) := by
        have h1 := hcross 0 1
        have h2 : |(m 0).2 * (m 1).1| ≤ ‖m 0‖ * ‖m 1‖ := by
          rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
          exact mul_le_mul (le_max_right _ _) (le_max_left _ _)
            (norm_nonneg _) (norm_nonneg _)
        linarith
  calc
    |amplifierDiag kappa / kappa *
          ((m 0).1 * (m 1).1 + (m 0).2 * (m 1).2) -
        amplifierOffDiag kappa / kappa *
          ((m 0).1 * (m 1).2 + (m 0).2 * (m 1).1)| ≤
        |amplifierDiag kappa / kappa *
          ((m 0).1 * (m 1).1 + (m 0).2 * (m 1).2)| +
        |amplifierOffDiag kappa / kappa *
          ((m 0).1 * (m 1).2 + (m 0).2 * (m 1).1)| := by
            simpa using abs_sub_le
              (amplifierDiag kappa / kappa *
                ((m 0).1 * (m 1).1 + (m 0).2 * (m 1).2)) 0
              (amplifierOffDiag kappa / kappa *
                ((m 0).1 * (m 1).2 + (m 0).2 * (m 1).1))
    _ ≤ 4 * (‖m 0‖ * ‖m 1‖) := by linarith
    _ = 4 * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_two]

/-! ## The complete joint quadratic on `(x,z,v1,v2)` -/

def kappaEightFullZProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × AmplifierAux)) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E AmplifierAux).comp
    (ContinuousLinearMap.snd ℝ E (E × AmplifierAux))

def kappaEightFullXZProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × AmplifierAux)) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E (E × AmplifierAux)).prod
    kappaEightFullZProjection

def kappaEightFullAuxProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × AmplifierAux)) →L[ℝ] AmplifierAux :=
  (ContinuousLinearMap.snd ℝ E AmplifierAux).comp
    (ContinuousLinearMap.snd ℝ E (E × AmplifierAux))

@[simp] theorem kappaEightFullZProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × AmplifierAux)) :
    kappaEightFullZProjection p = p.2.1 := rfl

@[simp] theorem kappaEightFullXZProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × AmplifierAux)) :
    kappaEightFullXZProjection p = (p.1, p.2.1) := rfl

@[simp] theorem kappaEightFullAuxProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × AmplifierAux)) :
    kappaEightFullAuxProjection p = p.2.2 := rfl

theorem norm_kappaEightFullZProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightFullZProjection :
      (E × (E × AmplifierAux)) →L[ℝ] E)‖ ≤ 1 := by
  calc
    ‖(kappaEightFullZProjection :
        (E × (E × AmplifierAux)) →L[ℝ] E)‖ ≤
        ‖ContinuousLinearMap.fst ℝ E AmplifierAux‖ *
          ‖ContinuousLinearMap.snd ℝ E (E × AmplifierAux)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_fst_le ℝ E AmplifierAux)
      (ContinuousLinearMap.norm_snd_le ℝ E (E × AmplifierAux))
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

theorem norm_kappaEightFullXZProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightFullXZProjection :
      (E × (E × AmplifierAux)) →L[ℝ] (E × E))‖ ≤ 1 := by
  rw [kappaEightFullXZProjection, ContinuousLinearMap.opNorm_prod,
    Prod.norm_def]
  exact max_le
    (ContinuousLinearMap.norm_fst_le ℝ E (E × AmplifierAux))
    (norm_kappaEightFullZProjection_le_one (E := E))

theorem norm_kappaEightFullAuxProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightFullAuxProjection :
      (E × (E × AmplifierAux)) →L[ℝ] AmplifierAux)‖ ≤ 1 := by
  calc
    ‖(kappaEightFullAuxProjection :
        (E × (E × AmplifierAux)) →L[ℝ] AmplifierAux)‖ ≤
        ‖ContinuousLinearMap.snd ℝ E AmplifierAux‖ *
          ‖ContinuousLinearMap.snd ℝ E (E × AmplifierAux)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_snd_le ℝ E AmplifierAux)
      (ContinuousLinearMap.norm_snd_le ℝ E (E × AmplifierAux))
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

def kappaEightFullScaledNormSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) : E × (E × AmplifierAux) → ℝ :=
  (scaledNormSq kappa) ∘ kappaEightFullZProjection

def kappaEightFullNegativeMixedInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E × (E × AmplifierAux) → ℝ :=
  negativeMixedInner ∘ kappaEightFullXZProjection

def kappaEightFullAmplifierQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : ℝ) : E × (E × AmplifierAux) → ℝ :=
  (amplifierQuadratic kappa) ∘ kappaEightFullAuxProjection

def kappaEightFullBaseQuadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) : E × (E × AmplifierAux) → ℝ :=
  (kappaEightFullScaledNormSq kappa +
    kappaEightFullNegativeMixedInner) +
      kappaEightFullAmplifierQuadratic kappa

@[simp] theorem kappaEightFullBaseQuadratic_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (p : E × (E × AmplifierAux)) :
    kappaEightFullBaseQuadratic kappa p =
      ‖p.2.1‖ ^ 2 / (2 * kappa) - inner ℝ p.1 p.2.1 +
        amplifierQuadratic kappa p.2.2 := by
  rfl

theorem kappaEightFullBaseQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) :
    ContDiff ℝ ∞ (kappaEightFullBaseQuadratic kappa :
      E × (E × AmplifierAux) → ℝ) := by
  exact (((scaledNormSq_contDiff kappa).comp
    (kappaEightFullZProjection (E := E)).contDiff).add
      (negativeMixedInner_contDiff.comp
        (kappaEightFullXZProjection (E := E)).contDiff)).add
    ((amplifierQuadratic_contDiff kappa).comp
      (kappaEightFullAuxProjection (E := E)).contDiff)

set_option maxHeartbeats 800000 in
-- Three composed Hessian bounds are aggregated on the four-block product.
theorem norm_iteratedFDeriv_kappaEightFullBaseQuadratic_two_le_eight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : 1 ≤ kappa)
    (p : E × (E × AmplifierAux)) :
    ‖iteratedFDeriv ℝ 2 (kappaEightFullBaseQuadratic kappa) p‖ ≤ 8 := by
  have hA : ContDiff ℝ ∞
      (kappaEightFullScaledNormSq kappa :
        E × (E × AmplifierAux) → ℝ) :=
    (scaledNormSq_contDiff kappa).comp
      (kappaEightFullZProjection (E := E)).contDiff
  have hB : ContDiff ℝ ∞
      (kappaEightFullNegativeMixedInner :
        E × (E × AmplifierAux) → ℝ) :=
    negativeMixedInner_contDiff.comp
      (kappaEightFullXZProjection (E := E)).contDiff
  have hC : ContDiff ℝ ∞
      (kappaEightFullAmplifierQuadratic kappa :
        E × (E × AmplifierAux) → ℝ) :=
    (amplifierQuadratic_contDiff kappa).comp
      (kappaEightFullAuxProjection (E := E)).contDiff
  have hA2 : ‖iteratedFDeriv ℝ 2
      (kappaEightFullScaledNormSq kappa :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (scaledNormSq_contDiff kappa) (kappaEightFullZProjection (E := E))
      (norm_kappaEightFullZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_scaledNormSq_two_le_two hkappa p.2.1)
  have hB2 : ‖iteratedFDeriv ℝ 2
      (kappaEightFullNegativeMixedInner :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      negativeMixedInner_contDiff (kappaEightFullXZProjection (E := E))
      (norm_kappaEightFullXZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_negativeMixedInner_two_le_two (p.1, p.2.1))
  have hC2 : ‖iteratedFDeriv ℝ 2
      (kappaEightFullAmplifierQuadratic kappa :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 4 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (amplifierQuadratic_contDiff kappa)
      (kappaEightFullAuxProjection (E := E))
      (norm_kappaEightFullAuxProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_amplifierQuadratic_two_le_four hkappa p.2.2)
  exact (norm_iteratedFDeriv_three_sum_le hA hB hC 2 p hA2 hB2 hC2).trans_eq
    (by norm_num)

set_option maxHeartbeats 800000 in
-- Each composed component is quadratic, hence its third derivative vanishes.
theorem iteratedFDeriv_kappaEightFullBaseQuadratic_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (p : E × (E × AmplifierAux)) :
    iteratedFDeriv ℝ 3 (kappaEightFullBaseQuadratic kappa) p = 0 := by
  have hA : ‖iteratedFDeriv ℝ 3
      (kappaEightFullScaledNormSq kappa :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (scaledNormSq_contDiff kappa) (kappaEightFullZProjection (E := E))
      (norm_kappaEightFullZProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_scaledNormSq_three_eq_zero, norm_zero])
  have hB : ‖iteratedFDeriv ℝ 3
      (kappaEightFullNegativeMixedInner :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      negativeMixedInner_contDiff (kappaEightFullXZProjection (E := E))
      (norm_kappaEightFullXZProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_negativeMixedInner_three_eq_zero, norm_zero])
  have hC : ‖iteratedFDeriv ℝ 3
      (kappaEightFullAmplifierQuadratic kappa :
        E × (E × AmplifierAux) → ℝ) p‖ ≤ 0 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (amplifierQuadratic_contDiff kappa)
      (kappaEightFullAuxProjection (E := E))
      (norm_kappaEightFullAuxProjection_le_one (E := E)) 3 p).trans_eq (by
        rw [iteratedFDeriv_amplifierQuadratic_three_eq_zero, norm_zero])
  have hAs : ContDiff ℝ ∞
      (kappaEightFullScaledNormSq kappa :
        E × (E × AmplifierAux) → ℝ) :=
    (scaledNormSq_contDiff kappa).comp
      (kappaEightFullZProjection (E := E)).contDiff
  have hBs : ContDiff ℝ ∞
      (kappaEightFullNegativeMixedInner :
        E × (E × AmplifierAux) → ℝ) :=
    negativeMixedInner_contDiff.comp
      (kappaEightFullXZProjection (E := E)).contDiff
  have hCs : ContDiff ℝ ∞
      (kappaEightFullAmplifierQuadratic kappa :
        E × (E × AmplifierAux) → ℝ) :=
    (amplifierQuadratic_contDiff kappa).comp
      (kappaEightFullAuxProjection (E := E)).contDiff
  have hsum : ‖iteratedFDeriv ℝ 3
      ((kappaEightFullScaledNormSq kappa +
        kappaEightFullNegativeMixedInner) +
          kappaEightFullAmplifierQuadratic kappa) p‖ ≤ 0 := by
    simpa using norm_iteratedFDeriv_three_sum_le
      hAs hBs hCs 3 p hA hB hC
  exact norm_eq_zero.mp (le_antisymm hsum (norm_nonneg _))

def kappaEightFullLowerProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × AmplifierAux)) →L[ℝ] (E × AmplifierAux) :=
  ContinuousLinearMap.snd ℝ E (E × AmplifierAux)

@[simp] theorem kappaEightFullLowerProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × AmplifierAux)) :
    kappaEightFullLowerProjection p = p.2 := rfl

theorem norm_kappaEightFullLowerProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightFullLowerProjection :
      (E × (E × AmplifierAux)) →L[ℝ] (E × AmplifierAux))‖ ≤ 1 :=
  ContinuousLinearMap.norm_snd_le ℝ E (E × AmplifierAux)

def kappaEightFullCompensatedPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta kappa : ℝ) (theta : E → ℝ) :
    E × (E × AmplifierAux) → ℝ :=
  (kappaEightCompensatedPair eta kappa theta) ∘
    kappaEightFullLowerProjection

theorem kappaEightFullCompensatedPair_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} (heta : eta ≠ 0) {theta : E → ℝ}
    (htheta : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (kappaEightFullCompensatedPair eta kappa theta) :=
  (kappaEightCompensatedPair_contDiff heta htheta).comp
    (kappaEightFullLowerProjection (E := E)).contDiff

def kappaEightFullPopulationLower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta : ℝ) (L : E →L[ℝ] ChainVector T) :
    E × (E × AmplifierAux) → ℝ :=
  lowerPopulationSum (kappaEightFullBaseQuadratic kappa)
    (kappaEightFullCompensatedPair eta kappa (hardFrontierMap eta L))

@[simp] theorem kappaEightFullPopulationLower_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta : ℝ) (L : E →L[ℝ] ChainVector T)
    (p : E × (E × AmplifierAux)) :
    kappaEightFullPopulationLower kappa eta L p =
      kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
        p.1 p.2.1 p.2.2 := by
  simp [kappaEightFullPopulationLower, lowerPopulationSum,
    kappaEightFullBaseQuadratic, kappaEightFullScaledNormSq,
    kappaEightFullNegativeMixedInner, kappaEightFullAmplifierQuadratic,
    kappaEightFullCompensatedPair, kappaEightPopulationLower,
    kappaEightCompensatedPair, amplifiedScalarBlock, scaledNormSq,
    negativeMixedInner, mixedInner]
  ring

theorem kappaEightFullPopulationLower_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (kappa : ℝ) (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (kappaEightFullPopulationLower kappa eta L) := by
  exact lowerPopulationSum_contDiff
    (kappaEightFullBaseQuadratic_contDiff kappa)
    (kappaEightFullCompensatedPair_contDiff heta.ne'
      (hardFrontierMap_contDiff heta hT L))

set_option maxHeartbeats 800000 in
-- The wrapper instantiates all joint-variable compositions uniformly.
theorem exists_kappaEightFullPopulationLower_regularities :
    ∃ CHess Cthird : ℝ, 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {kappa eta : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ p : E × (E × AmplifierAux),
          ‖iteratedFDeriv ℝ 2
            (kappaEightFullPopulationLower kappa eta L) p‖ ≤
              8 + CHess * eta / kappa) ∧
        (∀ p : E × (E × AmplifierAux),
          ‖iteratedFDeriv ℝ 3
            (kappaEightFullPopulationLower kappa eta L) p‖ ≤
              Cthird / kappa) ∧
        (∀ p q : E × (E × AmplifierAux),
          ‖fderiv ℝ (kappaEightFullPopulationLower kappa eta L) q -
              fderiv ℝ (kappaEightFullPopulationLower kappa eta L) p‖ ≤
            (8 + CHess * eta / kappa) * ‖q - p‖) ∧
        (∀ p q : E × (E × AmplifierAux),
          ‖iteratedFDeriv ℝ 2
              (kappaEightFullPopulationLower kappa eta L) q -
            iteratedFDeriv ℝ 2
              (kappaEightFullPopulationLower kappa eta L) p‖ ≤
            (Cthird / kappa) * ‖q - p‖) := by
  obtain ⟨Cnoise, CHess, Cthird, hCnoise, hCHess, hCthird, hreg⟩ :=
    exists_kappaEight_hard_compensated_pair_regularities
  refine ⟨CHess, Cthird, hCHess, hCthird, ?_⟩
  intro E _ _ T kappa eta heta heta1 hkappa hT L hL
  let theta : E → ℝ := hardFrontierMap eta L
  let perturbation : E × (E × AmplifierAux) → ℝ :=
    kappaEightFullCompensatedPair eta kappa theta
  have htheta : ContDiff ℝ ∞ theta := hardFrontierMap_contDiff heta hT L
  have hpert : ContDiff ℝ ∞ perturbation :=
    kappaEightFullCompensatedPair_contDiff heta.ne' htheta
  have hraw (p : E × (E × AmplifierAux)) :=
    hreg heta heta1 hkappa hT hL p.2
  have hpert2 (p : E × (E × AmplifierAux)) :
      ‖iteratedFDeriv ℝ 2 perturbation p‖ ≤ CHess * eta / kappa :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightCompensatedPair_contDiff heta.ne' htheta)
      (kappaEightFullLowerProjection (E := E))
      (norm_kappaEightFullLowerProjection_le_one (E := E)) 2 p).trans
        (hraw p).2.1
  have hpert3 (p : E × (E × AmplifierAux)) :
      ‖iteratedFDeriv ℝ 3 perturbation p‖ ≤ Cthird / kappa :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightCompensatedPair_contDiff heta.ne' htheta)
      (kappaEightFullLowerProjection (E := E))
      (norm_kappaEightFullLowerProjection_le_one (E := E)) 3 p).trans
        (hraw p).2.2
  have hbase := kappaEightFullBaseQuadratic_contDiff (E := E) kappa
  have hbase2 (p : E × (E × AmplifierAux)) :=
    norm_iteratedFDeriv_kappaEightFullBaseQuadratic_two_le_eight
      (show 1 ≤ kappa by linarith) p
  have hbase3 (p : E × (E × AmplifierAux)) :=
    iteratedFDeriv_kappaEightFullBaseQuadratic_three_eq_zero kappa p
  change
    (∀ p, ‖iteratedFDeriv ℝ 2
      (lowerPopulationSum (kappaEightFullBaseQuadratic kappa)
        perturbation) p‖ ≤ 8 + CHess * eta / kappa) ∧ _
  refine ⟨lowerPopulationSum_second_bound hbase hpert hbase2 hpert2, ?_⟩
  refine ⟨lowerPopulationSum_third_bound hbase hpert hbase3 hpert3, ?_⟩
  refine ⟨lowerPopulationSum_gradient_lipschitz
    hbase hpert hbase2 hpert2, ?_⟩
  exact lowerPopulationSum_hessian_lipschitz
    hbase hpert hbase3 hpert3

/-! ## The complete lower quadratic slice -/

def kappaEightFixedNegativeInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) : ℝ :=
  -inner ℝ x z

theorem kappaEightFixedNegativeInner_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) :
    ContDiff ℝ ∞ (kappaEightFixedNegativeInner x : E → ℝ) := by
  let L : E →L[ℝ] ℝ := -(innerSL ℝ x)
  have hfun : (kappaEightFixedNegativeInner x : E → ℝ) = L := by
    funext y
    simp [kappaEightFixedNegativeInner, L, innerSL_apply_apply]
  rw [hfun]
  exact L.contDiff

theorem iteratedFDeriv_kappaEightFixedNegativeInner_two_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) :
    iteratedFDeriv ℝ 2 (kappaEightFixedNegativeInner x : E → ℝ) z = 0 := by
  ext m
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fun y : E ↦
    fderiv ℝ (kappaEightFixedNegativeInner x : E → ℝ) y) z)
      (m 0)) (m 1) = 0
  have hfd : (fun y : E ↦
      fderiv ℝ (kappaEightFixedNegativeInner x : E → ℝ) y) =
      fun _ : E ↦ -(innerSL ℝ x) := by
    funext y
    let L : E →L[ℝ] ℝ := -(innerSL ℝ x)
    have hfun : (kappaEightFixedNegativeInner x : E → ℝ) = L := by
      funext w
      simp [kappaEightFixedNegativeInner, L, innerSL_apply_apply]
    rw [hfun]
    exact L.fderiv
  rw [hfd]
  simp

theorem iteratedFDeriv_kappaEightFixedNegativeInner_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) :
    iteratedFDeriv ℝ 3 (kappaEightFixedNegativeInner x : E → ℝ) z = 0 := by
  have hD2Diff : DifferentiableAt ℝ
      (iteratedFDeriv ℝ 2
        (kappaEightFixedNegativeInner x : E → ℝ)) z :=
    (kappaEightFixedNegativeInner_contDiff x).contDiffAt
      |>.differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2)
  ext m
  rw [hD2Diff.iteratedFDeriv_succ_apply_left']
  have hfun :
      (fun y : E ↦ iteratedFDeriv ℝ 2
        (kappaEightFixedNegativeInner x : E → ℝ) y (Fin.tail m)) =
      fun _ : E ↦ 0 := by
    funext y
    rw [iteratedFDeriv_kappaEightFixedNegativeInner_two_eq_zero]
    rfl
  rw [hfun]
  simp

def kappaEightLowerBaseSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (x : E) : E × AmplifierAux → ℝ :=
  fun p ↦ scaledNormSq kappa p.1 +
    kappaEightFixedNegativeInner x p.1 + amplifierQuadratic kappa p.2

@[simp] theorem kappaEightLowerBaseSlice_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (x : E) (p : E × AmplifierAux) :
    kappaEightLowerBaseSlice kappa x p =
      ‖p.1‖ ^ 2 / (2 * kappa) - inner ℝ x p.1 +
        amplifierQuadratic kappa p.2 := by
  simp [kappaEightLowerBaseSlice, scaledNormSq,
    kappaEightFixedNegativeInner]
  ring

theorem kappaEightLowerBaseSlice_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (x : E) :
    ContDiff ℝ ∞ (kappaEightLowerBaseSlice kappa x) := by
  exact (((scaledNormSq_contDiff kappa).comp contDiff_fst).add
    ((kappaEightFixedNegativeInner_contDiff x).comp contDiff_fst)).add
      ((amplifierQuadratic_contDiff kappa).comp contDiff_snd)

theorem kappaEightPopulationLower_eq_base_add_compensation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa eta : ℝ) (theta : E → ℝ) (x : E) :
    (fun p : E × AmplifierAux ↦
      kappaEightPopulationLower kappa eta theta x p.1 p.2) =
      lowerPopulationSum (kappaEightLowerBaseSlice kappa x)
        (kappaEightCompensatedPair eta kappa theta) := by
  funext p
  simp [kappaEightPopulationLower, kappaEightLowerBaseSlice,
    kappaEightCompensatedPair, amplifiedScalarBlock,
    lowerPopulationSum, scaledNormSq, kappaEightFixedNegativeInner]
  ring

theorem kappaEight_iteratedFDeriv_scaledNormSq_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : kappa ≠ 0) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (scaledNormSq kappa : E → ℝ) z m =
      (1 / kappa) * inner ℝ (m 0) (m 1) := by
  have hfun : (scaledNormSq kappa : E → ℝ) =
      (2 * kappa)⁻¹ • (fun y : E ↦ ‖y‖ ^ 2) := by
    funext y
    simp [scaledNormSq, div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
  simp only [smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_norm_sq_two_apply]
  field_simp [hkappa]

set_option maxHeartbeats 800000 in
-- Three composed Hessians on the nested product are normalized explicitly.
theorem iteratedFDeriv_kappaEightLowerBaseSlice_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : kappa ≠ 0) (x : E)
    (p : E × AmplifierAux) (m : Fin 2 → E × AmplifierAux) :
    iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p m =
      (1 / kappa) * inner ℝ (m 0).1 (m 1).1 +
        amplifierHessianForm kappa (m 0).2 (m 1).2 := by
  let Lz : (E × AmplifierAux) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Lv : (E × AmplifierAux) →L[ℝ] AmplifierAux :=
    ContinuousLinearMap.snd ℝ E AmplifierAux
  let A : E × AmplifierAux → ℝ := (scaledNormSq kappa) ∘ Lz
  let B : E × AmplifierAux → ℝ :=
    (kappaEightFixedNegativeInner x) ∘ Lz
  let C : E × AmplifierAux → ℝ := (amplifierQuadratic kappa) ∘ Lv
  have hA : ContDiff ℝ ∞ A := (scaledNormSq_contDiff kappa).comp Lz.contDiff
  have hB : ContDiff ℝ ∞ B :=
    (kappaEightFixedNegativeInner_contDiff x).comp Lz.contDiff
  have hC : ContDiff ℝ ∞ C :=
    (amplifierQuadratic_contDiff kappa).comp Lv.contDiff
  have hAAt : ContDiffAt ℝ 2 A p :=
    (hA.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hBAt : ContDiffAt ℝ 2 B p :=
    (hB.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hCAt : ContDiffAt ℝ 2 C p :=
    (hC.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  change iteratedFDeriv ℝ 2 ((A + B) + C) p m = _
  rw [show iteratedFDeriv ℝ 2 ((A + B) + C) p =
      iteratedFDeriv ℝ 2 (A + B) p + iteratedFDeriv ℝ 2 C p by
        exact iteratedFDeriv_add_apply (hAAt.add hBAt) hCAt,
    show iteratedFDeriv ℝ 2 (A + B) p =
      iteratedFDeriv ℝ 2 A p + iteratedFDeriv ℝ 2 B p by
        exact iteratedFDeriv_add_apply hAAt hBAt]
  simp only [add_apply]
  rw [Lz.iteratedFDeriv_comp_right (scaledNormSq_contDiff kappa) p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lz.iteratedFDeriv_comp_right
      (kappaEightFixedNegativeInner_contDiff x) p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lv.iteratedFDeriv_comp_right (amplifierQuadratic_contDiff kappa) p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [kappaEight_iteratedFDeriv_scaledNormSq_two_apply hkappa,
    iteratedFDeriv_kappaEightFixedNegativeInner_two_eq_zero,
    iteratedFDeriv_amplifierQuadratic_two_apply]
  simp [Lz, Lv]

theorem iteratedFDeriv_kappaEightLowerBaseSlice_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa : ℝ) (x : E) (p : E × AmplifierAux) :
    iteratedFDeriv ℝ 3 (kappaEightLowerBaseSlice kappa x) p = 0 := by
  let Lz : (E × AmplifierAux) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Lv : (E × AmplifierAux) →L[ℝ] AmplifierAux :=
    ContinuousLinearMap.snd ℝ E AmplifierAux
  let A : E × AmplifierAux → ℝ := (scaledNormSq kappa) ∘ Lz
  let B : E × AmplifierAux → ℝ :=
    (kappaEightFixedNegativeInner x) ∘ Lz
  let C : E × AmplifierAux → ℝ := (amplifierQuadratic kappa) ∘ Lv
  have hA : ContDiff ℝ ∞ A := (scaledNormSq_contDiff kappa).comp Lz.contDiff
  have hB : ContDiff ℝ ∞ B :=
    (kappaEightFixedNegativeInner_contDiff x).comp Lz.contDiff
  have hC : ContDiff ℝ ∞ C :=
    (amplifierQuadratic_contDiff kappa).comp Lv.contDiff
  have hAAt : ContDiffAt ℝ 3 A p :=
    (hA.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hBAt : ContDiffAt ℝ 3 B p :=
    (hB.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hCAt : ContDiffAt ℝ 3 C p :=
    (hC.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  change iteratedFDeriv ℝ 3 ((A + B) + C) p = 0
  rw [show iteratedFDeriv ℝ 3 ((A + B) + C) p =
      iteratedFDeriv ℝ 3 (A + B) p + iteratedFDeriv ℝ 3 C p by
        exact iteratedFDeriv_add_apply (hAAt.add hBAt) hCAt,
    show iteratedFDeriv ℝ 3 (A + B) p =
      iteratedFDeriv ℝ 3 A p + iteratedFDeriv ℝ 3 B p by
        exact iteratedFDeriv_add_apply hAAt hBAt]
  rw [Lz.iteratedFDeriv_comp_right (scaledNormSq_contDiff kappa) p
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lz.iteratedFDeriv_comp_right
      (kappaEightFixedNegativeInner_contDiff x) p
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lv.iteratedFDeriv_comp_right (amplifierQuadratic_contDiff kappa) p
      (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top),
    iteratedFDeriv_scaledNormSq_three_eq_zero,
    iteratedFDeriv_kappaEightFixedNegativeInner_three_eq_zero,
    iteratedFDeriv_amplifierQuadratic_three_eq_zero]
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem kappaEightLowerBaseSlice_diagonal_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : kappa ≠ 0) (x : E)
    (p w : E × AmplifierAux) :
    iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p
        (fun _ ↦ w) =
      (1 / kappa) * ‖w.1‖ ^ 2 +
        amplifierHessianForm kappa w.2 w.2 := by
  rw [iteratedFDeriv_kappaEightLowerBaseSlice_two_apply hkappa]
  rw [real_inner_self_eq_norm_sq]

theorem kappaEightLowerBaseSlice_coercive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (x : E)
    (p w : E × AmplifierAux) :
    (1 / kappa) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p
        (fun _ ↦ w) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  rw [kappaEightLowerBaseSlice_diagonal_hessian hkpos.ne']
  have hz0 : 0 ≤ (1 / kappa) * ‖w.1‖ ^ 2 := by positivity
  have hv := amplifierHessianForm_norm_coercive hkappa w.2
  rw [Prod.norm_def]
  rcases max_cases ‖w.1‖ ‖w.2‖ with hz | hvmax
  · rw [hz.1]
    exact le_add_of_nonneg_right
      (le_trans (by positivity : 0 ≤ (1 / kappa) * ‖w.2‖ ^ 2) hv)
  · rw [hvmax.1]
    exact hv.trans (le_add_of_nonneg_left hz0)

theorem norm_iteratedFDeriv_kappaEightLowerBaseSlice_two_le_six
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (x : E)
    (p : E × AmplifierAux) :
    ‖iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p‖ ≤ 6 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  rw [Real.norm_eq_abs,
    iteratedFDeriv_kappaEightLowerBaseSlice_two_apply
      (lt_of_lt_of_le (by norm_num) hkappa).ne']
  let Hz := (1 / kappa) * inner ℝ (m 0).1 (m 1).1
  let Hv := amplifierHessianForm kappa (m 0).2 (m 1).2
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hinv0 : 0 ≤ 1 / kappa := by positivity
  have hinv1 : 1 / kappa ≤ 1 := (div_le_one hkpos).2 hkappa
  have hz : |Hz| ≤ ‖m 0‖ * ‖m 1‖ := by
    dsimp [Hz]
    rw [abs_mul, abs_of_nonneg hinv0]
    calc
      (1 / kappa) * |inner ℝ (m 0).1 (m 1).1| ≤
          1 * (‖(m 0).1‖ * ‖(m 1).1‖) := by
            gcongr
            exact abs_real_inner_le_norm _ _
      _ ≤ ‖m 0‖ * ‖m 1‖ := by
        rw [one_mul]
        exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
          (norm_nonneg _) (norm_nonneg _)
  have hauxOp := norm_iteratedFDeriv_amplifierQuadratic_two_le_four
    hkappa p.2
  have hauxApply :=
    (iteratedFDeriv ℝ 2 (amplifierQuadratic kappa) p.2).le_opNorm
      (fun i ↦ (m i).2)
  rw [Real.norm_eq_abs,
    iteratedFDeriv_amplifierQuadratic_two_apply,
    Fin.prod_univ_two] at hauxApply
  have hv : |Hv| ≤ 4 * (‖m 0‖ * ‖m 1‖) := by
    dsimp [Hv]
    calc
      |amplifierHessianForm kappa (m 0).2 (m 1).2| ≤
          ‖iteratedFDeriv ℝ 2 (amplifierQuadratic kappa) p.2‖ *
            (‖(m 0).2‖ * ‖(m 1).2‖) := hauxApply
      _ ≤ 4 * (‖m 0‖ * ‖m 1‖) := by
        apply mul_le_mul hauxOp
        · exact mul_le_mul
            (le_max_right ‖(m 0).1‖ ‖(m 0).2‖)
            (le_max_right ‖(m 1).1‖ ‖(m 1).2‖)
            (norm_nonneg (m 1).2) (norm_nonneg (m 0))
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · norm_num
  calc
    |Hz + Hv| ≤ |Hz| + |Hv| := abs_add_le _ _
    _ ≤ 5 * (‖m 0‖ * ‖m 1‖) := by linarith
    _ ≤ 6 * (‖m 0‖ * ‖m 1‖) := by
      gcongr
      norm_num
    _ = 6 * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_two]

/-! ## Perturbation aggregation -/

/-- The exact base quadratic remains `(2*kappa)^{-1}` strongly convex after
adding any smooth perturbation whose full Hessian norm is at most that size.
This theorem includes every `zz`, `zv`, and `vv` mixed block. -/
theorem kappaEightLowerBase_add_perturbation_strong_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (x : E)
    {R : E × AmplifierAux → ℝ} (hR : ContDiff ℝ ∞ R)
    (hR2 : ∀ p, ‖iteratedFDeriv ℝ 2 R p‖ ≤ 1 / (2 * kappa))
    (p w : E × AmplifierAux) :
    (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2
        (lowerPopulationSum (kappaEightLowerBaseSlice kappa x) R) p
          (fun _ ↦ w) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hmu0 : 0 ≤ 1 / kappa := by positivity
  have hdelta0 : 0 ≤ 1 / (2 * kappa) := by positivity
  have hsmall : 1 / (2 * kappa) ≤ 1 / kappa := by
    field_simp [hkpos.ne']
    linarith
  have hraw := lowerPopulationSum_strong_hessian_certificate
    (kappaEightLowerBaseSlice_contDiff kappa x) hR hmu0 hdelta0 hsmall
    (kappaEightLowerBaseSlice_coercive hkappa x) hR2 p w
  have hcoef : 1 / (2 * kappa) = 1 / kappa - 1 / (2 * kappa) := by
    field_simp [hkpos.ne']
    norm_num
  rw [hcoef]
  exact hraw

/-- The population lower objective inherits a full Hessian bound from its
exact quadratic base and the compensated-frontier perturbation. -/
theorem kappaEightPopulationLower_second_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 ≤ kappa) (theta : E → ℝ) (x : E)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    {Ctwo : ℝ}
    (hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤ Ctwo)
    (p : E × AmplifierAux) :
    ‖iteratedFDeriv ℝ 2
      (fun q : E × AmplifierAux ↦
        kappaEightPopulationLower kappa eta theta x q.1 q.2) p‖ ≤
      6 + Ctwo := by
  rw [kappaEightPopulationLower_eq_base_add_compensation]
  exact lowerPopulationSum_second_bound
    (kappaEightLowerBaseSlice_contDiff kappa x) hcomp
    (norm_iteratedFDeriv_kappaEightLowerBaseSlice_two_le_six hkappa x)
    hcomp2 p

/-- The base is exactly quadratic, so the population lower third derivative
is controlled entirely by the compensated frontier. -/
theorem kappaEightPopulationLower_third_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (theta : E → ℝ) (x : E)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    {Cthree : ℝ}
    (hcomp3 : ∀ p,
      ‖iteratedFDeriv ℝ 3
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤ Cthree)
    (p : E × AmplifierAux) :
    ‖iteratedFDeriv ℝ 3
      (fun q : E × AmplifierAux ↦
        kappaEightPopulationLower kappa eta theta x q.1 q.2) p‖ ≤
      Cthree := by
  rw [kappaEightPopulationLower_eq_base_add_compensation]
  exact lowerPopulationSum_third_bound
    (kappaEightLowerBaseSlice_contDiff kappa x) hcomp
    (iteratedFDeriv_kappaEightLowerBaseSlice_three_eq_zero kappa x)
    hcomp3 p

/-- The concrete population lower objective is `(2*kappa)^{-1}` strongly
convex whenever the compensated block has Hessian norm at most that amount. -/
theorem kappaEightPopulationLower_strong_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 ≤ kappa) (theta : E → ℝ) (x : E)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    (hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤
          1 / (2 * kappa))
    (p w : E × AmplifierAux) :
    (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2
        (fun q : E × AmplifierAux ↦
          kappaEightPopulationLower kappa eta theta x q.1 q.2) p
        (fun _ ↦ w) := by
  rw [kappaEightPopulationLower_eq_base_add_compensation]
  exact kappaEightLowerBase_add_perturbation_strong_hessian
    hkappa x hcomp hcomp2 p w

/-- A uniform third-derivative estimate gives the full-Hessian Lipschitz
condition required in the `p = 1` statement. -/
theorem kappaEightPopulationLower_hessian_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (theta : E → ℝ) (x : E)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    {Cthree : ℝ}
    (hcomp3 : ∀ p,
      ‖iteratedFDeriv ℝ 3
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤ Cthree)
    (p q : E × AmplifierAux) :
    ‖iteratedFDeriv ℝ 2
        (fun r : E × AmplifierAux ↦
          kappaEightPopulationLower kappa eta theta x r.1 r.2) q -
      iteratedFDeriv ℝ 2
        (fun r : E × AmplifierAux ↦
          kappaEightPopulationLower kappa eta theta x r.1 r.2) p‖ ≤
      Cthree * ‖q - p‖ := by
  rw [kappaEightPopulationLower_eq_base_add_compensation]
  exact lowerPopulationSum_hessian_lipschitz
    (kappaEightLowerBaseSlice_contDiff kappa x) hcomp
    (iteratedFDeriv_kappaEightLowerBaseSlice_three_eq_zero kappa x)
    hcomp3 p q

/-! ## Concrete certificates for the hidden hard frontier -/

/-- Universal constants for the complete population lower objective.  This
is the direct analytic certificate used by the final hard-instance class:
the Hessian is uniformly bounded, the third derivative is `O(1/kappa)`, the
full Hessian is globally Lipschitz, and the lower slice is
`(2*kappa)^{-1}` strongly convex once `CHess*eta ≤ 1/2`. -/
theorem exists_kappaEightPopulationLower_certificates :
    ∃ Cnoise CHess Cthird : ℝ,
      0 < Cnoise ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta kappa : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ x : E, ContDiff ℝ ∞
          (fun p : E × AmplifierAux ↦
            kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
              x p.1 p.2)) ∧
        (∀ (x : E) (p : E × AmplifierAux),
          ‖iteratedFDeriv ℝ 2
            (fun q : E × AmplifierAux ↦
              kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
                x q.1 q.2) p‖ ≤ 6 + CHess * eta / kappa) ∧
        (∀ (x : E) (p : E × AmplifierAux),
          ‖iteratedFDeriv ℝ 3
            (fun q : E × AmplifierAux ↦
              kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
                x q.1 q.2) p‖ ≤ Cthird / kappa) ∧
        (CHess * eta ≤ 1 / 2 →
          ∀ (x : E) (p w : E × AmplifierAux),
          (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
            iteratedFDeriv ℝ 2
              (fun q : E × AmplifierAux ↦
                kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
                  x q.1 q.2) p (fun _ ↦ w)) ∧
        (∀ (x : E) (p q : E × AmplifierAux),
          ‖iteratedFDeriv ℝ 2
              (fun r : E × AmplifierAux ↦
                kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
                  x r.1 r.2) q -
            iteratedFDeriv ℝ 2
              (fun r : E × AmplifierAux ↦
                kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
                  x r.1 r.2) p‖ ≤
            (Cthird / kappa) * ‖q - p‖) := by
  obtain ⟨Cnoise, CHess, Cthird, hCnoise, hCHess, hCthird, hreg⟩ :=
    exists_kappaEight_hard_compensated_pair_regularities
  refine ⟨Cnoise, CHess, Cthird, hCnoise, hCHess, hCthird, ?_⟩
  intro E _ _ T eta kappa heta heta1 hkappa hT L hL
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have htheta : ContDiff ℝ ∞ (hardFrontierMap eta L) :=
    hardFrontierMap_contDiff heta hT L
  have hcomp : ContDiff ℝ ∞
      (kappaEightCompensatedPair eta kappa (hardFrontierMap eta L)) :=
    kappaEightCompensatedPair_contDiff heta.ne' htheta
  have hbounds (p : E × AmplifierAux) :=
    hreg heta heta1 hkappa hT hL p
  constructor
  · intro x
    rw [kappaEightPopulationLower_eq_base_add_compensation]
    exact lowerPopulationSum_contDiff
      (kappaEightLowerBaseSlice_contDiff kappa x) hcomp
  constructor
  · intro x p
    exact kappaEightPopulationLower_second_bound
      (show 1 ≤ kappa by linarith) (hardFrontierMap eta L) x hcomp
      (fun q ↦ (hbounds q).2.1) p
  constructor
  · intro x p
    exact kappaEightPopulationLower_third_bound
      (hardFrontierMap eta L) x hcomp (fun q ↦ (hbounds q).2.2) p
  constructor
  · intro hsmall x p w
    have hcompSmall : ∀ q : E × AmplifierAux,
        ‖iteratedFDeriv ℝ 2
          (kappaEightCompensatedPair eta kappa
            (hardFrontierMap eta L)) q‖ ≤ 1 / (2 * kappa) := by
      intro q
      calc
        ‖iteratedFDeriv ℝ 2
            (kappaEightCompensatedPair eta kappa
              (hardFrontierMap eta L)) q‖ ≤
            CHess * eta / kappa := (hbounds q).2.1
        _ ≤ (1 / 2) / kappa :=
          (div_le_div_iff_of_pos_right hkpos).2 hsmall
        _ = 1 / (2 * kappa) := by field_simp [hkpos.ne']
    exact kappaEightPopulationLower_strong_hessian
      (show 1 ≤ kappa by linarith) (hardFrontierMap eta L) x
      hcomp hcompSmall p w
  · intro x p q
    exact kappaEightPopulationLower_hessian_lipschitz
      (hardFrontierMap eta L) x hcomp (fun r ↦ (hbounds r).2.2) p q

end

end BilevelLowerBound
