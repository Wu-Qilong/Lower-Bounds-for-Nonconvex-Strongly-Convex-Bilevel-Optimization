/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.CompositionScales

/-!
# Quantitative derivatives of the radial soft projection

This module proves the explicit first-, second-, and third-order derivative
bounds for the radial soft projection used by the hard instance.  It then
postcomposes the projection with an arbitrary contraction, normalizes hidden
coordinates by `eta`, and discharges the hypotheses of the composition-scale
lemmas for the paper radius `230 * eta * sqrt T`.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

def softScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (z : E) : ℝ :=
  (Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2))⁻¹

def softCoeff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (z : E) : ℝ :=
  -(softScale R z) ^ 3 / R ^ 2

def softCoeffFive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (z : E) : ℝ :=
  3 * (softScale R z) ^ 5 / R ^ 4

def softCoeffThree
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (z : E) : ℝ :=
  (softScale R z) ^ 3 / R ^ 2

theorem softScale_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) :
    ContDiff ℝ ∞ (softScale R : E → ℝ) := by
  have hRadicand : ContDiff ℝ ∞
      (fun z : E ↦ 1 + ‖z‖ ^ 2 / R ^ 2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).div_const (R ^ 2))
  have hPos : ∀ z : E, 1 + ‖z‖ ^ 2 / R ^ 2 ≠ 0 := by
    intro z
    have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 := by positivity
    linarith
  unfold softScale
  exact (hRadicand.sqrt hPos).inv (fun z ↦
    (Real.sqrt_pos.2 (by
      have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 := by positivity
      linarith)).ne')

theorem softProjection_eq_softScale_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (z : E) :
    softProjection R z = softScale R z • z := rfl

theorem fderiv_softScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    fderiv ℝ (softScale R : E → ℝ) z =
      (-(softScale R z) ^ 3 / R ^ 2) • innerSL ℝ z := by
  have hpos : 0 < 1 + ‖z‖ ^ 2 / R ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2)
      (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hdiv : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ z)) z := by
    simpa only [div_eq_mul_inv] using hnorm.mul_const (R ^ 2)⁻¹
  have hrad : HasFDerivAt (fun y : E ↦ 1 + ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    hdiv.const_add 1
  have hsqrtDeriv := hrad.sqrt (ne_of_gt hpos)
  have hinv := (hasFDerivAt_inv' hsqrt).comp z hsqrtDeriv
  unfold softScale
  change fderiv ℝ
      (Inv.inv ∘ fun y : E ↦ Real.sqrt (1 + ‖y‖ ^ 2 / R ^ 2)) z = _
  rw [hinv.fderiv]
  ext h
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, innerSL_apply_apply]
  field_simp [hsqrt, hR, Real.sq_sqrt hpos.le]
  simp

theorem softScale_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    0 < softScale R z := by
  unfold softScale
  positivity

theorem softScale_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    softScale R z ≤ 1 := by
  unfold softScale
  apply (inv_le_one₀ (Real.sqrt_pos.2 (by positivity))).2
  rw [Real.one_le_sqrt]
  have hnonneg : 0 ≤ ‖z‖ ^ 2 / R ^ 2 := by positivity
  linarith

theorem softScale_mul_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    softScale R z * ‖z‖ ≤ R := by
  have h := norm_softProjection_le hR z
  rw [softProjection_eq_softScale_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (softScale_pos hR.ne' z)] at h
  exact h

theorem norm_fderiv_softScale_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖fderiv ℝ (softScale R : E → ℝ) z‖ ≤ R⁻¹ := by
  rw [fderiv_softScale hR.ne' z, norm_smul]
  rw [innerSL_apply_norm, Real.norm_eq_abs]
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have ha1 : softScale R z ≤ 1 := softScale_le_one hR.ne' z
  have haz : softScale R z * ‖z‖ ≤ R := softScale_mul_norm_le hR z
  have hR0 : 0 ≤ R := hR.le
  rw [abs_div, abs_neg, abs_pow, abs_of_nonneg ha0, abs_pow,
    abs_of_pos hR]
  rw [inv_eq_one_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hR)).2
  field_simp [hR.ne']
  calc
    softScale R z ^ 3 * ‖z‖ =
        softScale R z ^ 2 * (softScale R z * ‖z‖) := by ring
    _ ≤ 1 * (softScale R z * ‖z‖) := by
      exact mul_le_mul_of_nonneg_right (pow_le_one₀ ha0 ha1)
        (mul_nonneg ha0 (norm_nonneg z))
    _ ≤ R := by simpa using haz

theorem fderiv_softCoeff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    fderiv ℝ (softCoeff R : E → ℝ) z =
      (3 * (softScale R z) ^ 5 / R ^ 4) • innerSL ℝ z := by
  have hAlpha : HasFDerivAt (softScale R : E → ℝ)
      ((-(softScale R z) ^ 3 / R ^ 2) • innerSL ℝ z) z := by
    rw [← fderiv_softScale hR z]
    exact (softScale_contDiff hR).differentiable (by norm_num) z
      |>.hasFDerivAt
  have hpow := hAlpha.pow 3
  have hneg := hpow.neg
  have hdiv := hneg.mul_const (R ^ 2)⁻¹
  have hfun : (softCoeff R : E → ℝ) =
      fun y : E ↦ (-(fun x : E ↦ softScale R x ^ 3)) y * (R ^ 2)⁻¹ := by
    funext y
    simp only [softCoeff, div_eq_mul_inv, Pi.neg_apply]
  rw [hfun, hdiv.fderiv]
  ext h
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    innerSL_apply_apply, neg_apply, Nat.reduceSub, nsmul_eq_mul,
    smul_smul]
  field_simp [hR] <;> ring

theorem iteratedFDeriv_softScale_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z m =
      3 * (softScale R z) ^ 5 / R ^ 4 *
          inner ℝ z (m 0) * inner ℝ z (m 1) -
        (softScale R z) ^ 3 / R ^ 2 * inner ℝ (m 0) (m 1) := by
  have hF : (fun y : E ↦ fderiv ℝ (softScale R : E → ℝ) y) =
      fun y : E ↦ softCoeff R y • innerSL ℝ y := by
    funext y
    rw [fderiv_softScale hR y]
    rfl
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ
    (fun y : E ↦ fderiv ℝ (softScale R : E → ℝ) y) z) (m 0))
      (m 1) = _
  rw [hF]
  have hCoeffDiff : DifferentiableAt ℝ (softCoeff R : E → ℝ) z :=
    ((softScale_contDiff hR).pow 3).neg.div_const (R ^ 2)
      |>.differentiable (by norm_num) z
  have hInnerDiff : DifferentiableAt ℝ
      (fun y : E ↦ innerSL ℝ y) z :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).differentiableAt
  have hInnerFDeriv : fderiv ℝ (fun y : E ↦ innerSL ℝ y) z =
      (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.fderiv
  rw [fderiv_fun_smul hCoeffDiff hInnerDiff]
  rw [fderiv_softCoeff hR z]
  rw [hInnerFDeriv]
  simp only [add_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  unfold softCoeff
  rw [innerSL_apply_apply]
  ring

theorem norm_iteratedFDeriv_softScale_two_le_sharp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ ≤
      3 * (softScale R z) ^ 5 * ‖z‖ ^ 2 / R ^ 4 +
        (softScale R z) ^ 3 / R ^ 2 := by
  let M : ℝ := 3 * (softScale R z) ^ 5 * ‖z‖ ^ 2 / R ^ 4 +
    (softScale R z) ^ 3 / R ^ 2
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  apply ContinuousMultilinearMap.opNorm_le_bound hM0
  intro m
  rw [Real.norm_eq_abs, iteratedFDeriv_softScale_two_apply hR.ne' z m]
  have hc1 : 0 ≤ 3 * (softScale R z) ^ 5 / R ^ 4 := by positivity
  have hc2 : 0 ≤ (softScale R z) ^ 3 / R ^ 2 := by positivity
  have ht1 :
      ‖3 * (softScale R z) ^ 5 / R ^ 4 * inner ℝ z (m 0) *
          inner ℝ z (m 1)‖ ≤
        (3 * (softScale R z) ^ 5 * ‖z‖ ^ 2 / R ^ 4) *
          ‖m 0‖ * ‖m 1‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc1]
    calc
      3 * softScale R z ^ 5 / R ^ 4 * |inner ℝ z (m 0)| *
          |inner ℝ z (m 1)| ≤
          3 * softScale R z ^ 5 / R ^ 4 * (‖z‖ * ‖m 0‖) *
            (‖z‖ * ‖m 1‖) := by
        gcongr
        · exact abs_real_inner_le_norm z (m 0)
        · exact abs_real_inner_le_norm z (m 1)
      _ = (3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4) *
          ‖m 0‖ * ‖m 1‖ := by ring
  have ht2 :
      ‖(softScale R z) ^ 3 / R ^ 2 * inner ℝ (m 0) (m 1)‖ ≤
        ((softScale R z) ^ 3 / R ^ 2) * ‖m 0‖ * ‖m 1‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc2]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (m 0) (m 1)) hc2
  calc
    |3 * softScale R z ^ 5 / R ^ 4 * inner ℝ z (m 0) *
          inner ℝ z (m 1) -
        softScale R z ^ 3 / R ^ 2 * inner ℝ (m 0) (m 1)| ≤
        ‖3 * softScale R z ^ 5 / R ^ 4 * inner ℝ z (m 0) *
          inner ℝ z (m 1)‖ +
        ‖softScale R z ^ 3 / R ^ 2 * inner ℝ (m 0) (m 1)‖ :=
      abs_sub _ _
    _ ≤ (3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4) *
          ‖m 0‖ * ‖m 1‖ +
        (softScale R z ^ 3 / R ^ 2) * ‖m 0‖ * ‖m 1‖ :=
      add_le_add ht1 ht2
    _ = M * ∏ i, ‖m i‖ := by
      simp only [Fin.prod_univ_two]
      dsimp [M]
      ring

theorem norm_iteratedFDeriv_softScale_two_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ ≤
      4 / R ^ 2 := by
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have ha1 : softScale R z ≤ 1 := softScale_le_one hR.ne' z
  have haz : softScale R z * ‖z‖ ≤ R := softScale_mul_norm_le hR z
  have hazsq : (softScale R z * ‖z‖) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha0 (norm_nonneg z)) hR.le).2 haz
  have hcore : softScale R z ^ 5 * ‖z‖ ^ 2 ≤ R ^ 2 := by
    calc
      softScale R z ^ 5 * ‖z‖ ^ 2 =
          softScale R z ^ 3 * (softScale R z * ‖z‖) ^ 2 := by ring
      _ ≤ 1 * R ^ 2 := by
        exact mul_le_mul (pow_le_one₀ ha0 ha1) hazsq (sq_nonneg _)
          (by norm_num)
      _ = R ^ 2 := one_mul _
  have hfirst :
      3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4 ≤ 3 / R ^ 2 := by
    calc
      3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4 =
          (3 / R ^ 4) * (softScale R z ^ 5 * ‖z‖ ^ 2) := by ring
      _ ≤ (3 / R ^ 4) * R ^ 2 := by
        exact mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 3 / R ^ 2 := by field_simp [hR.ne']
  have hsecond : softScale R z ^ 3 / R ^ 2 ≤ 1 / R ^ 2 := by
    exact div_le_div_of_nonneg_right (pow_le_one₀ ha0 ha1) (sq_nonneg R)
  calc
    ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ ≤
        3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4 +
          softScale R z ^ 3 / R ^ 2 :=
      norm_iteratedFDeriv_softScale_two_le_sharp hR z
    _ ≤ 3 / R ^ 2 + 1 / R ^ 2 := add_le_add hfirst hsecond
    _ = 4 / R ^ 2 := by ring

theorem norm_iteratedFDeriv_softScale_two_mul_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
      4 / R := by
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have ha1 : softScale R z ≤ 1 := softScale_le_one hR.ne' z
  have haz : softScale R z * ‖z‖ ≤ R := softScale_mul_norm_le hR z
  have hpow3 : (softScale R z * ‖z‖) ^ 3 ≤ R ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg ha0 (norm_nonneg z)) haz 3
  have hcore3 : softScale R z ^ 5 * ‖z‖ ^ 3 ≤ R ^ 3 := by
    calc
      softScale R z ^ 5 * ‖z‖ ^ 3 =
          softScale R z ^ 2 * (softScale R z * ‖z‖) ^ 3 := by ring
      _ ≤ 1 * R ^ 3 := by
        exact mul_le_mul (pow_le_one₀ ha0 ha1) hpow3
          (pow_nonneg (mul_nonneg ha0 (norm_nonneg z)) 3) (by norm_num)
      _ = R ^ 3 := one_mul _
  have hcore1 : softScale R z ^ 3 * ‖z‖ ≤ R := by
    calc
      softScale R z ^ 3 * ‖z‖ =
          softScale R z ^ 2 * (softScale R z * ‖z‖) := by ring
      _ ≤ 1 * R := by
        exact mul_le_mul (pow_le_one₀ ha0 ha1) haz
          (mul_nonneg ha0 (norm_nonneg z)) (by norm_num)
      _ = R := one_mul _
  have hsharp := mul_le_mul_of_nonneg_right
    (norm_iteratedFDeriv_softScale_two_le_sharp hR z) (norm_nonneg z)
  calc
    ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
        (3 * softScale R z ^ 5 * ‖z‖ ^ 2 / R ^ 4 +
          softScale R z ^ 3 / R ^ 2) * ‖z‖ := hsharp
    _ = 3 * (softScale R z ^ 5 * ‖z‖ ^ 3) / R ^ 4 +
        (softScale R z ^ 3 * ‖z‖) / R ^ 2 := by ring
    _ ≤ 3 * R ^ 3 / R ^ 4 + R / R ^ 2 := by
      gcongr
    _ = 4 / R := by field_simp [hR.ne']; ring

theorem fderiv_softCoeffFive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    fderiv ℝ (softCoeffFive R : E → ℝ) z =
      (-15 * (softScale R z) ^ 7 / R ^ 6) • innerSL ℝ z := by
  have hAlpha : HasFDerivAt (softScale R : E → ℝ)
      ((-(softScale R z) ^ 3 / R ^ 2) • innerSL ℝ z) z := by
    rw [← fderiv_softScale hR z]
    exact (softScale_contDiff hR).differentiable (by norm_num) z
      |>.hasFDerivAt
  have hpow := hAlpha.pow 5
  have hmul := hpow.const_mul 3
  have hdiv := hmul.mul_const (R ^ 4)⁻¹
  have hfun : (softCoeffFive R : E → ℝ) =
      fun y : E ↦ 3 * (softScale R y ^ 5) * (R ^ 4)⁻¹ := by
    funext y
    simp only [softCoeffFive, div_eq_mul_inv]
  rw [hfun, hdiv.fderiv]
  ext h
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    innerSL_apply_apply, Nat.reduceSub, nsmul_eq_mul, smul_smul]
  field_simp [hR] <;> ring

theorem fderiv_softCoeffThree
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) :
    fderiv ℝ (softCoeffThree R : E → ℝ) z =
      (-3 * (softScale R z) ^ 5 / R ^ 4) • innerSL ℝ z := by
  have hAlpha : HasFDerivAt (softScale R : E → ℝ)
      ((-(softScale R z) ^ 3 / R ^ 2) • innerSL ℝ z) z := by
    rw [← fderiv_softScale hR z]
    exact (softScale_contDiff hR).differentiable (by norm_num) z
      |>.hasFDerivAt
  have hpow := hAlpha.pow 3
  have hdiv := hpow.mul_const (R ^ 2)⁻¹
  have hfun : (softCoeffThree R : E → ℝ) =
      fun y : E ↦ softScale R y ^ 3 * (R ^ 2)⁻¹ := by
    funext y
    simp only [softCoeffThree, div_eq_mul_inv]
  rw [hfun, hdiv.fderiv]
  ext h
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    innerSL_apply_apply, Nat.reduceSub, nsmul_eq_mul, smul_smul]
  field_simp [hR] <;> ring

theorem iteratedFDeriv_softScale_three_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z : E) (m : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z m =
      -15 * (softScale R z) ^ 7 / R ^ 6 *
          inner ℝ z (m 0) * inner ℝ z (m 1) * inner ℝ z (m 2) +
        3 * (softScale R z) ^ 5 / R ^ 4 *
          (inner ℝ (m 0) (m 1) * inner ℝ z (m 2) +
            inner ℝ (m 0) (m 2) * inner ℝ z (m 1) +
            inner ℝ (m 1) (m 2) * inner ℝ z (m 0)) := by
  have hD2Diff : DifferentiableAt ℝ
      (iteratedFDeriv ℝ 2 (softScale R : E → ℝ)) z :=
    (softScale_contDiff hR).contDiffAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2)
  rw [hD2Diff.iteratedFDeriv_succ_apply_left']
  have hfun :
      (fun y : E ↦ iteratedFDeriv ℝ 2
        (softScale R : E → ℝ) y (Fin.tail m)) =
      fun y : E ↦
        softCoeffFive R y * inner ℝ (m 1) y * inner ℝ (m 2) y -
          softCoeffThree R y * inner ℝ (m 1) (m 2) := by
    funext y
    rw [iteratedFDeriv_softScale_two_apply hR y (Fin.tail m)]
    simp only [Fin.tail, Fin.succ_zero_eq_one]
    change
      softCoeffFive R y * inner ℝ y (m 1) * inner ℝ y (m 2) -
          softCoeffThree R y * inner ℝ (m 1) (m 2) = _
    simp only [softCoeffFive, softCoeffThree]
    rw [real_inner_comm y (m 1), real_inner_comm y (m 2)]
  rw [hfun]
  have hC5Smooth : ContDiff ℝ ∞ (softCoeffFive R : E → ℝ) :=
    (contDiff_const.mul ((softScale_contDiff hR).pow 5)).div_const (R ^ 4)
  have hC3Smooth : ContDiff ℝ ∞ (softCoeffThree R : E → ℝ) :=
    ((softScale_contDiff hR).pow 3).div_const (R ^ 2)
  have hC5 : HasFDerivAt (softCoeffFive R : E → ℝ)
      ((-15 * (softScale R z) ^ 7 / R ^ 6) • innerSL ℝ z) z := by
    rw [← fderiv_softCoeffFive hR z]
    exact hC5Smooth.differentiable (by norm_num) z |>.hasFDerivAt
  have hC3 : HasFDerivAt (softCoeffThree R : E → ℝ)
      ((-3 * (softScale R z) ^ 5 / R ^ 4) • innerSL ℝ z) z := by
    rw [← fderiv_softCoeffThree hR z]
    exact hC3Smooth.differentiable (by norm_num) z |>.hasFDerivAt
  have hL1 : HasFDerivAt (fun y : E ↦ inner ℝ (m 1) y)
      (innerSL ℝ (m 1)) z := (innerSL ℝ (m 1)).hasFDerivAt
  have hL2 : HasFDerivAt (fun y : E ↦ inner ℝ (m 2) y)
      (innerSL ℝ (m 2)) z := (innerSL ℝ (m 2)).hasFDerivAt
  have hFirst := (hC5.mul hL1).mul hL2
  have hSecond := hC3.mul_const (inner ℝ (m 1) (m 2))
  have htarget :
      (fun y : E ↦
        softCoeffFive R y * inner ℝ (m 1) y * inner ℝ (m 2) y -
          softCoeffThree R y * inner ℝ (m 1) (m 2)) =
        ((softCoeffFive R * fun y : E ↦ inner ℝ (m 1) y) *
            fun y : E ↦ inner ℝ (m 2) y) -
          fun y : E ↦ softCoeffThree R y * inner ℝ (m 1) (m 2) := by
    funext y
    rfl
  rw [htarget]
  rw [(hFirst.sub hSecond).fderiv]
  simp only [sub_apply, add_apply, FunLike.coe_smul, Pi.smul_apply,
    Pi.mul_apply, smul_eq_mul, innerSL_apply_apply, softCoeffFive,
    div_eq_mul_inv]
  ring_nf
  rw [real_inner_comm (m 1) z, real_inner_comm (m 2) z,
    real_inner_comm (m 1) (m 0), real_inner_comm (m 2) (m 0)]
  ring

theorem norm_iteratedFDeriv_softScale_three_le_sharp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z‖ ≤
      15 * (softScale R z) ^ 7 * ‖z‖ ^ 3 / R ^ 6 +
        9 * (softScale R z) ^ 5 * ‖z‖ / R ^ 4 := by
  let M : ℝ := 15 * (softScale R z) ^ 7 * ‖z‖ ^ 3 / R ^ 6 +
    9 * (softScale R z) ^ 5 * ‖z‖ / R ^ 4
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  apply ContinuousMultilinearMap.opNorm_le_bound hM0
  intro m
  rw [Real.norm_eq_abs, iteratedFDeriv_softScale_three_apply hR.ne' z m]
  let P : ℝ := ‖m 0‖ * ‖m 1‖ * ‖m 2‖
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hc1 : 0 ≤ 15 * softScale R z ^ 7 / R ^ 6 := by positivity
  have hc2 : 0 ≤ 3 * softScale R z ^ 5 / R ^ 4 := by positivity
  have ht1 :
      |-15 * softScale R z ^ 7 / R ^ 6 * inner ℝ z (m 0) *
          inner ℝ z (m 1) * inner ℝ z (m 2)| ≤
        (15 * softScale R z ^ 7 * ‖z‖ ^ 3 / R ^ 6) * P := by
    rw [show -15 * softScale R z ^ 7 / R ^ 6 =
      -(15 * softScale R z ^ 7 / R ^ 6) by ring]
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hc1]
    calc
      15 * softScale R z ^ 7 / R ^ 6 * |inner ℝ z (m 0)| *
          |inner ℝ z (m 1)| * |inner ℝ z (m 2)| ≤
        15 * softScale R z ^ 7 / R ^ 6 * (‖z‖ * ‖m 0‖) *
          (‖z‖ * ‖m 1‖) * (‖z‖ * ‖m 2‖) := by
        gcongr
        · exact abs_real_inner_le_norm z (m 0)
        · exact abs_real_inner_le_norm z (m 1)
        · exact abs_real_inner_le_norm z (m 2)
      _ = (15 * softScale R z ^ 7 * ‖z‖ ^ 3 / R ^ 6) * P := by
        dsimp [P]
        ring
  have hs1 : |inner ℝ (m 0) (m 1) * inner ℝ z (m 2)| ≤
      ‖z‖ * P := by
    rw [abs_mul]
    calc
      |inner ℝ (m 0) (m 1)| * |inner ℝ z (m 2)| ≤
          (‖m 0‖ * ‖m 1‖) * (‖z‖ * ‖m 2‖) := by
        gcongr
        · exact abs_real_inner_le_norm (m 0) (m 1)
        · exact abs_real_inner_le_norm z (m 2)
      _ = ‖z‖ * P := by dsimp [P]; ring
  have hs2 : |inner ℝ (m 0) (m 2) * inner ℝ z (m 1)| ≤
      ‖z‖ * P := by
    rw [abs_mul]
    calc
      |inner ℝ (m 0) (m 2)| * |inner ℝ z (m 1)| ≤
          (‖m 0‖ * ‖m 2‖) * (‖z‖ * ‖m 1‖) := by
        gcongr
        · exact abs_real_inner_le_norm (m 0) (m 2)
        · exact abs_real_inner_le_norm z (m 1)
      _ = ‖z‖ * P := by dsimp [P]; ring
  have hs3 : |inner ℝ (m 1) (m 2) * inner ℝ z (m 0)| ≤
      ‖z‖ * P := by
    rw [abs_mul]
    calc
      |inner ℝ (m 1) (m 2)| * |inner ℝ z (m 0)| ≤
          (‖m 1‖ * ‖m 2‖) * (‖z‖ * ‖m 0‖) := by
        gcongr
        · exact abs_real_inner_le_norm (m 1) (m 2)
        · exact abs_real_inner_le_norm z (m 0)
      _ = ‖z‖ * P := by dsimp [P]; ring
  have hsum :
      |inner ℝ (m 0) (m 1) * inner ℝ z (m 2) +
          inner ℝ (m 0) (m 2) * inner ℝ z (m 1) +
          inner ℝ (m 1) (m 2) * inner ℝ z (m 0)| ≤
        3 * ‖z‖ * P := by
    calc
      |_ + _ + _| ≤
          |inner ℝ (m 0) (m 1) * inner ℝ z (m 2)| +
            |inner ℝ (m 0) (m 2) * inner ℝ z (m 1)| +
            |inner ℝ (m 1) (m 2) * inner ℝ z (m 0)| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ ‖z‖ * P + ‖z‖ * P + ‖z‖ * P := by linarith
      _ = 3 * ‖z‖ * P := by ring
  have ht2 :
      |3 * softScale R z ^ 5 / R ^ 4 *
        (inner ℝ (m 0) (m 1) * inner ℝ z (m 2) +
          inner ℝ (m 0) (m 2) * inner ℝ z (m 1) +
          inner ℝ (m 1) (m 2) * inner ℝ z (m 0))| ≤
        (9 * softScale R z ^ 5 * ‖z‖ / R ^ 4) * P := by
    rw [abs_mul, abs_of_nonneg hc2]
    calc
      3 * softScale R z ^ 5 / R ^ 4 *
          |_ + _ + _| ≤
        3 * softScale R z ^ 5 / R ^ 4 * (3 * ‖z‖ * P) :=
      mul_le_mul_of_nonneg_left hsum hc2
      _ = (9 * softScale R z ^ 5 * ‖z‖ / R ^ 4) * P := by ring
  calc
    |_ + _| ≤
        |-15 * softScale R z ^ 7 / R ^ 6 * inner ℝ z (m 0) *
          inner ℝ z (m 1) * inner ℝ z (m 2)| +
        |3 * softScale R z ^ 5 / R ^ 4 *
          (inner ℝ (m 0) (m 1) * inner ℝ z (m 2) +
            inner ℝ (m 0) (m 2) * inner ℝ z (m 1) +
            inner ℝ (m 1) (m 2) * inner ℝ z (m 0))| := abs_add_le _ _
    _ ≤ (15 * softScale R z ^ 7 * ‖z‖ ^ 3 / R ^ 6) * P +
        (9 * softScale R z ^ 5 * ‖z‖ / R ^ 4) * P :=
      add_le_add ht1 ht2
    _ = M * ∏ i, ‖m i‖ := by
      simp only [Fin.prod_univ_succ]
      dsimp [M, P]
      ring

theorem norm_iteratedFDeriv_softScale_three_mul_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
      24 / R ^ 2 := by
  have ha0 : 0 ≤ softScale R z := (softScale_pos hR.ne' z).le
  have ha1 : softScale R z ≤ 1 := softScale_le_one hR.ne' z
  have haz : softScale R z * ‖z‖ ≤ R := softScale_mul_norm_le hR z
  have hpow4 : (softScale R z * ‖z‖) ^ 4 ≤ R ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg ha0 (norm_nonneg z)) haz 4
  have hpow2 : (softScale R z * ‖z‖) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha0 (norm_nonneg z)) haz 2
  have hcore4 : softScale R z ^ 7 * ‖z‖ ^ 4 ≤ R ^ 4 := by
    calc
      softScale R z ^ 7 * ‖z‖ ^ 4 =
          softScale R z ^ 3 * (softScale R z * ‖z‖) ^ 4 := by ring
      _ ≤ 1 * R ^ 4 := by
        exact mul_le_mul (pow_le_one₀ ha0 ha1) hpow4
          (pow_nonneg (mul_nonneg ha0 (norm_nonneg z)) 4) (by norm_num)
      _ = R ^ 4 := one_mul _
  have hcore2 : softScale R z ^ 5 * ‖z‖ ^ 2 ≤ R ^ 2 := by
    calc
      softScale R z ^ 5 * ‖z‖ ^ 2 =
          softScale R z ^ 3 * (softScale R z * ‖z‖) ^ 2 := by ring
      _ ≤ 1 * R ^ 2 := by
        exact mul_le_mul (pow_le_one₀ ha0 ha1) hpow2
          (pow_nonneg (mul_nonneg ha0 (norm_nonneg z)) 2) (by norm_num)
      _ = R ^ 2 := one_mul _
  have hsharp := mul_le_mul_of_nonneg_right
    (norm_iteratedFDeriv_softScale_three_le_sharp hR z) (norm_nonneg z)
  calc
    ‖iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
        (15 * softScale R z ^ 7 * ‖z‖ ^ 3 / R ^ 6 +
          9 * softScale R z ^ 5 * ‖z‖ / R ^ 4) * ‖z‖ := hsharp
    _ = 15 * (softScale R z ^ 7 * ‖z‖ ^ 4) / R ^ 6 +
        9 * (softScale R z ^ 5 * ‖z‖ ^ 2) / R ^ 4 := by ring
    _ ≤ 15 * R ^ 4 / R ^ 6 + 9 * R ^ 2 / R ^ 4 := by gcongr
    _ = 24 / R ^ 2 := by field_simp [hR.ne']; ring

theorem iteratedFDeriv_id_two_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E) :
    iteratedFDeriv ℝ 2 (id : E → E) z = 0 := by
  have hF : (fun y : E ↦ fderiv ℝ (id : E → E) y) =
      fun _ : E ↦ ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  ext m
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ
    (fun y : E ↦ fderiv ℝ (id : E → E) y) z) (m 0)) (m 1) = 0
  rw [hF]
  simp

theorem iteratedFDeriv_id_three_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E) :
    iteratedFDeriv ℝ 3 (id : E → E) z = 0 := by
  have hF : (fun y : E ↦ fderiv ℝ (id : E → E) y) =
      fun _ : E ↦ ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  ext m
  simp only [iteratedFDeriv_succ_apply_right]
  change (((fderiv ℝ (fun y : E ↦ fderiv ℝ
    (fun y : E ↦ fderiv ℝ (id : E → E) y) y) z)
      (Fin.init (Fin.init m) 0)) (Fin.init m 1)) (m 2) = 0
  rw [hF]
  simp

theorem norm_iteratedFDeriv_id_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : E) :
    ‖iteratedFDeriv ℝ 1 (id : E → E) z‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_one, fderiv_id]
  exact ContinuousLinearMap.norm_id_le

theorem fderiv_softProjection_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : R ≠ 0) (z h : E) :
    fderiv ℝ (softProjection R : E → E) z h =
      softScale R z • h -
        ((softScale R z) ^ 3 / R ^ 2 * inner ℝ z h) • z := by
  have hAlphaDiff : DifferentiableAt ℝ (softScale R : E → ℝ) z :=
    (softScale_contDiff hR).differentiable (by norm_num) z
  have hIdDiff : DifferentiableAt ℝ (id : E → E) z := differentiableAt_id
  have hfun : (softProjection R : E → E) =
      fun y : E ↦ softScale R y • id y := rfl
  rw [hfun, fderiv_fun_smul hAlphaDiff hIdDiff]
  rw [fderiv_softScale hR z, fderiv_id]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  rw [sub_eq_add_neg]
  congr 1
  rw [show -softScale R z ^ 3 / R ^ 2 * inner ℝ z h =
    -(softScale R z ^ 3 / R ^ 2 * inner ℝ z h) by ring]
  simp

theorem norm_fderiv_softProjection_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖fderiv ℝ (softProjection R : E → E) z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (softProjection R : E → E) z) (by norm_num)
  intro h
  rw [one_mul, fderiv_softProjection_apply hR.ne' z h]
  let a : ℝ := softScale R z
  let c : ℝ := a ^ 3 / R ^ 2 * inner ℝ z h
  have ha0 : 0 ≤ a := by dsimp [a]; exact (softScale_pos hR.ne' z).le
  have ha1 : a ≤ 1 := by dsimp [a]; exact softScale_le_one hR.ne' z
  have haz : a * ‖z‖ ≤ R := by
    dsimp [a]
    exact softScale_mul_norm_le hR z
  have hazsq : a ^ 2 * ‖z‖ ^ 2 ≤ R ^ 2 := by
    have hsquare : (a * ‖z‖) ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (mul_nonneg ha0 (norm_nonneg z)) hR.le).2 haz
    nlinarith
  have hcoef : 0 ≤
      2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4 := by
    rw [show 2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4 =
      (a ^ 4 / R ^ 4) * (2 * R ^ 2 - a ^ 2 * ‖z‖ ^ 2) by
        field_simp [hR.ne']]
    exact mul_nonneg (by positivity) (by nlinarith [sq_nonneg R])
  have hsquared :
      ‖a • h - c • z‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm z h]
    rw [show (|c| * ‖z‖) ^ 2 = c ^ 2 * ‖z‖ ^ 2 by
      rw [mul_pow, sq_abs]]
    dsimp [c]
    have hinnerSq : 0 ≤ (inner ℝ z h) ^ 2 :=
      sq_nonneg (inner ℝ z h)
    have hdrop := mul_nonneg hcoef hinnerSq
    have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
    have hscale : a ^ 2 * ‖h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha2)
        (sq_nonneg ‖h‖)]
    calc
      _ = a ^ 2 * ‖h‖ ^ 2 -
          (2 * a ^ 4 / R ^ 2 - a ^ 6 * ‖z‖ ^ 2 / R ^ 4) *
            (inner ℝ z h) ^ 2 := by
        field_simp [hR.ne']
        ring
      _ ≤ a ^ 2 * ‖h‖ ^ 2 := sub_le_self _ hdrop
      _ ≤ ‖h‖ ^ 2 := hscale
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg h)).1 <| by
    simpa [a, c] using hsquared

theorem norm_iteratedFDeriv_softProjection_two_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 2 (softProjection R : E → E) z‖ ≤ 6 / R := by
  have hprod := norm_iteratedFDeriv_smul_le
    (softScale_contDiff hR.ne') (contDiff_id : ContDiff ℝ ∞ (id : E → E))
    z (n := 2) (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hfun : (softProjection R : E → E) =
      fun y : E ↦ softScale R y • id y := rfl
  rw [hfun]
  refine hprod.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [iteratedFDeriv_id_two_eq_zero z, norm_zero]
  rw [norm_iteratedFDeriv_zero]
  norm_num [Nat.reduceSub, norm_iteratedFDeriv_zero]
  rw [show (2 : ℕ) - 1 = 1 by norm_num,
    show (2 : ℕ) - 2 = 0 by norm_num, norm_iteratedFDeriv_zero]
  have hD1 := norm_fderiv_softScale_le hR z
  have hD2 := norm_iteratedFDeriv_softScale_two_mul_norm_le hR z
  have hId1 := norm_iteratedFDeriv_id_one_le z
  change
    2 * ‖fderiv ℝ (softScale R : E → ℝ) z‖ *
          ‖iteratedFDeriv ℝ 1 (id : E → E) z‖ +
        ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ * ‖z‖ ≤ 6 / R
  calc
    2 * ‖fderiv ℝ (softScale R : E → ℝ) z‖ *
          ‖iteratedFDeriv ℝ 1 (id : E → E) z‖ +
        ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
      2 * R⁻¹ * 1 + 4 / R := by gcongr
    _ = 6 / R := by rw [inv_eq_one_div]; ring

theorem norm_iteratedFDeriv_softProjection_three_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) :
    ‖iteratedFDeriv ℝ 3 (softProjection R : E → E) z‖ ≤
      36 / R ^ 2 := by
  have hprod := norm_iteratedFDeriv_smul_le
    (softScale_contDiff hR.ne') (contDiff_id : ContDiff ℝ ∞ (id : E → E))
    z (n := 3) (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hfun : (softProjection R : E → E) =
      fun y : E ↦ softScale R y • id y := rfl
  rw [hfun]
  refine hprod.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [iteratedFDeriv_id_three_eq_zero z, norm_zero,
    iteratedFDeriv_id_two_eq_zero z, norm_zero]
  rw [norm_iteratedFDeriv_zero]
  norm_num [Nat.reduceSub, norm_iteratedFDeriv_zero]
  rw [show (3 : ℕ) - 2 = 1 by norm_num,
    show (3 : ℕ) - 3 = 0 by norm_num, norm_iteratedFDeriv_zero]
  have hD2 := norm_iteratedFDeriv_softScale_two_le hR z
  have hD3 := norm_iteratedFDeriv_softScale_three_mul_norm_le hR z
  have hId1 := norm_iteratedFDeriv_id_one_le z
  change
    3 * ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ *
          ‖iteratedFDeriv ℝ 1 (id : E → E) z‖ +
        ‖iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
      36 / R ^ 2
  calc
    3 * ‖iteratedFDeriv ℝ 2 (softScale R : E → ℝ) z‖ *
          ‖iteratedFDeriv ℝ 1 (id : E → E) z‖ +
        ‖iteratedFDeriv ℝ 3 (softScale R : E → ℝ) z‖ * ‖z‖ ≤
      3 * (4 / R ^ 2) * 1 + 24 / R ^ 2 := by gcongr
    _ = 36 / R ^ 2 := by ring

def normalizedHiddenProbe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η R : ℝ) (L : E →L[ℝ] ChainVector T) :
    E → ChainVector T :=
  (normalizeCLM η) ∘ L ∘ softProjection R

def hiddenProbe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (R : ℝ) (L : E →L[ℝ] ChainVector T) :
    E → ChainVector T :=
  L ∘ softProjection R

theorem hiddenProbe_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {R : ℝ} (hR : R ≠ 0)
    (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (hiddenProbe R L) := by
  exact L.contDiff.comp (softProjection_contDiff hR)

theorem normalize_comp_hiddenProbe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η R : ℝ) (L : E →L[ℝ] ChainVector T) :
    (normalizeCLM η) ∘ hiddenProbe R L = normalizedHiddenProbe η R L := rfl

theorem normalizedHiddenProbe_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η R : ℝ} (hR : R ≠ 0)
    (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞ (normalizedHiddenProbe η R L) := by
  unfold normalizedHiddenProbe
  exact (normalizeCLM η).contDiff.comp
    (L.contDiff.comp (softProjection_contDiff hR))

theorem normalizedHiddenProbe_eq_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η R : ℝ) (L : E →L[ℝ] ChainVector T) :
    normalizedHiddenProbe η R L =
      ((normalizeCLM η).comp L) ∘ softProjection R := rfl

theorem norm_normalizedHiddenProbe_linear_part_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η)
    {L : E →L[ℝ] ChainVector T} (hL : ‖L‖ ≤ 1) :
    ‖(normalizeCLM η).comp L‖ ≤ η⁻¹ := by
  calc
    ‖(normalizeCLM η).comp L‖ ≤ ‖normalizeCLM η‖ * ‖L‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ η⁻¹ * 1 := by
      exact mul_le_mul (norm_normalizeCLM_le_inv hη) hL (norm_nonneg L)
        (inv_nonneg.mpr hη.le)
    _ = η⁻¹ := mul_one _

theorem norm_iteratedFDeriv_normalizedHiddenProbe_one_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η R : ℝ} (hη : 0 < η) (hR : 0 < R)
    {L : E →L[ℝ] ChainVector T} (hL : ‖L‖ ≤ 1) (z : E) :
    ‖iteratedFDeriv ℝ 1 (normalizedHiddenProbe η R L) z‖ ≤ η⁻¹ := by
  rw [normalizedHiddenProbe_eq_comp]
  have hleft := ((normalizeCLM η).comp L).norm_iteratedFDeriv_comp_left
    (x := z)
    (softProjection_contDiff hR.ne' |>.contDiffAt)
    (show (1 : ℕ∞) ≤ ∞ from mod_cast le_top)
  have hsoft : ‖iteratedFDeriv ℝ 1 (softProjection R : E → E) z‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_one]
    exact norm_fderiv_softProjection_le_one hR z
  calc
    ‖iteratedFDeriv ℝ 1 (((normalizeCLM η).comp L) ∘ softProjection R) z‖ ≤
        ‖(normalizeCLM η).comp L‖ *
          ‖iteratedFDeriv ℝ 1 (softProjection R : E → E) z‖ := hleft
    _ ≤ η⁻¹ * 1 := by
      exact mul_le_mul (norm_normalizedHiddenProbe_linear_part_le hη hL)
        hsoft (norm_nonneg _) (inv_nonneg.mpr hη.le)
    _ = η⁻¹ := mul_one _

theorem norm_iteratedFDeriv_normalizedHiddenProbe_two_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η R : ℝ} (hη : 0 < η) (hR : 0 < R)
    {L : E →L[ℝ] ChainVector T} (hL : ‖L‖ ≤ 1) (z : E) :
    ‖iteratedFDeriv ℝ 2 (normalizedHiddenProbe η R L) z‖ ≤
      η⁻¹ * (6 / R) := by
  rw [normalizedHiddenProbe_eq_comp]
  have hleft := ((normalizeCLM η).comp L).norm_iteratedFDeriv_comp_left
    (x := z)
    (softProjection_contDiff hR.ne' |>.contDiffAt)
    (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)
  calc
    ‖iteratedFDeriv ℝ 2 (((normalizeCLM η).comp L) ∘ softProjection R) z‖ ≤
        ‖(normalizeCLM η).comp L‖ *
          ‖iteratedFDeriv ℝ 2 (softProjection R : E → E) z‖ := hleft
    _ ≤ η⁻¹ * (6 / R) := by
      exact mul_le_mul (norm_normalizedHiddenProbe_linear_part_le hη hL)
        (norm_iteratedFDeriv_softProjection_two_le hR z) (by positivity)
        (inv_nonneg.mpr hη.le)

theorem norm_iteratedFDeriv_normalizedHiddenProbe_three_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η R : ℝ} (hη : 0 < η) (hR : 0 < R)
    {L : E →L[ℝ] ChainVector T} (hL : ‖L‖ ≤ 1) (z : E) :
    ‖iteratedFDeriv ℝ 3 (normalizedHiddenProbe η R L) z‖ ≤
      η⁻¹ * (36 / R ^ 2) := by
  rw [normalizedHiddenProbe_eq_comp]
  have hleft := ((normalizeCLM η).comp L).norm_iteratedFDeriv_comp_left
    (x := z)
    (softProjection_contDiff hR.ne' |>.contDiffAt)
    (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)
  calc
    ‖iteratedFDeriv ℝ 3 (((normalizeCLM η).comp L) ∘ softProjection R) z‖ ≤
        ‖(normalizeCLM η).comp L‖ *
          ‖iteratedFDeriv ℝ 3 (softProjection R : E → E) z‖ := hleft
    _ ≤ η⁻¹ * (36 / R ^ 2) := by
      exact mul_le_mul (norm_normalizedHiddenProbe_linear_part_le hη hL)
        (norm_iteratedFDeriv_softProjection_three_le hR z) (by positivity)
        (inv_nonneg.mpr hη.le)

def hardRadius (η : ℝ) (T : ℕ) : ℝ :=
  230 * η * Real.sqrt T

theorem hardRadius_pos {η : ℝ} {T : ℕ} (hη : 0 < η) (hT : 0 < T) :
    0 < hardRadius η T := by
  unfold hardRadius
  positivity

theorem one_le_sqrt_nat {T : ℕ} (hT : 0 < T) :
    1 ≤ Real.sqrt T := by
  rw [Real.one_le_sqrt]
  exact_mod_cast hT

theorem norm_iteratedFDeriv_normalizedHiddenProbe_le_inv_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T r : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    {L : E →L[ℝ] ChainVector T} (hL : ‖L‖ ≤ 1)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (z : E) :
    ‖iteratedFDeriv ℝ r (normalizedHiddenProbe η (hardRadius η T) L) z‖ ≤
      (η⁻¹) ^ r := by
  have hR : 0 < hardRadius η T := hardRadius_pos hη hT
  have hsqrt : 1 ≤ Real.sqrt T := one_le_sqrt_nat hT
  interval_cases r
  · simpa using norm_iteratedFDeriv_normalizedHiddenProbe_one_le
      hη hR hL z
  · have htwo := norm_iteratedFDeriv_normalizedHiddenProbe_two_le
      hη hR hL z
    refine htwo.trans ?_
    unfold hardRadius
    have hcoef : 6 / (230 * Real.sqrt T) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith
    calc
      η⁻¹ * (6 / (230 * η * Real.sqrt T)) =
          (6 / (230 * Real.sqrt T)) * (η⁻¹) ^ 2 := by
        field_simp [hη.ne']
      _ ≤ 1 * (η⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg η⁻¹)
      _ = (η⁻¹) ^ 2 := one_mul _
  · have hthree := norm_iteratedFDeriv_normalizedHiddenProbe_three_le
      hη hR hL z
    refine hthree.trans ?_
    unfold hardRadius
    have hTreal : 1 ≤ (T : ℝ) := by exact_mod_cast hT
    have hsqrtSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
    have hcoef : 36 / (230 ^ 2 * T) ≤ (1 : ℝ) := by
      apply (div_le_one (by positivity)).2
      norm_num
      nlinarith
    calc
      η⁻¹ * (36 / (230 * η * Real.sqrt T) ^ 2) =
          (36 / (230 ^ 2 * T)) * (η⁻¹) ^ 3 := by
        rw [mul_pow, hsqrtSq]
        field_simp [hη.ne']
      _ ≤ 1 * (η⁻¹) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (inv_nonneg.mpr hη.le) 3)
      _ = (η⁻¹) ^ 3 := one_mul _

theorem exists_frontier_hidden_composition_scales :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {η : ℝ}, 0 < η → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 → ∀ z : E,
        |((frontierExtractor η : ChainVector T → ℝ) ∘
            hiddenProbe (hardRadius η T) L) z| ≤ Cθ * η ^ 2 ∧
        ‖iteratedFDeriv ℝ 1
            ((frontierExtractor η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤ Cθ * η ∧
        ‖iteratedFDeriv ℝ 2
            ((frontierExtractor η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤ Cθ ∧
        ‖iteratedFDeriv ℝ 3
            ((frontierExtractor η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤ Cθ / η := by
  obtain ⟨Cext, hCext0, hCext⟩ :=
    exists_common_bound_frontierExtractor_three
  let Cθ : ℝ := 6 * Cext
  refine ⟨Cθ, by dsimp [Cθ]; positivity, ?_⟩
  intro E _ _ T η hη hT L hL z
  have hR : 0 < hardRadius η T := hardRadius_pos hη hT
  have hq : ContDiff ℝ ∞ (hiddenProbe (hardRadius η T) L) :=
    hiddenProbe_contDiff hR.ne' L
  have hExt : ∀ r : ℕ, r ≤ 3 → ∀ y : ChainVector T,
      ‖iteratedFDeriv ℝ r
          (frontierExtractor 1 : ChainVector T → ℝ) y‖ ≤ Cext := by
    intro r hr y
    have he := hCext (T := T) (η := (1 : ℝ)) (by norm_num) r hr y
    norm_num at he ⊢
    exact he
  have hInner : ∀ n : ℕ, n ≤ 3 → ∀ r : ℕ, 1 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r
          ((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z‖ ≤
        (η⁻¹) ^ r := by
    intro n hn r hr1 hrn
    rw [normalize_comp_hiddenProbe]
    exact norm_iteratedFDeriv_normalizedHiddenProbe_le_inv_pow
      hη hT hL hr1 (hrn.trans hn) z
  have hComp : ∀ n : ℕ, n ≤ 3 →
      ‖iteratedFDeriv ℝ n
          ((frontierExtractor η : ChainVector T → ℝ) ∘
            hiddenProbe (hardRadius η T) L) z‖ ≤
        η ^ 2 * (Nat.factorial n * Cext * (η⁻¹) ^ n) := by
    intro n hn
    exact norm_iteratedFDeriv_frontierExtractor_comp_le hq hExt hn z
      (hInner n hn)
  have hval0 := hCext (T := T) (η := η) hη 0 (by norm_num)
    (hiddenProbe (hardRadius η T) L z)
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hval0
  have hval :
      |frontierExtractor η (hiddenProbe (hardRadius η T) L z)| ≤
        Cθ * η ^ 2 := by
    dsimp [Cθ]
    norm_num at hval0
    nlinarith [mul_nonneg hCext0 (sq_nonneg η)]
  have h1 := hComp 1 (by norm_num)
  have h2 := hComp 2 (by norm_num)
  have h3 := hComp 3 (by norm_num)
  refine ⟨hval, ?_, ?_, ?_⟩
  · dsimp [Cθ]
    norm_num at h1 ⊢
    field_simp [hη.ne'] at h1 ⊢
    nlinarith [mul_nonneg hCext0 hη.le]
  · dsimp [Cθ]
    norm_num at h2 ⊢
    field_simp [hη.ne'] at h2 ⊢
    nlinarith
  · dsimp [Cθ]
    norm_num at h3 ⊢
    field_simp [hη.ne'] at h3 ⊢
    nlinarith

theorem exists_visible_hidden_composition_scales :
    ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {η : ℝ}, 0 < η → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 → ∀ z : E,
        ‖iteratedFDeriv ℝ 1
            ((visibleChain η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤
          Ca * η * Real.sqrt T ∧
        ‖iteratedFDeriv ℝ 2
            ((visibleChain η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤ Ca ∧
        ‖iteratedFDeriv ℝ 3
            ((visibleChain η : ChainVector T → ℝ) ∘
              hiddenProbe (hardRadius η T) L) z‖ ≤ Ca / η := by
  obtain ⟨CA, hCA0, hFirstBase, hHigherBase⟩ :=
    exists_visibleChain_base_bounds
  let Ca : ℝ := 10 * CA
  refine ⟨Ca, by dsimp [Ca]; positivity, ?_⟩
  intro E _ _ T η hη hT L hL z
  have hR : 0 < hardRadius η T := hardRadius_pos hη hT
  have hsqrt : 1 ≤ Real.sqrt T := one_le_sqrt_nat hT
  have hsqrtPos : 0 < Real.sqrt T := lt_of_lt_of_le (by norm_num) hsqrt
  have hq : ContDiff ℝ ∞ (hiddenProbe (hardRadius η T) L) :=
    hiddenProbe_contDiff hR.ne' L
  have hFirst : ‖fderiv ℝ
      (visibleChain 1 : ChainVector T → ℝ)
      (((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z)‖ ≤
      CA * Real.sqrt T := by
    rw [← norm_iteratedFDeriv_one]
    exact hFirstBase hT _
  have hHigher : ∀ r : ℕ, 2 ≤ r → r ≤ 3 →
      ‖iteratedFDeriv ℝ r
          (visibleChain 1 : ChainVector T → ℝ)
          (((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z)‖ ≤ CA := by
    intro r hr2 hr3
    exact hHigherBase r hr2 hr3 _
  have hInner : ∀ n : ℕ, n ≤ 3 → ∀ r : ℕ, 1 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r
          ((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z‖ ≤
        (η⁻¹) ^ r := by
    intro n hn r hr1 hrn
    rw [normalize_comp_hiddenProbe]
    exact norm_iteratedFDeriv_normalizedHiddenProbe_le_inv_pow
      hη hT hL hr1 (hrn.trans hn) z
  have hTop2 :
      ‖iteratedFDeriv ℝ 2
          ((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z‖ ≤
        η⁻¹ * (6 / hardRadius η T) := by
    rw [normalize_comp_hiddenProbe]
    exact norm_iteratedFDeriv_normalizedHiddenProbe_two_le hη hR hL z
  have hTop3 :
      ‖iteratedFDeriv ℝ 3
          ((normalizeCLM η) ∘ hiddenProbe (hardRadius η T) L) z‖ ≤
        η⁻¹ * (36 / (hardRadius η T) ^ 2) := by
    rw [normalize_comp_hiddenProbe]
    exact norm_iteratedFDeriv_normalizedHiddenProbe_three_le hη hR hL z
  have hInner1 := hInner 1 (by norm_num) 1 (by norm_num) (by norm_num)
  rw [norm_iteratedFDeriv_one] at hInner1
  have h1 := norm_iteratedFDeriv_visibleChain_comp_one_le hq z hFirst hInner1
  have h2 := norm_iteratedFDeriv_visibleChain_comp_le hq
    (by norm_num : 2 ≤ 2) (by norm_num : 2 ≤ 3) z hCA0
    (fun r hr2 hrn ↦ hHigher r hr2 (hrn.trans (by norm_num)))
    hFirst (hInner 2 (by norm_num)) hTop2
  have h3 := norm_iteratedFDeriv_visibleChain_comp_le hq
    (by norm_num : 2 ≤ 3) (by norm_num : 3 ≤ 3) z hCA0
    (fun r hr2 hrn ↦ hHigher r hr2 (hrn.trans (by norm_num)))
    hFirst (hInner 3 (by norm_num)) hTop3
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Ca]
    have hscale :
        η ^ 2 * (CA * Real.sqrt T * η⁻¹) = CA * η * Real.sqrt T := by
      field_simp [hη.ne']
    simp only [pow_one] at h1
    rw [hscale] at h1
    exact h1.trans <| by
      nlinarith [mul_nonneg hCA0 (mul_nonneg hη.le (Real.sqrt_nonneg T))]
  · dsimp [Ca]
    unfold hardRadius at h2
    norm_num at h2
    rw [← inv_pow] at h2
    have hsmall :
        η ^ 2 *
          (2 * CA * (η⁻¹) ^ 2 +
            CA * Real.sqrt T * (η⁻¹ * (6 / (230 * η * Real.sqrt T)))) ≤
          10 * CA := by
      field_simp [hη.ne', hsqrtPos.ne']
      nlinarith
    exact h2.trans hsmall
  · dsimp [Ca]
    unfold hardRadius at h3
    norm_num at h3
    rw [← inv_pow] at h3
    have hsqrtSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
    rw [mul_pow, hsqrtSq] at h3
    have hsmall :
        η ^ 2 *
          (6 * CA * (η⁻¹) ^ 3 +
            CA * Real.sqrt T *
              (η⁻¹ * (36 / ((230 * η) ^ 2 * T)))) ≤
          10 * CA / η := by
      have hTreal : 1 ≤ (T : ℝ) := by exact_mod_cast hT
      field_simp [hη.ne', hsqrtPos.ne']
      nlinarith [mul_nonneg hCA0 (sub_nonneg.mpr hsqrt)]
    exact h3.trans hsmall

end
end BilevelLowerBound
