/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightHardInstance
import BilevelLowerBoundLean.PopulationRegularity

/-!
# Uniform regularity of the two-coordinate amplifier

This file verifies the analytic scaling that is new in the `kappa^8`
construction.  Dividing the hidden frontier by the off-diagonal inverse
matrix entry attenuates every derivative by `O(1 / kappa)`.  Although the
constant compensation is multiplied by a coefficient of order `kappa`, the
complete compensated block consequently has the global scales

* `‖D R‖ = O(eta^2 / kappa)`;
* `‖D^2 R‖ = O(eta / kappa)`;
* `‖D^3 R‖ = O(1 / kappa)`.

All estimates are on `E × (R × R)`, so they include every mixed derivative.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Attenuation of the hidden frontier -/

/-- The attenuated frontier, viewed as a function on the hidden lower
variable. -/
def kappaEightAttenuatedFrontier
    {E : Type*} (kappa : ℝ) (theta : E → ℝ) : E → ℝ :=
  fun z ↦ attenuatedFrontier kappa (theta z)

theorem kappaEightAttenuatedFrontier_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : ℝ} {theta : E → ℝ} (htheta : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (kappaEightAttenuatedFrontier kappa theta) := by
  unfold kappaEightAttenuatedFrontier attenuatedFrontier
  fun_prop

/-- Every iterated derivative of the attenuated frontier gains the same
factor `4 / kappa`. -/
theorem norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa B : ℝ} (hkappa : 2 ≤ kappa) (_hB : 0 ≤ B)
    {theta : E → ℝ} (htheta : ContDiff ℝ ∞ theta)
    (n : ℕ) (z : E)
    (hderiv : ‖iteratedFDeriv ℝ n theta z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (kappaEightAttenuatedFrontier kappa theta) z‖ ≤
      4 * B / kappa := by
  have hsInv : |(amplifierOffDiag kappa)⁻¹| ≤ 4 / kappa := by
    have h := abs_attenuatedFrontier_le
      (kappa := kappa) (theta := (1 : ℝ)) (B := (1 : ℝ))
      hkappa (by norm_num) (by norm_num)
    simpa [attenuatedFrontier, div_eq_mul_inv] using h
  have hFun : kappaEightAttenuatedFrontier kappa theta =
      (amplifierOffDiag kappa)⁻¹ • theta := by
    funext y
    simp [kappaEightAttenuatedFrontier, attenuatedFrontier,
      div_eq_mul_inv, mul_comm]
  rw [hFun]
  rw [iteratedFDeriv_const_smul_apply
    ((htheta.of_le (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  calc
    |(amplifierOffDiag kappa)⁻¹| * ‖iteratedFDeriv ℝ n theta z‖ ≤
        (4 / kappa) * B := by gcongr
    _ = 4 * B / kappa := by ring

/-- The four quantitative attenuation estimates used below. -/
theorem kappaEightAttenuatedFrontier_scales
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa Ctheta : ℝ} (heta : 0 < eta) (hkappa : 2 ≤ kappa)
    (hCtheta : 0 ≤ Ctheta) {theta : E → ℝ}
    (hthetaSmooth : ContDiff ℝ ∞ theta)
    (htheta0 : ∀ z : E, |theta z| ≤ Ctheta * eta ^ 2)
    (htheta1 : ∀ z : E,
      ‖iteratedFDeriv ℝ 1 theta z‖ ≤ Ctheta * eta)
    (htheta2 : ∀ z : E,
      ‖iteratedFDeriv ℝ 2 theta z‖ ≤ Ctheta)
    (htheta3 : ∀ z : E,
      ‖iteratedFDeriv ℝ 3 theta z‖ ≤ Ctheta / eta)
    (z : E) :
    ‖iteratedFDeriv ℝ 0 (kappaEightAttenuatedFrontier kappa theta) z‖ ≤
        4 * Ctheta * eta ^ 2 / kappa ∧
      ‖iteratedFDeriv ℝ 1 (kappaEightAttenuatedFrontier kappa theta) z‖ ≤
        4 * Ctheta * eta / kappa ∧
      ‖iteratedFDeriv ℝ 2 (kappaEightAttenuatedFrontier kappa theta) z‖ ≤
        4 * Ctheta / kappa ∧
    ‖iteratedFDeriv ℝ 3 (kappaEightAttenuatedFrontier kappa theta) z‖ ≤
        4 * Ctheta / (kappa * eta) := by
  have h0 : ‖iteratedFDeriv ℝ 0 theta z‖ ≤ Ctheta * eta ^ 2 := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using htheta0 z
  constructor
  · simpa [mul_assoc] using
      norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le hkappa
        (mul_nonneg hCtheta (sq_nonneg eta)) hthetaSmooth 0 z h0
  constructor
  · simpa [mul_assoc] using
      norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le hkappa
        (mul_nonneg hCtheta heta.le) hthetaSmooth 1 z (htheta1 z)
  constructor
  · simpa using
      norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le hkappa hCtheta
        hthetaSmooth 2 z (htheta2 z)
  · have hB : 0 ≤ Ctheta / eta := div_nonneg hCtheta heta.le
    have h := norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le hkappa hB
      hthetaSmooth 3 z (htheta3 z)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-! ## Product estimate at first order -/

theorem norm_iteratedFDeriv_mul_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {F0 F1 G0 G1 : ℝ} (x : E)
    (hf0 : ‖iteratedFDeriv ℝ 0 f x‖ ≤ F0)
    (hf1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ F1)
    (hg0 : ‖iteratedFDeriv ℝ 0 g x‖ ≤ G0)
    (hg1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ G1) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f y * g y) x‖ ≤
      F0 * G1 + F1 * G0 := by
  calc
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (1 + 1),
          ((1 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (1 - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (show (1 : ℕ∞) ≤ ∞ from mod_cast le_top)
    _ ≤ F0 * G1 + F1 * G0 := by
      have hf0' : |f x| ≤ F0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hf0
      have hf1' : ‖fderiv ℝ f x‖ ≤ F1 := by
        simpa [norm_iteratedFDeriv_one] using hf1
      have hg0' : |g x| ≤ G0 := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg0
      have hg1' : ‖fderiv ℝ g x‖ ≤ G1 := by
        simpa [norm_iteratedFDeriv_one] using hg1
      have hF0 : 0 ≤ F0 := (abs_nonneg (f x)).trans hf0'
      have hF1 : 0 ≤ F1 := (norm_nonneg _).trans hf1'
      have hG0 : 0 ≤ G0 := (abs_nonneg (g x)).trans hg0'
      have hG1 : 0 ≤ G1 := (norm_nonneg _).trans hg1'
      norm_num [Finset.sum_range_succ]
      gcongr

/-! ## Full compensated-block estimates -/

theorem kappaEightCompensatedPair_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} (heta : eta ≠ 0) {theta : E → ℝ}
    (htheta : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta) := by
  let Lz : (E × AmplifierAux) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Laux : (E × AmplifierAux) →L[ℝ] AmplifierAux :=
    ContinuousLinearMap.snd ℝ E AmplifierAux
  let Lfirst : AmplifierAux →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ
  let Lv : (E × AmplifierAux) →L[ℝ] ℝ := Lfirst.comp Laux
  let Alpha : E × AmplifierAux → ℝ :=
    (kappaEightAttenuatedFrontier kappa theta) ∘ Lz
  let Psi : E × AmplifierAux → ℝ := (compactIdentity eta) ∘ Lv
  have hAlpha : ContDiff ℝ ∞ Alpha :=
    (kappaEightAttenuatedFrontier_contDiff htheta).comp Lz.contDiff
  have hPsi : ContDiff ℝ ∞ Psi :=
    (compactIdentity_contDiff heta).comp Lv.contDiff
  have hFun : kappaEightCompensatedPair eta kappa theta =
      (fun p ↦ (amplifierDiag kappa / 2) * (Alpha p * Alpha p)) -
        (fun p ↦ Alpha p * Psi p) := by
    funext p
    simp [kappaEightCompensatedPair, amplifiedCompensation, Alpha, Psi,
      kappaEightAttenuatedFrontier, Lz, Lv, Lfirst, Laux, pow_two]
  rw [hFun]
  exact (contDiff_const.mul (hAlpha.mul hAlpha)).sub (hAlpha.mul hPsi)

set_option maxHeartbeats 800000 in
-- The nested product-rule normalizations for three global derivative orders are expensive.
/-- Quantitative regularity of the new compensated block.  The constants are
universal once the frontier and cutoff constants are fixed. -/
theorem kappaEightCompensatedPair_first_second_third_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa Ctheta Cpsi : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hkappa : 2 ≤ kappa)
    (hCtheta : 0 ≤ Ctheta) (hCpsi : 0 ≤ Cpsi)
    {theta : E → ℝ} (hthetaSmooth : ContDiff ℝ ∞ theta)
    (htheta0 : ∀ z : E, |theta z| ≤ Ctheta * eta ^ 2)
    (htheta1 : ∀ z : E,
      ‖iteratedFDeriv ℝ 1 theta z‖ ≤ Ctheta * eta)
    (htheta2 : ∀ z : E,
      ‖iteratedFDeriv ℝ 2 theta z‖ ≤ Ctheta)
    (htheta3 : ∀ z : E,
      ‖iteratedFDeriv ℝ 3 theta z‖ ≤ Ctheta / eta)
    (hpsi : ∀ n : ℕ, n ≤ 3 → ∀ v : ℝ,
      ‖iteratedFDeriv ℝ n (compactIdentity 1) v‖ ≤ Cpsi)
    (p : E × AmplifierAux) :
    ‖iteratedFDeriv ℝ 1 (kappaEightCompensatedPair eta kappa theta) p‖ ≤
        16 * Ctheta * (Ctheta + Cpsi) * eta ^ 2 / kappa ∧
      ‖iteratedFDeriv ℝ 2 (kappaEightCompensatedPair eta kappa theta) p‖ ≤
        32 * Ctheta * (Ctheta + Cpsi) * eta / kappa ∧
      ‖iteratedFDeriv ℝ 3 (kappaEightCompensatedPair eta kappa theta) p‖ ≤
        64 * Ctheta * (Ctheta + Cpsi) / kappa := by
  let Lz : (E × AmplifierAux) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Laux : (E × AmplifierAux) →L[ℝ] AmplifierAux :=
    ContinuousLinearMap.snd ℝ E AmplifierAux
  let Lfirst : AmplifierAux →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ
  let Lv : (E × AmplifierAux) →L[ℝ] ℝ := Lfirst.comp Laux
  let Alpha : E × AmplifierAux → ℝ :=
    (kappaEightAttenuatedFrontier kappa theta) ∘ Lz
  let Psi : E × AmplifierAux → ℝ := (compactIdentity eta) ∘ Lv
  let TT : E × AmplifierAux → ℝ := fun y ↦ Alpha y * Alpha y
  let TP : E × AmplifierAux → ℝ := fun y ↦ Alpha y * Psi y
  let TH : E × AmplifierAux → ℝ :=
    fun y ↦ (amplifierDiag kappa / 2) * TT y
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hLz : ‖Lz‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ E AmplifierAux
  have hLaux : ‖Laux‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ E AmplifierAux
  have hLfirst : ‖Lfirst‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hLv : ‖Lv‖ ≤ 1 := by
    calc
      ‖Lv‖ ≤ ‖Lfirst‖ * ‖Laux‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hLfirst hLaux (norm_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  have hAlphaSmooth : ContDiff ℝ ∞ Alpha :=
    (kappaEightAttenuatedFrontier_contDiff hthetaSmooth).comp Lz.contDiff
  have hPsiSmooth : ContDiff ℝ ∞ Psi :=
    (compactIdentity_contDiff heta.ne').comp Lv.contDiff
  have hscales := kappaEightAttenuatedFrontier_scales heta hkappa hCtheta
    hthetaSmooth htheta0 htheta1 htheta2 htheta3 p.1
  have hAlpha0 : ‖iteratedFDeriv ℝ 0 Alpha p‖ ≤
      4 * Ctheta * eta ^ 2 / kappa :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightAttenuatedFrontier_contDiff hthetaSmooth) Lz hLz 0 p).trans
      hscales.1
  have hAlpha1 : ‖iteratedFDeriv ℝ 1 Alpha p‖ ≤
      4 * Ctheta * eta / kappa :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightAttenuatedFrontier_contDiff hthetaSmooth) Lz hLz 1 p).trans
      hscales.2.1
  have hAlpha2 : ‖iteratedFDeriv ℝ 2 Alpha p‖ ≤
      4 * Ctheta / kappa :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightAttenuatedFrontier_contDiff hthetaSmooth) Lz hLz 2 p).trans
      hscales.2.2.1
  have hAlpha3 : ‖iteratedFDeriv ℝ 3 Alpha p‖ ≤
      4 * Ctheta / (kappa * eta) :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (kappaEightAttenuatedFrontier_contDiff hthetaSmooth) Lz hLz 3 p).trans
      hscales.2.2.2
  have hPsi0 : ‖iteratedFDeriv ℝ 0 Psi p‖ ≤ Cpsi * eta := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact norm_compactIdentity_value_le heta hCpsi hpsi p.2.1
  have hPsi1 : ‖iteratedFDeriv ℝ 1 Psi p‖ ≤ Cpsi :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff heta.ne') Lv hLv 1 p).trans
      (norm_iteratedFDeriv_compactIdentity_one_le heta hCpsi hpsi p.2.1)
  have hPsi2 : ‖iteratedFDeriv ℝ 2 Psi p‖ ≤ Cpsi / eta :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff heta.ne') Lv hLv 2 p).trans
      (norm_iteratedFDeriv_compactIdentity_two_le heta hCpsi hpsi p.2.1)
  have hPsi3 : ‖iteratedFDeriv ℝ 3 Psi p‖ ≤ Cpsi / eta ^ 2 :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (compactIdentity_contDiff heta.ne') Lv hLv 3 p).trans
      (norm_iteratedFDeriv_compactIdentity_three_le heta hCpsi hpsi p.2.1)
  have hTT1 : ‖iteratedFDeriv ℝ 1 TT p‖ ≤
      32 * Ctheta ^ 2 * eta ^ 3 / kappa ^ 2 := by
    have h := norm_iteratedFDeriv_mul_one_le hAlphaSmooth hAlphaSmooth p
      hAlpha0 hAlpha1 hAlpha0 hAlpha1
    refine h.trans ?_
    field_simp [hkpos.ne']
    ring_nf
    exact le_rfl
  have hTP1 : ‖iteratedFDeriv ℝ 1 TP p‖ ≤
      8 * Ctheta * Cpsi * eta ^ 2 / kappa := by
    have h := norm_iteratedFDeriv_mul_one_le hAlphaSmooth hPsiSmooth p
      hAlpha0 hAlpha1 hPsi0 hPsi1
    refine h.trans ?_
    field_simp [hkpos.ne']
    ring_nf
    exact le_rfl
  have hTT2 : ‖iteratedFDeriv ℝ 2 TT p‖ ≤
      64 * Ctheta ^ 2 * eta ^ 2 / kappa ^ 2 := by
    have h := norm_iteratedFDeriv_mul_two_le hAlphaSmooth hAlphaSmooth p
      hAlpha0 hAlpha1 hAlpha2 hAlpha0 hAlpha1 hAlpha2
    refine h.trans ?_
    field_simp [hkpos.ne']
    ring_nf
    exact le_rfl
  have hTP2 : ‖iteratedFDeriv ℝ 2 TP p‖ ≤
      16 * Ctheta * Cpsi * eta / kappa := by
    have h := norm_iteratedFDeriv_mul_two_le hAlphaSmooth hPsiSmooth p
      hAlpha0 hAlpha1 hAlpha2 hPsi0 hPsi1 hPsi2
    refine h.trans ?_
    field_simp [hkpos.ne', heta.ne']
    ring_nf
    exact le_rfl
  have hTT3 : ‖iteratedFDeriv ℝ 3 TT p‖ ≤
      128 * Ctheta ^ 2 * eta / kappa ^ 2 := by
    have h := norm_iteratedFDeriv_mul_three_le hAlphaSmooth hAlphaSmooth p
      hAlpha0 hAlpha1 hAlpha2 hAlpha3 hAlpha0 hAlpha1 hAlpha2 hAlpha3
    refine h.trans ?_
    field_simp [hkpos.ne', heta.ne']
    ring_nf
    exact le_rfl
  have hTP3 : ‖iteratedFDeriv ℝ 3 TP p‖ ≤
      32 * Ctheta * Cpsi / kappa := by
    have h := norm_iteratedFDeriv_mul_three_le hAlphaSmooth hPsiSmooth p
      hAlpha0 hAlpha1 hAlpha2 hAlpha3 hPsi0 hPsi1 hPsi2 hPsi3
    refine h.trans ?_
    field_simp [hkpos.ne', heta.ne']
    ring_nf
    exact le_rfl
  have hTTSmooth : ContDiff ℝ ∞ TT := hAlphaSmooth.mul hAlphaSmooth
  have hTPSmooth : ContDiff ℝ ∞ TP := hAlphaSmooth.mul hPsiSmooth
  have hTHSmooth : ContDiff ℝ ∞ TH := contDiff_const.mul hTTSmooth
  have hTHFun : TH = (amplifierDiag kappa / 2) • TT := by
    funext y
    rfl
  have hFun : kappaEightCompensatedPair eta kappa theta = TH - TP := by
    funext y
    simp [kappaEightCompensatedPair, amplifiedCompensation, TH, TT, TP,
      Alpha, Psi, kappaEightAttenuatedFrontier, Lz, Lv, Lfirst, Laux,
      pow_two]
  have hdiag0 : 0 ≤ amplifierDiag kappa / 2 := by
    exact div_nonneg (amplifierDiag_pos hkpos).le (by norm_num)
  have hdiagLe : amplifierDiag kappa / 2 ≤ kappa / 2 := by
    linarith [amplifierDiag_le_kappa (by linarith : 1 ≤ kappa)]
  have hHalf1 : ‖iteratedFDeriv ℝ 1 TH p‖ ≤
      16 * Ctheta ^ 2 * eta ^ 3 / kappa := by
    rw [hTHFun]
    rw [iteratedFDeriv_const_smul_apply
      ((hTTSmooth.of_le (show (1 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiag0]
    calc
      amplifierDiag kappa / 2 * ‖iteratedFDeriv ℝ 1 TT p‖ ≤
          amplifierDiag kappa / 2 *
            (32 * Ctheta ^ 2 * eta ^ 3 / kappa ^ 2) :=
        mul_le_mul_of_nonneg_left hTT1 hdiag0
      _ ≤ kappa / 2 * (32 * Ctheta ^ 2 * eta ^ 3 / kappa ^ 2) := by
        gcongr
      _ = 16 * Ctheta ^ 2 * eta ^ 3 / kappa := by
        field_simp [hkpos.ne']
        ring
  have hHalf2 : ‖iteratedFDeriv ℝ 2 TH p‖ ≤
      32 * Ctheta ^ 2 * eta ^ 2 / kappa := by
    rw [hTHFun]
    rw [iteratedFDeriv_const_smul_apply
      ((hTTSmooth.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiag0]
    calc
      amplifierDiag kappa / 2 * ‖iteratedFDeriv ℝ 2 TT p‖ ≤
          amplifierDiag kappa / 2 *
            (64 * Ctheta ^ 2 * eta ^ 2 / kappa ^ 2) :=
        mul_le_mul_of_nonneg_left hTT2 hdiag0
      _ ≤ kappa / 2 * (64 * Ctheta ^ 2 * eta ^ 2 / kappa ^ 2) := by
        gcongr
      _ = 32 * Ctheta ^ 2 * eta ^ 2 / kappa := by
        field_simp [hkpos.ne']
        ring
  have hHalf3 : ‖iteratedFDeriv ℝ 3 TH p‖ ≤
      64 * Ctheta ^ 2 * eta / kappa := by
    rw [hTHFun]
    rw [iteratedFDeriv_const_smul_apply
      ((hTTSmooth.of_le (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiag0]
    calc
      amplifierDiag kappa / 2 * ‖iteratedFDeriv ℝ 3 TT p‖ ≤
          amplifierDiag kappa / 2 *
            (128 * Ctheta ^ 2 * eta / kappa ^ 2) :=
        mul_le_mul_of_nonneg_left hTT3 hdiag0
      _ ≤ kappa / 2 * (128 * Ctheta ^ 2 * eta / kappa ^ 2) := by
        gcongr
      _ = 64 * Ctheta ^ 2 * eta / kappa := by
        field_simp [hkpos.ne']
        ring
  rw [hFun]
  constructor
  · rw [iteratedFDeriv_sub_apply
      ((hTHSmooth.of_le
        (show (1 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
      ((hTPSmooth.of_le
        (show (1 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
    calc
      ‖iteratedFDeriv ℝ 1 TH p - iteratedFDeriv ℝ 1 TP p‖ ≤
          ‖iteratedFDeriv ℝ 1 TH p‖ + ‖iteratedFDeriv ℝ 1 TP p‖ :=
        norm_sub_le _ _
      _ ≤ 16 * Ctheta ^ 2 * eta ^ 3 / kappa +
          8 * Ctheta * Cpsi * eta ^ 2 / kappa := add_le_add hHalf1 hTP1
      _ ≤ 16 * Ctheta * (Ctheta + Cpsi) * eta ^ 2 / kappa := by
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right hkpos).2
        have hetaPow : eta ^ 3 ≤ eta ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg eta) (sub_nonneg.mpr heta1)]
        have hMain : 16 * Ctheta ^ 2 * eta ^ 3 ≤
            16 * Ctheta ^ 2 * eta ^ 2 :=
          mul_le_mul_of_nonneg_left hetaPow (by positivity)
        have hCross : 8 * Ctheta * Cpsi * eta ^ 2 ≤
            16 * Ctheta * Cpsi * eta ^ 2 := by
          have hnonneg : 0 ≤ Ctheta * Cpsi * eta ^ 2 := by positivity
          nlinarith
        calc
          16 * Ctheta ^ 2 * eta ^ 3 +
              8 * Ctheta * Cpsi * eta ^ 2 ≤
              16 * Ctheta ^ 2 * eta ^ 2 +
                16 * Ctheta * Cpsi * eta ^ 2 := add_le_add hMain hCross
          _ = 16 * Ctheta * (Ctheta + Cpsi) * eta ^ 2 := by ring
  constructor
  · rw [iteratedFDeriv_sub_apply
      ((hTHSmooth.of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
      ((hTPSmooth.of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
    calc
      ‖iteratedFDeriv ℝ 2 TH p - iteratedFDeriv ℝ 2 TP p‖ ≤
          ‖iteratedFDeriv ℝ 2 TH p‖ + ‖iteratedFDeriv ℝ 2 TP p‖ :=
        norm_sub_le _ _
      _ ≤ 32 * Ctheta ^ 2 * eta ^ 2 / kappa +
          16 * Ctheta * Cpsi * eta / kappa := add_le_add hHalf2 hTP2
      _ ≤ 32 * Ctheta * (Ctheta + Cpsi) * eta / kappa := by
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right hkpos).2
        have hetaSq : eta ^ 2 ≤ eta := by
          calc
            eta ^ 2 = eta * eta := pow_two eta
            _ ≤ eta * 1 := mul_le_mul_of_nonneg_left heta1 heta.le
            _ = eta := mul_one eta
        have hMain : 32 * Ctheta ^ 2 * eta ^ 2 ≤
            32 * Ctheta ^ 2 * eta :=
          mul_le_mul_of_nonneg_left hetaSq (by positivity)
        have hCross : 16 * Ctheta * Cpsi * eta ≤
            32 * Ctheta * Cpsi * eta := by
          have hnonneg : 0 ≤ Ctheta * Cpsi * eta := by positivity
          calc
            16 * Ctheta * Cpsi * eta = 16 * (Ctheta * Cpsi * eta) := by ring
            _ ≤ 32 * (Ctheta * Cpsi * eta) :=
              mul_le_mul_of_nonneg_right (by norm_num) hnonneg
            _ = 32 * Ctheta * Cpsi * eta := by ring
        calc
          32 * Ctheta ^ 2 * eta ^ 2 +
              16 * Ctheta * Cpsi * eta ≤
              32 * Ctheta ^ 2 * eta +
                32 * Ctheta * Cpsi * eta := add_le_add hMain hCross
          _ = 32 * Ctheta * (Ctheta + Cpsi) * eta := by ring
  · rw [iteratedFDeriv_sub_apply
      ((hTHSmooth.of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
      ((hTPSmooth.of_le
        (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
    calc
      ‖iteratedFDeriv ℝ 3 TH p - iteratedFDeriv ℝ 3 TP p‖ ≤
          ‖iteratedFDeriv ℝ 3 TH p‖ + ‖iteratedFDeriv ℝ 3 TP p‖ :=
        norm_sub_le _ _
      _ ≤ 64 * Ctheta ^ 2 * eta / kappa +
          32 * Ctheta * Cpsi / kappa := add_le_add hHalf3 hTP3
      _ ≤ 64 * Ctheta * (Ctheta + Cpsi) / kappa := by
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right hkpos).2
        have hMain : 64 * Ctheta ^ 2 * eta ≤ 64 * Ctheta ^ 2 := by
          calc
            64 * Ctheta ^ 2 * eta ≤ 64 * Ctheta ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left heta1 (by positivity)
            _ = 64 * Ctheta ^ 2 := mul_one _
        have hCross : 32 * Ctheta * Cpsi ≤ 64 * Ctheta * Cpsi := by
          have hnonneg : 0 ≤ Ctheta * Cpsi := mul_nonneg hCtheta hCpsi
          nlinarith
        calc
          64 * Ctheta ^ 2 * eta + 32 * Ctheta * Cpsi ≤
              64 * Ctheta ^ 2 + 64 * Ctheta * Cpsi := add_le_add hMain hCross
          _ = 64 * Ctheta * (Ctheta + Cpsi) := by ring

/-! ## Uniform constants for the hidden hard instance -/

/-- Universal regularity constants after substituting the actual hidden
frontier map.  `Cnoise` is chosen strictly positive because it is also used
as the scale in the Bernoulli reveal probability. -/
theorem exists_kappaEight_hard_compensated_pair_regularities :
    ∃ Cnoise CHess Cthird : ℝ,
      0 < Cnoise ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta kappa : ℝ},
        0 < eta → eta ≤ 1 → 2 ≤ kappa → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ p : E × AmplifierAux,
        ‖iteratedFDeriv ℝ 1
            (kappaEightCompensatedPair eta kappa
              (hardFrontierMap eta L)) p‖ ≤
              Cnoise * eta ^ 2 / kappa ∧
        ‖iteratedFDeriv ℝ 2
            (kappaEightCompensatedPair eta kappa
              (hardFrontierMap eta L)) p‖ ≤
              CHess * eta / kappa ∧
        ‖iteratedFDeriv ℝ 3
            (kappaEightCompensatedPair eta kappa
              (hardFrontierMap eta L)) p‖ ≤
              Cthird / kappa := by
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨Cpsi, hCpsi, hpsi⟩ :=
    exists_common_bound_compactIdentity_one_three
  let Cnoise : ℝ := 16 * Ctheta * (Ctheta + Cpsi) + 1
  let CHess : ℝ := 32 * Ctheta * (Ctheta + Cpsi)
  let Cthird : ℝ := 64 * Ctheta * (Ctheta + Cpsi)
  have hbase : 0 ≤ Ctheta * (Ctheta + Cpsi) := by positivity
  refine ⟨Cnoise, CHess, Cthird, by dsimp [Cnoise]; nlinarith,
    by dsimp [CHess]; positivity, by dsimp [Cthird]; positivity, ?_⟩
  intro E _ _ T eta kappa heta heta1 hkappa hT L hL p
  have hthetaAll := htheta heta hT hL
  have hthetaSmooth : ContDiff ℝ ∞ (hardFrontierMap eta L) :=
    hardFrontierMap_contDiff heta hT L
  have hbounds := kappaEightCompensatedPair_first_second_third_bounds
    heta heta1 hkappa hCtheta hCpsi hthetaSmooth
    (fun z ↦ by simpa only [hardFrontierMap] using (hthetaAll z).1)
    (fun z ↦ by simpa only [hardFrontierMap] using (hthetaAll z).2.1)
    (fun z ↦ by simpa only [hardFrontierMap] using (hthetaAll z).2.2.1)
    (fun z ↦ by simpa only [hardFrontierMap] using (hthetaAll z).2.2.2)
    hpsi p
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hcoef : 16 * Ctheta * (Ctheta + Cpsi) ≤ Cnoise := by
    dsimp [Cnoise]
    linarith
  constructor
  · exact hbounds.1.trans <|
      (div_le_div_iff_of_pos_right hkpos).2
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg eta))
  constructor
  · simpa only [CHess] using hbounds.2.1
  · simpa only [Cthird] using hbounds.2.2

end

end BilevelLowerBound
