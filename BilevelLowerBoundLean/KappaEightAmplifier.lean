/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.HardInstanceAnalytic

/-!
# The two-dimensional condition-number amplifier

This file contains the exact scalar algebra behind the `kappa^8` hard
instance.  The auxiliary lower variable is a pair.  Its quadratic form has
eigenvalues `1 / kappa` and `1`, while the off-diagonal entry of its inverse
transmits an attenuated frontier signal to the second coordinate.

The proofs are deliberately value based.  In particular, the compensated
block is shown to be globally nonnegative, and its unique zero is identified,
without appealing to a merely local stationarity calculation.
-/

open scoped ContDiff

namespace BilevelLowerBound

noncomputable section

/-- The two auxiliary lower coordinates used by the amplified construction. -/
abbrev AmplifierAux := ℝ × ℝ

/-- Diagonal entry of the inverse amplifier matrix. -/
def amplifierDiag (kappa : ℝ) : ℝ :=
  (kappa + 1) / 2

/-- Off-diagonal entry of the inverse amplifier matrix. -/
def amplifierOffDiag (kappa : ℝ) : ℝ :=
  (kappa - 1) / 2

/-- One half of `vᵀ M_kappa v`, written without finite matrices. -/
def amplifierQuadratic (kappa : ℝ) (v : AmplifierAux) : ℝ :=
  (amplifierDiag kappa / (2 * kappa)) * (v.1 ^ 2 + v.2 ^ 2) -
    (amplifierOffDiag kappa / kappa) * (v.1 * v.2)

/-- The symmetric bilinear form whose diagonal is twice
`amplifierQuadratic`. -/
def amplifierHessianForm (kappa : ℝ)
    (u v : AmplifierAux) : ℝ :=
  (amplifierDiag kappa / kappa) * (u.1 * v.1 + u.2 * v.2) -
    (amplifierOffDiag kappa / kappa) * (u.1 * v.2 + u.2 * v.1)

/-- The attenuated frontier forcing. -/
def attenuatedFrontier (kappa theta : ℝ) : ℝ :=
  theta / amplifierOffDiag kappa

/-- The randomized compensated part of the two-dimensional lower block. -/
def amplifiedCompensation (eta kappa theta : ℝ)
    (v : AmplifierAux) : ℝ :=
  let alpha := attenuatedFrontier kappa theta
  (amplifierDiag kappa / 2) * alpha ^ 2 -
    alpha * compactIdentity eta v.1

/-- The complete auxiliary population block. -/
def amplifiedScalarBlock (eta kappa theta : ℝ)
    (v : AmplifierAux) : ℝ :=
  amplifierQuadratic kappa v + amplifiedCompensation eta kappa theta v

theorem amplifierDiag_sub_offDiag (kappa : ℝ) :
    amplifierDiag kappa - amplifierOffDiag kappa = 1 := by
  unfold amplifierDiag amplifierOffDiag
  ring

theorem amplifierDiag_add_offDiag (kappa : ℝ) :
    amplifierDiag kappa + amplifierOffDiag kappa = kappa := by
  unfold amplifierDiag amplifierOffDiag
  ring

theorem amplifierDiag_sq_sub_offDiag_sq (kappa : ℝ) :
    amplifierDiag kappa ^ 2 - amplifierOffDiag kappa ^ 2 = kappa := by
  rw [sq_sub_sq, amplifierDiag_sub_offDiag, amplifierDiag_add_offDiag]
  ring

theorem amplifierOffDiag_pos {kappa : ℝ} (hkappa : 1 < kappa) :
    0 < amplifierOffDiag kappa := by
  unfold amplifierOffDiag
  linarith

theorem amplifierDiag_pos {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < amplifierDiag kappa := by
  unfold amplifierDiag
  linarith

theorem amplifierOffDiag_ge_quarter {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    kappa / 4 ≤ amplifierOffDiag kappa := by
  unfold amplifierOffDiag
  linarith

theorem amplifierDiag_le_three_quarters {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    amplifierDiag kappa ≤ 3 * kappa / 4 := by
  unfold amplifierDiag
  linarith

theorem amplifierDiag_le_kappa {kappa : ℝ} (hkappa : 1 ≤ kappa) :
    amplifierDiag kappa ≤ kappa := by
  unfold amplifierDiag
  linarith

theorem amplifierOffDiag_lt_diag (kappa : ℝ) :
    amplifierOffDiag kappa < amplifierDiag kappa := by
  unfold amplifierDiag amplifierOffDiag
  linarith

theorem amplifierDiag_div_offDiag_gt_one
    {kappa : ℝ} (hkappa : 1 < kappa) :
    1 < amplifierDiag kappa / amplifierOffDiag kappa := by
  rw [lt_div_iff₀ (amplifierOffDiag_pos hkappa)]
  simpa using amplifierOffDiag_lt_diag kappa

theorem amplifierDiag_div_offDiag_le_three
    {kappa : ℝ} (hkappa : 2 ≤ kappa) :
    amplifierDiag kappa / amplifierOffDiag kappa ≤ 3 := by
  rw [div_le_iff₀ (amplifierOffDiag_pos (by linarith))]
  unfold amplifierDiag amplifierOffDiag
  linarith

theorem abs_attenuatedFrontier_le
    {kappa theta B : ℝ} (hkappa : 2 ≤ kappa)
    (hB : 0 ≤ B) (htheta : |theta| ≤ B) :
    |attenuatedFrontier kappa theta| ≤ 4 * B / kappa := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hspos : 0 < amplifierOffDiag kappa :=
    amplifierOffDiag_pos (by linarith)
  have hsbound := amplifierOffDiag_ge_quarter hkappa
  unfold attenuatedFrontier
  rw [abs_div, abs_of_pos hspos]
  apply (div_le_iff₀ hspos).2
  rw [show 4 * B / kappa * amplifierOffDiag kappa =
      (4 * B * amplifierOffDiag kappa) / kappa by ring]
  apply (le_div_iff₀ hkpos).2
  calc
    |theta| * kappa ≤ B * kappa :=
      mul_le_mul_of_nonneg_right htheta hkpos.le
    _ ≤ 4 * B * amplifierOffDiag kappa := by
      have := mul_le_mul_of_nonneg_left hsbound hB
      nlinarith

/-- Completing the square in the first auxiliary coordinate. -/
theorem amplifierQuadratic_complete_square
    {kappa : ℝ} (hkappa : 0 < kappa)
    (v : AmplifierAux) :
    amplifierQuadratic kappa v =
      v.1 ^ 2 / (2 * amplifierDiag kappa) +
        (amplifierDiag kappa / (2 * kappa)) *
          (v.2 - (amplifierOffDiag kappa / amplifierDiag kappa) * v.1) ^ 2 := by
  have hd : amplifierDiag kappa ≠ 0 := by
    exact (amplifierDiag_pos hkappa).ne'
  unfold amplifierQuadratic
  field_simp [hkappa.ne', hd]
  have hdet := amplifierDiag_sq_sub_offDiag_sq kappa
  nlinarith

/-- Eigen-coordinate formula for the amplifier Hessian. -/
theorem amplifierHessianForm_diagonalize
    {kappa : ℝ} (hkappa : kappa ≠ 0) (v : AmplifierAux) :
    amplifierHessianForm kappa v v =
      ((v.1 - v.2) ^ 2 + (v.1 + v.2) ^ 2 / kappa) / 2 := by
  unfold amplifierHessianForm amplifierDiag amplifierOffDiag
  field_simp [hkappa]
  ring

theorem amplifierQuadratic_eq_half_hessian
    (kappa : ℝ) (v : AmplifierAux) :
    amplifierQuadratic kappa v =
      (1 / 2 : ℝ) * amplifierHessianForm kappa v v := by
  unfold amplifierQuadratic amplifierHessianForm
  ring

/-- The amplifier matrix has lower spectral bound `1 / kappa`. -/
theorem amplifierHessianForm_coercive
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (v : AmplifierAux) :
    (1 / kappa) * (v.1 ^ 2 + v.2 ^ 2) ≤
      amplifierHessianForm kappa v v := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  rw [amplifierHessianForm_diagonalize hkpos.ne']
  have hparallelogram :
      (v.1 - v.2) ^ 2 + (v.1 + v.2) ^ 2 =
        2 * (v.1 ^ 2 + v.2 ^ 2) := by ring
  have hnonneg : 0 ≤ (1 - 1 / kappa) * (v.1 - v.2) ^ 2 := by
    have hinv : 1 / kappa ≤ 1 := (div_le_one hkpos).2 hkappa
    exact mul_nonneg (sub_nonneg.mpr hinv) (sq_nonneg _)
  simp only [div_eq_mul_inv] at hnonneg ⊢
  nlinarith

/-- The amplifier matrix has upper spectral bound one. -/
theorem amplifierHessianForm_le
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (v : AmplifierAux) :
    amplifierHessianForm kappa v v ≤ v.1 ^ 2 + v.2 ^ 2 := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  rw [amplifierHessianForm_diagonalize hkpos.ne']
  have hinv : 1 / kappa ≤ 1 := (div_le_one hkpos).2 hkappa
  have hparallelogram :
      (v.1 - v.2) ^ 2 + (v.1 + v.2) ^ 2 =
        2 * (v.1 ^ 2 + v.2 ^ 2) := by ring
  have hnonneg : 0 ≤ (1 - 1 / kappa) * (v.1 + v.2) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hinv) (sq_nonneg _)
  simp only [div_eq_mul_inv] at hnonneg ⊢
  nlinarith

/-- Applying the amplifier matrix to the proposed inverse image gives the
attenuated forcing in the first coordinate and zero in the second. -/
theorem amplifierHessianForm_proposed
    {kappa alpha : ℝ} (hkappa : kappa ≠ 0) (w : AmplifierAux) :
    amplifierHessianForm kappa
        (amplifierDiag kappa * alpha, amplifierOffDiag kappa * alpha) w =
      alpha * w.1 := by
  have hdet := amplifierDiag_sq_sub_offDiag_sq kappa
  unfold amplifierHessianForm
  change amplifierDiag kappa / kappa *
        (amplifierDiag kappa * alpha * w.1 + amplifierOffDiag kappa * alpha * w.2) -
      amplifierOffDiag kappa / kappa *
        (amplifierDiag kappa * alpha * w.2 + amplifierOffDiag kappa * alpha * w.1) =
    alpha * w.1
  calc
    amplifierDiag kappa / kappa *
          (amplifierDiag kappa * alpha * w.1 + amplifierOffDiag kappa * alpha * w.2) -
        amplifierOffDiag kappa / kappa *
          (amplifierDiag kappa * alpha * w.2 + amplifierOffDiag kappa * alpha * w.1) =
        (alpha / kappa) *
          ((amplifierDiag kappa ^ 2 - amplifierOffDiag kappa ^ 2) * w.1) := by
            ring
    _ = alpha * w.1 := by rw [hdet]; field_simp

theorem amplified_proposed_second_coordinate
    {kappa theta : ℝ} (hkappa : 1 < kappa) :
    (amplifierOffDiag kappa * attenuatedFrontier kappa theta) = theta := by
  unfold attenuatedFrontier
  field_simp [(amplifierOffDiag_pos hkappa).ne']

theorem amplified_proposed_first_coordinate
    {kappa theta : ℝ} (hkappa : 1 < kappa) :
    amplifierDiag kappa * attenuatedFrontier kappa theta =
      (amplifierDiag kappa / amplifierOffDiag kappa) * theta := by
  unfold attenuatedFrontier
  field_simp [(amplifierOffDiag_pos hkappa).ne']

/-- At the inverse-amplified point, the complete auxiliary block is zero
whenever the first coordinate lies in the cutoff's identity region. -/
theorem amplifiedScalarBlock_at_proposed
    {eta kappa theta : ℝ} (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall :
      |amplifierDiag kappa * attenuatedFrontier kappa theta| ≤ eta) :
    amplifiedScalarBlock eta kappa theta
        (amplifierDiag kappa * attenuatedFrontier kappa theta,
          amplifierOffDiag kappa * attenuatedFrontier kappa theta) = 0 := by
  let alpha := attenuatedFrontier kappa theta
  have hkpos : 0 < kappa := by linarith
  have hdpos : 0 < amplifierDiag kappa := amplifierDiag_pos hkpos
  have hpsi : compactIdentity eta (amplifierDiag kappa * alpha) =
      amplifierDiag kappa * alpha :=
    compactIdentity_eq_self heta hsmall
  rw [amplifiedScalarBlock,
    amplifierQuadratic_complete_square hkpos]
  unfold amplifiedCompensation
  rw [hpsi]
  dsimp only [alpha]
  field_simp [hkpos.ne', hdpos.ne']
  ring

/-- The complete auxiliary block is globally nonnegative. -/
theorem amplifiedScalarBlock_nonneg
    {eta kappa theta : ℝ} (hkappa : 1 < kappa)
    (v : AmplifierAux) :
    0 ≤ amplifiedScalarBlock eta kappa theta v := by
  let d := amplifierDiag kappa
  let s := amplifierOffDiag kappa
  let alpha := attenuatedFrontier kappa theta
  have hkpos : 0 < kappa := by linarith
  have hdpos : 0 < d := amplifierDiag_pos hkpos
  have hq := amplifierQuadratic_complete_square hkpos v
  have hpsi := abs_compactIdentity_le eta v.1
  have htail : 0 ≤ (d / (2 * kappa)) *
      (v.2 - (s / d) * v.1) ^ 2 := by
    positivity
  rw [amplifiedScalarBlock, hq]
  unfold amplifiedCompensation
  dsimp only
  by_cases hsign : 0 ≤ alpha * v.1
  · have hbound : alpha * compactIdentity eta v.1 ≤ alpha * v.1 := by
      have hsame : 0 ≤ alpha * compactIdentity eta v.1 := by
        unfold compactIdentity
        rw [← mul_assoc]
        exact mul_nonneg hsign (cutoffWeight_nonneg (v.1 / eta))
      have habs : |alpha * compactIdentity eta v.1| ≤ |alpha * v.1| := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hpsi (abs_nonneg alpha)
      rw [abs_of_nonneg hsame, abs_of_nonneg hsign] at habs
      exact habs
    have hsquare : 0 ≤ (v.1 - d * alpha) ^ 2 / (2 * d) := by
      positivity
    have hcomplete : v.1 ^ 2 / (2 * d) + d / 2 * alpha ^ 2 - alpha * v.1 =
        (v.1 - d * alpha) ^ 2 / (2 * d) := by
      field_simp [hdpos.ne']
      ring
    have hgap : 0 ≤ alpha * v.1 - alpha * compactIdentity eta v.1 :=
      sub_nonneg.mpr hbound
    dsimp only [d, s, alpha] at htail hsquare hcomplete hgap ⊢
    nlinarith
  · have hprod : alpha * compactIdentity eta v.1 ≤ 0 := by
      unfold compactIdentity
      rw [← mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign)
        (cutoffWeight_nonneg (v.1 / eta))
    have hfirst : 0 ≤ v.1 ^ 2 / (2 * d) := by positivity
    have hforcing : 0 ≤ d / 2 * alpha ^ 2 := by positivity
    dsimp only [d, s, alpha] at htail hprod hfirst hforcing ⊢
    linarith

/-- A zero of the complete auxiliary block has the proposed first
coordinate. -/
theorem amplifiedScalarBlock_eq_zero_imp_first
    {eta kappa theta : ℝ} (hkappa : 1 < kappa)
    {v : AmplifierAux} (hzero : amplifiedScalarBlock eta kappa theta v = 0) :
    v.1 = amplifierDiag kappa * attenuatedFrontier kappa theta := by
  let d := amplifierDiag kappa
  let s := amplifierOffDiag kappa
  let alpha := attenuatedFrontier kappa theta
  have hkpos : 0 < kappa := by linarith
  have hdpos : 0 < d := amplifierDiag_pos hkpos
  have hq := amplifierQuadratic_complete_square hkpos v
  have hpsi := abs_compactIdentity_le eta v.1
  have htail : 0 ≤ d / (2 * kappa) *
      (v.2 - s / d * v.1) ^ 2 := by positivity
  rw [amplifiedScalarBlock, hq] at hzero
  unfold amplifiedCompensation at hzero
  dsimp only at hzero
  by_cases hsign : 0 ≤ alpha * v.1
  · have hsame : 0 ≤ alpha * compactIdentity eta v.1 := by
      unfold compactIdentity
      rw [← mul_assoc]
      exact mul_nonneg hsign (cutoffWeight_nonneg (v.1 / eta))
    have habs : |alpha * compactIdentity eta v.1| ≤ |alpha * v.1| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hpsi (abs_nonneg alpha)
    have hbound : alpha * compactIdentity eta v.1 ≤ alpha * v.1 := by
      rw [abs_of_nonneg hsame, abs_of_nonneg hsign] at habs
      exact habs
    have hsquare : 0 ≤ (v.1 - d * alpha) ^ 2 / (2 * d) := by
      positivity
    have hcomplete : v.1 ^ 2 / (2 * d) + d / 2 * alpha ^ 2 - alpha * v.1 =
        (v.1 - d * alpha) ^ 2 / (2 * d) := by
      field_simp [hdpos.ne']
      ring
    have hgap : 0 ≤ alpha * v.1 - alpha * compactIdentity eta v.1 :=
      sub_nonneg.mpr hbound
    have hsumzero : (v.1 - d * alpha) ^ 2 / (2 * d) +
        d / (2 * kappa) * (v.2 - s / d * v.1) ^ 2 +
        (alpha * v.1 - alpha * compactIdentity eta v.1) = 0 := by
      calc
        _ = v.1 ^ 2 / (2 * d) +
              d / (2 * kappa) * (v.2 - s / d * v.1) ^ 2 +
              (d / 2 * alpha ^ 2 - alpha * compactIdentity eta v.1) := by
                rw [← hcomplete]
                ring
        _ = 0 := by simpa [d, s, alpha] using hzero
    have hsquareFractionZero : (v.1 - d * alpha) ^ 2 / (2 * d) = 0 := by
      linarith
    have hsquareZero : (v.1 - d * alpha) ^ 2 = 0 := by
      exact (div_eq_zero_iff).mp hsquareFractionZero |>.resolve_right
        (mul_ne_zero (by norm_num) hdpos.ne')
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquareZero)
  · have hprod : alpha * compactIdentity eta v.1 ≤ 0 := by
      unfold compactIdentity
      rw [← mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign)
        (cutoffWeight_nonneg (v.1 / eta))
    have hfirst : 0 ≤ v.1 ^ 2 / (2 * d) := by positivity
    have hforcing : 0 ≤ d / 2 * alpha ^ 2 := by positivity
    have hminusprod : 0 ≤ -(alpha * compactIdentity eta v.1) :=
      neg_nonneg.mpr hprod
    have hsumzero : v.1 ^ 2 / (2 * d) +
        d / (2 * kappa) * (v.2 - s / d * v.1) ^ 2 +
        d / 2 * alpha ^ 2 - alpha * compactIdentity eta v.1 = 0 := by
      dsimp only [d, s, alpha]
      linarith [hzero]
    have hfirstZero : v.1 ^ 2 / (2 * d) = 0 := by linarith
    have hvzero : v.1 = 0 := by
      have : v.1 ^ 2 = 0 :=
        (div_eq_zero_iff).mp hfirstZero |>.resolve_right
          (mul_ne_zero (by norm_num) hdpos.ne')
      exact sq_eq_zero_iff.mp this
    have hforcingZero : d / 2 * alpha ^ 2 = 0 := by linarith
    have halpha : alpha = 0 := by
      have : alpha ^ 2 = 0 := by
        rcases mul_eq_zero.mp hforcingZero with hd | ha
        · exfalso
          exact (div_ne_zero hdpos.ne' (by norm_num)) hd
        · exact ha
      exact sq_eq_zero_iff.mp this
    change v.1 = d * alpha
    rw [hvzero, halpha, mul_zero]

/-- A zero of the complete auxiliary block has the proposed second
coordinate. -/
theorem amplifiedScalarBlock_eq_zero_imp_second
    {eta kappa theta : ℝ} (hkappa : 1 < kappa)
    {v : AmplifierAux} (hzero : amplifiedScalarBlock eta kappa theta v = 0) :
    v.2 = amplifierOffDiag kappa * attenuatedFrontier kappa theta := by
  let d := amplifierDiag kappa
  let s := amplifierOffDiag kappa
  let alpha := attenuatedFrontier kappa theta
  have hkpos : 0 < kappa := by linarith
  have hdpos : 0 < d := amplifierDiag_pos hkpos
  have hfirst := amplifiedScalarBlock_eq_zero_imp_first hkappa hzero
  have hq := amplifierQuadratic_complete_square hkpos v
  have htail : 0 ≤ d / (2 * kappa) *
      (v.2 - s / d * v.1) ^ 2 := by positivity
  rw [amplifiedScalarBlock, hq] at hzero
  unfold amplifiedCompensation at hzero
  dsimp only at hzero
  have hbaseNonneg : 0 ≤ v.1 ^ 2 / (2 * d) + d / 2 * alpha ^ 2 -
      alpha * compactIdentity eta v.1 := by
    have hblock := amplifiedScalarBlock_nonneg (eta := eta) (theta := theta) hkappa
      (v.1, (s / d) * v.1)
    rw [amplifiedScalarBlock,
      amplifierQuadratic_complete_square hkpos] at hblock
    unfold amplifiedCompensation at hblock
    dsimp only at hblock
    dsimp only [d, s, alpha]
    linarith [hblock]
  have hsumzero : v.1 ^ 2 / (2 * d) +
      d / (2 * kappa) * (v.2 - s / d * v.1) ^ 2 +
      d / 2 * alpha ^ 2 - alpha * compactIdentity eta v.1 = 0 := by
    dsimp only [d, s, alpha]
    linarith [hzero]
  have htailTermZero : d / (2 * kappa) *
      (v.2 - s / d * v.1) ^ 2 = 0 := by
    linarith
  have htailZero : (v.2 - s / d * v.1) ^ 2 = 0 := by
    exact (mul_eq_zero.mp htailTermZero).resolve_left
      (div_ne_zero hdpos.ne' (mul_ne_zero (by norm_num) hkpos.ne'))
  have hv2 : v.2 = s / d * v.1 :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp htailZero)
  change v.2 = s * alpha
  change v.1 = d * alpha at hfirst
  rw [hv2, hfirst]
  field_simp [hdpos.ne']

theorem amplifiedScalarBlock_eq_zero_iff
    {eta kappa theta : ℝ} (heta : 0 < eta) (hkappa : 1 < kappa)
    (hsmall :
      |amplifierDiag kappa * attenuatedFrontier kappa theta| ≤ eta)
    (v : AmplifierAux) :
    amplifiedScalarBlock eta kappa theta v = 0 ↔
      v = (amplifierDiag kappa * attenuatedFrontier kappa theta,
        amplifierOffDiag kappa * attenuatedFrontier kappa theta) := by
  constructor
  · intro hzero
    apply Prod.ext
    · exact amplifiedScalarBlock_eq_zero_imp_first hkappa hzero
    · exact amplifiedScalarBlock_eq_zero_imp_second hkappa hzero
  · intro hv
    subst v
    exact amplifiedScalarBlock_at_proposed heta hkappa hsmall

end

end BilevelLowerBound
