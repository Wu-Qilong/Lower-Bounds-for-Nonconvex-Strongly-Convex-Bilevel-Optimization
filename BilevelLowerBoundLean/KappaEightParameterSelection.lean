/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.Oracle

/-!
# Parameter selection for the `kappa^8 epsilon^-6` lower bound

This module is the scalar parameter layer of the two-dimensional amplifier
construction.  It is intentionally separate from the earlier scalar
amplifier parameter file.  The attenuated stochastic frontier has squared
size proportional to `eta^4 / kappa^2`, so the Bernoulli reveal probability
is

`min 1 (Cvar * eta^4 / (sigma^2 * kappa^2))`.

After substituting `eta = 4 epsilon / kappa`, its reciprocal contributes
`max 1 (sigma^2 * kappa^6 / (256 Cvar epsilon^4))`.  Multiplication by the
chain length, of order `Delta kappa^2 / epsilon^2`, produces the stochastic
scale `Delta sigma^2 kappa^8 / epsilon^6`.
-/

namespace BilevelLowerBound

noncomputable section

/-! ## Reveal probability for the attenuated lower-level signal -/

/-- Reveal probability for a stochastic frontier attenuated by `1 / kappa`.
The explicit `sigma = 0` branch gives the exact deterministic oracle. -/
def kappaEightRevealProbability
    (Cvar eta kappa sigma : ℝ) : ℝ :=
  if sigma = 0 then 1 else
    min 1 (Cvar * eta ^ 4 / (sigma ^ 2 * kappa ^ 2))

theorem kappaEightRevealProbability_pos
    {Cvar eta kappa sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hkappa : 0 < kappa) :
    0 < kappaEightRevealProbability Cvar eta kappa sigma := by
  unfold kappaEightRevealProbability
  split_ifs with hsigma
  · norm_num
  · apply lt_min (by norm_num)
    positivity

theorem kappaEightRevealProbability_le_one
    (Cvar eta kappa sigma : ℝ) :
    kappaEightRevealProbability Cvar eta kappa sigma ≤ 1 := by
  unfold kappaEightRevealProbability
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem kappaEightRevealProbability_mem_unitInterval
    {Cvar eta kappa sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hkappa : 0 < kappa) :
    kappaEightRevealProbability Cvar eta kappa sigma ∈ Set.Ioc 0 1 := by
  exact ⟨kappaEightRevealProbability_pos hCvar heta hkappa,
    kappaEightRevealProbability_le_one _ _ _ _⟩

/-- The attenuated Bernoulli correction obeys the prescribed variance
budget.  The factor preceding the Bernoulli ratio is the squared size of the
attenuated frontier. -/
theorem kappaEightRevealProbability_variance_le
    {Cvar eta kappa sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma) :
    (Cvar * eta ^ 4 / kappa ^ 2) *
        ((1 - kappaEightRevealProbability Cvar eta kappa sigma) /
          kappaEightRevealProbability Cvar eta kappa sigma) ≤
      sigma ^ 2 := by
  by_cases hs0 : sigma = 0
  · simp [kappaEightRevealProbability, hs0]
  · have hspos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hs0)
    let a : ℝ := Cvar * eta ^ 4 / (sigma ^ 2 * kappa ^ 2)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    rw [kappaEightRevealProbability, if_neg hs0]
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1]
      simp only [sub_self, div_one, mul_zero]
      exact sq_nonneg sigma
    · have halt : a < 1 := lt_of_not_ge ha1
      rw [min_eq_right halt.le]
      dsimp [a]
      field_simp [hs0, hkappa.ne']
      nlinarith [sq_nonneg sigma,
        mul_pos hCvar (pow_pos heta 4), sq_pos_of_pos hkappa]

/-- Exact reciprocal form of the reveal probability. -/
theorem one_div_kappaEightRevealProbability
    {Cvar eta kappa sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma) :
    1 / kappaEightRevealProbability Cvar eta kappa sigma =
      max 1 (sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4)) := by
  by_cases hs0 : sigma = 0
  · simp [kappaEightRevealProbability, hs0]
  · have hspos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hs0)
    let a : ℝ := Cvar * eta ^ 4 / (sigma ^ 2 * kappa ^ 2)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    rw [kappaEightRevealProbability, if_neg hs0]
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1]
      have hquot : sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4) ≤ 1 := by
        dsimp [a] at ha1
        have hnum : sigma ^ 2 * kappa ^ 2 ≤ Cvar * eta ^ 4 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (le_div_iff₀ (mul_pos (sq_pos_of_pos hspos)
              (sq_pos_of_pos hkappa))).mp ha1
        exact (div_le_one (mul_pos hCvar (pow_pos heta 4))).2 hnum
      simp [max_eq_left hquot]
    · have halt : a < 1 := lt_of_not_ge ha1
      rw [min_eq_right halt.le]
      have hinv : 1 / a =
          sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4) := by
        dsimp [a]
        field_simp [hCvar.ne', heta.ne', hkappa.ne', hs0]
      have hquot : 1 ≤
          sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4) := by
        rw [← hinv, one_div]
        exact (one_le_inv₀ ha).2 halt.le
      rw [max_eq_right hquot]
      exact hinv

/-- Direct stochastic-oracle consequence of the scalar variance estimate. -/
theorem kappaEightBernoulliSquaredNoise_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Cvar eta kappa sigma : ℝ}
    (hCvar : 0 < Cvar) (heta : 0 < eta) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma) (base frontier : V)
    (hfrontier : ‖frontier‖ ^ 2 ≤ Cvar * eta ^ 4 / kappa ^ 2) :
    bernoulliSquaredNoise
        (kappaEightRevealProbability Cvar eta kappa sigma)
        (importanceSample
          (kappaEightRevealProbability Cvar eta kappa sigma) 1 base frontier)
        (importanceSample
          (kappaEightRevealProbability Cvar eta kappa sigma) 0 base frontier)
        (base + frontier) ≤ sigma ^ 2 := by
  let p := kappaEightRevealProbability Cvar eta kappa sigma
  have hp : 0 < p := kappaEightRevealProbability_pos hCvar heta hkappa
  have hp1 : p ≤ 1 := kappaEightRevealProbability_le_one _ _ _ _
  rw [bernoulliSquaredNoise_importanceSample hp hp1]
  have hratio : 0 ≤ (1 - p) / p :=
    div_nonneg (sub_nonneg.mpr hp1) hp.le
  calc
    (1 - p) / p * ‖frontier‖ ^ 2 ≤
        (1 - p) / p * (Cvar * eta ^ 4 / kappa ^ 2) :=
      mul_le_mul_of_nonneg_left hfrontier hratio
    _ = (Cvar * eta ^ 4 / kappa ^ 2) * ((1 - p) / p) := by ring
    _ ≤ sigma ^ 2 := by
      simpa [p] using kappaEightRevealProbability_variance_le
        hCvar heta hkappa hsigma

/-! ## Accuracy scale and rounded chain length -/

def kappaEightFinalEta (epsilon kappa : ℝ) : ℝ :=
  4 * epsilon / kappa

def kappaEightFinalChainScale
    (Delta CDelta epsilon kappa : ℝ) : ℝ :=
  Delta / (2 * CDelta * (kappaEightFinalEta epsilon kappa) ^ 2)

def kappaEightFinalChainLength
    (Delta CDelta epsilon kappa : ℝ) : ℕ :=
  ⌊kappaEightFinalChainScale Delta CDelta epsilon kappa⌋₊

def kappaEightLowerBoundConstant (CDelta Cvar : ℝ) : ℝ :=
  1 / (512 * CDelta * max 1 (256 * Cvar))

theorem kappaEightFinalEta_pos
    {epsilon kappa : ℝ} (hepsilon : 0 < epsilon) (hkappa : 0 < kappa) :
    0 < kappaEightFinalEta epsilon kappa := by
  unfold kappaEightFinalEta
  positivity

theorem kappaEightFinalEta_sq
    {epsilon kappa : ℝ} (hkappa : kappa ≠ 0) :
    (kappaEightFinalEta epsilon kappa) ^ 2 =
      16 * epsilon ^ 2 / kappa ^ 2 := by
  unfold kappaEightFinalEta
  field_simp [hkappa]
  ring

theorem kappaEightFinalEta_fourth
    {epsilon kappa : ℝ} (hkappa : kappa ≠ 0) :
    (kappaEightFinalEta epsilon kappa) ^ 4 =
      256 * epsilon ^ 4 / kappa ^ 4 := by
  have hsq := kappaEightFinalEta_sq (epsilon := epsilon) hkappa
  calc
    (kappaEightFinalEta epsilon kappa) ^ 4 =
        ((kappaEightFinalEta epsilon kappa) ^ 2) ^ 2 := by ring
    _ = (16 * epsilon ^ 2 / kappa ^ 2) ^ 2 := by rw [hsq]
    _ = 256 * epsilon ^ 4 / kappa ^ 4 := by
      field_simp [hkappa]
      ring

theorem kappaEightFinalChainScale_eq
    {Delta CDelta epsilon kappa : ℝ}
    (hCDelta : CDelta ≠ 0) (hepsilon : epsilon ≠ 0)
    (hkappa : kappa ≠ 0) :
    kappaEightFinalChainScale Delta CDelta epsilon kappa =
      Delta * kappa ^ 2 / (32 * CDelta * epsilon ^ 2) := by
  unfold kappaEightFinalChainScale kappaEightFinalEta
  field_simp [hCDelta, hepsilon, hkappa]
  ring

theorem kappaEightNatFloor_two_sided
    {X : ℝ} (hX : 2 ≤ X) :
    X / 2 ≤ (⌊X⌋₊ : ℝ) ∧ (⌊X⌋₊ : ℝ) ≤ X := by
  have hX0 : 0 ≤ X := by linarith
  constructor
  · have hfloor := (Nat.sub_one_lt_floor X).le
    linarith
  · exact Nat.floor_le hX0

theorem kappaEightFinalChainLength_two_sided
    {Delta CDelta epsilon kappa : ℝ}
    (hX : 2 ≤ kappaEightFinalChainScale Delta CDelta epsilon kappa) :
    kappaEightFinalChainScale Delta CDelta epsilon kappa / 2 ≤
        (kappaEightFinalChainLength Delta CDelta epsilon kappa : ℝ) ∧
      (kappaEightFinalChainLength Delta CDelta epsilon kappa : ℝ) ≤
        kappaEightFinalChainScale Delta CDelta epsilon kappa := by
  exact kappaEightNatFloor_two_sided hX

theorem kappaEightFinalChainLength_pos
    {Delta CDelta epsilon kappa : ℝ}
    (hX : 2 ≤ kappaEightFinalChainScale Delta CDelta epsilon kappa) :
    0 < kappaEightFinalChainLength Delta CDelta epsilon kappa := by
  rw [kappaEightFinalChainLength, Nat.floor_pos]
  linarith

/-! ## Substitution into the call budget -/

theorem kappaEightMaxOneDivComparison
    {a beta : ℝ} (ha : 0 ≤ a) (hbeta : 0 < beta) :
    (1 / max 1 beta) * max 1 a ≤ max 1 (a / beta) := by
  by_cases hbetaOne : 1 ≤ beta
  · rw [max_eq_right hbetaOne]
    rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ (1 / beta : ℝ))]
    apply max_le
    · have hone : 1 / beta ≤ 1 := (div_le_one hbeta).2 hbetaOne
      simpa using hone.trans (le_max_left 1 (a / beta))
    · simpa [div_eq_mul_inv, mul_comm] using
        (le_max_right 1 (a / beta))
  · have hbetaLe : beta ≤ 1 := le_of_not_ge hbetaOne
    rw [max_eq_left hbetaLe]
    simp only [div_one, one_mul]
    apply max_le_max le_rfl
    exact (le_div_iff₀ hbeta).2 (by
      simpa only [mul_comm] using mul_le_of_le_one_right ha hbetaLe)

/-- Exact algebraic source of the sixth power inside the stochastic maximum.
The outer chain factor supplies the remaining `kappa^2`. -/
theorem kappaEightFinalCallScale_identity
    {Delta CDelta Cvar epsilon kappa sigma : ℝ}
    (hCDelta : CDelta ≠ 0) (hCvar : Cvar ≠ 0)
    (hepsilon : epsilon ≠ 0) (hkappa : kappa ≠ 0) :
    Delta / (32 * CDelta * (kappaEightFinalEta epsilon kappa) ^ 2) *
        max 1
          (sigma ^ 2 * kappa ^ 2 /
            (Cvar * (kappaEightFinalEta epsilon kappa) ^ 4)) =
      Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
        max 1
          (sigma ^ 2 * kappa ^ 6 /
            (256 * Cvar * epsilon ^ 4)) := by
  rw [kappaEightFinalEta_sq hkappa, kappaEightFinalEta_fourth hkappa]
  congr 1
  · field_simp [hCDelta, hepsilon, hkappa]
    ring
  · congr 1
    field_simp [hCvar, hepsilon, hkappa]

/-- The rounded-chain lower bound implies the raw `T / (8p)` budget. -/
theorem kappaEightFinal_T_over_p_raw
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {T : ℕ}
    (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma)
    (hTlower :
      Delta /
          (4 * CDelta * (kappaEightFinalEta epsilon kappa) ^ 2) ≤
        (T : ℝ)) :
    Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
        max 1
          (sigma ^ 2 * kappa ^ 6 /
            (256 * Cvar * epsilon ^ 4)) ≤
      (T : ℝ) /
        (8 * kappaEightRevealProbability Cvar
          (kappaEightFinalEta epsilon kappa) kappa sigma) := by
  let eta := kappaEightFinalEta epsilon kappa
  let prob := kappaEightRevealProbability Cvar eta kappa sigma
  have heta : 0 < eta := kappaEightFinalEta_pos hepsilon hkappa
  have hprob : 0 < prob :=
    kappaEightRevealProbability_pos hCvar heta hkappa
  have hinv : 1 / prob =
      max 1 (sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4)) := by
    exact one_div_kappaEightRevealProbability hCvar heta hkappa hsigma
  have hTdiv : Delta / (32 * CDelta * eta ^ 2) ≤ (T : ℝ) / 8 := by
    calc
      Delta / (32 * CDelta * eta ^ 2) =
          (Delta / (4 * CDelta * eta ^ 2)) / 8 := by ring
      _ ≤ (T : ℝ) / 8 := by
        exact div_le_div_of_nonneg_right (by simpa [eta] using hTlower)
          (by norm_num)
  have hscale0 : 0 ≤ 1 / prob := by positivity
  calc
    Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
          max 1
            (sigma ^ 2 * kappa ^ 6 /
              (256 * Cvar * epsilon ^ 4)) =
        Delta / (32 * CDelta * eta ^ 2) *
          max 1 (sigma ^ 2 * kappa ^ 2 / (Cvar * eta ^ 4)) := by
            symm
            simpa [eta] using kappaEightFinalCallScale_identity
              hCDelta.ne' hCvar.ne' hepsilon.ne' hkappa.ne'
    _ = Delta / (32 * CDelta * eta ^ 2) * (1 / prob) := by
      rw [hinv]
    _ ≤ ((T : ℝ) / 8) * (1 / prob) :=
      mul_le_mul_of_nonneg_right hTdiv hscale0
    _ = (T : ℝ) / (8 * prob) := by
      field_simp [hprob.ne']
    _ = (T : ℝ) /
        (8 * kappaEightRevealProbability Cvar
          (kappaEightFinalEta epsilon kappa) kappa sigma) := by
      rfl

/-- The full deterministic-plus-stochastic scale generated by the
two-dimensional amplifier. -/
def kappaEightComplexityScale
    (Delta epsilon kappa sigma : ℝ) : ℝ :=
  Delta * kappa ^ 2 / epsilon ^ 2 *
    max 1 (sigma ^ 2 * kappa ^ 6 / epsilon ^ 4)

theorem kappaEightComplexityScale_nonneg
    {Delta epsilon kappa sigma : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : epsilon ≠ 0) :
    0 ≤ kappaEightComplexityScale Delta epsilon kappa sigma := by
  unfold kappaEightComplexityScale
  positivity

theorem kappaEightComplexityScale_expand
    {Delta epsilon kappa sigma : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon) :
    kappaEightComplexityScale Delta epsilon kappa sigma =
      max (Delta * kappa ^ 2 / epsilon ^ 2)
        (Delta * sigma ^ 2 * kappa ^ 8 / epsilon ^ 6) := by
  unfold kappaEightComplexityScale
  rw [mul_max_of_nonneg _ _ (by positivity :
    0 ≤ Delta * kappa ^ 2 / epsilon ^ 2)]
  congr 1
  field_simp [hepsilon.ne']
  ring

theorem kappaEightFinal_T_over_p_main_scale
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {T : ℕ}
    (hDelta : 0 ≤ Delta) (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma)
    (hTlower :
      Delta /
          (4 * CDelta * (kappaEightFinalEta epsilon kappa) ^ 2) ≤
        (T : ℝ)) :
    kappaEightLowerBoundConstant CDelta Cvar *
        kappaEightComplexityScale Delta epsilon kappa sigma ≤
      (T : ℝ) /
        (8 * kappaEightRevealProbability Cvar
          (kappaEightFinalEta epsilon kappa) kappa sigma) := by
  have hraw := kappaEightFinal_T_over_p_raw hCDelta hCvar
    hepsilon hkappa hsigma hTlower
  let a : ℝ := sigma ^ 2 * kappa ^ 6 / epsilon ^ 4
  let beta : ℝ := 256 * Cvar
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hmax := kappaEightMaxOneDivComparison ha hbeta
  have hbase :
      0 ≤ Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) := by
    positivity
  calc
    kappaEightLowerBoundConstant CDelta Cvar *
          kappaEightComplexityScale Delta epsilon kappa sigma =
        (Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2)) *
          ((1 / max 1 beta) * max 1 a) := by
            unfold kappaEightLowerBoundConstant kappaEightComplexityScale
            dsimp [beta, a]
            field_simp [hCDelta.ne', hepsilon.ne']
    _ ≤ (Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2)) *
          max 1 (a / beta) :=
      mul_le_mul_of_nonneg_left hmax hbase
    _ = Delta * kappa ^ 2 / (512 * CDelta * epsilon ^ 2) *
          max 1
            (sigma ^ 2 * kappa ^ 6 /
              (256 * Cvar * epsilon ^ 4)) := by
      congr 2
      dsimp [a, beta]
      field_simp [hCvar.ne', hepsilon.ne']
    _ ≤ (T : ℝ) /
        (8 * kappaEightRevealProbability Cvar
          (kappaEightFinalEta epsilon kappa) kappa sigma) := hraw

theorem kappaEightCallBudget_implies_progress_condition
    {Delta CDelta Cvar epsilon kappa sigma : ℝ} {N T : ℕ}
    (hDelta : 0 ≤ Delta) (hCDelta : 0 < CDelta) (hCvar : 0 < Cvar)
    (hepsilon : 0 < epsilon) (hkappa : 0 < kappa)
    (hsigma : 0 ≤ sigma) (hT : 0 < T)
    (hTlower :
      Delta /
          (4 * CDelta * (kappaEightFinalEta epsilon kappa) ^ 2) ≤
        (T : ℝ))
    (hN : (N : ℝ) ≤
      kappaEightLowerBoundConstant CDelta Cvar *
        kappaEightComplexityScale Delta epsilon kappa sigma) :
    (N : ℝ) *
          kappaEightRevealProbability Cvar
            (kappaEightFinalEta epsilon kappa) kappa sigma /
        T ≤ 1 / 8 := by
  let prob := kappaEightRevealProbability Cvar
    (kappaEightFinalEta epsilon kappa) kappa sigma
  have heta := kappaEightFinalEta_pos hepsilon hkappa
  have hprob : 0 < prob :=
    kappaEightRevealProbability_pos hCvar heta hkappa
  have hbudget : (N : ℝ) ≤ (T : ℝ) / (8 * prob) :=
    hN.trans (kappaEightFinal_T_over_p_main_scale hDelta hCDelta hCvar
      hepsilon hkappa hsigma hTlower)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hmul := mul_le_mul_of_nonneg_right hbudget hprob.le
  have hNp : (N : ℝ) * prob ≤ (T : ℝ) / 8 := by
    calc
      (N : ℝ) * prob ≤ ((T : ℝ) / (8 * prob)) * prob := hmul
      _ = (T : ℝ) / 8 := by field_simp [hprob.ne']
  change (N : ℝ) * prob / T ≤ 1 / 8
  apply (div_le_iff₀ hTreal).2
  calc
    (N : ℝ) * prob ≤ (T : ℝ) / 8 := hNp
    _ = (1 / 8 : ℝ) * T := by ring

/-! ## Replacement by the intrinsic condition number -/

/-- Replacing the construction parameter by a comparable intrinsic
condition number loses at most the eighth power of the comparison constant. -/
theorem kappaEightConditionNumber_scale_comparison
    {Delta epsilon kappa kappaY sigma Ckappa : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (_hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (_hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hupper : kappaY ≤ Ckappa * kappa) :
    kappaEightComplexityScale Delta epsilon kappaY sigma /
        Ckappa ^ 8 ≤
      kappaEightComplexityScale Delta epsilon kappa sigma := by
  have hC0 : 0 ≤ Ckappa := hCkappa.trans' (by norm_num)
  have hkSqRaw := pow_le_pow_left₀ hkappaY hupper 2
  have hkSq : kappaY ^ 2 ≤ Ckappa ^ 2 * kappa ^ 2 := by
    calc
      kappaY ^ 2 ≤ (Ckappa * kappa) ^ 2 := hkSqRaw
      _ = Ckappa ^ 2 * kappa ^ 2 := by ring
  have hkSixRaw := pow_le_pow_left₀ hkappaY hupper 6
  have hkSix : kappaY ^ 6 ≤ Ckappa ^ 6 * kappa ^ 6 := by
    calc
      kappaY ^ 6 ≤ (Ckappa * kappa) ^ 6 := hkSixRaw
      _ = Ckappa ^ 6 * kappa ^ 6 := by ring
  let aY : ℝ := sigma ^ 2 * kappaY ^ 6 / epsilon ^ 4
  let aK : ℝ := sigma ^ 2 * kappa ^ 6 / epsilon ^ 4
  have haY : 0 ≤ aY := by
    dsimp [aY]
    positivity
  have haK : 0 ≤ aK := by
    dsimp [aK]
    positivity
  have haComp : aY ≤ Ckappa ^ 6 * aK := by
    dsimp [aY, aK]
    apply (div_le_iff₀ (by positivity : 0 < epsilon ^ 4)).2
    have hmul := mul_le_mul_of_nonneg_left hkSix (sq_nonneg sigma)
    calc
      sigma ^ 2 * kappaY ^ 6 ≤
          sigma ^ 2 * (Ckappa ^ 6 * kappa ^ 6) := hmul
      _ = Ckappa ^ 6 *
          (sigma ^ 2 * kappa ^ 6 / epsilon ^ 4) * epsilon ^ 4 := by
        field_simp [hepsilon.ne']
  have hCsix : 1 ≤ Ckappa ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hCkappa 6
    simpa using this
  have hmax : max 1 aY ≤ Ckappa ^ 6 * max 1 aK := by
    apply max_le
    · calc
        1 ≤ Ckappa ^ 6 := hCsix
        _ = Ckappa ^ 6 * 1 := by ring
        _ ≤ Ckappa ^ 6 * max 1 aK :=
          mul_le_mul_of_nonneg_left (le_max_left 1 aK) (by positivity)
    · exact haComp.trans
        (mul_le_mul_of_nonneg_left (le_max_right 1 aK) (by positivity))
  have hbase :
      Delta * kappaY ^ 2 / epsilon ^ 2 ≤
        Ckappa ^ 2 * (Delta * kappa ^ 2 / epsilon ^ 2) := by
    apply (div_le_iff₀ (by positivity : 0 < epsilon ^ 2)).2
    have hmul := mul_le_mul_of_nonneg_left hkSq hDelta
    calc
      Delta * kappaY ^ 2 ≤
          Delta * (Ckappa ^ 2 * kappa ^ 2) := hmul
      _ = Ckappa ^ 2 *
          (Delta * kappa ^ 2 / epsilon ^ 2) * epsilon ^ 2 := by
        field_simp [hepsilon.ne']
  have hprod := mul_le_mul hbase hmax
    (by exact le_max_left 1 aY |>.trans' (by norm_num))
    (by positivity)
  have hCpos : 0 < Ckappa ^ 8 := by positivity
  unfold kappaEightComplexityScale
  dsimp [aY, aK] at hprod ⊢
  apply (div_le_iff₀ hCpos).2
  calc
    (Delta * kappaY ^ 2 / epsilon ^ 2) *
          max 1 (sigma ^ 2 * kappaY ^ 6 / epsilon ^ 4) ≤
        (Ckappa ^ 2 * (Delta * kappa ^ 2 / epsilon ^ 2)) *
          (Ckappa ^ 6 *
            max 1 (sigma ^ 2 * kappa ^ 6 / epsilon ^ 4)) := hprod
    _ = (Delta * kappa ^ 2 / epsilon ^ 2 *
          max 1 (sigma ^ 2 * kappa ^ 6 / epsilon ^ 4)) *
        Ckappa ^ 8 := by ring

theorem kappaEightConditionNumber_callBudget_transfer
    {N : ℕ} {Delta epsilon kappa kappaY sigma Ckappa cLB : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hcLB : 0 ≤ cLB) (hupper : kappaY ≤ Ckappa * kappa)
    (hN : (N : ℝ) ≤
      (cLB / Ckappa ^ 8) *
        kappaEightComplexityScale Delta epsilon kappaY sigma) :
    (N : ℝ) ≤
      cLB * kappaEightComplexityScale Delta epsilon kappa sigma := by
  have hscale := kappaEightConditionNumber_scale_comparison hDelta hepsilon
    hkappa hkappaY hsigma hCkappa hupper
  calc
    (N : ℝ) ≤
        (cLB / Ckappa ^ 8) *
          kappaEightComplexityScale Delta epsilon kappaY sigma := hN
    _ = cLB *
        (kappaEightComplexityScale Delta epsilon kappaY sigma /
          Ckappa ^ 8) := by ring
    _ ≤ cLB * kappaEightComplexityScale Delta epsilon kappa sigma :=
      mul_le_mul_of_nonneg_left hscale hcLB

theorem kappaEightConditionNumber_scale_sandwich
    {Delta epsilon kappa kappaY sigma Ckappa : ℝ}
    (hDelta : 0 ≤ Delta) (hepsilon : 0 < epsilon)
    (hkappa : 0 ≤ kappa) (hkappaY : 0 ≤ kappaY)
    (hsigma : 0 ≤ sigma) (hCkappa : 1 ≤ Ckappa)
    (hlower : kappa ≤ kappaY) (hupper : kappaY ≤ Ckappa * kappa) :
    kappaEightComplexityScale Delta epsilon kappa sigma ≤
        kappaEightComplexityScale Delta epsilon kappaY sigma ∧
      kappaEightComplexityScale Delta epsilon kappaY sigma /
          Ckappa ^ 8 ≤
        kappaEightComplexityScale Delta epsilon kappa sigma := by
  constructor
  · have hmono := kappaEightConditionNumber_scale_comparison
      (kappa := kappaY) (kappaY := kappa) (Ckappa := 1)
      hDelta hepsilon hkappaY hkappa hsigma (by norm_num)
      (by simpa using hlower)
    simpa using hmono
  · exact kappaEightConditionNumber_scale_comparison hDelta hepsilon
      hkappa hkappaY hsigma hCkappa hupper

end

end BilevelLowerBound
