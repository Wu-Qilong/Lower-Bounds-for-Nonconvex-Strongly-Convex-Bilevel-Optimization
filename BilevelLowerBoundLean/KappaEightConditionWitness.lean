/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPopulationRegularity
import BilevelLowerBoundLean.ConditionWitness
import BilevelLowerBoundLean.KappaEightPaperClasses

/-!
# Condition-number witnesses for the two-coordinate hard instance

The weak and strong eigen-directions of the amplifier provide both sharp
condition-number witnesses at a point where the hidden frontier is locally
zero.  With Mathlib's product norm these directions both have norm one, and
their Hessian values are exactly `2 / kappa` and `2`.  Combined with the
global `(2*kappa)^{-1}` lower certificate and the uniform Hessian upper bound,
this proves that the intrinsic lower condition number is between `kappa` and
`14*kappa`.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Flatness of the amplified compensation -/

theorem eventually_kappaEightCompensatedPair_eq_zero_of_theta_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} {theta : E → ℝ} {z : E} (v : AmplifierAux)
    (htheta : theta =ᶠ[nhds z] (fun _ ↦ 0)) :
    kappaEightCompensatedPair eta kappa theta =ᶠ[nhds (z, v)]
      (fun _ ↦ 0) := by
  have hthetaProd := htheta.comp_tendsto
    (continuousAt_fst : Tendsto (fun p : E × AmplifierAux ↦ p.1)
      (nhds (z, v)) (nhds z))
  filter_upwards [hthetaProd] with p hp
  have hpzero : theta p.1 = 0 := by simpa using hp
  simp [kappaEightCompensatedPair, amplifiedCompensation,
    attenuatedFrontier, hpzero]

theorem iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_of_theta_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} {theta : E → ℝ} {z : E} (v : AmplifierAux)
    (htheta : theta =ᶠ[nhds z] (fun _ ↦ 0)) :
    iteratedFDeriv ℝ 2 (kappaEightCompensatedPair eta kappa theta)
      (z, v) = 0 := by
  have hlocal :=
    eventually_kappaEightCompensatedPair_eq_zero_of_theta_zero
      (eta := eta) (kappa := kappa) v htheta
  have hjet := hlocal.iteratedFDeriv (𝕜 := ℝ) 2
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hjet.eq_of_nhds

theorem iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_at_fullProgress
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta kappa : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T))
    (v : AmplifierAux) :
    iteratedFDeriv ℝ 2
      (kappaEightCompensatedPair eta kappa (hardFrontierMap eta L))
      (fullProgressWitness eta J, v) = 0 := by
  exact
    iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_of_theta_zero v
      (eventually_hardFrontierMap_eq_zero_at_fullProgressWitness
        heta hT L J hJ hLJ)

/-! ## Exact weak and strong eigen-directions -/

theorem amplifierHessianForm_weak_direction
    {kappa : ℝ} (hkappa : kappa ≠ 0) :
    amplifierHessianForm kappa (1, 1) (1, 1) = 2 / kappa := by
  unfold amplifierHessianForm
  norm_num
  field_simp [hkappa]
  nlinarith [amplifierDiag_sub_offDiag kappa]

theorem amplifierHessianForm_strong_direction
    {kappa : ℝ} (hkappa : kappa ≠ 0) :
    amplifierHessianForm kappa (1, -1) (1, -1) = 2 := by
  unfold amplifierHessianForm
  norm_num
  field_simp [hkappa]
  nlinarith [amplifierDiag_add_offDiag kappa]

def kappaEightWeakDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E × AmplifierAux :=
  (0, (1, 1))

def kappaEightStrongDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E × AmplifierAux :=
  (0, (1, -1))

@[simp] theorem norm_kappaEightWeakDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖kappaEightWeakDirection (E := E)‖ = 1 := by
  simp [kappaEightWeakDirection, Prod.norm_def]

@[simp] theorem norm_kappaEightStrongDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖kappaEightStrongDirection (E := E)‖ = 1 := by
  simp [kappaEightStrongDirection, Prod.norm_def]

theorem kappaEightLowerBaseSlice_weak_witness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : kappa ≠ 0) (x : E)
    (p : E × AmplifierAux) :
    iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p
      (fun _ ↦ kappaEightWeakDirection (E := E)) = 2 / kappa := by
  rw [kappaEightLowerBaseSlice_diagonal_hessian hkappa]
  simp [kappaEightWeakDirection, amplifierHessianForm_weak_direction hkappa]

theorem kappaEightLowerBaseSlice_strong_witness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa : ℝ} (hkappa : kappa ≠ 0) (x : E)
    (p : E × AmplifierAux) :
    iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x) p
      (fun _ ↦ kappaEightStrongDirection (E := E)) = 2 := by
  rw [kappaEightLowerBaseSlice_diagonal_hessian hkappa]
  simp [kappaEightStrongDirection,
    amplifierHessianForm_strong_direction hkappa]

/-! ## Sharp moduli and the intrinsic condition number -/

set_option maxHeartbeats 1000000 in
-- The proof simultaneously tracks the sharp lower and upper Hessian moduli.
/-- Abstract sharp-modulus comparison.  The only pointwise input is a flat
point at which the compensated block has zero Hessian; the preceding lemmas
construct that point for the hidden hard frontier. -/
theorem kappaEight_condition_number_comparison_of_flat_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 ≤ kappa) (theta : E → ℝ)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    (hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤
          1 / (2 * kappa))
    (x0 : E) (p0 : E × AmplifierAux)
    (hflat : iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p0 = 0)
    (muGAct Ly : ℝ)
    (hmuGAct : KappaEightIsSharpLowerHessianModulus
      (fun (x : E) (p : E × AmplifierAux) ↦ kappaEightPopulationLower
        kappa eta theta x p.1 p.2) muGAct)
    (hLy : KappaEightIsSharpLowerHessianUpperBound
      (fun (x : E) (p : E × AmplifierAux) ↦ kappaEightPopulationLower
        kappa eta theta x p.1 p.2) Ly) :
    kappa ≤ Ly / muGAct ∧ Ly / muGAct ≤ 14 * kappa := by
  let G : E → E × AmplifierAux → ℝ :=
    fun x p ↦ kappaEightPopulationLower kappa eta theta x p.1 p.2
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hmuCert : ∀ x p w,
      (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w) := by
    intro x p w
    exact kappaEightPopulationLower_strong_hessian
      hkappa theta x hcomp hcomp2 p w
  have hmuGActLower : 1 / (2 * kappa) ≤ muGAct :=
    hmuGAct.2.2 _ hmuCert
  have hLyCert : ∀ x p, ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ 7 := by
    intro x p
    have hraw := kappaEightPopulationLower_second_bound
      hkappa theta x hcomp hcomp2 p
    have hinv : 1 / (2 * kappa) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2 * kappa)).2
      nlinarith
    linarith
  have hLyUpper : Ly ≤ 7 := hLy.2.2 _ hLyCert
  let weak : E × AmplifierAux := kappaEightWeakDirection
  let strong : E × AmplifierAux := kappaEightStrongDirection
  have hpopulationFlat : iteratedFDeriv ℝ 2 (G x0) p0 =
      iteratedFDeriv ℝ 2 (kappaEightLowerBaseSlice kappa x0) p0 := by
    rw [show G x0 = lowerPopulationSum
        (kappaEightLowerBaseSlice kappa x0)
        (kappaEightCompensatedPair eta kappa theta) by
      exact kappaEightPopulationLower_eq_base_add_compensation
        kappa eta theta x0]
    unfold lowerPopulationSum
    rw [iteratedFDeriv_add_apply
      ((kappaEightLowerBaseSlice_contDiff kappa x0).of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
      ((hcomp.of_le
        (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt), hflat]
    simp
  have hmuGActWitness := hmuGAct.2.1 x0 p0 weak
  have hweakEval :
      iteratedFDeriv ℝ 2 (G x0) p0 (fun _ ↦ weak) = 2 / kappa := by
    rw [hpopulationFlat]
    exact kappaEightLowerBaseSlice_weak_witness hkpos.ne' x0 p0
  rw [hweakEval] at hmuGActWitness
  have hweakNorm : ‖weak‖ = 1 := by simp [weak]
  rw [hweakNorm] at hmuGActWitness
  norm_num at hmuGActWitness
  have hmuGActUpper : muGAct ≤ 2 / kappa := hmuGActWitness
  let H := iteratedFDeriv ℝ 2 (G x0) p0
  have hstrongEval : H (fun _ ↦ strong) = 2 := by
    dsimp [H]
    rw [hpopulationFlat]
    exact kappaEightLowerBaseSlice_strong_witness hkpos.ne' x0 p0
  have hHop := H.le_opNorm (fun _ : Fin 2 ↦ strong)
  have hstrongNorm : ‖strong‖ = 1 := by simp [strong]
  rw [Real.norm_eq_abs, hstrongEval, abs_of_nonneg (by norm_num),
    Fin.prod_univ_two, hstrongNorm, one_mul, mul_one] at hHop
  have hLyAt : ‖H‖ ≤ Ly := hLy.2.1 x0 p0
  have hLyLower : 2 ≤ Ly := hHop.trans hLyAt
  have hmuGActPos : 0 < muGAct := hmuGAct.1
  constructor
  · apply (le_div_iff₀ hmuGActPos).2
    have hkm : kappa * muGAct ≤ 2 := by
      have h := mul_le_mul_of_nonneg_left hmuGActUpper hkpos.le
      calc
        kappa * muGAct ≤ kappa * (2 / kappa) := h
        _ = 2 := by field_simp [hkpos.ne']
    exact hkm.trans hLyLower
  · apply (div_le_iff₀ hmuGActPos).2
    have hseven : 7 ≤ 14 * kappa * muGAct := by
      have h := mul_le_mul_of_nonneg_left hmuGActLower
        (show 0 ≤ 14 * kappa by positivity)
      calc
        7 = (14 * kappa) * (1 / (2 * kappa)) := by
          field_simp [hkpos.ne']
          ring
        _ ≤ (14 * kappa) * muGAct := h
        _ = 14 * kappa * muGAct := by ring
    exact hLyUpper.trans hseven

/-- Specialization of the sharp-modulus comparison to the actual hidden
frontier.  The full-progress point supplies the required flat Hessian. -/
theorem kappaEight_hardFrontier_condition_number_comparison
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {kappa eta : ℝ} (hkappa : 2 ≤ kappa)
    (heta : 0 < eta) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T))
    (hcomp : ContDiff ℝ ∞
      (kappaEightCompensatedPair eta kappa (hardFrontierMap eta L)))
    (hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa
          (hardFrontierMap eta L)) p‖ ≤ 1 / (2 * kappa))
    (v : AmplifierAux) (muGAct Ly : ℝ)
    (hmuGAct : KappaEightIsSharpLowerHessianModulus
      (fun (x : E) (p : E × AmplifierAux) ↦
        kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
          x p.1 p.2) muGAct)
    (hLy : KappaEightIsSharpLowerHessianUpperBound
      (fun (x : E) (p : E × AmplifierAux) ↦
        kappaEightPopulationLower kappa eta (hardFrontierMap eta L)
          x p.1 p.2) Ly) :
    kappa ≤ Ly / muGAct ∧ Ly / muGAct ≤ 14 * kappa := by
  exact kappaEight_condition_number_comparison_of_flat_point
    (show 1 ≤ kappa by linarith) (hardFrontierMap eta L)
    hcomp hcomp2 (0 : E) (fullProgressWitness eta J, v)
    (iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_at_fullProgress
      heta hT L J hJ hLJ v) muGAct Ly hmuGAct hLy

/-- Direct bridge from the paper-level intrinsic condition-data structure to
the analytic sharp-modulus theorem.  A hard-problem constructor only needs to
provide the displayed equality for its population lower objective. -/
theorem KappaEightLowerConditionData.condition_number_comparison_of_lower_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {kappa eta : ℝ} (hkappa : 1 ≤ kappa) (theta : E → ℝ)
    (hcomp : ContDiff ℝ ∞ (kappaEightCompensatedPair eta kappa theta))
    (hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤
          1 / (2 * kappa))
    (x0 : E) (p0 : E × AmplifierAux)
    (hflat : iteratedFDeriv ℝ 2
      (kappaEightCompensatedPair eta kappa theta) p0 = 0)
    {P : KappaEightPopulationProblem E}
    (data : KappaEightLowerConditionData P)
    (hlower : (fun x y ↦ P.lower (x, y)) =
      fun (x : E) (p : E × AmplifierAux) ↦
        kappaEightPopulationLower kappa eta theta x p.1 p.2) :
    kappa ≤ data.kappaY ∧ data.kappaY ≤ 14 * kappa := by
  have hmuGAct := data.muGAct_sharp
  have hLy := data.Ly_sharp
  rw [hlower] at hmuGAct hLy
  simpa only [KappaEightLowerConditionData.kappaY] using
    kappaEight_condition_number_comparison_of_flat_point
      hkappa theta hcomp hcomp2 x0 p0 hflat
        data.muGAct data.Ly hmuGAct hLy

end

end BilevelLowerBound
