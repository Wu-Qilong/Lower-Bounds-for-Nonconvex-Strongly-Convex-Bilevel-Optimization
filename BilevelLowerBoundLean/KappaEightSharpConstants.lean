/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightConditionWitness
import BilevelLowerBoundLean.SharpConstants

/-!
# Existence of the intrinsic lower condition number for the amplified pair

This file closes the order-completeness step that turns valid global Hessian
bounds into sharp constants.  It then applies the weak and strong amplifier
directions at the full-progress flat point to prove
`kappa <= kappaY <= 14 * kappa` for the actual population lower objective.
-/

open Function Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-- A positive largest lower-Hessian modulus exists from one positive valid
certificate and a finite upper bound on all valid certificates. -/
theorem exists_kappaEight_sharp_lower_hessian_modulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → KappaEightLowerPoint E → ℝ)
    (hexists : ∃ a, 0 < a ∧
      ∀ x p w, a * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w))
    (hbounded : ∃ U, ∀ a,
      (∀ x p w, a * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w)) → a ≤ U) :
    ∃ muGAct, KappaEightIsSharpLowerHessianModulus G muGAct := by
  obtain ⟨a, haPos, ha⟩ := hexists
  obtain ⟨muGAct, hmuGAct⟩ := exists_sharp_lower_hessian_modulus G
    ⟨a, ha⟩ hbounded
  refine ⟨muGAct, (haPos.trans_le (hmuGAct.2 a ha)),
    hmuGAct.1, hmuGAct.2⟩

/-- A nonnegative smallest Hessian upper bound exists from one finite valid
upper certificate and a nonnegative lower bound on all such certificates. -/
theorem exists_kappaEight_sharp_lower_hessian_upper_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → KappaEightLowerPoint E → ℝ)
    (hexists : ∃ a, ∀ x p, ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ a)
    (hbounded : ∃ L, 0 ≤ L ∧ ∀ a,
      (∀ x p, ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ a) → L ≤ a) :
    ∃ Ly, KappaEightIsSharpLowerHessianUpperBound G Ly := by
  obtain ⟨L, hL0, hL⟩ := hbounded
  obtain ⟨Ly, hLy⟩ := exists_sharp_lower_hessian_upper_bound G
    hexists ⟨L, hL⟩
  exact ⟨Ly, hL0.trans (hL Ly hLy.1), hLy.1, hLy.2⟩

set_option maxHeartbeats 1400000 in
-- This proof combines order completeness with both exact amplifier directions.
/-- The sharp constants of every rotated amplified lower problem exist and
their ratio is comparable to the construction parameter. -/
theorem exists_kappaEightFrame_sharp_lower_constants :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {kappa eta : ℝ},
        2 ≤ kappa → 0 < eta → eta ≤ 1 → 0 < T →
        ∀ (J : ChainVector T →ₗᵢ[ℝ] E),
        CHess * eta ≤ 1 / 2 →
        ∃ muGAct Ly : ℝ,
          KappaEightIsSharpLowerHessianModulus
            (fun (x : E) (p : E × AmplifierAux) ↦
              kappaEightPopulationLower kappa eta
                (hardFrontierMap eta (hiddenFrameTranspose J))
                x p.1 p.2) muGAct ∧
          KappaEightIsSharpLowerHessianUpperBound
            (fun (x : E) (p : E × AmplifierAux) ↦
              kappaEightPopulationLower kappa eta
                (hardFrontierMap eta (hiddenFrameTranspose J))
                x p.1 p.2) Ly ∧
          kappa ≤ Ly / muGAct ∧ Ly / muGAct ≤ 14 * kappa := by
  obtain ⟨_Cnoise, CHess, _Cthird, _hCnoise, hCHess, _hCthird, hreg⟩ :=
    exists_kappaEight_hard_compensated_pair_regularities
  refine ⟨CHess, hCHess, ?_⟩
  intro E _ _ _ T kappa eta hkappa heta hetaOne hT J hsmall
  let L : E →L[ℝ] ChainVector T := hiddenFrameTranspose J
  let theta : E → ℝ := hardFrontierMap eta L
  let G : E → E × AmplifierAux → ℝ :=
    fun x p ↦ kappaEightPopulationLower kappa eta theta x p.1 p.2
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hL : ‖L‖ ≤ 1 := by
    exact norm_hiddenFrameTranspose_le hT J
  have htheta : ContDiff ℝ ∞ theta := hardFrontierMap_contDiff heta hT L
  have hcomp : ContDiff ℝ ∞
      (kappaEightCompensatedPair eta kappa theta) :=
    kappaEightCompensatedPair_contDiff heta.ne' htheta
  have hraw (p : E × AmplifierAux) :=
    hreg heta hetaOne hkappa hT hL p
  have hcomp2 : ∀ p,
      ‖iteratedFDeriv ℝ 2
        (kappaEightCompensatedPair eta kappa theta) p‖ ≤
          1 / (2 * kappa) := by
    intro p
    calc
      ‖iteratedFDeriv ℝ 2
          (kappaEightCompensatedPair eta kappa theta) p‖ ≤
          CHess * eta / kappa := (hraw p).2.1
      _ ≤ (1 / 2) / kappa :=
        (div_le_div_iff_of_pos_right hkpos).2 hsmall
      _ = 1 / (2 * kappa) := by field_simp [hkpos.ne']
  have hmuValid : ∀ x p w,
      (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w) := by
    intro x p w
    exact kappaEightPopulationLower_strong_hessian
      (show 1 ≤ kappa by linarith) theta x hcomp hcomp2 p w
  have hLyValid : ∀ x p,
      ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ 7 := by
    intro x p
    have hbound := kappaEightPopulationLower_second_bound
      (show 1 ≤ kappa by linarith) theta x hcomp hcomp2 p
    have hinv : 1 / (2 * kappa) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2 * kappa)).2
      nlinarith
    exact hbound.trans (by linarith)
  have hmuCandidatesBounded : ∀ a,
      (∀ x p w, a * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w)) → a ≤ 7 := by
    intro a ha
    let w : E × AmplifierAux := kappaEightStrongDirection
    let p : E × AmplifierAux := (0, (0, 0))
    let H := iteratedFDeriv ℝ 2 (G (0 : E)) p
    have haw := ha (0 : E) p w
    have hwnorm : ‖w‖ = 1 := by simp [w]
    rw [hwnorm] at haw
    norm_num at haw
    have hop := H.le_opNorm (fun _ : Fin 2 ↦ w)
    rw [Fin.prod_univ_two, hwnorm, one_mul, mul_one] at hop
    calc
      a ≤ H (fun _ ↦ w) := haw
      _ ≤ ‖H (fun _ ↦ w)‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ ‖H‖ := hop
      _ ≤ 7 := hLyValid (0 : E) p
  obtain ⟨muGAct, hmuGAct⟩ :=
    exists_kappaEight_sharp_lower_hessian_modulus G
    ⟨1 / (2 * kappa), by positivity, hmuValid⟩
    ⟨7, hmuCandidatesBounded⟩
  have hLyCandidatesNonneg : ∀ a,
      (∀ x p, ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ a) → 0 ≤ a := by
    intro a ha
    exact (norm_nonneg
      (iteratedFDeriv ℝ 2 (G (0 : E)) (0 : E × AmplifierAux))).trans
        (ha (0 : E) (0 : E × AmplifierAux))
  obtain ⟨Ly, hLy⟩ := exists_kappaEight_sharp_lower_hessian_upper_bound G
    ⟨7, hLyValid⟩ ⟨0, le_rfl, hLyCandidatesNonneg⟩
  let p0 : E × AmplifierAux :=
    (fullProgressWitness eta J.toContinuousLinearMap, (0, 0))
  have hflat : iteratedFDeriv ℝ 2
      (kappaEightCompensatedPair eta kappa theta) p0 = 0 := by
    exact iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_at_fullProgress
      heta hT L J.toContinuousLinearMap J.norm_toContinuousLinearMap_le
      (hiddenFrameTranspose_comp_frame J) (0, 0)
  have hcomparison := kappaEight_condition_number_comparison_of_flat_point
    (show 1 ≤ kappa by linarith) theta hcomp hcomp2 (0 : E) p0 hflat
      muGAct Ly hmuGAct hLy
  exact ⟨muGAct, Ly, hmuGAct, hLy, hcomparison.1, hcomparison.2⟩

end

end BilevelLowerBound
