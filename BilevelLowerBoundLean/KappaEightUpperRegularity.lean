/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPaperHardInstance
import BilevelLowerBoundLean.HardObjectiveRegularity
import BilevelLowerBoundLean.PaperHardInstance

/-!
# Upper-objective regularity for the amplified hard pair

The new upper objective reads the second amplifier coordinate linearly.
Consequently this readout contributes one to the lower-variable first
derivative bound and zero to the Hessian.  The visible-chain and pseudo-Huber
components reuse the already verified dimension-free estimates.
-/

open Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

def kappaEightFullV2Projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × (E × AmplifierAux)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp kappaEightFullAuxProjection

@[simp] theorem kappaEightFullV2Projection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E × (E × AmplifierAux)) :
    kappaEightFullV2Projection p = p.2.2.2 := rfl

theorem norm_kappaEightFullV2Projection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightFullV2Projection :
      (E × (E × AmplifierAux)) →L[ℝ] ℝ)‖ ≤ 1 := by
  calc
    ‖(kappaEightFullV2Projection :
        (E × (E × AmplifierAux)) →L[ℝ] ℝ)‖ ≤
        ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ *
          ‖(kappaEightFullAuxProjection :
            (E × (E × AmplifierAux)) →L[ℝ] AmplifierAux)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      (norm_kappaEightFullAuxProjection_le_one (E := E))
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

def kappaEightLowerV2Projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    KappaEightLowerPoint E →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ E AmplifierAux)

@[simp] theorem kappaEightLowerV2Projection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : KappaEightLowerPoint E) :
    kappaEightLowerV2Projection p = p.2.2 := rfl

theorem norm_kappaEightLowerV2Projection_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖(kappaEightLowerV2Projection : KappaEightLowerPoint E →L[ℝ] ℝ)‖ ≤ 1 := by
  calc
    ‖(kappaEightLowerV2Projection : KappaEightLowerPoint E →L[ℝ] ℝ)‖ ≤
        ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ *
          ‖ContinuousLinearMap.snd ℝ E AmplifierAux‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      (ContinuousLinearMap.norm_snd_le ℝ E AmplifierAux)
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

def kappaEightFullHardVisible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta : ℝ) (L : E →L[ℝ] ChainVector T) :
    KappaEightQueryPoint E → ℝ :=
  (hardVisibleMap eta L) ∘ kappaEightFullZProjection

def kappaEightFullLinearReadout
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    KappaEightQueryPoint E → ℝ :=
  kappaEightFullV2Projection

def kappaEightFullPseudoHuber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam R : ℝ) : KappaEightQueryPoint E → ℝ :=
  (pseudoHuber lam R) ∘ kappaEightFullZProjection

theorem kappaEightFullHardUpper_eq_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta lam : ℝ) (L : E →L[ℝ] ChainVector T) :
    kappaEightFullHardUpper eta lam (hardRadius eta T) L =
      upperPopulationSum (kappaEightFullHardVisible eta L)
        kappaEightFullLinearReadout
        (kappaEightFullPseudoHuber lam (hardRadius eta T)) := by
  funext p
  rfl

theorem kappaEightFullHardUpper_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (lam : ℝ) (L : E →L[ℝ] ChainVector T) :
    ContDiff ℝ ∞
      (kappaEightFullHardUpper eta lam (hardRadius eta T) L) := by
  rw [kappaEightFullHardUpper_eq_sum]
  exact upperPopulationSum_contDiff
    ((hardVisibleMap_contDiff heta hT L).comp
      (kappaEightFullZProjection (E := E)).contDiff)
    (kappaEightFullV2Projection (E := E)).contDiff
    ((pseudoHuber_contDiff (hardRadius_pos heta hT).ne').comp
      (kappaEightFullZProjection (E := E)).contDiff)

theorem iteratedFDeriv_kappaEightFullLinearReadout_two_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : KappaEightQueryPoint E) :
    iteratedFDeriv ℝ 2
      (kappaEightFullLinearReadout : KappaEightQueryPoint E → ℝ) p = 0 := by
  let L : KappaEightQueryPoint E →L[ℝ] ℝ := kappaEightFullV2Projection
  have hfun : (kappaEightFullLinearReadout : KappaEightQueryPoint E → ℝ) = L := by
    rfl
  rw [hfun]
  ext m
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fun y : KappaEightQueryPoint E ↦
    fderiv ℝ (L : KappaEightQueryPoint E → ℝ) y) p) (m 0)) (m 1) = 0
  have hf : (fun y : KappaEightQueryPoint E ↦
      fderiv ℝ (L : KappaEightQueryPoint E → ℝ) y) = fun _ ↦ L := by
    funext y
    exact L.fderiv
  rw [hf]
  simp

set_option maxHeartbeats 900000 in
-- The quantified wrapper combines all three upper components.
/-- Uniform Hessian and gradient-Lipschitz bounds for the amplified upper
objective.  The linear readout contributes zero to both bounds. -/
theorem exists_kappaEightFullHardUpper_second_regularities :
    ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta lam : ℝ}, 0 < eta → 0 < T → 0 ≤ lam →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ p : KappaEightQueryPoint E,
          ‖iteratedFDeriv ℝ 2
            (kappaEightFullHardUpper eta lam (hardRadius eta T) L) p‖ ≤
              Ca + lam) ∧
        (∀ p q : KappaEightQueryPoint E,
          ‖fderiv ℝ
                (kappaEightFullHardUpper eta lam (hardRadius eta T) L) q -
              fderiv ℝ
                (kappaEightFullHardUpper eta lam (hardRadius eta T) L) p‖ ≤
            (Ca + lam) * ‖q - p‖) := by
  obtain ⟨Ca, hCa, hvisible⟩ := exists_visible_hidden_composition_scales
  refine ⟨Ca, hCa, ?_⟩
  intro E _ _ T eta lam heta hT hlam L hL
  let A : KappaEightQueryPoint E → ℝ := kappaEightFullHardVisible eta L
  let B : KappaEightQueryPoint E → ℝ := kappaEightFullLinearReadout
  let C : KappaEightQueryPoint E → ℝ :=
    kappaEightFullPseudoHuber lam (hardRadius eta T)
  have hA : ContDiff ℝ ∞ A :=
    (hardVisibleMap_contDiff heta hT L).comp
      (kappaEightFullZProjection (E := E)).contDiff
  have hB : ContDiff ℝ ∞ B :=
    (kappaEightFullV2Projection (E := E)).contDiff
  have hC : ContDiff ℝ ∞ C :=
    (pseudoHuber_contDiff (hardRadius_pos heta hT).ne').comp
      (kappaEightFullZProjection (E := E)).contDiff
  have hAB (p : KappaEightQueryPoint E) :
      ‖iteratedFDeriv ℝ 2 A p‖ ≤ Ca :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (hardVisibleMap_contDiff heta hT L)
      (kappaEightFullZProjection (E := E))
      (norm_kappaEightFullZProjection_le_one (E := E)) 2 p).trans
        (hvisible heta hT hL p.2.1).2.1
  have hBB (p : KappaEightQueryPoint E) :
      ‖iteratedFDeriv ℝ 2 B p‖ ≤ 0 := by
    rw [show B = (kappaEightFullLinearReadout :
      KappaEightQueryPoint E → ℝ) by rfl,
      iteratedFDeriv_kappaEightFullLinearReadout_two_eq_zero, norm_zero]
  have hCB (p : KappaEightQueryPoint E) :
      ‖iteratedFDeriv ℝ 2 C p‖ ≤ lam :=
    (norm_iteratedFDeriv_comp_clm_le_of_bound
      (pseudoHuber_contDiff (hardRadius_pos heta hT).ne')
      (kappaEightFullZProjection (E := E))
      (norm_kappaEightFullZProjection_le_one (E := E)) 2 p).trans
        (norm_iteratedFDeriv_pseudoHuber_two_le hlam
          (hardRadius_pos heta hT) p.2.1)
  rw [kappaEightFullHardUpper_eq_sum]
  exact ⟨by simpa [A, B, C] using
      upperPopulationSum_second_bound hA hB hC hAB hBB hCB,
    by simpa [A, B, C] using
      upperPopulationSum_gradient_lipschitz hA hB hC hAB hBB hCB⟩

/-- The lower-variable derivative of the upper objective is uniformly
bounded by the visible-chain scale, one linear readout, and the pseudo-Huber
radius contribution. -/
theorem exists_kappaEightFullHardUpper_lowerDerivative_bound :
    ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta lam : ℝ},
        0 < eta → 0 < T → 0 ≤ lam →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ x : E, ∀ y : KappaEightLowerPoint E,
        ‖fderiv ℝ
          (fun u : KappaEightLowerPoint E ↦
            kappaEightFullHardUpper eta lam (hardRadius eta T) L (x, u)) y‖ ≤
          Ca * eta * Real.sqrt T + 1 + lam * hardRadius eta T := by
  obtain ⟨Ca, hCa, hvisible⟩ := exists_visible_hidden_composition_scales
  refine ⟨Ca, hCa, ?_⟩
  intro E _ _ T eta lam heta hT hlam L hL x y
  let Lz : KappaEightLowerPoint E →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Lv : KappaEightLowerPoint E →L[ℝ] ℝ :=
    kappaEightLowerV2Projection
  let A : KappaEightLowerPoint E → ℝ := hardVisibleMap eta L ∘ Lz
  let B : KappaEightLowerPoint E → ℝ := Lv
  let C : KappaEightLowerPoint E → ℝ :=
    (pseudoHuber lam (hardRadius eta T)) ∘ Lz
  have hA : ContDiff ℝ ∞ A :=
    (hardVisibleMap_contDiff heta hT L).comp Lz.contDiff
  have hB : ContDiff ℝ ∞ B := Lv.contDiff
  have hC : ContDiff ℝ ∞ C :=
    (pseudoHuber_contDiff (hardRadius_pos heta hT).ne').comp Lz.contDiff
  have hfun :
      (fun u : KappaEightLowerPoint E ↦
        kappaEightFullHardUpper eta lam (hardRadius eta T) L (x, u)) =
        fun u ↦ A u + B u + C u := by
    funext u
    rfl
  have hAderiv : ‖fderiv ℝ A y‖ ≤ Ca * eta * Real.sqrt T := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      (hardVisibleMap_contDiff heta hT L) Lz
      (ContinuousLinearMap.norm_fst_le ℝ E AmplifierAux) 1 y
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (hvisible heta hT hL y.1).1
  have hBderiv : ‖fderiv ℝ B y‖ ≤ 1 := by
    change ‖fderiv ℝ (Lv : KappaEightLowerPoint E → ℝ) y‖ ≤ 1
    rw [Lv.fderiv]
    exact norm_kappaEightLowerV2Projection_le_one (E := E)
  have hCderiv : ‖fderiv ℝ C y‖ ≤ lam * hardRadius eta T := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      (pseudoHuber_contDiff (lam := lam) (hardRadius_pos heta hT).ne') Lz
      (ContinuousLinearMap.norm_fst_le ℝ E AmplifierAux) 1 y
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (by
      simpa [Lz, norm_iteratedFDeriv_one] using
        norm_fderiv_pseudoHuber_le hlam (hardRadius_pos heta hT) y.1)
  rw [hfun]
  change ‖fderiv ℝ (A + B + C) y‖ ≤ _
  have hsumDeriv :
      fderiv ℝ (A + B + C) y =
        fderiv ℝ A y + fderiv ℝ B y + fderiv ℝ C y := by
    have hAat := (hA.differentiable (by simp) y).hasFDerivAt
    have hBat := (hB.differentiable (by simp) y).hasFDerivAt
    have hCat := (hC.differentiable (by simp) y).hasFDerivAt
    simpa only [Pi.add_apply] using ((hAat.add hBat).add hCat).fderiv
  rw [hsumDeriv]
  have hABnorm :
      ‖fderiv ℝ A y + fderiv ℝ B y‖ ≤
        ‖fderiv ℝ A y‖ + ‖fderiv ℝ B y‖ :=
    norm_add_le (fderiv ℝ A y) (fderiv ℝ B y)
  have hABCnorm :
      ‖(fderiv ℝ A y + fderiv ℝ B y) + fderiv ℝ C y‖ ≤
        ‖fderiv ℝ A y + fderiv ℝ B y‖ + ‖fderiv ℝ C y‖ :=
    norm_add_le (fderiv ℝ A y + fderiv ℝ B y) (fderiv ℝ C y)
  calc
    ‖fderiv ℝ A y + fderiv ℝ B y + fderiv ℝ C y‖ ≤
        ‖fderiv ℝ A y + fderiv ℝ B y‖ + ‖fderiv ℝ C y‖ :=
      hABCnorm
    _ ≤ (‖fderiv ℝ A y‖ + ‖fderiv ℝ B y‖) + ‖fderiv ℝ C y‖ :=
      add_le_add hABnorm (le_refl _)
    _ ≤ Ca * eta * Real.sqrt T + 1 + lam * hardRadius eta T :=
      add_le_add (add_le_add hAderiv hBderiv) hCderiv

end

end BilevelLowerBound
