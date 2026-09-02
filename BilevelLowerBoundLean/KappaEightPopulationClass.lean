/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightUpperRegularity
import BilevelLowerBoundLean.KappaEightSharpConstants

/-!
# Population-class membership of the amplified hard pair

This module collects the complete joint-variable smoothness certificates,
the lower strong-convexity certificate, bounded upper lower-derivative, and
the hyper-objective gap into the exact amplified population class.
-/

open Function MeasureTheory Set
open scoped ContDiff ENNReal MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- Enlarging smoothness/gap budgets and decreasing the certified strong
convexity modulus preserves membership. -/
theorem KappaEightPopulationClassMember.mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : KappaEightPopulationProblem E}
    {Lf Lg rho Cf muG Delta Lf' Lg' rho' Cf' muG' Delta' : ℝ}
    (h : KappaEightPopulationClassMember P Lf Lg rho Cf muG Delta)
    (hLf : Lf ≤ Lf') (hLg : Lg ≤ Lg') (hrho : rho ≤ rho')
    (hCf : Cf ≤ Cf') (hmuG : muG' ≤ muG) (hDelta : Delta ≤ Delta') :
    KappaEightPopulationClassMember P Lf' Lg' rho' Cf' muG' Delta' := by
  refine
    { upper_gradient_lipschitz := ⟨h.upper_gradient_lipschitz.1, ?_⟩
      lower_gradient_lipschitz := ⟨h.lower_gradient_lipschitz.1, ?_⟩
      lower_strongly_convex := ?_
      lower_hessian_lipschitz := ⟨h.lower_hessian_lipschitz.1, ?_⟩
      upper_lower_derivative_bounded := ?_
      hyper_bddBelow := h.hyper_bddBelow
      initial_gap := h.initial_gap.trans hDelta }
  · intro x y
    exact h.upper_gradient_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hLf (norm_nonneg _))
  · intro x y
    exact h.lower_gradient_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hLg (norm_nonneg _))
  · intro x y w
    exact (mul_le_mul_of_nonneg_right hmuG (sq_nonneg ‖w‖)).trans
      (h.lower_strongly_convex x y w)
  · intro x y
    exact h.lower_hessian_lipschitz.2 x y |>.trans
      (mul_le_mul_of_nonneg_right hrho (norm_nonneg _))
  · intro x y
    exact (h.upper_lower_derivative_bounded x y).trans hCf

def kappaEightUniversalLowerGradientConstant (CHess : ℝ) : ℝ :=
  8 + CHess

def kappaEightGapUpperLowerDerivativeConstant
    (Ca CDelta Delta : ℝ) : ℝ :=
  1 + (Ca + 230 / 4) * Real.sqrt (Delta / CDelta)

/-- The chain-gap inequality eliminates the construction-dependent factor
`eta * sqrt T` from the final upper lower-derivative bound. -/
theorem KappaEightPopulationClassMember.to_final_uniform_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : KappaEightPopulationProblem E} {T : ℕ}
    {eta Delta CDelta Ca Lf Lg rho muG : ℝ}
    (hCDelta : 0 < CDelta) (heta : 0 ≤ eta)
    (hDelta : 0 ≤ Delta) (hCa : 0 ≤ Ca)
    (hgap : CDelta * eta ^ 2 * T ≤ Delta)
    (h : KappaEightPopulationClassMember P Lf Lg rho
      (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
      muG Delta) :
    KappaEightPopulationClassMember P Lf Lg rho
      (kappaEightGapUpperLowerDerivativeConstant Ca CDelta Delta)
      muG Delta := by
  have hscale : eta * Real.sqrt T ≤ Real.sqrt (Delta / CDelta) :=
    eta_mul_sqrt_le_sqrt_div_of_gap hCDelta heta hDelta hgap
  have hcoef : 0 ≤ Ca + 230 / 4 := by positivity
  have hCfScale := mul_le_mul_of_nonneg_left hscale hcoef
  have hCf :
      Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T ≤
        kappaEightGapUpperLowerDerivativeConstant Ca CDelta Delta := by
    unfold hardRadius kappaEightGapUpperLowerDerivativeConstant
    nlinarith
  exact h.mono le_rfl le_rfl le_rfl hCf le_rfl le_rfl

set_option maxHeartbeats 1800000 in
-- Multiple independent universal analytic certificates are synchronized here.
/-- Universal constants certify the full amplified population class for every
orthonormal hidden frame.  The Hessian-Lipschitz field is the full joint
`p=1` condition, not merely a lower-variable slice condition. -/
theorem exists_kappaEightPaperPopulationClassMember :
    ∃ Ctheta CHess Cthird Ca : ℝ,
      0 ≤ Ctheta ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧ 0 ≤ Ca ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa Delta : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 2 ≤ kappa) → (hT : 0 < T) →
        (hthetaSmall : 3 * Ctheta * eta ≤ 1) →
        (hHessSmall : CHess * eta ≤ 1 / 2) →
        (hgap : populationChainGapConstant * eta ^ 2 * T ≤ Delta) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ hsmall : ∀ x : E,
            |amplifierDiag kappa * attenuatedFrontier kappa
              (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤
              eta,
          KappaEightPopulationClassMember
            (kappaEightPaperPopulationProblem eta kappa J heta
              (by linarith) hsmall)
            (Ca + 1 / 4)
            (kappaEightUniversalLowerGradientConstant CHess)
            Cthird
            (Ca * eta * Real.sqrt T + 1 +
              (1 / 4) * hardRadius eta T)
            (1 / (2 * kappa)) Delta := by
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨CHessFull, CthirdFull, hCHessFull, hCthirdFull, hlowerFull⟩ :=
    exists_kappaEightFullPopulationLower_regularities
  obtain ⟨_Cnoise, CHessSlice, CthirdSlice, _hCnoise,
      hCHessSlice, hCthirdSlice, hlowerSlice⟩ :=
    exists_kappaEightPopulationLower_certificates
  obtain ⟨CaSecond, hCaSecond, hupperSecond⟩ :=
    exists_kappaEightFullHardUpper_second_regularities
  obtain ⟨CaFirst, hCaFirst, hupperFirst⟩ :=
    exists_kappaEightFullHardUpper_lowerDerivative_bound
  let CHess := max CHessFull CHessSlice
  let Cthird := max CthirdFull CthirdSlice
  let Ca := max CaSecond CaFirst
  refine ⟨Ctheta, CHess, Cthird, Ca, hCtheta,
    hCHessFull.trans (le_max_left _ _),
    hCthirdFull.trans (le_max_left _ _),
    hCaSecond.trans (le_max_left _ _), ?_⟩
  intro E _ _ _ T eta kappa Delta heta hetaOne hkappa hT
    hthetaSmall hHessSmall hgap J
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  have hthetaValue : ∀ z : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) z| ≤
        Ctheta * eta ^ 2 := by
    intro z
    exact (htheta heta hT hL z).1
  have hsmall : ∀ x : E,
      |amplifierDiag kappa * attenuatedFrontier kappa
        (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤ eta := by
    intro x
    exact kappaEightCandidateFirst_le_eta_of_scale heta hkappa hCtheta
      hthetaSmall hthetaValue _
  refine ⟨hsmall, ?_⟩
  let P := kappaEightPaperPopulationProblem eta kappa J heta
    (by linarith) hsmall
  have hfull := hlowerFull heta hetaOne hkappa hT hL
  have hslice := hlowerSlice heta hetaOne hkappa hT hL
  have hupper := hupperSecond heta hT (by norm_num : 0 ≤ (1 / 4 : ℝ)) hL
  have hfirst := hupperFirst heta hT (by norm_num : 0 ≤ (1 / 4 : ℝ)) hL
  have hsliceSmall : CHessSlice * eta ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right
      (le_max_right CHessFull CHessSlice) heta.le).trans hHessSmall
  refine
    { upper_gradient_lipschitz := ?_
      lower_gradient_lipschitz := ?_
      lower_strongly_convex := ?_
      lower_hessian_lipschitz := ?_
      upper_lower_derivative_bounded := ?_
      hyper_bddBelow := ?_
      initial_gap := ?_ }
  · refine ⟨(contDiff_infty.mp (kappaEightFullHardUpper_contDiff heta hT
      (1 / 4) (hiddenFrameTranspose J))) 1, ?_⟩
    intro p q
    exact (hupper.2 p q).trans (mul_le_mul_of_nonneg_right
      (by dsimp [Ca]; linarith [le_max_left CaSecond CaFirst])
      (norm_nonneg (q - p)))
  · refine ⟨(contDiff_infty.mp (kappaEightFullPopulationLower_contDiff
      heta hT kappa (hiddenFrameTranspose J))) 1, ?_⟩
    intro p q
    exact (hfull.2.2.1 p q).trans (mul_le_mul_of_nonneg_right
      (by
        dsimp [kappaEightUniversalLowerGradientConstant, CHess]
        have hdiv : CHessFull * eta / kappa ≤ CHessFull * eta :=
          div_le_self (mul_nonneg hCHessFull heta.le)
            (show 1 ≤ kappa by linarith)
        have hetaMul : CHessFull * eta ≤ CHessFull :=
          mul_le_of_le_one_right hCHessFull hetaOne
        simpa [add_comm] using add_le_add_left
          ((hdiv.trans hetaMul).trans
            (le_max_left CHessFull CHessSlice)) 8)
      (norm_nonneg (q - p)))
  · intro x y w
    simpa only [P, kappaEightPaperPopulationProblem,
      kappaEightFullPopulationLower_apply] using
        hslice.2.2.2.1 hsliceSmall x y w
  · refine ⟨(contDiff_infty.mp (kappaEightFullPopulationLower_contDiff
      heta hT kappa (hiddenFrameTranspose J))) 2, ?_⟩
    intro p q
    exact (hfull.2.2.2 p q).trans (mul_le_mul_of_nonneg_right
      (by
        dsimp [Cthird]
        have hle : CthirdFull / kappa ≤ CthirdFull :=
          div_le_self hCthirdFull (show 1 ≤ kappa by linarith)
        exact hle.trans (le_max_left CthirdFull CthirdSlice))
      (norm_nonneg (q - p)))
  · intro x y
    change ‖fderiv ℝ
      (fun u : KappaEightLowerPoint E ↦
        kappaEightFullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J) (x, u)) y‖ ≤ _
    exact (hfirst x y).trans (by
      dsimp [Ca]
      have hCaComp := le_max_right CaSecond CaFirst
      have hmul := mul_le_mul_of_nonneg_right hCaComp
        (mul_nonneg heta.le (Real.sqrt_nonneg T))
      linarith)
  · exact hardHyperObjective_range_bddBelow eta kappa J
  · exact (hardHyperObjective_initial_gap_le_populationChainGapConstant
      eta kappa J).trans hgap

end

end BilevelLowerBound
