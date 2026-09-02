/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPopulationClass
import BilevelLowerBoundLean.KappaEightPaperOracle

/-!
# Simultaneous population, oracle, and intrinsic-condition certificates

One choice of universal constants certifies the same amplified hard pair as a
population problem, an admissible fresh SFO, and a problem whose actual lower
condition number lies between `kappa` and `14 * kappa`.
-/

namespace BilevelLowerBound

noncomputable section

set_option maxHeartbeats 1800000 in
-- This wrapper synchronizes three independently quantified certificate families.
theorem exists_simultaneous_kappaEight_hard_certificates :
    ∃ Ctheta CHess Cthird Ca Cvar : ℝ,
      0 ≤ Ctheta ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧ 0 ≤ Ca ∧ 0 < Cvar ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa Delta sigma : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 2 ≤ kappa) → (hT : 0 < T) →
        (hsigma : 0 ≤ sigma) →
        (hthetaSmall : 3 * Ctheta * eta ≤ 1) →
        (hHessSmall : CHess * eta ≤ 1 / 2) →
        (hgap : populationChainGapConstant * eta ^ 2 * T ≤ Delta) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ hsmall : ∀ x : E,
            |amplifierDiag kappa * attenuatedFrontier kappa
              (hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x))| ≤
              eta,
          let P := kappaEightPaperPopulationProblem eta kappa J heta
            (by linarith) hsmall
          let O := kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
            heta (by linarith) hsmall
          KappaEightPopulationClassMember P
              (Ca + 1 / 4)
              (kappaEightUniversalLowerGradientConstant CHess)
              Cthird
              (Ca * eta * Real.sqrt T + 1 +
                (1 / 4) * hardRadius eta T)
              (1 / (2 * kappa)) Delta ∧
            KappaEightBernoulliSFOMember O sigma ∧
            ∃ data : KappaEightLowerConditionData P,
              kappa ≤ data.kappaY ∧ data.kappaY ≤ 14 * kappa := by
  obtain ⟨Ctheta, CHessPop, Cthird, Ca, hCtheta, hCHessPop,
      hCthird, hCa, hpopulation⟩ :=
    exists_kappaEightPaperPopulationClassMember
  obtain ⟨CHessSharp, hCHessSharp, hsharp⟩ :=
    exists_kappaEightFrame_sharp_lower_constants
  obtain ⟨Cvar, hCvar, horacle⟩ :=
    exists_kappaEightPaperHardBernoulliSFOMember
  let CHess := max CHessPop CHessSharp
  refine ⟨Ctheta, CHess, Cthird, Ca, Cvar, hCtheta,
    hCHessPop.trans (le_max_left _ _), hCthird, hCa, hCvar, ?_⟩
  intro E _ _ _ T eta kappa Delta sigma heta hetaOne hkappa hT
    hsigma hthetaSmall hHessSmall hgap J
  have hHessPopSmall : CHessPop * eta ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right
      (le_max_left CHessPop CHessSharp) heta.le).trans hHessSmall
  have hHessSharpSmall : CHessSharp * eta ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right
      (le_max_right CHessPop CHessSharp) heta.le).trans hHessSmall
  obtain ⟨hsmall, hpopRaw⟩ := hpopulation heta hetaOne hkappa hT
    hthetaSmall hHessPopSmall hgap J
  let P := kappaEightPaperPopulationProblem eta kappa J heta
    (by linarith) hsmall
  let O := kappaEightPaperHardBernoulliSFO Cvar eta kappa sigma J
    heta (by linarith) hsmall
  have hpop : KappaEightPopulationClassMember P
      (Ca + 1 / 4) (kappaEightUniversalLowerGradientConstant CHess)
      Cthird
      (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
      (1 / (2 * kappa)) Delta := by
    apply hpopRaw.mono le_rfl _ le_rfl le_rfl le_rfl le_rfl
    unfold kappaEightUniversalLowerGradientConstant
    simpa [CHess, add_comm] using
      add_le_add_left (le_max_left CHessPop CHessSharp) 8
  have hO : KappaEightBernoulliSFOMember O sigma := by
    simpa [O, P] using
      (horacle heta hetaOne hkappa hT hsigma J hsmall).1
  obtain ⟨muGAct, Ly, hmuGAct, hLy, hcondLower, hcondUpper⟩ :=
    hsharp hkappa heta hetaOne hT J hHessSharpSmall
  have hmuGActP : KappaEightIsSharpLowerHessianModulus
      (fun x y ↦ P.lower (x, y)) muGAct := by
    simpa only [P, kappaEightPaperPopulationProblem,
      kappaEightFullPopulationLower_apply] using hmuGAct
  have hLyP : KappaEightIsSharpLowerHessianUpperBound
      (fun x y ↦ P.lower (x, y)) Ly := by
    simpa only [P, kappaEightPaperPopulationProblem,
      kappaEightFullPopulationLower_apply] using hLy
  let data : KappaEightLowerConditionData P :=
    { muGAct := muGAct
      Ly := Ly
      muGAct_pos := hmuGAct.1
      muGAct_sharp := hmuGActP
      Ly_sharp := hLyP }
  refine ⟨hsmall, hpop, hO, data, ?_, ?_⟩
  · simpa [data, KappaEightLowerConditionData.kappaY] using hcondLower
  · simpa [data, KappaEightLowerConditionData.kappaY] using hcondUpper

end

end BilevelLowerBound
