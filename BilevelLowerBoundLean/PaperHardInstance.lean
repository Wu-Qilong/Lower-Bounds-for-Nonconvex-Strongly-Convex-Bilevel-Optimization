/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperClasses
import BilevelLowerBoundLean.GapGradient
import BilevelLowerBoundLean.HardObjectiveRegularity

/-!
# The paper hard pair as one concrete population problem

This file closes a bookkeeping gap between the analytic files and the final
minimax statement.  The upper objective, lower objective, exact lower
solution, and hyper-objective are packaged into one object, and their defining
identities are proved rather than assumed.
-/

open Function MeasureTheory Set
open scoped ContDiff ENNReal MeasureTheory

namespace BilevelLowerBound

noncomputable section

/-- The exact lower solution used by the construction. -/
def paperHardLowerSolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta kappa : ℝ) (L : E →L[ℝ] ChainVector T) (x : E) :
    PaperLowerPoint E :=
  (kappa • x, hardFrontierMap eta L (kappa • x))

/-- The upper objective evaluated at the proposed lower solution is precisely
the rotated hard hyper-objective. -/
theorem fullHardUpper_at_paperHardLowerSolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {eta kappa : ℝ}
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (J : ChainVector T →ₗᵢ[ℝ] E)
    (hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta)
    (x : E) :
    fullHardUpper eta (1 / 4) (hardRadius eta T)
        (hiddenFrameTranspose J)
        (x, paperHardLowerSolution eta kappa (hiddenFrameTranspose J) x) =
      hardHyperObjective eta kappa J x := by
  rw [fullHardUpper_apply]
  simp only [paperHardLowerSolution]
  change hardUpper eta (1 / 4) (hardRadius eta T)
      (hiddenProbe (hardRadius eta T) (hiddenFrameTranspose J))
      (kappa • x)
      (frontierExtractor eta
        (hiddenProbe (hardRadius eta T) (hiddenFrameTranspose J)
          (kappa • x))) = hardHyperObjective eta kappa J x
  rw [hardUpper_at_proposed_solution heta
    (hiddenProbe (hardRadius eta T) (hiddenFrameTranspose J)) x
    hetaOne (hfrontier x)]
  rfl

/-- The concrete population problem used in the paper.  The only smallness
input is the already-proved uniform bound on the frontier value. -/
def paperHardPopulationProblem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hkappa : 0 < kappa)
    (hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta) :
    PaperPopulationProblem E where
  upper := fullHardUpper eta (1 / 4) (hardRadius eta T)
    (hiddenFrameTranspose J)
  lower := fullPopulationLower kappa eta (hiddenFrameTranspose J)
  lowerSolution := paperHardLowerSolution eta kappa (hiddenFrameTranspose J)
  hyperObjective := hardHyperObjective eta kappa J
  lowerSolution_minimizes := by
    intro x y
    rcases y with ⟨z, v⟩
    exact populationLower_minimum hkappa heta
      (hardFrontierMap eta (hiddenFrameTranspose J)) x z v (hfrontier x)
  lowerSolution_unique := by
    intro x y hmin
    rcases y with ⟨z, v⟩
    have hpair := populationLower_unique_minimizer hkappa heta
      (hardFrontierMap eta (hiddenFrameTranspose J)) x z v
      (hfrontier x) hmin
    rcases hpair with ⟨hz, hv⟩
    simp only [paperHardLowerSolution]
    exact Prod.ext hz hv
  hyperObjective_eq := by
    intro x
    symm
    exact fullHardUpper_at_paperHardLowerSolution
      heta hetaOne J hfrontier x

/-- The derivative estimates for the frontier imply the uniform value
smallness needed by the exact lower-solution proof. -/
theorem hardFrontierMap_le_eta_of_scale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta Ctheta : ℝ} (heta : 0 < eta)
    (hscale : Ctheta * eta ≤ 1)
    {L : E →L[ℝ] ChainVector T}
    (hvalue : ∀ z : E, |hardFrontierMap eta L z| ≤ Ctheta * eta ^ 2)
    (z : E) :
    |hardFrontierMap eta L z| ≤ eta := by
  calc
    |hardFrontierMap eta L z| ≤ Ctheta * eta ^ 2 := hvalue z
    _ = (Ctheta * eta) * eta := by ring
    _ ≤ 1 * eta := mul_le_mul_of_nonneg_right hscale heta.le
    _ = eta := one_mul eta

/-- There is one universal frontier constant for which every sufficiently
small scaled construction is a genuine population bilevel problem with the
claimed exact lower solution and hyper-objective. -/
theorem exists_paperHardPopulationProblem :
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa : ℝ},
        0 < eta → eta ≤ 1 → 0 < kappa → 0 < T →
        Ctheta * eta ≤ 1 →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ P : PaperPopulationProblem E,
          P.upper = fullHardUpper eta (1 / 4) (hardRadius eta T)
            (hiddenFrameTranspose J) ∧
          P.lower = fullPopulationLower kappa eta
            (hiddenFrameTranspose J) ∧
          P.lowerSolution =
            paperHardLowerSolution eta kappa (hiddenFrameTranspose J) ∧
          P.hyperObjective = hardHyperObjective eta kappa J := by
  obtain ⟨Ctheta, hCtheta, hbounds⟩ :=
    exists_frontier_hidden_composition_scales
  refine ⟨Ctheta, hCtheta, ?_⟩
  intro E _ _ _ T eta kappa heta hetaOne hkappa hT hscale J
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  have hvalue : ∀ z : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) z| ≤
        Ctheta * eta ^ 2 := by
    intro z
    exact (hbounds heta hT hL z).1
  have hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta := by
    intro x
    exact hardFrontierMap_le_eta_of_scale heta hscale hvalue _
  let P := paperHardPopulationProblem eta kappa J
    heta hetaOne hkappa hfrontier
  exact ⟨P, rfl, rfl, rfl, rfl⟩

/-! ## Membership in the paper's population class -/

/-- The explicit universal coefficient in the zero-chain gap estimate. -/
def populationChainGapConstant : ℝ :=
  4 * Real.exp 1 * phiBound

theorem hardHyperObjective_initial_gap_le_populationChainGapConstant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (eta kappa : ℝ)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    hardHyperObjective eta kappa J 0 -
        sInf (Set.range (hardHyperObjective eta kappa J)) ≤
      populationChainGapConstant * eta ^ 2 * T := by
  have hgap := hardHyperObjective_initial_gap eta kappa J
  unfold populationChainGapConstant
  calc
    hardHyperObjective eta kappa J 0 -
          sInf (Set.range (hardHyperObjective eta kappa J)) ≤
        eta ^ 2 * (2 * ((T : ℝ) * (2 * Real.exp 1 * phiBound))) := hgap
    _ = (4 * Real.exp 1 * phiBound) * eta ^ 2 * T := by ring

/-- The one-dimensional cutoff derivative has operator norm at most one. -/
theorem norm_fderiv_cutoffPrimitive_le_one (v : ℝ) :
    ‖fderiv ℝ cutoffPrimitive v‖ ≤ 1 := by
  rw [← toSpanSingleton_deriv, cutoffPrimitive_deriv]
  simpa [Real.norm_eq_abs] using abs_cutoffWeight_le_one v

/-- The pseudo-Huber first derivative is uniformly bounded by `lam * R`. -/
theorem norm_fderiv_pseudoHuber_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) (z : E) :
    ‖fderiv ℝ (pseudoHuber lam R : E → ℝ) z‖ ≤ lam * R := by
  rw [fderiv_pseudoHuber hR.ne', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hlam, innerSL_apply_norm]
  exact mul_le_mul_of_nonneg_left (norm_softProjection_le hR z) hlam

/-- Uniform bound on the derivative of the upper objective with respect to
the complete lower variable `(z,v)`.  This is the formal counterpart of the
paper's bounded-`nabla_y f` calculation. -/
theorem exists_fullHardUpper_lowerDerivative_bound :
    ∃ Ca : ℝ, 0 ≤ Ca ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {eta lam R : ℝ},
        0 < eta → 0 < T → 0 ≤ lam → 0 < R →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        ∀ x : E, ∀ y : PaperLowerPoint E,
        ‖fderiv ℝ
          (fun u : PaperLowerPoint E ↦ fullHardUpper eta lam R L (x, u))
          y‖ ≤ Ca * eta * Real.sqrt T + 1 + lam * R := by
  obtain ⟨Ca, hCa, hvisible⟩ := exists_visible_hidden_composition_scales
  refine ⟨Ca, hCa, ?_⟩
  intro E _ _ T eta lam R heta hT hlam hR L hL x y
  let Lz : PaperLowerPoint E →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E ℝ
  let Lv : PaperLowerPoint E →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ E ℝ
  let A : PaperLowerPoint E → ℝ := hardVisibleMap eta L ∘ Lz
  let B : PaperLowerPoint E → ℝ := cutoffPrimitive ∘ Lv
  let C : PaperLowerPoint E → ℝ := (pseudoHuber lam R) ∘ Lz
  have hA : ContDiff ℝ ∞ A :=
    (hardVisibleMap_contDiff heta hT L).comp Lz.contDiff
  have hB : ContDiff ℝ ∞ B := cutoffPrimitive_contDiff.comp Lv.contDiff
  have hC : ContDiff ℝ ∞ C := (pseudoHuber_contDiff hR.ne').comp Lz.contDiff
  have hfun :
      (fun u : PaperLowerPoint E ↦ fullHardUpper eta lam R L (x, u)) =
        fun u ↦ A u + B u + C u := by
    funext u
    rfl
  have hAderiv : ‖fderiv ℝ A y‖ ≤ Ca * eta * Real.sqrt T := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      (hardVisibleMap_contDiff heta hT L) Lz
      (ContinuousLinearMap.norm_fst_le ℝ E ℝ) 1 y
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (hvisible heta hT hL y.1).1
  have hBderiv : ‖fderiv ℝ B y‖ ≤ 1 := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      cutoffPrimitive_contDiff Lv
      (ContinuousLinearMap.norm_snd_le ℝ E ℝ) 1 y
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (by
      simpa [Lv, norm_iteratedFDeriv_one] using
        norm_fderiv_cutoffPrimitive_le_one y.2)
  have hCderiv : ‖fderiv ℝ C y‖ ≤ lam * R := by
    have hcomp := norm_iteratedFDeriv_comp_clm_le_of_bound
      (pseudoHuber_contDiff (lam := lam) hR.ne') Lz
      (ContinuousLinearMap.norm_fst_le ℝ E ℝ) 1 y
    rw [norm_iteratedFDeriv_one] at hcomp
    exact hcomp.trans (by
      simpa [Lz, norm_iteratedFDeriv_one] using
        norm_fderiv_pseudoHuber_le hlam hR y.1)
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
  calc
    ‖fderiv ℝ A y + fderiv ℝ B y + fderiv ℝ C y‖ ≤
        ‖fderiv ℝ A y‖ + ‖fderiv ℝ B y‖ + ‖fderiv ℝ C y‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Ca * eta * Real.sqrt T + 1 + lam * R :=
      add_le_add (add_le_add hAderiv hBderiv) hCderiv

set_option maxHeartbeats 1200000 in
/-- All analytic properties of the hard pair are collected in the exact
population-class predicate used by the final lower bound.  The displayed
constants are conservative universal bounds; no class property remains as an
unproved assumption. -/
theorem exists_paperHardPopulationClassMember :
    ∃ Ctheta CHess Cthird Ca Cell : ℝ,
      0 ≤ Ctheta ∧ 0 ≤ CHess ∧ 0 ≤ Cthird ∧ 0 ≤ Ca ∧ 0 ≤ Cell ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {eta kappa Delta : ℝ},
        (heta : 0 < eta) → (hetaOne : eta ≤ 1) →
        (hkappa : 1 ≤ kappa) → (hT : 0 < T) →
        (hthetaSmall : Ctheta * eta ≤ 1) →
        (hHessSmall : CHess * eta ≤ 1 / (2 * kappa)) →
        (hgap : populationChainGapConstant * eta ^ 2 * T ≤ Delta) →
        ∀ J : ChainVector T →ₗᵢ[ℝ] E,
        ∃ hfrontier : ∀ x : E,
            |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta,
          PaperPopulationClassMember
            (paperHardPopulationProblem eta kappa J
              heta hetaOne (lt_of_lt_of_le (by norm_num) hkappa)
              hfrontier)
            (Ca + Cell + 1 / 4)
            (5 + CHess * eta)
            Cthird
            (Ca * eta * Real.sqrt T + 1 + (1 / 4) * hardRadius eta T)
            (1 / (2 * kappa)) Delta := by
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨CHess, Cthird, hCHess, hCthird, hlower⟩ :=
    exists_fullPopulationLower_regularities
  obtain ⟨CHessSlice, hCHessSlice, hslice⟩ :=
    exists_hardLowerSlice_certificates
  obtain ⟨Ca, Cell, hCa, hCell, hupper⟩ :=
    exists_fullHardUpper_second_regularities
  obtain ⟨CaFirst, hCaFirst, hfirst⟩ :=
    exists_fullHardUpper_lowerDerivative_bound
  let Ctheta' := Ctheta
  let CHess' := max CHess CHessSlice
  let Cthird' := Cthird
  let Ca' := max Ca CaFirst
  let Cell' := Cell
  refine ⟨Ctheta', CHess', Cthird', Ca', Cell', hCtheta,
    hCHess.trans (le_max_left _ _), hCthird,
    hCa.trans (le_max_left _ _), hCell, ?_⟩
  intro E _ _ _ T eta kappa Delta heta hetaOne hkappa hT
    hthetaSmall hHessSmall hgap J
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  have hthetaRaw : ∀ z : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) z| ≤ Ctheta' * eta ^ 2 := by
    intro z
    exact (htheta heta hT hL z).1
  have hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta := by
    intro x
    exact hardFrontierMap_le_eta_of_scale heta hthetaSmall hthetaRaw _
  refine ⟨hfrontier, ?_⟩
  let P := paperHardPopulationProblem eta kappa J heta hetaOne
    (lt_of_lt_of_le (by norm_num) hkappa) hfrontier
  have hlowerHere := hlower hkappa heta hetaOne hT hL
  have hupperHere := hupper heta hT (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (hardRadius_pos heta hT) hL
  have hsliceSmall : CHessSlice * eta ≤ 1 / (2 * kappa) := by
    exact (mul_le_mul_of_nonneg_right (le_max_right CHess CHessSlice)
      heta.le).trans hHessSmall
  have hsliceHere := hslice hkappa heta hetaOne hT hL
  have hfirstHere := hfirst heta hT (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (hardRadius_pos heta hT) hL
  refine
    { upper_gradient_lipschitz := ?_
      lower_gradient_lipschitz := ?_
      lower_strongly_convex := ?_
      lower_hessian_lipschitz := ?_
      upper_lower_derivative_bounded := ?_
      hyper_bddBelow := ?_
      initial_gap := ?_ }
  · refine ⟨(contDiff_infty.mp (fullHardUpper_contDiff heta hT
      (hardRadius_pos heta hT).ne' (1 / 4) (hiddenFrameTranspose J))) 1, ?_⟩
    intro p q
    exact (hupperHere.2 p q).trans (mul_le_mul_of_nonneg_right
      (by dsimp [Ca', Cell']; linarith [le_max_left Ca CaFirst])
      (norm_nonneg (q - p)))
  · refine ⟨(contDiff_infty.mp (fullPopulationLower_contDiff heta hT kappa
      (hiddenFrameTranspose J))) 1, ?_⟩
    intro p q
    exact (hlowerHere.2.2.1 p q).trans (mul_le_mul_of_nonneg_right
      (by dsimp [CHess'];
          have hm := mul_le_mul_of_nonneg_right
            (le_max_left CHess CHessSlice) heta.le
          linarith)
      (norm_nonneg (q - p)))
  · intro x y w
    change (1 / (2 * kappa)) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2
        (hardLowerSlice kappa eta (hiddenFrameTranspose J) x) y
        (fun _ ↦ w)
    exact hsliceHere.2 hsliceSmall x y w
  · refine ⟨(contDiff_infty.mp (fullPopulationLower_contDiff heta hT kappa
      (hiddenFrameTranspose J))) 2, ?_⟩
    intro p q
    exact hlowerHere.2.2.2 p q
  · intro x y
    change ‖fderiv ℝ
      (fun u : PaperLowerPoint E ↦
        fullHardUpper eta (1 / 4) (hardRadius eta T)
          (hiddenFrameTranspose J) (x, u)) y‖ ≤ _
    exact (hfirstHere x y).trans (by
      dsimp [Ca']
      have hCaComp := le_max_right Ca CaFirst
      have hmul := mul_le_mul_of_nonneg_right hCaComp
        (mul_nonneg heta.le (Real.sqrt_nonneg T))
      linarith)
  · exact hardHyperObjective_range_bddBelow eta kappa J
  · exact (hardHyperObjective_initial_gap_le_populationChainGapConstant
      eta kappa J).trans hgap

end

end BilevelLowerBound
