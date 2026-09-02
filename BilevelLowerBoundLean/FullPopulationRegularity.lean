/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PopulationRegularity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Population-regularity aggregation

The preceding modules establish the quantitative derivative estimates for the
scaled chain, the hidden soft projection, and the compensated frontier block.
This file verifies the deterministic aggregation step used by the population
regularity lemma:

* componentwise Hessian bounds add to a full-objective Hessian bound;
* a uniform Hessian bound implies a globally Lipschitz gradient;
* componentwise third-derivative bounds add to a full third-derivative bound;
* a uniform third-derivative bound implies a globally Lipschitz Hessian;
* a coercive base Hessian remains coercive under a small operator-norm
  perturbation;
* the resulting lower condition number is within a universal factor of the
  construction parameter `kappa`, once the sharp upper/lower witnesses are
  supplied.

The aggregation theorems deliberately expose their component estimates as
hypotheses.  In particular, this module does not silently identify Mathlib's
sup norm on ordinary products with the Euclidean product norm used in the
paper.  Their explicit dimension-free equivalence is proved below.
-/

open Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Uniform derivative bounds imply Lipschitz regularity -/

theorem fderiv_lipschitz_of_second_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    (x y : E) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦
      ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) z)
    (fun z _hz ↦ ?_) (mem_univ x) (mem_univ y)
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hC z

theorem hessian_lipschitz_of_third_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ C)
    (x y : E) :
    ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤
      C * ‖y - x‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦
      (hf.differentiable_iteratedFDeriv (m := 2)
        (show (2 : ℕ∞ω) < (∞ : ℕ∞ω) from
          WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))) z)
    (fun z _hz ↦ ?_) (mem_univ x) (mem_univ y)
  rw [norm_fderiv_iteratedFDeriv]
  exact hC z

/-! ## Norm convention on product spaces -/

/-- Mathlib's sup norm on an ordinary product and the Euclidean product norm
are equivalent with the dimension-free factor `sqrt 2`. -/
theorem max_sqrt_sum_sq_equivalence {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ Real.sqrt (a ^ 2 + b ^ 2) ∧
      Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt 2 * max a b := by
  have hsum : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hmax : 0 ≤ max a b := ha.trans (le_max_left a b)
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · apply (sq_le_sq₀ hmax (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt hsum]
    rcases max_cases a b with hab | hba
    · rw [hab.1]
      nlinarith [sq_nonneg b]
    · rw [hba.1]
      nlinarith [sq_nonneg a]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hsqrt2 hmax)).1
    rw [Real.sq_sqrt hsum, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rcases max_cases a b with hab | hba
    · rw [hab.1]
      nlinarith [sq_nonneg (a - b)]
    · rw [hba.1]
      nlinarith [sq_nonneg (a - b)]

/-! ## Addition of component derivative bounds -/

theorem norm_iteratedFDeriv_add_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : E) {F G : ℝ}
    (hfB : ‖iteratedFDeriv ℝ n f x‖ ≤ F)
    (hgB : ‖iteratedFDeriv ℝ n g x‖ ≤ G) :
    ‖iteratedFDeriv ℝ n (f + g) x‖ ≤ F + G := by
  have hfAt : ContDiffAt ℝ n f x :=
    (hf.of_le (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hgAt : ContDiffAt ℝ n g x :=
    (hg.of_le (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  calc
    ‖iteratedFDeriv ℝ n (f + g) x‖ =
        ‖iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n g x‖ := by
      rw [iteratedFDeriv_add_apply hfAt hgAt]
    _ ≤ ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ :=
      norm_add_le _ _
    _ ≤ F + G := add_le_add hfB hgB

theorem norm_iteratedFDeriv_three_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (n : ℕ) (x : E) {F G H : ℝ}
    (hfB : ‖iteratedFDeriv ℝ n f x‖ ≤ F)
    (hgB : ‖iteratedFDeriv ℝ n g x‖ ≤ G)
    (hhB : ‖iteratedFDeriv ℝ n h x‖ ≤ H) :
    ‖iteratedFDeriv ℝ n ((f + g) + h) x‖ ≤ F + G + H := by
  exact norm_iteratedFDeriv_add_le (hf.add hg) hh n x
    (norm_iteratedFDeriv_add_le hf hg n x hfB hgB) hhB

/-! ## Full upper population objective -/

def upperPopulationSum {E : Type*} (A ell hub : E → ℝ) : E → ℝ :=
  (A + ell) + hub

theorem upperPopulationSum_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A ell hub : E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hell : ContDiff ℝ ∞ ell)
    (hhub : ContDiff ℝ ∞ hub) :
    ContDiff ℝ ∞ (upperPopulationSum A ell hub) := by
  exact (hA.add hell).add hhub

theorem upperPopulationSum_second_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A ell hub : E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hell : ContDiff ℝ ∞ ell)
    (hhub : ContDiff ℝ ∞ hub)
    {CA Cell Chub : ℝ}
    (hAB : ∀ x, ‖iteratedFDeriv ℝ 2 A x‖ ≤ CA)
    (hellB : ∀ x, ‖iteratedFDeriv ℝ 2 ell x‖ ≤ Cell)
    (hhubB : ∀ x, ‖iteratedFDeriv ℝ 2 hub x‖ ≤ Chub)
    (x : E) :
    ‖iteratedFDeriv ℝ 2 (upperPopulationSum A ell hub) x‖ ≤
      CA + Cell + Chub := by
  exact norm_iteratedFDeriv_three_sum_le hA hell hhub 2 x
    (hAB x) (hellB x) (hhubB x)

theorem upperPopulationSum_gradient_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A ell hub : E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hell : ContDiff ℝ ∞ ell)
    (hhub : ContDiff ℝ ∞ hub)
    {CA Cell Chub : ℝ}
    (hAB : ∀ x, ‖iteratedFDeriv ℝ 2 A x‖ ≤ CA)
    (hellB : ∀ x, ‖iteratedFDeriv ℝ 2 ell x‖ ≤ Cell)
    (hhubB : ∀ x, ‖iteratedFDeriv ℝ 2 hub x‖ ≤ Chub)
    (x y : E) :
    ‖fderiv ℝ (upperPopulationSum A ell hub) y -
        fderiv ℝ (upperPopulationSum A ell hub) x‖ ≤
      (CA + Cell + Chub) * ‖y - x‖ := by
  exact fderiv_lipschitz_of_second_bound
    (upperPopulationSum_contDiff hA hell hhub)
    (upperPopulationSum_second_bound hA hell hhub hAB hellB hhubB) x y

/-! ## Full lower population objective -/

def lowerPopulationSum {E : Type*} (base perturbation : E → ℝ) : E → ℝ :=
  base + perturbation

theorem lowerPopulationSum_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation) :
    ContDiff ℝ ∞ (lowerPopulationSum base perturbation) :=
  hbase.add hpert

theorem lowerPopulationSum_second_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation)
    {Cbase Cpert : ℝ}
    (hbaseB : ∀ x, ‖iteratedFDeriv ℝ 2 base x‖ ≤ Cbase)
    (hpertB : ∀ x, ‖iteratedFDeriv ℝ 2 perturbation x‖ ≤ Cpert)
    (x : E) :
    ‖iteratedFDeriv ℝ 2 (lowerPopulationSum base perturbation) x‖ ≤
      Cbase + Cpert := by
  exact norm_iteratedFDeriv_add_le hbase hpert 2 x (hbaseB x) (hpertB x)

theorem lowerPopulationSum_third_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation)
    {Cpert : ℝ}
    (hbaseZero : ∀ x, iteratedFDeriv ℝ 3 base x = 0)
    (hpertB : ∀ x, ‖iteratedFDeriv ℝ 3 perturbation x‖ ≤ Cpert)
    (x : E) :
    ‖iteratedFDeriv ℝ 3 (lowerPopulationSum base perturbation) x‖ ≤
      Cpert := by
  unfold lowerPopulationSum
  have h := norm_iteratedFDeriv_add_le hbase hpert 3 x
    (show ‖iteratedFDeriv ℝ 3 base x‖ ≤ 0 by simp [hbaseZero x])
    (hpertB x)
  simpa using h

theorem lowerPopulationSum_gradient_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation)
    {Cbase Cpert : ℝ}
    (hbaseB : ∀ x, ‖iteratedFDeriv ℝ 2 base x‖ ≤ Cbase)
    (hpertB : ∀ x, ‖iteratedFDeriv ℝ 2 perturbation x‖ ≤ Cpert)
    (x y : E) :
    ‖fderiv ℝ (lowerPopulationSum base perturbation) y -
        fderiv ℝ (lowerPopulationSum base perturbation) x‖ ≤
      (Cbase + Cpert) * ‖y - x‖ := by
  exact fderiv_lipschitz_of_second_bound
    (lowerPopulationSum_contDiff hbase hpert)
    (lowerPopulationSum_second_bound hbase hpert hbaseB hpertB) x y

theorem lowerPopulationSum_hessian_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation)
    {Cthird : ℝ}
    (hbaseZero : ∀ x, iteratedFDeriv ℝ 3 base x = 0)
    (hpertB : ∀ x, ‖iteratedFDeriv ℝ 3 perturbation x‖ ≤ Cthird)
    (x y : E) :
    ‖iteratedFDeriv ℝ 2 (lowerPopulationSum base perturbation) y -
        iteratedFDeriv ℝ 2 (lowerPopulationSum base perturbation) x‖ ≤
      Cthird * ‖y - x‖ := by
  exact hessian_lipschitz_of_third_bound
    (lowerPopulationSum_contDiff hbase hpert)
    (lowerPopulationSum_third_bound hbase hpert hbaseZero hpertB) x y

/-! ## Strong-Hessian aggregation -/

theorem lowerPopulationSum_strong_hessian_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {base perturbation : E → ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hpert : ContDiff ℝ ∞ perturbation)
    {muG delta : ℝ} (_hmuG : 0 ≤ muG) (_hdelta : 0 ≤ delta)
    (_hsmall : delta ≤ muG)
    (hbaseCoercive : ∀ x w,
      muG * ‖w‖ ^ 2 ≤
        iteratedFDeriv ℝ 2 base x (fun _ ↦ w))
    (hpertB : ∀ x, ‖iteratedFDeriv ℝ 2 perturbation x‖ ≤ delta)
    (x w : E) :
    (muG - delta) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2 (lowerPopulationSum base perturbation) x
        (fun _ ↦ w) := by
  have hbaseAt : ContDiffAt ℝ 2 base x :=
    (hbase.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hpertAt : ContDiffAt ℝ 2 perturbation x :=
    (hpert.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  unfold lowerPopulationSum
  rw [iteratedFDeriv_add_apply hbaseAt hpertAt,
    add_apply]
  let R := iteratedFDeriv ℝ 2 perturbation x
  have hRapply := R.le_opNorm (fun _ : Fin 2 ↦ w)
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at hRapply
  have hRabs : |R (fun _ : Fin 2 ↦ w)| ≤ delta * ‖w‖ ^ 2 := by
    calc
      |R (fun _ : Fin 2 ↦ w)| ≤ ‖R‖ * (‖w‖ * ‖w‖) := hRapply
      _ ≤ delta * (‖w‖ * ‖w‖) := by
        gcongr
        exact hpertB x
      _ = delta * ‖w‖ ^ 2 := by ring
  have hRlower : -(delta * ‖w‖ ^ 2) ≤ R (fun _ : Fin 2 ↦ w) :=
    (abs_le.mp hRabs).1
  have hBase := hbaseCoercive x w
  dsimp [R] at hRlower
  linarith

/-! ## Gap scaling and condition-number algebra -/

theorem eta_mul_sqrt_le_sqrt_div_of_gap
    {CDelta eta Delta : ℝ} {T : ℕ}
    (hCDelta : 0 < CDelta) (heta : 0 ≤ eta) (hDelta : 0 ≤ Delta)
    (hgap : CDelta * eta ^ 2 * T ≤ Delta) :
    eta * Real.sqrt T ≤ Real.sqrt (Delta / CDelta) := by
  have hratio : eta ^ 2 * T ≤ Delta / CDelta := by
    apply (le_div_iff₀ hCDelta).2
    nlinarith
  have hsqrtT : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by positivity)
  have hratio0 : 0 ≤ Delta / CDelta := div_nonneg hDelta hCDelta.le
  have hsqrtRatio : (Real.sqrt (Delta / CDelta)) ^ 2 = Delta / CDelta :=
    Real.sq_sqrt hratio0
  apply (sq_le_sq₀ (mul_nonneg heta (Real.sqrt_nonneg T))
    (Real.sqrt_nonneg _)).1
  rw [mul_pow, hsqrtT, hsqrtRatio]
  exact_mod_cast hratio

theorem first_derivative_bound_of_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {eta Delta CDelta Cgrad : ℝ}
    (hCDelta : 0 < CDelta) (heta : 0 ≤ eta) (hDelta : 0 ≤ Delta)
    (hCgrad : 0 ≤ Cgrad)
    (hgap : CDelta * eta ^ 2 * T ≤ Delta)
    {f : E → ℝ}
    (hraw : ∀ p : E,
      ‖iteratedFDeriv ℝ 1 f p‖ ≤ Cgrad * eta * Real.sqrt T + 1)
    (p : E) :
    ‖iteratedFDeriv ℝ 1 f p‖ ≤
      1 + Cgrad * Real.sqrt (Delta / CDelta) := by
  calc
    ‖iteratedFDeriv ℝ 1 f p‖ ≤ Cgrad * eta * Real.sqrt T + 1 := hraw p
    _ ≤ Cgrad * Real.sqrt (Delta / CDelta) + 1 := by
      have hscale := eta_mul_sqrt_le_sqrt_div_of_gap
        hCDelta heta hDelta hgap
      nlinarith [mul_le_mul_of_nonneg_left hscale hCgrad]
    _ = 1 + Cgrad * Real.sqrt (Delta / CDelta) := by ring

theorem lower_condition_number_sandwich
    {kappa muGAct Ly CHess : ℝ}
    (hkappa : 1 ≤ kappa) (hmuGAct : 0 < muGAct)
    (hCHess : 0 ≤ CHess)
    (hmuGActLower : 1 / (2 * kappa) ≤ muGAct)
    (hmuGActUpper : muGAct ≤ 1 / kappa)
    (hLyLower : 1 ≤ Ly) (hLyUpper : Ly ≤ 2 + CHess) :
    kappa ≤ Ly / muGAct ∧
      Ly / muGAct ≤ 2 * (2 + CHess) * kappa := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  constructor
  · apply (le_div_iff₀ hmuGAct).2
    have hkm : kappa * muGAct ≤ 1 := by
      have h := (le_div_iff₀ hkpos).1 hmuGActUpper
      simpa [mul_comm] using h
    exact hkm.trans hLyLower
  · apply (div_le_iff₀ hmuGAct).2
    have hscale : 1 ≤ 2 * kappa * muGAct := by
      have h := mul_le_mul_of_nonneg_left hmuGActLower
        (show 0 ≤ 2 * kappa from mul_nonneg (by norm_num) hkpos.le)
      have hden : 2 * kappa ≠ 0 := mul_ne_zero (by norm_num) hkpos.ne'
      field_simp [hden] at h
      simpa [mul_assoc] using h
    have hnonneg : 0 ≤ 2 + CHess := by linarith
    calc
      Ly ≤ 2 + CHess := hLyUpper
      _ ≤ (2 + CHess) * (2 * kappa * muGAct) := by
        exact le_mul_of_one_le_right hnonneg hscale
      _ = 2 * (2 + CHess) * kappa * muGAct := by ring

end

end BilevelLowerBound
