/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainGradient
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Higher-order global bounds for the zero chain

This file verifies the dimension-free second- and third-order estimates used
for the smooth zero chain.  The analytic part first proves that every
inverse-polynomial multiple of the flat bump is globally bounded.  It then
transfers this fact to all scalar derivatives of `psi`.
-/

open Filter Function Polynomial Real Set
open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

/-- At `+∞`, an inverse-polynomial multiple of the flat bump converges to the
constant term of the polynomial. -/
theorem tendsto_polynomial_eval_inv_mul_expNegInvSqGlue_atTop
    (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x⁻¹ * expNegInvSqGlue x)
      atTop (nhds (p.eval 0)) := by
  have hInv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hPoly : Tendsto (fun x : ℝ ↦ p.eval x⁻¹) atTop (nhds (p.eval 0)) :=
    p.continuous.continuousAt.tendsto.comp hInv
  have hExp : Tendsto (fun x : ℝ ↦ Real.exp (-((x⁻¹) ^ 2)))
      atTop (nhds 1) := by
    have hSq : Tendsto (fun x : ℝ ↦ (x⁻¹) ^ 2) atTop (nhds 0) := by
      simpa using hInv.pow 2
    have hNeg : Tendsto (fun x : ℝ ↦ -((x⁻¹) ^ 2)) atTop (nhds 0) := by
      simpa using hSq.neg
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hNeg
  have hBump : Tendsto expNegInvSqGlue atTop (nhds 1) := by
    apply hExp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (expNegInvSqGlue_eq_exp_of_pos hx).symm
  simpa using hPoly.mul hBump

/-- At `-∞`, an inverse-polynomial multiple of the one-sided flat bump is
eventually zero. -/
theorem tendsto_polynomial_eval_inv_mul_expNegInvSqGlue_atBot
    (p : ℝ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval x⁻¹ * expNegInvSqGlue x)
      atBot (nhds 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  simp [expNegInvSqGlue_eq_zero_of_nonpos hx]

/-- Every inverse-polynomial multiple of the flat bump has bounded range. -/
theorem isBounded_range_polynomial_eval_inv_mul_expNegInvSqGlue
    (p : ℝ[X]) :
    Bornology.IsBounded
      (Set.range (fun x : ℝ ↦ p.eval x⁻¹ * expNegInvSqGlue x)) := by
  apply (continuous_polynomial_eval_inv_mul_expNegInvSqGlue p).isBounded_range_iff_isBigO_atTop_atBot.mpr
  exact ⟨
    (tendsto_polynomial_eval_inv_mul_expNegInvSqGlue_atTop p).isBigO_one ℝ,
    (tendsto_polynomial_eval_inv_mul_expNegInvSqGlue_atBot p).isBigO_one ℝ⟩

/-- A nonnegative numerical bound may be chosen for every inverse-polynomial
multiple of the flat bump. -/
theorem exists_bound_polynomial_eval_inv_mul_expNegInvSqGlue
    (p : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, |p.eval x⁻¹ * expNegInvSqGlue x| ≤ C := by
  have hBounded :=
    isBounded_range_polynomial_eval_inv_mul_expNegInvSqGlue p
  rw [isBounded_iff_forall_norm_le] at hBounded
  obtain ⟨C, hC⟩ := hBounded
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  simpa [Real.norm_eq_abs] using
    (hC _ ⟨x, rfl⟩).trans (le_max_left C 0)

/-- Every fixed-order derivative of `psi` is globally bounded. -/
theorem exists_bound_psi_iteratedDeriv (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv n psi t| ≤ C := by
  obtain ⟨p, hp⟩ :=
    exists_polynomial_iteratedDeriv_expNegInvSqGlue n 1
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_polynomial_eval_inv_mul_expNegInvSqGlue p
  refine ⟨Real.exp 1 * 2 ^ n * C, by positivity, fun t ↦ ?_⟩
  rw [psi_iteratedDeriv]
  have hRep := congrFun hp (2 * t - 1)
  have hOne :
      (fun x ↦ (1 : ℝ[X]).eval x⁻¹ * expNegInvSqGlue x) =
        expNegInvSqGlue := by
    funext x
    simp
  rw [hOne] at hRep
  rw [hRep, abs_mul, abs_mul, abs_of_pos (Real.exp_pos 1),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-- The Fréchet and ordinary one-dimensional iterated derivatives have the
same norm, hence the preceding scalar bound is also an operator-norm bound. -/
theorem exists_bound_psi_iteratedFDeriv (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ n psi t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_psi_iteratedDeriv n
  refine ⟨C, hC0, fun t ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact hC t

/-- First derivative of the Gaussian kernel. -/
theorem gaussianKernel_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianKernel (-t * gaussianKernel t) t := by
  change HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2) / 2))
    (-t * Real.exp (-(t ^ 2) / 2)) t
  have hSq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
    have hRaw := (hasDerivAt_id t).pow 2
    have hFun : (fun x : ℝ ↦ x ^ 2) =ᶠ[nhds t] (id ^ 2) :=
      Filter.Eventually.of_forall (by simp)
    refine (hRaw.congr_of_eventuallyEq hFun).congr_deriv ?_
    simp
  have hQuad : HasDerivAt (fun x : ℝ ↦ -(x ^ 2) / 2) (-t) t := by
    have hRaw := hSq.neg.div_const 2
    have hFun : (fun x : ℝ ↦ -(x ^ 2) / 2) =ᶠ[nhds t]
        (fun x ↦ -(x ^ 2) / 2) := Filter.Eventually.of_forall (fun _ ↦ rfl)
    refine (hRaw.congr_of_eventuallyEq hFun).congr_deriv ?_
    ring
  simpa only [mul_comm] using hQuad.exp

theorem gaussianKernel_deriv (t : ℝ) :
    deriv gaussianKernel t = -t * gaussianKernel t :=
  (gaussianKernel_hasDerivAt t).deriv

/-- Second ordinary derivative of the Gaussian kernel. -/
theorem gaussianKernel_iteratedDeriv_two (t : ℝ) :
    iteratedDeriv 2 gaussianKernel t =
      (t ^ 2 - 1) * gaussianKernel t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ']
  have hDeriv : deriv gaussianKernel = fun x ↦ -x * gaussianKernel x := by
    funext x
    exact gaussianKernel_deriv x
  rw [hDeriv, iteratedDeriv_one]
  have hNeg : HasDerivAt (fun x : ℝ ↦ -x) (-1) t := by
    change HasDerivAt (-id) (-1) t
    exact (hasDerivAt_id t).neg
  have hProd : HasDerivAt (fun x : ℝ ↦ -x * gaussianKernel x)
      ((-1) * gaussianKernel t + (-t) * (-t * gaussianKernel t)) t :=
    hNeg.mul (gaussianKernel_hasDerivAt t)
  calc
    deriv (fun x : ℝ ↦ -x * gaussianKernel x) t =
        (-1) * gaussianKernel t + (-t) * (-t * gaussianKernel t) :=
      hProd.deriv
    _ = (t ^ 2 - 1) * gaussianKernel t := by ring

/-- The product `|t| exp(-t²/2)` is at most one. -/
theorem abs_mul_gaussianKernel_le_one (t : ℝ) :
    |t * gaussianKernel t| ≤ 1 := by
  apply abs_le_of_sq_le_sq _ (by norm_num)
  have h := Real.mul_exp_neg_le_exp_neg_one (t ^ 2)
  have hExp : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  calc
    (t * gaussianKernel t) ^ 2 = t ^ 2 * Real.exp (-(t ^ 2)) := by
      simp only [gaussianKernel, mul_pow]
      rw [← Real.exp_nat_mul]
      ring_nf
    _ ≤ Real.exp (-1) := h
    _ ≤ 1 ^ 2 := by simpa using hExp

/-- A coarse but global bound for the second derivative of the Gaussian
kernel. -/
theorem abs_gaussianKernel_iteratedDeriv_two_le_three (t : ℝ) :
    |iteratedDeriv 2 gaussianKernel t| ≤ 3 := by
  rw [gaussianKernel_iteratedDeriv_two, abs_mul]
  have hGauss0 : 0 ≤ gaussianKernel t := gaussianKernel_nonneg t
  have hGauss1 : gaussianKernel t ≤ 1 := gaussianKernel_le_one t
  have hy : 0 ≤ t ^ 2 / 2 := by positivity
  have h := Real.mul_exp_neg_le_exp_neg_one (t ^ 2 / 2)
  have hExp : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  have hQuad : t ^ 2 * gaussianKernel t ≤ 2 := by
    have hRewrite :
        (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)) =
          (t ^ 2 * gaussianKernel t) / 2 := by
      simp only [gaussianKernel]
      ring
    rw [hRewrite] at h
    nlinarith [h.trans hExp]
  have hAbs : |t ^ 2 - 1| ≤ t ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have hNorm : |gaussianKernel t| = gaussianKernel t := abs_of_nonneg hGauss0
  rw [hNorm]
  calc
    |t ^ 2 - 1| * gaussianKernel t ≤
        (t ^ 2 + 1) * gaussianKernel t := by gcongr
    _ = t ^ 2 * gaussianKernel t + gaussianKernel t := by ring
    _ ≤ 3 := by linarith

/-- The first three Fréchet derivatives of the Gaussian primitive are bounded
by a single numerical constant. -/
theorem norm_iteratedFDeriv_phiZero_le_five
    (n : ℕ) (hn : n ≤ 3) (t : ℝ) :
    ‖iteratedFDeriv ℝ n phiZero t‖ ≤ 5 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  interval_cases n
  · exact (abs_phiZero_le_bound t).trans (phiBound_lt.trans (by norm_num)).le
  · rw [iteratedDeriv_one, phiZero_deriv]
    calc
      |Real.sqrt (Real.exp 1) * gaussianKernel t|
          ≤ Real.sqrt (Real.exp 1) := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
              abs_of_nonneg (gaussianKernel_nonneg t)]
            exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
              (gaussianKernel_le_one t)
      _ ≤ 5 := (sqrt_exp_one_lt.trans (by norm_num)).le
  · rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ']
    have hDeriv : deriv phiZero =
        fun x ↦ Real.sqrt (Real.exp 1) * gaussianKernel x := by
      funext x
      exact phiZero_deriv x
    rw [hDeriv, iteratedDeriv_one, deriv_const_mul_field,
      gaussianKernel_deriv, abs_mul]
    calc
      |Real.sqrt (Real.exp 1)| * |-t * gaussianKernel t|
          ≤ Real.sqrt (Real.exp 1) * 1 := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]
            gcongr
            simpa only [neg_mul, abs_neg] using abs_mul_gaussianKernel_le_one t
      _ ≤ 5 := by
        simpa using (sqrt_exp_one_lt.trans (by norm_num)).le
  · rw [iteratedDeriv_succ']
    have hDeriv : deriv phiZero =
        fun x ↦ Real.sqrt (Real.exp 1) * gaussianKernel x := by
      funext x
      exact phiZero_deriv x
    rw [hDeriv, iteratedDeriv_const_mul_field, abs_mul]
    calc
      |Real.sqrt (Real.exp 1)| * |iteratedDeriv 2 gaussianKernel t|
          ≤ (1649 / 1000 : ℝ) * 3 := by
            gcongr
            · exact (abs_of_nonneg (Real.sqrt_nonneg _)).trans_le sqrt_exp_one_lt.le
            · exact abs_gaussianKernel_iteratedDeriv_two_le_three t
      _ ≤ 5 := by norm_num

/-- One constant controls the first four jets of `psi`. -/
theorem exists_common_bound_psi_three :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
        ‖iteratedFDeriv ℝ n psi t‖ ≤ C := by
  obtain ⟨C0, hC00, hC0⟩ := exists_bound_psi_iteratedFDeriv 0
  obtain ⟨C1, hC10, hC1⟩ := exists_bound_psi_iteratedFDeriv 1
  obtain ⟨C2, hC20, hC2⟩ := exists_bound_psi_iteratedFDeriv 2
  obtain ⟨C3, hC30, hC3⟩ := exists_bound_psi_iteratedFDeriv 3
  refine ⟨C0 + C1 + C2 + C3, by positivity, fun n hn t ↦ ?_⟩
  interval_cases n
  · exact (hC0 t).trans (by linarith)
  · exact (hC1 t).trans (by linarith)
  · exact (hC2 t).trans (by linarith)
  · exact (hC3 t).trans (by linarith)

/-- Composing a scalar function with a contraction does not increase any of
its fixed-order derivative bounds. -/
theorem norm_iteratedFDeriv_comp_clm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n f t‖ ≤ C)
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (n : ℕ) (hn : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ C := by
  rw [L.iteratedFDeriv_comp_right hf x
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)]
  calc
    ‖(iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ ↦ L)‖
        ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ∏ _ : Fin n, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * 1 := by
      gcongr
      · exact hC n hn (L x)
      · apply Finset.prod_le_one
        · intro i _hi
          exact norm_nonneg _
        · intro i _hi
          exact hL
    _ = C := mul_one C

/-- A Leibniz bound specialized to derivative orders at most three. -/
theorem norm_iteratedFDeriv_mul_le_eight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hC : ∀ n : ℕ, n ≤ 3 → ∀ x : E,
      ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (hD : ∀ n : ℕ, n ≤ 3 → ∀ x : E,
      ‖iteratedFDeriv ℝ n g x‖ ≤ D)
    (n : ℕ) (hn : n ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f y * g y) x‖ ≤ 8 * C * D := by
  calc
    ‖iteratedFDeriv ℝ n (fun y ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * C * D := by
      gcongr with i hi
      · exact hC i (by
          have hi' := Finset.mem_range.1 hi
          omega) x
      · exact hD (n - i) (by omega) x
    _ ≤ 8 * C * D := by
      interval_cases n <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith [mul_nonneg hC0 hD0]

/-- All link jets through order three admit a common global operator-norm
bound.  The value of the constant is immaterial; importantly, it does not
depend on the chain length. -/
theorem exists_common_bound_chainQ_three :
    ∃ Cq : ℝ, 0 ≤ Cq ∧
      ∀ n : ℕ, n ≤ 3 → ∀ w : ℝ × ℝ,
        ‖iteratedFDeriv ℝ n
          (fun z : ℝ × ℝ ↦ chainQ z.1 z.2) w‖ ≤ Cq := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_common_bound_psi_three
  let Lfst : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let Lsnd : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hLfst : ‖Lfst‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hLsnd : ‖Lsnd‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  have hNegLfst : ‖-Lfst‖ ≤ 1 := by simpa using hLfst
  have hNegLsnd : ‖-Lsnd‖ ≤ 1 := by simpa using hLsnd
  let fNeg : ℝ × ℝ → ℝ := fun z ↦ psi (-z.1)
  let fPos : ℝ × ℝ → ℝ := fun z ↦ psi z.1
  let gNeg : ℝ × ℝ → ℝ := fun z ↦ phiZero (-z.2)
  let gPos : ℝ × ℝ → ℝ := fun z ↦ phiZero z.2
  have hfNegSmooth : ContDiff ℝ ∞ fNeg := by
    dsimp [fNeg]
    exact psi_contDiff.comp contDiff_fst.neg
  have hfPosSmooth : ContDiff ℝ ∞ fPos := by
    dsimp [fPos]
    exact psi_contDiff.comp contDiff_fst
  have hgNegSmooth : ContDiff ℝ ∞ gNeg := by
    dsimp [gNeg]
    exact phiZero_contDiff.comp contDiff_snd.neg
  have hgPosSmooth : ContDiff ℝ ∞ gPos := by
    dsimp [gPos]
    exact phiZero_contDiff.comp contDiff_snd
  have hfNegBound : ∀ n : ℕ, n ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ n fNeg w‖ ≤ Cψ := by
    intro n hn w
    have h := norm_iteratedFDeriv_comp_clm_le psi_contDiff Cψ hCψ0 hCψ
      (-Lfst) hNegLfst n hn w
    simpa [fNeg, Function.comp_def, Lfst] using h
  have hfPosBound : ∀ n : ℕ, n ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ n fPos w‖ ≤ Cψ := by
    intro n hn w
    have h := norm_iteratedFDeriv_comp_clm_le psi_contDiff Cψ hCψ0 hCψ
      Lfst hLfst n hn w
    simpa [fPos, Function.comp_def, Lfst] using h
  have hgNegBound : ∀ n : ℕ, n ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ n gNeg w‖ ≤ 5 := by
    intro n hn w
    have h := norm_iteratedFDeriv_comp_clm_le phiZero_contDiff 5 (by norm_num)
      (fun k hk t ↦ norm_iteratedFDeriv_phiZero_le_five k hk t)
      (-Lsnd) hNegLsnd n hn w
    simpa [gNeg, Function.comp_def, Lsnd] using h
  have hgPosBound : ∀ n : ℕ, n ≤ 3 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ n gPos w‖ ≤ 5 := by
    intro n hn w
    have h := norm_iteratedFDeriv_comp_clm_le phiZero_contDiff 5 (by norm_num)
      (fun k hk t ↦ norm_iteratedFDeriv_phiZero_le_five k hk t)
      Lsnd hLsnd n hn w
    simpa [gPos, Function.comp_def, Lsnd] using h
  refine ⟨16 * Cψ * 5, by positivity, fun n hn w ↦ ?_⟩
  have hNegProd := norm_iteratedFDeriv_mul_le_eight hfNegSmooth hgNegSmooth
    hCψ0 (by norm_num) hfNegBound hgNegBound n hn w
  have hPosProd := norm_iteratedFDeriv_mul_le_eight hfPosSmooth hgPosSmooth
    hCψ0 (by norm_num) hfPosBound hgPosBound n hn w
  change ‖iteratedFDeriv ℝ n (fun z : ℝ × ℝ ↦ fNeg z * gNeg z -
    fPos z * gPos z) w‖ ≤ 16 * Cψ * 5
  have hSub :
      (fun z : ℝ × ℝ ↦ fNeg z * gNeg z - fPos z * gPos z) =
        (fun z ↦ fNeg z * gNeg z) - (fun z ↦ fPos z * gPos z) := rfl
  rw [hSub, iteratedFDeriv_sub_apply
    ((hfNegSmooth.mul hgNegSmooth).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
    ((hfPosSmooth.mul hgPosSmooth).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The predecessor-coordinate projection used by a link derivative. -/
def predecessorCLM {T : ℕ} (i : Fin T) : ChainVector T →L[ℝ] ℝ := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
      exact Fin.cases 0 (fun j : Fin n ↦ EuclideanSpace.proj j.castSucc) i

@[simp]
theorem predecessorCLM_apply {T : ℕ} (i : Fin T) (v : ChainVector T) :
    predecessorCLM i v = withInitialZero v i.castSucc := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
      cases i using Fin.cases with
      | zero => simp [predecessorCLM, withInitialZero]
      | succ j => simp [predecessorCLM, withInitialZero]

/-- The two coordinates of a direction seen by one link. -/
def linkDirectionCLM {T : ℕ} (i : Fin T) :
    ChainVector T →L[ℝ] ℝ × ℝ :=
  (predecessorCLM i).prod (EuclideanSpace.proj i)

@[simp]
theorem linkDirectionCLM_apply {T : ℕ} (i : Fin T) (v : ChainVector T) :
    linkDirectionCLM i v = (withInitialZero v i.castSucc, v i) := by
  simp [linkDirectionCLM]

/-- The squared predecessor coordinates omit the final coordinate and are
therefore bounded by the full squared Euclidean norm. -/
theorem sum_predecessor_sq_le_sum_sq {T : ℕ} (v : ChainVector T) :
    (∑ i : Fin T, (withInitialZero v i.castSucc) ^ 2) ≤
      ∑ i : Fin T, (v i) ^ 2 := by
  cases T with
  | zero => simp
  | succ n =>
      have hPred :
          (∑ i : Fin (n + 1), (withInitialZero v i.castSucc) ^ 2) =
            ∑ j : Fin n, (v j.castSucc) ^ 2 := by
        rw [Fin.sum_univ_succ]
        simp [withInitialZero]
      rw [hPred, Fin.sum_univ_castSucc]
      nlinarith [sq_nonneg (v (Fin.last n))]

/-- Because each coordinate belongs to at most two neighboring links, the
sum of squared local direction norms is at most twice the global squared
Euclidean norm. -/
theorem sum_linkDirection_norm_sq_le {T : ℕ} (v : ChainVector T) :
    (∑ i : Fin T, ‖linkDirectionCLM i v‖ ^ 2) ≤ 2 * ‖v‖ ^ 2 := by
  calc
    (∑ i : Fin T, ‖linkDirectionCLM i v‖ ^ 2) ≤
        ∑ i : Fin T,
          ((withInitialZero v i.castSucc) ^ 2 + (v i) ^ 2) := by
      gcongr with i
      rw [linkDirectionCLM_apply, Prod.norm_def,
        Real.norm_eq_abs, Real.norm_eq_abs]
      by_cases h : |withInitialZero v i.castSucc| ≤ |v i|
      · rw [max_eq_right h, sq_abs]
        nlinarith [sq_nonneg (withInitialZero v i.castSucc)]
      · rw [max_eq_left (le_of_not_ge h), sq_abs]
        nlinarith [sq_nonneg (v i)]
    _ = (∑ i : Fin T, (withInitialZero v i.castSucc) ^ 2) +
        ∑ i : Fin T, (v i) ^ 2 := Finset.sum_add_distrib
    _ ≤ (∑ i : Fin T, (v i) ^ 2) + ∑ i : Fin T, (v i) ^ 2 := by
      exact add_le_add (sum_predecessor_sq_le_sum_sq v) le_rfl
    _ = 2 * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      ring

/-- Each local two-coordinate direction has norm at most the norm of the
whole direction vector. -/
theorem linkDirection_norm_le {T : ℕ} (i : Fin T) (v : ChainVector T) :
    ‖linkDirectionCLM i v‖ ≤ ‖v‖ := by
  rw [linkDirectionCLM_apply, Prod.norm_def]
  apply max_le
  · cases T with
    | zero => exact Fin.elim0 i
    | succ n =>
        cases i using Fin.cases with
        | zero => simp [withInitialZero]
        | succ j =>
            simpa [withInitialZero] using PiLp.norm_apply_le v j.castSucc
  · exact PiLp.norm_apply_le v i

/-- Cauchy--Schwarz plus the overlap count controls two local directions. -/
theorem sum_linkDirection_norm_mul_le {T : ℕ}
    (v w : ChainVector T) :
    (∑ i : Fin T, ‖linkDirectionCLM i v‖ * ‖linkDirectionCLM i w‖) ≤
      2 * ‖v‖ * ‖w‖ := by
  let A : ℝ := ∑ i : Fin T, ‖linkDirectionCLM i v‖ ^ 2
  let B : ℝ := ∑ i : Fin T, ‖linkDirectionCLM i w‖ ^ 2
  let S : ℝ := ∑ i : Fin T,
    ‖linkDirectionCLM i v‖ * ‖linkDirectionCLM i w‖
  have hCS : S ^ 2 ≤ A * B := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i ↦ ‖linkDirectionCLM i v‖)
      (fun i ↦ ‖linkDirectionCLM i w‖)
  have hA : A ≤ 2 * ‖v‖ ^ 2 := sum_linkDirection_norm_sq_le v
  have hB : B ≤ 2 * ‖w‖ ^ 2 := sum_linkDirection_norm_sq_le w
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hAB : A * B ≤ (2 * ‖v‖ * ‖w‖) ^ 2 := by
    calc
      A * B ≤ (2 * ‖v‖ ^ 2) * (2 * ‖w‖ ^ 2) :=
        mul_le_mul hA hB hB0 (by positivity)
      _ = (2 * ‖v‖ * ‖w‖) ^ 2 := by ring
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg (fun _ _ ↦
      mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (sq_le_sq₀ hS0 (by positivity)).mp (hCS.trans hAB)

/-- The same overlap estimate for three local directions. -/
theorem sum_linkDirection_norm_triple_le {T : ℕ}
    (u v w : ChainVector T) :
    (∑ i : Fin T, ‖linkDirectionCLM i u‖ *
      ‖linkDirectionCLM i v‖ * ‖linkDirectionCLM i w‖) ≤
      2 * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc
    (∑ i : Fin T, ‖linkDirectionCLM i u‖ *
        ‖linkDirectionCLM i v‖ * ‖linkDirectionCLM i w‖) ≤
      ∑ i : Fin T, (‖linkDirectionCLM i u‖ *
        ‖linkDirectionCLM i v‖) * ‖w‖ := by
        gcongr with i
        exact linkDirection_norm_le i w
    _ = (∑ i : Fin T, ‖linkDirectionCLM i u‖ *
        ‖linkDirectionCLM i v‖) * ‖w‖ := by rw [Finset.sum_mul]
    _ ≤ (2 * ‖u‖ * ‖v‖) * ‖w‖ := by
      gcongr
      exact sum_linkDirection_norm_mul_le u v
    _ = 2 * ‖u‖ * ‖v‖ * ‖w‖ := rfl

/-- The constant part of the affine coordinate map of one link. -/
def linkOffset {T : ℕ} (i : Fin T) : ℝ × ℝ :=
  (withInitialOne (0 : ChainVector T) i.castSucc, 0)

theorem withInitialOne_eq_offset_add {T : ℕ}
    (q : ChainVector T) (i : Fin T) :
    withInitialOne q i.castSucc =
      (linkOffset i).1 + withInitialZero q i.castSucc := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
      cases i using Fin.cases with
      | zero => simp [linkOffset, withInitialOne, withInitialZero]
      | succ j => simp [linkOffset, withInitialOne, withInitialZero]

/-- A single unscaled link, regarded as a function on the whole chain
space. -/
def unscaledLink {T : ℕ} (i : Fin T) (q : ChainVector T) : ℝ :=
  chainQ (withInitialOne q i.castSucc) (q i)

/-- Exact evaluation formula for every derivative of one affine link. -/
theorem iteratedFDeriv_unscaledLink_apply {T n : ℕ}
    (i : Fin T) (q : ChainVector T) (m : Fin n → ChainVector T) :
    iteratedFDeriv ℝ n (unscaledLink i) q m =
      iteratedFDeriv ℝ n (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
        (withInitialOne q i.castSucc, q i)
        (fun j ↦ linkDirectionCLM i (m j)) := by
  let qPair : ℝ × ℝ → ℝ := fun z ↦ chainQ z.1 z.2
  let L := linkDirectionCLM i
  let c := linkOffset i
  let shifted : ℝ × ℝ → ℝ := fun z ↦ qPair (c + z)
  have hShiftSmooth : ContDiff ℝ ∞ shifted := by
    exact chainQ_contDiff.comp (contDiff_const.add contDiff_id)
  have hFun : unscaledLink i = shifted ∘ L := by
    funext x
    change chainQ (withInitialOne x i.castSucc) (x i) =
      chainQ ((c + L x).1) ((c + L x).2)
    rw [show L x = (withInitialZero x i.castSucc, x i) by
      exact linkDirectionCLM_apply i x]
    simp only [c, linkOffset, Prod.fst_add, Prod.snd_add]
    rw [withInitialOne_eq_offset_add]
    simp [linkOffset]
  rw [hFun, L.iteratedFDeriv_comp_right hShiftSmooth q
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ n shifted (L q) (fun j ↦ L (m j)) = _
  rw [show shifted = (fun z ↦ qPair (c + z)) from rfl,
    iteratedFDeriv_comp_add_left]
  have hPoint : c + L q = (withInitialOne q i.castSucc, q i) := by
    ext
    · simpa [c, L, linkOffset, linkDirectionCLM_apply] using
        (withInitialOne_eq_offset_add q i).symm
    · simp [c, L, linkOffset, linkDirectionCLM_apply]
  rw [hPoint]

theorem unscaledLink_contDiff {T : ℕ} (i : Fin T) :
    ContDiff ℝ ∞ (unscaledLink i) := by
  exact chainQ_comp_contDiff (withInitialOne_coord_contDiff i) (by fun_prop)

/-- Exact sum-of-local-jets formula for the complete unscaled chain. -/
theorem iteratedFDeriv_unscaledChain_apply {T n : ℕ}
    (q : ChainVector T) (m : Fin n → ChainVector T) :
    iteratedFDeriv ℝ n (unscaledChain : ChainVector T → ℝ) q m =
      ∑ i : Fin T,
        iteratedFDeriv ℝ n (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
          (withInitialOne q i.castSucc, q i)
          (fun j ↦ linkDirectionCLM i (m j)) := by
  have hFun : (unscaledChain : ChainVector T → ℝ) =
      fun x ↦ ∑ i : Fin T, unscaledLink i x := by
    funext x
    rfl
  rw [hFun, iteratedFDeriv_fun_sum_apply]
  · rw [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    exact iteratedFDeriv_unscaledLink_apply i q m
  · intro i _hi
    exact ((unscaledLink_contDiff i).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt

/-- The unscaled chain has a dimension- and length-independent Hessian
operator-norm bound. -/
theorem exists_unscaledChain_second_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) (q : ChainVector T),
      ‖iteratedFDeriv ℝ 2 (unscaledChain : ChainVector T → ℝ) q‖ ≤ C := by
  obtain ⟨Cq, hCq0, hCq⟩ := exists_common_bound_chainQ_three
  refine ⟨2 * Cq, by positivity, fun T q ↦ ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  rw [iteratedFDeriv_unscaledChain_apply]
  calc
    ‖∑ i : Fin T,
        iteratedFDeriv ℝ 2 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
          (withInitialOne q i.castSucc, q i)
          (fun j ↦ linkDirectionCLM i (m j))‖ ≤
      ∑ i : Fin T,
        ‖iteratedFDeriv ℝ 2 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
          (withInitialOne q i.castSucc, q i)
          (fun j ↦ linkDirectionCLM i (m j))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin T, Cq *
        (‖linkDirectionCLM i (m 0)‖ *
          ‖linkDirectionCLM i (m 1)‖) := by
      gcongr with i
      have hOp := (iteratedFDeriv ℝ 2
        (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
        (withInitialOne q i.castSucc, q i)).le_opNorm
          (fun j ↦ linkDirectionCLM i (m j))
      calc
        ‖iteratedFDeriv ℝ 2 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
            (withInitialOne q i.castSucc, q i)
            (fun j ↦ linkDirectionCLM i (m j))‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
            (withInitialOne q i.castSucc, q i)‖ *
              ∏ j : Fin 2, ‖linkDirectionCLM i (m j)‖ := hOp
        _ ≤ Cq * ∏ j : Fin 2, ‖linkDirectionCLM i (m j)‖ := by
          gcongr
          exact hCq 2 (by norm_num) _
        _ = Cq * (‖linkDirectionCLM i (m 0)‖ *
            ‖linkDirectionCLM i (m 1)‖) := by
          simp [Fin.prod_univ_succ]
    _ = Cq * ∑ i : Fin T, (‖linkDirectionCLM i (m 0)‖ *
          ‖linkDirectionCLM i (m 1)‖) := by rw [Finset.mul_sum]
    _ ≤ Cq * (2 * ‖m 0‖ * ‖m 1‖) := by
      gcongr
      exact sum_linkDirection_norm_mul_le (m 0) (m 1)
    _ = (2 * Cq) * ∏ j : Fin 2, ‖m j‖ := by
      simp [Fin.prod_univ_succ]
      ring

/-- The unscaled chain has a dimension- and length-independent third
derivative operator-norm bound. -/
theorem exists_unscaledChain_third_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) (q : ChainVector T),
      ‖iteratedFDeriv ℝ 3 (unscaledChain : ChainVector T → ℝ) q‖ ≤ C := by
  obtain ⟨Cq, hCq0, hCq⟩ := exists_common_bound_chainQ_three
  refine ⟨2 * Cq, by positivity, fun T q ↦ ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  rw [iteratedFDeriv_unscaledChain_apply]
  calc
    ‖∑ i : Fin T,
        iteratedFDeriv ℝ 3 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
          (withInitialOne q i.castSucc, q i)
          (fun j ↦ linkDirectionCLM i (m j))‖ ≤
      ∑ i : Fin T,
        ‖iteratedFDeriv ℝ 3 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
          (withInitialOne q i.castSucc, q i)
          (fun j ↦ linkDirectionCLM i (m j))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin T, Cq *
        (‖linkDirectionCLM i (m 0)‖ *
          ‖linkDirectionCLM i (m 1)‖ *
          ‖linkDirectionCLM i (m 2)‖) := by
      gcongr with i
      have hOp := (iteratedFDeriv ℝ 3
        (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
        (withInitialOne q i.castSucc, q i)).le_opNorm
          (fun j ↦ linkDirectionCLM i (m j))
      calc
        ‖iteratedFDeriv ℝ 3 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
            (withInitialOne q i.castSucc, q i)
            (fun j ↦ linkDirectionCLM i (m j))‖ ≤
          ‖iteratedFDeriv ℝ 3 (fun z : ℝ × ℝ ↦ chainQ z.1 z.2)
            (withInitialOne q i.castSucc, q i)‖ *
              ∏ j : Fin 3, ‖linkDirectionCLM i (m j)‖ := hOp
        _ ≤ Cq * ∏ j : Fin 3, ‖linkDirectionCLM i (m j)‖ := by
          gcongr
          exact hCq 3 (by norm_num) _
        _ = Cq * (‖linkDirectionCLM i (m 0)‖ *
            ‖linkDirectionCLM i (m 1)‖ *
            ‖linkDirectionCLM i (m 2)‖) := by
          simp [Fin.prod_univ_succ, mul_assoc]
    _ = Cq * ∑ i : Fin T, (‖linkDirectionCLM i (m 0)‖ *
          ‖linkDirectionCLM i (m 1)‖ *
          ‖linkDirectionCLM i (m 2)‖) := by rw [Finset.mul_sum]
    _ ≤ Cq * (2 * ‖m 0‖ * ‖m 1‖ * ‖m 2‖) := by
      gcongr
      exact sum_linkDirection_norm_triple_le (m 0) (m 1) (m 2)
    _ = (2 * Cq) * ∏ j : Fin 3, ‖m j‖ := by
      simp [Fin.prod_univ_succ]
      ring

/-- The scaled chain has a universal Hessian bound. -/
theorem exists_scaledChain_second_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) {η : ℝ}, η ≠ 0 →
      ∀ z : ChainVector T,
        ‖iteratedFDeriv ℝ 2 (scaledChain η : ChainVector T → ℝ) z‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_unscaledChain_second_bound
  refine ⟨C, hC0, fun T η hη z ↦ ?_⟩
  rw [iteratedFDeriv_scaledChain_two hη]
  exact hC T (normalize η z)

/-- The third derivative of the scaled chain is bounded by a universal
constant times `η⁻¹`, exactly as required by the paper's scaling. -/
theorem exists_scaledChain_third_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) {η : ℝ}, 0 < η →
      ∀ z : ChainVector T,
        ‖iteratedFDeriv ℝ 3 (scaledChain η : ChainVector T → ℝ) z‖ ≤
          C / η := by
  obtain ⟨C, hC0, hC⟩ := exists_unscaledChain_third_bound
  refine ⟨C, hC0, fun T η hη z ↦ ?_⟩
  rw [iteratedFDeriv_scaledChain_three hη.ne']
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη]
  change η⁻¹ *
      ‖iteratedFDeriv ℝ 3 (unscaledChain : ChainVector T → ℝ)
        (normalize η z)‖ ≤ C / η
  rw [div_eq_mul_inv, mul_comm C η⁻¹]
  exact mul_le_mul_of_nonneg_left (hC T (normalize η z)) (inv_nonneg.mpr hη.le)

end

end BilevelLowerBound
