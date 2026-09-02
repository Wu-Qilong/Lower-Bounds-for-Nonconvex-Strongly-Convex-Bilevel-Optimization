/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierGateQuantitative
import BilevelLowerBoundLean.HardInstanceAnalytic

/-!
# Quantitative composition scales

This module proves the exact scaling identities for the frontier extractor
and visible chain, uniform derivative bounds for the unit-scale visible
chain, and composition estimates through order three.  The higher-order
composition estimate removes the affine part of the outer function before
applying the generic Faà di Bruno bound.  Consequently, the
dimension-dependent first derivative is charged only against the top
derivative of the inner map.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

theorem normalize_one {T : ℕ} (z : ChainVector T) :
    normalize 1 z = z := by
  ext i
  simp [normalize, chainVectorOfFun]

theorem tailActivation_one_normalize {T : ℕ} {η : ℝ}
    (z : ChainVector T) (i : Fin T) :
    tailActivation 1 (normalize η z) i = tailActivation η z i := by
  ext j
  simp only [tailActivation, chainVectorOfFun_apply]
  split_ifs
  · congr 1
    simp [normalize, chainVectorOfFun]
  · rfl

theorem chainLink_one_normalize {T : ℕ} {η : ℝ}
    (z : ChainVector T) (i : Fin T) :
    chainLink 1 (normalize η z) i = chainLink η z i := by
  unfold chainLink
  rw [normalize_one]

theorem frontierLinkGate_one_normalize {T : ℕ} {η : ℝ}
    (z : ChainVector T) (i : Fin T) :
    frontierLinkGate 1 (normalize η z) i = frontierLinkGate η z i := by
  unfold frontierLinkGate
  rw [tailActivation_one_normalize]

theorem frontierExtractor_scaling {T : ℕ} (η : ℝ) (z : ChainVector T) :
    frontierExtractor η z =
      η ^ 2 * frontierExtractor 1 (normalize η z) := by
  unfold frontierExtractor frontierSummand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [frontierLinkGate_one_normalize, chainLink_one_normalize]
  ring

theorem visibleChain_scaling {T : ℕ} (η : ℝ) (z : ChainVector T) :
    visibleChain η z = η ^ 2 * visibleChain 1 (normalize η z) := by
  rw [visibleChain, visibleChain, scaledChain_eq_scaled_unscaled,
    frontierExtractor_scaling, scaledChain_eq_scaled_unscaled, normalize_one]
  ring

/-- Quantitative composition bound for the rotated frontier, stated in terms
of the normalized hidden-coordinate map. -/
theorem norm_iteratedFDeriv_frontierExtractor_comp_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T n : ℕ} {η Cext D : ℝ}
    {q : E → ChainVector T} (hq : ContDiff ℝ ∞ q)
    (hExt : ∀ r : ℕ, r ≤ 3 → ∀ y : ChainVector T,
      ‖iteratedFDeriv ℝ r
          (frontierExtractor 1 : ChainVector T → ℝ) y‖ ≤ Cext)
    (hn : n ≤ 3) (z : E)
    (hD : ∀ r : ℕ, 1 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r ((normalizeCLM η) ∘ q) z‖ ≤ D ^ r) :
    ‖iteratedFDeriv ℝ n
        ((frontierExtractor η : ChainVector T → ℝ) ∘ q) z‖ ≤
      η ^ 2 * (Nat.factorial n * Cext * D ^ n) := by
  let qNorm : E → ChainVector T := (normalizeCLM η) ∘ q
  have hqNorm : ContDiff ℝ ∞ qNorm :=
    (normalizeCLM η).contDiff.comp hq
  have hComp := norm_iteratedFDeriv_comp_le
    (frontierExtractor_contDiff 1) hqNorm
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top) z
    (C := Cext) (D := D)
    (fun r hr ↦ hExt r (hr.trans hn) _)
    (by simpa [qNorm] using hD)
  have hFun :
      ((frontierExtractor η : ChainVector T → ℝ) ∘ q) =
        (η ^ 2) •
          ((frontierExtractor 1 : ChainVector T → ℝ) ∘ qNorm) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, comp_apply, qNorm]
    rw [frontierExtractor_scaling]
    rw [normalizeCLM_apply]
  rw [hFun]
  rw [iteratedFDeriv_const_smul_apply
    (((frontierExtractor_contDiff 1).comp hqNorm).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt), norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
  exact mul_le_mul_of_nonneg_left hComp (sq_nonneg η)

section AffineRemainder

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_clm_sub_const (L : F →L[ℝ] ℝ) (a y : F) :
    fderiv ℝ (fun w : F ↦ L (w - a)) y = L := by
  exact (L.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const a)).fderiv

theorem iteratedFDeriv_clm_sub_const_one (L : F →L[ℝ] ℝ) (a : F) :
    iteratedFDeriv ℝ 1 (fun y : F ↦ L (y - a)) a =
      (continuousMultilinearCurryFin1 ℝ F ℝ).symm L := by
  ext m
  rw [iteratedFDeriv_one_apply, fderiv_clm_sub_const]
  rfl

theorem iteratedFDeriv_clm_sub_const_two (L : F →L[ℝ] ℝ) (a : F) :
    iteratedFDeriv ℝ 2 (fun y : F ↦ L (y - a)) a = 0 := by
  have hf : (fun y : F ↦ fderiv ℝ (fun w : F ↦ L (w - a)) y) =
      fun _ : F ↦ L := by
    funext y
    exact fderiv_clm_sub_const L a y
  ext m
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ
    (fun y : F ↦ fderiv ℝ (fun w : F ↦ L (w - a)) y) a) (m 0))
      (m 1) = 0
  rw [hf]
  simp

theorem iteratedFDeriv_clm_sub_const_three (L : F →L[ℝ] ℝ) (a : F) :
    iteratedFDeriv ℝ 3 (fun y : F ↦ L (y - a)) a = 0 := by
  have hf : (fun y : F ↦ fderiv ℝ (fun w : F ↦ L (w - a)) y) =
      fun _ : F ↦ L := by
    funext y
    exact fderiv_clm_sub_const L a y
  ext m
  simp only [iteratedFDeriv_succ_apply_right]
  change (((fderiv ℝ (fun y : F ↦ fderiv ℝ
    (fun y : F ↦ fderiv ℝ (fun w : F ↦ L (w - a)) y) y) a)
      (Fin.init (Fin.init m) 0)) (Fin.init m 1)) (m 2) = 0
  rw [hf]
  simp

theorem iteratedFDeriv_clm_sub_const_eq_zero
    {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3)
    (L : F →L[ℝ] ℝ) (a : F) :
    iteratedFDeriv ℝ n (fun y : F ↦ L (y - a)) a = 0 := by
  interval_cases n
  · exact iteratedFDeriv_clm_sub_const_two L a
  · exact iteratedFDeriv_clm_sub_const_three L a

def affineRemainder (g : F → ℝ) (a : F) : F → ℝ :=
  fun y ↦ g y - g a - fderiv ℝ g a (y - a)

theorem affineRemainder_contDiff {g : F → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : F) : ContDiff ℝ ∞ (affineRemainder g a) := by
  unfold affineRemainder
  exact (hg.sub contDiff_const).sub
    ((fderiv ℝ g a).contDiff.comp (contDiff_id.sub contDiff_const))

@[simp]
theorem affineRemainder_apply_self (g : F → ℝ) (a : F) :
    affineRemainder g a a = 0 := by
  simp [affineRemainder]

theorem fderiv_affineRemainder_self {g : F → ℝ}
    (hg : DifferentiableAt ℝ g a) :
    fderiv ℝ (affineRemainder g a) a = 0 := by
  let L : F →L[ℝ] ℝ := fderiv ℝ g a
  have hg' : HasFDerivAt g L a := by
    simpa [L] using hg.hasFDerivAt
  have hc : HasFDerivAt (fun _ : F ↦ g a) (0 : F →L[ℝ] ℝ) a :=
    hasFDerivAt_const (x := a) (c := g a)
  have hlin : HasFDerivAt (fun y : F ↦ L (y - a)) L a :=
    L.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a)
  have hFun : affineRemainder g a =
      (g - (fun _ : F ↦ g a)) - (fun y : F ↦ L (y - a)) := by
    funext y
    rfl
  have hrem : HasFDerivAt (affineRemainder g a) (L - 0 - L) a := by
    rw [hFun]
    exact (hg'.sub hc).sub hlin
  simpa using hrem.fderiv

theorem iteratedFDeriv_affineRemainder_eq
    {g : F → ℝ} (hg : ContDiff ℝ ∞ g)
    {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3) (a : F) :
    iteratedFDeriv ℝ n (affineRemainder g a) a =
      iteratedFDeriv ℝ n g a := by
  let L : F →L[ℝ] ℝ := fderiv ℝ g a
  have hgAt : ContDiffAt ℝ n g a := (hg.of_le
    (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hcAt : ContDiffAt ℝ n (fun _ : F ↦ g a) a := contDiffAt_const
  have hlinSmooth : ContDiff ℝ ∞ (fun y : F ↦ L (y - a)) :=
    L.contDiff.comp (contDiff_id.sub contDiff_const)
  have hlinAt : ContDiffAt ℝ n (fun y : F ↦ L (y - a)) a :=
    (hlinSmooth.of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hFun : affineRemainder g a =
      (g - (fun _ : F ↦ g a)) - (fun y : F ↦ L (y - a)) := by
    funext y
    rfl
  rw [hFun]
  calc
    iteratedFDeriv ℝ n
        ((g - (fun _ : F ↦ g a)) - (fun y : F ↦ L (y - a))) a =
        iteratedFDeriv ℝ n (g - (fun _ : F ↦ g a)) a -
          iteratedFDeriv ℝ n (fun y : F ↦ L (y - a)) a :=
      iteratedFDeriv_sub_apply (hgAt.sub hcAt) hlinAt
    _ = (iteratedFDeriv ℝ n g a -
          iteratedFDeriv ℝ n (fun _ : F ↦ g a) a) -
          iteratedFDeriv ℝ n (fun y : F ↦ L (y - a)) a := by
      rw [iteratedFDeriv_sub_apply hgAt hcAt]
    _ = iteratedFDeriv ℝ n g a := by
      rw [show iteratedFDeriv ℝ n (fun _ : F ↦ g a) a = 0 by
        have hconst := congrFun
          (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := F) (n := n)
            (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn2)) (g a)) a
        simpa using hconst]
      rw [show iteratedFDeriv ℝ n (fun y : F ↦ L (y - a)) a = 0 by
        exact iteratedFDeriv_clm_sub_const_eq_zero hn2 hn3 L a]
      simp

/-- Composition estimate that keeps the first derivative of the outer map
separate.  This prevents a dimension-dependent first-derivative bound from
contaminating the higher-order remainder terms. -/
theorem norm_iteratedFDeriv_comp_le_affine_remainder
    {g : F → ℝ} {f : E → F} {n : ℕ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hn2 : 2 ≤ n) (hn3 : n ≤ 3) (x : E)
    {C D L Fn : ℝ} (hC0 : 0 ≤ C) (hL0 : 0 ≤ L)
    (hHigher : ∀ r : ℕ, 2 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r g (f x)‖ ≤ C)
    (hInner : ∀ r : ℕ, 1 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r f x‖ ≤ D ^ r)
    (hFirst : ‖fderiv ℝ g (f x)‖ ≤ L)
    (hTopInner : ‖iteratedFDeriv ℝ n f x‖ ≤ Fn) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      Nat.factorial n * C * D ^ n + L * Fn := by
  let a : F := f x
  let Lmap : F →L[ℝ] ℝ := fderiv ℝ g a
  let rem : F → ℝ := affineRemainder g a
  have hremSmooth : ContDiff ℝ ∞ rem := affineRemainder_contDiff hg a
  have hremBound : ∀ r : ℕ, r ≤ n →
      ‖iteratedFDeriv ℝ r rem a‖ ≤ C := by
    intro r hr
    rcases lt_trichotomy r 1 with hrlt | hre | hrgt
    · have hr0 : r = 0 := by omega
      subst r
      rw [norm_iteratedFDeriv_zero]
      simp [rem]
      exact hC0
    · subst r
      rw [norm_iteratedFDeriv_one]
      rw [show fderiv ℝ rem a = 0 by
        exact fderiv_affineRemainder_self
          (hg.differentiable (by norm_num) a)]
      simpa using hC0
    · have hr2 : 2 ≤ r := by omega
      rw [show iteratedFDeriv ℝ r rem a = iteratedFDeriv ℝ r g a by
        exact iteratedFDeriv_affineRemainder_eq hg hr2 (hr.trans hn3) a]
      exact hHigher r hr2 hr
  have hRemComp :
      ‖iteratedFDeriv ℝ n (rem ∘ f) x‖ ≤
        Nat.factorial n * C * D ^ n := by
    exact norm_iteratedFDeriv_comp_le hremSmooth hf
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top) x
      hremBound hInner
  have hLinearComp :
      ‖iteratedFDeriv ℝ n (Lmap ∘ f) x‖ ≤ L * Fn := by
    calc
      ‖iteratedFDeriv ℝ n (Lmap ∘ f) x‖ ≤
          ‖Lmap‖ * ‖iteratedFDeriv ℝ n f x‖ :=
        Lmap.norm_iteratedFDeriv_comp_left
          ((hf.of_le (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)
          le_rfl
      _ ≤ L * Fn := by gcongr
  let c : ℝ := g a - Lmap a
  have hFun : g ∘ f = (rem ∘ f) + (Lmap ∘ f) + (fun _ : E ↦ c) := by
    funext y
    simp only [Pi.add_apply, comp_apply, rem, affineRemainder, c, Lmap, a]
    rw [map_sub]
    ring
  have hRemAt : ContDiffAt ℝ n (rem ∘ f) x :=
    ((hremSmooth.comp hf).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hLinAt : ContDiffAt ℝ n (Lmap ∘ f) x :=
    ((Lmap.contDiff.comp hf).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hConstAt : ContDiffAt ℝ n (fun _ : E ↦ c) x := contDiffAt_const
  rw [hFun]
  have hTopAdd :
      iteratedFDeriv ℝ n
          (((rem ∘ f) + (Lmap ∘ f)) + (fun _ : E ↦ c)) x =
        iteratedFDeriv ℝ n ((rem ∘ f) + (Lmap ∘ f)) x +
          iteratedFDeriv ℝ n (fun _ : E ↦ c) x :=
    iteratedFDeriv_add_apply (hRemAt.add hLinAt) hConstAt
  rw [hTopAdd]
  rw [show iteratedFDeriv ℝ n (fun _ : E ↦ c) x = 0 by
    have hconst := congrFun
      (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E) (n := n)
        (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn2)) c) x
    simpa using hconst]
  rw [add_zero]
  have hInnerAdd :
      iteratedFDeriv ℝ n ((rem ∘ f) + (Lmap ∘ f)) x =
        iteratedFDeriv ℝ n (rem ∘ f) x +
          iteratedFDeriv ℝ n (Lmap ∘ f) x :=
    iteratedFDeriv_add_apply hRemAt hLinAt
  rw [hInnerAdd]
  exact (norm_add_le _ _).trans (add_le_add hRemComp hLinearComp)

end AffineRemainder

theorem norm_iteratedFDeriv_scaledChain_one_le
    {T : ℕ} (z : ChainVector T) :
    ‖iteratedFDeriv ℝ 1
        (scaledChain 1 : ChainVector T → ℝ) z‖ ≤
      23 * Real.sqrt T := by
  rw [norm_iteratedFDeriv_one]
  rw [← toDual_gradient]
  have hnorm := (InnerProductSpace.toDual ℝ (ChainVector T)).norm_map
    (gradient (scaledChain 1 : ChainVector T → ℝ) z)
  rw [hnorm]
  simpa using norm_scaledChain_gradient_le (η := (1 : ℝ)) (by norm_num) z

theorem exists_visibleChain_base_bounds :
    ∃ CA : ℝ, 0 ≤ CA ∧
      (∀ {T : ℕ}, 0 < T → ∀ z : ChainVector T,
        ‖iteratedFDeriv ℝ 1
            (visibleChain 1 : ChainVector T → ℝ) z‖ ≤
          CA * Real.sqrt T) ∧
      (∀ {T : ℕ} (r : ℕ), 2 ≤ r → r ≤ 3 → ∀ z : ChainVector T,
        ‖iteratedFDeriv ℝ r
            (visibleChain 1 : ChainVector T → ℝ) z‖ ≤ CA) := by
  obtain ⟨Cext, hCext0, hCext⟩ :=
    exists_common_bound_frontierExtractor_three
  obtain ⟨C2, hC20, hC2⟩ := exists_scaledChain_second_bound
  obtain ⟨C3, hC30, hC3⟩ := exists_scaledChain_third_bound
  let CA : ℝ := 23 + Cext + C2 + C3
  have hCA0 : 0 ≤ CA := by dsimp [CA]; positivity
  refine ⟨CA, hCA0, ?_, ?_⟩
  · intro T hT z
    have hsAt : ContDiffAt ℝ 1
      (scaledChain 1 : ChainVector T → ℝ) z :=
      (scaledChain_contDiff 1).contDiffAt.of_le
        (show (1 : ℕ∞) ≤ ∞ by simp)
    have heAt : ContDiffAt ℝ 1
      (frontierExtractor 1 : ChainVector T → ℝ) z :=
      (frontierExtractor_contDiff 1).contDiffAt.of_le
        (show (1 : ℕ∞) ≤ ∞ by simp)
    have hSub := iteratedFDeriv_sub_apply hsAt heAt
    have hVisible : (visibleChain 1 : ChainVector T → ℝ) =
        (scaledChain 1 : ChainVector T → ℝ) - frontierExtractor 1 := rfl
    rw [hVisible, hSub]
    calc
      ‖iteratedFDeriv ℝ 1 (scaledChain 1 : ChainVector T → ℝ) z -
          iteratedFDeriv ℝ 1 (frontierExtractor 1) z‖ ≤
          ‖iteratedFDeriv ℝ 1 (scaledChain 1 : ChainVector T → ℝ) z‖ +
            ‖iteratedFDeriv ℝ 1 (frontierExtractor 1) z‖ := norm_sub_le _ _
      _ ≤ 23 * Real.sqrt T + Cext := by
        apply add_le_add
        · exact norm_iteratedFDeriv_scaledChain_one_le z
        · have he := hCext (T := T) (η := (1 : ℝ))
            (by norm_num) 1 (by norm_num) z
          norm_num at he ⊢
          exact he
      _ ≤ CA * Real.sqrt T := by
        have hsqrt : 1 ≤ Real.sqrt T := by
          rw [Real.one_le_sqrt]
          exact_mod_cast hT
        dsimp [CA]
        nlinarith [mul_nonneg hCext0 (sub_nonneg.mpr hsqrt),
          mul_nonneg hC20 (Real.sqrt_nonneg T),
          mul_nonneg hC30 (Real.sqrt_nonneg T)]
  · intro T r hr2 hr3 z
    have hSub :
        iteratedFDeriv ℝ r
            ((scaledChain 1 : ChainVector T → ℝ) - frontierExtractor 1) z =
          iteratedFDeriv ℝ r
              (scaledChain 1 : ChainVector T → ℝ) z -
            iteratedFDeriv ℝ r (frontierExtractor 1) z := by
      interval_cases r
      · exact iteratedFDeriv_sub_apply
          ((scaledChain_contDiff 1).of_le
            (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
          ((frontierExtractor_contDiff 1).of_le
            (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
      · exact iteratedFDeriv_sub_apply
          ((scaledChain_contDiff 1).of_le
            (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
          ((frontierExtractor_contDiff 1).of_le
            (show (3 : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
    have hVisible : (visibleChain 1 : ChainVector T → ℝ) =
        (scaledChain 1 : ChainVector T → ℝ) - frontierExtractor 1 := rfl
    rw [hVisible, hSub]
    calc
      ‖iteratedFDeriv ℝ r (scaledChain 1 : ChainVector T → ℝ) z -
          iteratedFDeriv ℝ r (frontierExtractor 1) z‖ ≤
          ‖iteratedFDeriv ℝ r (scaledChain 1 : ChainVector T → ℝ) z‖ +
            ‖iteratedFDeriv ℝ r (frontierExtractor 1) z‖ := norm_sub_le _ _
      _ ≤ (if r = 2 then C2 else C3) + Cext := by
        gcongr
        · by_cases hr : r = 2
          · subst r
            simpa using hC2 T (by norm_num : (1 : ℝ) ≠ 0) z
          · have hrEq : r = 3 := by omega
            subst r
            simpa using hC3 T (by norm_num : (0 : ℝ) < 1) z
        · have he := hCext (T := T) (η := (1 : ℝ))
            (by norm_num) r hr3 z
          norm_num at he ⊢
          exact he
      _ ≤ CA := by
        dsimp [CA]
        split_ifs <;> linarith

/-- Quantitative higher-order composition estimate for the visible part of
the chain.  The affine part of the outer map is charged only against the top
derivative of the normalized inner map.  This is the mechanism that keeps
the dimension-dependent first derivative from entering every Faà di Bruno
term. -/
theorem norm_iteratedFDeriv_visibleChain_comp_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T n : ℕ} {η CA D Fn : ℝ}
    {q : E → ChainVector T} (hq : ContDiff ℝ ∞ q)
    (hn2 : 2 ≤ n) (hn3 : n ≤ 3) (z : E)
    (hCA0 : 0 ≤ CA)
    (hHigher : ∀ r : ℕ, 2 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r
          (visibleChain 1 : ChainVector T → ℝ)
          (((normalizeCLM η) ∘ q) z)‖ ≤ CA)
    (hFirst : ‖fderiv ℝ
        (visibleChain 1 : ChainVector T → ℝ)
        (((normalizeCLM η) ∘ q) z)‖ ≤ CA * Real.sqrt T)
    (hInner : ∀ r : ℕ, 1 ≤ r → r ≤ n →
      ‖iteratedFDeriv ℝ r ((normalizeCLM η) ∘ q) z‖ ≤ D ^ r)
    (hTopInner : ‖iteratedFDeriv ℝ n
        ((normalizeCLM η) ∘ q) z‖ ≤ Fn) :
    ‖iteratedFDeriv ℝ n
        ((visibleChain η : ChainVector T → ℝ) ∘ q) z‖ ≤
      η ^ 2 *
        (Nat.factorial n * CA * D ^ n +
          (CA * Real.sqrt T) * Fn) := by
  let qNorm : E → ChainVector T := (normalizeCLM η) ∘ q
  have hqNorm : ContDiff ℝ ∞ qNorm :=
    (normalizeCLM η).contDiff.comp hq
  have hComp := norm_iteratedFDeriv_comp_le_affine_remainder
    (visibleChain_contDiff 1) hqNorm hn2 hn3 z
    hCA0 (mul_nonneg hCA0 (Real.sqrt_nonneg T))
    (by simpa [qNorm] using hHigher)
    (by simpa [qNorm] using hInner)
    (by simpa [qNorm] using hFirst)
    (by simpa [qNorm] using hTopInner)
  have hFun :
      ((visibleChain η : ChainVector T → ℝ) ∘ q) =
        (η ^ 2) • ((visibleChain 1 : ChainVector T → ℝ) ∘ qNorm) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, comp_apply, qNorm]
    rw [visibleChain_scaling, normalizeCLM_apply]
  rw [hFun]
  rw [iteratedFDeriv_const_smul_apply
    (((visibleChain_contDiff 1).comp hqNorm).of_le
      (show (n : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt), norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
  exact mul_le_mul_of_nonneg_left hComp (sq_nonneg η)

/-- First-order companion to
`norm_iteratedFDeriv_visibleChain_comp_le`. -/
theorem norm_iteratedFDeriv_visibleChain_comp_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {η CA D : ℝ}
    {q : E → ChainVector T} (hq : ContDiff ℝ ∞ q) (z : E)
    (hFirst : ‖fderiv ℝ
        (visibleChain 1 : ChainVector T → ℝ)
        (((normalizeCLM η) ∘ q) z)‖ ≤ CA * Real.sqrt T)
    (hInner : ‖fderiv ℝ ((normalizeCLM η) ∘ q) z‖ ≤ D) :
    ‖iteratedFDeriv ℝ 1
        ((visibleChain η : ChainVector T → ℝ) ∘ q) z‖ ≤
      η ^ 2 * ((CA * Real.sqrt T) * D) := by
  let qNorm : E → ChainVector T := (normalizeCLM η) ∘ q
  have hqNorm : ContDiff ℝ ∞ qNorm :=
    (normalizeCLM η).contDiff.comp hq
  have hOuterDiff : DifferentiableAt ℝ
      (visibleChain 1 : ChainVector T → ℝ) (qNorm z) :=
    (visibleChain_contDiff 1).differentiable (by norm_num) (qNorm z)
  have hInnerDiff : DifferentiableAt ℝ qNorm z :=
    hqNorm.differentiable (by norm_num) z
  have hFun :
      ((visibleChain η : ChainVector T → ℝ) ∘ q) =
        (η ^ 2) • ((visibleChain 1 : ChainVector T → ℝ) ∘ qNorm) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, comp_apply, qNorm]
    rw [visibleChain_scaling, normalizeCLM_apply]
  rw [norm_iteratedFDeriv_one, hFun]
  rw [fderiv_const_smul (hOuterDiff.comp z hInnerDiff), norm_smul]
  rw [fderiv_comp (f := qNorm) z hOuterDiff hInnerDiff]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
  calc
    η ^ 2 *
        ‖(fderiv ℝ (visibleChain 1 : ChainVector T → ℝ) (qNorm z)).comp
          (fderiv ℝ qNorm z)‖ ≤
        η ^ 2 *
          (‖fderiv ℝ (visibleChain 1 : ChainVector T → ℝ) (qNorm z)‖ *
            ‖fderiv ℝ qNorm z‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ η ^ 2 * ((CA * Real.sqrt T) * D) := by
      have hFirst' :
          ‖fderiv ℝ (visibleChain 1 : ChainVector T → ℝ) (qNorm z)‖ ≤
            CA * Real.sqrt T := by
        simpa [qNorm] using hFirst
      have hInner' : ‖fderiv ℝ qNorm z‖ ≤ D := by
        simpa [qNorm] using hInner
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
      exact mul_le_mul hFirst' hInner' (norm_nonneg _)
        ((norm_nonneg _).trans hFirst')

end
end BilevelLowerBound
