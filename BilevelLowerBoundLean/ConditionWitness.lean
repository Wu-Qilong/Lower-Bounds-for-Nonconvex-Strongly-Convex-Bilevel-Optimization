/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.HardObjectiveRegularity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sharp lower-level condition-number witnesses

This module upgrades the uniform regularity estimates for the concrete hard
instance to pointwise lower-level Hessian certificates.  It first computes
the exact Hessian of the unperturbed `(z,v)` slice, and then constructs a
strict full-progress point at which the compensated frontier block is locally
zero.  These facts provide the lower and upper witnesses used in the
condition-number comparison.
-/

open Filter Function Real Set
open scoped ContDiff Topology RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-! ## Exact Hessian of the unperturbed lower slice -/

theorem iteratedFDeriv_scaledNormSq_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : κ ≠ 0) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (scaledNormSq κ : E → ℝ) z m =
      (1 / κ) * inner ℝ (m 0) (m 1) := by
  have hfun : (scaledNormSq κ : E → ℝ) =
      (2 * κ)⁻¹ • (fun y : E ↦ ‖y‖ ^ 2) := by
    funext y
    simp [scaledNormSq, div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
  simp only [smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_norm_sq_two_apply]
  field_simp [hκ]

theorem iteratedFDeriv_halfSquare_two_apply
    (v : ℝ) (m : Fin 2 → ℝ) :
    iteratedFDeriv ℝ 2 halfSquare v m = (m 0) * (m 1) := by
  have hfun : halfSquare =
      (1 / 2 : ℝ) • (fun y : ℝ ↦ ‖y‖ ^ 2) := by
    funext y
    simp [halfSquare, Real.norm_eq_abs, sq_abs]
  rw [hfun, iteratedFDeriv_const_smul_apply
    (((contDiff_norm_sq ℝ).of_le
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt)]
  simp only [smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_norm_sq_two_apply]
  simp
  ring

def fixedNegativeInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) : ℝ :=
  -inner ℝ x z

theorem fixedNegativeInner_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) :
    ContDiff ℝ ∞ (fixedNegativeInner x : E → ℝ) := by
  let L : E →L[ℝ] ℝ := -(innerSL ℝ x)
  have hfun : (fixedNegativeInner x : E → ℝ) = L := by
    funext y
    simp [fixedNegativeInner, L, innerSL_apply_apply]
  rw [hfun]
  exact L.contDiff

theorem fderiv_fixedNegativeInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) :
    fderiv ℝ (fixedNegativeInner x : E → ℝ) z =
      -(innerSL ℝ x) := by
  let L : E →L[ℝ] ℝ := -(innerSL ℝ x)
  have hfun : (fixedNegativeInner x : E → ℝ) = L := by
    funext y
    simp [fixedNegativeInner, L, innerSL_apply_apply]
  rw [hfun]
  exact L.fderiv

theorem iteratedFDeriv_fixedNegativeInner_two_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x z : E) :
    iteratedFDeriv ℝ 2 (fixedNegativeInner x : E → ℝ) z = 0 := by
  ext m
  rw [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fun y : E ↦
    fderiv ℝ (fixedNegativeInner x : E → ℝ) y) z) (m 0)) (m 1) = 0
  have hfd : (fun y : E ↦
      fderiv ℝ (fixedNegativeInner x : E → ℝ) y) =
      fun _ : E ↦ -(innerSL ℝ x) := by
    funext y
    exact fderiv_fixedNegativeInner x y
  rw [hfd]
  simp

def lowerBaseSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (x : E) : E × ℝ → ℝ :=
  ((scaledNormSq κ) ∘ (ContinuousLinearMap.fst ℝ E ℝ)) +
    ((fixedNegativeInner x) ∘ (ContinuousLinearMap.fst ℝ E ℝ)) +
      (halfSquare ∘ (ContinuousLinearMap.snd ℝ E ℝ))

@[simp] theorem lowerBaseSlice_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (x : E) (p : E × ℝ) :
    lowerBaseSlice κ x p =
      ‖p.1‖ ^ 2 / (2 * κ) - inner ℝ x p.1 +
        (1 / 2 : ℝ) * p.2 ^ 2 := by
  rfl

theorem lowerBaseSlice_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (κ : ℝ) (x : E) :
    ContDiff ℝ ∞ (lowerBaseSlice κ x) := by
  exact
    (((scaledNormSq_contDiff κ).comp contDiff_fst).add
      ((fixedNegativeInner_contDiff x).comp contDiff_fst)).add
        (halfSquare_contDiff.comp contDiff_snd)

set_option maxHeartbeats 800000 in
-- The exact formula expands three second-derivative compositions on a product.
theorem iteratedFDeriv_lowerBaseSlice_two_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : κ ≠ 0) (x : E) (p : E × ℝ)
    (m : Fin 2 → E × ℝ) :
    iteratedFDeriv ℝ 2 (lowerBaseSlice κ x) p m =
      (1 / κ) * inner ℝ (m 0).1 (m 1).1 + (m 0).2 * (m 1).2 := by
  let Lz : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let Lv : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let A : E × ℝ → ℝ := (scaledNormSq κ) ∘ Lz
  let B : E × ℝ → ℝ := (fixedNegativeInner x) ∘ Lz
  let C : E × ℝ → ℝ := halfSquare ∘ Lv
  have hA : ContDiff ℝ ∞ A := (scaledNormSq_contDiff κ).comp Lz.contDiff
  have hB : ContDiff ℝ ∞ B := (fixedNegativeInner_contDiff x).comp Lz.contDiff
  have hC : ContDiff ℝ ∞ C := halfSquare_contDiff.comp Lv.contDiff
  have hAAt : ContDiffAt ℝ 2 A p :=
    (hA.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hBAt : ContDiffAt ℝ 2 B p :=
    (hB.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hCAt : ContDiffAt ℝ 2 C p :=
    (hC.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  change iteratedFDeriv ℝ 2 ((A + B) + C) p m = _
  rw [show iteratedFDeriv ℝ 2 ((A + B) + C) p =
      iteratedFDeriv ℝ 2 (A + B) p + iteratedFDeriv ℝ 2 C p by
        exact iteratedFDeriv_add_apply (hAAt.add hBAt) hCAt,
    show iteratedFDeriv ℝ 2 (A + B) p =
      iteratedFDeriv ℝ 2 A p + iteratedFDeriv ℝ 2 B p by
        exact iteratedFDeriv_add_apply hAAt hBAt]
  simp only [add_apply]
  rw [Lz.iteratedFDeriv_comp_right (scaledNormSq_contDiff κ) p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lz.iteratedFDeriv_comp_right (fixedNegativeInner_contDiff x) p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top),
    Lv.iteratedFDeriv_comp_right halfSquare_contDiff p
      (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_scaledNormSq_two_apply hκ,
    iteratedFDeriv_fixedNegativeInner_two_eq_zero,
    iteratedFDeriv_halfSquare_two_apply]
  simp [Lz, Lv]

theorem lowerBaseSlice_diagonal_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : κ ≠ 0) (x : E) (p w : E × ℝ) :
    iteratedFDeriv ℝ 2 (lowerBaseSlice κ x) p (fun _ ↦ w) =
      (1 / κ) * ‖w.1‖ ^ 2 + w.2 ^ 2 := by
  rw [iteratedFDeriv_lowerBaseSlice_two_apply hκ]
  rw [real_inner_self_eq_norm_sq]
  ring

theorem lowerBaseSlice_coercive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : 1 ≤ κ) (x : E) (p w : E × ℝ) :
    (1 / κ) * ‖w‖ ^ 2 ≤
      iteratedFDeriv ℝ 2 (lowerBaseSlice κ x) p (fun _ ↦ w) := by
  have hkpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  rw [lowerBaseSlice_diagonal_hessian hkpos.ne']
  rw [Prod.norm_def]
  rcases max_cases ‖w.1‖ ‖w.2‖ with hz | hv
  · rw [hz.1]
    exact le_add_of_nonneg_right (sq_nonneg w.2)
  · rw [hv.1]
    have hinv : 1 / κ ≤ 1 := by
      exact (div_le_one hkpos).2 hκ
    have hinv0 : 0 ≤ 1 / κ := by positivity
    have hvnorm : ‖w.2‖ ^ 2 = w.2 ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    calc
      (1 / κ) * ‖w.2‖ ^ 2 ≤ 1 * ‖w.2‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
      _ = w.2 ^ 2 := by rw [one_mul, hvnorm]
      _ ≤ (1 / κ) * ‖w.1‖ ^ 2 + w.2 ^ 2 :=
        le_add_of_nonneg_left (mul_nonneg hinv0 (sq_nonneg _))

theorem norm_iteratedFDeriv_lowerBaseSlice_two_le_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {κ : ℝ} (hκ : 1 ≤ κ) (x : E) (p : E × ℝ) :
    ‖iteratedFDeriv ℝ 2 (lowerBaseSlice κ x) p‖ ≤ 2 := by
  have hkpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  rw [Real.norm_eq_abs, iteratedFDeriv_lowerBaseSlice_two_apply hkpos.ne']
  have hinv : 1 / κ ≤ 1 := (div_le_one hkpos).2 hκ
  have hinv0 : 0 ≤ 1 / κ := by positivity
  have hz := abs_real_inner_le_norm (m 0).1 (m 1).1
  have hv : |(m 0).2 * (m 1).2| ≤ ‖m 0‖ * ‖m 1‖ := by
    rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _
  have hzm : |(1 / κ) * inner ℝ (m 0).1 (m 1).1| ≤
      ‖m 0‖ * ‖m 1‖ := by
    rw [abs_mul, abs_of_nonneg hinv0]
    calc
      (1 / κ) * |inner ℝ (m 0).1 (m 1).1| ≤
          1 * (‖(m 0).1‖ * ‖(m 1).1‖) := by gcongr
      _ ≤ ‖m 0‖ * ‖m 1‖ := by
        rw [one_mul]
        exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
          (norm_nonneg ((m 1).1)) (norm_nonneg (m 0))
  calc
    |(1 / κ) * inner ℝ (m 0).1 (m 1).1 + (m 0).2 * (m 1).2| ≤
        |(1 / κ) * inner ℝ (m 0).1 (m 1).1| +
          |(m 0).2 * (m 1).2| := abs_add_le _ _
    _ ≤ 2 * (‖m 0‖ * ‖m 1‖) := by linarith
    _ = 2 * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_two]

/-! ## A strict full-progress point -/

def constantChainVector {T : ℕ} (η : ℝ) : ChainVector T :=
  chainVectorOfFun fun _ ↦ η

@[simp] theorem constantChainVector_apply
    {T : ℕ} (η : ℝ) (i : Fin T) :
    constantChainVector η i = η := rfl

theorem norm_constantChainVector {T : ℕ} (η : ℝ) :
    ‖constantChainVector (T := T) η‖ = |η| * Real.sqrt T := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (abs_nonneg η) (Real.sqrt_nonneg T))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
    Real.sq_sqrt (by positivity), sq_abs]
  simp [constantChainVector]
  ring

theorem one_half_lt_softScale_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (z : E) (hz : ‖z‖ ≤ R) :
    (1 / 2 : ℝ) < softScale R z := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hzsq : ‖z‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - ‖z‖), norm_nonneg z]
  have hratio : ‖z‖ ^ 2 / R ^ 2 ≤ 1 :=
    (div_le_one hR2).2 hzsq
  have hradpos : 0 < 1 + ‖z‖ ^ 2 / R ^ 2 := by positivity
  have hradlt : 1 + ‖z‖ ^ 2 / R ^ 2 < 4 := by linarith
  have hsqrt : Real.sqrt (1 + ‖z‖ ^ 2 / R ^ 2) < 2 := by
    have := Real.sqrt_lt_sqrt hradpos.le hradlt
    norm_num at this ⊢
    exact this
  unfold softScale
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ (Real.sqrt_pos.2 hradpos)).2
  nlinarith

def fullProgressWitness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (η : ℝ) (J : ChainVector T →L[ℝ] E) : E :=
  J (constantChainVector η)

theorem hiddenProbe_fullProgressWitness_coordinate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T))
    (i : Fin T) :
    η / 2 <
      |hiddenProbe (hardRadius η T) L (fullProgressWitness η J) i| := by
  let w : ChainVector T := constantChainVector η
  let z : E := J w
  have hw : ‖w‖ = η * Real.sqrt T := by
    rw [norm_constantChainVector, abs_of_pos hη]
  have hz : ‖z‖ ≤ ‖w‖ := by
    calc
      ‖z‖ = ‖J w‖ := rfl
      _ ≤ ‖J‖ * ‖w‖ := J.le_opNorm w
      _ ≤ 1 * ‖w‖ := by gcongr
      _ = ‖w‖ := one_mul _
  have hzR : ‖z‖ ≤ hardRadius η T := by
    calc
      ‖z‖ ≤ ‖w‖ := hz
      _ = η * Real.sqrt T := hw
      _ ≤ 230 * η * Real.sqrt T := by
        have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
        nlinarith [mul_nonneg hη.le hsqrt]
      _ = hardRadius η T := rfl
  have hs : (1 / 2 : ℝ) < softScale (hardRadius η T) z :=
    one_half_lt_softScale_of_norm_le (hardRadius_pos hη hT) z hzR
  have hright : L (J w) = w := by
    have heval := congrArg
      (fun K : ChainVector T →L[ℝ] ChainVector T ↦ K w) hLJ
    simpa using heval
  have hcoord :
      hiddenProbe (hardRadius η T) L (fullProgressWitness η J) i =
        softScale (hardRadius η T) z * η := by
    change (L (softProjection (hardRadius η T) z)) i = _
    rw [softProjection_eq_softScale_smul, map_smul, hright]
    simp [w]
  rw [hcoord, abs_mul, abs_of_pos hη,
    abs_of_pos (softScale_pos (hardRadius_pos hη hT).ne' z)]
  nlinarith

theorem hiddenProbe_fullProgressWitness_progress
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T)) :
    progress (η / 2)
      (hiddenProbe (hardRadius η T) L (fullProgressWitness η J)) = T := by
  let q := hiddenProbe (hardRadius η T) L (fullProgressWitness η J)
  have hlarge : ∀ i : Fin T, η / 2 < |q i| :=
    hiddenProbe_fullProgressWitness_coordinate hη hT L J hJ hLJ
  have hle := progress_le_dim (η / 2) q
  by_contra hne
  have hlt : progress (η / 2) q < T := Nat.lt_of_le_of_ne hle hne
  let i : Fin T := ⟨progress (η / 2) q, hlt⟩
  have hindex := (progress_le_iff.mp (le_refl (progress (η / 2) q)))
    i (hlarge i)
  dsimp [i] at hindex
  omega

/-! ## Local flatness after strict full progress -/

theorem eventually_frontierExtractor_eq_zero_of_strict_full_progress
    {T : ℕ} {η : ℝ} (hη : 0 < η) (q : ChainVector T)
    (hstrict : ∀ i : Fin T, η / 2 < |q i|) :
    (frontierExtractor η : ChainVector T → ℝ) =ᶠ[nhds q]
      (fun _ ↦ 0) := by
  have hi (i : Fin T) :
      {y : ChainVector T | η / 2 < |y i|} ∈ nhds q := by
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (hstrict i)
  have hall : (⋂ i : Fin T,
      {y : ChainVector T | η / 2 < |y i|}) ∈ nhds q := by
    rw [Filter.iInter_mem]
    exact hi
  filter_upwards [hall] with y hy
  have hylarge : ∀ i : Fin T, η / 2 < |y i| := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hy
  have hfull : progress (η / 2) y = T := by
    have hle := progress_le_dim (η / 2) y
    by_contra hne
    have hlt : progress (η / 2) y < T := Nat.lt_of_le_of_ne hle hne
    let i : Fin T := ⟨progress (η / 2) y, hlt⟩
    have hindex := (progress_le_iff.mp (le_refl (progress (η / 2) y)))
      i (hylarge i)
    dsimp [i] at hindex
    omega
  exact frontierExtractor_eq_zero_of_full_progress hη y hfull

theorem eventually_hardFrontierMap_eq_zero_at_fullProgressWitness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T)) :
    hardFrontierMap η L =ᶠ[nhds (fullProgressWitness η J)]
      (fun _ ↦ 0) := by
  let z := fullProgressWitness η J
  let q := hiddenProbe (hardRadius η T) L z
  have hstrict : ∀ i : Fin T, η / 2 < |q i| :=
    hiddenProbe_fullProgressWitness_coordinate hη hT L J hJ hLJ
  have houter :=
    eventually_frontierExtractor_eq_zero_of_strict_full_progress hη q hstrict
  have hprobe : Continuous (hiddenProbe (hardRadius η T) L) :=
    (hiddenProbe_contDiff (hardRadius_pos hη hT).ne' L).continuous
  exact houter.comp_tendsto hprobe.continuousAt

theorem eventually_compensatedPair_eq_zero_of_eventually_theta_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} {θ : E → ℝ} {z : E} (v : ℝ)
    (hθ : θ =ᶠ[nhds z] (fun _ ↦ 0)) :
    compensatedPair η θ =ᶠ[nhds (z, v)] (fun _ ↦ 0) := by
  have hθprod := hθ.comp_tendsto
    (continuousAt_fst : Tendsto (fun p : E × ℝ ↦ p.1)
      (nhds (z, v)) (nhds z))
  filter_upwards [hθprod] with p hp
  have hp' : θ p.1 = 0 := by simpa using hp
  simp [compensatedPair, compensatedBlock, hp']

theorem iteratedFDeriv_compensatedPair_two_eq_zero_at_fullProgressWitness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T))
    (v : ℝ) :
    iteratedFDeriv ℝ 2
      (compensatedPair η (hardFrontierMap η L))
      (fullProgressWitness η J, v) = 0 := by
  have hlocal := eventually_compensatedPair_eq_zero_of_eventually_theta_zero
    (η := η) v
    (eventually_hardFrontierMap_eq_zero_at_fullProgressWitness
      hη hT L J hJ hLJ)
  have hjet := hlocal.iteratedFDeriv (𝕜 := ℝ) 2
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hjet.eq_of_nhds

/-! ## The actual lower slice -/

def hardLowerSlice
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (κ η : ℝ) (L : E →L[ℝ] ChainVector T)
    (x : E) : E × ℝ → ℝ :=
  lowerPopulationSum (lowerBaseSlice κ x)
    (compensatedPair η (hardFrontierMap η L))

@[simp] theorem hardLowerSlice_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (κ η : ℝ) (L : E →L[ℝ] ChainVector T)
    (x : E) (p : E × ℝ) :
    hardLowerSlice κ η L x p =
      populationLower κ η (hardFrontierMap η L) x p.1 p.2 := by
  rfl

theorem hardLowerSlice_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {η : ℝ} (hη : 0 < η) (hT : 0 < T)
    (κ : ℝ) (L : E →L[ℝ] ChainVector T) (x : E) :
    ContDiff ℝ ∞ (hardLowerSlice κ η L x) :=
  lowerPopulationSum_contDiff (lowerBaseSlice_contDiff κ x)
    (compensatedPair_contDiff hη.ne'
      (hardFrontierMap_contDiff hη hT L))

theorem hardLowerSlice_flat_witness_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {κ η : ℝ} (hκ : κ ≠ 0) (hη : 0 < η) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hJ : ‖J‖ ≤ 1)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T))
    (x : E) (v : ℝ) (m : Fin 2 → E × ℝ) :
    iteratedFDeriv ℝ 2 (hardLowerSlice κ η L x)
      (fullProgressWitness η J, v) m =
        (1 / κ) * inner ℝ (m 0).1 (m 1).1 + (m 0).2 * (m 1).2 := by
  have hbase : ContDiff ℝ ∞ (lowerBaseSlice κ x) :=
    lowerBaseSlice_contDiff κ x
  have hpert : ContDiff ℝ ∞
      (compensatedPair η (hardFrontierMap η L)) :=
    compensatedPair_contDiff hη.ne'
      (hardFrontierMap_contDiff hη hT L)
  have hbaseAt : ContDiffAt ℝ 2 (lowerBaseSlice κ x)
      (fullProgressWitness η J, v) :=
    (hbase.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  have hpertAt : ContDiffAt ℝ 2
      (compensatedPair η (hardFrontierMap η L))
      (fullProgressWitness η J, v) :=
    (hpert.of_le (show (2 : ℕ∞) ≤ ∞ from mod_cast le_top)).contDiffAt
  unfold hardLowerSlice lowerPopulationSum
  rw [iteratedFDeriv_add_apply hbaseAt hpertAt,
    iteratedFDeriv_compensatedPair_two_eq_zero_at_fullProgressWitness
      hη hT L J hJ hLJ, add_zero]
  exact iteratedFDeriv_lowerBaseSlice_two_apply hκ x _ m

set_option maxHeartbeats 800000 in
-- The certificate bundles all quantified lower slices and perturbation bounds.
/-- Uniform lower-slice regularity and strong-convexity constants for the
actual hard instance. -/
theorem exists_hardLowerSlice_certificates :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {κ η : ℝ}, 1 ≤ κ → 0 < η → η ≤ 1 → 0 < T →
        ∀ {L : E →L[ℝ] ChainVector T}, ‖L‖ ≤ 1 →
        (∀ (x : E) (p : E × ℝ),
          ‖iteratedFDeriv ℝ 2 (hardLowerSlice κ η L x) p‖ ≤
            2 + CHess * η) ∧
        (CHess * η ≤ 1 / (2 * κ) →
          ∀ (x : E) (p w : E × ℝ),
            (1 / (2 * κ)) * ‖w‖ ^ 2 ≤
              iteratedFDeriv ℝ 2 (hardLowerSlice κ η L x) p
                (fun _ ↦ w)) := by
  obtain ⟨CHess, Cthird, hCHess, hCthird, hreg⟩ :=
    exists_hard_compensated_pair_regularities
  refine ⟨CHess, hCHess, ?_⟩
  intro E _ _ T κ η hκ hη hη1 hT L hL
  have hpert : ContDiff ℝ ∞
      (compensatedPair η (hardFrontierMap η L)) :=
    compensatedPair_contDiff hη.ne'
      (hardFrontierMap_contDiff hη hT L)
  have hpert2 (p : E × ℝ) :
      ‖iteratedFDeriv ℝ 2
        (compensatedPair η (hardFrontierMap η L)) p‖ ≤ CHess * η :=
    (hreg hη hη1 hT hL p).1
  constructor
  · intro x p
    exact lowerPopulationSum_second_bound
      (lowerBaseSlice_contDiff κ x) hpert
      (norm_iteratedFDeriv_lowerBaseSlice_two_le_two hκ x) hpert2 p
  · intro hsmall x p w
    have hkpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
    have hraw := lowerPopulationSum_strong_hessian_certificate
      (lowerBaseSlice_contDiff κ x) hpert
      (show 0 ≤ 1 / κ by positivity) (mul_nonneg hCHess hη.le)
      (show CHess * η ≤ 1 / κ by
        calc CHess * η ≤ 1 / (2 * κ) := hsmall
          _ ≤ 1 / κ := by
            field_simp [hkpos.ne']
            nlinarith)
      (lowerBaseSlice_coercive hκ x) hpert2 p w
    have hcoef : 1 / (2 * κ) ≤ 1 / κ - CHess * η := by
      have hsplit : 1 / κ = 2 * (1 / (2 * κ)) := by
        field_simp [hkpos.ne']
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)).trans hraw

/-! ## Sharp moduli and the condition-number comparison -/

def HasLowerHessianModulus
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ) (muG : ℝ) : Prop :=
  ∀ x p w, muG * ‖w‖ ^ 2 ≤
    iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w)

def HasLowerHessianUpperBound
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ) (Ly : ℝ) : Prop :=
  ∀ x p, ‖iteratedFDeriv ℝ 2 (G x) p‖ ≤ Ly

/-- `muGAct` is the largest valid uniform directional-Hessian lower bound. -/
def IsSharpLowerHessianModulus
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ) (muGAct : ℝ) : Prop :=
  HasLowerHessianModulus G muGAct ∧
    ∀ a, HasLowerHessianModulus G a → a ≤ muGAct

/-- `Ly` is the smallest valid uniform Hessian operator-norm upper bound. -/
def IsSharpLowerHessianUpperBound
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ) (Ly : ℝ) : Prop :=
  HasLowerHessianUpperBound G Ly ∧
    ∀ a, HasLowerHessianUpperBound G a → Ly ≤ a

theorem rightInverse_image_constant_one_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E)
    (hLJ : L.comp J = ContinuousLinearMap.id ℝ (ChainVector T)) :
    J (constantChainVector (T := T) 1) ≠ 0 := by
  let e : ChainVector T := constantChainVector 1
  have hright : L (J e) = e := by
    have heval := congrArg
      (fun K : ChainVector T →L[ℝ] ChainVector T ↦ K e) hLJ
    simpa using heval
  intro hzero
  have hezero : e = 0 := by rw [← hright, hzero, map_zero]
  let i : Fin T := ⟨0, hT⟩
  have hcoord := congrArg (fun q : ChainVector T ↦ q i) hezero
  simp [e, i] at hcoord

set_option maxHeartbeats 1000000 in
-- The theorem combines the global certificates with two explicit flat-point witnesses.
/-- For the concrete hard lower objective, the sharp lower-level condition
number is within a universal factor of the construction parameter `kappa`.
The right-inverse hypotheses are exactly the algebraic properties supplied by
the transpose of the hidden Stiefel frame. -/
theorem exists_hardLower_condition_number_comparison :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        {T : ℕ} {κ η : ℝ}, 1 ≤ κ → 0 < η → η ≤ 1 → 0 < T →
        ∀ (L : E →L[ℝ] ChainVector T) (J : ChainVector T →L[ℝ] E),
        ‖L‖ ≤ 1 → ‖J‖ ≤ 1 →
        L.comp J = ContinuousLinearMap.id ℝ (ChainVector T) →
        CHess * η ≤ 1 / (2 * κ) →
        ∀ muGAct Ly : ℝ,
        IsSharpLowerHessianModulus (hardLowerSlice κ η L) muGAct →
        IsSharpLowerHessianUpperBound (hardLowerSlice κ η L) Ly →
        κ ≤ Ly / muGAct ∧
          Ly / muGAct ≤ 2 * (2 + CHess) * κ := by
  obtain ⟨CHess, hCHess, hcert⟩ := exists_hardLowerSlice_certificates
  refine ⟨CHess, hCHess, ?_⟩
  intro E _ _ T κ η hκ hη hη1 hT L J hL hJ hLJ hsmall muGAct Ly
    hmuGAct hLy
  have hkpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hcertHere := hcert hκ hη hη1 hT hL
  have hmuCert : HasLowerHessianModulus
      (hardLowerSlice κ η L) (1 / (2 * κ)) := by
    intro x p w
    exact hcertHere.2 hsmall x p w
  have hLyCert : HasLowerHessianUpperBound
      (hardLowerSlice κ η L) (2 + CHess) := by
    intro x p
    calc
      ‖iteratedFDeriv ℝ 2 (hardLowerSlice κ η L x) p‖ ≤
          2 + CHess * η := hcertHere.1 x p
      _ ≤ 2 + CHess := by
        have hmul := mul_le_of_le_one_right hCHess hη1
        linarith
  have hmuGActLower : 1 / (2 * κ) ≤ muGAct :=
    hmuGAct.2 _ hmuCert
  have hLyUpper : Ly ≤ 2 + CHess := hLy.2 _ hLyCert
  let e : ChainVector T := constantChainVector 1
  let u : E := J e
  have hu : u ≠ 0 :=
    rightInverse_image_constant_one_ne_zero hT L J hLJ
  let z0 : E := fullProgressWitness η J
  let wz : E × ℝ := (u, 0)
  have hmuGActWitness := hmuGAct.1 (0 : E) (z0, 0) wz
  have hflatZ :
      iteratedFDeriv ℝ 2 (hardLowerSlice κ η L (0 : E))
        (z0, 0) (fun _ ↦ wz) = (1 / κ) * ‖u‖ ^ 2 := by
    rw [hardLowerSlice_flat_witness_hessian hkpos.ne' hη hT
      L J hJ hLJ]
    simp [wz]
  rw [hflatZ] at hmuGActWitness
  have hwzNorm : ‖wz‖ = ‖u‖ := by
    simp [wz, Prod.norm_def]
  rw [hwzNorm] at hmuGActWitness
  have huSq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hmuGActUpper : muGAct ≤ 1 / κ := by
    nlinarith
  let wv : E × ℝ := (0, 1)
  let H := iteratedFDeriv ℝ 2 (hardLowerSlice κ η L (0 : E)) (z0, 0)
  have hHeval : H (fun _ ↦ wv) = 1 := by
    dsimp [H]
    rw [hardLowerSlice_flat_witness_hessian hkpos.ne' hη hT
      L J hJ hLJ]
    simp [wv]
  have hHop := H.le_opNorm (fun _ : Fin 2 ↦ wv)
  have hwvNorm : ‖wv‖ = 1 := by simp [wv, Prod.norm_def]
  rw [Real.norm_eq_abs, hHeval, abs_one, Fin.prod_univ_two,
    hwvNorm, one_mul, mul_one] at hHop
  have hLyAt : ‖H‖ ≤ Ly := hLy.1 (0 : E) (z0, 0)
  have hLyLower : 1 ≤ Ly := hHop.trans hLyAt
  have hmuGActPos : 0 < muGAct :=
    lt_of_lt_of_le (by positivity) hmuGActLower
  exact lower_condition_number_sandwich hκ hmuGActPos hCHess
    hmuGActLower hmuGActUpper hLyLower hLyUpper

/-! ## Specialization to an orthonormal hidden frame -/

/-- The transpose of an orthonormal hidden frame.  A linear isometry
`J : R^T -> E` represents the synthesis map `q |-> U q`; its adjoint is
the analysis map `z |-> U^T z`. -/
def hiddenFrameTranspose
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (J : ChainVector T →ₗᵢ[ℝ] E) : E →L[ℝ] ChainVector T :=
  J.toContinuousLinearMap.adjoint

@[simp] theorem hiddenFrameTranspose_comp_frame
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    (hiddenFrameTranspose J).comp J.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (ChainVector T) := by
  ext q
  have hq := congrArg
    (fun K : ChainVector T →L[ℝ] ChainVector T ↦ K q)
    J.adjoint_comp_self
  simp [hiddenFrameTranspose] at hq ⊢

theorem norm_hiddenFrameTranspose_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    ‖hiddenFrameTranspose J‖ ≤ 1 := by
  let i : Fin T := ⟨0, hT⟩
  let e : ChainVector T := EuclideanSpace.single i (1 : ℝ)
  have he : e ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun q : ChainVector T ↦ q i) hzero
    simp [e] at hcoord
  let _ : Nontrivial (ChainVector T) := ⟨⟨e, 0, he⟩⟩
  calc
    ‖hiddenFrameTranspose J‖ = ‖J.toContinuousLinearMap‖ := by
      exact ContinuousLinearMap.adjoint.norm_map J.toContinuousLinearMap
    _ ≤ 1 := J.norm_toContinuousLinearMap_le

set_option maxHeartbeats 1000000 in
-- This is the exact Stiefel-frame form used by the rotated hard instance.
/-- The sharp condition number of the actual hard lower problem is comparable
to `kappa` when the hidden columns form an orthonormal frame. -/
theorem exists_orthonormalFrame_hardLower_condition_number_comparison :
    ∃ CHess : ℝ, 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {κ η : ℝ},
        1 ≤ κ → 0 < η → η ≤ 1 → 0 < T →
        ∀ (J : ChainVector T →ₗᵢ[ℝ] E),
        CHess * η ≤ 1 / (2 * κ) →
        ∀ muGAct Ly : ℝ,
        IsSharpLowerHessianModulus
            (hardLowerSlice κ η (hiddenFrameTranspose J)) muGAct →
        IsSharpLowerHessianUpperBound
            (hardLowerSlice κ η (hiddenFrameTranspose J)) Ly →
        κ ≤ Ly / muGAct ∧
          Ly / muGAct ≤ 2 * (2 + CHess) * κ := by
  obtain ⟨CHess, hCHess, hmain⟩ :=
    exists_hardLower_condition_number_comparison
  refine ⟨CHess, hCHess, ?_⟩
  intro E _ _ _ T κ η hκ hη hη1 hT J hsmall muGAct Ly hmuGAct hLy
  exact hmain hκ hη hη1 hT
    (hiddenFrameTranspose J) J.toContinuousLinearMap
    (norm_hiddenFrameTranspose_le hT J)
    J.norm_toContinuousLinearMap_le
    (hiddenFrameTranspose_comp_frame J) hsmall muGAct Ly hmuGAct hLy

end

end BilevelLowerBound
