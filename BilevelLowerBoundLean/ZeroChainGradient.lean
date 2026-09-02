/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.ZeroChainBounds

/-!
# Gradient coordinates of the finite zero chain

This module lifts the scalar link estimates to coordinate derivatives of the
finite chain.  The proof works with scalar lines through the Euclidean chain
space, avoiding any ambiguity between the sup norm and the paper's Euclidean
norm.
-/

open scoped ContDiff Gradient InnerProductSpace Topology
open InnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-- Adjoin a zero initial coordinate to a direction vector. -/
def withInitialZero {T : ℕ} (v : ChainVector T) : Fin (T + 1) → ℝ :=
  Fin.cases 0 v

theorem withInitialOne_add_smul {T : ℕ} (q v : ChainVector T) (t : ℝ)
    (k : Fin (T + 1)) :
    withInitialOne (q + t • v) k =
      withInitialOne q k + t * withInitialZero v k := by
  cases k using Fin.cases with
  | zero => simp [withInitialOne, withInitialZero]
  | succ i => simp [withInitialOne, withInitialZero]

theorem unscaledChain_line (T : ℕ) (q v : ChainVector T) (t : ℝ) :
    unscaledChain (q + t • v) =
      ∑ i : Fin T,
        chainQ
          (withInitialOne q i.castSucc +
            t * withInitialZero v i.castSucc)
          (q i + t * v i) := by
  unfold unscaledChain
  apply Finset.sum_congr rfl
  intro i _hi
  rw [withInitialOne_add_smul]
  congr 1

/-- Directional derivative of the full chain as a sum of link derivatives. -/
theorem unscaledChain_line_deriv {T : ℕ} (q v : ChainVector T) :
    deriv (fun t : ℝ ↦ unscaledChain (q + t • v)) 0 =
      ∑ i : Fin T,
        (deriv
            (fun x ↦ chainQ x (q i))
            (withInitialOne q i.castSucc) *
          withInitialZero v i.castSucc +
        deriv
            (fun y ↦ chainQ (withInitialOne q i.castSucc) y)
            (q i) * v i) := by
  have hFun :
      (fun t : ℝ ↦ unscaledChain (q + t • v)) =
        fun t : ℝ ↦ ∑ i : Fin T,
          chainQ
            (withInitialOne q i.castSucc +
              t * withInitialZero v i.castSucc)
            (q i + t * v i) := by
    funext t
    exact unscaledChain_line T q v t
  change deriv (fun t : ℝ ↦ unscaledChain (q + t • v)) 0 = _
  rw [hFun, deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    exact chainQ_affine_deriv
      (withInitialOne q i.castSucc) (q i)
      (withInitialZero v i.castSucc) (v i)
  · intro i _hi
    exact ContDiffAt.differentiableAt (ContDiff.contDiffAt (chainQ_comp_contDiff
      (contDiff_const.add (contDiff_id.mul contDiff_const))
      (contDiff_const.add (contDiff_id.mul contDiff_const)))) (by simp)

/-- For a differentiable scalar function, a gradient coordinate is the
derivative along the corresponding Euclidean coordinate line. -/
theorem gradient_coordinate_eq_line_deriv {T : ℕ}
    (f : ChainVector T → ℝ) (q : ChainVector T)
    (hf : DifferentiableAt ℝ f q) (j : Fin T) :
    gradient f q j =
      deriv (fun t : ℝ ↦ f (q + t • EuclideanSpace.single j 1)) 0 := by
  let e : ChainVector T := EuclideanSpace.single j 1
  have hLine : HasDerivAt (fun t : ℝ ↦ q + t • e) e 0 := by
    simpa only [one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add q
  have hComp := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hd := hComp.deriv
  have hEval : (fderiv ℝ f q) e = gradient f q j := by
    rw [← toDual_gradient]
    change inner ℝ (gradient f q) e = _
    dsimp [e]
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) (gradient f q)
  rw [hEval] at hd
  exact hd.symm

theorem unscaledChain_gradient_coordinate {T : ℕ}
    (q : ChainVector T) (j : Fin T) :
    gradient (unscaledChain : ChainVector T → ℝ) q j =
      ∑ i : Fin T,
        (deriv
            (fun x ↦ chainQ x (q i))
            (withInitialOne q i.castSucc) *
          withInitialZero (EuclideanSpace.single j 1) i.castSucc +
        deriv
            (fun y ↦ chainQ (withInitialOne q i.castSucc) y)
            (q i) * EuclideanSpace.single j 1 i) := by
  rw [gradient_coordinate_eq_line_deriv
    (unscaledChain : ChainVector T → ℝ) q
    (ContDiffAt.differentiableAt unscaledChain_contDiff.contDiffAt (by simp)) j]
  exact unscaledChain_line_deriv q (EuclideanSpace.single j 1)

theorem withInitialZero_single_apply {T : ℕ} (i j : Fin T) :
    withInitialZero (EuclideanSpace.single j 1) i.castSucc =
      if i.val = j.val + 1 then 1 else 0 := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases i using Fin.cases with
    | zero => simp [withInitialZero]
    | succ k => simp [withInitialZero, Pi.single_apply, Fin.ext_iff]

theorem sum_abs_withInitialZero_single_le_one {T : ℕ} (j : Fin T) :
    ∑ i : Fin T,
      |withInitialZero (EuclideanSpace.single j 1) i.castSucc| ≤ 1 := by
  simp_rw [withInitialZero_single_apply]
  simp only [abs_ite, abs_one, abs_zero]
  by_cases hj : j.val + 1 < T
  · let k : Fin T := ⟨j.val + 1, hj⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b _hb hbk
      simp only [ite_eq_right_iff]
      intro heq
      exact (hbk (Fin.ext (by simpa [k] using heq))).elim
    · simp
  · have hNone : ∀ i : Fin T, i.val ≠ j.val + 1 := by
      intro i hi
      apply hj
      simpa [hi] using i.isLt
    simp [hNone]

theorem sum_abs_single_eq_one {T : ℕ} (j : Fin T) :
    ∑ i : Fin T, |EuclideanSpace.single j (1 : ℝ) i| = 1 := by
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    simp [hbj]
  · simp

theorem sum_mul_single {T : ℕ} (f : Fin T → ℝ) (j : Fin T) :
    ∑ i : Fin T, f i * EuclideanSpace.single j (1 : ℝ) i = f j := by
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    simp [hbj]
  · simp

theorem sum_mul_withInitialZero_single {T : ℕ} (f : Fin T → ℝ)
    (j : Fin T) :
    ∑ i : Fin T,
      f i * withInitialZero (EuclideanSpace.single j 1) i.castSucc =
      if h : j.val + 1 < T then f ⟨j.val + 1, h⟩ else 0 := by
  simp_rw [withInitialZero_single_apply]
  by_cases hj : j.val + 1 < T
  · simp only [hj, dite_true]
    let k : Fin T := ⟨j.val + 1, hj⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b _hb hbk
      by_cases hb : b.val = j.val + 1
      · exact (hbk (Fin.ext (by simpa [k] using hb))).elim
      · simp [hb]
    · simp
  · simp only [hj, dite_false]
    have hNone : ∀ i : Fin T, i.val ≠ j.val + 1 := by
      intro i hi
      apply hj
      simpa [hi] using i.isLt
    simp [hNone]

theorem unscaledChain_gradient_coordinate_eq {T : ℕ}
    (q : ChainVector T) (j : Fin T) :
    gradient (unscaledChain : ChainVector T → ℝ) q j =
      deriv (fun y ↦ chainQ (withInitialOne q j.castSucc) y) (q j) +
      if h : j.val + 1 < T then
        deriv (fun x ↦ chainQ x (q ⟨j.val + 1, h⟩)) (q j)
      else 0 := by
  rw [unscaledChain_gradient_coordinate, Finset.sum_add_distrib,
    sum_mul_withInitialZero_single, sum_mul_single]
  split
  · rename_i h
    rw [show withInitialOne q
        (⟨j.val + 1, h⟩ : Fin T).castSucc = q j by
      simp [withInitialOne]]
    ring
  · ring

theorem withInitialOne_castSucc_eq_of_index {T : ℕ} (q : ChainVector T)
    (i j : Fin T) (hij : i.val + 1 = j.val) :
    withInitialOne q j.castSucc = q i := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ k =>
      have hval : i.val = k.val := by simpa using hij
      have hik : i = k.castSucc := Fin.ext hval
      subst i
      simp [withInitialOne]

/-- The unscaled frontier coordinate has derivative at most `-1`. -/
theorem unscaledChain_frontier_gradient_le {T : ℕ}
    (q : ChainVector T) (j : Fin T)
    (hj : j.val = progress 1 q) :
    gradient (unscaledChain : ChainVector T → ℝ) q j ≤ -1 := by
  have hb : |q j| ≤ 1 := by
    apply abs_le_threshold_of_progress_le (le_refl (progress 1 q)) j
    omega
  have ha : 1 ≤ |withInitialOne q j.castSucc| := by
    by_cases hjZero : j.val = 0
    · have hjEq : j.castSucc = (0 : Fin (T + 1)) := Fin.ext hjZero
      rw [hjEq]
      simp [withInitialOne]
    · have hProgPos : 0 < progress 1 q := by omega
      obtain ⟨i, hi, hiProg⟩ := exists_coordinate_at_progress hProgPos
      have hij : i.val + 1 = j.val := by omega
      rw [withInitialOne_castSucc_eq_of_index q i j hij]
      exact hi.le
  have hCurrent :
      deriv (fun y ↦ chainQ (withInitialOne q j.castSucc) y) (q j) ≤ -1 :=
    chainQ_deriv_snd_le_neg_one ha hb
  rw [unscaledChain_gradient_coordinate_eq]
  split
  · rename_i hnext
    have hFollowing :
        deriv (fun x ↦ chainQ x (q ⟨j.val + 1, hnext⟩)) (q j) ≤ 0 :=
      chainQ_deriv_fst_nonpos _ _
    linarith
  · simpa using hCurrent

/-- Every coordinate of the unscaled-chain gradient is strictly smaller than `23`. -/
theorem abs_unscaledChain_gradient_coordinate_lt_twentyThree {T : ℕ}
    (q : ChainVector T) (j : Fin T) :
    |gradient (unscaledChain : ChainVector T → ℝ) q j| < 23 := by
  let A : ℝ := (447 / 100 : ℝ) * (207 / 50 : ℝ)
  let B : ℝ := 449 / 100
  rw [unscaledChain_gradient_coordinate]
  calc
    |∑ i : Fin T,
        (deriv (fun x ↦ chainQ x (q i))
            (withInitialOne q i.castSucc) *
          withInitialZero (EuclideanSpace.single j 1) i.castSucc +
        deriv (fun y ↦ chainQ (withInitialOne q i.castSucc) y)
            (q i) * EuclideanSpace.single j 1 i)|
        ≤ ∑ i : Fin T,
          |deriv (fun x ↦ chainQ x (q i))
              (withInitialOne q i.castSucc) *
            withInitialZero (EuclideanSpace.single j 1) i.castSucc +
          deriv (fun y ↦ chainQ (withInitialOne q i.castSucc) y)
              (q i) * EuclideanSpace.single j 1 i| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin T,
          (|deriv (fun x ↦ chainQ x (q i))
              (withInitialOne q i.castSucc) *
            withInitialZero (EuclideanSpace.single j 1) i.castSucc| +
          |deriv (fun y ↦ chainQ (withInitialOne q i.castSucc) y)
              (q i) * EuclideanSpace.single j 1 i|) := by
            exact Finset.sum_le_sum fun i _hi ↦ abs_add_le _ _
    _ ≤ ∑ i : Fin T,
          (A * |withInitialZero (EuclideanSpace.single j 1) i.castSucc| +
            B * |EuclideanSpace.single j 1 i|) := by
            apply Finset.sum_le_sum
            intro i _hi
            rw [abs_mul, abs_mul]
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right
                (abs_chainQ_deriv_fst_le
                  (withInitialOne q i.castSucc) (q i)) (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right
                (abs_chainQ_deriv_snd_le
                  (withInitialOne q i.castSucc) (q i)) (abs_nonneg _)
    _ = A * (∑ i : Fin T,
          |withInitialZero (EuclideanSpace.single j 1) i.castSucc|) +
        B * (∑ i : Fin T, |EuclideanSpace.single j 1 i|) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.mul_sum]
    _ ≤ A * 1 + B * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (sum_abs_withInitialZero_single_le_one j) (by positivity)
          · rw [sum_abs_single_eq_one]
    _ < 23 := by
      norm_num [A, B]

/-- Euclidean gradient bound for the unscaled chain. -/
theorem norm_unscaledChain_gradient_le {T : ℕ} (q : ChainVector T) :
    ‖gradient (unscaledChain : ChainVector T → ℝ) q‖ ≤
      23 * Real.sqrt T := by
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt
        (∑ i : Fin T,
          ‖gradient (unscaledChain : ChainVector T → ℝ) q i‖ ^ 2)
        ≤ Real.sqrt (∑ _i : Fin T, (23 : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro i _hi
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_unscaledChain_gradient_coordinate_lt_twentyThree q i).le 2
    _ = Real.sqrt ((T : ℝ) * (23 : ℝ) ^ 2) := by simp
    _ = 23 * Real.sqrt T := by
      rw [Real.sqrt_mul (Nat.cast_nonneg T), Real.sqrt_sq_eq_abs]
      norm_num
      ring

theorem fderiv_scaledChain_one {T : ℕ} {η : ℝ} (hη : η ≠ 0)
    (z : ChainVector T) :
    fderiv ℝ (scaledChain η : ChainVector T → ℝ) z =
      η • fderiv ℝ (unscaledChain : ChainVector T → ℝ) (normalize η z) := by
  have h := iteratedFDeriv_scaledChain_one hη z
  ext v
  let m : Fin 1 → ChainVector T := fun _ ↦ v
  have hv := congrArg (fun L ↦ L m) h
  simpa [m] using hv

theorem gradient_scaledChain_one {T : ℕ} {η : ℝ} (hη : η ≠ 0)
    (z : ChainVector T) :
    gradient (scaledChain η : ChainVector T → ℝ) z =
      η • gradient (unscaledChain : ChainVector T → ℝ) (normalize η z) := by
  apply (toDual ℝ (ChainVector T)).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  exact fderiv_scaledChain_one hη z

/-- Coordinatewise `ℓ∞` gradient estimate in the scaled standard-chain lemma. -/
theorem abs_scaledChain_gradient_coordinate_le {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (j : Fin T) :
    |gradient (scaledChain η : ChainVector T → ℝ) z j| ≤ 23 * η := by
  rw [gradient_scaledChain_one hη.ne' z]
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hη]
  calc
    η * |gradient (unscaledChain : ChainVector T → ℝ) (normalize η z) j|
        ≤ η * 23 := mul_le_mul_of_nonneg_left
          (abs_unscaledChain_gradient_coordinate_lt_twentyThree
            (normalize η z) j).le hη.le
    _ = 23 * η := by ring

/-- Euclidean gradient estimate in the scaled standard-chain lemma. -/
theorem norm_scaledChain_gradient_le {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) :
    ‖gradient (scaledChain η : ChainVector T → ℝ) z‖ ≤
      23 * η * Real.sqrt T := by
  rw [gradient_scaledChain_one hη.ne' z, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη]
  calc
    η * ‖gradient (unscaledChain : ChainVector T → ℝ) (normalize η z)‖
        ≤ η * (23 * Real.sqrt T) := mul_le_mul_of_nonneg_left
          (norm_unscaledChain_gradient_le (normalize η z)) hη.le
    _ = 23 * η * Real.sqrt T := by ring

/-- Scaled frontier-gradient estimate, with zero-based Lean coordinates.
The hypothesis `j.val = progress η z` is the paper's one-based relation
`j + 1 = prog_η(z) + 1`. -/
theorem scaledChain_frontier_gradient_le {T : ℕ} {η : ℝ}
    (hη : 0 < η) (z : ChainVector T) (j : Fin T)
    (hj : j.val = progress η z) :
    gradient (scaledChain η : ChainVector T → ℝ) z j ≤ -η := by
  have hProg : progress 1 (normalize η z) = progress η z := by
    simpa [normalize] using progress_div z 1 η hη
  have hFrontier := unscaledChain_frontier_gradient_le
    (normalize η z) j (by rw [hProg]; exact hj)
  rw [gradient_scaledChain_one hη.ne' z]
  simp only [PiLp.smul_apply, smul_eq_mul]
  nlinarith

end

end BilevelLowerBound
