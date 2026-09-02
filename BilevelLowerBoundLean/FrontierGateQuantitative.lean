/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.FrontierExtractorQuantitative

/-!
# Dimension-free quantitative bounds for the radial frontier gate

This module proves dimension-free operator-norm bounds through derivative
order three for the coordinatewise tail activation, its squared norm, the
radial frontier gate, and the complete frontier extractor.  In particular, it
discharges the gate hypothesis in
`norm_iteratedFDeriv_frontierExtractor_le_of_gate_bound`.
-/

open Filter Function Real Set
open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

def scaledCoordinateCLM {T : ℕ} (η : ℝ) (j : Fin T) :
    ChainVector T →L[ℝ] ℝ :=
  η⁻¹ • PiLp.proj 2 (fun _ : Fin T ↦ ℝ) j

@[simp]
theorem scaledCoordinateCLM_apply {T : ℕ} (η : ℝ) (j : Fin T)
    (z : ChainVector T) :
    scaledCoordinateCLM η j z = z j / η := by
  simp [scaledCoordinateCLM, div_eq_mul_inv, mul_comm]

theorem tailActivation_coordinate_eq_comp_scaledCoordinateCLM
    {T : ℕ} (η : ℝ) (i j : Fin T) (hij : i.val ≤ j.val) :
    (fun z : ChainVector T ↦ tailActivation η z i j) =
      coordinateGate ∘ scaledCoordinateCLM η j := by
  funext z
  rw [tailActivation_apply_of_le z i j hij]
  simp

theorem iteratedFDeriv_tailActivation_apply
    {T r : ℕ} (η : ℝ) (i : Fin T) (z : ChainVector T)
    (m : Fin r → ChainVector T) (j : Fin T) :
    (iteratedFDeriv ℝ r (tailActivation η · i) z m) j =
      if _hij : i.val ≤ j.val then
        iteratedFDeriv ℝ r coordinateGate (z j / η)
          (fun a ↦ m a j / η)
      else 0 := by
  let Pj : ChainVector T →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin T ↦ ℝ) j
  have hLeft := Pj.iteratedFDeriv_comp_left
    (x := z)
    ((tailActivation_contDiff η i).of_le
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top) |>.contDiffAt)
    (i := r) le_rfl
  have hEval :
      (iteratedFDeriv ℝ r (Pj ∘ (tailActivation η · i)) z) m =
        (iteratedFDeriv ℝ r (tailActivation η · i) z m) j := by
    rw [hLeft]
    rfl
  rw [← hEval]
  split_ifs with hij
  · rw [show Pj ∘ (tailActivation η · i) =
        coordinateGate ∘ scaledCoordinateCLM η j by
      exact tailActivation_coordinate_eq_comp_scaledCoordinateCLM η i j hij]
    rw [(scaledCoordinateCLM η j).iteratedFDeriv_comp_right
      coordinateGate_contDiff z
        (show (r : ℕ∞) ≤ ∞ from mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      scaledCoordinateCLM_apply]
    congr 1
    funext a
    exact scaledCoordinateCLM_apply η j (m a)
  · have hCoordZero : Pj ∘ (tailActivation η · i) =
        (fun _ : ChainVector T ↦ (0 : ℝ)) := by
      funext y
      change tailActivation η y i j = 0
      exact tailActivation_apply_of_lt y i j (Nat.lt_of_not_ge hij)
    rw [hCoordZero]
    simp

theorem abs_iteratedFDeriv_tailActivation_apply_le
    {T r : ℕ} {η K : ℝ} (hη : 0 < η) (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n coordinateGate t‖ ≤ K)
    (hr : r ≤ 3) (i : Fin T) (z : ChainVector T)
    (m : Fin r → ChainVector T) (j : Fin T) :
    |(iteratedFDeriv ℝ r (tailActivation η · i) z m) j| ≤
      K * (η⁻¹) ^ r * ∏ a : Fin r, |m a j| := by
  rw [iteratedFDeriv_tailActivation_apply]
  split_ifs with hij
  · have hOp := (iteratedFDeriv ℝ r coordinateGate (z j / η)).le_opNorm
        (fun a ↦ m a j / η)
    rw [Real.norm_eq_abs] at hOp
    calc
      |iteratedFDeriv ℝ r coordinateGate (z j / η)
          (fun a ↦ m a j / η)| ≤
          ‖iteratedFDeriv ℝ r coordinateGate (z j / η)‖ *
            ∏ a : Fin r, ‖m a j / η‖ := hOp
      _ ≤ K * ∏ a : Fin r, |m a j / η| := by
        gcongr
        · exact hK r hr _
        · rw [Real.norm_eq_abs, abs_div]
      _ = K * (η⁻¹) ^ r * ∏ a : Fin r, |m a j| := by
        simp_rw [abs_div, abs_of_pos hη, div_eq_mul_inv]
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
  · simp only [abs_zero]
    positivity

theorem sum_coordinate_product_sq_le
    {T r : ℕ} (hr0 : 0 < r) (hr3 : r ≤ 3)
    (m : Fin r → ChainVector T) :
    (∑ j : Fin T, (∏ a : Fin r, |m a j|) ^ 2) ≤
      ∏ a : Fin r, ‖m a‖ ^ 2 := by
  interval_cases r
  · simpa [Fin.prod_univ_succ, sq_abs,
      EuclideanSpace.real_norm_sq_eq]
  · simp [Fin.prod_univ_succ]
    calc
      (∑ j : Fin T, (|m 0 j| * |m 1 j|) ^ 2) ≤
          ∑ j : Fin T, |m 0 j| ^ 2 * ‖m 1‖ ^ 2 := by
        gcongr with j
        rw [mul_pow]
        gcongr
        have hj := PiLp.norm_apply_le (m 1) j
        rw [Real.norm_eq_abs] at hj
        exact hj
      _ = (∑ j : Fin T, |m 0 j| ^ 2) * ‖m 1‖ ^ 2 := by
        rw [Finset.sum_mul]
      _ = ‖m 0‖ ^ 2 * ‖m 1‖ ^ 2 := by
        simp only [sq_abs]
        rw [← EuclideanSpace.real_norm_sq_eq]
  · simp [Fin.prod_univ_succ]
    calc
      (∑ j : Fin T, (|m 0 j| * (|m 1 j| * |m 2 j|)) ^ 2) ≤
          ∑ j : Fin T, |m 0 j| ^ 2 * (‖m 1‖ ^ 2 * ‖m 2‖ ^ 2) := by
        gcongr with j
        rw [mul_pow, mul_pow]
        gcongr
        · have hj := PiLp.norm_apply_le (m 1) j
          rw [Real.norm_eq_abs] at hj
          exact hj
        · have hj := PiLp.norm_apply_le (m 2) j
          rw [Real.norm_eq_abs] at hj
          exact hj
      _ = (∑ j : Fin T, |m 0 j| ^ 2) *
          (‖m 1‖ ^ 2 * ‖m 2‖ ^ 2) := by
        rw [Finset.sum_mul]
      _ = ‖m 0‖ ^ 2 * (‖m 1‖ ^ 2 * ‖m 2‖ ^ 2) := by
        simp only [sq_abs]
        rw [← EuclideanSpace.real_norm_sq_eq]

theorem norm_iteratedFDeriv_tailActivation_le
    {T r : ℕ} {η K : ℝ} (hη : 0 < η) (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n coordinateGate t‖ ≤ K)
    (hr0 : 0 < r) (hr3 : r ≤ 3) (i : Fin T) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ r (tailActivation η · i) z‖ ≤
      K * (η⁻¹) ^ r := by
  let C : ℝ := K * (η⁻¹) ^ r
  have hC0 : 0 ≤ C :=
    mul_nonneg hK0 (pow_nonneg (inv_nonneg.mpr hη.le) r)
  apply ContinuousMultilinearMap.opNorm_le_bound hC0
  intro m
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  have hCoord : ∀ j : Fin T,
      |(iteratedFDeriv ℝ r (tailActivation η · i) z m) j| ≤
        C * ∏ a : Fin r, |m a j| := by
    intro j
    exact abs_iteratedFDeriv_tailActivation_apply_le
      hη hK0 hK hr3 i z m j
  calc
    Real.sqrt (∑ j : Fin T,
        (iteratedFDeriv ℝ r (tailActivation η · i) z m j) ^ 2) ≤
      Real.sqrt (C ^ 2 *
        ∑ j : Fin T, (∏ a : Fin r, |m a j|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _hj
        calc
          (iteratedFDeriv ℝ r (tailActivation η · i) z m j) ^ 2 =
              |(iteratedFDeriv ℝ r (tailActivation η · i) z m) j| ^ 2 :=
            (sq_abs _).symm
          _ ≤ (C * ∏ a : Fin r, |m a j|) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg _)
              (mul_nonneg hC0 (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _))).2
                (hCoord j)
          _ = C ^ 2 * (∏ a : Fin r, |m a j|) ^ 2 := by ring
    _ ≤ Real.sqrt (C ^ 2 * ∏ a : Fin r, ‖m a‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      gcongr
      exact sum_coordinate_product_sq_le hr0 hr3 m
    _ = Real.sqrt ((C * ∏ a : Fin r, ‖m a‖) ^ 2) := by
      congr 1
      simp only [C, mul_pow, Finset.prod_pow]
    _ = C * ∏ a : Fin r, ‖m a‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact mul_nonneg hC0 (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

theorem norm_iteratedFDeriv_bilinear_scaled_le_eight
    {D E F G : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {f : D → E} {g : D → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C Dconst a : ℝ} (hC0 : 0 ≤ C) (hD0 : 0 ≤ Dconst) (ha0 : 0 ≤ a)
    (n : ℕ) (hn : n ≤ 3) (x : D)
    (hC : ∀ r : ℕ, r ≤ 3 →
      ‖iteratedFDeriv ℝ r f x‖ ≤ C * a ^ r)
    (hD : ∀ r : ℕ, r ≤ 3 →
      ‖iteratedFDeriv ℝ r g x‖ ≤ Dconst * a ^ r) :
    ‖iteratedFDeriv ℝ n (fun y ↦ B (f y) (g y)) x‖ ≤
      8 * C * Dconst * a ^ n := by
  calc
    ‖iteratedFDeriv ℝ n (fun y ↦ B (f y) (g y)) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x
        (show (n : ℕ∞) ≤ ∞ from mod_cast le_top) hB
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (C * a ^ i) *
            (Dconst * a ^ (n - i)) := by
      gcongr with i hi
      · exact hC i (by
          have hi' := Finset.mem_range.1 hi
          omega)
      · exact hD (n - i) (by omega)
    _ = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * C * Dconst * a ^ n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := by
        have := Finset.mem_range.1 hi
        omega
      calc
        (n.choose i : ℝ) * (C * a ^ i) * (Dconst * a ^ (n - i)) =
            (n.choose i : ℝ) * C * Dconst *
              (a ^ i * a ^ (n - i)) := by ring
        _ = (n.choose i : ℝ) * C * Dconst * a ^ n := by
          rw [← pow_add, Nat.add_sub_of_le hin]
    _ ≤ 8 * C * Dconst * a ^ n := by
      interval_cases n <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith [mul_nonneg hC0 hD0, pow_nonneg ha0 0,
          pow_nonneg ha0 1, pow_nonneg ha0 2, pow_nonneg ha0 3]

theorem norm_iteratedFDeriv_tailActivationNormSq_le_of_norm
    {T r : ℕ} {η K : ℝ} (hη : 0 < η) (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n coordinateGate t‖ ≤ K)
    (hr : r ≤ 3) (i : Fin T) (z : ChainVector T)
    (hV : ‖tailActivation η z i‖ ≤ 1) :
    ‖iteratedFDeriv ℝ r (tailActivationNormSq η i) z‖ ≤
      8 * (1 + K) ^ 2 * (η⁻¹) ^ r := by
  have hOneK0 : 0 ≤ 1 + K := by linarith
  have hVJets : ∀ n : ℕ, n ≤ 3 →
      ‖iteratedFDeriv ℝ n (tailActivation η · i) z‖ ≤
        (1 + K) * (η⁻¹) ^ n := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      rw [norm_iteratedFDeriv_zero]
      simpa using hV.trans (by linarith : (1 : ℝ) ≤ 1 + K)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      exact (norm_iteratedFDeriv_tailActivation_le hη hK0 hK hnpos hn i z).trans
        (mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (inv_nonneg.mpr hη.le) n))
  have hBound := norm_iteratedFDeriv_bilinear_scaled_le_eight
    (innerSL ℝ : ChainVector T →L[ℝ] ChainVector T →L[ℝ] ℝ)
    (norm_innerSL_le ℝ) (tailActivation_contDiff η i)
    (tailActivation_contDiff η i) hOneK0 hOneK0
    (inv_nonneg.mpr hη.le)
    r hr z hVJets hVJets
  have hFun : tailActivationNormSq η i =
      fun y ↦ (innerSL ℝ) (tailActivation η y i)
        (tailActivation η y i) := by
    funext y
    simp [tailActivationNormSq, pow_two]
  rw [hFun]
  convert hBound using 1 <;> ring

theorem iteratedFDeriv_frontierLinkGate_eq_zero_of_three_quarters_lt
    {T r : ℕ} {η : ℝ} (i : Fin T) (z : ChainVector T)
    (hV : 3 / 4 < ‖tailActivation η z i‖) :
    iteratedFDeriv ℝ r (frontierLinkGate η · i) z = 0 := by
  have hCont : ContinuousAt
      (fun y : ChainVector T ↦ ‖tailActivation η y i‖) z :=
    (tailActivation_contDiff η i).continuous.norm.continuousAt
  have hEventually : ∀ᶠ y in nhds z,
      3 / 4 < ‖tailActivation η y i‖ :=
    hCont.tendsto.eventually (Ioi_mem_nhds hV)
  have hLocal : (frontierLinkGate η · i) =ᶠ[nhds z]
      (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hEventually] with y hy
    unfold frontierLinkGate
    apply frontierTransition_eq_zero_of_le_quarter
    linarith
  have hJet := hLocal.iteratedFDeriv (𝕜 := ℝ) r
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hJet.eq_of_nhds

theorem norm_iteratedFDeriv_frontierLinkGate_le
    {T r : ℕ} {η K Kρ : ℝ} (hη : 0 < η)
    (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, n ≤ 3 → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n coordinateGate t‖ ≤ K)
    (hKρ0 : 0 ≤ Kρ)
    (hKρ : ∀ n : ℕ, n ≤ 3 → ∀ s : ℝ,
      ‖iteratedFDeriv ℝ n frontierRadialProfile s‖ ≤ Kρ)
    (hr : r ≤ 3) (i : Fin T) (z : ChainVector T) :
    ‖iteratedFDeriv ℝ r (frontierLinkGate η · i) z‖ ≤
      (6 * Kρ * (8 * (1 + K) ^ 2) ^ 3) * (η⁻¹) ^ r := by
  let Cs : ℝ := 8 * (1 + K) ^ 2
  have hCs0 : 0 ≤ Cs := by positivity
  have hCs1 : 1 ≤ Cs := by
    dsimp [Cs]
    nlinarith [sq_nonneg (1 + K)]
  by_cases hsmall : ‖tailActivation η z i‖ ≤ 3 / 4
  · have hSBound : ∀ n : ℕ, 1 ≤ n → n ≤ r →
        ‖iteratedFDeriv ℝ n (tailActivationNormSq η i) z‖ ≤
          (Cs * η⁻¹) ^ n := by
      intro n hn1 hnr
      have hn3 : n ≤ 3 := hnr.trans hr
      have hRaw := norm_iteratedFDeriv_tailActivationNormSq_le_of_norm
        hη hK0 hK hn3 i z (hsmall.trans (by norm_num))
      calc
        ‖iteratedFDeriv ℝ n (tailActivationNormSq η i) z‖ ≤
            Cs * (η⁻¹) ^ n := by simpa [Cs] using hRaw
        _ ≤ (Cs * η⁻¹) ^ n := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (le_self_pow₀ hCs1 (by omega))
            (pow_nonneg (inv_nonneg.mpr hη.le) n)
    have hComp := norm_iteratedFDeriv_comp_le
      frontierRadialProfile_contDiff (tailActivationNormSq_contDiff η i)
      (show (r : ℕ∞) ≤ ∞ from mod_cast le_top) z
      (C := Kρ) (D := Cs * η⁻¹)
      (fun n hnr ↦ hKρ n (hnr.trans hr) _)
      hSBound
    rw [frontierLinkGate_eq_radialProfile_comp_tailActivationNormSq] 
    calc
      ‖iteratedFDeriv ℝ r
          (frontierRadialProfile ∘ tailActivationNormSq η i) z‖ ≤
          (Nat.factorial r : ℝ) * Kρ * (Cs * η⁻¹) ^ r := hComp
      _ ≤ (6 * Kρ * Cs ^ 3) * (η⁻¹) ^ r := by
        have hfac : (Nat.factorial r : ℝ) ≤ 6 := by
          interval_cases r <;> norm_num
        have hpow : Cs ^ r ≤ Cs ^ 3 := pow_le_pow_right₀ hCs1 hr
        have hcoef : (Nat.factorial r : ℝ) * Cs ^ r ≤ 6 * Cs ^ 3 :=
          calc
            (Nat.factorial r : ℝ) * Cs ^ r ≤ 6 * Cs ^ r := by
              gcongr
            _ ≤ 6 * Cs ^ 3 := by gcongr
        rw [mul_pow]
        calc
          (Nat.factorial r : ℝ) * Kρ * (Cs ^ r * (η⁻¹) ^ r) =
              ((Nat.factorial r : ℝ) * Cs ^ r) *
                (Kρ * (η⁻¹) ^ r) := by ring
          _ ≤ (6 * Cs ^ 3) * (Kρ * (η⁻¹) ^ r) := by
            exact mul_le_mul_of_nonneg_right hcoef
              (mul_nonneg hKρ0 (pow_nonneg (inv_nonneg.mpr hη.le) r))
          _ = (6 * Kρ * Cs ^ 3) * (η⁻¹) ^ r := by ring
      _ = (6 * Kρ * (8 * (1 + K) ^ 2) ^ 3) * (η⁻¹) ^ r := by
        rfl
  · have hzero :=
      iteratedFDeriv_frontierLinkGate_eq_zero_of_three_quarters_lt
        (r := r) i z (lt_of_not_ge hsmall)
    rw [hzero, norm_zero]
    positivity

/-- The radial frontier gate has one common dimension-free jet constant
through order three.  The constant is independent of the chain length and of
the link index. -/
theorem exists_common_bound_frontierLinkGate_three :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ {T : ℕ} {η : ℝ}, 0 < η → ∀ r : ℕ, r ≤ 3 →
        ∀ (i : Fin T) (z : ChainVector T),
          ‖iteratedFDeriv ℝ r (frontierLinkGate η · i) z‖ ≤
            Cg * (η⁻¹) ^ r := by
  obtain ⟨K, hK0, hK⟩ := exists_common_bound_coordinateGate_three
  obtain ⟨Kρ, hKρ0, hKρ⟩ :=
    exists_common_bound_frontierRadialProfile_three
  refine ⟨6 * Kρ * (8 * (1 + K) ^ 2) ^ 3, by positivity, ?_⟩
  intro T η hη r hr i z
  exact norm_iteratedFDeriv_frontierLinkGate_le
    hη hK0 hK hKρ0 hKρ hr i z

/-- The full frontier extractor has a common dimension-free jet constant
through order three, with the exact scale `eta^2 (eta^-1)^r` used in the hard
instance. -/
theorem exists_common_bound_frontierExtractor_three :
    ∃ Cext : ℝ, 0 ≤ Cext ∧
      ∀ {T : ℕ} {η : ℝ}, 0 < η → ∀ r : ℕ, r ≤ 3 →
        ∀ z : ChainVector T,
          ‖iteratedFDeriv ℝ r
              (frontierExtractor η : ChainVector T → ℝ) z‖ ≤
            Cext * η ^ 2 * (η⁻¹) ^ r := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_common_bound_frontierLinkGate_three
  obtain ⟨Cq, hCq0, hCq⟩ := exists_common_bound_chainQ_three
  refine ⟨8 * Cg * Cq, by positivity, ?_⟩
  intro T η hη r hr z
  exact norm_iteratedFDeriv_frontierExtractor_le_of_gate_bound
    hη hCg0 hCq0
    (fun n hn i y ↦ hCg hη n hn i y)
    (fun n hn i y ↦ norm_iteratedFDeriv_chainLink_le
      hη Cq hCq0 hCq hn i y)
    hr z

end
end BilevelLowerBound
