/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperExpectation

/-!
# Existence of the sharp lower-level Hessian constants

The paper defines the actual strong-convexity and lower-gradient smoothness
constants by an infimum/supremum over lower Hessians.  Earlier files proved
all estimates needed once sharp constants were supplied.  Here we close the
logical gap: completeness of `ℝ`, together with one valid global certificate
and the explicit flat-point witnesses, produces the two sharp constants.
-/

open Function Set

namespace BilevelLowerBound

noncomputable section

/-! ## One scale for all analytic smallness conditions -/

/-- The paper's `c_reg`: it enforces both frontier-value smallness and the
Hessian-perturbation condition. -/
def paperConstructionRegularityScale (Ctheta CHess : ℝ) : ℝ :=
  min (constructionRegularityScale CHess) (1 / (1 + Ctheta))

theorem paperConstructionRegularityScale_pos
    {Ctheta CHess : ℝ} (hCtheta : 0 ≤ Ctheta) (hCHess : 0 ≤ CHess) :
    0 < paperConstructionRegularityScale Ctheta CHess := by
  unfold paperConstructionRegularityScale
  exact lt_min (constructionRegularityScale_pos hCHess) (by positivity)

theorem paper_final_scale_implies_regularities
    {Ctheta CHess eta kappa : ℝ}
    (hCtheta : 0 ≤ Ctheta) (hCHess : 0 ≤ CHess)
    (hkappa : 1 ≤ kappa) (heta : 0 ≤ eta)
    (hetaSmall :
      eta ≤ paperConstructionRegularityScale Ctheta CHess / kappa) :
    eta ≤ 1 ∧ Ctheta * eta ≤ 1 ∧
      CHess * eta ≤ 1 / (2 * kappa) := by
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  have hregLe : paperConstructionRegularityScale Ctheta CHess ≤
      constructionRegularityScale CHess := min_le_left _ _
  have hetaHess : eta ≤ constructionRegularityScale CHess / kappa :=
    hetaSmall.trans (div_le_div_of_nonneg_right hregLe hkpos.le)
  have hbase := final_scale_implies_regularities hCHess hkappa heta hetaHess
  refine ⟨hbase.1, ?_, hbase.2⟩
  have hfrontLe : paperConstructionRegularityScale Ctheta CHess ≤
      1 / (1 + Ctheta) := min_le_right _ _
  have hetaFront : eta ≤ 1 / (1 + Ctheta) := by
    calc
      eta ≤ paperConstructionRegularityScale Ctheta CHess / kappa :=
        hetaSmall
      _ ≤ paperConstructionRegularityScale Ctheta CHess :=
        div_le_self
          (paperConstructionRegularityScale_pos hCtheta hCHess).le hkappa
      _ ≤ 1 / (1 + Ctheta) := hfrontLe
  have hmul := mul_le_mul_of_nonneg_left hetaFront hCtheta
  calc
    Ctheta * eta ≤ Ctheta * (1 / (1 + Ctheta)) := hmul
    _ ≤ 1 := by
      calc
        Ctheta * (1 / (1 + Ctheta)) = Ctheta / (1 + Ctheta) := by
          ring
        _ ≤ 1 :=
          (div_le_one (by positivity : 0 < 1 + Ctheta)).2 (by linarith)

/-- A largest valid directional-Hessian lower bound exists whenever the set
of valid bounds is nonempty and bounded above. -/
theorem exists_sharp_lower_hessian_modulus
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ)
    (hexists : ∃ a, HasLowerHessianModulus G a)
    (hbounded : ∃ U, ∀ a, HasLowerHessianModulus G a → a ≤ U) :
    ∃ muGAct, IsSharpLowerHessianModulus G muGAct := by
  let S : Set ℝ := {a | HasLowerHessianModulus G a}
  have hSne : S.Nonempty := by
    rcases hexists with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have hSbdd : BddAbove S := by
    rcases hbounded with ⟨U, hU⟩
    exact ⟨U, fun a ha ↦ hU a ha⟩
  let muGAct := sSup S
  refine ⟨muGAct, ?_, ?_⟩
  · intro x p w
    by_cases hw : w = 0
    · subst w
      obtain ⟨a, ha⟩ := hexists
      simpa using ha x p (0 : F)
    · have hnormSq : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
      have hub : ∀ a ∈ S,
          a ≤
            iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w) / ‖w‖ ^ 2 := by
        intro a ha
        exact (le_div_iff₀ hnormSq).2 (ha x p w)
      have hmuGAct : muGAct ≤
          iteratedFDeriv ℝ 2 (G x) p (fun _ ↦ w) / ‖w‖ ^ 2 := by
        exact csSup_le hSne hub
      exact (le_div_iff₀ hnormSq).1 hmuGAct
  · intro a ha
    exact le_csSup hSbdd ha

/-- A smallest valid Hessian operator-norm upper bound exists whenever the
set of valid bounds is nonempty and bounded below. -/
theorem exists_sharp_lower_hessian_upper_bound
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F → ℝ)
    (hexists : ∃ a, HasLowerHessianUpperBound G a)
    (hbounded : ∃ L, ∀ a, HasLowerHessianUpperBound G a → L ≤ a) :
    ∃ Ly, IsSharpLowerHessianUpperBound G Ly := by
  let S : Set ℝ := {a | HasLowerHessianUpperBound G a}
  have hSne : S.Nonempty := by
    rcases hexists with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have hSbdd : BddBelow S := by
    rcases hbounded with ⟨L, hL⟩
    exact ⟨L, fun a ha ↦ hL a ha⟩
  let Ly := sInf S
  refine ⟨Ly, ?_, ?_⟩
  · intro x p
    apply le_csInf hSne
    intro a ha
    exact ha x p
  · intro a ha
    exact csInf_le hSbdd ha

/-! ## Specialization to the hard lower slice -/

set_option maxHeartbeats 1200000 in
-- The proof uses the explicit full-progress point twice, for `muGAct` and `Ly`.
/-- The sharp constants of the rotated hard lower problem exist.  Moreover,
the same construction that proves existence supplies exactly the two
certificates consumed by the condition-number comparison theorem. -/
theorem exists_orthonormalFrame_sharp_lower_constants :
    ∃ Ctheta CHess : ℝ, 0 ≤ Ctheta ∧ 0 ≤ CHess ∧
      ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {T : ℕ} {kappa eta : ℝ},
        1 ≤ kappa → 0 < eta → eta ≤ 1 → 0 < T →
        ∀ (J : ChainVector T →ₗᵢ[ℝ] E),
        Ctheta * eta ≤ 1 →
        CHess * eta ≤ 1 / (2 * kappa) →
        ∃ _hfrontier : ∀ x : E,
            |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta,
          ∃ muGAct Ly : ℝ,
            0 < muGAct ∧
            IsSharpLowerHessianModulus
              (hardLowerSlice kappa eta (hiddenFrameTranspose J)) muGAct ∧
            IsSharpLowerHessianUpperBound
              (hardLowerSlice kappa eta (hiddenFrameTranspose J)) Ly ∧
            kappa ≤ Ly / muGAct ∧
              Ly / muGAct ≤ 2 * (2 + CHess) * kappa := by
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_frontier_hidden_composition_scales
  obtain ⟨CHess, hCHess, hcert⟩ := exists_hardLowerSlice_certificates
  refine ⟨Ctheta, CHess, hCtheta, hCHess, ?_⟩
  intro E _ _ _ T kappa eta hkappa heta hetaOne hT J
    hthetaSmall hsmall
  have hL : ‖hiddenFrameTranspose J‖ ≤ 1 :=
    norm_hiddenFrameTranspose_le hT J
  have hcertHere := hcert hkappa heta hetaOne hT hL
  have hmuValid : HasLowerHessianModulus
      (hardLowerSlice kappa eta (hiddenFrameTranspose J))
      (1 / (2 * kappa)) := by
    exact hcertHere.2 hsmall
  have hLyValid : HasLowerHessianUpperBound
      (hardLowerSlice kappa eta (hiddenFrameTranspose J))
      (2 + CHess * eta) := hcertHere.1
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  let e : ChainVector T := constantChainVector 1
  let u : E := J e
  have hu : u ≠ 0 := rightInverse_image_constant_one_ne_zero hT
    (hiddenFrameTranspose J) J.toContinuousLinearMap
    (hiddenFrameTranspose_comp_frame J)
  let z0 : E := fullProgressWitness eta J.toContinuousLinearMap
  have hmuUpper : ∀ a,
      HasLowerHessianModulus
        (hardLowerSlice kappa eta (hiddenFrameTranspose J)) a →
      a ≤ 1 / kappa := by
    intro a ha
    let wz : E × ℝ := (u, 0)
    have hwitness := ha (0 : E) (z0, 0) wz
    have hflat :
        iteratedFDeriv ℝ 2
            (hardLowerSlice kappa eta (hiddenFrameTranspose J) (0 : E))
            (z0, 0) (fun _ ↦ wz) =
          (1 / kappa) * ‖u‖ ^ 2 := by
      rw [hardLowerSlice_flat_witness_hessian hkpos.ne' heta hT
        (hiddenFrameTranspose J) J.toContinuousLinearMap
        J.norm_toContinuousLinearMap_le
        (hiddenFrameTranspose_comp_frame J)]
      simp [wz]
    rw [hflat] at hwitness
    have hwzNorm : ‖wz‖ = ‖u‖ := by simp [wz, Prod.norm_def]
    rw [hwzNorm] at hwitness
    have huSq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    nlinarith
  have hLyLower : ∀ a,
      HasLowerHessianUpperBound
        (hardLowerSlice kappa eta (hiddenFrameTranspose J)) a →
      1 ≤ a := by
    intro a ha
    let wv : E × ℝ := (0, 1)
    let H := iteratedFDeriv ℝ 2
      (hardLowerSlice kappa eta (hiddenFrameTranspose J) (0 : E)) (z0, 0)
    have hHeval : H (fun _ ↦ wv) = 1 := by
      dsimp [H]
      rw [hardLowerSlice_flat_witness_hessian hkpos.ne' heta hT
        (hiddenFrameTranspose J) J.toContinuousLinearMap
        J.norm_toContinuousLinearMap_le
        (hiddenFrameTranspose_comp_frame J)]
      simp [wv]
    have hHop := H.le_opNorm (fun _ : Fin 2 ↦ wv)
    have hwvNorm : ‖wv‖ = 1 := by simp [wv, Prod.norm_def]
    rw [Real.norm_eq_abs, hHeval, abs_one, Fin.prod_univ_two,
      hwvNorm, one_mul, mul_one] at hHop
    exact hHop.trans (ha (0 : E) (z0, 0))
  obtain ⟨muGAct, hmuGAct⟩ := exists_sharp_lower_hessian_modulus
    (hardLowerSlice kappa eta (hiddenFrameTranspose J))
    ⟨_, hmuValid⟩ ⟨_, hmuUpper⟩
  obtain ⟨Ly, hLy⟩ := exists_sharp_lower_hessian_upper_bound
    (hardLowerSlice kappa eta (hiddenFrameTranspose J))
    ⟨_, hLyValid⟩ ⟨_, hLyLower⟩
  have hmuGActPos : 0 < muGAct :=
    lt_of_lt_of_le (by positivity) (hmuGAct.2 _ hmuValid)
  have hthetaValue : ∀ z : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) z| ≤
        Ctheta * eta ^ 2 := by
    intro z
    exact (htheta heta hT hL z).1
  let hfrontier : ∀ x : E,
      |hardFrontierMap eta (hiddenFrameTranspose J) (kappa • x)| ≤ eta :=
    fun x ↦ hardFrontierMap_le_eta_of_scale heta hthetaSmall
      hthetaValue (kappa • x)
  have hmuGActLower : 1 / (2 * kappa) ≤ muGAct :=
    hmuGAct.2 _ hmuValid
  have hLyUpperRaw : Ly ≤ 2 + CHess * eta := hLy.2 _ hLyValid
  have hLyUpper : Ly ≤ 2 + CHess := by
    have hmul := mul_le_of_le_one_right hCHess hetaOne
    linarith
  have hcomparison := lower_condition_number_sandwich
    hkappa hmuGActPos hCHess hmuGActLower
      (hmuUpper muGAct hmuGAct.1)
      (hLyLower Ly hLy.1) hLyUpper
  exact ⟨hfrontier, muGAct, Ly, hmuGActPos, hmuGAct, hLy,
    hcomparison.1, hcomparison.2⟩

end

end BilevelLowerBound
