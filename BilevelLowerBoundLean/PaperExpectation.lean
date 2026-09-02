/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperHaarBridge

/-!
# From the large-event statement to the paper's expectation criterion

The probability assembly is deliberately valid without an integrability
assumption and therefore returns the alternative "not integrable or the
integral is large".  For the concrete hard objective this alternative is
unnecessary: its gradient is continuous and globally bounded.  This file
proves that fact and removes the nonintegrable branch for every measurable
algorithmic output.
-/

open Function InnerProductSpace MeasureTheory
open scoped Gradient MeasureTheory RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-- A uniform upper bound for the normalized hard gradient.  The numerical
constant is intentionally conservative; only global boundedness is needed. -/
theorem norm_normalizedHardGradient_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (w : E) :
    ‖normalizedHardGradient (1 / 4) (230 * Real.sqrt T) J w‖ ≤
      81 * Real.sqrt T := by
  let R : ℝ := 230 * Real.sqrt T
  let r : E := softProjection R w
  let q : ChainVector T := hiddenFrameTranspose J r
  let g : ChainVector T :=
    gradient (unscaledChain : ChainVector T → ℝ) q
  let D : E →L[ℝ] E := fderiv ℝ (softProjection R : E → E) w
  have hsqrt : 0 < Real.sqrt T := by
    exact lt_of_lt_of_le (by norm_num) (one_le_sqrt_nat hT)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hD : ‖D‖ ≤ 1 := by
    dsimp [D]
    exact norm_fderiv_softProjection_le_one hR w
  have hg : ‖g‖ ≤ 23 * Real.sqrt T := by
    dsimp [g]
    exact norm_unscaledChain_gradient_le q
  have hJg : ‖J g‖ ≤ 23 * Real.sqrt T := by
    rw [J.norm_map]
    exact hg
  have hchain : ‖D (J g)‖ ≤ 23 * Real.sqrt T := by
    calc
      ‖D (J g)‖ ≤ ‖D‖ * ‖J g‖ := D.le_opNorm (J g)
      _ ≤ 1 * (23 * Real.sqrt T) :=
        mul_le_mul hD hJg (norm_nonneg _) (by positivity)
      _ = 23 * Real.sqrt T := one_mul _
  have hr : ‖r‖ ≤ R := by
    exact (norm_softProjection_lt hR w).le
  have hradial : ‖(1 / 4 : ℝ) • r‖ ≤ 58 * Real.sqrt T := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    dsimp [R] at hr
    nlinarith
  unfold normalizedHardGradient
  dsimp only
  calc
    ‖D (J g) + (1 / 4 : ℝ) • r‖ ≤
        ‖D (J g)‖ + ‖(1 / 4 : ℝ) • r‖ := norm_add_le _ _
    _ ≤ 23 * Real.sqrt T + 58 * Real.sqrt T :=
      add_le_add hchain hradial
    _ = 81 * Real.sqrt T := by ring

/-- The concrete hard hyper-gradient is globally bounded. -/
theorem norm_gradient_hardHyperObjective_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {eta kappa : ℝ}
    (heta : 0 < eta) (hkappa : 0 < kappa) (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) (x : E) :
    ‖gradient (hardHyperObjective eta kappa J) x‖ ≤
      (eta * kappa) * (81 * Real.sqrt T) := by
  rw [gradient_hardHyperObjective heta hT, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos heta hkappa)]
  rw [gradient_normalizedHardObjective (by
    have := one_le_sqrt_nat hT
    positivity)]
  exact mul_le_mul_of_nonneg_left
    (norm_normalizedHardGradient_le hT J _) (mul_pos heta hkappa).le

/-- A smooth real-valued function on a real Hilbert space has a continuous
gradient. -/
theorem continuous_gradient_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  unfold gradient
  exact (toDual ℝ E).symm.continuous.comp
    (hf.continuous_fderiv (by norm_num))

/-- The hard hyper-gradient is continuous, hence Borel measurable. -/
theorem continuous_gradient_hardHyperObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ} {eta kappa : ℝ}
    (heta : 0 < eta) (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E) :
    Continuous (gradient (hardHyperObjective eta kappa J)) := by
  have hR : (230 * Real.sqrt T : ℝ) ≠ 0 := by
    have := one_le_sqrt_nat hT
    positivity
  have hnormalized := normalizedHardObjective_contDiff hR (1 / 4) J
  have hfun : hardHyperObjective eta kappa J =
      fun x : E ↦ eta ^ 2 *
        normalizedHardObjective (1 / 4) (230 * Real.sqrt T) J
          ((kappa / eta) • x) := by
    funext x
    exact hardHyperObjective_eq_normalized heta hT J x
  apply continuous_gradient_of_contDiff
  rw [hfun]
  exact (contDiff_const.mul
    (hnormalized.comp (contDiff_const.smul contDiff_id))).of_le
      (by norm_num)

/-- For a measurable random output, the norm of the hard hyper-gradient and
its square are integrable under every probability measure. -/
theorem hardHyperGradient_moments_integrable
    {E Omega : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {mOmega : MeasurableSpace Omega} {mu : @Measure Omega mOmega}
    [IsProbabilityMeasure mu]
    {T : ℕ} {eta kappa : ℝ}
    (heta : 0 < eta) (hkappa : 0 < kappa) (hT : 0 < T)
    (J : ChainVector T →ₗᵢ[ℝ] E)
    (output : Omega → E) (houtput : Measurable output) :
    Integrable (fun omega ↦
        ‖gradient (hardHyperObjective eta kappa J) (output omega)‖) mu ∧
      Integrable (fun omega ↦
        ‖gradient (hardHyperObjective eta kappa J) (output omega)‖ ^ 2) mu := by
  let C : ℝ := (eta * kappa) * (81 * Real.sqrt T)
  have hgradMeas : Measurable (fun omega ↦
      gradient (hardHyperObjective eta kappa J) (output omega)) :=
    (continuous_gradient_hardHyperObjective heta hT J).measurable.comp houtput
  have hlossMeas : Measurable (fun omega ↦
      ‖gradient (hardHyperObjective eta kappa J) (output omega)‖) :=
    hgradMeas.norm
  constructor
  · apply Integrable.of_bound hlossMeas.aestronglyMeasurable C
    filter_upwards [] with omega
    simpa only [Real.norm_eq_abs, abs_norm] using
      norm_gradient_hardHyperObjective_le heta hkappa hT J (output omega)
  · apply Integrable.of_bound
      (hlossMeas.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_gradient_hardHyperObjective_le heta hkappa hT J (output omega)) 2

/-- Eliminate both nonintegrability alternatives returned by the probability
assembly. -/
theorem expectation_bounds_of_moment_alternatives
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} {loss : Omega → ℝ} {epsilon : ℝ}
    (hloss : Integrable loss mu)
    (hlossSq : Integrable (fun omega ↦ loss omega ^ 2) mu)
    (hfirst : ¬ Integrable loss mu ∨ epsilon < ∫ omega, loss omega ∂mu)
    (hsecond : ¬ Integrable (fun omega ↦ loss omega ^ 2) mu ∨
      epsilon ^ 2 < ∫ omega, loss omega ^ 2 ∂mu) :
    epsilon < ∫ omega, loss omega ∂mu ∧
      epsilon ^ 2 < ∫ omega, loss omega ^ 2 ∂mu := by
  constructor
  · rcases hfirst with hnot | hlarge
    · exact False.elim (hnot hloss)
    · exact hlarge
  · rcases hsecond with hnot | hlarge
    · exact False.elim (hnot hlossSq)
    · exact hlarge

/-! ## Expectation-valued main assembly -/

/-- The residual-geometry assembly in exactly the expectation form used in
the paper.  Measurability of each fixed-frame output section is a property of
the algorithmic recursion, not an extra moment assumption; global boundedness
of the hard gradient supplies both moments. -/
theorem main_lower_bound_expectation_from_residual_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {T N : ℕ}
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : @Measure Omega mOmega} [IsProbabilityMeasure mu]
    {mFrame : MeasurableSpace (ChainVector T →ₗᵢ[ℝ] E)}
    {nu : @Measure (ChainVector T →ₗᵢ[ℝ] E) mFrame}
    [IsProbabilityMeasure nu]
    {Delta CDelta creg Cvar epsilon kappa sigma q : ℝ}
    (hCDelta : 0 < CDelta) (hchainGap : chainGapConstant ≤ CDelta)
    (hcreg : 0 < creg) (hDelta : 0 < Delta) (hkappa : 2 ≤ kappa)
    (hepsilon : 0 < epsilon) (hsigma : 0 ≤ sigma)
    (hCvar : 0 < Cvar)
    (haccuracy : epsilon ≤ finalAccuracyConstant CDelta creg *
      min 1 (Real.sqrt Delta))
    (hTdef : T = finalChainLength Delta CDelta epsilon kappa)
    (hN : (N : ℝ) ≤ finalLowerBoundConstant CDelta Cvar *
      mainComplexityScale Delta epsilon kappa sigma)
    (past : Fin N → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (success : Fin N → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hfresh : ∀ t, FreshBernoulliEvent
      (mFrame.prod mOmega) (nu.prod mu) (past t) (success t)
      (revealProbability Cvar (finalEta epsilon kappa) sigma))
    (output : (ChainVector T →ₗᵢ[ℝ] E) × Omega → E)
    (houtputSection : ∀ U, Measurable (fun omega ↦ output (U, omega)))
    (capInfo : PaddedCapIndex (N + 1) T → MeasurableSpace
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (capEvent : PaddedCapIndex (N + 1) T → Set
      ((ChainVector T →ₗᵢ[ℝ] E) × Omega))
    (hcap : ∀ i, ConditionalEventBound (nu.prod mu)
      (capInfo i) (capEvent i) q)
    (hcapBudget : ((((N + 1) ^ 2 * T : ℕ) : ℝ) * q ≤ 1 / 8))
    (geometry : AdaptiveNoCapGeometry
      (finalEta epsilon kappa) (230 * Real.sqrt T)
      (fun z ↦ z.1)
      (fun z ↦ (finalEta epsilon kappa)⁻¹ •
        softProjection (hardRadius (finalEta epsilon kappa) T)
          (kappa • output z))
      (fun z ↦ min T (successCountNat success z)) capEvent) :
    ∃ U0 : ChainVector T →ₗᵢ[ℝ] E,
      hardHyperObjective (finalEta epsilon kappa) kappa U0 0 -
          sInf (Set.range
            (hardHyperObjective (finalEta epsilon kappa) kappa U0)) ≤ Delta ∧
      epsilon < ∫ omega,
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ∂mu ∧
      epsilon ^ 2 < ∫ omega,
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ^ 2 ∂mu := by
  obtain ⟨U0, hgap, hfirst, hsecond⟩ :=
    main_lower_bound_assembly_from_residual_geometry
      hCDelta hchainGap hcreg hDelta hkappa hepsilon hsigma hCvar
      haccuracy hTdef hN past success hfresh output capInfo capEvent
      hcap hcapBudget geometry
  have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
    hepsilon haccuracy
  have heta : 0 < finalEta epsilon kappa := hparams.1
  have hT : 0 < T := by simpa [hTdef] using hparams.2.2.1
  have hkpos : 0 < kappa := lt_of_lt_of_le (by norm_num) hkappa
  obtain ⟨hloss, hlossSq⟩ := hardHyperGradient_moments_integrable
    (mu := mu) heta hkpos hT U0 (fun omega ↦ output (U0, omega))
      (houtputSection U0)
  have hbounds := expectation_bounds_of_moment_alternatives
    hloss hlossSq hfirst hsecond
  exact ⟨U0, hgap, hbounds.1, hbounds.2⟩

end

end BilevelLowerBound
