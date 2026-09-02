/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.PaperOracle
import BilevelLowerBoundLean.MainTheorem

/-!
# Deterministic bridge from padded cap events to output progress

Conditional Haar invariance and the spherical-cap probability remain the two
external cited inputs.  Everything after those inputs is represented here by
explicit residual-space data and proved in Lean.  In particular, the main
theorem no longer needs to assume its final no-cap progress implication.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal InnerProductSpace MeasureTheory
  ProbabilityTheory RealInnerProductSpace

namespace BilevelLowerBound

noncomputable section

/-- The `j`-th column of a hidden orthonormal frame. -/
def hiddenFrameColumn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (J : ChainVector T →ₗᵢ[ℝ] E) (j : Fin T) : E :=
  J (EuclideanSpace.single j 1)

/-- Analysis by `J^T` is coordinatewise inner product with the frame
columns. -/
theorem hiddenFrameTranspose_apply_eq_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (J : ChainVector T →ₗᵢ[ℝ] E) (r : E) (j : Fin T) :
    hiddenFrameTranspose J r j = ⟪hiddenFrameColumn J j, r⟫_ℝ := by
  have h := J.toContinuousLinearMap.adjoint_inner_right
    (EuclideanSpace.single j (1 : ℝ)) r
  rw [real_inner_comm] at h
  simpa [hiddenFrameTranspose, hiddenFrameColumn, PiLp.inner_apply] using h

/-- All deterministic data used for one still-hidden coordinate in Step 6 of
the Haar proof. -/
structure ResidualCapWitness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (R : ℝ) (u r : E) where
  exposedSpace : Submodule ℝ E
  projection : exposedSpace.HasOrthogonalProjection
  residualDimension : ℕ
  dimension_le : residualDimension ≤ n
  residualBasis : Fin residualDimension → E
  residualBasis_orthonormal : Orthonormal ℝ residualBasis
  coefficients : ChainVector residualDimension
  column_orthogonal : u ∈ exposedSpaceᗮ
  residual_expansion :
    residualProbe exposedSpace r =
      ∑ s : Fin residualDimension, coefficients s • residualBasis s
  cap_coordinates : ∀ s : Fin residualDimension,
    |⟪u, residualBasis s⟫_ℝ| ≤
      1 / (4 * R * Real.sqrt n)

/-- The residual certificate implies the `1/4` coordinate bound. -/
theorem ResidualCapWitness.coordinate_le_quarter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {R : ℝ} {u r : E}
    (hR : 0 < R) (hn : 0 < n) (hr : ‖r‖ ≤ R)
    (W : ResidualCapWitness n R u r) :
    |⟪u, r⟫_ℝ| ≤ 1 / 4 := by
  letI := W.projection
  exact hiddenCoordinate_le_quarter_of_no_cap
    hR hn W.dimension_le W.exposedSpace W.column_orthogonal hr
    W.residualBasis_orthonormal W.coefficients
    W.residual_expansion W.cap_coordinates

/-- A complete deterministic residual construction for all active tail
coordinates.  Inactive padded triples are absent because `witness` is only
requested after proving both `prefix <= j` and the complement of every fixed
cap event. -/
structure AdaptiveNoCapGeometry
    {E Omega : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Omega] {T n : ℕ}
    (eta Rbar : ℝ)
    (frame : Omega → ChainVector T →ₗᵢ[ℝ] E)
    (probe : Omega → E) (prefixLength : Omega → ℕ)
    (capEvent : PaddedCapIndex n T → Set Omega) where
  eta_pos : 0 < eta
  radius_pos : 0 < Rbar
  n_pos : 0 < n
  probe_norm : ∀ omega, ‖probe omega‖ ≤ Rbar
  analysis_measurable : Measurable (fun omega ↦
    hiddenFrameTranspose (frame omega) (probe omega))
  witness : ∀ omega, (∀ i, omega ∉ capEvent i) →
    ∀ j : Fin T, prefixLength omega ≤ j.val →
      ResidualCapWitness n Rbar
        (hiddenFrameColumn (frame omega) j) (probe omega)

/-- The explicit residual data turn the complement of all padded cap events
into a progress bound for the normalized probe. -/
theorem AdaptiveNoCapGeometry.normalized_progress_le
    {E Omega : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Omega] {T n : ℕ}
    {eta Rbar : ℝ}
    {frame : Omega → ChainVector T →ₗᵢ[ℝ] E}
    {probe : Omega → E} {prefixLength : Omega → ℕ}
    {capEvent : PaddedCapIndex n T → Set Omega}
    (G : AdaptiveNoCapGeometry eta Rbar frame probe prefixLength capEvent)
    (omega : Omega) (hnoCap : ∀ i, omega ∉ capEvent i) :
    progress (1 / 4 : ℝ)
      (hiddenFrameTranspose (frame omega) (probe omega)) ≤
      prefixLength omega := by
  apply progress_quarter_le_of_hidden_coordinates
  intro j hj
  rw [hiddenFrameTranspose_apply_eq_inner]
  exact (G.witness omega hnoCap j hj).coordinate_le_quarter
    G.radius_pos G.n_pos (G.probe_norm omega)

/-- Rescaled form used by the paper: residual geometry is applied to
`eta^{-1} rho_R`, then converted back to threshold `eta/4`. -/
theorem noCapProgress_of_residual_geometry
    {E Omega : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Omega] {T n : ℕ}
    {eta Rbar : ℝ} (heta : 0 < eta)
    (frame : Omega → ChainVector T →ₗᵢ[ℝ] E)
    (rawProbe : Omega → E) (prefixLength : Omega → ℕ)
    (capEvent : PaddedCapIndex n T → Set Omega)
    (G : AdaptiveNoCapGeometry eta Rbar frame
      (fun omega ↦ eta⁻¹ • rawProbe omega) prefixLength capEvent) :
    ∀ omega, (∀ i, omega ∉ capEvent i) →
      progress (eta / 4)
          (hiddenFrameTranspose (frame omega) (rawProbe omega)) ≤
        prefixLength omega := by
  intro omega hnoCap
  have hnormalized := G.normalized_progress_le omega hnoCap
  have hvector :
      chainVectorOfFun (fun i ↦
        hiddenFrameTranspose (frame omega) (rawProbe omega) i / eta) =
        hiddenFrameTranspose (frame omega) (eta⁻¹ • rawProbe omega) := by
    ext i
    simp only [chainVectorOfFun_apply, map_smul, PiLp.smul_apply,
      smul_eq_mul]
    field_simp [heta.ne']
  rw [← progress_quarter_rescaling
    (hiddenFrameTranspose (frame omega) (rawProbe omega)) eta heta]
  rw [hvector]
  exact hnormalized

/-! ## Measurability of the unfinished event -/

/-- For a nonempty chain, being unfinished is equivalent to the last
coordinate lying below the threshold. -/
theorem progress_lt_dim_iff_last_coordinate_le
    {T : ℕ} (hT : 0 < T) (c : ℝ) (z : ChainVector T) :
    progress c z < T ↔
      |z ⟨T - 1, by omega⟩| ≤ c := by
  let last : Fin T := ⟨T - 1, by omega⟩
  constructor
  · intro hprog
    have hle : progress c z ≤ T - 1 := by omega
    exact abs_le_threshold_of_progress_le hle last (by simp [last])
  · intro hlast
    have hle : progress c z ≤ T - 1 := by
      apply progress_le_of_tail_bound
      intro i hi
      have hilast : i = last := by
        apply Fin.ext
        dsimp [last]
        omega
      simpa [hilast, last] using hlast
    omega

/-- A measurable chain-valued probe has a measurable unfinished event. -/
theorem measurableSet_progress_lt_dim
    {Omega : Type*} [MeasurableSpace Omega] {T : ℕ}
    (hT : 0 < T) (c : ℝ) {probe : Omega → ChainVector T}
    (hprobe : Measurable probe) :
    MeasurableSet {omega | progress c (probe omega) < T} := by
  let last : Fin T := ⟨T - 1, by omega⟩
  have hcoord : Measurable (fun omega ↦ probe omega last) := by
    change Measurable ((EuclideanSpace.proj last) ∘ probe)
    exact (EuclideanSpace.proj last).measurable.comp hprobe
  have habs : Measurable (fun omega ↦ |probe omega last|) := hcoord.abs
  have hset :
      {omega | progress c (probe omega) < T} =
        {omega | |probe omega last| ≤ c} := by
    ext omega
    exact progress_lt_dim_iff_last_coordinate_le hT c (probe omega)
  rw [hset]
  exact habs measurableSet_Iic

/-- Measurability of the raw analysis probe follows from the normalized
analysis probe stored in the residual geometry. -/
theorem rawAnalysis_measurable_of_residual_geometry
    {E Omega : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Omega] {T n : ℕ}
    {eta Rbar : ℝ} (heta : 0 < eta)
    (frame : Omega → ChainVector T →ₗᵢ[ℝ] E)
    (rawProbe : Omega → E) (prefixLength : Omega → ℕ)
    (capEvent : PaddedCapIndex n T → Set Omega)
    (G : AdaptiveNoCapGeometry eta Rbar frame
      (fun omega ↦ eta⁻¹ • rawProbe omega) prefixLength capEvent) :
    Measurable (fun omega ↦
      hiddenFrameTranspose (frame omega) (rawProbe omega)) := by
  have heq :
      (fun omega ↦ hiddenFrameTranspose (frame omega) (rawProbe omega)) =
        fun omega ↦ eta • hiddenFrameTranspose (frame omega)
          (eta⁻¹ • rawProbe omega) := by
    funext omega
    rw [map_smul, smul_smul, mul_inv_cancel₀ heta.ne', one_smul]
  rw [heq]
  exact G.analysis_measurable.const_smul eta

/-- Main assembly with the former `hnoCapProgress` premise derived from the
residual construction.  Thus the remaining geometric premises are exactly
the cited conditional cap estimates and their explicit deterministic data. -/
theorem main_lower_bound_assembly_from_residual_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T N : ℕ}
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
      (¬ Integrable (fun omega ↦
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖) mu ∨
        epsilon < ∫ omega,
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ∂mu) ∧
      (¬ Integrable (fun omega ↦
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ^ 2) mu ∨
        epsilon ^ 2 < ∫ omega,
          ‖gradient (hardHyperObjective (finalEta epsilon kappa) kappa U0)
            (output (U0, omega))‖ ^ 2 ∂mu) := by
  have hnoCapProgress : ∀ z, (∀ i, z ∉ capEvent i) →
      progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) ≤
        min T (successCountNat success z) := by
    intro z hnoCap
    exact noCapProgress_of_residual_geometry
      (frame := fun z ↦ z.1)
      (rawProbe := fun z ↦
        softProjection (hardRadius (finalEta epsilon kappa) T)
          (kappa • output z))
      (prefixLength := fun z ↦ min T (successCountNat success z))
      (capEvent := capEvent)
      geometry.eta_pos geometry z hnoCap
  have hT : 0 < T := by
    have hparams := final_parameters_basic hCDelta hcreg hDelta hkappa
      hepsilon haccuracy
    simpa [hTdef] using hparams.2.2.1
  have hunfMeas : MeasurableSet
      {z | progress (finalEta epsilon kappa / 4)
          (hiddenFrameTranspose z.1
            (softProjection (hardRadius (finalEta epsilon kappa) T)
              (kappa • output z))) < T} := by
    apply measurableSet_progress_lt_dim hT
    exact rawAnalysis_measurable_of_residual_geometry
      geometry.eta_pos
      (fun z ↦ z.1)
      (fun z ↦ softProjection
        (hardRadius (finalEta epsilon kappa) T) (kappa • output z))
      (fun z ↦ min T (successCountNat success z)) capEvent geometry
  obtain ⟨U0, hgap, hfirst, hsecond⟩ :=
    main_lower_bound_assembly hCDelta hchainGap hcreg hDelta hkappa
      hepsilon hsigma hCvar haccuracy hTdef hN past success hfresh output
      capInfo capEvent hcap hcapBudget hnoCapProgress hunfMeas
  refine ⟨U0, hgap, ?_, ?_⟩
  · rcases hfirst with hnot | hlarge
    · exact Or.inl hnot
    · exact Or.inr (by nlinarith)
  · rcases hsecond with hnot | hlarge
    · exact Or.inl hnot
    · exact Or.inr (by nlinarith [sq_pos_of_pos hepsilon])

end

end BilevelLowerBound
