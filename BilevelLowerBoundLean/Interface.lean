/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.VisibleChainCylinder
import BilevelLowerBoundLean.Oracle
import BilevelLowerBoundLean.Transcript

/-!
# The analytic one-frontier interface

This file turns the two cylinder identities into uniform prefix response maps.
An input consists of the hidden coordinate vector and the derivative of the
hidden-coordinate probe at the public query.  The failed response uses its
`k`-prefix, while the successful response uses the `k`-prefix for the visible
upper part and the `k+1`-prefix for the stochastic frontier.

The resulting maps are continuous, hence Borel.  They do not evaluate the
random progress index.  The separate transcript module shows that adding
proof-only bits and exposed columns does not change the original algorithm's
queries or output.
-/

open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

/-- The hidden coordinate and its first derivative at one public query. -/
abbrev HiddenProbeJet (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : ℕ) :=
  ChainVector T × (E →L[ℝ] ChainVector T)

/-- Sufficient hidden data for assembling the joint upper/lower first-order
response.  On a failed call the last two entries are exactly zero. -/
abbrev HiddenOracleResponse (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :=
  (E →L[ℝ] ℝ) × (ℝ × (E →L[ℝ] ℝ))

/-- Prefix the hidden coordinate and its derivative by the same truncation. -/
def prefixProbeJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (k : ℕ) (data : HiddenProbeJet E T) : HiddenProbeJet E T :=
  (truncate k data.1, (truncateCLM k).comp data.2)

@[simp]
theorem prefixProbeJet_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T k : ℕ} (data : HiddenProbeJet E T) :
    (prefixProbeJet k data).1 = truncate k data.1 := rfl

@[simp]
theorem prefixProbeJet_snd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T k : ℕ} (data : HiddenProbeJet E T) :
    (prefixProbeJet k data).2 = (truncateCLM k).comp data.2 := rfl

/-- Capping a truncation index by the ambient chain length does not change
the truncation. -/
theorem truncate_min_dim {T : ℕ} (k : ℕ) (z : ChainVector T) :
    truncate (min T k) z = truncate k z := by
  rcases le_total T k with hTk | hkT
  · rw [min_eq_left hTk, truncate_eq_self_of_dim_le z le_rfl,
      truncate_eq_self_of_dim_le z hTk]
  · rw [min_eq_right hkT]

theorem truncateCLM_min_dim {T : ℕ} (k : ℕ) :
    truncateCLM (T := T) (min T k) = truncateCLM k := by
  apply ContinuousLinearMap.ext
  intro z
  simpa only [truncateCLM_apply] using truncate_min_dim k z

theorem prefixProbeJet_min_dim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (k : ℕ) (data : HiddenProbeJet E T) :
    prefixProbeJet (min T k) data = prefixProbeJet k data := by
  apply Prod.ext
  · exact truncate_min_dim k data.1
  · simp only [prefixProbeJet_snd, truncateCLM_min_dim]

/-- Pull a scalar chain derivative back to the ambient query space. -/
def pullbackChainDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (f : ChainVector T → ℝ) (data : HiddenProbeJet E T) :
    E →L[ℝ] ℝ :=
  (fderiv ℝ f data.1).comp data.2

/-- Actual hidden payload on a failed call.  The stochastic frontier is
absent, rather than merely evaluated and then hidden. -/
def failedHiddenResponse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (η : ℝ) (data : HiddenProbeJet E T) :
    HiddenOracleResponse E :=
  (pullbackChainDerivative (visibleChain η) data, (0, 0))

/-- Actual hidden payload on a successful call. -/
def successfulHiddenResponse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (η : ℝ) (data : HiddenProbeJet E T) :
    HiddenOracleResponse E :=
  (pullbackChainDerivative (visibleChain η) data,
    (frontierExtractor η data.1,
      pullbackChainDerivative (frontierExtractor η) data))

/-- The uniform failed-call prefix map.  Its input is truncated to `ell`
inside the definition, so the map never evaluates the progress index. -/
def failedPrefixResponse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (η : ℝ) (ell : ℕ) (data : HiddenProbeJet E T) :
    HiddenOracleResponse E :=
  failedHiddenResponse η (prefixProbeJet ell data)

/-- The uniform successful-call prefix map.  The upper payload uses `ell`,
and the frontier payload uses `min T (ell+1)`. -/
def successfulPrefixResponse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} (η : ℝ) (ell : ℕ) (data : HiddenProbeJet E T) :
    HiddenOracleResponse E :=
  let ellPlus := min T (ell + 1)
  let visibleData := prefixProbeJet ell data
  let frontierData := prefixProbeJet ellPlus data
  (pullbackChainDerivative (visibleChain η) visibleData,
    (frontierExtractor η frontierData.1,
      pullbackChainDerivative (frontierExtractor η) frontierData))

/-- The visible derivative pulls back through exactly the first `ell`
coordinates whenever progress is at most `ell`. -/
theorem pullback_visibleChain_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    pullbackChainDerivative (visibleChain η) data =
      pullbackChainDerivative (visibleChain η) (prefixProbeJet ell data) := by
  apply ContinuousLinearMap.ext
  intro v
  have hCylinder :=
    iteratedFDeriv_visibleChain_cylinder_of_progress_le
      (r := 1) hη data.1 hprog
  have hAtV := congrArg
    (fun M : ContinuousMultilinearMap ℝ
        (fun _ : Fin 1 ↦ ChainVector T) ℝ ↦ M (fun _ ↦ data.2 v))
    hCylinder
  simp only [iteratedFDeriv_one_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] at hAtV
  simpa [pullbackChainDerivative, prefixProbeJet,
    ContinuousLinearMap.comp_apply] using hAtV

/-- The frontier value and derivative pull back through the first `ell+1`
coordinates, capped by the chain length. -/
theorem frontier_value_derivative_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    let ellPlus := min T (ell + 1)
    frontierExtractor η data.1 =
        frontierExtractor η (prefixProbeJet ellPlus data).1 ∧
      pullbackChainDerivative (frontierExtractor η) data =
        pullbackChainDerivative (frontierExtractor η)
          (prefixProbeJet ellPlus data) := by
  let ellPlus := min T (ell + 1)
  constructor
  · have hValue := (frontierExtractor_truncate_succ_of_progress_le
      hη data.1 hprog).symm
    change frontierExtractor η data.1 =
      frontierExtractor η (truncate ellPlus data.1)
    rw [show ellPlus = min T (ell + 1) from rfl,
      truncate_min_dim]
    exact hValue
  · apply ContinuousLinearMap.ext
    intro v
    have hCylinder :=
      iteratedFDeriv_frontierExtractor_cylinder_of_progress_le
        (r := 1) hη data.1 hprog
    have hAtV := congrArg
      (fun M : ContinuousMultilinearMap ℝ
          (fun _ : Fin 1 ↦ ChainVector T) ℝ ↦ M (fun _ ↦ data.2 v))
      hCylinder
    simp only [iteratedFDeriv_one_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply] at hAtV
    rw [prefixProbeJet_min_dim (E := E) (T := T) (ell + 1) data]
    simpa [pullbackChainDerivative, prefixProbeJet,
      ContinuousLinearMap.comp_apply] using hAtV

/-- Failed calls have a representation through the first `ell` hidden
directions only. -/
theorem failedHiddenResponse_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    failedHiddenResponse η data = failedPrefixResponse η ell data := by
  change
    (pullbackChainDerivative (visibleChain η) data, (0, 0)) =
      (pullbackChainDerivative (visibleChain η) (prefixProbeJet ell data),
        (0, 0))
  rw [pullback_visibleChain_eq_prefix hη data hprog]

/-- Successful calls have a representation through the first
`min T (ell+1)` directions only, while their upper component still uses just
the first `ell` directions. -/
theorem successfulHiddenResponse_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    successfulHiddenResponse η data =
      successfulPrefixResponse η ell data := by
  have hVisible := pullback_visibleChain_eq_prefix hη data hprog
  have hFrontier :=
    frontier_value_derivative_eq_prefix hη data hprog
  unfold successfulHiddenResponse successfulPrefixResponse
  dsimp only
  rw [hVisible, hFrontier.1, hFrontier.2]

/-! ## Borel regularity of the uniform prefix maps -/

theorem prefixProbeJet_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T k : ℕ} :
    Continuous (prefixProbeJet (E := E) (T := T) k) := by
  apply Continuous.prodMk
  · exact (truncateCLM k).continuous.comp continuous_fst
  · exact continuous_const.clm_comp continuous_snd

theorem pullbackChainDerivative_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {f : ChainVector T → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (pullbackChainDerivative (E := E) f) := by
  exact ((hf.continuous_fderiv (by simp)).comp continuous_fst).clm_comp
    continuous_snd

theorem failedPrefixResponse_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} (η : ℝ) :
    Continuous (failedPrefixResponse (E := E) (T := T) η ell) := by
  unfold failedPrefixResponse failedHiddenResponse
  exact ((pullbackChainDerivative_continuous
      (E := E) (visibleChain_contDiff η)).comp
        (prefixProbeJet_continuous (E := E) (T := T) (k := ell))).prodMk
    continuous_const

theorem successfulPrefixResponse_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} (η : ℝ) :
    Continuous (successfulPrefixResponse (E := E) (T := T) η ell) := by
  let ellPlus := min T (ell + 1)
  let hVisible : Continuous
      (fun data : HiddenProbeJet E T ↦
        pullbackChainDerivative (visibleChain η)
          (prefixProbeJet ell data)) :=
    (pullbackChainDerivative_continuous
      (E := E) (visibleChain_contDiff η)).comp
        (prefixProbeJet_continuous (E := E) (T := T) (k := ell))
  let hFrontierData : Continuous
      (prefixProbeJet (E := E) (T := T) ellPlus) :=
    prefixProbeJet_continuous
  let hFrontierValue : Continuous
      (fun data : HiddenProbeJet E T ↦
        frontierExtractor η (prefixProbeJet ellPlus data).1) :=
    (frontierExtractor_contDiff η).continuous.comp
      (continuous_fst.comp hFrontierData)
  let hFrontierDerivative : Continuous
      (fun data : HiddenProbeJet E T ↦
        pullbackChainDerivative (frontierExtractor η)
          (prefixProbeJet ellPlus data)) :=
    (pullbackChainDerivative_continuous
      (E := E) (frontierExtractor_contDiff η)).comp hFrontierData
  change Continuous (fun data : HiddenProbeJet E T ↦
    (pullbackChainDerivative (visibleChain η) (prefixProbeJet ell data),
      (frontierExtractor η (prefixProbeJet ellPlus data).1,
        pullbackChainDerivative (frontierExtractor η)
          (prefixProbeJet ellPlus data))))
  exact hVisible.prodMk (hFrontierValue.prodMk hFrontierDerivative)

theorem failedPrefixResponse_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {T ell : ℕ} (η : ℝ) :
    Measurable (failedPrefixResponse (E := E) (T := T) η ell) :=
  (failedPrefixResponse_continuous (E := E) (T := T) η).measurable

theorem successfulPrefixResponse_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {T ell : ℕ} (η : ℝ) :
    Measurable (successfulPrefixResponse (E := E) (T := T) η ell) :=
  (successfulPrefixResponse_continuous (E := E) (T := T) η).measurable

/-- Any deterministic response assembler preserves the failed prefix
identity.  This is the formal reason that public base-gradient, cutoff, and
pseudo-Huber terms can be added without changing the information bound. -/
theorem assemble_failed_prefix_identity
    {E Response : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (assemble : HiddenOracleResponse E → Response)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    assemble (failedHiddenResponse η data) =
      assemble (failedPrefixResponse η ell data) := by
  rw [failedHiddenResponse_eq_prefix hη data hprog]

/-- Any deterministic response assembler preserves the successful prefix
identity. -/
theorem assemble_successful_prefix_identity
    {E Response : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T ell : ℕ} {η : ℝ} (hη : 0 < η)
    (assemble : HiddenOracleResponse E → Response)
    (data : HiddenProbeJet E T)
    (hprog : progress (η / 4) data.1 ≤ ell) :
    assemble (successfulHiddenResponse η data) =
      assemble (successfulPrefixResponse η ell data) := by
  rw [successfulHiddenResponse_eq_prefix hη data hprog]

end

end BilevelLowerBound
