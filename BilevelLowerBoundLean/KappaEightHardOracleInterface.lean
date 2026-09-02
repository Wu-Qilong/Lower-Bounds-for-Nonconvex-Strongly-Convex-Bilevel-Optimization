/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightOracle
import BilevelLowerBoundLean.KappaEightPaperHardInstance
import BilevelLowerBoundLean.Interface

/-!
# One-frontier interface for the two-coordinate hard oracle

The amplified compensated block depends on a hidden frontier only through its
value and first derivative at the lower query.  This file derives that local
jet formula, assembles the complete upper/lower stochastic response, and
proves exact failed- and successful-call prefix representations.  In
particular, a failed call contains no occurrence of the current hidden
frontier, while a successful call exposes only its single next first jet.
-/

open scoped ContDiff Topology

namespace BilevelLowerBound

noncomputable section

/-! ## Reconstructing the attenuated compensation from a first jet -/

/-- First derivative of the amplified compensation reconstructed from the
frontier value and covector at the queried hidden lower point. -/
def kappaEightCompensatedDerivativeFromJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta kappa : ℝ) (v : AmplifierAux) (theta : ℝ)
    (dtheta : E →L[ℝ] ℝ) : (E × AmplifierAux) →L[ℝ] ℝ :=
  let alpha := attenuatedFrontier kappa theta
  let dalpha := (amplifierOffDiag kappa)⁻¹ • dtheta
  let Lz := ContinuousLinearMap.fst ℝ E AmplifierAux
  let Lv1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ E AmplifierAux)
  (amplifierDiag kappa * alpha - compactIdentity eta v.1) •
      dalpha.comp Lz -
    alpha • (fderiv ℝ (compactIdentity eta) v.1).comp Lv1

/-- The derivative of the complete amplified compensation is determined by
exactly the value and derivative of the hidden frontier. -/
theorem fderiv_kappaEightCompensatedPair_eq_fromJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} (heta : eta ≠ 0)
    {thetaFun : E → ℝ} {z : E}
    (htheta : DifferentiableAt ℝ thetaFun z) (v : AmplifierAux) :
    fderiv ℝ (kappaEightCompensatedPair eta kappa thetaFun) (z, v) =
      kappaEightCompensatedDerivativeFromJet eta kappa v
        (thetaFun z) (fderiv ℝ thetaFun z) := by
  let Lz : (E × AmplifierAux) →L[ℝ] E :=
    ContinuousLinearMap.fst ℝ E AmplifierAux
  let Lv1 : (E × AmplifierAux) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ E AmplifierAux)
  let Theta : E × AmplifierAux → ℝ := fun p ↦ thetaFun p.1
  let Alpha : E × AmplifierAux → ℝ :=
    fun p ↦ attenuatedFrontier kappa (thetaFun p.1)
  let Psi : E × AmplifierAux → ℝ :=
    fun p ↦ compactIdentity eta p.2.1
  have hTheta : HasFDerivAt Theta
      ((fderiv ℝ thetaFun z).comp Lz) (z, v) := by
    exact htheta.hasFDerivAt.comp (z, v) Lz.hasFDerivAt
  have hAlpha : HasFDerivAt Alpha
      ((amplifierOffDiag kappa)⁻¹ •
        (fderiv ℝ thetaFun z).comp Lz) (z, v) := by
    have hAlphaFun : Alpha = (amplifierOffDiag kappa)⁻¹ • Theta := by
      funext p
      simp [Alpha, Theta, attenuatedFrontier, div_eq_mul_inv,
        mul_comm]
    rw [hAlphaFun]
    exact hTheta.const_smul (amplifierOffDiag kappa)⁻¹
  have hPsiBase : DifferentiableAt ℝ (compactIdentity eta) v.1 :=
    (compactIdentity_contDiff heta).differentiable (by norm_num) v.1
  have hPsi : HasFDerivAt Psi
      ((fderiv ℝ (compactIdentity eta) v.1).comp Lv1) (z, v) := by
    exact hPsiBase.hasFDerivAt.comp (z, v) Lv1.hasFDerivAt
  have hSquare := (hAlpha.mul hAlpha).const_mul (amplifierDiag kappa / 2)
  have hProduct := hAlpha.mul hPsi
  have hDerivative := hSquare.sub hProduct
  have hfun : kappaEightCompensatedPair eta kappa thetaFun =
      fun p : E × AmplifierAux ↦
        (amplifierDiag kappa / 2) * (Alpha p * Alpha p) -
          Alpha p * Psi p := by
    funext p
    simp [kappaEightCompensatedPair, amplifiedCompensation, Alpha, Psi,
      pow_two]
  have htarget :
      (fun p : E × AmplifierAux ↦
        (amplifierDiag kappa / 2) * (Alpha p * Alpha p) -
          Alpha p * Psi p) =
      ((fun p : E × AmplifierAux ↦
        (amplifierDiag kappa / 2) * (Alpha * Alpha) p) -
          Alpha * Psi) := by
    funext p
    rfl
  rw [hfun, htarget, hDerivative.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [kappaEightCompensatedDerivativeFromJet, Alpha, Psi, Lz, Lv1,
    ContinuousLinearMap.comp_apply]
  ring

/-! ## Concrete hidden probe and full response -/

/-- Hidden coordinate and derivative of the rotated soft probe at `z`. -/
def kappaEightHardProbeJetAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (R : ℝ) (L : E →L[ℝ] ChainVector T) (z : E) :
    HiddenProbeJet E T :=
  (hiddenProbe R L z, fderiv ℝ (hiddenProbe R L) z)

theorem pullback_visibleChain_kappaEightHardProbeJetAt_hardRadius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (z : E) :
    pullbackChainDerivative (visibleChain eta)
        (kappaEightHardProbeJetAt (hardRadius eta T) L z) =
      fderiv ℝ (hardVisibleMap eta L) z := by
  have hOuter : DifferentiableAt ℝ
      (visibleChain eta : ChainVector T → ℝ)
        (hiddenProbe (hardRadius eta T) L z) :=
    (visibleChain_contDiff eta).differentiable (by norm_num) _
  have hInner : DifferentiableAt ℝ
      (hiddenProbe (hardRadius eta T) L) z :=
    (hiddenProbe_contDiff (hardRadius_pos heta hT).ne' L)
      |>.differentiable (by norm_num) z
  exact (fderiv_comp z hOuter hInner).symm

theorem frontier_value_pullback_kappaEightHardProbeJetAt_hardRadius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (L : E →L[ℝ] ChainVector T) (z : E) :
    frontierExtractor eta
          (kappaEightHardProbeJetAt (hardRadius eta T) L z).1 =
        hardFrontierMap eta L z ∧
      pullbackChainDerivative (frontierExtractor eta)
          (kappaEightHardProbeJetAt (hardRadius eta T) L z) =
        fderiv ℝ (hardFrontierMap eta L) z := by
  constructor
  · rfl
  · have hOuter : DifferentiableAt ℝ
        (frontierExtractor eta : ChainVector T → ℝ)
          (hiddenProbe (hardRadius eta T) L z) :=
      (frontierExtractor_contDiff eta).differentiable (by norm_num) _
    have hInner : DifferentiableAt ℝ
        (hiddenProbe (hardRadius eta T) L) z :=
      (hiddenProbe_contDiff (hardRadius_pos heta hT).ne' L)
        |>.differentiable (by norm_num) z
    exact (fderiv_comp z hOuter hInner).symm

/-- Second amplified coordinate, as a linear functional on the joint query. -/
def kappaEightFullAuxSecondProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    KappaEightQueryPoint E →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    kappaEightFullAuxProjection

@[simp]
theorem kappaEightFullAuxSecondProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : KappaEightQueryPoint E) :
    kappaEightFullAuxSecondProjection p = p.2.2.2 := rfl

/-- Full upper objective used by the amplified oracle. -/
def kappaEightOracleFullHardUpper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta lam R : ℝ) (L : E →L[ℝ] ChainVector T) :
    KappaEightQueryPoint E → ℝ :=
  fun p ↦ hardVisibleMap eta L p.2.1 + p.2.2.2 +
    pseudoHuber lam R p.2.1

/-- At the paper radius, the interface upper objective is literally the
upper objective packaged in the concrete amplified population problem. -/
theorem kappaEightFullHardUpper_hardRadius_eq_oracleUpper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (eta lam : ℝ) (L : E →L[ℝ] ChainVector T) :
    kappaEightFullHardUpper eta lam (hardRadius eta T) L =
      kappaEightOracleFullHardUpper eta lam (hardRadius eta T) L := by
  funext p
  rfl

/-- Assemble the complete amplified response from public data and the
sufficient hidden payload. -/
def assembleKappaEightHardJointResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa eta prob xi lam R : ℝ) (a : KappaEightQueryPoint E)
    (payload : HiddenOracleResponse E) : KappaEightGradientResponse E :=
  let upper := payload.1.comp kappaEightFullZProjection +
    kappaEightFullAuxSecondProjection +
    fderiv ℝ ((pseudoHuber lam R) ∘ kappaEightFullZProjection) a
  let frontierLocal := kappaEightCompensatedDerivativeFromJet
    eta kappa a.2.2 payload.2.1 payload.2.2
  let lower := fderiv ℝ (kappaEightFullBaseQuadratic kappa) a +
    (xi / prob) • frontierLocal.comp kappaEightFullLowerProjection
  (upper, lower)

/-- Exact joint response of the new hard stochastic oracle. -/
def kappaEightHardJointGradientResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi lam R : ℝ)
    (L : E →L[ℝ] ChainVector T) (a : KappaEightQueryPoint E) :
    KappaEightGradientResponse E :=
  (fderiv ℝ (kappaEightOracleFullHardUpper eta lam R L) a,
    fderiv ℝ (kappaEightFullSampleLower kappa eta prob xi L) a)

/-- The response used by the interface is the derivative response of the
literal paper objectives when `R` is the paper radius. -/
theorem kappaEightHardJointGradientResponse_eq_paperResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob xi lam : ℝ)
    (L : E →L[ℝ] ChainVector T) (a : KappaEightQueryPoint E) :
    kappaEightHardJointGradientResponse kappa eta prob xi lam
        (hardRadius eta T) L a =
      (fderiv ℝ
          (kappaEightFullHardUpper eta lam (hardRadius eta T) L) a,
        fderiv ℝ
          (kappaEightFullSampleLower kappa eta prob xi L) a) := by
  rw [kappaEightHardJointGradientResponse,
    kappaEightFullHardUpper_hardRadius_eq_oracleUpper]

theorem fderiv_kappaEightOracleFullHardUpper_as_assembled
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta R : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (hR : R ≠ 0) (lam : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    fderiv ℝ (kappaEightOracleFullHardUpper eta lam R L) a =
      (fderiv ℝ (hardVisibleMap eta L) a.2.1).comp
          kappaEightFullZProjection +
        kappaEightFullAuxSecondProjection +
        fderiv ℝ ((pseudoHuber lam R) ∘
          kappaEightFullZProjection) a := by
  let A : KappaEightQueryPoint E → ℝ :=
    (hardVisibleMap eta L) ∘ kappaEightFullZProjection
  let B : KappaEightQueryPoint E → ℝ :=
    kappaEightFullAuxSecondProjection
  let C : KappaEightQueryPoint E → ℝ :=
    (pseudoHuber lam R) ∘ kappaEightFullZProjection
  have hA : DifferentiableAt ℝ A a :=
    ((hardVisibleMap_contDiff heta hT L).comp
      (kappaEightFullZProjection (E := E)).contDiff)
      |>.differentiable (by norm_num) a
  have hB : DifferentiableAt ℝ B a :=
    (kappaEightFullAuxSecondProjection (E := E)).differentiableAt
  have hC : DifferentiableAt ℝ C a :=
    ((pseudoHuber_contDiff hR).comp
      (kappaEightFullZProjection (E := E)).contDiff)
      |>.differentiable (by norm_num) a
  have hAderiv : fderiv ℝ A a =
      (fderiv ℝ (hardVisibleMap eta L) a.2.1).comp
        kappaEightFullZProjection := by
    have hcomp := fderiv_comp a
      ((hardVisibleMap_contDiff heta hT L).differentiable (by norm_num) _)
      (kappaEightFullZProjection (E := E)).differentiableAt
    rw [(kappaEightFullZProjection (E := E)).hasFDerivAt.fderiv] at hcomp
    exact hcomp
  have hfun : kappaEightOracleFullHardUpper eta lam R L =
      (A + B) + C := by
    funext p
    simp [kappaEightOracleFullHardUpper, A, B, C]
  rw [hfun, fderiv_add (hA.add hB) hC, fderiv_add hA hB,
    hAderiv]
  change _ + fderiv ℝ (kappaEightFullAuxSecondProjection :
    KappaEightQueryPoint E → ℝ) a + _ = _
  rw [(kappaEightFullAuxSecondProjection (E := E)).hasFDerivAt.fderiv]

theorem fderiv_kappaEightFullCompensatedPair_eq_fromJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta kappa : ℝ} (heta : eta ≠ 0)
    {thetaFun : E → ℝ} (htheta : ContDiff ℝ ∞ thetaFun)
    (a : KappaEightQueryPoint E) :
    fderiv ℝ (kappaEightFullCompensatedPair eta kappa thetaFun) a =
      (kappaEightCompensatedDerivativeFromJet eta kappa a.2.2
        (thetaFun a.2.1) (fderiv ℝ thetaFun a.2.1)).comp
          kappaEightFullLowerProjection := by
  have hlocal := fderiv_kappaEightCompensatedPair_eq_fromJet
    (kappa := kappa) heta
    (htheta.differentiable (by norm_num) a.2.1) a.2.2
  have hcomp := fderiv_comp
    (f := (kappaEightFullLowerProjection :
      KappaEightQueryPoint E → KappaEightLowerPoint E))
    (g := kappaEightCompensatedPair eta kappa thetaFun) a
    ((kappaEightCompensatedPair_contDiff (kappa := kappa) heta htheta).differentiable
      (by norm_num) a.2)
    (kappaEightFullLowerProjection (E := E)).differentiableAt
  change fderiv ℝ
      (kappaEightCompensatedPair eta kappa thetaFun ∘
        (kappaEightFullLowerProjection :
          KappaEightQueryPoint E → KappaEightLowerPoint E)) a = _
  rw [hcomp, kappaEightFullLowerProjection_apply, hlocal,
    (kappaEightFullLowerProjection (E := E)).hasFDerivAt.fderiv]

/-! ## Failed and successful response identities -/

/-- With a failed bit the exact response is assembled without any frontier
value or derivative in its hidden payload. -/
theorem kappaEightHardJointGradientResponse_failed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta R prob : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (hR : R ≠ 0) (kappa lam : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    kappaEightHardJointGradientResponse kappa eta prob 0 lam R L a =
      assembleKappaEightHardJointResponse kappa eta prob 0 lam R a
        (failedHiddenResponse eta
          (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1)) := by
  apply Prod.ext
  · rw [kappaEightHardJointGradientResponse,
      assembleKappaEightHardJointResponse]
    dsimp only
    rw [fderiv_kappaEightOracleFullHardUpper_as_assembled heta hT hR]
    simp only [failedHiddenResponse]
    rw [pullback_visibleChain_kappaEightHardProbeJetAt_hardRadius
      heta hT]
  · rw [kappaEightHardJointGradientResponse,
      assembleKappaEightHardJointResponse]
    dsimp only
    rw [fderiv_kappaEightFullSampleLower heta hT]
    simp [importanceSample, failedHiddenResponse,
      kappaEightCompensatedDerivativeFromJet]

/-- With a successful bit the exact response is reconstructed from the
visible prefix and precisely one hidden frontier first jet. -/
theorem kappaEightHardJointGradientResponse_successful
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {eta R prob : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (hR : R ≠ 0) (kappa lam : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E) :
    kappaEightHardJointGradientResponse kappa eta prob 1 lam R L a =
      assembleKappaEightHardJointResponse kappa eta prob 1 lam R a
        (successfulHiddenResponse eta
          (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1)) := by
  have hFrontier :=
    frontier_value_pullback_kappaEightHardProbeJetAt_hardRadius
      heta hT L a.2.1
  apply Prod.ext
  · rw [kappaEightHardJointGradientResponse,
      assembleKappaEightHardJointResponse]
    dsimp only
    rw [fderiv_kappaEightOracleFullHardUpper_as_assembled heta hT hR]
    simp only [successfulHiddenResponse]
    rw [pullback_visibleChain_kappaEightHardProbeJetAt_hardRadius
      heta hT]
  · rw [kappaEightHardJointGradientResponse,
      assembleKappaEightHardJointResponse]
    dsimp only
    rw [fderiv_kappaEightFullSampleLower heta hT]
    rw [fderiv_kappaEightFullCompensatedPair_eq_fromJet heta.ne'
      (hardFrontierMap_contDiff heta hT L)]
    simp only [successfulHiddenResponse]
    rw [hFrontier.1, hFrontier.2]
    rfl

/-! ## Uniform Borel prefix maps -/

def kappaEightFailedHardPrefixMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) (data : HiddenProbeJet E T) : KappaEightGradientResponse E :=
  assembleKappaEightHardJointResponse kappa eta prob 0 lam R a
    (failedPrefixResponse eta ell data)

def kappaEightSuccessfulHardPrefixMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) (data : HiddenProbeJet E T) : KappaEightGradientResponse E :=
  assembleKappaEightHardJointResponse kappa eta prob 1 lam R a
    (successfulPrefixResponse eta ell data)

theorem assembleKappaEightHardJointResponse_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (kappa eta prob xi lam R : ℝ) (a : KappaEightQueryPoint E) :
    Continuous (assembleKappaEightHardJointResponse
      kappa eta prob xi lam R a) := by
  unfold assembleKappaEightHardJointResponse
    kappaEightCompensatedDerivativeFromJet attenuatedFrontier
  fun_prop

theorem kappaEightFailedHardPrefixMap_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) :
    Continuous (kappaEightFailedHardPrefixMap
      (T := T) kappa eta prob lam R a ell) :=
  (assembleKappaEightHardJointResponse_continuous
    kappa eta prob 0 lam R a).comp (failedPrefixResponse_continuous eta)

theorem kappaEightSuccessfulHardPrefixMap_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) :
    Continuous (kappaEightSuccessfulHardPrefixMap
      (T := T) kappa eta prob lam R a ell) :=
  (assembleKappaEightHardJointResponse_continuous
    kappa eta prob 1 lam R a).comp (successfulPrefixResponse_continuous eta)

theorem kappaEightFailedHardPrefixMap_measurable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) :
    Measurable (kappaEightFailedHardPrefixMap
      (T := T) kappa eta prob lam R a ell) :=
  (kappaEightFailedHardPrefixMap_continuous
    kappa eta prob lam R a ell).measurable

theorem kappaEightSuccessfulHardPrefixMap_measurable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {T : ℕ} (kappa eta prob lam R : ℝ) (a : KappaEightQueryPoint E)
    (ell : ℕ) :
    Measurable (kappaEightSuccessfulHardPrefixMap
      (T := T) kappa eta prob lam R a ell) :=
  (kappaEightSuccessfulHardPrefixMap_continuous
    kappa eta prob lam R a ell).measurable

theorem kappaEightHardJointGradientResponse_failed_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T ell : ℕ} {eta R prob : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (hR : R ≠ 0) (kappa lam : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E)
    (hprog : progress (eta / 4)
      (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1).1 ≤ ell) :
    kappaEightHardJointGradientResponse kappa eta prob 0 lam R L a =
      kappaEightFailedHardPrefixMap kappa eta prob lam R a ell
        (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1) := by
  rw [kappaEightHardJointGradientResponse_failed heta hT hR]
  unfold kappaEightFailedHardPrefixMap
  rw [failedHiddenResponse_eq_prefix heta _ hprog]

theorem kappaEightHardJointGradientResponse_successful_eq_prefix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T ell : ℕ} {eta R prob : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (hR : R ≠ 0) (kappa lam : ℝ) (L : E →L[ℝ] ChainVector T)
    (a : KappaEightQueryPoint E)
    (hprog : progress (eta / 4)
      (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1).1 ≤ ell) :
    kappaEightHardJointGradientResponse kappa eta prob 1 lam R L a =
      kappaEightSuccessfulHardPrefixMap kappa eta prob lam R a ell
        (kappaEightHardProbeJetAt (hardRadius eta T) L a.2.1) := by
  rw [kappaEightHardJointGradientResponse_successful heta hT hR]
  unfold kappaEightSuccessfulHardPrefixMap
  rw [successfulHiddenResponse_eq_prefix heta _ hprog]

end

end BilevelLowerBound
