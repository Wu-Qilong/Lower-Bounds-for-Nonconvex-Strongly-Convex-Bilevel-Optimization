# Project guide: independent `κ_y^8 ε^-6` formalization

This directory is a standalone Lean project for the two-coordinate amplified
hard instance.  It intentionally keeps the new construction in
`KappaEight*.lean` modules instead of rewriting the old scalar hard-family
files.

## Main entry points

- `BilevelLowerBoundLean/KappaEightAmplifier.lean`: two-dimensional
  amplifier algebra.
- `BilevelLowerBoundLean/KappaEightHardInstance.lean`: the new population
  and sample hard pair.
- `BilevelLowerBoundLean/KappaEightRegularity.lean`: attenuation and full
  mixed `D1`--`D3` estimates.
- `BilevelLowerBoundLean/KappaEightPopulationRegularity.lean`: complete
  population smoothness, strong convexity, and full-Hessian Lipschitzness.
- `BilevelLowerBoundLean/KappaEightOracle.lean`: stochastic first-order
  oracle realization.
- `BilevelLowerBoundLean/KappaEightHardOracleInterface.lean`: exact
  one-frontier reconstruction of the complete hard-oracle response and its
  measurable failed/successful prefix maps.
- `BilevelLowerBoundLean/KappaEightUpperRegularity.lean`: dimension-free
  upper-objective Hessian and lower-variable derivative certificates.
- `BilevelLowerBoundLean/KappaEightParameterSelection.lean`: reveal
  probability and `κ^8` call-scale algebra.
- `BilevelLowerBoundLean/KappaEightConditionWitness.lean`: actual intrinsic
  condition number and the comparison `κ <= κ_y <= 14κ`.
- `BilevelLowerBoundLean/KappaEightSharpConstants.lean`: existence of the
  sharp modulus and Hessian upper bound realizing that intrinsic condition
  number.
- `BilevelLowerBoundLean/KappaEightPopulationClass.lean`: the full
  population-class certificate, including joint `p=1` Hessian Lipschitzness
  and a construction-independent upper lower-variable derivative budget.
- `BilevelLowerBoundLean/KappaEightPaperOracle.lean`: the concrete fresh
  Bernoulli SFO attached to the amplified paper problem.
- `BilevelLowerBoundLean/KappaEightSimultaneousCertificates.lean`: one
  synchronized witness for population membership, SFO admissibility, and
  sharp intrinsic condition data on the same hidden frame.
- `BilevelLowerBoundLean/KappaEightPaperMainTheorem.lean`: checked
  fixed-frame consequence of an explicit cited adaptive-Haar run, retaining
  `E||grad|| > 3 epsilon/2` and `E||grad||^2 > 9 epsilon^2/4`.
- `BilevelLowerBoundLean/KappaEightPaperFinalTheorem.lean`: the concrete
  outer quantifiers and construction-scale theorem, conditional on
  `KappaEightCitedAdaptiveHaarPrinciple`.
- `BilevelLowerBoundLean/KappaEightImportSmokeTest.lean`: combined-import
  guard against declaration collisions among the new analytic and oracle
  modules.
- `BilevelLowerBoundLean/KappaEightAudit.lean`: paper-facing axiom and
  no-placeholder audit.
- `BilevelLowerBoundLean/KappaEightCompleteAudit.lean`: mechanical
  no-`sorryAx` audit of every theorem loaded from this standalone project's
  modules, including reused infrastructure and internal helper lemmas.
- `FORMALIZATION_STATUS.md`: paper-to-Lean theorem map and verification
  boundary.

## Recommended reading order

1. Generic smooth chain infrastructure:
   `ZeroChain*.lean`, `FrontierExtractor*.lean`,
   `FrontierGateQuantitative.lean`, `CompositionScales.lean`, and
   `SoftProjectionQuantitative.lean`.
2. New hard family:
   `KappaEightAmplifier.lean` and `KappaEightHardInstance.lean`.
3. New analytic certificates:
   `KappaEightRegularity.lean`, `KappaEightPopulationRegularity.lean`, and
   `KappaEightUpperRegularity.lean`.
4. Paper problem and oracle:
   `KappaEightPaperClasses.lean`, `KappaEightPaperHardInstance.lean`, and
   `KappaEightOracle.lean`, followed by `KappaEightPaperOracle.lean` and
   `KappaEightHardOracleInterface.lean`.
5. Amplified parameter selection:
   `KappaEightParameterSelection.lean` and
   `KappaEightAssemblyBridge.lean`, together with the intrinsic-condition
   certificates in `KappaEightConditionWitness.lean` and
   `KappaEightSharpConstants.lean`.
6. Unified class certificates:
   `KappaEightPopulationClass.lean` and
   `KappaEightSimultaneousCertificates.lean`.
7. Actual adaptive run and cited boundary:
   `KappaEightInteraction.lean` and
   `KappaEightPaperMainTheorem.lean`, then the outer quantifiers in
   `KappaEightPaperFinalTheorem.lean`.
8. Integration and audit:
   `KappaEightImportSmokeTest.lean`, `KappaEightAudit.lean`, and
   `KappaEightCompleteAudit.lean`.

## What is new and what is reused

The new proof owns the two-coordinate amplifier, attenuated compensation,
exact lower solution, stochastic lower oracle, full population certificates,
sharp condition witness, and eighth-power parameter transfer.

The project reuses generic theorems for the zero-chain, extractor support,
soft projection, fresh Bernoulli samples, coupled one-frontier process,
adaptive no-cap geometry, probability bookkeeping, and gap-gradient
argument.  `KappaEightAssemblyBridge.lean` specializes that generic
probability assembly using effective noise `sigma*κ`; it does not substitute
the old scalar hard pair for the new one.

## Key scales

```text
eta = 4 * epsilon / kappa
T = Theta(Delta * kappa^2 / epsilon^2)
p_reveal = min {1, Cvar * eta^4 / (sigma^2 * kappa^2)}
T / p_reveal
  = Theta(Delta * kappa^2 / epsilon^2
      * max {1, sigma^2 * kappa^6 / epsilon^4}).
```

The intrinsic comparison is

```text
kappa <= kappa_y <= 14 * kappa.
```

Thus replacing the construction parameter by `kappa_y` costs `14^8`, a
universal constant, and preserves the `κ_y^8 epsilon^-6` order.

The final theorem keeps the nominal `kappa` in its construction parameters
and returns sharp data `kappa <= kappaY <= 14 * kappa` for the selected
problem.  `KappaEightRunFailure.intrinsic_budget_is_covered` is the checked
bridge showing exactly where the factor `14^8` enters when a call budget is
written in terms of the actual `kappaY`.

## `p = 1` regularity

The two-coordinate compensation has global third derivative
`O(1/kappa)`.  Since the remaining lower base is quadratic, Lean derives a
global Lipschitz bound for the **full** lower Hessian in
`kappaEightPopulationLower_hessian_lipschitz` and packages it in
`exists_kappaEightPopulationLower_certificates`.  This is the stronger
full-Hessian Lipschitz condition needed for the `p = 1` result.

## External boundary

The only external mathematical ingredient is deterministic-prefix Haar
disintegration, its independent bits-only stopped-prefix specialization, and
the spherical-cap estimate.  The stopped-prefix passage is proved stratumwise
in the LaTeX paper but is not reconstructed from Haar measure in Lean.  Their
exact Lean interface is `KappaEightCitedAdaptiveHaarPrinciple`.  This interface is
restricted definitionally to the concrete population problem and Bernoulli
SFO of this project; it is not a principle for arbitrary frame-indexed
oracles, and it applies only under `0 < Cvar` and `0 ≤ sigma`.  The repository
does not prove this proposition:
`concrete_kappaEight_paper_main_theorem` takes it as an explicit premise and
derives the final result from the returned run structure.  The failed and
successful prefix identities needed to justify applying the cited principle
to this family are proved in `KappaEightHardOracleInterface.lean`.  No custom
Lean axiom is declared.  See
`FORMALIZATION_STATUS.md` for the precise fields and internally checked
consequences.

## Build and audit

From the repository root:

```text
./verify.sh
```

The first build may download and compile the pinned Mathlib revision.  The
large generated `.lake` directory is not part of the source snapshot.

The detailed audit lists the paper-facing statements one by one.  The
complete audit additionally visits every theorem loaded from this project's
modules, so generic infrastructure and technical helpers receive the same
no-placeholder check even when their explanation is given at section or
module level.
