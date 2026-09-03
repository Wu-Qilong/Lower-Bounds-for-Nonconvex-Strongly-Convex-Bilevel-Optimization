# Verifying the `κ_y^8 ε^-6` Lean project

## 1. Open the standalone project

In VS Code, open this repository root, not an individual `.lean` file.  The
root contains:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
BilevelLowerBoundLean.lean
```

Opening the root lets Lean use the pinned toolchain and Mathlib revision.

## 2. Confirm the toolchain

Run in the integrated terminal:

```text
lean --version
lake --version
```

The project pins Lean `v4.33.0-rc2`.  If a different Lean version appears,
confirm that the terminal is located at this repository root.

## 3. Build the project

Run:

```text
lake build
```

The first build can be slow because Lake may need to download and compile the
pinned Mathlib dependencies.  A successful build ends with
`Build completed successfully`.

For a focused check of the new analytic core, run:

```text
lake build BilevelLowerBoundLean.KappaEightAmplifier
lake build BilevelLowerBoundLean.KappaEightHardInstance
lake build BilevelLowerBoundLean.KappaEightRegularity
lake build BilevelLowerBoundLean.KappaEightPopulationRegularity
lake build BilevelLowerBoundLean.KappaEightUpperRegularity
lake build BilevelLowerBoundLean.KappaEightHardOracleInterface
lake build BilevelLowerBoundLean.KappaEightConditionWitness
lake build BilevelLowerBoundLean.KappaEightSharpConstants
lake build BilevelLowerBoundLean.KappaEightParameterSelection
lake build BilevelLowerBoundLean.KappaEightPaperOracle
lake build BilevelLowerBoundLean.KappaEightPopulationClass
lake build BilevelLowerBoundLean.KappaEightSimultaneousCertificates
lake build BilevelLowerBoundLean.KappaEightPaperFinalTheorem
lake build BilevelLowerBoundLean.KappaEightImportSmokeTest
```

## 4. Run the theorem audits

Run:

```text
lake env lean BilevelLowerBoundLean/KappaEightAudit.lean
lake env lean BilevelLowerBoundLean/KappaEightCompleteAudit.lean
```

For every listed paper-facing declaration, the detailed audit uses:

1. `#print axioms`, which reports the logical dependencies;
2. `assert_no_sorry`, which fails if the declaration transitively depends on
   a `sorry` placeholder.

Standard foundations reported by Lean, such as `Classical.choice`, `propext`,
or `Quot.sound`, are not proof placeholders.  The cited adaptive-Haar result
appears as a theorem premise/interface rather than as a custom Lean axiom.
The complete audit then visits every theorem loaded from this standalone
project's modules and rejects any transitive dependence on `sorryAx`.

## 5. Run the complete verification script

```text
chmod +x verify.sh
./verify.sh
```

The script:

- directly builds `KappaEightPopulationClass`,
  `KappaEightSimultaneousCertificates`, `KappaEightPaperFinalTheorem`, and
  `KappaEightImportSmokeTest` (thereby checking their transitive new-module
  dependencies);
- compiles the detailed `KappaEightAudit.lean` and the exhaustive
  `KappaEightCompleteAudit.lean`;
- scans all project sources for `sorry`, `admit`, and custom `axiom`
  declarations.

It exits nonzero if any of these checks fails.

## 6. Inspect the new proof interactively

Read the new modules in this order:

```text
BilevelLowerBoundLean/KappaEightAmplifier.lean
BilevelLowerBoundLean/KappaEightHardInstance.lean
BilevelLowerBoundLean/KappaEightRegularity.lean
BilevelLowerBoundLean/KappaEightPopulationRegularity.lean
BilevelLowerBoundLean/KappaEightPaperClasses.lean
BilevelLowerBoundLean/KappaEightPaperHardInstance.lean
BilevelLowerBoundLean/KappaEightOracle.lean
BilevelLowerBoundLean/KappaEightPaperOracle.lean
BilevelLowerBoundLean/KappaEightHardOracleInterface.lean
BilevelLowerBoundLean/KappaEightUpperRegularity.lean
BilevelLowerBoundLean/KappaEightParameterSelection.lean
BilevelLowerBoundLean/KappaEightConditionWitness.lean
BilevelLowerBoundLean/KappaEightSharpConstants.lean
BilevelLowerBoundLean/KappaEightPopulationClass.lean
BilevelLowerBoundLean/KappaEightSimultaneousCertificates.lean
BilevelLowerBoundLean/KappaEightAssemblyBridge.lean
BilevelLowerBoundLean/KappaEightInteraction.lean
BilevelLowerBoundLean/KappaEightPaperMainTheorem.lean
BilevelLowerBoundLean/KappaEightPaperFinalTheorem.lean
BilevelLowerBoundLean/KappaEightImportSmokeTest.lean
BilevelLowerBoundLean/KappaEightAudit.lean
BilevelLowerBoundLean/KappaEightCompleteAudit.lean
```

Place the cursor inside a theorem.  The Lean Infoview shows the current goals
and hypotheses.  A clean Infoview plus the successful command-line build is
the local verification signal.

## 7. Check the three decisive calculations

### Attenuated stochastic signal

In `KappaEightRegularity.lean`, inspect
`kappaEightCompensatedPair_first_second_third_bounds` and
`exists_kappaEight_hard_compensated_pair_regularities`.  They prove globally,
including every mixed derivative,

```text
norm(D R)  <= Cnoise * eta^2 / kappa
norm(D2 R) <= CHess  * eta   / kappa
norm(D3 R) <= Cthird         / kappa.
```

### Full-Hessian Lipschitzness at `p = 1`

In `KappaEightPopulationRegularity.lean`, inspect
`kappaEightPopulationLower_hessian_lipschitz` and
`exists_kappaEightPopulationLower_certificates`.  The quadratic base has zero
third derivative, so the `D3 R` estimate yields a global Lipschitz bound for
the full lower Hessian.

### Actual `κ_y` and the eighth-power transfer

In `KappaEightConditionWitness.lean`, inspect
`kappaEight_condition_number_comparison_of_flat_point`, which proves
`κ <= κ_y <= 14κ`.  Then inspect
`kappaEightConditionNumber_callBudget_transfer` in
`KappaEightParameterSelection.lean`; the complexity replacement loses
`14^8` and no κ-dependent factor beyond that universal constant.

`KappaEightSharpConstants.lean` closes the order-completeness step: inspect
`exists_kappaEightFrame_sharp_lower_constants` to see that the sharp Hessian
modulus and upper bound used to define the actual `κ_y` genuinely exist.

### Exact one-frontier oracle interface

In `KappaEightHardOracleInterface.lean`, inspect
`fderiv_kappaEightFullCompensatedPair_eq_fromJet` and the two theorems ending
in `_eq_prefix`.  They show that the full stochastic gradient response is
reconstructed from public data plus one frontier first jet, and that a
failed response contains no current hidden-frontier information.  The
corresponding prefix maps are proved measurable.

### Population, SFO, and condition data for one hard instance

In `KappaEightPopulationClass.lean`, inspect
`exists_kappaEightPaperPopulationClassMember` for the complete population
class, including full joint-Hessian Lipschitzness.  Then inspect
`exists_simultaneous_kappaEight_hard_certificates` in
`KappaEightSimultaneousCertificates.lean`.  It synchronizes the population
certificate, admissible fresh Bernoulli SFO, and sharp condition data for the
same frame; these are not three unrelated existential hard instances.

### Final quantifiers and intrinsic scale

In `KappaEightPaperFinalTheorem.lean`, `ConcreteKappaEightLowerBound` records
the order `exists d, forall algorithm, exists problem, exists SFO`.
`concrete_kappaEight_paper_main_theorem` proves this proposition at

```text
max {Delta * kappa^2 / epsilon^2,
     Delta * sigma^2 * kappa^8 / epsilon^6},
```

conditional on `KappaEightCitedAdaptiveHaarPrinciple`.  The returned failure
certificate contains actual sharp condition data with
`kappa <= kappaY <= 14 * kappa`.  The intrinsic transfer theorem incurs
exactly the universal denominator `14^8` when the call budget is expressed
using `kappaY`.

## 8. Understand the reused modules

The `ZeroChain*`, `FrontierExtractor*`, soft-projection, fresh-sample,
coupled-process, Haar-geometry, progress, and gap-gradient modules are reused
as generic infrastructure.  They do not define the two-coordinate hard pair.
The new hard family begins in `KappaEightAmplifier.lean` and
`KappaEightHardInstance.lean`.

## 9. Understand the external boundary

The formalization does not derive deterministic-prefix Haar disintegration,
its independent bits-only stopped-prefix specialization, or the spherical-cap
estimate from a construction of Haar measure on the Stiefel manifold.  The
paper proves the stopped-prefix passage by a finite stratum argument.  Lean
packages the combined geometric input instead as the explicit proposition
`KappaEightCitedAdaptiveHaarPrinciple`, specialized definitionally to this
project's concrete hard population problem and Bernoulli SFO and requiring
`0 < Cvar` and `0 ≤ sigma`.  It is **not proved in Lean** here.  The final
theorem accepts a proof of it as `hHaar`;
applying that premise produces `KappaEightCitedAdaptiveHaarRun`.  Conditional
on this one premise, the concrete oracle's prefix identities, no-cap geometry,
union bound, progress argument, fixed-frame extraction, simultaneous
population/SFO certificates, intrinsic-condition transfer, and
expected-gradient failure are checked internally.

The fixed-frame certificate retains the strict quantitative margins
`E||grad|| > 3 epsilon/2` and `E||grad||^2 > 9 epsilon^2/4`, derived from the
event of probability at least `3/4` on which `||grad|| > 2 epsilon`.

To remove the final external boundary, one would need to formalize Stiefel
Haar disintegration, the stopped-prefix conditional law, and the cap estimate,
then discharge the cited premise.  No other mathematical lemma is
intentionally left external.
