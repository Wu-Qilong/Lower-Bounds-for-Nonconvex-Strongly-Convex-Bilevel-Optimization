# Formalization status: the `κ_y^8 ε^-6` hard instance

## Scope

This repository formalizes a new two-coordinate lower-level amplifier for a
stochastic NC--SC bilevel SFO lower bound.  The construction-level complexity
scale is

```text
Delta * kappa^2 / epsilon^2
  * max {1, sigma^2 * kappa^6 / epsilon^4}.
```

The actual lower condition number satisfies `κ <= κ_y <= 14κ`.  Therefore
the checked condition-number transfer replaces the nominal scale by the
intrinsic scale with a universal loss of `14^8`, giving the stochastic term
`Omega(Delta * sigma^2 * κ_y^8 * epsilon^-6)`.

This is an independent `κ_y^8 epsilon^-6` development.  The generic
zero-chain and probability lemmas inherited from the earlier codebase are
infrastructure only; the two-dimensional amplifier, population problem,
SFO, simultaneous certificates, and final specialization are new
`KappaEight*` declarations.

“Complete” below means that the named declaration type-checks without
`sorry`, `admit`, or a custom Lean axiom.  It may use ordinary Mathlib
foundations such as `Classical.choice`, `propext`, or quotient soundness.

## New two-coordinate construction

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Auxiliary lower variable `(v₁,v₂)` and amplifier coefficients | `AmplifierAux`, `amplifierDiag`, `amplifierOffDiag`, `amplifierQuadratic`, `amplifierHessianForm` in `KappaEightAmplifier.lean` | complete |
| Eigenvalues `1/κ` and `1`, coercivity, and upper spectral bound | `amplifierHessianForm_diagonalize`, `amplifierHessianForm_coercive`, `amplifierHessianForm_le` | complete |
| Attenuated frontier and inverse transmission to the second coordinate | `attenuatedFrontier`, `amplifierHessianForm_proposed`, `amplified_proposed_second_coordinate` | complete |
| Global nonnegativity and unique zero of the compensated amplifier block | `amplifiedScalarBlock_nonneg`, `amplifiedScalarBlock_eq_zero_iff` | complete |
| New population/sample lower pair and upper objective | `kappaEightPopulationLower`, `kappaEightSampleLower`, `kappaEightHardUpper` in `KappaEightHardInstance.lean` | complete |
| Bernoulli population identity | `kappaEightSampleLower_bernoulli_population` | complete |
| Exact global lower minimizer and uniqueness | `kappaEightPopulationLower_minimum`, `kappaEightPopulationLower_unique_minimizer` | complete |
| Exact recovery of the unattenuated hyper-objective | `kappaEightHardUpper_at_proposed_solution` | complete |

## Smoothness, strong convexity, and `p = 1`

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Attenuation of all jets by `O(1/κ)` | `norm_iteratedFDeriv_kappaEightAttenuatedFrontier_le`, `kappaEightAttenuatedFrontier_scales` in `KappaEightRegularity.lean` | complete |
| Full mixed derivative bounds `D R=O(η²/κ)`, `D²R=O(η/κ)`, `D³R=O(1/κ)` | `kappaEightCompensatedPair_first_second_third_bounds` | complete |
| Uniform hidden-frontier constants | `exists_kappaEight_hard_compensated_pair_regularities` | complete |
| Exact Hessian and zero third derivative of the amplifier quadratic | `iteratedFDeriv_amplifierQuadratic_two_apply`, `iteratedFDeriv_amplifierQuadratic_three_eq_zero` in `KappaEightPopulationRegularity.lean` | complete |
| Complete lower-base coercivity and bounded Hessian | `kappaEightLowerBaseSlice_coercive`, `norm_iteratedFDeriv_kappaEightLowerBaseSlice_two_le_six` | complete |
| Strong Hessian after the compensated perturbation | `kappaEightLowerBase_add_perturbation_strong_hessian`, `kappaEightPopulationLower_strong_hessian` | complete |
| Population Hessian and third-derivative bounds | `kappaEightPopulationLower_second_bound`, `kappaEightPopulationLower_third_bound` | complete |
| Global full-Hessian Lipschitz condition required at `p=1` | `kappaEightPopulationLower_hessian_lipschitz` | complete |
| One concrete uniform certificate containing smoothness, strong convexity, and Hessian Lipschitzness | `exists_kappaEightPopulationLower_certificates` | complete |

## Oracle and parameter scale

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Full-query sample and population lower objectives | `kappaEightFullSampleLower`, `kappaEightFullPopulationLower_eq_base_add_frontier` in `KappaEightOracle.lean` | complete |
| Exact sample derivative and unbiased population gradient | `fderiv_kappaEightFullSampleLower`, `kappaEightFullSampleLower_bernoulli_gradient_unbiased` | complete |
| Uniform `O(η²/κ)` stochastic-gradient signal and SFO variance certificate | `exists_kappaEightFullCompensatedPair_gradient_bound`, `exists_kappaEightFullSampleLower_oracle_properties` | complete |
| Exact reconstruction of the compensated derivative from a frontier first jet | `fderiv_kappaEightCompensatedPair_eq_fromJet`, `fderiv_kappaEightFullCompensatedPair_eq_fromJet` in `KappaEightHardOracleInterface.lean` | complete |
| Complete upper/lower stochastic response and its failed/successful forms | `kappaEightHardJointGradientResponse_failed`, `kappaEightHardJointGradientResponse_successful` | complete |
| Measurable visible-prefix response maps and exact one-frontier identities | `kappaEightFailedHardPrefixMap_measurable`, `kappaEightSuccessfulHardPrefixMap_measurable`, `kappaEightHardJointGradientResponse_failed_eq_prefix`, `kappaEightHardJointGradientResponse_successful_eq_prefix` | complete |
| Dimension-free upper Hessian and gradient-Lipschitz bounds | `exists_kappaEightFullHardUpper_second_regularities` in `KappaEightUpperRegularity.lean` | complete |
| Uniform lower-variable derivative bound for the upper objective | `exists_kappaEightFullHardUpper_lowerDerivative_bound` | complete |
| Amplified reveal probability | `kappaEightRevealProbability` in `KappaEightParameterSelection.lean` | complete |
| Positivity, unit-interval membership, variance bound, and exact inverse probability | `kappaEightRevealProbability_pos`, `kappaEightRevealProbability_mem_unitInterval`, `kappaEightRevealProbability_variance_le`, `one_div_kappaEightRevealProbability` | complete |
| Final choices of `η` and chain length | `kappaEightFinalEta`, `kappaEightFinalChainLength` | complete |
| Exact call scale and `T/(8p)` comparison | `kappaEightComplexityScale_expand`, `kappaEightFinal_T_over_p_main_scale`, `kappaEightCallBudget_implies_progress_condition` | complete |
| Intrinsic condition-number transfer with eighth-power loss | `kappaEightConditionNumber_scale_comparison`, `kappaEightConditionNumber_callBudget_transfer`, `kappaEightConditionNumber_scale_sandwich` | complete |

## Actual intrinsic condition number

The formal population class uses `muG` for its certified strong-convexity
coefficient.  The sharp condition-data structure separately records the
actual modulus `muGAct` and defines `kappaY = Ly / muGAct`.  The theorem
`KappaEightPopulationClassMember.muG_le_muGAct` proves `muG <= muGAct`, so
the formal interface includes the compatibility implication stated after
Definition 3.2.

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Flat full-progress point for the new compensated block | `iteratedFDeriv_kappaEightCompensatedPair_two_eq_zero_at_fullProgress` in `KappaEightConditionWitness.lean` | complete |
| Weak and strong amplifier directions | `kappaEightLowerBaseSlice_weak_witness`, `kappaEightLowerBaseSlice_strong_witness` | complete |
| Sharp comparison `κ <= κ_y <= 14κ` | `kappaEight_condition_number_comparison_of_flat_point`, `kappaEight_hardFrontier_condition_number_comparison` | complete |
| Paper-class bridge for the intrinsic condition data | `KappaEightLowerConditionData.condition_number_comparison_of_lower_eq` | complete |
| Certified-to-actual curvature compatibility `muG <= muGAct` | `KappaEightPopulationClassMember.muG_le_muGAct` | complete |
| Existence of the sharp lower Hessian modulus, sharp Hessian upper bound, and concrete condition data | `exists_kappaEight_sharp_lower_hessian_modulus`, `exists_kappaEight_sharp_lower_hessian_upper_bound`, `exists_kappaEightFrame_sharp_lower_constants` in `KappaEightSharpConstants.lean` | complete |

## Population class and simultaneous certificates

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Monotonicity under enlarged smoothness/gap budgets and a reduced certified strong-convexity modulus | `KappaEightPopulationClassMember.mono` in `KappaEightPopulationClass.lean` | complete |
| Removal of the construction-dependent `eta * sqrt T` factor from the final upper lower-variable derivative budget | `KappaEightPopulationClassMember.to_final_uniform_bounds` | complete |
| Uniform population-class membership for every orthonormal hidden frame, including the full joint `p=1` Hessian-Lipschitz condition | `exists_kappaEightPaperPopulationClassMember` | complete |
| One common choice of universal constants certifying the population problem, fresh Bernoulli SFO, and sharp intrinsic condition data for the same frame | `exists_simultaneous_kappaEight_hard_certificates` in `KappaEightSimultaneousCertificates.lean` | complete |

## Paper-level construction and lower-bound assembly

| Paper component | Lean declarations | Status |
| --- | --- | --- |
| Paper population problem with the exact lower solution | `kappaEightPaperPopulationProblem`, `exists_kappaEightPaperPopulationProblem` in `KappaEightPaperHardInstance.lean` | complete |
| Recursive adaptive transcript, query, output, and past sigma-fields | `kappaEightRunTranscript`, `kappaEightRunQuery`, `kappaEightRunOutput`, `kappaEightRunPastMeasurableSpace` in `KappaEightInteraction.lean` | complete |
| Reduction of the new reveal probability to the generic one-frontier assembly at effective noise `sigma*κ` | `kappaEightRevealProbability_eq_revealProbability_mul` in `KappaEightAssemblyBridge.lean` | complete; this reuses only the generic probability theorem, not the old scalar hard family |
| `κ^8` specialization of the progress/fixed-frame assembly | `moment_failure_of_large_event_with_margin`, `kappaEight_main_lower_bound_assembly` | complete conditional on the explicit adaptive-Haar inputs; retains the strict margins `E||grad|| > 3 epsilon/2` and `E||grad||^2 > 9 epsilon^2/4` |
| Actual run is tied to the cited adaptive-Haar interface | `KappaEightCitedAdaptiveHaarRun.output_eq_run`, `past_eq_actual_run`, `success_eq_bit` in `KappaEightPaperMainTheorem.lean` | explicit interface obligations |
| Fixed-frame expected-gradient failure for the amplified scale | `kappaEight_expectation_from_cited_run` | complete conditional on `KappaEightCitedAdaptiveHaarRun`; first- and second-moment margins are `3/2` and `9/4` |
| Concrete run-failure certificate, including both first- and second-moment stationarity failure | `KappaEightRunFailure` in `KappaEightPaperFinalTheorem.lean` | complete with the same strict uniform margins |
| Literal minimax quantifier order `exists dimension, forall algorithm, exists problem, exists SFO` | `ConcreteKappaEightLowerBound` | complete as a definition |
| Replacement of the nominal construction scale by the actual condition number with `14^8` loss | `KappaEightRunFailure.intrinsic_scale_sandwich`, `KappaEightRunFailure.intrinsic_budget_is_covered` | complete |
| Fully quantified paper theorem at the `kappa^8 epsilon^-6` construction scale | `concrete_kappaEight_paper_main_theorem` | complete conditional on `KappaEightCitedAdaptiveHaarPrinciple`, which is restricted to the concrete hard family |

## Reused generic modules

The following are reused mathematical infrastructure and are not assertions
that the old scalar hard instance proves the new result:

- `ZeroChain*.lean`: smooth zero-chain identities and derivative bounds;
- `FrontierExtractor*.lean`, `FrontierGateQuantitative.lean`, and
  `VisibleChainCylinder.lean`: one-frontier support and jet identities;
- `CompositionScales.lean` and `SoftProjectionQuantitative.lean`: generic
  composition and soft-projection estimates;
- `FreshSample.lean`, `CoupledProcess.lean`, `HaarGeometry.lean`,
  `HaarProbability.lean`, and `ProgressBound.lean`: fresh-bit and adaptive
  progress bookkeeping;
- `GapGradient.lean`, `PaperExpectation.lean`, and the probability portion
  of `MainTheorem.lean`: generic gap-gradient and fixed-frame extraction.

The old scalar `compensatedBlock`, scalar lower solution, and its stochastic
signal estimate are not used as the new hard family.

## External mathematical boundary

The sole external mathematical input consists of deterministic-prefix Haar
disintegration, its independent bits-only stopped-prefix specialization, and
the spherical-cap estimate.  The paper proves the stopped-prefix passage by a
finite stratum argument; Lean does not rebuild it from Stiefel Haar measure.
The exact paper-facing proposition packaging these facts is
`KappaEightCitedAdaptiveHaarPrinciple`.  The proposition is definitionally
specialized to `kappaEightPaperPopulationProblem` and
`kappaEightPaperHardBernoulliSFO`; it does not grant a conclusion for an
arbitrary frame-indexed oracle, and it requires `0 < Cvar` and `0 ≤ sigma`
before constructing the Bernoulli run.  The failed and successful
one-frontier prefix identities for this pair are proved in
`KappaEightHardOracleInterface.lean`.  The theorem
`concrete_kappaEight_paper_main_theorem` explicitly assumes
`hHaar : KappaEightCitedAdaptiveHaarPrinciple CH`; this premise is **not
proved in Lean** in the present repository.  Applying it returns a
`KappaEightCitedAdaptiveHaarRun`, whose seed law, fresh samples, conditional
cap estimates, residual geometry, and exact recursive output are visible
fields rather than hidden axioms.

Everything after this premise—no-cap geometry, finite union bound, Markov
argument, fixed-frame selection, and expected-gradient failure—is checked in
Lean.  A completely self-contained development would additionally formalize
Haar measure on the relevant Stiefel manifold and prove the deterministic- and
stopped-prefix conditional laws and cap estimate internally.

## Norm encoding relative to the paper

The LaTeX paper uses the Euclidean norm after identifying the lower variable
with `R^(d+2)`.  Lean instead keeps the construction modular as
`E × (R × R)`, equipped with Mathlib's product norm.  These norms are
uniformly equivalent with constants independent of the ambient dimension and
all complexity parameters, so the translation changes only universal
regularity constants and preserves the `kappa_y^8 epsilon^-6` order.  The
current repository does not contain a literal Euclidean `Fin (d+2)` isometry
bridge.  Accordingly, the formal intrinsic-condition certificate and the
paper's Euclidean spectral condition number correspond up to these universal
norm-equivalence factors, not by equality of every displayed numerical
constant.

## Audit policy

Run:

```text
lake build
lake build BilevelLowerBoundLean.KappaEightPopulationClass
lake build BilevelLowerBoundLean.KappaEightSimultaneousCertificates
lake build BilevelLowerBoundLean.KappaEightPaperFinalTheorem
lake build BilevelLowerBoundLean.KappaEightImportSmokeTest
lake env lean BilevelLowerBoundLean/KappaEightAudit.lean
lake env lean BilevelLowerBoundLean/KappaEightCompleteAudit.lean
```

`KappaEightAudit.lean` prints dependencies for paper-facing declarations and
uses `assert_no_sorry`.  `KappaEightCompleteAudit.lean` mechanically checks
every theorem loaded from a module of this standalone project for transitive
dependence on `sorryAx`, including reused generic infrastructure and technical
helper lemmas that are explained at section or module level rather than
listed individually.  `verify.sh`
additionally scans every source for `sorry`, `admit`, and custom `axiom`
declarations.
