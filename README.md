# Lean verification of the $\kappa_y^{8}\epsilon^{-6}$ stochastic bilevel lower bound

This is a standalone Lean 4 + Mathlib project for the two-coordinate hard
instance used to prove the stochastic NC--SC bilevel lower bound

```text
Omega(Delta * kappa_y^2 / epsilon^2 * max {1, sigma^2 * kappa_y^6 / epsilon^4}).
```

In the noise-dominated regime, this gives
`Omega(Delta * sigma^2 * kappa_y^8 * epsilon^-6)`.  The
`KappaEight*.lean` modules define the hard pair and its stochastic oracle,
establish the population and regularity properties, verify the parameter
choices, and derive the final complexity statement.

## Hard-instance construction

The lower auxiliary variable is two-dimensional, `v = (v₁,v₂)`.  Its
quadratic block has eigenvalues `1/κ` and `1`.  Before the stochastic
frontier term enters the lower objective, it is divided by the off-diagonal
entry `sκ` of the inverse quadratic block.  Solving the lower problem
multiplies this term by `sκ` in `v₂`, and the upper objective depends linearly
on this coordinate.  Thus the unscaled frontier term is recovered after the
lower solution is substituted.

The construction therefore has the following two properties:

- after substitution of the exact lower solution, the population
  hyper-objective is the zero-chain objective used in the progress argument;
- the randomized lower-gradient contribution has norm `O(η²/κ)`.

The Bernoulli probability can consequently be chosen as

```text
min {1, Cvar * eta^4 / (sigma^2 * kappa^2)}.
```

With `η = 4 * epsilon / κ` and
`T = Theta(Delta * κ^2 / epsilon^2)`, the one-frontier progress argument
then gives the `κ^8 epsilon^-6` stochastic term.

## Analytic guarantees checked in Lean

Subject to the adaptive-Haar premise described under
**Verification boundary**, the modules verify the following claims without
`sorry`, `admit`, or custom axiom declarations:

- the spectrum of the two-coordinate quadratic block, the relevant entries
  of its inverse, global nonnegativity of the compensated block, and the
  uniqueness of its zero;
- the exact global lower minimizer and the exact population
  hyper-objective identity;
- attenuation of the first three derivatives and the mixed derivative
  bounds `D R = O(η²/κ)`, `D²R = O(η/κ)`, and `D³R = O(1/κ)`;
- lower strong convexity, full-Hessian bounds, and global full-Hessian
  Lipschitzness, including the full-Hessian Lipschitz property used in the
  paper's first-order-smooth setting;
- unbiased Bernoulli importance weighting, variance at most `sigma²`, and
  the formula for the Bernoulli probability;
- a one-frontier interface for the complete upper/lower oracle response:
  when the Bernoulli variable is zero, the response is a function of the
  exposed prefix, while a value of one may expose the next frontier first
  jet;
- dimension-free Hessian and gradient-Lipschitz bounds for the upper
  objective, together with its derivative bounds in the lower variable;
- membership of the hard pair in a population class carrying the required
  upper- and lower-level smoothness, lower strong convexity, full-Hessian
  Lipschitzness, upper-objective lower-variable derivative, and initial-gap
  certificates;
- simultaneous population-class, fresh-sample SFO, and intrinsic
  condition-number certificates for the same hidden frame;
- the parameter choices and the resulting `κ^8 epsilon^-6` call scale;
- the intrinsic condition-number comparison
  `κ <= κ_y <= 14 * κ`, including existence of the sharp lower-Hessian
  modulus and Hessian upper bound used to define `κ_y`;
- the minimax quantifier order and the final lower-bound consequence,
  conditional on the explicitly stated adaptive-Haar principle.

## Main formal theorem

The construction-scale theorem is
`concrete_kappaEight_paper_main_theorem` in
`KappaEightPaperFinalTheorem.lean`.  It constructs a finite ambient dimension
and proves that, for every adaptive randomized algorithm below the stated
call budget, there are a population problem and an admissible fresh-sample
SFO for which the output satisfies

```text
E||grad||   > 3 * epsilon / 2,
E||grad||^2 > 9 * epsilon^2 / 4.
```

These bounds follow from an event of probability at least `3/4` on which
`||grad|| > 2 * epsilon`.  The construction-scale call bound expands as

```text
max {Delta * kappa^2 / epsilon^2, Delta * sigma^2 * kappa^8 / epsilon^6}.
```

## Strong-convexity and condition-number notation

The class parameter `muG` is the certified strong-convexity modulus of the
lower objective `g`, whereas `muGAct` is its sharp lower-Hessian modulus.  The
intrinsic condition data use

```text
kappaY = Ly / muGAct.
```

`KappaEightPopulationClassMember.muG_le_muGAct` proves the Definition 3.2
compatibility inequality `muG <= muGAct`.  The formalized instance satisfies
`kappa <= kappaY <= 14 * kappa`.  Replacing the construction parameter by the
actual `kappaY` therefore changes the bound by at most the universal factor
`14^8` and preserves the `kappaY^8 epsilon^-6` stochastic order.

## Formalization structure

The project contains separate modules for the smooth zero-chain, frontier
extractor, soft projection, two-coordinate compensated block, hard bilevel
pair, fresh-sample conditional expectation, population regularity,
one-frontier process, finite-event probability estimates, gap-gradient
argument, intrinsic condition-number transfer, fixed-frame extraction, and
final theorem assembly.  This organization separates the analytic
properties of the hard instance from the probabilistic random-rotation
argument.

## Verification boundary

The external mathematical input consists of deterministic-prefix Haar
disintegration, its independent bits-only stopped-prefix specialization, and
the spherical-cap estimate cited in the paper.  The paper proves the finite
stratum stopped-prefix passage, but this Lean project does not construct
Stiefel Haar measure and reprove that passage from first principles.

The required input is stated as
`KappaEightCitedAdaptiveHaarPrinciple`.  It is restricted to the concrete
population problem and Bernoulli SFO formalized in this project, and its
interface includes the conditions `0 < Cvar` and `0 <= sigma`.  The final
theorem takes a proof of this proposition as an explicit argument.  The
principle is not proved in Lean here, but it is neither declared as an axiom
nor hidden in the oracle model.

Conditional on this premise, Lean checks the deterministic geometry, the
prefix interface for the two Bernoulli outcomes, the population and oracle
certificates, the probability bookkeeping, fixed-frame extraction,
intrinsic condition-number transfer, and the final minimax consequence.

## Representation of the lower variable

The paper identifies the lower variable with Euclidean `R^(d+2)`.  The Lean
project represents it as `E × (R × R)` with Mathlib's product norm.  These
norms are uniformly equivalent, with constants depending only on the three
displayed blocks and not on `d`, `kappa`, or `epsilon`.  This representation
therefore preserves the complexity orders and changes only universal
regularity constants.  It is not a literal isometric identification, so
`conditionData.kappaY` is the norm-equivalent condition certificate used by
the Lean encoding rather than the paper's Euclidean spectral ratio with the
same numerical constants.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the theorem map and
the precise formalization boundary.

## Quick verification

From the project directory, run

```text
./verify.sh
```

The script builds the population-class, simultaneous-certificate,
final-theorem, import-smoke-test, `KappaEightAudit.lean`, and
`KappaEightCompleteAudit.lean` modules.  It also scans the source files for
placeholders and custom axiom declarations.  The project pins Lean
`v4.33.0-rc2` and the corresponding Mathlib revision in `lean-toolchain` and
`lake-manifest.json`.
