# Lean verification of the `κ_y^8 ε^-6` stochastic bilevel lower bound

This is a standalone Lean 4 + Mathlib project for the two-coordinate hard
instance underlying the stochastic NC--SC bilevel lower bound

```text
Omega(Delta * kappa_y^2 / epsilon^2
  * max {1, sigma^2 * kappa_y^6 / epsilon^4}).
```

Its stochastic term is
`Omega(Delta * sigma^2 * kappa_y^8 * epsilon^-6)`.  This repository is not
the old `κ_y^6 ε^-6` hard family with a few constants changed.  The new hard
pair, its oracle, its population certificates, and its parameter algebra are
defined in new `KappaEight*.lean` modules.

## What is new in the hard instance

The lower auxiliary variable is two-dimensional, `v = (v₁,v₂)`.  Its
quadratic amplifier has eigenvalues `1/κ` and `1`.  The hidden frontier is
attenuated by the off-diagonal inverse coefficient before it enters the
randomized lower block.  Solving the lower problem exactly restores the
unattenuated frontier in `v₂`, which the upper objective reads linearly.

This has two simultaneous effects:

- the population hyper-objective is the same zero-chain objective needed by
  the progress argument;
- the randomized lower-gradient signal is only `O(η²/κ)`.

Consequently the reveal probability is

```text
min {1, Cvar * eta^4 / (sigma^2 * kappa^2)}.
```

With the exact Lean choice `η = 4 * epsilon/κ` and chain length
`T = Theta(Delta * κ^2 / epsilon^2)`, the one-frontier argument gives the
`κ^8 epsilon^-6` stochastic term.

## Analytic guarantees checked in Lean

The new modules verify, without `sorry`, `admit`, or custom axioms:

- the amplifier spectrum, inverse transmission, global nonnegativity, and
  unique zero of the compensated two-coordinate block;
- the exact global lower minimizer and exact hyper-objective identity;
- attenuation of the first three derivatives and the full mixed bounds
  `D R = O(η²/κ)`, `D²R = O(η/κ)`, and `D³R = O(1/κ)`;
- lower strong convexity, full Hessian bounds, and global full-Hessian
  Lipschitzness.  The last property is the full-Hessian Lipschitz condition
  required by the `p = 1` statement;
- unbiased Bernoulli importance weighting, variance at most `sigma²`, and
  the amplified reveal-probability identity;
- an exact one-frontier interface for the complete upper/lower oracle
  response: failed calls are visible-prefix functions and successful calls
  expose exactly the next hidden frontier first jet;
- dimension-free upper-objective Hessian, gradient-Lipschitz, and
  lower-variable derivative bounds;
- membership of the concrete hard pair in one population class carrying the
  upper/lower smoothness, lower strong-convexity, full-Hessian Lipschitz,
  upper lower-variable derivative, and initial-gap certificates;
- simultaneous certificates for the same hidden frame: population-class
  membership, an admissible fresh Bernoulli SFO, and sharp intrinsic lower
  condition data;
- parameter selection and the resulting `κ^8 epsilon^-6` call scale;
- the sharp intrinsic condition-number comparison
  `κ <= κ_y <= 14 κ`.  Replacing the construction parameter by the actual
  `κ_y` therefore loses only the universal factor `14^8`.  The sharp
  modulus and Hessian upper bound whose ratio defines `κ_y` are proved to
  exist, rather than postulated;
- the concrete minimax quantifier order and final lower-bound consequence,
  conditional on the explicitly named cited adaptive-Haar principle.

The construction-scale result is `concrete_kappaEight_paper_main_theorem` in
`KappaEightPaperFinalTheorem.lean`.  It constructs an ambient dimension and,
for every adaptive randomized algorithm below the stated call budget, a
population problem, an admissible SFO, and a run whose first and second
stationarity moments satisfy the strict uniform margins
`E||grad|| > 3 epsilon / 2` and
`E||grad||^2 > 9 epsilon^2 / 4`.  These constants come from a fixed-frame
event of probability at least `3/4` on which `||grad|| > 2 epsilon`.
Its construction scale expands exactly as

```text
max {Delta * kappa^2 / epsilon^2,
     Delta * sigma^2 * kappa^8 / epsilon^6}.
```

The class parameter `muG` is the certified strong-convexity modulus of the
lower objective `g`, whereas `muGAct` is its sharp actual lower-Hessian
modulus.  The intrinsic condition data use
`kappaY = Ly / muGAct`, and
`KappaEightPopulationClassMember.muG_le_muGAct` proves the Definition 3.2
compatibility inequality `muG <= muGAct`.  The theorem carries sharp data
satisfying `kappa <= kappaY <= 14 * kappa`.  Expressing the budget using the
actual `kappaY` costs the universal factor `14^8`; it does not change the
`kappaY^8 epsilon^-6` stochastic order.

## Reused generic infrastructure

Several modules predate this two-coordinate construction and are reused as
generic lemmas: the smooth zero-chain, frontier extractor, soft projection,
fresh-sample conditional expectation, coupled one-frontier process,
finite-event probability bookkeeping, gap-gradient argument, and
fixed-frame extraction.  Reusing those theorems does **not** identify the
old scalar hard family with the new proof.  In particular, the new
amplifier, hard pair, stochastic oracle, population regularity, intrinsic
condition witness, and `κ^8` parameter transfer are all formalized
separately.

## Verification boundary

The only external mathematical input is deterministic-prefix Haar
disintegration, its independent bits-only stopped-prefix specialization, and
the spherical-cap estimate cited in the paper.  The paper proves the finite
stratum stopped-prefix passage, but the present Lean project does not rebuild
that passage from a formal construction of Stiefel Haar measure.  The combined
input is exposed by
the exact proposition `KappaEightCitedAdaptiveHaarPrinciple`, restricted to
the concrete population problem and Bernoulli SFO constructed here.  It does
not quantify over arbitrary oracles, and its interface explicitly requires
the nondegenerate oracle conditions `0 < Cvar` and `0 ≤ sigma`.  The final
theorem takes a proof of this proposition as an explicit argument.  This
principle is **not proved in
Lean** in this repository; it is also not declared as an axiom or hidden
inside the oracle model.  Conditional on this one premise, Lean checks the
deterministic geometry, the failed/successful prefix interface, population
and oracle certificates, probability bookkeeping, fixed-frame extraction,
intrinsic condition-number transfer, and final minimax consequence.

There is one representation-level difference from the LaTeX notation.  The
paper identifies the lower variable with Euclidean `R^(d+2)`, whereas the
Lean project represents it as `E × (R × R)` with Mathlib's product norm.  The
two norms are uniformly equivalent, with constants depending only on the
three displayed blocks and not on `d`, `kappa`, or `epsilon`.  Therefore this
encoding preserves every claimed complexity order and changes only universal
regularity constants.  It is not a literal isometric identification, so the
formal `conditionData.kappaY` should be read as the norm-equivalent certificate
used by the Lean encoding rather than as the paper's Euclidean spectral ratio
with exactly the same numerical constants.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact boundary
and theorem map.

## Quick verification

From this directory run:

```text
./verify.sh
```

The script directly builds the new population-class, simultaneous-certificate,
final-theorem, and import-smoke-test modules, compiles the detailed
`KappaEightAudit.lean`, runs `KappaEightCompleteAudit.lean` over every theorem
loaded from this standalone project's modules, and scans the sources for
placeholders and custom axiom declarations.  The project pins Lean
`v4.33.0-rc2` and its
Mathlib revision in `lean-toolchain` and `lake-manifest.json`.
