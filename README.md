# Lean verification of the $\kappa_y^8 \epsilon^{-6}$ stochastic bilevel lower bound

This is a standalone Lean 4 + Mathlib project for the two-coordinate hard instance used to prove the stochastic nonconvex--strongly-convex bilevel lower bound

$$
\Omega\Bigl( \frac{\Delta \kappa_y^2}{\epsilon^2} \max\Bigl(1, \frac{\sigma^2 \kappa_y^6}{\epsilon^4}\Bigr) \Bigr).
$$

In the noise-dominated regime,

$$
\frac{\sigma^2 \kappa_y^6}{\epsilon^4} \ge 1,
$$

the lower bound becomes

$$
\Omega( \Delta \sigma^2 \kappa_y^8 \epsilon^{-6} ).
$$

The `KappaEight*.lean` modules define the hard pair and its stochastic oracle, establish the population and regularity properties, verify the parameter choices, and derive the final complexity statement.

## Hard-instance construction

The lower auxiliary variable is two-dimensional:

$$
v=(v_1,v_2) \in \mathbb{R}^2.
$$

Its quadratic block has eigenvalues

$$
\frac{1}{\kappa}
$$

and

$$
1.
$$

Before the stochastic frontier term enters the lower objective, it is divided by the off-diagonal entry $s_\kappa$ of the inverse quadratic block. Solving the lower problem multiplies this term by $s_\kappa$ in the $v_2$ coordinate, and the upper objective depends linearly on that coordinate. Thus, after the exact lower solution is substituted, the original unscaled frontier term is recovered.

The construction has two key properties.

First, after substitution of the exact lower solution, the population hyper-objective is exactly the zero-chain objective used in the progress argument.

Second, the randomized lower-gradient contribution satisfies

$$
\|G\| = O\Bigl( \frac{\eta^2}{\kappa} \Bigr).
$$

When $\sigma=0$, set

$$
p=1.
$$

When $\sigma>0$, choose

$$
p=\min\Bigl(1, \frac{C_v\eta^4}{\sigma^2\kappa^2}\Bigr).
$$

For every $\sigma\ge 0$, this gives

$$
\frac{1}{p}=\max\Bigl(1, \frac{\sigma^2\kappa^2}{C_v\eta^4}\Bigr).
$$

The stationarity and chain-length parameters are

$$
\eta=\frac{4\epsilon}{\kappa}
$$

and

$$
T=\Theta\Bigl( \frac{\Delta\kappa^2}{\epsilon^2} \Bigr).
$$

Substituting the choice of $\eta$ into the Bernoulli probability gives

$$
\frac{1}{p}=\max\Bigl(1, \frac{\sigma^2\kappa^6}{256C_v\epsilon^4}\Bigr).
$$

The one-frontier progress argument therefore gives the call scale

$$
\Theta\Bigl( \frac{T}{p} \Bigr) = \Theta\Bigl( \frac{\Delta\kappa^2}{\epsilon^2} \max\Bigl(1, \frac{\sigma^2\kappa^6}{\epsilon^4}\Bigr) \Bigr),
$$

up to universal numerical constants. In the noise-dominated regime, the stochastic term is

$$
\Theta\Bigl( \frac{\Delta\sigma^2\kappa^8}{\epsilon^6} \Bigr).
$$

## Analytic guarantees checked in Lean

Subject to the adaptive-Haar premise described under **Verification boundary**, the modules verify the following claims without `sorry`, `admit`, or custom axiom declarations:

- the spectrum of the two-coordinate quadratic block, the relevant entries of its inverse, global nonnegativity of the compensated block, and uniqueness of its zero;
- the exact global lower minimizer and the exact population hyper-objective identity;
- attenuation of the first three derivatives and the mixed derivative bounds displayed below;
- lower strong convexity, full-Hessian bounds, and global full-Hessian Lipschitzness, including the full-Hessian Lipschitz property used in the paper's first-order-smooth setting;
- unbiased Bernoulli importance weighting, variance at most $\sigma^2$, and the formula for the Bernoulli probability;
- a one-frontier interface for the complete upper/lower oracle response: when the Bernoulli variable is zero, the response is a function of the exposed prefix, while a value of one may expose the next frontier first jet;
- dimension-free Hessian and gradient-Lipschitz bounds for the upper objective, together with its derivative bounds in the lower variable;
- membership of the hard pair in a population class carrying the required upper- and lower-level smoothness, lower strong convexity, full-Hessian Lipschitzness, upper-objective lower-variable derivative, and initial-gap certificates;
- simultaneous population-class, fresh-sample SFO, and intrinsic condition-number certificates for the same hidden frame;
- the parameter choices and the resulting $\kappa^8\epsilon^{-6}$ call scale;
- the intrinsic condition-number comparison, including existence of the sharp lower-Hessian modulus and the Hessian upper bound used to define $\kappa_y$;
- the minimax quantifier order and the final lower-bound consequence, conditional on the explicitly stated adaptive-Haar principle.

The mixed derivative bounds are

$$
\|DR\|=O\Bigl( \frac{\eta^2}{\kappa} \Bigr),
$$

$$
\|D^2R\|=O\Bigl( \frac{\eta}{\kappa} \Bigr),
$$

and

$$
\|D^3R\|=O\Bigl( \frac{1}{\kappa} \Bigr).
$$

The intrinsic condition number satisfies

$$
\kappa \le \kappa_y \le 14\kappa.
$$

## Main formal theorem

The construction-scale theorem is `concrete_kappaEight_paper_main_theorem` in `KappaEightPaperFinalTheorem.lean`.

It constructs a finite ambient dimension and proves that, for every adaptive randomized algorithm below the stated call budget, there are a population problem and an admissible fresh-sample SFO for which the output $\widehat{x}$ satisfies

$$
\mathbb{E}\|\nabla\Phi(\widehat{x})\| > \frac{3\epsilon}{2}
$$

and

$$
\mathbb{E}\|\nabla\Phi(\widehat{x})\|^2 > \frac{9\epsilon^2}{4}.
$$

These inequalities follow from an event with probability at least

$$
\frac{3}{4},
$$

on which

$$
\|\nabla\Phi(\widehat{x})\| > 2\epsilon.
$$

The construction-scale call bound is

$$
\max\Bigl(\frac{\Delta\kappa^2}{\epsilon^2}, \frac{\Delta\sigma^2\kappa^8}{\epsilon^6}\Bigr).
$$

## Strong-convexity and condition-number notation

The class parameter `muG` is the certified strong-convexity modulus of the lower objective $g$. The quantity `muGAct` is its sharp lower-Hessian modulus:

$$
\mu_g^{act}=\inf_{x,y}\lambda_{\min}(\nabla_{yy}^2g(x,y)).
$$

The intrinsic condition number is

$$
\kappa_y=\frac{L_y}{\mu_g^{act}}.
$$

`KappaEightPopulationClassMember.muG_le_muGAct` proves the Definition 3.2 compatibility inequality

$$
\mu_g \le \mu_g^{act}.
$$

The formalized instance satisfies

$$
\kappa \le \kappa_y \le 14\kappa.
$$

Consequently,

$$
\kappa_y^8 \le 14^8\kappa^8
$$

and

$$
\kappa^8 \ge 14^{-8}\kappa_y^8.
$$

Replacing the construction parameter $\kappa$ by the actual condition number $\kappa_y$ therefore changes the lower bound by at most the universal factor $14^8$ and preserves the stochastic order

$$
\Omega( \Delta\sigma^2\kappa_y^8\epsilon^{-6} ).
$$

## Formalization structure

The project contains separate modules for the smooth zero-chain, frontier extractor, soft projection, two-coordinate compensated block, hard bilevel pair, fresh-sample conditional expectation, population regularity, one-frontier process, finite-event probability estimates, gap-gradient argument, intrinsic condition-number transfer, fixed-frame extraction, and final theorem assembly.

This organization separates the analytic properties of the hard instance from the probabilistic random-rotation argument.

## Verification boundary

The external mathematical input consists of deterministic-prefix Haar disintegration, its independent bits-only stopped-prefix specialization, and the spherical-cap estimate cited in the paper. The paper proves the finite-stratum stopped-prefix passage, but this Lean project does not construct Stiefel Haar measure and reprove that passage from first principles.

The required input is stated as `KappaEightCitedAdaptiveHaarPrinciple`. It is restricted to the concrete population problem and Bernoulli SFO formalized in this project. Its interface includes

$$
C_v>0
$$

and

$$
\sigma\ge 0.
$$

The final theorem takes a proof of this proposition as an explicit argument. The principle is not proved in Lean here, but it is neither declared as an axiom nor hidden in the oracle model.

Conditional on this premise, Lean checks the deterministic geometry, the prefix interface for the two Bernoulli outcomes, the population and oracle certificates, the probability bookkeeping, fixed-frame extraction, intrinsic condition-number transfer, and the final minimax consequence.

## Representation of the lower variable

The paper identifies the lower variable with the Euclidean space

$$
\mathbb{R}^{d+2}.
$$

The Lean project represents it as

$$
E \times (\mathbb{R} \times \mathbb{R})
$$

with Mathlib's product norm. These norms are uniformly equivalent, with equivalence constants depending only on the three displayed blocks and not on $d$, $\kappa$, or $\epsilon$. This representation therefore preserves all complexity orders and changes only universal regularity constants.

It is not a literal isometric identification. Accordingly, `conditionData.kappaY` is the norm-equivalent condition certificate used by the Lean encoding rather than the paper's Euclidean spectral ratio with exactly the same numerical constants.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the theorem map and the precise formalization boundary.

## Quick verification

From the project directory, run

```bash
./verify.sh
```

The script builds the population-class, simultaneous-certificate, final-theorem, import-smoke-test, `KappaEightAudit.lean`, and `KappaEightCompleteAudit.lean` modules. It also scans the source files for placeholders and custom axiom declarations.

The project pins Lean `v4.33.0-rc2` and the corresponding Mathlib revision in `lean-toolchain` and `lake-manifest.json`.
