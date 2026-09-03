# Verification snapshot: independent kappa-eight project

- Snapshot date: 2026-08-23.
- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`.
- Mathlib revision: `v4.33.0-rc2`.
- `lake build`: passed.
- `BilevelLowerBoundLean/KappaEightAudit.lean`: passed.
- `BilevelLowerBoundLean/KappaEightCompleteAudit.lean`: passed; it checked
  all 1557 theorem declarations loaded from this standalone project's
  modules.
- `./verify.sh`: passed, including the population-class, simultaneous
  certificate, final-theorem, and combined-import targets.
- Placeholder scan for `sorry`, `admit`, and custom `axiom`: clear.

The audit reports standard Lean/Mathlib logical axioms such as `propext`,
`Classical.choice`, and `Quot.sound`.  These are not placeholder proofs.
The sole cited adaptive-Haar input—deterministic-prefix Haar disintegration,
its independent bits-only stopped-prefix specialization, and the spherical-cap
estimate—is represented by the explicit proposition
`KappaEightCitedAdaptiveHaarPrinciple`, restricted definitionally to the
concrete hard population problem and SFO and guarded by `0 < Cvar` and
`0 ≤ sigma`.  It is a premise of the final theorem, not a custom Lean axiom.
See `PROJECT_GUIDE.md` and
`FORMALIZATION_STATUS.md` for the exact boundary.

The checked fixed-frame failure certificate uses the strict margins
`E||grad|| > 3 epsilon/2` and `E||grad||^2 > 9 epsilon^2/4`.
