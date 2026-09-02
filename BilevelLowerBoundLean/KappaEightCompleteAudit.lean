/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean
import Mathlib.Util.AssertNoSorry

/-!
# Complete theorem audit for the independent kappa-eight modules

`KappaEightAudit.lean` records detailed dependencies for the paper-facing
declarations.  This complementary audit mechanically visits every theorem
defined by any loaded module of this standalone project and rejects any
transitive dependency on `sorryAx`, including the generic infrastructure and
all analytic and algebraic helper lemmas.
-/

open Lean Meta Elab Command

/-- Check every theorem defined in a module whose name begins with the supplied prefix. -/
elab "#assert_module_prefix_no_sorry " modulePrefixSyntax:str : command => do
  let env ← getEnv
  let modulePrefix := modulePrefixSyntax.getString
  let mut checked : Nat := 0
  for (declName, info) in env.constants.toList do
    if info.isTheorem then
      if let some moduleIdx := env.getModuleIdxFor? declName then
        let moduleName := env.header.moduleNames[moduleIdx.toNat]!
        if moduleName.toString.startsWith modulePrefix then
          let axioms ← liftCoreM <| Lean.collectAxioms declName
          if axioms.contains ``sorryAx then
            throwError "{declName} contains sorryAx"
          checked := checked + 1
  logInfo m!"Complete audit checked {checked} theorem declarations in {modulePrefix}*"

#assert_module_prefix_no_sorry "BilevelLowerBoundLean."
