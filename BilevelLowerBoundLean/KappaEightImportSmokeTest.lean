/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightOracle
import BilevelLowerBoundLean.KappaEightPopulationRegularity
import BilevelLowerBoundLean.KappaEightConditionWitness
import BilevelLowerBoundLean.KappaEightPaperClasses
import BilevelLowerBoundLean.KappaEightPaperOracle
import BilevelLowerBoundLean.KappaEightHardOracleInterface

/-!
# Import compatibility smoke test

This deliberately imports the analytic population, condition-number, paper
class, concrete oracle, and one-frontier modules in one environment.  It
guards against accidentally reintroducing duplicate declarations between the
independently developed parts of the amplified formalization.
-/

namespace BilevelLowerBound

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (KappaEightLowerPoint E) = (E × AmplifierAux) := rfl

end BilevelLowerBound
