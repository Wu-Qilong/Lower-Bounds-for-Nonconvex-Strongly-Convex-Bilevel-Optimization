/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.MainTheorem

/-!
# Final worst-case quantifier packaging

The analytic files construct and certify a hard population pair and a
fresh-sample oracle for each fixed algorithm.  `MainTheorem.lean` proves the
corresponding stationarity failure.  This file records the outer logical
layer explicitly, so the final statement has the paper's quantifier order

`exists d, for all A, exists (f,g), exists O`.

The types of admissible algorithms, population problems, and oracles are
left abstract here.  Their concrete predicates are supplied by the paper's
algorithm-class, population-class, and fresh-SFO definitions.  In particular,
the two membership proofs are fields of `CertifiedHardInstance`; they cannot
be dropped when the outer quantifiers are assembled.
-/

open Set

namespace BilevelLowerBound

/-- One certified hard instance against one fixed algorithm.  The fields
`population_mem` and `oracle_mem` are the formal counterparts of
`(f,g) ∈ F` and `O ∈ O_sigma^SFO(f,g)`. -/
structure CertifiedHardInstance
    {Algorithm : ℕ → Type*}
    {Problem : ℕ → Type*}
    {Oracle : (d : ℕ) → Problem d → Type*}
    (populationClass : (d : ℕ) → Set (Problem d))
    (oracleClass : (d : ℕ) → (P : Problem d) → Set (Oracle d P))
    (failure : (d : ℕ) → Algorithm d →
      (P : Problem d) → Oracle d P → Prop)
    {d : ℕ} (A : Algorithm d) where
  problem : Problem d
  oracle : Oracle d problem
  population_mem : problem ∈ populationClass d
  oracle_mem : oracle ∈ oracleClass d problem
  stationarity_failure : failure d A problem oracle

/-- The fully quantified worst-case lower-bound statement.  Taking
`Algorithm d` itself to be the class of admissible randomized adaptive
first-order algorithms avoids an extra membership guard after `A`. -/
def FullyQuantifiedLowerBound
    (Algorithm : ℕ → Type*)
    (Problem : ℕ → Type*)
    (Oracle : (d : ℕ) → Problem d → Type*)
    (populationClass : (d : ℕ) → Set (Problem d))
    (oracleClass : (d : ℕ) → (P : Problem d) → Set (Oracle d P))
    (failure : (d : ℕ) → Algorithm d →
      (P : Problem d) → Oracle d P → Prop) : Prop :=
  ∃ d : ℕ, ∀ A : Algorithm d,
    ∃ P : Problem d, P ∈ populationClass d ∧
      ∃ O : Oracle d P,
        O ∈ oracleClass d P ∧ failure d A P O

/-- Assemble the paper's final quantifier order from the per-algorithm
certificates.  Unlike a statement which only returns a hard frame, this
conclusion explicitly retains both class-membership obligations. -/
theorem fullyQuantifiedLowerBound_of_certified_realizer
    {Algorithm : ℕ → Type*}
    {Problem : ℕ → Type*}
    {Oracle : (d : ℕ) → Problem d → Type*}
    {populationClass : (d : ℕ) → Set (Problem d)}
    {oracleClass : (d : ℕ) → (P : Problem d) → Set (Oracle d P)}
    {failure : (d : ℕ) → Algorithm d →
      (P : Problem d) → Oracle d P → Prop}
    (d : ℕ)
    (realize : ∀ A : Algorithm d,
      CertifiedHardInstance populationClass oracleClass failure A) :
    FullyQuantifiedLowerBound Algorithm Problem Oracle
      populationClass oracleClass failure := by
  refine ⟨d, ?_⟩
  intro A
  let certificate := realize A
  exact ⟨certificate.problem, certificate.population_mem,
    certificate.oracle, certificate.oracle_mem,
    certificate.stationarity_failure⟩

/-- Version in which the ambient dimension is itself supplied existentially,
as it is by `final_parameter_dimension_certificate`.  The realization map may
use the dimension certificate to construct the Haar frame law and the hard
interaction for each algorithm. -/
theorem fullyQuantifiedLowerBound_of_dimension_certificate
    {Algorithm : ℕ → Type*}
    {Problem : ℕ → Type*}
    {Oracle : (d : ℕ) → Problem d → Type*}
    {populationClass : (d : ℕ) → Set (Problem d)}
    {oracleClass : (d : ℕ) → (P : Problem d) → Set (Oracle d P)}
    {failure : (d : ℕ) → Algorithm d →
      (P : Problem d) → Oracle d P → Prop}
    {DimensionCertificate : ℕ → Prop}
    (hdimension : ∃ d, DimensionCertificate d)
    (realize : ∀ d, DimensionCertificate d → ∀ A : Algorithm d,
      CertifiedHardInstance populationClass oracleClass failure A) :
    FullyQuantifiedLowerBound Algorithm Problem Oracle
      populationClass oracleClass failure := by
  obtain ⟨d, hd⟩ := hdimension
  exact fullyQuantifiedLowerBound_of_certified_realizer d
    (realize d hd)

/-- Constructor used after applying `main_lower_bound_assembly` and the
separately checked population/oracle certificates to one algorithm. -/
def certifiedHardInstance_mk
    {Algorithm : ℕ → Type*}
    {Problem : ℕ → Type*}
    {Oracle : (d : ℕ) → Problem d → Type*}
    {populationClass : (d : ℕ) → Set (Problem d)}
    {oracleClass : (d : ℕ) → (P : Problem d) → Set (Oracle d P)}
    {failure : (d : ℕ) → Algorithm d →
      (P : Problem d) → Oracle d P → Prop}
    {d : ℕ} {A : Algorithm d} {P : Problem d} {O : Oracle d P}
    (hpopulation : P ∈ populationClass d)
    (horacle : O ∈ oracleClass d P)
    (hfailure : failure d A P O) :
    CertifiedHardInstance populationClass oracleClass failure A :=
  ⟨P, O, hpopulation, horacle, hfailure⟩

end BilevelLowerBound
