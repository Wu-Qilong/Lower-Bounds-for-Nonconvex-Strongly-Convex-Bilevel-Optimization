/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import BilevelLowerBoundLean.KappaEightPaperClasses

/-!
# Exact recursive interaction for the amplified SFO model

The recursion below uses the new query type `E × (E × (R × R))`.  Thus the
output appearing in the final lower bound is definitionally the output of the
algorithm after the stated sequence of oracle calls, not an unrelated random
point.
-/

namespace BilevelLowerBound

noncomputable section

def kappaEightRunTranscript
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) : ℕ → KappaEightOriginalTranscript E
  | 0 => []
  | t + 1 =>
      if ht : t < N then
        let i : Fin N := ⟨t, ht⟩
        let previous := kappaEightRunTranscript A O seed bits t
        let query := A.query i seed previous
        previous ++ [(query, O.response (bits i) query)]
      else
        kappaEightRunTranscript A O seed bits t

@[simp]
theorem kappaEightRunTranscript_zero
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) :
    kappaEightRunTranscript A O seed bits 0 = [] := rfl

theorem kappaEightRunTranscript_succ
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) {t : ℕ} (ht : t < N) :
    kappaEightRunTranscript A O seed bits (t + 1) =
      let i : Fin N := ⟨t, ht⟩
      let previous := kappaEightRunTranscript A O seed bits t
      let query := A.query i seed previous
      previous ++ [(query, O.response (bits i) query)] := by
  rw [kappaEightRunTranscript]
  simp only [dif_pos ht]

theorem length_kappaEightRunTranscript
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) :
    ∀ t ≤ N, (kappaEightRunTranscript A O seed bits t).length = t := by
  intro t htN
  induction t with
  | zero => simp
  | succ t iht =>
      have ht : t < N := by omega
      rw [kappaEightRunTranscript_succ A O seed bits ht]
      simp [iht (by omega)]

def kappaEightRunQuery
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) (t : Fin N) :
    KappaEightQueryPoint E :=
  A.query t seed (kappaEightRunTranscript A O seed bits t.val)

def kappaEightRunOutput
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) : E :=
  A.output seed (kappaEightRunTranscript A O seed bits N)

@[instance_reducible]
def kappaEightRunPastMeasurableSpace
    {E Seed Omega : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {mSeed : MeasurableSpace Seed}
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : @KappaEightAdaptiveAlgorithm N E Seed _ _ _ mSeed)
    (O : KappaEightBernoulliSFO P)
    (seed : Omega → Seed) (bits : Omega → Fin N → Bool)
    (t : Fin N) : MeasurableSpace Omega :=
  MeasurableSpace.comap
    (fun omega ↦
      (seed omega,
        kappaEightRunTranscript A O (seed omega) (bits omega) t.val))
    (explicitProductMeasurableSpace mSeed A.transcriptMeasurableSpace)

def kappaEightRunSuccessEvent
    {Omega : Type*} {N : ℕ}
    (bits : Omega → Fin N → Bool) (t : Fin N) : Set Omega :=
  {omega | bits omega t = true}

@[instance_reducible]
def kappaEightJointRunPastMeasurableSpace
    {E Seed Omega Frame : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {mSeed : MeasurableSpace Seed}
    (mFrame : MeasurableSpace Frame)
    {N : ℕ} (P : Frame → KappaEightPopulationProblem E)
    (A : @KappaEightAdaptiveAlgorithm N E Seed _ _ _ mSeed)
    (O : ∀ U, KappaEightBernoulliSFO (P U))
    (seed : Omega → Seed) (bits : Omega → Fin N → Bool)
    (t : Fin N) : MeasurableSpace (Frame × Omega) :=
  MeasurableSpace.comap
    (fun z ↦
      (z.1,
        (seed z.2,
          kappaEightRunTranscript A (O z.1) (seed z.2)
            (bits z.2) t.val)))
    (explicitProductMeasurableSpace mFrame
      (explicitProductMeasurableSpace mSeed
        A.transcriptMeasurableSpace))

theorem get_kappaEightRunTranscript_succ_last
    {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Seed]
    {N : ℕ} {P : KappaEightPopulationProblem E}
    (A : KappaEightAdaptiveAlgorithm N E Seed)
    (O : KappaEightBernoulliSFO P)
    (seed : Seed) (bits : Fin N → Bool) (t : Fin N) :
    (kappaEightRunTranscript A O seed bits (t.val + 1)).getLast? =
      some (kappaEightRunQuery A O seed bits t,
        O.response (bits t) (kappaEightRunQuery A O seed bits t)) := by
  rw [kappaEightRunTranscript_succ A O seed bits t.isLt]
  simp [kappaEightRunQuery]

end

end BilevelLowerBound
