/-
Copyright (c) 2026 Zhihao Gu, Qilong Wu, and Junchi Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Gu, Qilong Wu, Junchi Yang
-/
import Mathlib

/-!
# Original and augmented transcripts

This file isolates the type-level point used by the coupled-transcript proof:
the augmented transcript contains gifted samples and exposed frame columns,
but the original algorithm is extended by projection onto its original
transcript.  Therefore the added information does not alter its queries or
output.
-/

namespace BilevelLowerBound

/-- An augmented transcript packages the actual transcript with proof-only data. -/
structure AugmentedTranscript (Original Sample Column : Type*) where
  original : Original
  samples : List Sample
  exposedPrefix : List Column

/-- Canonical projection onto the transcript actually seen by the algorithm. -/
def originalProjection {Original Sample Column : Type*} :
    AugmentedTranscript Original Sample Column → Original :=
  fun transcript ↦ transcript.original

/-- Extend an original query rule to augmented transcripts by projection. -/
def extendQuery {Seed Original Sample Column Query : Type*}
    (query : Seed → Original → Query) :
    Seed → AugmentedTranscript Original Sample Column → Query :=
  fun seed transcript ↦ query seed (originalProjection transcript)

/-- Extend an original output rule to augmented transcripts by projection. -/
def extendOutput {Seed Original Sample Column Output : Type*}
    (output : Seed → Original → Output) :
    Seed → AugmentedTranscript Original Sample Column → Output :=
  fun seed transcript ↦ output seed (originalProjection transcript)

@[simp]
theorem originalProjection_mk {Original Sample Column : Type*}
    (original : Original) (samples : List Sample) (columns : List Column) :
    originalProjection
      (AugmentedTranscript.mk original samples columns) = original := rfl

@[simp]
theorem extendQuery_apply {Seed Original Sample Column Query : Type*}
    (query : Seed → Original → Query) (seed : Seed)
    (transcript : AugmentedTranscript Original Sample Column) :
    extendQuery query seed transcript = query seed transcript.original := rfl

@[simp]
theorem extendOutput_apply {Seed Original Sample Column Output : Type*}
    (output : Seed → Original → Output) (seed : Seed)
    (transcript : AugmentedTranscript Original Sample Column) :
    extendOutput output seed transcript = output seed transcript.original := rfl

/-- Gifted information cannot change the lifted query when originals agree. -/
theorem extendQuery_ignores_gifted_information
    {Seed Original Sample Column Query : Type*}
    (query : Seed → Original → Query) (seed : Seed)
    (left right : AugmentedTranscript Original Sample Column)
    (hOriginal : left.original = right.original) :
    extendQuery query seed left = extendQuery query seed right := by
  change query seed left.original = query seed right.original
  rw [hOriginal]

/-- Gifted information cannot change the lifted output when originals agree. -/
theorem extendOutput_ignores_gifted_information
    {Seed Original Sample Column Output : Type*}
    (output : Seed → Original → Output) (seed : Seed)
    (left right : AugmentedTranscript Original Sample Column)
    (hOriginal : left.original = right.original) :
    extendOutput output seed left = extendOutput output seed right := by
  change output seed left.original = output seed right.original
  rw [hOriginal]

end BilevelLowerBound
