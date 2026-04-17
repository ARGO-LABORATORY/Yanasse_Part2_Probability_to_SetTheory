/-
  Yanasse B_reprove: item_id=19, schema=push/3
  Source: Mathlib.Probability (push _ ∈ _ — normalizing set membership)
  Target: Mathlib.SetTheory (omega0_lt_preOmega_iff)

  Semantic adaptation of "push" normalization:
  The source `push _ ∈ _` normalizes by pushing set membership through
  set-builder/union/preimage to expose underlying propositions.
  The structural analog: normalize by "pushing" `preOmega` through ordinal
  comparisons using the order embedding's monotonicity, analogous to
  how `push _ ∈ _` pushes ∈ through set-builder notation.

  Original proof:
    conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]
-/
import Mathlib.SetTheory.Cardinal.Aleph

open Ordinal

-- ═══════════════════════════════════════════════════════════════
-- PROOF 1: constructor + rwa
-- Mirrors push's pattern of normalizing each direction separately.
-- The rwa chain [← preOmega_omega0, preOmega_lt_preOmega] is
-- the ordinal analog of push's [Set.mem_setOf_eq, Set.mem_preimage].
-- ═══════════════════════════════════════════════════════════════
theorem omega0_lt_preOmega_iff_v1 {x : Ordinal} :
    ω < preOmega x ↔ ω < x := by
  constructor
  · intro h
    rwa [← preOmega_omega0, preOmega_lt_preOmega] at h
  · intro h
    rwa [← preOmega_omega0, preOmega_lt_preOmega]

-- ═══════════════════════════════════════════════════════════════
-- PROOF 2: nth_rw for targeted normalization
-- Replace only the first ω with preOmega ω (targeted push),
-- then close with the embedding's lt_iff_lt.
-- ═══════════════════════════════════════════════════════════════
theorem omega0_lt_preOmega_iff_v2 {x : Ordinal} :
    ω < preOmega x ↔ ω < x := by
  nth_rw 1 [show (ω : Ordinal) = preOmega ω from preOmega_omega0.symm]
  exact preOmega_lt_preOmega

-- ═══════════════════════════════════════════════════════════════
-- PROOF 3: calc chain showing the "push-through" steps explicitly
-- Step 1: Introduce preOmega wrapper on ω (inverse of normalization)
-- Step 2: Cancel paired preOmega via monotonicity (the actual push)
-- ═══════════════════════════════════════════════════════════════
theorem omega0_lt_preOmega_iff_v3 {x : Ordinal} :
    ω < preOmega x ↔ ω < x := by
  calc ω < preOmega x
      ↔ preOmega ω < preOmega x := by rw [preOmega_omega0]
    _ ↔ ω < x := preOmega_lt_preOmega
