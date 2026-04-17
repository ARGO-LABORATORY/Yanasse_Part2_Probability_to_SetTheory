import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Reproof of mul_eq_left_iff using ext1-analog reasoning

## Transfer
- **Source schema**: `ext1` (arity 1, no with-clause, no lemma arg) — schema_id 95
- **Source area**: Mathlib.Probability (e.g., measurable_stoppedValue in Stopping.lean)
- **Target area**: Mathlib.SetTheory (Cardinal/Arithmetic.lean)
- **Target theorem**: mul_eq_left_iff
- **Target proof state**: ⊢ a * 1 = a (sub-goal after rintro case split, previously closed by `all_goals simp`)

## Semantic adaptation
In the source, `ext1 ω` reduces set equality `S = T` to pointwise membership `ω ∈ S ↔ ω ∈ T`.
The semantic analog for Cardinals: reduce cardinal equality `#α * #β = #γ` to
constructing an explicit type equivalence `α × β ≃ γ`.

The adaptation uses:
  1. `Cardinal.inductionOn` — reduce from abstract cardinal to concrete type
  2. `Cardinal.mul_def` — express multiplication as product type cardinality
  3. `Cardinal.mk_congr` + `Equiv.prodPUnit` / `Equiv.pemptyProd` — the "extensionality witness"
-/

open Cardinal in
theorem mul_eq_left_iff' {a b : Cardinal} :
    a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_gt ℵ₀ a with ha | ha
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_gt aleph0_pos
      left
      rw [and_assoc]
      use ha
      constructor
      · rw [← not_lt]
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
      · rintro rfl
        apply this
        rw [mul_zero] at h
        exact h.symm
    right
    by_cases h2a : a = 0
    · exact Or.inr h2a
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      exact h.symm
    left
    rw [← h, mul_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    · contradiction
    · contradiction
    rw [← Ne] at h2a
    rw [← Cardinal.one_le_iff_ne_zero] at h2a hb
    norm_cast at h2a hb h ⊢
    apply le_antisymm _ hb
    rw [← not_lt]
    apply fun h2b => ne_of_gt _ h
    conv_rhs => left; rw [← mul_one n]
    rw [Nat.mul_lt_mul_left]
    · exact id
    apply Nat.lt_of_succ_le h2a
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph0_le_left ha hb, max_eq_left hab]
    -- ===== TRANSFERRED TACTIC: ext1-analog (semantic adaptation) =====
    -- Original: all_goals simp
    -- Adapted: reduce cardinal equality to type equivalence via inductionOn + mk_congr
    --
    -- Case b = 1: goal is a * 1 = a
    · induction a using Cardinal.inductionOn with
      | mk α =>
        rw [show (1 : Cardinal) = Cardinal.mk PUnit from (Cardinal.mk_eq_one PUnit).symm]
        rw [Cardinal.mul_def]
        exact Cardinal.mk_congr (Equiv.prodPUnit α)
    -- Case a = 0: goal is 0 * b = 0
    · induction b using Cardinal.inductionOn with
      | mk β =>
        rw [show (0 : Cardinal) = Cardinal.mk PEmpty from (Cardinal.mk_eq_zero PEmpty).symm]
        rw [Cardinal.mul_def]
        exact Cardinal.mk_congr (Equiv.pemptyProd β)
