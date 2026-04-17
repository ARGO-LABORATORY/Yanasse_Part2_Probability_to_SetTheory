/-
  Yanasse item 15, B_reprove
  Schema 320: any_goals (arity 1)
  Source: MB_PRO_10037 — `any_goals lia` in Mathlib.Probability.Kernel.IonescuTulcea.Traj
  Target: MB_STH_2134 — mul_eq_left_iff in Mathlib.SetTheory.Cardinal.Arithmetic

  Transfer: `any_goals lia` (the literal source tactic) replaces `all_goals simp`
  at the cleanup step of mul_eq_left_iff's backward direction.
  Status: CLOSED — full theorem compiles.
-/
import Mathlib.SetTheory.Cardinal.Arithmetic

open Cardinal

-- Full proof of mul_eq_left_iff with the transferred tactic pattern
theorem mul_eq_left_iff_reproof {a b : Cardinal} :
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
    /-
      TRANSFERRED TACTIC: any_goals lia
      Source: Mathlib.Probability.Kernel.IonescuTulcea.Traj (trajContent_tendsto_zero)
      Original at this position: all_goals simp

      After `rintro (... | rfl | rfl)`, two goals remain:
        1. ⊢ a * 1 = a   (from b = 1 substitution)
        2. ⊢ 0 * b = 0   (from a = 0 substitution)
      `any_goals lia` closes both via lia's internal normalization.
    -/
    any_goals lia
