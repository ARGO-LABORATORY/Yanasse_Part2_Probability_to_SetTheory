/-
  Reproof of Cardinal.mul_eq_left_iff using a top-level `by_cases` on ℵ₀ ≤ a,
  semantically adapted from the Probability kernel proof pattern:
    `by_cases hκ : IsSFiniteKernel κ`
  which splits on a structural "niceness" predicate first.

  Source: Mathlib.Probability.Kernel.Composition.MeasureComp (comp_compProd_comm)
  Schema: by_cases (arity 4, no with, no lemma)
  Target: Mathlib.SetTheory.Cardinal.Arithmetic (mul_eq_left_iff)

  Semantic analogy: IsSFiniteKernel κ ↔ ℵ₀ ≤ a
    Both are structural "niceness" predicates. S-finite kernels support
    composition-product theory; infinite cardinals support max-absorption
    arithmetic. The negative case degenerates: for kernels, compProd
    collapses via simp; for cardinals, we fall to finite/ℕ arithmetic.
-/
import Mathlib.SetTheory.Cardinal.Arithmetic

open Cardinal

theorem mul_eq_left_iff_reproof {a b : Cardinal} :
    a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  -- TOP-LEVEL by_cases: structural "niceness" split, mirroring
  -- the source's `by_cases hκ : IsSFiniteKernel κ`
  by_cases ha : ℵ₀ ≤ a
  · -- INFINITE CASE (the "nice" regime): multiplication = max
    rw [show max ℵ₀ b ≤ a ↔ ℵ₀ ≤ a ∧ b ≤ a from max_le_iff]
    constructor
    · -- Forward: a * b = a → first disjunct
      intro h
      have ha0 : a ≠ 0 := ne_of_gt (aleph0_pos.trans_le ha)
      have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact ha0 h.symm
      left
      refine ⟨⟨ha, ?_⟩, hb0⟩
      -- From mul_eq_max_of_aleph0_le_left: a * b = max a b
      -- Combined with a * b = a: max a b = a, so b ≤ a
      have h1 := mul_eq_max_of_aleph0_le_left ha hb0
      rw [h] at h1  -- h1 : a = max a b
      exact (max_le_iff.mp (le_of_eq h1.symm)).2
    · -- Backward: three disjuncts
      rintro (⟨⟨_, hab⟩, hb⟩ | rfl | rfl)
      · exact mul_eq_left ha hab hb
      · simp
      · simp
  · -- FINITE CASE (the "degenerate" regime): reduces to ℕ arithmetic
    -- The first disjunct requires ℵ₀ ≤ a, which contradicts our case.
    push Not at ha  -- ha : a < ℵ₀
    constructor
    · -- Forward: a * b = a with a finite
      intro h
      -- First disjunct is impossible (needs ℵ₀ ≤ a)
      right
      by_cases h2a : a = 0
      · exact Or.inr h2a
      · left  -- show b = 1
        -- b must also be finite: otherwise a * b ≥ b ≥ ℵ₀ > a
        have hb : b < ℵ₀ := by
          by_contra hb'
          push Not at hb'
          have := mul_eq_max_of_aleph0_le_right h2a hb'
          rw [h, max_eq_right (ha.trans_le hb').le] at this
          exact ne_of_lt (ha.trans_le hb') this
        -- Cast to natural numbers and use Nat.mul_eq_left
        rw [lt_aleph0] at ha hb
        obtain ⟨n, rfl⟩ := ha
        obtain ⟨m, rfl⟩ := hb
        have hn : n ≠ 0 := by exact_mod_cast h2a
        norm_cast at h ⊢
        exact (Nat.mul_eq_left hn).mp h
    · -- Backward: first disjunct impossible, others trivial
      rintro (⟨h1, _⟩ | rfl | rfl)
      · exact absurd (le_of_max_le_left h1) (not_le.mpr ha)
      · simp
      · simp
