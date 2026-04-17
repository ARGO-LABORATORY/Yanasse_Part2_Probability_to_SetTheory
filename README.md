# Yanasse Part 2: Probability Theory &rarr; Set Theory

New Lean 4 proofs of cardinal and ordinal arithmetic theorems, discovered by transferring tactic invocation patterns from Probability Theory via GPU-accelerated relational analogy matching.

> **Method.** GPU-accelerated NP-hard relational analogy (Deep Vision, running on a MacBook Air via Apple MPS) identifies structurally similar proof states across 217,133 Mathlib-extracted entries; an AI reasoning agent semantically adapts the source tactic pattern to the target theorem. The matching engine is entirely domain-independent.

## Repository contents

| File | Description |
|------|-------------|
| `yanasse_part2.tex` | Paper (LaTeX source) |
| `yanasse_part2.pdf` | Compiled paper |
| `proofs/item_13_ext1_*.lean` | New proof: `ext1` schema &rarr; `Cardinal.inductionOn` + `mk_congr` |
| `proofs/item_15_any_goals_*.lean` | New proof: `any_goals lia` replaces `all_goals simp` |
| `proofs/item_17_by_cases_*.lean` | New proof: top-level `by_cases aleph0 <= a` restructures entire argument |
| `proofs/item_19_push_*.lean` | New proof: `push` normalization &rarr; 3 proof variants for ordinal comparison |

## Results

6 new Lean-verified proofs from 4 successful schema transfers out of 10 attempts (40% schema success rate). Zero `sorry` declarations. The proofs target two theorems:

- **`mul_eq_left_iff`** (Cardinal.Arithmetic): when does cardinal multiplication absorb? `a * b = a` iff `max aleph0 b <= a` and `b != 0`, or `b = 1`, or `a = 0`.
- **`omega0_lt_preOmega_iff`** (Cardinal.Aleph): `omega < preOmega x <-> omega < x`.

| Item | Source schema | Target theorem | Adaptation |
|------|--------------|----------------|------------|
| 13 | `ext1 w` | `mul_eq_left_iff` | Pointwise set extensionality &rarr; reduce cardinal equality to type equivalence via `inductionOn + mk_congr + Equiv.prodPUnit` |
| 15 | `any_goals lia` | `mul_eq_left_iff` | `lia`'s normalization closes both residual goals (`a*1=a` and `0*b=0`) where `simp` was used |
| 17 | `by_cases hk : IsSFiniteKernel k` | `mul_eq_left_iff` | Structural niceness predicate `IsSFiniteKernel` maps to `aleph0 <= a`; entire proof restructured around this split |
| 19 | `push _ in _` | `omega0_lt_preOmega_iff` | Set-membership normalization &rarr; ordinal-embedding normalization; 3 variant proofs (constructor+rwa, nth_rw, calc chain) |

## Key findings

1. **Proof-architecture transfer.** The deepest transfer is item 17: the probability pattern "case-split on a structural niceness predicate" (`IsSFiniteKernel kappa`) maps to "case-split on whether a cardinal is infinite" (`aleph0 <= a`). The two predicates share no identifiers, types, or namespaces; the connection is purely semantic.

2. **Cross-pair stability.** The same three schemas that transferred to Representation Theory (Part 1) &mdash; `ext1`, `any_goals`, `by_cases` &mdash; also transfer to Set Theory. The same three that failed in Part 1 &mdash; `lift`, `measurability`, `congrm` &mdash; fail here too. This suggests a stable partition into transferable vs. domain-locked schemas.

3. **Multiple proof variants.** Item 19 produces 3 distinct valid proofs from a single schema transfer, demonstrating that semantic adaptation is generative, not template-filling.

## Building

Requires Lean 4 (v4.29.0+) and Mathlib (v4.29.0+). Each proof file is self-contained:

```lean
import Mathlib
```

## Citation

```bibtex
@article{linhares2026yanasse2,
  title   = {Yanasse: Finding New Proofs from Deep Vision's Analogies --- Part~2:
             Probability Theory to Set Theory},
  author  = {Linhares, Alexandre},
  year    = {2026},
  month   = {April},
  publication = {Argolab.org Report for Dissemination}
}
```

## Authors

- **Alexandre Linhares** (alexandre@linhares.ltd)

## License

MIT. See [LICENSE](LICENSE).
