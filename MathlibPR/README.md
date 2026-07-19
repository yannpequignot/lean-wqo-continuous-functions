# TwoBQO

A self-contained Lean 4 / Mathlib formalization of **2-better-quasi-orders (2-BQO)**, staged as a
candidate Mathlib contribution.

A 2-BQO is a strengthening of well-quasi-order (WQO) phrased via *pair-sequences*
`f : ∀ m n, m < n → α` rather than plain sequences: a relation `r` is 2-BQO if every pair-sequence
has a *good triple* `m < n < l` with `r (f m n) (f n l)`. Unlike WQO, 2-BQO is closed under several
constructions WQO alone is not known to be closed under — most importantly infinite (lexicographic)
sums indexed by a 2-BQO and passage to sequences under a suitable embedding relation.

The theory follows Pequignot, *Better-quasi-order: ideals and spaces*, EMS Surveys 2017.

## Files

The three files build in order; each is `sorry`-free and elaborates against Mathlib `v4.28.0`.

| File | Contents | Suggested Mathlib path |
|------|----------|------------------------|
| [`RamseyInfinite.lean`](RamseyInfinite.lean) | Infinite Ramsey theorem for pairs and triples (`infinite_ramsey_pairs`, `infinite_ramsey_triples`), via an iterated pigeonhole "fan" argument. | `Mathlib/Combinatorics/Ramsey/Infinite.lean` |
| [`WellQuasiOrderRegular.lean`](WellQuasiOrderRegular.lean) | Regular sequences in a WQO (`WellQuasiOrdered.eventuallyRegular`), stabilization of antitone sequences, and Higman's order as a WQO on all of `List Q` (`WellQuasiOrdered.sublistForall₂`). | `Mathlib/Order/WellQuasiOrder/Regular.lean` |
| [`TwoBQO.lean`](TwoBQO.lean) | The 2-BQO theory: `PairSeq`, `TwoBQO`, and the closure/consequence theorems. | `Mathlib/Order/TwoBQO.lean` |

## Main results

- `TwoBQO.wellQuasiOrdered` — 2-BQO implies WQO.
- `TwoBQO.of_finite_coloring` — a preorder with a finite partial-order quotient is 2-BQO.
- `TwoBQO.of_wellFoundedLT`, `Ordinal.isTwoBQO` — well-founded linear orders (and ordinals) are 2-BQO.
- `TwoBQO.comap`, `TwoBQO.mono`, `TwoBQO.union`, `TwoBQO.prod`, `TwoBQO.pi` — closure under monotone
  preimage, relation weakening, covering by two parts, and finite products.
- `TwoBQO.lexSigmaQO` — closure under lexicographic sum along a 2-BQO index.
- `TwoBQO.dom_twoBQO` — the domination order on subsets of a 2-BQO is WQO.
- `TwoBQO.embedForAll_wqo` — the pointwise embedding preorder on `ℕ → Q` is WQO when `r` is 2-BQO.

## Building

The files are not wired into a Lake project; each elaborates directly against a Mathlib olean cache:

```sh
# RamseyInfinite and WellQuasiOrderRegular have no local dependencies:
lake env lean RamseyInfinite.lean -o RamseyInfinite.olean
lake env lean WellQuasiOrderRegular.lean -o WellQuasiOrderRegular.olean

# TwoBQO imports both, so put their oleans on LEAN_PATH:
LEAN_PATH="$(lake env printenv LEAN_PATH):$(pwd)" lake env lean TwoBQO.lean
```

## Status

Staged for a Mathlib contribution; not yet submitted. Naming, target file locations, and namespaces
are provisional and subject to discussion on the Mathlib Zulip.

## License

Released under the Apache 2.0 license, matching Mathlib. Copyright (c) 2026 Yann Pequignot.
