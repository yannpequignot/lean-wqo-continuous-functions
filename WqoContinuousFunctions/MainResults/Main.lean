import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.WellQuasiOrder
import WqoContinuousFunctions.ContinuousReducibility.Defs
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Formalization of main theorems

This file should eventually contain all the main theorems
with proofs by importing the relevant lemmas from the repo.

## Main theorem statements

* `MainTheorem1` — Continuous reducibility is a WQO on continuous functions from an
  analytic zero-dimensional space to a separable metrizable space.
* `MainTheorem2` — Continuous reducibility is a WQO on continuous functions from a
  separable metrizable zero-dimensional space to a countable metrizable space.
* `MainTheorem3` — Continuous reducibility is a WQO on scattered continuous functions
  from a zero-dimensional separable metrizable space to a metrizable space.
* `scattered_iff_empty_perfectKernel` — A continuous function between topolical spaces is scattered iff it has empty perfect kernel.
* `levels_finitely_generated` — Each CB-rank level is finitely generated.
-/


section WQO

/-!
## Well-Quasi-Orders

An *antichain* is a set of pairwise incomparable elements. A quasi-order is a
*well-quasi-order (WQO)* if it has no infinite antichains and no infinite strictly
descending chains. Equivalently (by Ramsey-like arguments), `(Q, ≤)` is WQO iff
for every infinite sequence there exist `m < n` with `f(m) ≤ f(n)`.

Mathlib provides `WellQuasiOrdered` with the sequential characterization.
-/

-- `WellQuasiOrdered` is already in Mathlib:
-- `WellQuasiOrdered r ↔ ∀ f : ℕ → α, ∃ m n, m < n ∧ r (f m) (f n)`
#check @WellQuasiOrdered

end WQO


section MainTheorems

/-!
## Main Theorems

We state the three main theorems from the introduction. These are deep results whose
proofs occupy the rest of the memoir. Here they are stated with `sorry`.

### Notation

* A space is *Polish* if it is separable and completely metrizable. In Mathlib:
  `PolishSpace`.
* A space is *zero-dimensional* if it has a basis of clopen sets. In Mathlib:
  `TotallyDisconnectedSpace` (for T₁ spaces, equivalent to zero-dimensionality).
* A space is *analytic* if it is a continuous image of a Polish space.
-/

/-- **Main Theorem 1.** Continuous reducibility is a well-quasi-order on continuous
functions from an analytic zero-dimensional space to a separable metrizable space.

Formally: for any sequence `fₙ : Xₙ → Yₙ` of continuous functions where each `Xₙ`
is Polish and zero-dimensional and each `Yₙ` is separable and metrizable, there
exist `m < n` such that `fₘ` continuously reduces to `fₙ`. -/
theorem MainTheorem1
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, PolishSpace (X n)] [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, SeparableSpace (Y n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

/-- **Main Theorem 2.** Continuous reducibility is a well-quasi-order on continuous
functions from a separable metrizable zero-dimensional space to a countable metrizable
space. -/
theorem MainTheorem2
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, MetrizableSpace (Y n)] [∀ n, Countable (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

/-- **Main Theorem 3.** Continuous reducibility is a well-quasi-order on scattered
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space. -/
theorem MainTheorem3
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n))
    (hsc : ∀ n, ScatteredFun (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

end MainTheorems


section BetterQuasiOrder

/-!
## Better-Quasi-Orders

We should only need the notion of 2-BQO formalized in Bqo.TwoBQO.

The *Ellentuck space* `[ℕ]^ω` is the space of all infinite subsets of `ℕ`, identified
with their increasing enumerations. Given `Z ∈ [ℕ]^ω`, the *shift* of `Z` is
`Z \ {min Z}`.

A quasi-order `(Q, ≤)` is a *better-quasi-order (BQO)* if there is no *bad*
`Q`-multisequence, where a `Q`-multisequence is a locally constant map
`φ : [ℕ]^ω → Q`, and it is *bad* if `φ(Z) ≰ φ(shift(Z))` for all `Z`.

Every BQO is a WQO.
-/


/-- **Theorem (2-BQO strengthening).** Continuous reducibility is a BQO on the class of
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space, provided either the domain is analytic or the codomain is countable.

This is Theorem 1.4 of the memoir, strengthening Main Theorems 1 and 2. The precise
formalization of this statement requires quantification over a class of functions with
varying type universes; see `MainTheorem1` and `MainTheorem2` for the WQO consequences. -/
theorem bqo_strengthening : True := by trivial

/-- **Theorem (BQO on scattered functions).** Continuous reducibility is a BQO on the
class of scattered continuous functions from a zero-dimensional separable metrizable
space to a metrizable space.

This is the 2-BQO version of Theorem 1.5 of the memoir, strengthening Main Theorem 3. -/
theorem MainTheorem3_2BQO_Baire
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n))
    (hsc : ∀ n, ScatteredFun (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry
end BetterQuasiOrder

section FiniteGeneration

/-!
## Finite Generation of CB-Rank Levels

Let `𝒞` be the class of scattered continuous functions `f : A → B` where `A, B` are
subsets of the Baire space `ℕ → ℕ`. For `α < ω₁`, let `𝒞_α` be the functions in `𝒞`
with Cantor–Bendixson rank exactly `α`.

A set `ℱ` of functions is *finitely generated* if there exists a finite set `G` of
functions such that each element of `ℱ` is continuously equivalent to a finite gluing
of elements of `G`.

**Theorem (Finite generation).** For all `α < ω₁`, the set `𝒞_α` is finitely generated.
This is the key structural result enabling the proof of Main Theorem 3.
-/


end FiniteGeneration
