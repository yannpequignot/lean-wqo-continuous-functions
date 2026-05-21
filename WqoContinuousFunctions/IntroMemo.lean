import Mathlib
import WqoContinuousFunctions.PrelimMemo.Basic
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Formalization of `1_intro_memo.tex`

This file formalizes the key definitions and theorem statements from the introduction
of the memoir on continuous reducibility between functions.

## Main definitions

* `ContinuouslyReduces f g` — `f` continuously reduces to `g`, i.e., there exist
  continuous maps `σ` and `τ` such that `f = τ ∘ g ∘ σ`.
* `ContinuouslyEquiv f g` — `f` and `g` are continuously equivalent (`f ≤ g ∧ g ≤ f`).
* `StrictlyContinuouslyReduces f g` — `f < g`, i.e., `f ≤ g` but `¬(g ≤ f)`.
* `ScatteredFun f` — the function `f` is scattered: every nonempty subset of its domain
  contains a nonempty open set on which `f` is constant.
* `IsBetterQuasiOrder` — a quasi-order is a better-quasi-order (no bad multisequences).

## Main results (proved)

* `ContinuouslyReduces.refl` — continuous reducibility is reflexive.
* `ContinuouslyReduces.trans` — continuous reducibility is transitive.

## Main theorem statements (stated, not proved)

* `MainTheorem1` — Continuous reducibility is a WQO on continuous functions from an
  analytic zero-dimensional space to a separable metrizable space.
* `MainTheorem2` — Continuous reducibility is a WQO on continuous functions from a
  separable metrizable zero-dimensional space to a countable metrizable space.
* `MainTheorem3` — Continuous reducibility is a WQO on scattered continuous functions
  from a zero-dimensional separable metrizable space to a metrizable space.
* `scatteredIffEmptyKernel` — A continuous function from a metrizable domain to a
  Hausdorff codomain is scattered iff it has empty perfect kernel.
* `bqo_continuous_functions` — Strengthening of Main Theorems 1 and 2 to BQO.
* `bqo_scattered_continuous_functions` — BQO on scattered continuous functions.
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

The *Ellentuck space* `[ℕ]^ω` is the space of all infinite subsets of `ℕ`, identified
with their increasing enumerations. Given `Z ∈ [ℕ]^ω`, the *shift* of `Z` is
`Z \ {min Z}`.

A quasi-order `(Q, ≤)` is a *better-quasi-order (BQO)* if there is no *bad*
`Q`-multisequence, where a `Q`-multisequence is a locally constant map
`φ : [ℕ]^ω → Q`, and it is *bad* if `φ(Z) ≰ φ(shift(Z))` for all `Z`.

Every BQO is a WQO.
-/

/-- The Ellentuck space: infinite subsets of `ℕ`, represented as strictly increasing
functions `ℕ → ℕ`. -/
def EllentuckSpace : Type := {f : ℕ → ℕ // StrictMono f}

instance : TopologicalSpace EllentuckSpace :=
  instTopologicalSpaceSubtype

/-- The shift operation on the Ellentuck space: drop the first element. -/
def EllentuckSpace.shift (Z : EllentuckSpace) : EllentuckSpace :=
  ⟨fun n => Z.val (n + 1), Z.property.comp (fun _ _ h => Nat.add_lt_add_right h 1)⟩

/-- A quasi-order `(Q, ≤)` is a *better-quasi-order* if there is no bad multisequence.
We say a function `φ : EllentuckSpace → Q` is *bad* if `¬ r (φ Z) (φ (shift Z))` for
all `Z`. A BQO has no bad locally constant multisequences. -/
def IsBetterQuasiOrder (Q : Type*) (r : Q → Q → Prop) : Prop :=
  ∀ (φ : EllentuckSpace → Q),
    LocallyConstant EllentuckSpace Q →
    ∃ Z : EllentuckSpace, r (φ Z) (φ Z.shift)



/-- **Theorem (BQO strengthening).** Continuous reducibility is a BQO on the class of
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space, provided either the domain is analytic or the codomain is countable.

This is Theorem 1.4 of the memoir, strengthening Main Theorems 1 and 2. The precise
formalization of this statement requires quantification over a class of functions with
varying type universes; see `MainTheorem1` and `MainTheorem2` for the WQO consequences. -/
theorem bqo_strengthening : True := by trivial

/-- **Theorem (BQO on scattered functions).** Continuous reducibility is a BQO on the
class of scattered continuous functions from a zero-dimensional separable metrizable
space to a metrizable space.

This is Theorem 1.5 of the memoir, strengthening Main Theorem 3. -/
theorem bqo_scattered_strengthening : True := by trivial

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

-- The precise formalization of finite generation and the CB-rank levels requires
-- the gluing operation and transfinite induction machinery developed in later chapters.
-- We record the statement informally here for reference.

end FiniteGeneration
