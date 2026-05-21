import WqoContinuousFunctions.PointedGluing.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `4_centered_memo.tex` — Definitions

This file contains the definitions from Chapter 4 (Centered Functions) of the memoir
on continuous reducibility between functions.

## Main definitions

* `IsCenterFor` — a point `x` is a center for a function `g`
* `IsCentered` — a function admits a center
* `IsRegularSeq` — a sequence is regular for continuous reducibility
* `Cocenter` — the cocenter of a centered scattered function
* `IsLocallyCentered` — a function is locally centered
-/

noncomputable section

/-!
## Definition: Center and Centered Functions
-/

/-- A point `x ∈ A` is a *center* for a function `g : A → B` if for every neighbourhood
`U` of `x` we have `g ≤ g|_U` (i.e., `g` continuously reduces to its restriction to
any neighbourhood of `x`). -/
def IsCenterFor {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (g : A → B) (x : A) : Prop :=
  ∀ U : Set A, IsOpen U → x ∈ U →
    ContinuouslyReduces g (g ∘ (Subtype.val : U → A))

/-- A function `g : A → B` is *centered* if it admits a center. -/
def IsCentered {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (g : A → B) : Prop :=
  ∃ x : A, IsCenterFor g x

/-!
## Definition: Regular Sequence
-/

/-- A sequence `(f_i)_{i ∈ ℕ}` of functions is *regular* (for continuous reducibility)
if for every `i ∈ ℕ`, the set `{j ∈ ℕ | f_i ≤ f_j}` is infinite. -/
def IsRegularSeq {X Y : ℕ → Type*}
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    (f : ∀ n, X n → Y n) : Prop :=
  ∀ i : ℕ, Set.Infinite {j : ℕ | ContinuouslyReduces (f i) (f j)}

/-- A sequence is *monotone* for continuous reducibility:
for all `i ≤ j`, `f_i ≤ f_j`. -/
def IsMonotoneSeq {X Y : ℕ → Type*}
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    (f : ∀ n, X n → Y n) : Prop :=
  ∀ i j : ℕ, i ≤ j → ContinuouslyReduces (f i) (f j)

/-- A monotone sequence is regular. -/
theorem IsMonotoneSeq.isRegularSeq {X Y : ℕ → Type*}
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    {f : ∀ n, X n → Y n} (hf : IsMonotoneSeq f) : IsRegularSeq f := fun i =>
  Set.infinite_of_injective_forall_mem (f := fun n => n + i + 1)
    (fun m n (h : m + i + 1 = n + i + 1) => by omega)
    (fun n => hf i (n + i + 1) (by omega))

/-!
## Definition: Cocenter
-/

/-- The *cocenter* of a centered function `f` is the common image of all centers of `f`
under `f`. This is well-defined when `f` is scattered (by Proposition
`scatteredhavecocenter`). -/
noncomputable def cocenter {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hc : IsCentered f) : B :=
  f hc.choose

/-!
## Definition: Locally Centered
-/

/-- A function `f : A → B` is *locally centered* if every point `x ∈ A` admits a
neighbourhood `U` such that `f|_U` is centered. -/
def IsLocallyCentered {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) : Prop :=
  ∀ x : A, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧
    IsCentered (f ∘ (Subtype.val : U → A))

/-!
## Useful abbreviation for rays
-/

/-- The *n*-th ray of `f` at `y`: the restriction of `f` to the set of points
that agree with `y` on the first `n` coordinates but differ at position `n`. -/
abbrev RayFun {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (y : ℕ → ℕ) (n : ℕ) :
    {a : A | (∀ k, k < n → f a k = y k) ∧ f a n ≠ y n} → ℕ → ℕ :=
  f ∘ Subtype.val

end
