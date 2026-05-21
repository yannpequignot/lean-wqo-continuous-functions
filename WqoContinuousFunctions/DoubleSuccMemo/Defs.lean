import WqoContinuousFunctions.PreciseStructMemo.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `6_double_successor_memo.tex` — Definitions

This file formalizes the definitions from Chapter 6 (Finite Generation at Double
Successors) of the memoir on continuous reducibility between functions on the Baire space.

## Main definitions

### Section 1: Fine partitions in centered functions (§6.1)
* `IsCPartition` — a clopen partition such that each restriction is centered
* `CPartitionCocenters` — the set `Y_𝒫` of cocenters of a c-partition
* `CPartitionRestriction` — the function `f_{(g,y)}`
* `OmegaRegularSet` — the set `W(α)` = {k_λ} ∪ {ωh | h ∈ C(α)}
* `IsOmegaRegularAt` — ω-regularity of a function at a point
* `IsLump` — a lump is a pair (g, y) where f_{(g,y)} is not ω-regular at y
* `IsFineCPartition` — a fine c-partition (no lumps, all ranks > λ)

### Section 2: Pseudo-centered functions (§6.2)
* `IsPseudoCentered` — pseudo-centered function with fine c-partition

### Section 3: Strongly solvable functions (§6.3)
* `IsStronglySolvable` — strongly solvable function at y

### Section 4: Solvable functions (§6.4)
* `IsSolvable` — solvable function with fine c-partition
* `CPartitionCorestriction` — corestriction of a c-partition to a clopen set

## References
- Chapter 6 of the memoir on continuous reducibility
-/

noncomputable section

/-!
## Section 1: c-Partitions
-/

/-- A *c-partition* of a function `f : A → B` is a countable clopen partition `𝒫` of `A`
such that for each `P ∈ 𝒫`, the restriction `f|_P` is centered with cocenter `y_P`.

We model a c-partition as:
- `parts : ℕ → Set A` — the clopen partition (indexed by ℕ)
- `cocenters : ℕ → B` — the cocenter of `f|_{parts i}` for each `i`
- proofs that the parts are clopen, pairwise disjoint, cover `A`, and each restriction
  is centered with the given cocenter. -/
structure IsCPartition {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) where
  /-- The clopen partition of the domain, indexed by ℕ. -/
  parts : ℕ → Set A
  /-- The cocenter of `f` restricted to each part. -/
  cocenters : ℕ → B
  /-- Each part is clopen. -/
  parts_clopen : ∀ i, IsClopen (parts i)
  /-- The parts are pairwise disjoint. -/
  parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)
  /-- The parts cover the domain. -/
  parts_cover : ⋃ i, parts i = Set.univ
  /-- Each restriction `f|_{parts i}` is centered. -/
  parts_centered : ∀ i, IsCentered (f ∘ (Subtype.val : parts i → A))
  /-- The cocenter of `f|_{parts i}` is `cocenters i`. -/
  cocenter_eq : ∀ i, cocenter (f ∘ (Subtype.val : parts i → A))
    (parts_centered i) = cocenters i

/-- The set of all cocenters `Y_𝒫 = {y_P | P ∈ 𝒫}`. -/
def IsCPartition.cocenterSet {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (P : IsCPartition f) : Set B :=
  Set.range P.cocenters

/-!
## Section 1: ω-regularity and lumps
-/

/-- The set `W(α) = {k_λ} ∪ {ω h | h ∈ C(α)}` where `α = λ + n` with `λ` limit.

This is a finite set of "test functions" used to define ω-regularity.
We model it abstractly as a finite set of functions on the Baire space. -/
def OmegaRegularSet (α : Ordinal.{0}) : Set ((ℕ → ℕ) → (ℕ → ℕ)) :=
  -- k_λ (the maximal function at the limit part of α)
  {h | ∃ (lam : Ordinal.{0}), (lam = 0 ∨ Order.IsSuccLimit lam) ∧
    lam ≤ α ∧ CBRank h = lam} ∪
  -- {ω h | h ∈ C(α)} (omega of centered functions at level α)
  {h | ∃ (g : (ℕ → ℕ) → (ℕ → ℕ)), IsCentered g ∧ InCBLevel g α ∧ h = OmegaFun g}

/-- A function `f` is *ω-regular* at a point `y` if for all `h ∈ W(α)`, the set
`{j ∈ ℕ | h ≤ ray_f(y, j)}` is either empty or infinite.

This property ensures that whenever a test function reduces to some ray of `f` at `y`,
it reduces to infinitely many such rays. -/
def IsOmegaRegularAt {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (y : ℕ → ℕ) (α : Ordinal.{0}) : Prop :=
  ∀ h ∈ OmegaRegularSet α,
    (Set.Finite {j : ℕ | ContinuouslyReduces h (RayFun f y j)} →
     {j : ℕ | ContinuouslyReduces h (RayFun f y j)} = ∅)

/-- A *lump* of a c-partition `𝒫` is a pair `(g, y)` where:
- `y` is a cocenter in `Y_𝒫`
- `g` is a centered function
- The combined function `f_{(g,y)} = ⊔_{P ∈ 𝒫_{g,y}} f|_P` is not ω-regular at `y`.

The *rank* of the lump is `CB(g)`. -/
structure IsLump {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (P : IsCPartition f) (α : Ordinal.{0}) where
  /-- The centered function `g`. -/
  g : (ℕ → ℕ) → (ℕ → ℕ)
  /-- The cocenter `y`. -/
  y : ℕ → ℕ
  /-- `y` is a cocenter in `Y_𝒫`. -/
  y_mem : y ∈ P.cocenterSet
  /-- `g` is centered. -/
  g_centered : IsCentered g
  /-- The combined restriction `f_{(g,y)}` is not ω-regular at `y`. -/
  not_regular : ¬ IsOmegaRegularAt f y α
  /-- The rank of the lump. -/
  rank : Ordinal.{0}
  /-- The rank equals `CB(g)`. -/
  rank_eq : rank = CBRank g

/-!
## Section 1: Fine c-partitions (Definition, §6.1.3)
-/

/-- A c-partition `𝒫` of `f ∈ 𝒞_{λ+n+1}` is *fine* if:
1. There are no 𝒫-lumps.
2. `CB(f|_P) > λ` for all `P ∈ 𝒫`.

Here `λ` is a limit ordinal and `n ∈ ℕ`. -/
structure IsFineCPartition {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (α : Ordinal.{0}) extends IsCPartition f where
  /-- The limit ordinal `λ` in the decomposition `α = λ + n + 1`. -/
  lam : Ordinal.{0}
  /-- `λ` is limit (or zero). -/
  lam_limit : lam = 0 ∨ Order.IsSuccLimit lam
  /-- `n` in the decomposition `α = λ + n + 1`. -/
  n : ℕ
  /-- `α = λ + n + 1`. -/
  alpha_eq : α = lam + ↑n + 1
  /-- There are no lumps. -/
  no_lumps : ¬ ∃ (_ : IsLump f toIsCPartition α), True
  /-- All parts have CB-rank > λ. -/
  parts_rank_gt_lam : ∀ i, lam < CBRank (f ∘ (Subtype.val : parts i → A))

/-!
## Section 2: Pseudo-centered functions (Definition)
-/

/-- A function `f` together with a fine c-partition is *pseudo-centered* at `y` if:
1. `Y_𝒫 = {y}` — there is a single cocenter.
2. For all `P, P' ∈ 𝒫`, `f|_P ≡ f|_{P'}`. -/
structure IsPseudoCentered {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (α : Ordinal.{0}) extends IsFineCPartition f α where
  /-- The common cocenter. -/
  y : ℕ → ℕ
  /-- All cocenters equal `y`. -/
  all_cocenters_eq : ∀ i, cocenters i = y
  /-- All restrictions are mutually equivalent. -/
  all_parts_equiv : ∀ i j, ContinuouslyEquiv
    (f ∘ (Subtype.val : parts i → A))
    (f ∘ (Subtype.val : parts j → A))

/-!
## Section 3: Strongly solvable functions (Definition)
-/

/-- A function `f` with a fine c-partition `𝒫` is *strongly solvable* at `y ∈ Y_𝒫`
if for all clopen neighborhoods `V` of `y`:
1. The set `{y_P | P ∈ 𝒫, y_P ∉ V}` is finite.
2. For all `P ∈ 𝒫` with `y_P ≠ y`, there exists `Q ∈ 𝒫` with `y_Q ∈ V` and
   `f|_P ≤ f|_Q`. -/
structure IsStronglySolvable {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (α : Ordinal.{0}) extends IsFineCPartition f α where
  /-- The distinguished point `y`. -/
  y : ℕ → ℕ
  /-- `y` is a cocenter. -/
  y_mem : y ∈ toIsCPartition.cocenterSet
  /-- Condition 1: finitely many cocenters outside any clopen neighborhood of `y`. -/
  finitely_many_outside : ∀ (V : Set (ℕ → ℕ)), IsClopen V → y ∈ V →
    Set.Finite {i : ℕ | cocenters i ∉ V}
  /-- Condition 2: each non-`y` part can be matched with a part whose cocenter is
  in any neighborhood of `y`. -/
  matching_condition : ∀ (V : Set (ℕ → ℕ)), IsClopen V → y ∈ V →
    ∀ i, cocenters i ≠ y →
    ∃ j, cocenters j ∈ V ∧ cocenters j ≠ y ∧
      ContinuouslyReduces
        (f ∘ (Subtype.val : parts i → A))
        (f ∘ (Subtype.val : parts j → A))

/-!
## Section 4: Solvable functions (Definition)
-/

/-- A function `f` is *solvable* with a fine c-partition `𝒫` if for some `y ∈ Y_𝒫`,
for all `P ∈ 𝒫` with `y_P ≠ y` and all clopen `V ∋ y`, there exists `Q ∈ 𝒫` with
`y_Q ∈ V`, `y_Q ≠ y`, and `f|_P ≤ f|_Q`.

Note: unlike strongly solvable, this does *not* require finitely many cocenters
outside any neighborhood. -/
structure IsSolvableFun {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (α : Ordinal.{0}) extends IsFineCPartition f α where
  /-- The distinguished point `y`. -/
  y : ℕ → ℕ
  /-- `y` is a cocenter. -/
  y_mem : y ∈ toIsCPartition.cocenterSet
  /-- Solvability condition: each non-`y` part can be matched with a part whose cocenter
  is in any neighborhood of `y`. -/
  solvability_condition : ∀ (V : Set (ℕ → ℕ)), IsClopen V → y ∈ V →
    ∀ i, cocenters i ≠ y →
    ∃ j, cocenters j ∈ V ∧ cocenters j ≠ y ∧
      ContinuouslyReduces
        (f ∘ (Subtype.val : parts i → A))
        (f ∘ (Subtype.val : parts j → A))

/-- The corestriction of a c-partition `𝒫` to a clopen set `U ⊆ B`:
`𝒫↾U = {P ∈ 𝒫 | y_P ∈ U}`.

The domain restricted to this sub-partition is `A^U_𝒫 = ⋃ (𝒫↾U)`. -/
def IsCPartition.corestrictionParts {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (P : IsCPartition f) (U : Set B) : Set ℕ :=
  {i | P.cocenters i ∈ U}

end
