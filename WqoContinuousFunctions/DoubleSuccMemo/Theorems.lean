import WqoContinuousFunctions.DoubleSuccMemo.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `6_double_successor_memo.tex` — Main Theorems

This file formalizes the main theorems from Chapter 6 (Finite Generation at Double
Successors) of the memoir on continuous reducibility between functions on the Baire space.

## Main results

### Section 1: Fine partitions (§6.1)
* `refining_dissolves_lump` — Lemma 6.1 (RefiningBy1): Dissolving lumps
* `gobbling_less_than_lambda` — Lemma 6.2 (gobblingLessThanLambda): Gobbling up small functions
* `existence_fine_partitions` — Proposition 6.3 (ExistenceFinePartitions):
  Existence of fine c-partitions

### Section 2: Pseudo-centered functions (§6.2)
* `vertical_theorem` — Theorem 6.4 (VerticalTheorem): Vertical theorem

### Section 3: Strongly solvable functions (§6.3)
* `diagonal_theorem` — Theorem 6.5 (DiagonalTheorem): Diagonal theorem

### Section 4: Solvable functions (§6.4)
* `solvable_decomposition` — Theorem 6.6 (SolvableDecomposition):
  Solvable decomposition of fine c-partitions
* `solvable_lambda_plus_one` — Proposition 6.7 (solvablelambda+1):
  Statement S(λ) for limit λ
* `FG_for_solvable` — Theorem 6.8 (FiniteGenerationForSolvable):
  Finite generation for solvable functions
* `FG_at_double_successors` — Theorem 6.9 (FGatdoublesuccessors):
  The main inductive step: FG(<α+2) ⟹ FG(≤α+2)

## References
- Chapter 6 of the memoir on continuous reducibility
-/

noncomputable section

/-!
## Section 1: Dissolving Lumps (Lemma 6.1)
-/

/-- **Lemma 6.1 (lemma:RefiningBy1).** Dissolving lumps.

Let `α < ω₁` and assume `FG(< α)`. Let `f ∈ 𝒞_α` and `𝒫` a c-partition for `f`.
If `(g, y)` is a 𝒫-lump of rank `β ≤ α`, then there exists a finer c-partition `𝒫'`
such that:
1. `(g, y)` is not a 𝒫'-lump.
2. `𝒫 \ 𝒫_{(g,y)} ⊆ 𝒫'`.
3. Every 𝒫'-lump is either a 𝒫-lump or has rank `< β`. -/
theorem refining_dissolves_lump
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_below α)
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f α)
    (P : IsCPartition f)
    (L : IsLump f P α)
    (hβ : L.rank ≤ α) :
    ∃ (P' : IsCPartition f),
      -- (1) (g, y) is not a 𝒫'-lump
      (¬ ∃ (L' : IsLump f P' α), L'.g = L.g ∧ L'.y = L.y) ∧
      -- (3) every 𝒫'-lump is either a 𝒫-lump or has rank < β
      (∀ (L' : IsLump f P' α),
        (∃ (L₀ : IsLump f P α), L₀.g = L'.g ∧ L₀.y = L'.y) ∨
        L'.rank < L.rank) := by
  sorry

/-!
## Section 1: Gobbling Up Small Functions (Lemma 6.2)
-/

/-- **Lemma 6.2 (lem:gobblingLessThanLambda).** Gobbling up small functions.

Let `λ < ω₁` be limit and `f ∈ 𝒞`. Assume that `f = f₀ ⊔ f₁` with `f₀` centered,
`pgl k_λ ≤ f₀`, and `f₁ ≤ k_λ`. Then `f` is centered and `f ≡ f₀`.

The key idea is that the large centered piece `f₀` "gobbles up" the small piece `f₁`
of rank `< λ`. -/
theorem gobbling_less_than_lambda
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam)
    -- f = f₀ ⊔ f₁ (disjoint union)
    (A₀ A₁ : Set (ℕ → ℕ))
    (hA_clopen₀ : IsClopen A₀) (hA_clopen₁ : IsClopen A₁)
    (hA_disj : Disjoint A₀ A₁) (hA_cover : A₀ ∪ A₁ = Set.univ)
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf_cont : Continuous f)
    -- f₀ is centered
    (hf₀_centered : IsCentered (f ∘ (Subtype.val : A₀ → ℕ → ℕ)))
    -- pgl k_λ ≤ f₀ : there exists a centered function h of CB-rank λ
    -- such that its pointed gluing reduces to f₀
    (hf₀_large : ∃ (h : (ℕ → ℕ) → (ℕ → ℕ)),
      CBRank h = lam ∧ IsCentered h ∧
      ∃ (A_pgl : ℕ → Set (ℕ → ℕ)) (B_pgl : ℕ → Set (ℕ → ℕ))
        (pgl_f : ∀ i, A_pgl i → B_pgl i),
        ContinuouslyReduces
          (fun (x : PointedGluingSet A_pgl) => PointedGluingFun A_pgl B_pgl pgl_f x)
          (f ∘ (Subtype.val : A₀ → ℕ → ℕ)))
    -- f₁ ≤ k_λ
    (hf₁_small : ∃ (h : (ℕ → ℕ) → (ℕ → ℕ)),
      CBRank h = lam ∧
      ContinuouslyReduces (f ∘ (Subtype.val : A₁ → ℕ → ℕ)) h) :
    -- Conclusion: f is centered and f ≡ f₀
    IsCentered f ∧
    ContinuouslyEquiv f (f ∘ (Subtype.val : A₀ → ℕ → ℕ)) := by
  sorry

/-!
## Section 1: Existence of Fine c-Partitions (Proposition 6.3)
-/

/-- **Proposition 6.3 (ExistenceFinePartitions).** Existence of fine c-partitions.

Let `α = λ + n + 2` with `λ < ω₁` limit, `n ∈ ℕ`, and assume `FG(< α)`.
Then every function in `𝒞_α` admits a fine c-partition.

The proof constructs a sequence of c-partitions by dissolving lumps in decreasing
order of rank, then gobbles up any small pieces of rank `< λ`. -/
theorem existence_fine_partitions
    (lam : Ordinal.{0}) (hlam : lam = 0 ∨ Order.IsSuccLimit lam)
    (n : ℕ)
    (α : Ordinal.{0}) (hα_eq : α = lam + ↑n + 2)
    (hα_lt : α < omega1)
    (hFG : FiniteGeneration_below α)
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f α) :
    ∃ (P : IsFineCPartition f α), True := by
  sorry

/-!
## Section 2: Vertical Theorem (Theorem 6.4)
-/

/-- **Theorem 6.4 (VerticalTheorem).** Vertical Theorem.

Let `α < ω₁` and assume `FG(≤ α + 1)`. Let `f : A → B` in `𝒞_{α+2}` be
pseudo-centered at `y`. There exist `g ∈ C(α + 2)` and `H ⊆ W(α + 1)` such that
for all clopen neighborhoods `U` of `y`, there is a clopen set `W ⊆ U` and a clopen
partition `A = A⁰ ⊔ A¹` such that:
1. `y ∉ W` and `f|_{A⁰} ≤ ⊔ H ≤ f↾W`.
2. For all clopen `V ∋ y`, `f|_{A¹} ≤ g ≤ f↾V` (in fact `g ≤ f|_{A¹}↾V`).
3. `⊔ H ≤ g`, so in particular `f ≤ g ⊔ g`.

This theorem handles the case of disjoint unions of the same centered function
with a single cocenter. -/
theorem vertical_theorem
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_le (α + 1))
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f (α + 2))
    (hpc : IsPseudoCentered f (α + 2)) :
    -- There exist g ∈ C(α+2) and H ⊆ W(α+1)
    ∃ (g : (ℕ → ℕ) → (ℕ → ℕ)),
      IsCentered g ∧ InCBLevel g (α + 2) ∧
      -- For all clopen U ∋ y, there exist W ⊆ U and partition A = A⁰ ⊔ A¹
      (∀ (U : Set (ℕ → ℕ)), IsClopen U → hpc.y ∈ U →
        ∃ (W : Set (ℕ → ℕ)) (A₀ A₁ : Set (ℕ → ℕ)),
          -- W ⊆ U, y ∉ W
          W ⊆ U ∧ hpc.y ∉ W ∧
          -- A₀, A₁ partition the domain
          IsClopen A₀ ∧ IsClopen A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = Set.univ ∧
          -- (1) f|_{A⁰} ≤ some H-related function ≤ f↾W
          (∃ (w : (ℕ → ℕ) → (ℕ → ℕ)),
            ContinuouslyReduces (f ∘ (Subtype.val : A₀ → ℕ → ℕ)) w ∧
            ContinuouslyReduces w (CoRestrict' f W)) ∧
          -- (2) f|_{A¹} ≤ g ≤ f↾V for all clopen V ∋ y
          ContinuouslyReduces (f ∘ (Subtype.val : A₁ → ℕ → ℕ)) g ∧
          (∀ (V : Set (ℕ → ℕ)), IsClopen V → hpc.y ∈ V →
            ContinuouslyReduces g (CoRestrict' f V))) ∧
      -- (3) f ≤ g ⊔ g (i.e., f reduces to the gluing of two copies of g)
      ContinuouslyReduces f
        (fun (x : ℕ → ℕ) => prepend (x 0) (g (unprepend x))) := by
  sorry

/-!
## Section 3: Diagonal Theorem (Theorem 6.5)
-/

/-- **Theorem 6.5 (DiagonalTheorem).** Diagonal Theorem.

Assume `FG(≤ α + 1)` for `α < ω₁`. Let `f : A → B` in `𝒞_{α+2}` be strongly
solvable at `y`. Then there exists `g ∈ FinGl(𝒢(α + 2))` such that
`f ≤ g ≤ f↾U` for all clopen `U ∋ y`.

This handles the case where cocenters `{y_P | P ∈ 𝒫 \ 𝒫_y}` converge to `y`
and the restrictions satisfy a nice combinatorial property. -/
theorem diagonal_theorem
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_le (α + 1))
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f (α + 2))
    (hss : IsStronglySolvable f (α + 2)) :
    ∃ (m : ℕ) (gs : Fin m → ((ℕ → ℕ) → (ℕ → ℕ))),
      -- Each g_i is a generator at level α + 2
      (∀ i, InCBLevelLE (gs i) (α + 2)) ∧
      -- f ≤ ⊔ gs
      ContinuouslyReduces f
        (fun x => prepend (x 0)
          (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x)) ∧
      -- ⊔ gs ≤ f↾U for all clopen U ∋ y
      (∀ (U : Set (ℕ → ℕ)), IsClopen U → hss.y ∈ U →
        ContinuouslyReduces
          (fun x => prepend (x 0)
            (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x))
          (CoRestrict' f U)) := by
  sorry

/-!
## Section 4: Solvable Decomposition (Theorem 6.6)
-/

/-- **Theorem 6.6 (SolvableDecomposition).** Solvable decomposition.

For `α < ω₁`, assume `FG(< α + 2)` and let `𝒫` be a fine c-partition of
`f : A → B` in `𝒞_{α+2}`. Then there exists a countable family `𝒰` of pairwise
disjoint clopen subsets of `B` such that:
1. `Y_𝒫 ⊆ ⋃ 𝒰`.
2. For all `U ∈ 𝒰`, the function `f|_{A^U_𝒫}` is solvable with `𝒫↾U`. -/
theorem solvable_decomposition
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_below (α + 2))
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f (α + 2))
    (P : IsFineCPartition f (α + 2)) :
    ∃ (U : ℕ → Set (ℕ → ℕ)),
      -- The sets are pairwise disjoint and clopen
      (∀ i, IsClopen (U i)) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      -- They cover Y_𝒫
      P.toIsCPartition.cocenterSet ⊆ ⋃ i, U i ∧
      -- Each restriction is solvable
      (∀ i, ∃ (S : IsSolvableFun
        (f ∘ (Subtype.val :
          (⋃ (k ∈ P.toIsCPartition.corestrictionParts (U i)), P.parts k) → ℕ → ℕ))
        (α + 2)), True) := by
  sorry

/-!
## Section 4: Solvable at λ + 1 (Proposition 6.7)
-/

/-- **Proposition 6.7 (solvablelambda+1).** Statement S(λ) for limit or null λ.

Let `λ < ω₁` be limit or null and assume `FG(≤ λ)`. Suppose that `f : A → B`
in `𝒞_{λ+1}` is solvable with `𝒫`.

Then there exists a finite gluing `g` of functions in `𝒢(λ + 1)` such that
`f ≤ g` and `g ≤ f↾U` for every clopen `U ⊇ Y_𝒫`. -/
theorem solvable_lambda_plus_one
    (lam : Ordinal.{0})
    (hlam : lam = 0 ∨ Order.IsSuccLimit lam)
    (hlam_lt : lam < omega1)
    (hFG : FiniteGeneration_le lam)
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f (lam + 1))
    (S : IsSolvableFun f (lam + 1)) :
    ∃ (m : ℕ) (gs : Fin m → ((ℕ → ℕ) → (ℕ → ℕ))),
      (∀ i, InCBLevelLE (gs i) (lam + 1)) ∧
      -- f ≤ ⊔ gs
      ContinuouslyReduces f
        (fun x => prepend (x 0)
          (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x)) ∧
      -- ⊔ gs ≤ f↾U for all clopen U ⊇ Y_𝒫
      (∀ (U : Set (ℕ → ℕ)), IsClopen U →
        S.toIsCPartition.cocenterSet ⊆ U →
        ContinuouslyReduces
          (fun x => prepend (x 0)
            (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x))
          (CoRestrict' f U)) := by
  sorry

/-!
## Section 4: Finite Generation for Solvable Functions (Theorem 6.8)
-/

/-- **Theorem 6.8 (FiniteGenerationForSolvable).** Finite generation for solvable functions.

Assume `FG(≤ α + 1)` for `α < ω₁`. Let `f : A → B` in `𝒞_{α+2}` be solvable with `𝒫`.
Then there exists `g ∈ FinGl(𝒢(α + 2))` such that `f ≤ g` and `g ≤ f↾U`,
so in particular `f ≡ g ≡ f↾U`, for every clopen `U ⊇ Y_𝒫`.

The proof uses the Diagonal Theorem for the strongly solvable part and
intertwining reductions for the remaining part. -/
theorem FG_for_solvable
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_le (α + 1))
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : InCBLevel f (α + 2))
    (S : IsSolvableFun f (α + 2)) :
    ∃ (m : ℕ) (gs : Fin m → ((ℕ → ℕ) → (ℕ → ℕ))),
      (∀ i, InCBLevelLE (gs i) (α + 2)) ∧
      -- f ≤ ⊔ gs
      ContinuouslyReduces f
        (fun x => prepend (x 0)
          (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x)) ∧
      -- ⊔ gs ≤ f↾U for all clopen U ⊇ Y_𝒫
      (∀ (U : Set (ℕ → ℕ)), IsClopen U →
        S.toIsCPartition.cocenterSet ⊆ U →
        ContinuouslyReduces
          (fun x => prepend (x 0)
            (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x))
          (CoRestrict' f U)) := by
  sorry

/-!
## Section 4: Finite Generation at Double Successors (Theorem 6.9)

This is the main result of the chapter, completing the inductive step of the
Precise Structure Theorem.
-/

/-- **Theorem 6.9 (FGatdoublesuccessors).** Finite generation at double successors.

For all `α < ω₁`, if `FG(< α + 2)` holds then so does `FG(≤ α + 2)`.

The proof combines:
1. Existence of fine c-partitions (Proposition 6.3)
2. Solvable decomposition (Theorem 6.6)
3. Finite generation for solvable functions at level λ+1 (Proposition 6.7)
4. Finite generation for solvable functions at level α+2 (Theorem 6.8) -/
theorem FG_at_double_successors
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_below (α + 2)) :
    FiniteGeneration_le (α + 2) := by
  sorry

/-!
## Corollary: Proof of the Precise Structure Theorem

Combining the results from all chapters:
- `FG(0)` and `FG(λ)` for limit `λ` (base cases, Proposition 5.20)
- `FG(< λ+1) ⟹ FG(λ+1)` for limit `λ` (Theorem 5.13)
- `FG(< α+2) ⟹ FG(≤ α+2)` (Theorem 6.9 above)

we obtain by transfinite induction that `FG(α)` holds for all `α < ω₁`.
-/

/-- **Precise Structure Theorem (combined).** For all `α < ω₁`, `FG(α)` holds.

This is the culmination of the entire memoir: every level `𝒞_α` of the hierarchy
of scattered continuous functions is finitely generated by a finite set of generators
`𝒢(α)`.

As a consequence, continuous reducibility is a better-quasi-order (BQO) on scattered
continuous functions. -/
theorem preciseStructureThm_combined
    (α : Ordinal.{0}) (hα : α < omega1) :
    FiniteGeneration α := by
  sorry

/-- **Main Theorem (BQO).** Continuous reducibility is a BQO on scattered continuous
functions between zero-dimensional Polish spaces. -/
theorem bqo_scattered_combined
    (α : Ordinal.{0}) (hα : α < omega1) :
    -- Every infinite sequence of scattered continuous functions of CB-rank < α
    -- contains a reduction f_m ≤ f_n with m < n.
    ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n) := by
  sorry

end
