import WqoContinuousFunctions.PreciseStructMemo.Defs
import WqoContinuousFunctions.PrelimMemo.Scattered.Decomposition

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `5_precise_struct_memo.tex` — Main Theorems

This file formalizes the main theorems from Chapter 5 (Precise Structure) of the
memoir on continuous reducibility between functions.

## Main results

### Section 1: The Wedge Operation (§5.1)
* `wedge_preserves_continuity` — Fact 5.3, Item 1
* `wedge_not_injective` — Fact 5.3, Item 2
* `wedge_CBrank` — Fact 5.3, Item 3
* `wedge_upper_bound` — Proposition 5.5 (Wedge as upper bound)
* `wedge_domination_equiv` — Corollary 5.6
* `disjointification_lemma` — Lemma 5.7 (Disjointification Lemma)

### Section 2: Finite Generation at Successors of Limits (§5.2)
* `infiniteEmbedOmegaStronger` — Lemma 5.9
* `intertwine_reductions` — Lemma 5.10
* `intertwine_reductions_omega_centered` — Lemma 5.11
* `diagonal_for_lambda_plus_one` — Lemma 5.12
* `FG_at_successor_of_limit` — Theorem 5.13

### Section 3: The Generators (§5.3)
* `alreadyKnownGenerators_1` — Fact 5.16, Item 1
* `generators_finite` — Proposition 5.17, Item 3
* `preciseStructureThm` — Theorem 5.18 (Precise Structure Theorem)
* `FG_base_cases` — Proposition 5.20, base cases
* `FG_implies_FG_succ_limit` — Proposition 5.20, Item 1
* `FG_le_implies_interval_gen` — Proposition 5.20, Item 2
* `FG_below_implies_bqo` — Proposition 5.20, Item 3
* `FG_below_implies_locally_centered` — Proposition 5.20, Item 4
* `FG_below_centered_classification` — Proposition 5.20, Item 5
-/

noncomputable section

/-!
## Section 1: The Wedge Operation — Basic Facts (Fact 5.3)
-/

/-- **Fact 5.3, Item 1 (BasicfactsWedge).** The wedge operation preserves continuity:
if each `f_i` is continuous, then `⋁(f₀, …, fₖ | f_{k+1})` is continuous. -/
theorem wedge_preserves_continuity
    (k : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ))
    (hv : ∀ i, Continuous (f_vert i))
    (hd : Continuous f_diag) :
    Continuous (WedgeFun k f_vert f_diag) := by
  sorry

/--
**Fact 5.3, Item 2 (BasicfactsWedge).** If `k > 0`, then the wedge is
not injective. This is because `(0) ⌢ 0^ω` and `(1) ⌢ 0^ω` both map to `0^ω`.
-/
theorem wedge_not_injective
    (k : ℕ) (hk : 0 < k)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ)) :
    ¬ Injective (WedgeFun k f_vert f_diag) := by
  unfold WedgeFun
  unfold zeroStream; simp +decide [Injective]
  use fun n => if n = 0 then 0 else 0, fun n => if n = 0 then 1 else 0; simp +decide [funext_iff]
  unfold unprepend; aesop

/-- **Fact 5.3, Item 3 (BasicfactsWedge).** CB-rank of the wedge:
`CB(⋁(f₀, …, fₖ | f_{k+1})) = max({CB(f_i) + 1 | i ≤ k} ∪ {CB(f_{k+1})})`.

We state this as: the CB-rank of the wedge equals the supremum of `CB(f_i) + 1`
for `i ≤ k` and `CB(f_{k+1})`. -/
theorem wedge_CBrank
    (k : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ))
    (hv : ∀ i, InScatteredClass (f_vert i))
    (hd : InScatteredClass f_diag) :
    CBRank (WedgeFun k f_vert f_diag) =
      (⨆ (i : Fin (k + 1)), CBRank (f_vert i) + 1) ⊔
      CBRank f_diag := by
  sorry

/-!
## Section 1: Wedge as Upper Bound (Proposition 5.5)
-/

/-- **Proposition 5.5 (Wedgeasupperbound).** Wedge as upper bound.

Let `f : A → B` be continuous in `𝒞`, and `(f_i)_{i ≤ k+1} ⊆ 𝒞`.
Suppose there exist `y ∈ B` and a clopen partition `(A_i)_{i ∈ ℕ}` of `A` such that:
1. For all `i ≤ k`, the rays of `f|_{A_i}` at `y` are reducible by pieces
   to the constant sequence `(f_i)`.
2. `(f|_{A_i})_{i > k}` is reducible by pieces to `(f_{k+1})`.
3. `f(A_i) → y`.

Then `f ≤ ⋁(f₀, …, fₖ | f_{k+1})`. -/
theorem wedge_upper_bound
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (hf_cont : Continuous f)
    (k : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ))
    -- Existence of y and clopen partition
    (y : ℕ → ℕ) (Aparts : ℕ → Set (ℕ → ℕ))
    (hclopen : ∀ i, IsClopen (Aparts i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Aparts i) (Aparts j))
    (hcover : ⋃ i, Aparts i = Set.univ)
    -- Condition 1: for all i ≤ k, the rays of f|_{A_i} at y are
    -- reducible by pieces to the constant sequence ω f_i
    (hvert : ∀ (i : Fin (k + 1)),
      ∃ (I : ℕ → Finset ℕ),
        (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
        ∀ j, ContinuouslyReduces
          (f ∘ (Subtype.val : RaySet (f '' (Aparts i)) y j → ℕ → ℕ))
          (f_vert i))
    -- Condition 2: the restrictions (f|_{A_i})_{i > k} are reducible by
    -- pieces to ω f_{k+1}
    (hdiag : ∃ (I : ℕ → Finset ℕ),
        (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
        ∀ i, ContinuouslyReduces
          (f ∘ (Subtype.val : (Aparts (k + 1 + i)) → ℕ → ℕ))
          (f_diag))
    -- Condition 3: f(A_i) converges to y
    (hconv : SetsConvergeTo (fun i => f '' (Aparts i)) y) :
    ContinuouslyReduces f (WedgeFun k f_vert f_diag) := by
  sorry

/-!
## Section 1: Wedge and Domination Equivalence (Corollary 5.6)
-/

/-- **Corollary 5.6 (cor:wedgeSets).** If the sets of vertical functions
`{f_i | i ≤ k}` and `{h_j | j ≤ l}` are domination-equivalent,
then `⋁(f₀, …, fₖ | g) ≡ ⋁(h₀, …, hₗ | g)`. -/
theorem wedge_domination_equiv
    (k l : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (h_vert : Fin (l + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (g : (ℕ → ℕ) → (ℕ → ℕ))
    (hv_cont : ∀ i, Continuous (f_vert i))
    (hw_cont : ∀ i, Continuous (h_vert i))
    (hg_cont : Continuous g)
    -- Domination equivalence of the verticals
    (hdom : ∀ (i : Fin (k + 1)), ∃ (j : Fin (l + 1)),
              ContinuouslyReduces (f_vert i) (h_vert j))
    (hdom' : ∀ (j : Fin (l + 1)), ∃ (i : Fin (k + 1)),
              ContinuouslyReduces (h_vert j) (f_vert i)) :
    ContinuouslyEquiv (WedgeFun k f_vert g) (WedgeFun l h_vert g) := by
  sorry

/-!
## Section 1: Disjointification Lemma (Lemma 5.7)
-/

/-- **Lemma 5.7 (DisjointificationLemma).** Wedge as lower bound.

Let `f : A → B` be continuous in `𝒞` and `(f_i)_{i ≤ k+1} ⊆ 𝒞`.
Suppose there exist `y ∈ im f` and `(x_i)_{i ≤ k}` in `f⁻¹({y})` such that:
1. For every `i ≤ k`, for every open `U ∋ x_i`, there exists `(σ, τ)` reducing
   `f_i` to `f` with `im(σ) ⊆ U` and `y ∉ cl(im(f ∘ σ))`.
2. For every open `V ∋ y`, there exists `(σ, τ)` reducing `f_{k+1}` to `f`
   with `im(f ∘ σ) ⊆ V` and `y ∉ cl(im(f ∘ σ))`.

Then `⋁(f₀, …, fₖ | f_{k+1}) ≤ f`. -/
theorem disjointification_lemma
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (hf_cont : Continuous f)
    (k : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ))
    -- y in im f and x_i in f⁻¹(y)
    (y : ℕ → ℕ) (hy : y ∈ Set.range f)
    (x : Fin (k + 1) → (ℕ → ℕ)) (hx : ∀ i, f (x i) = y)
    -- Condition 1: for each vertical, reductions with image in neighborhoods of x_i
    (hcond1 : ∀ (i : Fin (k + 1)) (U : Set (ℕ → ℕ)), IsOpen U → x i ∈ U →
      ∃ (σ : (ℕ → ℕ) → (ℕ → ℕ)) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
        Continuous σ ∧ ContinuousOn τ (Set.range (f ∘ σ)) ∧
        (∀ z, f_vert i z = τ (f (σ z))) ∧
        Set.range σ ⊆ U ∧
        y ∉ closure (Set.range (f ∘ σ)))
    -- Condition 2: for diagonal, reductions with image in neighborhoods of y
    (hcond2 : ∀ (V : Set (ℕ → ℕ)), IsOpen V → y ∈ V →
      ∃ (σ : (ℕ → ℕ) → (ℕ → ℕ)) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
        Continuous σ ∧ ContinuousOn τ (Set.range (f ∘ σ)) ∧
        (∀ z, f_diag z = τ (f (σ z))) ∧
        Set.range (f ∘ σ) ⊆ V ∧
        y ∉ closure (Set.range (f ∘ σ))) :
    ContinuouslyReduces (WedgeFun k f_vert f_diag) f := by
  sorry

/-!
## Section 2: Infinite Embed Omega Stronger (Lemma 5.9)
-/

/-- **Lemma 5.9 (InfiniteEmbedOmegaStronger).** Let `X₀, …, Xₙ` be infinite
subsets of a metrizable space `B`. Then there are pairwise disjoint infinite
sets `Y_i ⊆ X_i` for all `i ≤ n` such that `⋃_{i ≤ n} Y_i` is discrete. -/
theorem infiniteEmbedOmegaStronger
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    (n : ℕ) (X : Fin (n + 1) → Set B)
    (hX_inf : ∀ i, Set.Infinite (X i)) :
    ∃ Y : Fin (n + 1) → Set B,
      (∀ i, Y i ⊆ X i) ∧
      (∀ i, Set.Infinite (Y i)) ∧
      (∀ i j, i ≠ j → Disjoint (Y i) (Y j)) ∧
      DiscreteTopology (⋃ i, Y i : Set B) := by
  sorry

/-!
## Section 2: Intertwining Reductions (Lemma 5.10)
-/

/-- **Lemma 5.10 (Intertwinereductions).** Let `f ∈ 𝒞` be continuous
and `G ⊆ 𝒞` be a finite set of functions. Suppose that for all `g ∈ G`,
there are infinitely many points `y ∈ B` such that for all neighborhoods
`V ∋ y` we have `g ≤ f↾V`. Then `ω G ≤ f`. -/
theorem intertwine_reductions
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (hf_cont : Continuous f)
    (n : ℕ) (G : Fin (n + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    -- For each g ∈ G, infinitely many y with g ≤ f↾V for all V ∋ y
    (hG : ∀ (i : Fin (n + 1)),
      Set.Infinite {y : ℕ → ℕ | ∀ (V : Set (ℕ → ℕ)), IsOpen V → y ∈ V →
        ContinuouslyReduces (G i) (CoRestrict f V)}) :
    -- ω G ≤ f (i.e., the infinite gluing of the G_i reduces to f)
    ContinuouslyReduces
      (OmegaFun (fun x => prepend (x 0) (G ⟨x 0 % (n + 1), Nat.mod_lt _ (by omega)⟩ (unprepend x))))
      f := by
  sorry

/-!
## Section 2: Intertwining Reductions for Omega Centered (Lemma 5.11)
-/

/-- **Lemma 5.11 (Intertwinereductionsforomegacentered).** Let `f ∈ 𝒞` be continuous
and `G ⊆ 𝒞` be a finite set of centered functions. If `ω g ≤ f` for all `g ∈ G`,
then `ω G ≤ f`.

Moreover, if `f = ⊔_{i=0}^{m} f_i`, then:
1. If `g` is centered and `ω g ≤ f`, then `ω g ≤ f_i` for some `i ≤ m`.
2. If `λ` is limit and `k_λ ≤ f`, then `k_λ ≤ f_i` for some `i ≤ m`. -/
theorem intertwine_reductions_omega_centered
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (hf_cont : Continuous f)
    (n : ℕ) (G : Fin (n + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (hG_cent : ∀ i, IsCentered (G i))
    (hG_omega : ∀ i, ContinuouslyReduces (OmegaFun (G i)) f) :
    -- ω(⊔ G) ≤ f
    ContinuouslyReduces
      (OmegaFun (fun x => prepend (x 0) (G ⟨x 0 % (n + 1), Nat.mod_lt _ (by omega)⟩ (unprepend x))))
      f := by
  sorry

/-- **Lemma 5.11, Item 1.** If `g` is centered and `ω g ≤ f = ⊔ f_i`,
then `ω g ≤ f_i` for some `i`. -/
theorem omega_centered_to_component
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (m : ℕ)
    (A : Fin (m + 1) → Set (ℕ → ℕ))
    (hA_clopen : ∀ i, IsClopen (A i))
    (hA_disj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hA_cover : ⋃ i, A i = Set.univ)
    (g : (ℕ → ℕ) → (ℕ → ℕ))
    (hg_cent : IsCentered g)
    (hg_omega : ContinuouslyReduces (OmegaFun g) f) :
    ∃ i : Fin (m + 1),
      ContinuouslyReduces (OmegaFun g) (f ∘ (Subtype.val : A i → ℕ → ℕ)) := by
  sorry

/-- **Lemma 5.11, Item 2.** If `λ` is limit and `k_λ ≤ f = ⊔ f_i`,
then `k_λ ≤ f_i` for some `i`. -/
theorem maxFun_limit_to_component
    (f : (ℕ → ℕ) → (ℕ → ℕ))
    (m : ℕ)
    (A : Fin (m + 1) → Set (ℕ → ℕ))
    (hA_clopen : ∀ i, IsClopen (A i))
    (hA_disj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hA_cover : ⋃ i, A i = Set.univ)
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam)
    -- k_λ ≤ f (there exists a function of CB-rank λ that reduces to f)
    (hmax : ∃ (h : (ℕ → ℕ) → (ℕ → ℕ)),
      CBRank h = lam ∧ ContinuouslyReduces h f) :
    ∃ i : Fin (m + 1),
      ∃ (h : (ℕ → ℕ) → (ℕ → ℕ)),
        CBRank h = lam ∧
        ContinuouslyReduces h (f ∘ (Subtype.val : A i → ℕ → ℕ)) := by
  sorry

/-!
## Section 2: Diagonal Lemma for λ+1 (Lemma 5.12)
-/

/-- **Lemma 5.12 (Diagonalforlambda+1).**
Suppose `f = ⊔_{n ∈ ℕ} f_n` for simple functions `f_n ∈ 𝒞_{λ+1}`
with pairwise distinct distinguished points `y_n`. Assume:
1. `f₀ ≡ pgl k_λ`
2. `f_n ≤ ℓ_{λ+1} ⊔ k_λ` for `n > 0`
3. `(y_n)_{n>0}` converges to `y₀`

Then for all clopen `U ∋ y₀`:
`f ≤ ⋁(k_λ | ℓ_{λ+1}) ≤ f↾U`. -/
theorem diagonal_for_lambda_plus_one
    (lam : Ordinal.{0}) (hlam : lam = 1 ∨ Order.IsSuccLimit lam)
    (f : ℕ → ((ℕ → ℕ) → (ℕ → ℕ)))
    -- f_n are simple of CB-rank λ+1
    (hsimp : ∀ n, SimpleFun (f n))
    (hcb : ∀ n, CBRank (f n) = lam + 1)
    -- distinguished points y_n (pairwise distinct, converging)
    (y : ℕ → (ℕ → ℕ))
    (hy_dist : ∀ i j, i ≠ j → y i ≠ y j)
    -- Condition 1: f₀ ≡ pgl k_λ (f₀ is centered)
    (hf0_centered : IsCentered (f 0))
    -- Condition 2: f_n ≤ ℓ_{λ+1} ⊔ k_λ for n > 0
    (hfn : ∀ n, 0 < n → InCBLevelLE (f n) (lam + 1))
    -- Condition 3: (y_n)_{n>0} converges to y₀
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0))) :
    -- Conclusion: f ≤ ⋁(k_λ | ℓ_{λ+1})
    -- and for all clopen U ∋ y₀, ⋁(k_λ | ℓ_{λ+1}) ≤ f↾U
    ∃ (f_v : Fin 1 → ((ℕ → ℕ) → (ℕ → ℕ)))
      (f_d : (ℕ → ℕ) → (ℕ → ℕ)),
      CBRank (f_v 0) = lam ∧
      CBRank f_d = lam + 1 ∧
      -- The overall gluing reduces to the wedge
      ContinuouslyReduces
        (fun x => prepend (x 0) (f (x 0) (unprepend x)))
        (WedgeFun 0 f_v f_d) ∧
      -- The wedge reduces to corestrictions
      (∀ U : Set (ℕ → ℕ), IsClopen U → y 0 ∈ U →
        ContinuouslyReduces (WedgeFun 0 f_v f_d)
          (CoRestrict (fun x => prepend (x 0) (f (x 0) (unprepend x))) U)) := by
  sorry

/-!
## Section 2: Finite Generation at Successor of Limit (Theorem 5.13)
-/

/-- **Theorem 5.13 (FGatsuccessoroflimit).** Let `λ` be limit or `1`.
Suppose that continuous reducibility is BQO on `𝒞_{<λ}`.
Then `𝒞_{λ+1}` is generated by the finite set
`{k_λ, ℓ_{λ+1}, pgl k_λ, ω ℓ_{λ+1}, ⋁(k_λ | ℓ_{λ+1}), k_{λ+1}}`. -/
theorem FG_at_successor_of_limit
    (lam : Ordinal.{0}) (hlam : lam = 1 ∨ Order.IsSuccLimit lam)
    (hlam_lt : lam < omega1)
    -- BQO on 𝒞_{<λ}
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
        [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
        (seq : ∀ n, X n → Y n),
        (∀ n, ScatteredFun (seq n)) →
        (∀ n, CBRank (seq n) < lam) →
        ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n)) :
    FiniteGeneration (lam + 1) := by
  sorry

/-!
## Section 3: Already Known Generators (Fact 5.16)
-/

/-- **Fact 5.16, Item 1 (AlreadyKnownGenerators).**
`𝒢(1) = {ℓ₁, ω ℓ₁}`: the generators at level 1 are exactly `ℓ₁` and `ω ℓ₁`. -/
theorem alreadyKnownGenerators_1 : FiniteGeneration 1 := by
  sorry

/-!
## Section 3: Properties of Generators (Proposition 5.17)
-/

/-- **Proposition 5.17, Item 3 (BasicsOnGenerators).**
The sets `𝒞(α)` and `𝒢(α)` are finite: there are only finitely many
continuous-equivalence classes of generators at any level. -/
theorem generators_finite
    (α : Ordinal.{0}) (hα : α < omega1) :
    ∃ N : ℕ,
      ∀ (gs : Fin N.succ → ((ℕ → ℕ) → (ℕ → ℕ))),
        (∀ i, InCBLevel (gs i) α) →
        ∃ i j, i ≠ j ∧ ContinuouslyEquiv (gs i) (gs j) := by
  sorry

/-!
## Section 3: The Precise Structure Theorem (Theorem 5.18)
-/

/-- **Theorem 5.18 (PreciseStructureThm) — The Precise Structure Theorem.**
For all `α < ω₁`, every function in `𝒞_α` is continuously equivalent to a finite
gluing of functions in `𝒢(α)`.

This is the main result of the chapter: the set `𝒞_α` of scattered continuous
functions of CB-rank `α` is finitely generated for every countable ordinal `α`. -/
theorem preciseStructureThm
    (α : Ordinal.{0}) (hα : α < omega1) :
    FiniteGeneration α := by
  sorry

/-!
## Section 3: FG Consequences (Proposition 5.20)
-/

/-- **Proposition 5.20, base cases (FGconsequences).**
`FG(0)`, `FG(1)`, and `FG(λ)` for every limit `λ`. -/
theorem FG_base_cases :
    FiniteGeneration 0 ∧
    FiniteGeneration 1 ∧
    (∀ (lam : Ordinal.{0}), Order.IsSuccLimit lam → lam < omega1 →
      FiniteGeneration lam) := by
  sorry

/-- **Proposition 5.20, Item 1 (FGconsequences).**
`FG(< λ)` implies `FG(λ + 1)` for `λ` limit. -/
theorem FG_implies_FG_succ_limit
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam)
    (hlam_lt : lam < omega1)
    (hFG : FiniteGeneration_below lam) :
    FiniteGeneration (lam + 1) := by
  sorry

/-- **Proposition 5.20, Item 2 (FGconsequences).**
`FG(≤ α)` implies that every function in `𝒞_{[λ, α]}` is a finite gluing of
generators in `𝒢(α)`. -/
theorem FG_le_implies_interval_gen
    (lam : Ordinal.{0}) (n : ℕ)
    (hlam : lam = 0 ∨ Order.IsSuccLimit lam)
    (hlam_lt : lam + ↑n < omega1)
    (hFG : FiniteGeneration_le (lam + ↑n))
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y)
    (hf : InCBLevelInterval f lam (lam + ↑n)) :
    ∃ (m : ℕ) (gs : Fin m → ((ℕ → ℕ) → (ℕ → ℕ))),
      (∀ i, InCBLevelInterval (gs i) lam (lam + ↑n)) ∧
      ContinuouslyEquiv f
        (fun x => prepend (x 0)
          (if h : x 0 < m then gs ⟨x 0, h⟩ (unprepend x) else unprepend x)) := by
  sorry

/-- **Proposition 5.20, Item 3 (FGconsequences).**
`FG(< α)` implies that continuous reducibility is a BQO on `𝒞_{< α}`. -/
theorem FG_below_implies_bqo
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_below α) :
    ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n) := by
  sorry

/-- **Proposition 5.20, Item 4 (FGconsequences).**
If `FG(< α)` holds, then every function in `𝒞_α` is locally centered. -/
theorem FG_below_implies_locally_centered
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : FiniteGeneration_below α)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : InCBLevel f α) :
    IsLocallyCentered f := by
  sorry

/-- **Proposition 5.20, Item 5 (FGconsequences).**
If `FG(< α)` holds, then every centered function in `𝒞_{[λ, α]}` is equivalent
to some centered generator in `𝒞(α)`. -/
theorem FG_below_centered_classification
    (α : Ordinal.{0}) (hα : α < omega1)
    (lam : Ordinal.{0}) (n : ℕ) (hn : 0 < n)
    (hα_eq : α = lam + ↑n)
    (hlam : lam = 0 ∨ Order.IsSuccLimit lam)
    (hFG : FiniteGeneration_below α)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y)
    (hf : InCBLevelInterval f lam α)
    (hf_cent : IsCentered f) :
    -- f is equivalent to some centered generator
    ∃ (g : (ℕ → ℕ) → (ℕ → ℕ)),
      IsCentered g ∧
      InCBLevelInterval g lam α ∧
      ContinuouslyEquiv f g := by
  sorry

end
