import WqoContinuousFunctions.ContinuousReducibility.Scattered.NonScattered
import WqoContinuousFunctions.ContinuousReducibility.Gluing
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import ZeroDimensionalSpaces.Basics

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Simple Functions and Decomposition Lemma

## Main definitions

* `SimpleFun` — a function is simple if it constant on the last nonempty CB level

## Main results

* `decomposition_lemma_baire` — Lemma 2.15

The First Reduction Theorem (Theorem 2.12, `first_reduction_theorem`) lives in
`MainResults/Main.lean`: it is informative but off the critical path for the WQO program.
-/

section SimpleFunctions

/-- A function is simple if it has CB-degree 1: there is a last nonempty CB-level,
on which `f` is constant.  (Scatteredness is automatic, since `CBLevel f (succ α) = ∅`
already forces the perfect kernel to be empty — see `scatteredFun_of_CBLevel_empty`.) -/
def SimpleFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∃ α : Ordinal,
    (CBLevel f α).Nonempty ∧
    CBLevel f (Order.succ α) = ∅ ∧
    ∃ y, ∀ x ∈ CBLevel f α, f x = y

end SimpleFunctions

section ZeroDimAndDisjointUnion

/-!
## Proposition 2.14 (0dimanddisjointunion)

Let `f` be a function with separable metrizable 0-dimensional domain and `F` a class
of functions. Then `f` is locally `F` if and only if `f = ⨆ᵢ fᵢ` for some sequence of
functions `(fᵢ) ⊆ F`.

**Locally F** means: for every `x ∈ dom(f)`, there exists a clopen neighborhood `C ∋ x`
such that `f|_C ∈ F`.
-/

/-- A function `f : X → Y` is *locally in class `F`* if every point of `X` has a
clopen neighborhood on which `f` restricted is in `F`.
Here `F` is a predicate on functions from subtypes of `X` to `Y`. -/
def IsLocallyInClass {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (F : (S : Set X) → (S → Y) → Prop) : Prop :=
  ∀ x : X, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ F C (fun a => f a.val)

/-!
### Proposition 2.14 (0dimanddisjointunion)

For a function `f` with domain a subspace of the Baire space and `F` a class of
functions, `f` is locally `F` if and only if `f` is a disjoint union of functions
in `F` over a clopen partition.

The forward direction is the interesting one: in a 0-dimensional separable metrizable
space, every open cover can be refined to a clopen partition, using the tree structure
of the Baire space. The backward direction is trivial since each piece of a clopen
partition is itself clopen.
-/

theorem locally_implies_disjoint_union_baire
    {A : Set Baire}
    (f : A → Baire)
    (F : (S : Set A) → (S → Baire) → Prop)
    (hloc : IsLocallyInClass f F)
    (hF_restrict : ∀ (C D : Set A), D ⊆ C → IsClopen D →
      F C (fun a => f a.val) → F D (fun a => f a.val)) :
    ∃ (I : Type) (P : I → Set A) (fi : ∀ i, P i → Baire),
      IsDisjointUnion f P fi ∧ ∀ i, F (P i) (fi i) := by
  choose C hC hc using hloc
  -- use Lindelof property to get a countable subcover
  obtain ⟨I, hI⟩ : ∃ I : Set A, Set.Countable I ∧ ⋃ x ∈ I, C x = Set.univ := by
    have h_countable_subcover : IsLindelof (Set.univ : Set A) := by
      exact isLindelof_univ
    have := h_countable_subcover.elim_countable_subcover (fun x => C x)
    exact Exists.elim (this (fun x => (hC x).isOpen) (fun x _ => Set.mem_iUnion_of_mem x (hc x |>.1))) fun r hr => ⟨r, hr.1, Set.Subset.antisymm (Set.subset_univ _) hr.2⟩
  have := hI.1.exists_eq_range
  by_cases hI_empty : I.Nonempty
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → A, I = Set.range g := by
      exact this hI_empty
    refine ⟨ℕ, fun n => disjointed (fun n => C (g n)) n, fun n => fun a => f a.val, ?_, ?_⟩ <;> simp_all +decide [IsDisjointUnion]
    · refine ⟨?_, ?_, ?_⟩
      · exact fun i => disjointed_clopen (fun n => C (g n)) (fun n => hC (↑(g n)) (g n).property) i
      · exact fun i j hij => disjoint_disjointed _ hij
      · convert hI.2 using 1
        exact iUnion_disjointed
    · intro n
      apply hF_restrict
      exact disjointed_subset _ _
      · exact disjointed_clopen _ (fun n => hC _ _) _
      · exact hc _ _ |>.2
  · simp_all +decide [Set.not_nonempty_iff_eq_empty.mp hI_empty]
    simp_all +decide [IsDisjointUnion]
    exact ⟨PEmpty, fun _ => ∅, by aesop⟩

end ZeroDimAndDisjointUnion

/-- `≤` direction of `cb_rank_of_clopen_union`: the supremum of the restriction ranks bounds
`CBRank f`, because at that supremum every restriction's CB level is already empty, hence so is
`f`'s (an open cover with each piece exhausted is exhausted). -/
private lemma cb_rank_of_clopen_union_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (A : ℕ → Set X)
    (h_cover : ∀ x, ∃ n, x ∈ A n) (h_open : ∀ i, IsOpen (A i)) :
    CBRank f ≤ ⨆ i, CBRank (fun (x : A i) => f x.val) := by
  set α := ⨆ i, CBRank (fun (x : A i) => f x.val) with hα_def
  rw [CBRank_eq_sInf_empty f hf]
  apply csInf_le'
  simp only [Set.mem_setOf_eq]
  have h_all_empty : ∀ i, CBLevel (fun x : A i => f x.val) α = ∅ := by
    intro i
    obtain h_Ai_open : IsOpen (A i) := h_open i
    have h_CBf_empty : CBLevel f (CBRank f) = ∅ := CBLevel_eq_empty_at_rank f hf
    obtain h_iff := CBLevel_open_restrict f _ h_Ai_open (CBRank f)
    have hfi_scat : ScatteredFun (fun x : A i => f x.val) := scattered_restrict f hf (A i)
    have hfi_at_rank :
        CBLevel (fun (x : A i) => f x.val) (CBRank (fun (x : A i) => f x.val)) = ∅ :=
      CBLevel_eq_empty_at_rank (fun (x : A i) => f x.val) hfi_scat
    have h_le : CBRank (fun (x : A i) => f x.val) ≤ α := by
      rw [hα_def]
      exact Ordinal.le_iSup (fun j => CBRank (fun x : A j => f x.val)) i
    exact Set.eq_empty_of_subset_empty
      (hfi_at_rank ▸ CBLevel_antitone (fun (x : A i) => f x.val) h_le)
  apply CBLevel_open_union_empty f A h_open h_cover α h_all_empty

/-- `≥` direction of `cb_rank_of_clopen_union`: each restriction rank is `≤ CBRank f`, since if
some restriction had a strictly larger rank its CB level at `CBRank f` would be nonempty, yet it
equals `CBLevel f (CBRank f) = ∅` restricted to `A i`. -/
private lemma cb_rank_of_clopen_union_ge {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (A : ℕ → Set X) (h_open : ∀ i, IsOpen (A i)) :
    (⨆ i, CBRank (fun (x : A i) => f x.val)) ≤ CBRank f := by
  apply Ordinal.iSup_le
  intro i
  by_contra h
  push_neg at h
  have hfi_scat : ScatteredFun (fun x : A i => f x.val) := scattered_restrict f hf (A i)
  have hne : (CBLevel (fun x : A i => f x.val) (CBRank f)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hle : CBRank (fun x : A i => f x.val) ≤ CBRank f := by
      rw [CBRank_eq_sInf_empty _ hfi_scat]
      apply csInf_le'
      simp only [Set.mem_setOf_eq]
      exact hemp
    exact absurd hle (not_le.mpr h)
  have h_CBf_empty : CBLevel f (CBRank f) = ∅ := CBLevel_eq_empty_at_rank f hf
  have hempty : CBLevel (fun x : A i => f x.val) (CBRank f) = ∅ := by
    have h_openi : IsOpen (A i) := h_open i
    obtain h_iff := CBLevel_open_restrict f _ h_openi (CBRank f)
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hxX : x.val ∈ CBLevel f (CBRank f) := (h_iff x).mp hx
    rw [h_CBf_empty] at hxX
    exact hxX
  exact hne.ne_empty hempty

/-- Corollary \label{CBrankofclopenunion}
Let $f$ be a scattered function and $(A_i)_{i\in I}$ be an open covering of $\dom(f)$ for some set $I$.
Then $\CB(f)=\sup_{i\in I}\CB(f\restr{A_i})$.
-/
theorem cb_rank_of_clopen_union {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

    (f : X → Y) (hf : ScatteredFun f) (A : ℕ → Set X)
    (h_cover : ∀ x, ∃ n, x ∈  A n)
    (h_open : ∀ i, IsOpen (A i)) :
    CBRank f = ⨆ i, CBRank (fun (x : A i) => f x.val) :=
  le_antisymm (cb_rank_of_clopen_union_le f hf A h_cover h_open)
    (cb_rank_of_clopen_union_ge f hf A h_open)

section DecompositionLemma

/-!
## Lemma 2.15 (DecompositionLemma)

Any scattered function from a zero-dimensional separable metrizable space is locally
simple.

The proof requires several ingredients:
1. **Clopen basis**: In a metrizable totally disconnected space, every open set
   containing a point has a clopen subset containing that point. This is de Groot's
   theorem: metrizable + totally disconnected → ultra-metrizable, and in an
   ultrametric space, all balls are clopen.
2. **CB analysis of restrictions**: The CB levels of a restriction relate to the
   CB levels of the original function.
3. **Local simplicity**: Using the CB rank of each point and the clopen basis,
   we find a clopen neighborhood on which the function is simple.
-/

lemma cb_stabilizing_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (_hf : ScatteredFun f) :
    {α : Ordinal | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  -- By definition of scattered, the CB level at sometimes stabilizes.
  have hCBStabilize : ∃ α, CBLevel f α = CBLevel f (Order.succ α) := by
    by_contra h
    push_neg at h
    --clauses t, 3, 0
    exact absurd (CBLevel_strictAnti_of_ne f h) (by rintro ⟨g, hg⟩ ; exact not_injective_of_ordinal g hg)
  exact hCBStabilize

/--
For a scattered function, the CB level at CBRank is empty.
-/
lemma cbLevel_at_cbRank_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) :
    CBLevel f (CBRank f) = ∅ := by
  by_cases h_empty : (CBLevel f (CBRank f)).Nonempty
  · have h_eq : CBLevel f (CBRank f) = CBLevel f (Order.succ (CBRank f)) := by
      exact csInf_mem (cb_stabilizing_set_nonempty f hf)
    exact absurd h_eq (ne_of_gt (CBLevel_succ_ssubset_of_scattered f hf _ h_empty))
  · exact Set.not_nonempty_iff_eq_empty.mp h_empty

lemma isolatedLocus_gives_simple_neighborhood {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (β : Ordinal)
    (x : X)
    (hx : x ∈ isolatedLocus f (CBLevel f β)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      CBLevel f (Order.succ β) ∩ U = ∅ ∧
      ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
  obtain ⟨U, hU_open, hx_in_U, hconst⟩ : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ (CBLevel f β), f y = f x := by
    exact hx.2
  refine ⟨U, hU_open, hx_in_U, ?_, hconst⟩
  simp_all +decide [Set.ext_iff, CBLevel_succ']
  intro y hy hy' hy''; contrapose! hy'; unfold isolatedLocus at *; aesop

/--
Key lemma for decomposition: the restriction of f to a Baire-clopen set
    contained in the isolated locus neighborhood is simple.
-/
lemma restriction_to_clopen_is_simple
    {A : Set Baire}
    (f : A → Baire)
    (_ : ScatteredFun f)
    (β : Ordinal)
    (V : Set Baire)
    (hV : IsClopen V)
    (hx_exists : ∃ x : A, (x : Baire) ∈ V ∧ x ∈ CBLevel f β)
    (hempty : CBLevel f (Order.succ β) ∩ (Subtype.val ⁻¹' V : Set A) = ∅)
    (hconst : ∃ y : Baire, ∀ z ∈ (Subtype.val ⁻¹' V : Set A) ∩ CBLevel f β, f z = y) :
    SimpleFun (f ∘ (Subtype.val : {a : A | (a : Baire) ∈ V} → A)) := by
  refine ⟨β, ?_, ?_, ?_⟩
  · obtain ⟨x, hx₁, hx₂⟩ := hx_exists; use ⟨x, hx₁⟩ ; simp_all +decide
    have h_local : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) β = (CBLevel f β) ∩ Subtype.val ⁻¹' V := by
      convert local_cb_derivative (Subtype.val ⁻¹' V) (hV.2.preimage (continuous_subtype_val)) β using 1
      exact Pi.topologicalSpace
    exact h_local.symm.subset ⟨hx₂, hx₁⟩ |> fun ⟨y, hy₁, hy₂⟩ => hy₂ ▸ hy₁
  · have h_local_cb_derivative : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) (Order.succ β) = CBLevel f (Order.succ β) ∩ Subtype.val ⁻¹' V := by
      apply local_cb_derivative
      exact hV.isOpen.preimage continuous_subtype_val
    aesop
  · use hconst.choose
    intro x hx
    apply hconst.choose_spec
    exact ⟨x.2, local_cb_derivative _ (show IsOpen (Subtype.val ⁻¹' V) from hV.isOpen.preimage continuous_subtype_val) _ |>.subset (Set.mem_image_of_mem _ hx) |> fun h => h.1⟩

/-
**Decomposition Lemma.** Any scattered function `f : A → Baire`
with `A ⊆ Baire` is locally simple: around each point of `A` there is a clopen
neighborhood (in the Baire space) on which `f` is simple.
-/
theorem decomposition_lemma_baire
    (A : Set Baire)
    (f : A → Baire)
    (hf : ScatteredFun f) :
    ∀ x : A, ∃ U : Set Baire, IsClopen U ∧ (x : Baire) ∈ U ∧
         SimpleFun ((f ∘ (Subtype.val : {a : A | (a : Baire) ∈ U} → A)))
     := by
  -- proof differ from the mmemoir. It relies on the exit ordinal for each point in the domain.
  intros x
  obtain ⟨β, hβ⟩ : ∃ β : Ordinal, x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
    have h_empty : CBLevel f (CBRank f) = ∅ := by
      -- Apply the lemma that states the CBLevel at the CB rank is empty.
      apply cbLevel_at_cbRank_empty; assumption
    have h_exists_beta : ∃ β : Ordinal, x ∉ CBLevel f β := by
      exact ⟨_, fun hx => h_empty.subset hx⟩
    exact exit_ordinal_is_successor x _ h_exists_beta.choose_spec |> fun ⟨β, hβ₁, hβ₂, hβ₃⟩ => ⟨β, hβ₂, hβ₃⟩
  obtain ⟨U, hU_open, hxU, hU_empty, hU_const⟩ : ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ ∧ ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
    apply isolatedLocus_gives_simple_neighborhood
    exact Classical.not_not.1 fun h => hβ.2 <| by rw [CBLevel_succ'] ; exact ⟨hβ.1, h⟩
  obtain ⟨V, hV_clopen, hxV, hV_subset⟩ : ∃ V : Set Baire, IsClopen V ∧ x.val ∈ V ∧ Subtype.val ⁻¹' V ⊆ U := by
    obtain ⟨W, hW_open, hxW, hW_subset⟩ : ∃ W : Set Baire, IsOpen W ∧ x.val ∈ W ∧ Subtype.val ⁻¹' W ⊆ U := by
      rcases hU_open with ⟨W, hW_open, rfl⟩ ; use W; aesop
    exact Exists.elim (baire_exists_clopen_subset_of_open x.val W hW_open hxW) fun V hV => ⟨V, hV.1, hV.2.1, Set.Subset.trans (Set.preimage_mono hV.2.2) hW_subset⟩
  refine ⟨V, hV_clopen, hxV, ?_⟩
  apply restriction_to_clopen_is_simple f hf β V hV_clopen ⟨x, hxV, hβ.left⟩ (by
  exact Set.eq_empty_of_forall_notMem fun y hy => hU_empty.subset ⟨hy.1, hV_subset hy.2⟩) (by
  exact ⟨f x, fun z hz => hU_const z ⟨hV_subset hz.1, hz.2⟩⟩)

end DecompositionLemma
