import Mathlib.Tactic
import Mathlib.Topology.NatEmbedding
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Set.Card.Arithmetic

open scoped Topology
open Set Function TopologicalSpace Topology

set_option autoImplicit false

/-!
# Infinite discrete subspaces of metrizable spaces

General topology/combinatorics facts used in the development. These are independent of the
continuous-reducibility machinery, hence kept in a Mathlib-only file.

## Main results

* `exists_infinite_discrete_subspace` — **Fact 2.25 (`InfiniteEmbedOmega`)**: any infinite
  metrizable space contains a countably infinite discrete subspace.
* `exists_pairwise_disjoint_infinite_discrete_subspaces` — **Lemma `InfiniteEmbedOmegaStronger`**:
  given finitely many infinite subsets of a metrizable space, one can thin them to pairwise
  disjoint infinite subsets whose union is discrete.
-/

section InfiniteDiscreteSubspace

/-!
## Fact 2.25 (InfiniteEmbedOmega)

Any infinite metrizable space contains an infinite discrete subspace.
-/

/--
Any infinite metrizable space contains a countably infinite discrete subspace.
-/
theorem exists_infinite_discrete_subspace {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [Infinite X] :
    ∃ (S : Set X), S.Infinite ∧ DiscreteTopology S :=
  exists_infinite_discreteTopology X

/-- `Set`-level form of `exists_infinite_discrete_subspace`: any infinite subset `X` of a
metrizable space has an infinite subset `Y ⊆ X` that is discrete (in the subspace topology
inherited from the ambient space).

This is the workhorse used both for the base case and for the last coordinate in the inductive
step of `exists_pairwise_disjoint_infinite_discrete_subspaces`. -/
theorem exists_infinite_discrete_subset {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    {X : Set B} (hX : X.Infinite) :
    ∃ Y ⊆ X, Y.Infinite ∧ DiscreteTopology (Y : Set B) := by
  -- Work inside the subspace `↥X` (metrizable, infinite) and apply the space-level lemma.
  haveI : Infinite ↥X := infinite_coe_iff.mpr hX
  obtain ⟨S, hSinf, hSdisc⟩ := exists_infinite_discrete_subspace (X := ↥X)
  haveI : DiscreteTopology ↥S := hSdisc
  refine ⟨Subtype.val '' S, Subtype.coe_image_subset _ _, hSinf.image Subtype.val_injective.injOn, ?_⟩
  -- `Subtype.val '' S` is the range of the embedding `↥S → B`, so it is homeomorphic to `↥S`
  -- and hence discrete.
  have hemb : Topology.IsEmbedding
      ((Subtype.val : ↥X → B) ∘ (Subtype.val : ↥S → ↥X)) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hrange : Set.range ((Subtype.val : ↥X → B) ∘ (Subtype.val : ↥S → ↥X))
      = Subtype.val '' S := by
    rw [Set.range_comp, Subtype.range_coe]
  have hd : DiscreteTopology
      (↥(Set.range ((Subtype.val : ↥X → B) ∘ (Subtype.val : ↥S → ↥X)))) :=
    hemb.toHomeomorph.discreteTopology
  rwa [hrange] at hd

/-- Any infinite set splits into two disjoint infinite subsets whose union is the whole set. -/
theorem exists_infinite_split {α : Type*} {s : Set α} (h : s.Infinite) :
    ∃ t u : Set α, t ⊆ s ∧ u ⊆ s ∧ Disjoint t u ∧ t ∪ u = s ∧ t.Infinite ∧ u.Infinite := by
  obtain ⟨t, u, hunion, hdisj, hcard⟩ :=
    Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite h
  -- Equal cardinality transfers finiteness, so neither half can be finite (their union is infinite).
  have fin_of_card_eq : ∀ {a b : Set α}, a.Finite → Cardinal.mk a = Cardinal.mk b → b.Finite := by
    intro a b ha hab
    have hfa : Finite a := ha.to_subtype
    have hlt : Cardinal.mk a < Cardinal.aleph0 := Cardinal.lt_aleph0_iff_finite.mpr hfa
    rw [hab] at hlt
    exact Set.finite_coe_iff.mp (Cardinal.lt_aleph0_iff_finite.mp hlt)
  refine ⟨t, u, by rw [← hunion]; exact subset_union_left,
    by rw [← hunion]; exact subset_union_right, hdisj, hunion, ?_, ?_⟩
  · by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h (hunion ▸ hfin.union (fin_of_card_eq hfin hcard))
  · by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h (hunion ▸ (fin_of_card_eq hfin hcard.symm).union hfin)

/-- The conclusion of `exists_pairwise_disjoint_infinite_discrete_subspaces` is invariant under
permuting the index: solving the problem for the permuted family `fun i => X (σ i)` solves it for
`X`. Used to reduce the "infinite intersection" case to one where the pair involves `Fin.last`. -/
private theorem solve_of_perm {B : Type*} [TopologicalSpace B] {n : ℕ}
    (X : Fin (n + 1) → Set B) (σ : Equiv.Perm (Fin (n + 1)))
    (h : ∃ Y : Fin (n + 1) → Set B, (∀ i, Y i ⊆ X (σ i)) ∧ (∀ i, (Y i).Infinite) ∧
        Pairwise (Disjoint on Y) ∧ DiscreteTopology ↥(⋃ i, Y i)) :
    ∃ Y : Fin (n + 1) → Set B, (∀ i, Y i ⊆ X i) ∧ (∀ i, (Y i).Infinite) ∧
        Pairwise (Disjoint on Y) ∧ DiscreteTopology ↥(⋃ i, Y i) := by
  obtain ⟨Y, hsub, hinf, hdisj, hdisc⟩ := h
  refine ⟨fun i => Y (σ.symm i), fun i => ?_, fun i => hinf _, fun a b hab => ?_, ?_⟩
  · have := hsub (σ.symm i); rwa [Equiv.apply_symm_apply] at this
  · exact hdisj (σ.symm.injective.ne hab)
  · have huu : (⋃ i, Y (σ.symm i)) = ⋃ k, Y k := by
      apply subset_antisymm
      · exact iUnion_subset fun i => subset_iUnion Y (σ.symm i)
      · refine iUnion_subset fun k => ?_
        rw [show Y k = Y (σ.symm (σ k)) from by rw [Equiv.symm_apply_apply]]
        exact subset_iUnion (fun i => Y (σ.symm i)) (σ k)
    rw [huu]; exact hdisc

/-- Inductive step, "infinite intersection" case, reduced to the situation where the overlapping
pair is `(a.castSucc, last)`. We shrink coordinate `a` to its intersection with `last`, drop the
`last` coordinate to apply the induction hypothesis `ih`, then split the resulting `a`-block into
two infinite halves — one stays at `a`, the other becomes the new `last` block. Splitting a set
into two pieces does not change the union, so discreteness is inherited for free. -/
private theorem solve_pair_last {B : Type*} [TopologicalSpace B] [MetrizableSpace B] {n : ℕ}
    (F : Fin (n + 2) → Set B) (hFinf : ∀ k, (F k).Infinite)
    (ih : ∀ (Z : Fin (n + 1) → Set B), (∀ i, (Z i).Infinite) →
      ∃ Y : Fin (n + 1) → Set B, (∀ i, Y i ⊆ Z i) ∧ (∀ i, (Y i).Infinite) ∧
        Pairwise (Disjoint on Y) ∧ DiscreteTopology ↥(⋃ i, Y i))
    (a : Fin (n + 1))
    (hpair : (F a.castSucc ∩ F (Fin.last (n + 1))).Infinite) :
    ∃ Y : Fin (n + 2) → Set B, (∀ i, Y i ⊆ F i) ∧ (∀ i, (Y i).Infinite) ∧
      Pairwise (Disjoint on Y) ∧ DiscreteTopology ↥(⋃ i, Y i) := by
  classical
  -- Smaller family `Z` on `Fin (n+1)`: coordinate `a` shrunk to `F a.castSucc ∩ F last`, the rest
  -- inherited from the first `n+1` coordinates of `F`.
  set Z : Fin (n + 1) → Set B :=
    Function.update (fun k => F k.castSucc) a (F a.castSucc ∩ F (Fin.last (n + 1))) with hZdef
  have hZinf : ∀ k, (Z k).Infinite := by
    intro k
    rcases eq_or_ne k a with rfl | hk
    · rw [hZdef, Function.update_self]; exact hpair
    · rw [hZdef, Function.update_of_ne hk]; exact hFinf _
  obtain ⟨W, hWsub, hWinf, hWdisj, hWdisc⟩ := ih Z hZinf
  -- `W a ⊆ Z a = F a.castSucc ∩ F last`; split it into two infinite halves.
  obtain ⟨P, Q, hPW, hQW, hPQ, hPQunion, hPinf, hQinf⟩ := exists_infinite_split (hWinf a)
  have hWaZ : W a ⊆ F a.castSucc ∩ F (Fin.last (n + 1)) := by
    have := hWsub a; rwa [hZdef, Function.update_self] at this
  set Y : Fin (n + 2) → Set B := Fin.snoc (Function.update W a P) Q with hYdef
  -- Classify each `Y`-block: it is `P` (at `a.castSucc`), `Q` (at `last`), or some `W k` (`k ≠ a`).
  have key : ∀ x : Fin (n + 2),
      (Y x = P ∧ x = a.castSucc) ∨ (Y x = Q ∧ x = Fin.last (n + 1)) ∨
      (∃ k, k ≠ a ∧ Y x = W k ∧ x = k.castSucc) := by
    intro x
    induction x using Fin.lastCases with
    | last => exact Or.inr (Or.inl ⟨by rw [hYdef, Fin.snoc_last], rfl⟩)
    | cast k =>
      rcases eq_or_ne k a with rfl | hk
      · exact Or.inl ⟨by rw [hYdef, Fin.snoc_castSucc, Function.update_self], rfl⟩
      · exact Or.inr (Or.inr ⟨k, hk,
          by rw [hYdef, Fin.snoc_castSucc, Function.update_of_ne hk], rfl⟩)
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · -- `Y i ⊆ F i`
    intro x
    rcases key x with ⟨hYx, rfl⟩ | ⟨hYx, rfl⟩ | ⟨k, hk, hYx, rfl⟩
    · rw [hYx]; exact (hPW.trans hWaZ).trans Set.inter_subset_left
    · rw [hYx]; exact (hQW.trans hWaZ).trans Set.inter_subset_right
    · rw [hYx]; have := hWsub k; rwa [hZdef, Function.update_of_ne hk] at this
  · -- each `Y i` infinite
    intro x
    rcases key x with ⟨hYx, _⟩ | ⟨hYx, _⟩ | ⟨k, _, hYx, _⟩
    · rw [hYx]; exact hPinf
    · rw [hYx]; exact hQinf
    · rw [hYx]; exact hWinf k
  · -- pairwise disjoint
    intro x y hxy
    show Disjoint (Y x) (Y y)
    rcases key x with ⟨hYx, rfl⟩ | ⟨hYx, rfl⟩ | ⟨kx, hkx, hYx, rfl⟩
    · rcases key y with ⟨hYy, rfl⟩ | ⟨hYy, rfl⟩ | ⟨ky, hky, hYy, rfl⟩
      · exact absurd rfl hxy
      · rw [hYx, hYy]; exact hPQ
      · rw [hYx, hYy]; exact Disjoint.mono hPW le_rfl (hWdisj (Ne.symm hky))
    · rcases key y with ⟨hYy, rfl⟩ | ⟨hYy, rfl⟩ | ⟨ky, hky, hYy, rfl⟩
      · rw [hYx, hYy]; exact hPQ.symm
      · exact absurd rfl hxy
      · rw [hYx, hYy]; exact Disjoint.mono hQW le_rfl (hWdisj (Ne.symm hky))
    · rcases key y with ⟨hYy, rfl⟩ | ⟨hYy, rfl⟩ | ⟨ky, hky, hYy, rfl⟩
      · rw [hYx, hYy]; exact Disjoint.mono le_rfl hPW (hWdisj hkx)
      · rw [hYx, hYy]; exact Disjoint.mono le_rfl hQW (hWdisj hkx)
      · rw [hYx, hYy]; exact hWdisj (fun h => hxy (by rw [h]))
  · -- discrete union: `⋃ Y = ⋃ W` since splitting `W a` into `P, Q` leaves the union unchanged.
    have hueq : (⋃ i, Y i) = ⋃ k, W k := by
      apply subset_antisymm
      · refine iUnion_subset fun x => ?_
        rcases key x with ⟨hYx, _⟩ | ⟨hYx, _⟩ | ⟨k, _, hYx, _⟩
        · rw [hYx]; exact hPW.trans (subset_iUnion W a)
        · rw [hYx]; exact hQW.trans (subset_iUnion W a)
        · rw [hYx]; exact subset_iUnion W k
      · refine iUnion_subset fun k => ?_
        rcases eq_or_ne k a with rfl | hk
        · rw [← hPQunion]
          refine union_subset ?_ ?_
          · have e : Y k.castSucc = P := by rw [hYdef, Fin.snoc_castSucc, Function.update_self]
            rw [← e]; exact subset_iUnion Y k.castSucc
          · have e : Y (Fin.last (n + 1)) = Q := by rw [hYdef, Fin.snoc_last]
            rw [← e]; exact subset_iUnion Y (Fin.last (n + 1))
        · have e : Y k.castSucc = W k := by
            rw [hYdef, Fin.snoc_castSucc, Function.update_of_ne hk]
          rw [← e]; exact subset_iUnion Y k.castSucc
    rw [hueq]; exact hWdisc

/-
**Dichotomy / extraction lemma.** Any infinite subset `S` of a metrizable space has an infinite
subset `T ⊆ S` whose derived set (set of accumulation points) is finite.

Either `S` already has no accumulation point (then `T = S` works, with empty derived set), or there
is an accumulation point `z` of `S`; using first countability we extract a sequence in `S \ {z}`
converging to `z`, and the range `T` of that sequence is infinite with `{z}` its only possible
accumulation point.
-/
private theorem exists_infinite_subset_derivedSet_finite {B : Type*} [TopologicalSpace B]
    [MetrizableSpace B] {S : Set B} (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ (derivedSet T).Finite := by
  by_cases h_ac : ∃ z, AccPt z (Filter.principal S);
  · obtain ⟨ z, hz ⟩ := h_ac
    have h_seq : ∃ x : ℕ → B, (∀ n, x n ∈ S \ {z}) ∧ Filter.Tendsto x Filter.atTop (nhds z) := by
      obtain ⟨x, hx⟩ : ∃ x : ℕ → B, Filter.Tendsto x Filter.atTop (nhdsWithin z (S \ {z})) := by
        have h_seq : Filter.NeBot (nhdsWithin z (S \ {z})) := by
          simp_all +decide [ accPt_principal_iff_nhdsWithin ];
        exact Filter.exists_seq_tendsto (𝓝[S \ {z}] z)
      have := hx.eventually ( self_mem_nhdsWithin );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ fun n => x ( n + N ), fun n => hN _ ( by linarith ), hx.mono_left ( Filter.tendsto_add_atTop_nat _ ) |> fun h => h.mono_right inf_le_left ⟩ ;
    obtain ⟨ x, hx₁, hx₂ ⟩ := h_seq
    obtain ⟨ N, hN ⟩ : ∃ N, ∀ n ≥ N, x n ≠ z := by
      exact ⟨ 0, fun n _ => hx₁ n |>.2 ⟩
    set y : ℕ → B := fun n => x (N + n)
    have hy_ne_z : ∀ n, y n ≠ z := by
      exact fun n => hN _ ( Nat.le_add_right _ _ )
    have hy_tendsto : Filter.Tendsto y Filter.atTop (nhds z) := by
      exact hx₂.comp ( Filter.tendsto_atTop_mono ( fun n => Nat.le_add_left _ _ ) Filter.tendsto_id )
    have hy_subset : Set.range y ⊆ S := by
      exact Set.range_subset_iff.mpr fun n => hx₁ _ |>.1
    have hy_infinite : (Set.range y).Infinite := by
      by_contra hy_finite;
      simp_all +decide [ Set.not_infinite ];
      have := hy_finite.isClosed.mem_of_tendsto hy_tendsto ; aesop
    have hy_derived : (derivedSet (Set.range y)).Finite := by
      refine Set.Finite.subset ( Set.finite_singleton z ) ?_;
      intro w hw
      by_contra hw_ne_z
      have h_disjoint : ∃ U V : Set B, IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ w ∈ V ∧ Disjoint U V := by
        exact t2_separation fun a => hw_ne_z (id (Eq.symm a))
      obtain ⟨ U, V, hU, hV, hzU, hwV, hUV ⟩ := h_disjoint
      have h_finite : Set.Finite {n | y n ∈ V} := by
        have := hy_tendsto.eventually ( hU.mem_nhds hzU );
        exact Set.finite_iff_bddAbove.2 ( by rcases Filter.eventually_atTop.1 this with ⟨ n, hn ⟩ ; exact ⟨ n, fun m hm => not_lt.1 fun contra => hUV.le_bot ⟨ hn m contra.le, hm ⟩ ⟩ );
      have h_acc : AccPt w (Filter.principal (Set.range y ∩ V)) := by
        rw [ mem_derivedSet ] at hw;
        rw [ accPt_iff_frequently ] at *;
        rw [ Filter.frequently_iff ] at *;
        intro U hU; rcases hw ( Filter.inter_mem hU ( hV.mem_nhds hwV ) ) with ⟨ x, hx₁, hx₂, hx₃ ⟩ ; use x; aesop;
      have h_finite_range : Set.Finite (Set.range y ∩ V) := by
        exact Set.Finite.subset ( h_finite.image y ) fun x hx => by aesop;
      exact absurd ( Set.Infinite.of_accPt h_acc ) ( by simpa using h_finite_range )
    use Set.range y;
  · refine ⟨ S, Set.Subset.refl _, hS, ?_ ⟩;
    simp_all +decide [ derivedSet ]

/-
Inductive step, "all pairwise intersections finite" case.

Disjointify the `X i` (each loses only finitely much, so stays infinite) to get pairwise disjoint
infinite `S i ⊆ X i`. From each `S i` extract an infinite `T i` with finite derived set
(`exists_infinite_subset_derivedSet_finite`). The finite set `Z = ⋃ i, derivedSet (T i)` collects
all possible accumulation points; deleting it, `Y i = T i \ Z` stays infinite and the union
`⋃ i, Y i` has no accumulation point inside itself, hence is discrete.
-/
private theorem solve_disjoint_case {B : Type*} [TopologicalSpace B] [MetrizableSpace B] {n : ℕ}
    (X : Fin (n + 2) → Set B) (hX : ∀ i, (X i).Infinite)
    (hfin : ∀ i j, i ≠ j → (X i ∩ X j).Finite) :
    ∃ Y : Fin (n + 2) → Set B, (∀ i, Y i ⊆ X i) ∧ (∀ i, (Y i).Infinite) ∧
      Pairwise (Disjoint on Y) ∧ DiscreteTopology ↥(⋃ i, Y i) := by
  -- Define `S : Fin (n+2) → Set B := fun i => X i \ ⋃ (j) (_ : j ≠ i), X j`.
  set S : Fin (n + 2) → Set B := fun i => X i \ ⋃ (j) (_ : j ≠ i), X j;
  -- From each `S i` extract an infinite `T i` with finite derived set.
  obtain ⟨T, hT⟩ : ∃ T : Fin (n + 2) → Set B, (∀ i, T i ⊆ S i) ∧ (∀ i, (T i).Infinite) ∧ (∀ i, (derivedSet (T i)).Finite) := by
    have hT : ∀ i, ∃ T : Set B, T ⊆ S i ∧ (T).Infinite ∧ (derivedSet T).Finite := by
      intro i;
      convert exists_infinite_subset_derivedSet_finite _;
      · infer_instance;
      · exact Set.Infinite.diff ( hX i ) ( Set.Finite.biUnion ( Set.toFinite ( Finset.univ.erase i : Finset ( Fin ( n + 2 ) ) ) ) fun j hj => hfin i j ( by aesop ) ) |> Set.Infinite.mono fun x hx => by aesop;
    exact ⟨ fun i => Classical.choose ( hT i ), fun i => Classical.choose_spec ( hT i ) |>.1, fun i => Classical.choose_spec ( hT i ) |>.2.1, fun i => Classical.choose_spec ( hT i ) |>.2.2 ⟩;
  refine ⟨ fun i => T i \ ⋃ i, derivedSet ( T i ), ?_, ?_, ?_, ?_ ⟩;
  · exact fun i => fun x hx => hT.1 i hx.1 |>.1;
  · exact fun i => Set.Infinite.diff ( hT.2.1 i ) ( Set.finite_iUnion hT.2.2 );
  · intro i j hij; simp_all +decide [ Set.disjoint_left ] ;
    intro x hx₁ hx₂ hx₃; have := hT.1 i hx₁; have := hT.1 j hx₃; simp_all +decide [ Set.subset_def ] ;
    exact absurd ( hT.1 i x hx₁ |>.2 |> fun h => h <| Set.mem_iUnion₂.2 ⟨ j, by tauto, hT.1 j x hx₃ |>.1 ⟩ ) ( by tauto );
  · refine discreteTopology_of_noAccPts ?_;
    simp +decide only [mem_iUnion, mem_diff, mem_derivedSet, AccPt, not_exists, Filter.not_neBot, exists_and_right, and_imp, forall_exists_index];
    simp +decide only [Filter.inf_principal_eq_bot, compl_iUnion, Filter.iInter_mem];
    intro x i hx hi j; filter_upwards [ hi j ] with y hy; aesop;

/-- **Lemma `InfiniteEmbedOmegaStronger`.**

Generalization of `exists_infinite_discrete_subspace` to finitely many infinite subsets:
given infinite `X 0, …, X n` in a metrizable space `B`, there are pairwise disjoint infinite
`Y i ⊆ X i` whose union is discrete. (Indexed by `Fin (n+1)`, so `n = 0` is the single-set
base case `exists_infinite_discrete_subspace`.)

PROVIDED SOLUTION
We prove the statement by induction on `n`. If `n = 0`, this is simply `InfiniteEmbedOmega`
(`exists_infinite_discrete_subspace`). So assume it holds for all collections of size `n` and
let `X 0, …, X (n+1)` be infinite subsets of `B`. We distinguish two cases.

First case: there exist distinct `i, j ≤ n+1` such that `X i ∩ X j` is infinite. Reindexing if
necessary, assume `j = n+1` and define `X̃ i = X i ∩ X (n+1)` and `X̃ k = X k` otherwise. We can
apply the induction hypothesis to `X̃ 0, …, X̃ n` to obtain pairwise disjoint infinite sets
`Ỹ i ⊆ X̃ i`, for `i ≤ n`, whose union is discrete. To obtain the desired sets for the original
collection, it suffices to set `Y j = Ỹ j` for `j ≠ i` and further partition `Ỹ i` into two
infinite sets `Y i` and `Y (n+1)`.

Second case: for all `i, j ≤ n+1` the set `X i ∩ X j` is finite. We can make them disjoint: set
`X̃ i = X i \ ⋃_{j ≠ i} X j` for all `i ≤ n`. Apply the induction hypothesis to `X̃ i` for
`i ≤ n` to get infinite pairwise disjoint sets `Y i ⊆ X̃ i`, `i ≤ n`, with a discrete union. Now
pick a discrete `Y (n+1) ⊆ X̃ (n+1)` by `InfiniteEmbedOmega` and note that the sets `Y i` for
`i ≤ n+1` are infinite pairwise disjoint discrete sets. If `Y = ⋃_{i ≤ n+1} Y i` is discrete as
well, we are done. Otherwise, there exists `i ≤ n` such that either `Y i ∩ closure (Y (n+1)) ≠ ∅`
or `closure (Y i) ∩ Y (n+1) ≠ ∅`. Suppose that the former holds, choose `y ∈ Y i ∩ closure (Y (n+1))`
and an open neighborhood `V` of `y` such that `V ∩ Y i = {y}` (since `Y i` is discrete). Note that
`Y (n+1) ∩ V` is infinite and so we can shrink these two sets as follows: `Y (n+1) := Y (n+1) ∩ V`
and `Y i := Y i \ {y}`. Both `Y i` and `Y (n+1)` are infinite and now `Y i ∩ closure (Y (n+1)) = ∅`.
The latter case is similar and since `n` is finite, we can apply this procedure repeatedly until we
obtain the desired family `(Y i)_{i ≤ n+1}`.
-/
theorem exists_pairwise_disjoint_infinite_discrete_subspaces {B : Type*}
    [TopologicalSpace B] [MetrizableSpace B] {n : ℕ}
    (X : Fin (n + 1) → Set B) (hX : ∀ i, (X i).Infinite) :
    ∃ Y : Fin (n + 1) → Set B,
      (∀ i, Y i ⊆ X i) ∧ (∀ i, (Y i).Infinite) ∧
      Pairwise (Disjoint on Y) ∧ DiscreteTopology (↥(⋃ i, Y i)) := by
  -- Induction on `n`; `X` and `hX` are auto-generalized (they depend on `n`), so the induction
  -- hypothesis `ih` quantifies over all `Fin (n+1)`-indexed families.
  induction n with
  | zero =>
    -- Base case `n = 0`: a single infinite set `X 0`. `exists_infinite_discrete_subset` gives an
    -- infinite discrete `Y₀ ⊆ X 0`; take the constant family `Y _ := Y₀`. Disjointness is vacuous
    -- on `Fin 1` and the union `⋃ i, Y₀` collapses to `Y₀`.
    obtain ⟨Y₀, hsub, hinf, hdisc⟩ := exists_infinite_discrete_subset (hX 0)
    refine ⟨fun _ => Y₀, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i; exact hsub
    · intro _; exact hinf
    · intro i j hij; fin_cases i; fin_cases j; exact absurd rfl hij
    · rw [Set.iUnion_const]; exact hdisc
  | succ n ih =>
    -- `ih : ∀ X : Fin (n+1) → Set B, (∀ i, (X i).Infinite) → ∃ Y, …`.
    by_cases hpair : ∃ i j : Fin (n + 2), i ≠ j ∧ (X i ∩ X j).Infinite
    · -- First case: some pair `X i, X j` has infinite intersection.
      obtain ⟨i, j, hij, hXij⟩ := hpair
      -- Move `j` to the last coordinate via the swap permutation, then apply `solve_pair_last`.
      refine solve_of_perm X (Equiv.swap j (Fin.last (n + 1))) ?_
      set σ := Equiv.swap j (Fin.last (n + 1)) with hσ
      have hσσ : ∀ x, σ (σ x) = x := by intro x; rw [hσ]; exact Equiv.swap_apply_self _ _ x
      have hσlast : σ (Fin.last (n + 1)) = j := by rw [hσ]; exact Equiv.swap_apply_right _ _
      -- `σ i` is the position of the second set; it is not `last` (else `i = j`).
      have ha_ne : σ i ≠ Fin.last (n + 1) := by
        intro hc
        apply hij
        have h := congrArg σ hc
        rwa [hσσ, hσlast] at h
      have ha_cs : ((σ i).castPred ha_ne).castSucc = σ i := Fin.castSucc_castPred (σ i) ha_ne
      refine solve_pair_last (fun k => X (σ k)) (fun k => hX (σ k)) ih
        ((σ i).castPred ha_ne) ?_
      show (X (σ (((σ i).castPred ha_ne).castSucc)) ∩ X (σ (Fin.last (n + 1)))).Infinite
      rw [ha_cs, hσσ, hσlast]
      exact hXij
    · -- Second case: every pairwise intersection is finite. Hand off to `solve_disjoint_case`.
      have hfin : ∀ i j, i ≠ j → (X i ∩ X j).Finite := fun i j hij => by
        by_contra hinf; exact hpair ⟨i, j, hij, hinf⟩
      exact solve_disjoint_case X hX hfin

end InfiniteDiscreteSubspace