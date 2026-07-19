import Mathlib.Tactic
import Mathlib.Topology.Clopen

open scoped Topology
open Set Function

set_option autoImplicit false

/-!
# Set algebra for countable clopen partitions

General topology facts about countable clopen partitions `(A i)` of a space `X` and
sub-pieces `D i ⊆ A i`, used by the diagonal argument in
`CenteredFunctions/DiagonalForLambdaPlusOne.lean` but not specific to `ScatFun`.

## Main results

* `isClopen_iUnion_sub_partition` — a union of clopen sub-pieces of a clopen partition is
  clopen.
* `setdiff_iUnion_eq_iUnion_diff` — the complement of `⋃ E` inside a disjoint clopen cover
  `A` (with `E i ⊆ A i`) is the union of the block-complements `A i \ E i`.
-/

/-
**Union of subset-pieces of a clopen partition is clopen.**  If `(A i)` is a clopen cover
of `X` and `D i ⊆ A i` is clopen for each `i`, then `⋃ i, D i` is clopen (block-openness
prevents cross-block accumulation).
-/
lemma isClopen_iUnion_sub_partition {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (hA : ∀ i, IsClopen (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (D : ℕ → Set X) (hD : ∀ i, IsClopen (D i)) (hDA : ∀ i, D i ⊆ A i) :
    IsClopen (⋃ i, D i) := by
  refine ⟨ ?_, ?_ ⟩;
  · refine isClosed_of_closure_subset fun x hx => ?_;
    -- Since $x \in \overline{\bigcup_{i} D_i}$, there exists some $m$ such that $x \in A_m$.
    obtain ⟨m, hm⟩ : ∃ m, x ∈ A m := by
      simpa using Set.ext_iff.mp hcover x;
    -- Since $x \in \overline{\bigcup_{i} D_i}$ and $x \in A_m$, we have $x \in \overline{D_m}$.
    have hx_Dm : x ∈ closure (D m) := by
      rw [ mem_closure_iff_nhds ] at hx ⊢;
      intro t ht
      obtain ⟨y, hyt, hyD⟩ : ∃ y, y ∈ t ∧ y ∈ ⋃ i, D i ∧ y ∈ A m := by
        obtain ⟨ y, hyt, hyD ⟩ := hx ( t ∩ A m ) ( Filter.inter_mem ht ( hA m |>.isOpen.mem_nhds hm ) ) ; use y; aesop;
      obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp hyD.1; specialize hdisj m i; by_cases hi' : m = i <;> simp_all +decide [ Set.disjoint_left ] ;
      · exact ⟨ y, hyt, hi ⟩;
      · exact False.elim ( hdisj hyD.2 ( hDA i hi ) );
    exact Set.mem_iUnion.2 ⟨ m, by simpa [ hD m |> IsClopen.isClosed |> IsClosed.closure_eq ] using hx_Dm ⟩;
  · exact isOpen_iUnion fun i => ( hD i ).isOpen

/-
Set identity: the complement of `⋃ E` inside a disjoint clopen cover `A` (with `E i ⊆ A i`)
is the union of the block-complements `A i \ E i`.
-/
lemma setdiff_iUnion_eq_iUnion_diff {X : Type*} (A E : ℕ → Set X)
    (hcover : (⋃ i, A i) = Set.univ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hEA : ∀ i, E i ⊆ A i) :
    Set.univ \ (⋃ i, E i) = ⋃ i, (A i \ E i) := by
  simp_all +decide [ Set.ext_iff, Set.mem_iUnion ];
  exact fun x => ⟨ fun hx => by obtain ⟨ i, hi ⟩ := hcover x; exact ⟨ i, hi, hx i ⟩, fun hx => by obtain ⟨ i, hi, hx ⟩ := hx; exact fun j hj => Set.disjoint_left.mp ( hdisj i j ( by aesop ) ) hi ( hEA j hj ) ⟩
