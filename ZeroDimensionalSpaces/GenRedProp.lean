import ZeroDimensionalSpaces.Basics

open scoped Topology
open Set Function TopologicalSpace

/-!
# Baire open reduction (relative version)

We prove that for any subspace `A` of the Baire space `ℕ → ℕ`,
any countable family of open sets `U n` in `A` can be "reduced" to
a pairwise-disjoint family of open sets `V n` with `V n ⊆ U n`
and `⋃ V n = ⋃ U n`.

The proof goes through a clopen decomposition in the zero-dimensional Baire space.
-/

section MainTheorem

theorem baire_open_reduction_rel
    (A : Set Baire) (U : ℕ → Set A) (hU_open : ∀ n, IsOpen (U n)) :
    ∃ V : ℕ → Set A,
      (∀ n, IsOpen (V n)) ∧ (∀ n, V n ⊆ U n) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ (⋃ n, V n = ⋃ n, U n) := by
  obtain ⟨C, hC_clopen, hC_union⟩ : ∃ C : ℕ → ℕ → Set A,
      (∀ n k, IsClopen (C n k)) ∧ (∀ n, U n = ⋃ k, C n k) := by
    choose C hC using fun n => subspace_open_eq_countable_union_clopen A (hU_open n)
    exact ⟨C, fun n k => (hC n).1 k, fun n => (hC n).2⟩
  let C_flat : ℕ → Set A := fun m => C (Nat.unpair m).1 (Nat.unpair m).2
  let D := disjointed C_flat
  let V : ℕ → Set A := fun n => ⋃ (m : ℕ) (_ : (Nat.unpair m).1 = n), D m
  refine ⟨V, fun n => isOpen_iUnion fun m => isOpen_iUnion fun _ =>
      (disjointed_clopen C_flat (fun m => hC_clopen _ _) m).2, fun n x hx => ?_,
    fun i j hij => ?_, ?_⟩
  · obtain ⟨m, hm, hxD⟩ := Set.mem_iUnion₂.mp hx
    have hxC := disjointed_subset _ _ hxD
    rw [hC_union n]; simp only [C_flat] at hxC; rw [hm] at hxC
    exact Set.mem_iUnion.mpr ⟨_, hxC⟩
  · exact Set.disjoint_iUnion₂_left.mpr fun mi hmi =>
      Set.disjoint_iUnion₂_right.mpr fun mj hmj =>
        disjoint_disjointed C_flat fun h => hij (hmi ▸ hmj ▸ congrArg _ (congrArg _ h))
  · have h_union_D : ⋃ m, D m = ⋃ n, U n := by
      rw [iUnion_disjointed]
      ext x; simp [C_flat, hC_union]
      exact ⟨fun ⟨m, hm⟩ => ⟨_, _, hm⟩, fun ⟨n, k, hk⟩ => ⟨Nat.pair n k, by simpa using hk⟩⟩
    convert h_union_D using 1; ext x; simp [V]

/-- **Clopen-partition refinement of a countable open cover** (the partition form of the
generalized reduction property, Kechris 22.16).  If the open sets `U n` *cover* the subspace
`A ⊆ Baire`, the reduced family `V n ⊆ U n` is a clopen partition of `A`: it is disjoint and
covering by `baire_open_reduction_rel`, and each `V n` is then also closed because its
complement is the (open) union of the other blocks. -/
theorem baire_clopen_partition_refines_cover
    (A : Set Baire) (U : ℕ → Set A) (hU_open : ∀ n, IsOpen (U n))
    (hcover : ⋃ n, U n = Set.univ) :
    ∃ V : ℕ → Set A,
      (∀ n, IsClopen (V n)) ∧ (∀ n, V n ⊆ U n) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ (⋃ n, V n = Set.univ) := by
  obtain ⟨V, hV_open, hV_sub, hV_disj, hV_union⟩ := baire_open_reduction_rel A U hU_open
  have hV_cover : ⋃ n, V n = Set.univ := hV_union.trans hcover
  refine ⟨V, fun n => ⟨?_, hV_open n⟩, hV_sub, hV_disj, hV_cover⟩
  -- `V n` is closed: its complement is `⋃ m ≠ n, V m`, an open set.
  have hcompl : (V n)ᶜ = ⋃ (m : ℕ) (_ : m ≠ n), V m := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      have hxu : x ∈ ⋃ m, V m := hV_cover ▸ Set.mem_univ x
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxu
      exact ⟨m, fun h => hx (h ▸ hm), hm⟩
    · rintro ⟨m, hmn, hm⟩ hx
      exact Set.disjoint_left.mp (hV_disj m n hmn) hm hx
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion fun m => isOpen_iUnion fun _ => hV_open m

/-- **Pointed clopen-partition refinement.**  Strengthens `baire_clopen_partition_refines_cover`
to keep a designated clopen "core" `B n ⊆ U n` inside the `n`-th block, *provided* the cores form
a disjoint clopen family with clopen union.

This hypothesis is necessary: without separation the pointed refinement is false (e.g. cover
`{X, {1/n}}` of `{0}∪{1/n}` with cores at `0` and each `1/n` — any clopen block around `0`
swallows a tail of the `1/n`).  When the cores ARE separated, refine the cover normally to a
partition `W`, then graft the cores back on the clopen complement `L = (⋃ B)ᶜ`:
`V n = (W n ∩ L) ∪ B n`.

Used to turn a *locally centered* function into a *disjoint union of centered* blocks: take
`U n` the centered neighbourhoods, `B n` disjoint clopen neighbourhoods of their centers; then
each block `V n ⊇ B n` contains a center, so `G|_{V n}` is centered (`isCenterFor_restrict`). -/
theorem baire_clopen_partition_pointed
    (A : Set Baire) (U : ℕ → Set A) (hU_open : ∀ n, IsOpen (U n))
    (hcover : ⋃ n, U n = Set.univ)
    (B : ℕ → Set A) (hB_clopen : ∀ n, IsClopen (B n)) (hBU : ∀ n, B n ⊆ U n)
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) (hB_union : IsClopen (⋃ n, B n)) :
    ∃ V : ℕ → Set A,
      (∀ n, IsClopen (V n)) ∧ (∀ n, V n ⊆ U n) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ (⋃ n, V n = Set.univ) ∧ (∀ n, B n ⊆ V n) := by
  obtain ⟨W, hW_clopen, hW_sub, hW_disj, hW_union⟩ :=
    baire_clopen_partition_refines_cover A U hU_open hcover
  set L : Set A := (⋃ n, B n)ᶜ with hL
  have hL_clopen : IsClopen L := hB_union.compl
  have hB_in : ∀ {n} {a : A}, a ∈ B n → a ∈ ⋃ k, B k := fun {n a} h => Set.mem_iUnion.mpr ⟨n, h⟩
  refine ⟨fun n => (W n ∩ L) ∪ B n, fun n => ((hW_clopen n).inter hL_clopen).union (hB_clopen n),
    fun n => Set.union_subset (Set.inter_subset_left.trans (hW_sub n)) (hBU n), ?_, ?_,
    fun n => Set.subset_union_right⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro a (⟨haW, haL⟩ | haB) (⟨haW', haL'⟩ | haB')
    · exact Set.disjoint_left.mp (hW_disj i j hij) haW haW'
    · exact haL (hB_in haB')
    · exact haL' (hB_in haB)
    · exact Set.disjoint_left.mp (hB_disj i j hij) haB haB'
  · rw [Set.eq_univ_iff_forall]
    intro a
    by_cases ha : a ∈ ⋃ k, B k
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨n, Or.inr hn⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hW_union ▸ Set.mem_univ a)
      exact Set.mem_iUnion.mpr ⟨n, Or.inl ⟨hn, ha⟩⟩

end MainTheorem
