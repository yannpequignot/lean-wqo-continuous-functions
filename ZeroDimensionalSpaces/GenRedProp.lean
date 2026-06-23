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

end MainTheorem
