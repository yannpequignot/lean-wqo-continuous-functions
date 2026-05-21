import WqoContinuousFunctions.PointedGluing.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for pointedGluing_upper_bound (Proposition 3.5)
-/

lemma rayIdx_tendsto_atTop_of_converge
    {B : Set (ℕ → ℕ)} {y : ℕ → ℕ} {vals : ℕ → ℕ → ℕ} {j : ℕ → ℕ}
    (hvals_ray : ∀ n, vals n ∈ RaySet B y (j n))
    (hconv : Filter.Tendsto vals Filter.atTop (nhds y)) :
    Filter.Tendsto j Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun M => ?_
  have := hconv
  rw [tendsto_pi_nhds] at this
  simp_all +decide [RaySet]
  choose f hf using this
  exact ⟨Finset.sup (Finset.range (M + 1)) f, fun n hn => not_lt.1 fun contra => hvals_ray n |>.2.2 <| hf _ _ <| le_trans (Finset.le_sup (f := f) <| Finset.mem_range.mpr <| Nat.lt_succ_of_le contra.le) hn⟩

lemma disjoint_finset_member_tendsto_atTop
    {I : ℕ → Finset ℕ} (hI : ∀ m n, m ≠ n → Disjoint (I m) (I n))
    {j k : ℕ → ℕ}
    (hk : ∀ n, k n ∈ I (j n))
    (hj : Filter.Tendsto j Filter.atTop Filter.atTop) :
    Filter.Tendsto k Filter.atTop Filter.atTop := by
  have h_finite : ∀ M : ℕ, Set.Finite {n | k n ≤ M} := by
    intro M
    have h_finite : Set.Finite {j | ∃ k ∈ I j, k ≤ M} := by
      have h_finite : ∀ k ≤ M, {j : ℕ | k ∈ I j}.Finite := by
        intro k hk; exact Set.Subsingleton.finite (fun m hm n hn => Classical.not_not.1 fun hmn => Finset.disjoint_left.mp (hI m n hmn) hm hn)
      exact Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic M) fun k hk => h_finite k hk) fun x hx => by aesop
    have h_finite : Set.Finite {n | j n ∈ {j | ∃ k ∈ I j, k ≤ M}} := by
      exact Set.finite_iff_bddAbove.mpr (Filter.eventually_atTop.mp (hj.eventually (Filter.eventually_ge_atTop (h_finite.bddAbove.choose + 1))) |> fun ⟨N, hN⟩ ↦ ⟨N, fun n hn ↦ not_lt.mp fun contra ↦ not_lt_of_ge (h_finite.bddAbove.choose_spec hn) (by linarith [hN n contra.le])⟩)
    exact h_finite.subset fun n hn => ⟨k n, hk n, hn⟩
  exact Filter.tendsto_atTop_atTop.mpr fun M => by rcases Set.Finite.bddAbove (h_finite M) with ⟨N, hN⟩ ; exact ⟨N + 1, fun n hn => not_lt.1 fun contra => not_lt_of_ge (hN contra.le) hn⟩

lemma prependZerosOne_tendsto_zeroStream
    {k : ℕ → ℕ} (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (x : ℕ → ℕ → ℕ) :
    Filter.Tendsto (fun n => prependZerosOne (k n) (x n)) Filter.atTop (nhds zeroStream) := by
  rw [tendsto_pi_nhds]; intro m
  exact tendsto_const_nhds.congr' (by filter_upwards [hk.eventually_gt_atTop m] with n hn; unfold prependZerosOne; aesop)

lemma disjoint_finset_idx_tendsto_of_member_tendsto
    {I : ℕ → Finset ℕ} (_hI : ∀ m n, m ≠ n → Disjoint (I m) (I n))
    {j k : ℕ → ℕ}
    (hk_mem : ∀ n, k n ∈ I (j n))
    (hk_tendsto : Filter.Tendsto k Filter.atTop Filter.atTop) :
    Filter.Tendsto j Filter.atTop Filter.atTop := by
  have h_finite : ∀ m, Set.Finite {n | j n < m} := by
    intro m
    have h_bounded : ∃ M, ∀ n ∈ {n | j n < m}, k n ≤ M := by
      exact ⟨Finset.sup (Finset.biUnion (Finset.range m) fun i => I i) id, fun n hn => Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨j n, Finset.mem_range.mpr hn, hk_mem n⟩)⟩
    exact Set.finite_iff_bddAbove.mpr (Filter.eventually_atTop.mp (hk_tendsto.eventually_gt_atTop h_bounded.choose) |> fun ⟨N, hN⟩ => ⟨N, fun n hn => not_lt.1 fun contra => not_lt_of_ge (h_bounded.choose_spec n hn) (hN n contra.le)⟩)
  exact Filter.tendsto_atTop_atTop.mpr fun m => by rcases Set.Finite.bddAbove (h_finite m) with ⟨N, hN⟩ ; exact ⟨N + 1, fun n hn => not_lt.1 fun contra => not_lt_of_ge (hN contra) hn⟩

lemma finite_indices_with_small_members
    {I : ℕ → Finset ℕ} (hI : ∀ m n, m ≠ n → Disjoint (I m) (I n))
    (K : ℕ) : Set.Finite {j : ℕ | ∃ k ∈ I j, k ≤ K} := by
  by_contra h_inf
  obtain ⟨k, _, hk⟩ : ∃ k ≤ K, Set.Infinite {j | k ∈ I j} := by
    contrapose! h_inf
    exact Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic K) fun k hk => h_inf k hk) fun x hx => by aesop
  exact hk (Set.Finite.subset (Set.finite_singleton (Classical.choose (hk.nonempty))) fun j hj => Classical.not_not.1 fun hj' => Finset.disjoint_left.mp (hI _ _ hj') hj (Classical.choose_spec (hk.nonempty)))

end
