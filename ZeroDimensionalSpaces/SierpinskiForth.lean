import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Countable.Defs
import ZeroDimensionalSpaces.CantorRat
import ZeroDimensionalSpaces.Engine

/-!
# The "forth" direction: every countable metrizable space embeds into `CantorRat`

This file proves `countable_metrizable_embeds_cantorRat`: every countable metrizable space `X`
embeds topologically into `CantorRat` (no perfectness or nonemptiness needed).  Together with
`cantorRat_embeds_perfect` (in `SierpinskiAux.lean`) this yields Sierpiński universality.

## Construction

Fix a compatible metric on `X`, a surjective enumeration `e : ℕ → X`, and the
zero-dimensional structure.  We build a refining binary tree of clopen "cells" of `X`:

* `cellOf e x 0 = univ`;
* at each node we look at the cell `C = cellOf e x n`, take its **least-indexed** point
  `p = leastPt e C` (w.r.t. `e`), and a small clopen neighbourhood `cball p n ⊆ ball p (eps n)`
  of it. The `0`-child is `zeroChild = C ∩ cball p n` (it keeps `p`), the `1`-child is the rest
  `C \ zeroChild`.

`bitOf e x n` records, for the point `x`, whether it falls in the `0`-child (bit `0`) or the
`1`-child (bit `1`) at level `n`.  The map `g x = fun n => bitOf e x n : X → CantorSpace` is a
topological embedding, and crucially every `g x` is **eventually zero** (each `x` eventually
becomes, and stays, the least point of its cell), so `g` corestricts to an embedding into
`CantorRat`.
-/

open scoped Topology Classical
open Set Function TopologicalSpace SierpinskiBuild

set_option autoImplicit false

namespace SierpinskiForth

section Construction

variable {X : Type*} [MetricSpace X] [ZeroDimensionalSpace X]

/-- Radius schedule: `eps n = (1/2)^(n+1)`. -/
noncomputable def eps (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)

lemma eps_pos (n : ℕ) : 0 < eps n := by unfold eps; positivity

/-- A chosen small clopen neighbourhood of `p` contained in `ball p (eps n)`. -/
noncomputable def cball (p : X) (n : ℕ) : Set X :=
  (exists_clopen_ball p (eps_pos n)).choose

lemma cball_isClopen (p : X) (n : ℕ) : IsClopen (cball p n) :=
  (exists_clopen_ball p (eps_pos n)).choose_spec.1

lemma mem_cball (p : X) (n : ℕ) : p ∈ cball p n :=
  (exists_clopen_ball p (eps_pos n)).choose_spec.2.1

lemma cball_subset (p : X) (n : ℕ) : cball p n ⊆ Metric.ball p (eps n) :=
  (exists_clopen_ball p (eps_pos n)).choose_spec.2.2

variable (e : ℕ → X)

/-- The least-`e`-indexed point of a set `C` (junk value `e 0` if `C` misses the range). -/
noncomputable def leastPt (C : Set X) : X :=
  if h : ∃ k, e k ∈ C then e (Nat.find h) else e 0

omit [MetricSpace X] [ZeroDimensionalSpace X] in
lemma leastPt_mem {C : Set X} (h : ∃ k, e k ∈ C) : leastPt e C ∈ C := by
  rw [leastPt, dif_pos h]; exact Nat.find_spec h

/-- The `0`-child of a cell `C` at level `n`: a small clopen neighbourhood of its least point. -/
noncomputable def zeroChild (C : Set X) (n : ℕ) : Set X :=
  C ∩ cball (leastPt e C) n

lemma zeroChild_subset (C : Set X) (n : ℕ) : zeroChild e C n ⊆ C :=
  Set.inter_subset_left

lemma zeroChild_isClopen {C : Set X} (hC : IsClopen C) (n : ℕ) :
    IsClopen (zeroChild e C n) :=
  hC.inter (cball_isClopen _ _)

/-- The cell of `x` at level `n`: a clopen set of the refining binary tree. -/
noncomputable def cellOf (x : X) : ℕ → Set X
  | 0 => Set.univ
  | (n + 1) =>
      if x ∈ zeroChild e (cellOf x n) n then zeroChild e (cellOf x n) n
      else (cellOf x n) \ zeroChild e (cellOf x n) n

/-- The `n`-th bit of `x`: `0` if `x` is in the `0`-child of its cell, `1` otherwise. -/
noncomputable def bitOf (x : X) (n : ℕ) : Fin 2 :=
  if x ∈ zeroChild e (cellOf e x n) n then 0 else 1

lemma cellOf_zero (x : X) : cellOf e x 0 = Set.univ := rfl

lemma cellOf_succ (x : X) (n : ℕ) :
    cellOf e x (n + 1) =
      if x ∈ zeroChild e (cellOf e x n) n then zeroChild e (cellOf e x n) n
      else (cellOf e x n) \ zeroChild e (cellOf e x n) n := rfl

/-
`x` lies in its own cell at every level.
-/
lemma mem_cellOf (x : X) (n : ℕ) : x ∈ cellOf e x n := by
  induction' n with n ih;
  · exact Set.mem_univ x;
  · by_cases h : x ∈ zeroChild e ( cellOf e x n ) n <;> simp +decide [ *, cellOf_succ ]

/-
The cells are clopen.
-/
lemma cellOf_isClopen (x : X) (n : ℕ) : IsClopen (cellOf e x n) := by
  induction' n with n ih;
  · convert isClopen_univ;
  · rw [ cellOf_succ ];
    split_ifs <;> simp_all +decide [ zeroChild_isClopen, IsClopen.diff ]

/-
Cells are nested.
-/
lemma cellOf_succ_subset (x : X) (n : ℕ) : cellOf e x (n + 1) ⊆ cellOf e x n := by
  rw [cellOf];
  split_ifs <;> [ exact Set.inter_subset_left; exact Set.diff_subset ]

/-
If `x` and `y` agree on the first `n` bits, their cells at level `n` coincide.
-/
lemma cellOf_congr (x y : X) (n : ℕ) (h : ∀ i < n, bitOf e y i = bitOf e x i) :
    cellOf e y n = cellOf e x n := by
  induction' n with n ih;
  · exact Set.ext fun z => by simp +decide [ cellOf_zero ] ;
  · simp_all +decide [ bitOf, cellOf_succ ];
    grind

/-
Characterisation of the cell as the set of points agreeing on the first `n` bits.
-/
lemma cellOf_eq (x : X) (n : ℕ) :
    cellOf e x n = {y | ∀ i < n, bitOf e y i = bitOf e x i} := by
  ext y;
  constructor;
  · induction' n with n ih generalizing y;
    · aesop;
    · intro hy;
      have hZ : cellOf e y n = cellOf e x n := by
        apply cellOf_congr;
        exact ih y ( cellOf_succ_subset e x n hy );
      grind +locals;
  · intro hy
    have h_cell : cellOf e y n = cellOf e x n := by
      exact cellOf_congr e x y n hy
    exact h_cell ▸ mem_cellOf e y n

/-
Diameter bound for a `0`-child.
-/
lemma diam_zeroChild (C : Set X) (n : ℕ) :
    Metric.diam (zeroChild e C n) ≤ (1 / 2) ^ n := by
  apply Metric.diam_le_of_forall_dist_le;
  · positivity;
  · intro x hx y hy
    have h_dist : dist x (leastPt e C) < eps n ∧ dist y (leastPt e C) < eps n := by
      exact ⟨ Metric.mem_ball.mp ( cball_subset _ _ hx.2 ), Metric.mem_ball.mp ( cball_subset _ _ hy.2 ) ⟩;
    convert le_trans ( dist_triangle_right _ _ _ ) ( add_le_add h_dist.1.le h_dist.2.le ) using 1 ; unfold eps ; ring

/-
When the `n`-th bit of `x` is `0`, the next cell is small.
-/
lemma diam_cellOf_succ_of_bit0 (x : X) (n : ℕ) (h : bitOf e x n = 0) :
    Metric.diam (cellOf e x (n + 1)) ≤ (1 / 2) ^ n := by
  convert diam_zeroChild e ( cellOf e x n ) n using 1;
  grind +locals

/-- There is always an index of `e` landing in `cellOf e x n` (since `x` lies in it). -/
lemma exists_mem_cellOf (he : Surjective e) (x : X) (n : ℕ) : ∃ k, e k ∈ cellOf e x n := by
  obtain ⟨k, hk⟩ := he x
  exact ⟨k, hk ▸ mem_cellOf e x n⟩

/-
A monotone, bounded `ℕ → ℕ` sequence is eventually constant.
-/
lemma monotone_nat_bounded_eventually_const (a : ℕ → ℕ) (hmono : Monotone a) (B : ℕ)
    (hB : ∀ n, a n ≤ B) : ∃ N, ∀ n ≥ N, a n = a N := by
  -- Since the range is nonempty and bounded above, `v ∈ Set.range a` (`Nat.sSup_mem`), so there is `N` with `a N = v`.
  obtain ⟨N, hN⟩ : ∃ N, a N = sSup (Set.range a) := by
    have := Nat.sSup_mem ( Set.range_nonempty a ) ( show BddAbove ( Set.range a ) from ⟨ B, Set.forall_mem_range.mpr hB ⟩ ) ; aesop;
  exact ⟨ N, fun n hn => le_antisymm ( hN ▸ le_csSup ( show BddAbove ( Set.range a ) from ⟨ B, Set.forall_mem_range.mpr hB ⟩ ) ( Set.mem_range_self n ) ) ( hN ▸ hmono hn ) ⟩

/-
If `x` is the least point of its cell at level `n`, then its `n`-th bit is `0`.
-/
lemma bit_zero_of_leastPt (x : X) (n : ℕ) (h : leastPt e (cellOf e x n) = x) :
    bitOf e x n = 0 := by
  unfold bitOf;
  -- Since `x` is the least point of its cell at level `n`, it must be in the zero child of its cell at level `n`.
  simp only [zeroChild, h, mem_inter_iff, Fin.isValue, ite_eq_left_iff, not_and, one_ne_zero, imp_false, Classical.not_imp, Decidable.not_not];
  exact ⟨ mem_cellOf e x n, mem_cball x n ⟩

/-
If `x` is the least point of its cell at level `n`, it remains the least point at level
`n+1`.
-/
lemma leastPt_succ_of_leastPt (x : X) (n : ℕ) (h : leastPt e (cellOf e x n) = x) :
    leastPt e (cellOf e x (n + 1)) = x := by
  rw [ cellOf_succ ];
  split_ifs <;> simp_all +decide [ leastPt ];
  · split_ifs at * <;> simp_all +decide [ zeroChild ];
    · convert h using 2;
      refine le_antisymm ?_ ?_ <;> simp_all +decide;
      grind [ZeroDimensionalSpace.clopen_basis, Nat.find_le];
    · grind;
    · grind;
  · split_ifs at * <;> simp_all +decide [ zeroChild ];
    · grind +locals;
    · grind;
    · grind +qlia

/-
Eventually, `x` is the least point of its cell.
-/
lemma leastPt_eventually (he : Surjective e) (x : X) :
    ∃ N, leastPt e (cellOf e x N) = x := by
  revert x;
  intro x
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, e k₀ = x := by
    exact he x
  set a : ℕ → ℕ := fun n => Nat.find (exists_mem_cellOf e he x n)
  have ha_mono : Monotone a := by
    refine' monotone_nat_of_le_succ fun n => Nat.find_le _;
    exact cellOf_succ_subset e x n ( Nat.find_spec ( exists_mem_cellOf e he x ( n + 1 ) ) )
  have ha_bound : ∀ n, a n ≤ k₀ := by
    intro n
    apply Nat.find_le
    simp [hk₀, mem_cellOf]
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, a n = a N := by
    apply SierpinskiForth.monotone_nat_bounded_eventually_const a ha_mono k₀ ha_bound
  set L := a N
  have hL : ∀ n ≥ N, leastPt e (cellOf e x n) = e L := by
    intro n hn; specialize hN n hn; simp_all +decide [ leastPt ] ;
    grind
  have hL_eq_x : e L = x := by
    by_contra hL_ne_x
    set d := dist x (e L) with hd
    have hd_pos : 0 < d := by
      exact dist_pos.mpr ( Ne.symm hL_ne_x )
    obtain ⟨n, hn⟩ : ∃ n ≥ N, (1 / 2 : ℝ) ^ n < d := by
      obtain ⟨ n, hn ⟩ := exists_pow_lt_of_lt_one hd_pos ( by norm_num : ( 1 / 2 : ℝ ) < 1 ) ; exact ⟨ n + N, by linarith, by exact lt_of_le_of_lt ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by linarith ) ) hn ⟩ ;
    have h_case : x ∈ zeroChild e (cellOf e x n) n ∨ x ∉ zeroChild e (cellOf e x n) n := by
      exact em _
    cases' h_case with h_case h_case
    ·
      have h_dist : dist x (e L) < (1 / 2 : ℝ) ^ n := by
        have h_dist : x ∈ Metric.ball (e L) (eps n) := by
          exact cball_subset _ _ ( hL n hn.1 ▸ h_case.2 );
        exact lt_of_lt_of_le h_dist ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( Nat.le_succ _ ) );
      lia
    ·
      have h_contra : e L ∈ cellOf e x (n + 1) := by
        grind;
      grind +locals
  use N
  simp [hL, hL_eq_x]

/-- Once `x` is the least point of its cell at level `N`, it stays so forever. -/
lemma leastPt_stays (x : X) (N : ℕ) (h : leastPt e (cellOf e x N) = x) :
    ∀ n ≥ N, leastPt e (cellOf e x n) = x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact leastPt_succ_of_leastPt e x m ih

/-- **Eventually zero.** Every point eventually becomes (and stays) the least point of its
cell, so its bit sequence is eventually `0`. Requires `e` surjective. -/
lemma eventually_bit_zero (he : Surjective e) (x : X) :
    ∃ N, ∀ n ≥ N, bitOf e x n = 0 := by
  obtain ⟨N, hN⟩ := leastPt_eventually e he x
  exact ⟨N, fun n hn => bit_zero_of_leastPt e x n (leastPt_stays e x N hN n hn)⟩

/-
The coordinate maps are continuous (locally constant).
-/
lemma bitOf_continuous (n : ℕ) : Continuous (fun x => bitOf e x n) := by
  have h_bit_of_locally_constant : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, bitOf e y n = bitOf e x n := by
    intro x;
    refine ⟨ cellOf e x ( n + 1 ), ( cellOf_isClopen e x ( n + 1 ) ).2, mem_cellOf e x ( n + 1 ), ?_ ⟩;
    intro y hy; rw [ cellOf_eq ] at hy; exact hy n ( Nat.lt_succ_self _ ) ;
  refine continuous_iff_continuousAt.mpr ?_;
  intro x; specialize h_bit_of_locally_constant x; rcases h_bit_of_locally_constant with ⟨ U, hUo, hxU, hU ⟩ ; exact tendsto_const_nhds.congr' ( by filter_upwards [ IsOpen.mem_nhds hUo hxU ] with y hy; aesop ) ;

/-- The combined map into Cantor space. -/
noncomputable def toCantor (x : X) : CantorSpace := fun n => bitOf e x n

lemma toCantor_continuous : Continuous (toCantor e) := by
  exact continuous_pi fun n => bitOf_continuous e n

lemma toCantor_injective (he : Surjective e) : Function.Injective (toCantor e) := by
  intro x y hxy
  have h_cells : ∀ m, cellOf e y m = cellOf e x m := by
    intro m
    apply cellOf_congr
    intro i hi
    apply congr_fun hxy i |> Eq.symm
  have h_dist : ∀ n ≥ (Classical.choose (eventually_bit_zero e he x)), dist x y ≤ (1 / 2) ^ n := by
    intro n hn
    have h_bit_zero : bitOf e x n = 0 := by
      exact Classical.choose_spec ( eventually_bit_zero e he x ) n hn
    have h_cell_subset : cellOf e x (n + 1) ⊆ Metric.ball (leastPt e (cellOf e x n)) (eps n) := by
      rw [cellOf] at *; simp_all +decide [ bitOf ] ;
      exact Set.Subset.trans ( Set.inter_subset_right ) ( cball_subset _ _ )
    have h_dist : dist x y ≤ (1 / 2) ^ n := by
      have h_dist : x ∈ Metric.ball (leastPt e (cellOf e x n)) (eps n) ∧ y ∈ Metric.ball (leastPt e (cellOf e x n)) (eps n) := by
        exact ⟨ h_cell_subset ( mem_cellOf e x ( n + 1 ) ), h_cell_subset ( h_cells ( n + 1 ) ▸ mem_cellOf e y ( n + 1 ) ) ⟩;
      convert dist_triangle_right x y ( leastPt e ( cellOf e x n ) ) |> le_trans <| add_le_add h_dist.1.le h_dist.2.le using 1 ; norm_num [ eps ] ; ring
    exact h_dist
  have h_eq : x = y := by
    contrapose! h_dist;
    exact ⟨ _, le_max_left _ _, lt_of_le_of_lt ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( le_max_right _ _ ) ) ( by simpa using exists_pow_lt_of_lt_one ( dist_pos.mpr h_dist ) ( by norm_num : ( 1 / 2 : ℝ ) < 1 ) |> Classical.choose_spec ) ⟩
  exact h_eq

lemma toCantor_isEmbedding (he : Surjective e) : Topology.IsEmbedding (toCantor e) := by
  refine ⟨ ?_, ?_ ⟩;
  · -- To prove it's inducing, use `Topology.isInducing_iff_nhds`: for each `x`, `𝓝 x = Filter.comap f (𝓝 (f x))`.
    apply Topology.isInducing_iff_nhds.mpr
    intro x
    apply le_antisymm
    · -- Show `𝓝 x ≤ comap f (𝓝 (f x))` via continuity.
      exact (toCantor_continuous e).continuousAt.le_comap
    · -- Show `comap f (𝓝 (f x)) ≤ 𝓝 x`.
      intro U hU
      -- Choose `m` such that `cellOf e x m ⊆ U`.
      obtain ⟨m, hm⟩ : ∃ m, cellOf e x m ⊆ U := by
        obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball x ε ⊆ U := by
          exact Metric.mem_nhds_iff.1 hU;
        obtain ⟨ N, hN ⟩ := eventually_bit_zero e he x;
        obtain ⟨n, hn⟩ : ∃ n ≥ N, (1 / 2 : ℝ) ^ n < ε := by
          rcases exists_pow_lt_of_lt_one hε_pos one_half_lt_one with ⟨ n, hn ⟩ ; exact ⟨ n + N, by linarith, by exact lt_of_le_of_lt ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by linarith ) ) hn ⟩;
        refine ⟨ n + 1, fun y hy => hε ?_ ⟩;
        have h_dist : dist x y < 2 * eps n := by
          have h_dist : x ∈ Metric.ball (leastPt e (cellOf e x n)) (eps n) ∧ y ∈ Metric.ball (leastPt e (cellOf e x n)) (eps n) := by
            have h_dist : x ∈ zeroChild e (cellOf e x n) n ∧ y ∈ zeroChild e (cellOf e x n) n := by
              rw [cellOf] at hy;
              split_ifs at hy <;> simp_all +decide [ bitOf ];
            exact ⟨ cball_subset _ _ h_dist.1.2, cball_subset _ _ h_dist.2.2 ⟩;
          exact lt_of_le_of_lt ( dist_triangle_right _ _ _ ) ( by linarith [ Metric.mem_ball.mp h_dist.1, Metric.mem_ball.mp h_dist.2 ] );
        simp_all +decide [ eps ];
        rw [ dist_comm ] ; exact h_dist.trans_le ( by ring_nf at *; linarith );
      refine ⟨ { z : CantorSpace | ∀ i < m, z i = toCantor e x i }, ?_, ?_ ⟩ <;> simp_all +decide [ Set.subset_def ];
      · rw [ nhds_pi ];
        simp +decide only [nhds_discrete, Filter.mem_pi, Filter.mem_pure];
        refine ⟨ Finset.range m, Finset.finite_toSet _, fun i => { toCantor e x i }, ?_, ?_ ⟩ <;> simp +decide [ Set.subset_def ];
      · intro y hy; specialize hm y; rw [ cellOf_eq ] at hm; aesop;
  · exact toCantor_injective e he

lemma toCantor_eventuallyZero (he : Surjective e) (x : X) :
    IsEventuallyZero (toCantor e x) := by
  obtain ⟨N, hN⟩ := eventually_bit_zero e he x
  exact ⟨N, fun n hn => hN n hn⟩

end Construction

end SierpinskiForth

/-- **The forth direction (universality of `CantorRat`).** Every countable metrizable space
embeds topologically into `CantorRat`. Neither nonemptiness nor perfectness of the domain is
required — the empty domain embeds vacuously, and perfectness is genuinely unused for this
direction. -/
theorem countable_metrizable_embeds_cantorRat {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [Countable X] :
    ∃ f : X → CantorRat, Topology.IsEmbedding f := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun x => isEmptyElim x, ⟨⟨Subsingleton.elim _ _⟩, fun a => isEmptyElim a⟩⟩
  · letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    obtain ⟨e, he⟩ := exists_surjective_nat X
    have hemb : Topology.IsEmbedding (SierpinskiForth.toCantor e) :=
      SierpinskiForth.toCantor_isEmbedding e he
    refine ⟨fun x => ⟨SierpinskiForth.toCantor e x,
      SierpinskiForth.toCantor_eventuallyZero e he x⟩, ?_⟩
    have hcont : Continuous (fun x => (⟨SierpinskiForth.toCantor e x,
        SierpinskiForth.toCantor_eventuallyZero e he x⟩ : CantorRat)) :=
      hemb.continuous.subtype_mk _
    exact Topology.IsEmbedding.of_comp hcont continuous_subtype_val hemb