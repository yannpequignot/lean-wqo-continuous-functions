import Mathlib.Tactic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity

open scoped Topology
open Set Function

set_option autoImplicit false

/-!
# Disjoint open neighbourhoods of a discrete subspace

General topology fact used by the intertwining-reductions lemma, kept in a Mathlib-only file
(separate from `Topology/DiscreteSubspaces`).

## Main result

* `exists_pairwise_disjoint_open_nhds` — in a metrizable space, an injective family `y` whose image
  is discrete admits pairwise disjoint open neighbourhoods `V i ∋ y i`.
-/

/-
**Disjoint open neighbourhoods of a discrete subspace.**

In a metrizable space `B`, if `y : ι → B` is injective with discrete image, then there are
pairwise disjoint open sets `V i ∋ y i`.

INTENDED PROOF.  Fix a compatible metric `d` (`metrizableSpaceMetric`).  Discreteness makes each
`y i` isolated in `range y`: there is `ε i > 0` with `ε i ≤ d (y i) (y j)` for all `j ≠ i`.  Take
`V i = ball (y i) (ε i / 2)`.  These contain `y i`, are open, and are pairwise disjoint: if
`x ∈ V i ∩ V j` with (wlog) `ε i ≤ ε j`, the triangle inequality gives
`d (y i) (y j) < ε i / 2 + ε j / 2 ≤ ε j ≤ d (y i) (y j)`, a contradiction.
-/
theorem exists_pairwise_disjoint_open_nhds {B : Type*} [TopologicalSpace B]
    [TopologicalSpace.MetrizableSpace B] {ι : Type*} (y : ι → B) (hinj : Function.Injective y)
    (hdisc : DiscreteTopology ↥(Set.range y)) :
    ∃ V : ι → Set B, (∀ i, IsOpen (V i)) ∧ (∀ i, y i ∈ V i) ∧ Pairwise (Disjoint on V) := by
  obtain ⟨d, hd⟩ : ∃ d : MetricSpace B, @UniformSpace.toTopologicalSpace B d.toUniformSpace = ‹TopologicalSpace B› := by
    convert ( inferInstance : TopologicalSpace.MetrizableSpace B ) |> fun h => h.1;
    constructor <;> intro h;
    · infer_instance;
    · exact ⟨ TopologicalSpace.metrizableSpaceMetric B, rfl ⟩;
  -- By discreteness of `range y`, there exist `ε i > 0` such that `ε i ≤ d (y i) (y j)` for all `j ≠ i`.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧ (∀ i j, i ≠ j → ε i ≤ dist (y i) (y j)) := by
    have h_discrete : ∀ i, ∃ ε > 0, ∀ j, y j ∈ Metric.ball (y i) ε → j = i := by
      intro i
      have h_isolated : ∀ᶠ x in nhds (⟨y i, Set.mem_range_self i⟩ : Set.range y), x = ⟨y i, Set.mem_range_self i⟩ := by
        simp +decide [ nhds_discrete ];
      rw [ nhds_induced ] at h_isolated;
      rw [ Filter.eventually_comap ] at h_isolated;
      rw [ hd.symm ] at h_isolated;
      rcases Metric.mem_nhds_iff.1 h_isolated with ⟨ ε, εpos, hε ⟩;
      exact ⟨ ε, εpos, fun j hj => hinj <| by simpa using congr_arg Subtype.val <| hε hj ⟨ y j, Set.mem_range_self j ⟩ rfl ⟩;
    choose ε hε_pos hε using h_discrete;
    exact ⟨ ε, hε_pos, fun i j hij => le_of_not_gt fun h => hij <| hε i j ( Metric.mem_ball'.2 h ) ▸ rfl ⟩;
  refine ⟨ fun i => Metric.ball ( y i ) ( ε i / 2 ), ?_, ?_, ?_ ⟩;
  · intro i;
    convert Metric.isOpen_ball;
    exact hd.symm;
  · exact fun i => Metric.mem_ball_self ( half_pos ( hε_pos i ) );
  · intro i j hij; rw [ Function.onFun, Set.disjoint_left ] ; intro x hx hx'; have := hε i j hij; have := hε j i hij.symm; simp_all +decide [ dist_comm ] ;
    linarith [ hε i j hij, dist_triangle_left ( y i ) ( y j ) x ]