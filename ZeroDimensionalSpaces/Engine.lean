import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import ZeroDimensionalSpaces.Basics

/-!
# Engine lemmas for the back-and-forth construction

Elementary building blocks for the (one-sided or full) back-and-forth construction underlying
Sierpiński's theorem:

* `exists_clopen_ball` — arbitrarily small clopen neighbourhoods in a zero-dimensional metric
  space;
* `open_infinite` — nonempty open sets are infinite when there are no isolated points;
* `clopen_split` — a nonempty clopen set splits into two nonempty clopen pieces.

Moved verbatim from `WqoContinuousFunctions.ContinuousReducibility.Scattered.Sierpinski`.
-/

open scoped Topology
open Set Function TopologicalSpace Metric

namespace SierpinskiBuild

set_option autoImplicit false

variable {X : Type*} [MetricSpace X]

/-- In a zero-dimensional metric space, every point has arbitrarily small clopen neighbourhoods
contained in a given ball. -/
lemma exists_clopen_ball [ZeroDimensionalSpace X] (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ Metric.ball x ε := by
  obtain ⟨ B, hB₁, hB₂ ⟩ := ZeroDimensionalSpace.clopen_basis ( X := X );
  exact Exists.elim ( hB₁.mem_nhds_iff.1 ( Metric.isOpen_ball.mem_nhds ( Metric.mem_ball_self hε ) ) ) fun V hV => ⟨ V, hB₂ V hV.1, hV.2.1, hV.2.2 ⟩

/-- In a `T1` space with no isolated points, every nonempty open set is infinite. -/
lemma open_infinite (hni : ∀ x : X, ¬ IsOpen ({x} : Set X)) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : U.Infinite := by
  by_contra h_contra;
  obtain ⟨x, hxU⟩ : ∃ x, x ∈ U := hne;
  refine' hni x _;
  convert hU.inter ( show IsOpen ( U \ { x } ) ᶜ from ?_ ) using 1;
  · grind;
  · exact isOpen_compl_iff.mpr ( Set.Finite.isClosed ( Set.Finite.subset ( Set.not_infinite.mp h_contra ) fun y hy => by aesop ) )

/--
A nonempty clopen set in a zero-dimensional space with no isolated points can be split into
two nonempty clopen pieces.
-/
lemma clopen_split [ZeroDimensionalSpace X] (hni : ∀ x : X, ¬ IsOpen ({x} : Set X))
    {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ V : Set X, IsClopen V ∧ V ⊆ U ∧ V.Nonempty ∧ (U \ V).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ U := hne
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ U, y ≠ x := by
    exact Set.Infinite.nonempty ( Set.Infinite.diff ( open_infinite hni hU.2 ( Set.nonempty_of_mem hx ) ) ( Set.finite_singleton x ) );
  obtain ⟨ W, hW₁, hW₂, hW₃ ⟩ := exists_clopen_ball x ( show 0 < Dist.dist y x from dist_pos.mpr hxy );
  refine' ⟨ U ∩ W, _, _, _, _ ⟩;
  · exact hU.inter hW₁;
  · exact Set.inter_subset_left;
  · exact ⟨ x, hx, hW₂ ⟩;
  · exact ⟨ y, hy, by rintro ⟨ hy₁, hy₂ ⟩ ; exact absurd ( hW₃ hy₂ ) ( by simp +decide [ dist_comm ] ) ⟩

end SierpinskiBuild
