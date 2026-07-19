import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import WqoContinuousFunctions.ContinuousReducibility.Defs
import ZeroDimensionalSpaces.GenRedProp
import WqoContinuousFunctions.ContinuousReducibility.Scattered
import WqoContinuousFunctions.ContinuousReducibility.Gluing
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.PointedGluing.Defs
import WqoContinuousFunctions.PointedGluing.CBRank.Helpers
import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers
import WqoContinuousFunctions.PointedGluing.UpperBound.Helpers
import WqoContinuousFunctions.PointedGluing.Basics.ContinuousOnTau
import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers
import WqoContinuousFunctions.PointedGluing.MinFun.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helpers for the pointed gluing lower bound
-/

/-- In the Baire space, cylinder sets form a neighborhood basis. -/
lemma baire_cylinder_mem_nhds (p : ℕ → ℕ) (U : Set (ℕ → ℕ)) (hU : IsOpen U) (hp : p ∈ U) :
    ∃ m : ℕ, {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = p i} ⊆ U := by
  rw [isOpen_pi_iff] at hU
  obtain ⟨I, u, hu, hU⟩ := hU p hp
  use I.sup id + 1
  intro h hh; specialize hU; simp_all +decide [Set.subset_def]
  exact hU _ fun i hi => by simpa [hh i (Finset.le_sup (f := id) hi)] using hu i hi

/-- In a subspace of the Baire space, cylinder sets form a neighborhood basis. -/
lemma baire_subspace_cylinder_mem_nhds {A : Set (ℕ → ℕ)} (x : A)
    (U : Set A) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ m : ℕ, (Subtype.val ⁻¹' {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = x.val i}) ⊆ U := by
  induction hU
  rename_i V hV
  rcases baire_cylinder_mem_nhds x.val V hV.1 (hV.2.symm.subset hx) with ⟨m, hm⟩ ; exact ⟨m, fun y hy => hV.2.subset <| hm hy⟩
