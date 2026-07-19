import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Constructions
import Mathlib.Data.Countable.Defs
import ZeroDimensionalSpaces.Basics

/-!
# `CantorRat`: the eventually-zero binary sequences

`CantorRat` (a.k.a. `CantorEventuallyZero`) is the subspace of `CantorSpace = ℕ → Fin 2`
consisting of the eventually-zero sequences. It is a nonempty countable metrizable space
without isolated points — the concrete model of "the rationals" used as the universal
countable perfect space.

Definitions are copied from `WqoContinuousFunctions.ContinuousReducibility.Scattered.NonScattered`
and the instances from `…ContinuousReducibility.Universality`; names kept in the root namespace.
-/

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-- A binary sequence is eventually zero. -/
def IsEventuallyZero (x : CantorSpace) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, x n = 0

/-- The subspace of eventually-zero binary sequences. -/
def CantorEventuallyZero : Type :=
  { x : CantorSpace // IsEventuallyZero x }

/-- Shorthand notation `CantorRat` for the eventually-zero binary sequences. -/
notation "CantorRat" => CantorEventuallyZero

instance : TopologicalSpace CantorEventuallyZero := instTopologicalSpaceSubtype

/-- Helper: extract the canonical prefix of an eventually-zero sequence. -/
noncomputable def cantorRatPrefix (x : CantorEventuallyZero) : List (Fin 2) := by
  classical
  exact PiNat.res x.val (Nat.find x.prop)

/-- `CantorRat` is metrizable, being a subspace of the metrizable Cantor space. -/
instance instMetrizableSpaceCantorEventuallyZero : MetrizableSpace CantorEventuallyZero :=
  inferInstanceAs (MetrizableSpace ↥{x : CantorSpace | IsEventuallyZero x})

/-- `CantorRat` is countable: an eventually-zero binary sequence is determined by its
(finite) support. -/
instance instCountableCantorEventuallyZero : Countable CantorEventuallyZero := by
  have hfin : ∀ x : CantorEventuallyZero, (Function.support x.val).Finite := by
    intro x
    obtain ⟨N, hN⟩ := x.prop
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_Iio]
    by_contra h
    exact hn (hN n (not_lt.mp h))
  apply Function.Injective.countable (f := fun x => (hfin x).toFinset)
  intro x y hxy
  simp only at hxy
  apply Subtype.ext
  funext n
  have hn : n ∈ (hfin x).toFinset ↔ n ∈ (hfin y).toFinset := by rw [hxy]
  simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hn
  by_cases hx : x.val n = 0 <;> by_cases hy : y.val n = 0 <;>
    first
      | rw [hx, hy]
      | (exfalso; tauto)
      | omega

/-- The all-zero sequence, a distinguished point of `CantorRat`. -/
instance instInhabitedCantorEventuallyZero : Inhabited CantorEventuallyZero :=
  ⟨⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩⟩

/--
`CantorRat` has no isolated points: every basic clopen neighbourhood of an eventually-zero
sequence `x` (fixing finitely many coordinates) contains another eventually-zero sequence,
obtained by setting a far-out coordinate to `1`.
-/
lemma cantorRat_no_isolated (x : CantorEventuallyZero) :
    ¬ IsOpen ({x} : Set CantorEventuallyZero) := by
  -- By definition of CantorRat, every point is a cluster point of its complement.
  have h_cluster : ∀ x : CantorRat, ∀ m : ℕ, ∃ y : CantorRat, y ≠ x ∧ ∀ n < m, y.val n = x.val n := by
    intro x m
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, x.val n = 0 := by
      exact x.2;
    refine ⟨ ⟨ fun n => if n = m + N then 1 else x.val n, ?_ ⟩, ?_, ?_ ⟩;
    refine ⟨ m + N + 1, fun n hn => ?_ ⟩;
    grind;
    · intro h; have := congr_arg ( fun f => f.val ( m + N ) ) h; simp +decide [ hN ] at this;
    · grind;
  intro h_open
  obtain ⟨U, hU_open, hU_subset⟩ : ∃ U : Set CantorSpace, IsOpen U ∧ x.val ∈ U ∧ ∀ y : CantorRat, y.val ∈ U → y = x := by
    convert h_open using 1;
    constructor <;> intro h;
    · convert h_open using 1;
    · obtain ⟨ U, hU₁, hU₂ ⟩ := h;
      exact ⟨ U, hU₁, hU₂.symm.subset rfl, fun y hy => hU₂.subset hy ⟩;
  -- Choose m such that the basic clopen neighborhood of x defined by fixing the first m coordinates is contained in U.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ y : CantorSpace, (∀ n < m, y n = x.val n) → y ∈ U := by
    rw [ isOpen_pi_iff ] at hU_open;
    obtain ⟨ I, u, hu₁, hu₂ ⟩ := hU_open _ hU_subset.1;
    use I.sup id + 1;
    intro y hy; exact hu₂ fun n hn => by have := hy n ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hn ) ) ; aesop;
  obtain ⟨ y, hy₁, hy₂ ⟩ := h_cluster x m
  exact hy₁ (hU_subset.2 y (hm _ hy₂))

/-- A product `A × B` has no isolated points whenever the second factor `B` has none:
the slice map `y ↦ (a, y)` is continuous, and the preimage of `{(a, b)}` is `{b}`. -/
lemma prod_no_isolated_of_right {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (hB : ∀ b : B, ¬ IsOpen ({b} : Set B)) :
    ∀ p : A × B, ¬ IsOpen ({p} : Set (A × B)) := by
  rintro ⟨a, b⟩ h
  apply hB b
  have hpre : (fun y : B => (a, y)) ⁻¹' {(a, b)} = {b} := by
    ext y; simp [Prod.ext_iff]
  rw [← hpre]
  exact h.preimage (continuous_const.prodMk continuous_id)
