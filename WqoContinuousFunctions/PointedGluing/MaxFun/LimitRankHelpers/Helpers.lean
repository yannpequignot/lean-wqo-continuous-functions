import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import ZeroDimensionalSpaces.Basics

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-! ## Helper lemmas for the antichain construction in MaxFunLimitRank -/

/-- Key combinatorial lemma: given an injective function f : ℕ → B where
    range f carries the discrete topology, we can find an antichain of finite
    truncations covering all of f.

    The discrete topology hypothesis is used in Case 2: if every coordinate
    function i ↦ f i k had finite range, a diagonal argument would produce a
    subsequence converging in ℕ → ℕ to some limit v; but v would be a limit
    point of range f, contradicting DiscreteTopology (Set.range f) unless the
    subsequence were eventually constant — contradicting Injective f. -/
lemma infinite_baire_antichain_prefixes
    {B : Set (ℕ → ℕ)}
    (f : ℕ → B)
    (hf : Injective f)
    (hdisc : DiscreteTopology B) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                       ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∃ m, ∀ j : Fin (seq i).1, (seq i).2 j = (f m).val j := by
  -- For each i, find k_i such that BaNbhd (f i ↾ k_i) ∩ range f = {f i}.
  have hiso : ∀ i, ∃ k : ℕ, ∀ j, (∀ l : Fin k, (f j).val l = (f i).val l) → j = i := by
    intro i
    -- {f i} is open in B since B is discrete.
    have hopen : IsOpen ({f i} : Set B) := isOpen_discrete _
    -- Openness in the subspace topology: ∃ V open in ℕ^ℕ with V ∩ B = {f i}.
    rw [isOpen_induced_iff] at hopen
    obtain ⟨V, hV_open, hV_eq⟩ := hopen
    -- f i ∈ V.
    have hV_fi : (f i).val ∈ V := by
      have : f i ∈ ({f i} : Set B) := Set.mem_singleton _
      rwa [← hV_eq] at this
    -- V is open in ℕ^ℕ, so ∃ finite I ⊆ ℕ and open U k covering F i with
    -- ∀ x agreeing with F i on I, x ∈ V.
    rw [isOpen_pi_iff] at hV_open
    obtain ⟨I, U, hU, hIU⟩ := hV_open _ hV_fi
    -- Take k := I.sup id + 1, so all coords in I lie below k.
    refine ⟨I.sup id + 1, fun j hagree => ?_⟩
    -- F j agrees with F i on all coords in I (since they lie below k).
    have hFj_V : (f j).val ∈ V := hIU (fun l hl => by
      have hlt : l < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hl)
      simpa using (hagree ⟨l, hlt⟩).symm ▸ (hU l hl).2)
    exact hf (Set.mem_singleton_iff.mp (hV_eq ▸ hFj_V))
  choose k hk using hiso
  -- seq i := the truncation of f i to length k i.
  refine ⟨fun i => ⟨k i, fun l => (f i).val l⟩, fun i j hij => ⟨?_, ?_⟩,
          fun i => ⟨i, fun l => rfl⟩⟩
  -- ¬ IsPrefix (seq i).2 (seq j).2
  · rintro ⟨_, hagree⟩
    exact hij.symm (hk i j (fun l => (hagree l).symm))
  -- ¬ IsPrefix (seq j).2 (seq i).2
  · rintro ⟨_, hagree⟩
    exact hij (hk j i (fun l => (hagree l).symm))
