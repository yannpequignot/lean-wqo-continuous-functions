import Mathlib
import RequestProject.BaireSpace.Basics

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-! ## Helper lemmas for the antichain construction in MaxFunLimitRank -/

lemma nat_range_infinite_or_fiber_infinite (g : ℕ → ℕ) :
    (Set.range g).Infinite ∨ ∃ v, (g ⁻¹' {v}).Infinite := by
  by_contra!
  exact Set.infinite_univ (Set.Finite.subset (Set.Finite.biUnion this.1 fun x hx => this.2 x) fun x _ => by aesop)

lemma injective_subseq_of_infinite_range (g : ℕ → ℕ) (h : (Set.range g).Infinite) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Injective (g ∘ a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ n, g (a n) ∉ Finset.image g (Finset.range (a n)) := by
    have h_infinite_range : ∀ n, ∃ m ≥ n, g m ∉ Finset.image g (Finset.range m) := by
      intro n; by_contra h_contra; push_neg at h_contra
      have h_range_subset : Set.range g ⊆ Finset.image g (Finset.range n) := by
        rintro x ⟨m, rfl⟩; induction' m using Nat.strong_induction_on with m ih
        rcases lt_or_ge m n with hm | hm <;> simp_all +decide [Finset.mem_image]
        · exact ⟨m, hm, rfl⟩
        · obtain ⟨a, ha₁, ha₂⟩ := h_contra m hm; obtain ⟨x, hx₁, hx₂⟩ := ih a ha₁; exact ⟨x, hx₁, hx₂.trans ha₂⟩
      exact h (Set.Finite.subset (Finset.finite_toSet _) h_range_subset)
    exact ⟨fun n => Nat.recOn n (Nat.find (h_infinite_range 0)) fun n ih => Nat.find (h_infinite_range (ih + 1)),
      strictMono_nat_of_lt_succ fun n => Nat.find_spec (h_infinite_range _) |>.1.trans_lt' (Nat.lt_succ_self _),
      fun n => Nat.recOn n (Nat.find_spec (h_infinite_range 0) |>.2) fun n ih => Nat.find_spec (h_infinite_range _) |>.2⟩
  exact ⟨a, ha.1, fun x y hxy => le_antisymm
    (le_of_not_gt fun hxy' => ha.2 _ <| Finset.mem_image.mpr ⟨a y, Finset.mem_range.mpr <| ha.1 hxy', hxy.symm⟩)
    (le_of_not_gt fun hxy' => ha.2 _ <| Finset.mem_image.mpr ⟨a x, Finset.mem_range.mpr <| ha.1 hxy', hxy⟩)⟩

/-- Case 1: branching level antichain -/
lemma branching_level_antichain (f : ℕ → (ℕ → ℕ)) (k : ℕ)
    (_hprefix : ∀ i j : ℕ, ∀ m : ℕ, m < k → f i m = f j m)
    (hinj : Injective (fun i => f i k)) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧ ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∀ j : Fin (seq i).1, (seq i).2 j = f i j := by
  refine ⟨fun i ↦ ⟨k + 1, fun j ↦ f i j⟩, ?_, ?_⟩ <;> simp +decide [IsPrefix]
  exact fun i j hij => ⟨⟨⟨k, Nat.lt_succ_self _⟩, fun h => hij <| hinj <| by simpa using h⟩,
    ⟨⟨k, Nat.lt_succ_self _⟩, fun h => hij <| hinj <| by simpa using h.symm⟩⟩

/-- Case 2: orphan extraction antichain -/
lemma orphan_antichain
    (f : ℕ → (ℕ → ℕ)) (v : ℕ → ℕ)
    (levels : ℕ → ℕ) (hlev_strict : StrictMono levels)
    (hagree : ∀ n m, m < levels n → f n m = v m)
    (hdiffer : ∀ n, f n (levels n) ≠ v (levels n)) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧ ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∀ j : Fin (seq i).1, (seq i).2 j = f i j := by
  refine ⟨fun i => ⟨levels i + 1, fun j => f i j⟩, ?_, ?_⟩ <;> simp +decide [IsPrefix]
  intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [hlev_strict.lt_iff_lt]
  · exact fun _ => ⟨⟨levels i, by linarith [hlev_strict ‹_›]⟩,
      by specialize hdiffer i; specialize hagree j (levels i) (by linarith [hlev_strict ‹_›]); aesop⟩
  · exact fun _ => ⟨⟨levels j, Nat.lt_succ_self _⟩,
      by specialize hdiffer j; specialize hagree i (levels j) (hlev_strict ‹_›); aesop⟩

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

/--
Discrete topology transfers through `Subtype.val`: if `S` is a discrete subset
of `↥A` (a subtype of `X`), then `Subtype.val '' S` is a discrete subset of `X`.
-/
lemma discreteTopology_image_val {X : Type*} [TopologicalSpace X]
    {A : Set X} (S : Set A) [DiscreteTopology S] :
    DiscreteTopology (Subtype.val '' S : Set X) := by
  rw [discreteTopology_subtype_iff] at *
  simp_all +decide [Filter.inf_principal_eq_bot, nhdsWithin]
  intro x hx hxS; specialize ‹∀ a : X, ∀ b : a ∈ A, ⟨a, b⟩ ∈ S → Sᶜ ∈ 𝓝 ⟨a, b⟩ ⊓ Filter.principal { ⟨a, b⟩ } ᶜ› x hx hxS; simp_all +decide [Filter.mem_inf_principal]
  rw [mem_nhds_subtype] at *
  rcases ‹_› with ⟨u, hu, hu'⟩ ; filter_upwards [hu] with y hy ; specialize hu' ; aesop
