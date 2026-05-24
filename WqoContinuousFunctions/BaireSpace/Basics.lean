import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib.Topology.NatEmbedding
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Disjointed
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Baire Space Basics

This file defines the Baire space `ℕ → ℕ` with the product topology and establishes
its basic topological properties, including:

* Clopen basis from cylinder sets
* Countable topological basis
* Disjointification of clopen covers
-/


/-- The constant zero sequence `0^ω ∈ ℕ → ℕ`. -/
def zeroStream : ℕ → ℕ := fun _ => 0

abbrev Baire := ℕ → ℕ

section ClopenBasis


def nbhd (x : Baire) (n : ℕ) : Set Baire :=
  {h : Baire | ∀ i ∈ Finset.range n, h i = x i}

/-- neighborhood of a point in the Baire space is clopen -/
lemma baire_nbhd_isClopen (x : Baire) (n : ℕ) :
    IsClopen (nbhd x n) := by
  -- Rewrite as a finite intersection
  have h_eq : nbhd x n = ⋂ i ∈ Finset.range n, {h : Baire | h i = x i} := by
    ext h
    simp [nbhd]
  rw [h_eq]

  -- PROOF 1: The intersection is Closed
  have h_closed : IsClosed (⋂ i ∈ Finset.range n, {h : Baire | h i = x i}) := by
    apply isClosed_biInter
    intro i _
    exact isClosed_eq (continuous_apply i) continuous_const

  -- PROOF 2: The intersection is Open
  have h_open : IsOpen (⋂ i ∈ Finset.range n, {h : Baire | h i = x i}) := by
    apply Set.Finite.isOpen_biInter (Finset.finite_toSet (Finset.range n))
    intro i _
    have h_preimage : {h : Baire | h i = x i} = (fun h => h i) ⁻¹' {x i} := rfl
    rw [isOpen_pi_iff]
    exact fun h hf => ⟨{ i }, fun _ => { x i }, by aesop⟩
  -- Combine them explicitly (IsClopen is defined as IsClosed ∧ IsOpen)
  exact ⟨h_closed, h_open⟩


def nbhd' (A : Set Baire) (x : A) (n : ℕ) : Set A :=
  {h : A | ∀ i ∈ Finset.range n, h.val i = x.val i}

lemma baire_nbhd'_isClopen (A : Set Baire) (x : A) (n : ℕ) :
    IsClopen (nbhd' A x n) := by
  -- nbhd' A x n is the preimage of nbhd x.val n under Subtype.val
  have h_eq : nbhd' A x n = Subtype.val ⁻¹' nbhd x.val n := by
    ext h
    simp [nbhd', nbhd]
  rw [h_eq]
  -- Preimage of a clopen set under a continuous map is clopen
  exact (baire_nbhd_isClopen x.val n).preimage continuous_subtype_val

/--
In the Baire space ℕ → ℕ, the set `{f | f i = a}` is clopen for every `i a : ℕ`.
-/
lemma baire_fiber_isClopen (i a : ℕ) :
    IsClopen {f : ℕ → ℕ | f i = a} := by
  constructor
  · exact isClosed_eq (continuous_apply i) continuous_const
  · rw [isOpen_pi_iff]
    exact fun f hf => ⟨{ i }, fun _ => { a }, by aesop⟩

/--
A cylinder set (finite intersection of fibers) in the Baire space is clopen.
-/
lemma baire_cylinder_isClopen (s : Finset ℕ) (g : ℕ → ℕ) :
    IsClopen {f : ℕ → ℕ | ∀ i ∈ s, f i = g i} := by
  induction s using Finset.induction <;> simp_all +decide [Set.setOf_and]
  · exact isClopen_univ
  · exact IsClopen.inter (baire_fiber_isClopen _ _) ‹_›

/--
Singletons form a topological basis for the discrete topology on ℕ.
-/
lemma nat_singleton_basis :
    IsTopologicalBasis {s : Set ℕ | ∃ n, s = {n}} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · aesop
  · exact fun a u ha hu => ⟨{ a }, ⟨a, rfl⟩, by simp, by simpa⟩

/--
Neighbourhoods given by initial segments form a neighbourhood basis in subspace of the Baire space.
-/
lemma nbhd_basis' (A : Set (ℕ → ℕ)) (x : A) : ∀ U : Set A, IsOpen U → x ∈ U →
    ∃ n, nbhd' A x n ⊆ U := by
  intro U hU hxU
  -- U is open in the subspace topology on A, so U = Subtype.val ⁻¹' V
  -- for some open V in ℕ → ℕ
  rw [isOpen_induced_iff] at hU
  obtain ⟨V, hV_open, hV_eq⟩ := hU
  -- x.val ∈ V
  have hxV : x.val ∈ V := by
    have : x ∈ Subtype.val ⁻¹' V := hV_eq ▸ hxU
    exact this
  -- The product topology on ℕ → ℕ has a basis of cylinder sets.
  -- V is open and contains x.val, so some cylinder nbhd x.val n ⊆ V.
  -- This follows from the neighborhood filter having cylinders as a basis.
  rw [isOpen_pi_iff] at hV_open
  -- hV_open : ∀ y ∈ V, ∃ I : Finset ℕ, ∃ U : ℕ → Set ℕ,
  --   (∀ i ∈ I, IsOpen (U i) ∧ y i ∈ U i) ∧ Set.pi I U ⊆ V
  obtain ⟨I, F, hF, hpi⟩ := hV_open x.val hxV
  -- I is a finite set; take n = I.sup id + 1 so that I ⊆ Finset.range n
  -- Then nbhd x.val n ⊆ Set.pi I F ⊆ V
  use I.sup id + 1
  -- Show nbhd' A x n ⊆ U = Subtype.val ⁻¹' V
  intro a ha
  rw [← hV_eq]
  -- Need: a.val ∈ V
  apply hpi
  -- Need: a.val ∈ Set.pi I F, i.e. ∀ i ∈ I, a.val i ∈ F i
  intro i hi
  -- a ∈ nbhd' A x n means a.val agrees with x.val on Finset.range n
  -- and i ∈ I ⊆ Finset.range n since i ≤ I.sup id < n
  have hi_lt : i < I.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have hi_range : i ∈ Finset.range (I.sup id + 1) :=
    Finset.mem_range.mpr hi_lt
  have hagree : a.val i = x.val i := ha i hi_range
  rw [hagree]
  exact (hF i hi).2

lemma nbhd_basis (x : Baire) : ∀ U : Set Baire, IsOpen U → x ∈ U →
    ∃ n, nbhd x n ⊆ U := by
  intro U hU hxU
  rw [isOpen_pi_iff] at hU
  obtain ⟨I, F, hF, hpi⟩ := hU x hxU
  refine ⟨I.sup id + 1, fun a ha => hpi (fun i hi => ?_)⟩
  have hi_range : i ∈ Finset.range (I.sup id + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  rw [ha i hi_range]
  exact (hF i hi).2

/--
The Baire space has a topological basis consisting of clopen sets.
-/
lemma baire_has_clopen_basis :
    ∃ B : Set (Set (ℕ → ℕ)), IsTopologicalBasis B ∧ B.Countable ∧ ∀ s ∈ B, IsClopen s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  refine { s : Set (ℕ → ℕ) | ∃ (F : Finset ℕ) (g : ℕ → ℕ), s = { f : ℕ → ℕ | ∀ i ∈ F, f i = g i } }
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · simp +zetaDelta at *
      intro u F g hu; rw [hu] ; exact baire_cylinder_isClopen F g |>.isOpen
    · intro a u ha hu
      rw [isOpen_pi_iff] at hu
      obtain ⟨I, u, hu₁, hu₂⟩ := hu a ha
      refine ⟨_, ⟨I, a, rfl⟩, ?_, ?_⟩ <;> simp_all +decide [Set.subset_def]
  · -- The set of finite subsets of ℕ is countable.
    have h_finite_subsets_countable : Set.Countable {F : Finset ℕ | True} := by
      exact Set.countable_univ
    refine Set.Countable.mono ?_ (h_finite_subsets_countable.biUnion fun F _ => Set.countable_range (fun g : F → ℕ => { f : ℕ → ℕ | ∀ i : F, f i = g i }))
    intro s hs; obtain ⟨F, g, rfl⟩ := hs; simp +decide [Set.ext_iff]
    exact ⟨F, fun i => g i, fun x => ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩⟩
  · rintro s ⟨F, g, rfl⟩ ; exact baire_cylinder_isClopen F g

/--
In the Baire space, every open set is a countable union of clopen sets.
-/
lemma baire_open_eq_countable_union_clopen {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    ∃ C : ℕ → Set (ℕ → ℕ), (∀ k, IsClopen (C k)) ∧ U = ⋃ k, C k := by
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := baire_has_clopen_basis
  have h_union : U = ⋃₀ { s ∈ B | s ⊆ U } := by
    exact hB₁.open_eq_sUnion' hU
  have h_countable : Set.Countable { s ∈ B | s ⊆ U } := by
    exact hB₂.mono fun s hs => hs.1
  have := h_countable.exists_eq_range
  by_cases h : { s ∈ B | s ⊆ U }.Nonempty
  · obtain ⟨f, hf⟩ := this h
    refine ⟨f, ?_, ?_⟩
    · exact fun k => hB₃ _ <| hf.symm.subset (Set.mem_range_self k) |>.1
    · convert h_union using 1
      simp +decide [hf]
  · simp_all +singlePass [Set.not_nonempty_iff_eq_empty]
    exact ⟨fun _ => ∅, fun _ => by simp +decide [IsClopen], by simp +decide⟩

/--
In any subspace of the Baire space, every open set is a countable union of
    sets that are clopen in the subspace.
-/
lemma subspace_open_eq_countable_union_clopen (A : Set (ℕ → ℕ))
    {U : Set A} (hU : IsOpen U) :
    ∃ C : ℕ → Set A, (∀ k, IsClopen (C k)) ∧ U = ⋃ k, C k := by
  obtain ⟨V, hV⟩ : ∃ V : Set (ℕ → ℕ), IsOpen V ∧ U = Subtype.val ⁻¹' V := by
    obtain ⟨V, hV₁, hV₂⟩ := hU
    exact ⟨V, hV₁, hV₂.symm⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (ℕ → ℕ), (∀ k, IsClopen (C k)) ∧ V = ⋃ k, C k := by
    exact baire_open_eq_countable_union_clopen hV.1
  use fun k => Subtype.val ⁻¹' C k
  simp_all +decide [Set.ext_iff]
  intro k; specialize hC; have := hC.1 k; exact ⟨this.1.preimage continuous_subtype_val, this.2.preimage continuous_subtype_val⟩

end ClopenBasis

section DisjointedClopen

/--
The `disjointed` of a sequence of clopen sets is clopen.
-/
lemma disjointed_clopen {X : Type*} [TopologicalSpace X]
    (f : ℕ → Set X) (hf : ∀ n, IsClopen (f n)) (n : ℕ) :
    IsClopen (disjointed f n) := by
  convert IsClopen.diff (hf n) _
  induction' (Finset.Iio n) using Finset.induction <;> simp_all +decide [Finset.sup_insert]
  · exact isClopen_empty
  · exact IsClopen.union (hf _) ‹_›

end DisjointedClopen

/-! **Helper (clopen basis).** In a metrizable, separable, totally disconnected space,
every open set containing a point has a clopen subset containing that point.
This is a consequence of de Groot's theorem (metrizable + TD → ultra-metrizable)
and the fact that balls in an ultrametric space are clopen.
we only use this result in the specific case of subspace of the Baire space.
This specific result is proved below.

lemma exists_clopen_subset_of_open {X : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  sorry
 -/

/--
In the Baire space, every open set containing a point has a clopen subset
containing that point. Follows from `baire_has_clopen_basis`.
-/
lemma baire_exists_clopen_subset_of_open
    (x : Baire) (U : Set Baire) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set Baire, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨B, hB_basis, _, hB_clopen⟩ := baire_has_clopen_basis
  have hU_nhds : U ∈ nhds x := hU.mem_nhds hx
  rw [hB_basis.mem_nhds_iff] at hU_nhds
  obtain ⟨V, hV_in_B, hx_in_V, hV_sub_U⟩ := hU_nhds
  exact ⟨V, hB_clopen V hV_in_B, hx_in_V, hV_sub_U⟩

/--
In a subspace of the Baire space, every open set containing a point has a
clopen subset containing that point.
-/
lemma baire_subspace_exists_clopen_subset_of_open
    (A : Set Baire) (x : A) (U : Set A) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set A, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  rcases hU with ⟨V, hV, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ x.val ∈ W ∧ W ⊆ V := by
    exact baire_exists_clopen_subset_of_open x.val V hV hx
  refine ⟨Subtype.val ⁻¹' W, ?_, ?_, ?_⟩
  · exact hW.1.preimage continuous_subtype_val
  · aesop
  · exact Set.preimage_mono hW.2.2



/-! ## §1  Basic clopen neighborhoods indexed by finite sequences -/

/--
It is often useful to index basic neighborhoods by finite sequences.
`BaNbhd s` is the basic clopen neighborhood determined by the finite sequence
`s : Fin n → ℕ`: the set of all `h : ℕ → ℕ` whose first `n` values agree with `s`.
This is the analogue of `nbhd x n = {h | ∀ i < n, h i = x i}` but parametrized
by an *abstract* finite sequence rather than a point in Baire space.
Of course `nbhd x n` = `BaNbhd x|n` where `x|n`
is the finite sequence obtained by restricting `x: ℕ → ℕ ` to `Fin n`  -/
def BaNbhd {n : ℕ} (s : Fin n → ℕ) : Set (ℕ → ℕ) :=
  {h : ℕ → ℕ | ∀ i : Fin n, h i = s i}

/-- `BaNbhd` of the empty sequence is the whole Baire space. -/
lemma BaNbhd_empty : BaNbhd (Fin.elim0 : Fin 0 → ℕ) = Set.univ := by
  simp [BaNbhd]

lemma BaNbhd.as_inter {n : ℕ} (s : Fin n → ℕ)
  : BaNbhd s = ⋂ i : Fin n, {h : ℕ → ℕ | h i = s i} := by
    ext h; simp [BaNbhd, Set.mem_iInter]

/-- `BaNbhd s` is open. -/
lemma BaNbhd_isOpen {n : ℕ} (s : Fin n → ℕ) : IsOpen (BaNbhd s) := by
  -- BaNbhd s = ⋂ i : Fin n, {h | h i = s i}
  -- Each {h | h i = s i} = (fun h => h i) ⁻¹' {s i} is open (discrete codomain).
  have h_open : IsOpen (⋂ i : Fin n, {h : Baire | h i = s i}) := by
    apply isOpen_iInter_of_finite
    intro i
    have h_preimage : {h : Baire | h i = s i} = (fun h => h (i : ℕ)) ⁻¹' {s i} := rfl
    rw [h_preimage]
    exact (isOpen_discrete {s i}).preimage (continuous_apply (i : ℕ))
  rw[BaNbhd.as_inter]
  exact h_open

/-- `BaNbhd s` is closed (it is also the intersection of finitely many closed sets). -/
lemma BaNbhd_isClosed {n : ℕ} (s : Fin n → ℕ) : IsClosed (BaNbhd s) := by

  have h_closed : IsClosed (⋂ i : Fin n, {h : Baire | h i = s i}) := by
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_apply (i : ℕ)) continuous_const
  rw [BaNbhd.as_inter]
  exact h_closed

/-- `BaNbhd s` is clopen. -/
lemma BaNbhd_isClopen {n : ℕ} (s : Fin n → ℕ) : IsClopen (BaNbhd s) :=
  ⟨BaNbhd_isClosed s, BaNbhd_isOpen s⟩

/-- `BaNbhd s` is nonempty: the sequence `s` extended by zeros belongs to it. -/
lemma BaNbhd_nonempty {n : ℕ} (s : Fin n → ℕ) : (BaNbhd s).Nonempty := by
  use fun k => if h : k < n then s ⟨k, h⟩ else 0
  simp [BaNbhd]

-- Prefix order on finite sequences

/-- `s` is a prefix of `t` (or `t` extends `s`): `n ≤ m` and the first `n` values
of `t` agree with `s`. -/
def IsPrefix {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ) : Prop :=
  ∃ h : n ≤ m, ∀ i : Fin n, s i = t ⟨i, i.isLt.trans_le h⟩

/-- If `s` is a prefix of `t` then `BaNbhd t ⊆ BaNbhd s`. -/
lemma BaNbhd_antitone {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) : BaNbhd t ⊆ BaNbhd s := by
  intro h hh
  simp only [BaNbhd, Set.mem_setOf_eq] at *
  intro i
  rw [hpre.2 i, ← hh ⟨i, i.isLt.trans_le hpre.1⟩]

-- Extension of finite sequences

/-- Extend a finite sequence `s : Fin n → ℕ` by appending the value `k`. -/
def extendSeq {n : ℕ} (s : Fin n → ℕ) (k : ℕ) : Fin (n + 1) → ℕ :=
  Fin.snoc s k
/-- The extension `extendSeq s k` extends `s`. -/
lemma extendSeq_isPrefix {n : ℕ} (s : Fin n → ℕ) (k : ℕ) :
    IsPrefix s (extendSeq s k) :=
  ⟨Nat.le_succ n, fun i => by
    simp only [extendSeq, Fin.snoc]
    split_ifs with h
    · congr 1
    · exact absurd i.isLt (by omega)⟩

/-- `BaNbhd`s for different extensions are pairwise disjoint. -/
lemma BaNbhd_extend_disjoint {n : ℕ} (s : Fin n → ℕ) (j k : ℕ) (hjk : j ≠ k) :
    Disjoint (BaNbhd (extendSeq s j)) (BaNbhd (extendSeq s k)) := by
  simp only [Set.disjoint_left, BaNbhd, Set.mem_setOf_eq, extendSeq]
  intro h hj hk
  have hj' : h n = j := by
    have := hj ⟨n, Nat.lt_succ_self n⟩
    simp [Fin.snoc, Fin.last] at this
    exact this
  have hk' : h n = k := by
    have := hk ⟨n, Nat.lt_succ_self n⟩
    simp [Fin.snoc, Fin.last] at this
    exact this
  exact hjk (by omega)
