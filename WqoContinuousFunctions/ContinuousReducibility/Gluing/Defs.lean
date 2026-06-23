import WqoContinuousFunctions.ContinuousReducibility.Defs
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Gluing Definitions and Continuity of Unions

This file contains the core definitions for disjoint unions and gluing operations,
along with the continuity theorem for relative clopen partitions.

## Main definitions

* `IsDisjointUnion` — disjoint union of a sequence of functions
* `IsRelativeClopenPartition` — a relative clopen partition
* `prepend` / `unprepend` — prepend/strip the first element of a Baire sequence
* `GluingSet` — gluing of sets: ⊔_i (i) ⌢ A_i
* `GluingFunVal` — gluing of functions

## Main results

* `continuous_of_relativeClopenPartition_seq` — continuity from relative clopen partitions
* `RelativeClopenPartition_stable_by_refine` — stability under refinement
-/

section DisjointUnion

/-- A function `f : X → Y` is a disjoint union of the sequence `(fᵢ)` over a clopen
partition `(Aᵢ)` of `X`. (Duplicated from Gluing.lean to avoid circular import.) -/
def IsDisjointUnion {X Y : Type*} [TopologicalSpace X]
    {I : Type*} (f : X → Y) (A : I → Set X) (fi : ∀ i, A i → Y) : Prop :=
  (∀ i, IsClopen (A i)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (⋃ i, A i) = univ ∧
  (∀ i (x : A i), f x.val = fi i x)

end DisjointUnion

section ContinuityOfUnion

/-- A relative clopen partition: pairwise disjoint sets, each relatively open in
their union. -/
def IsRelativeClopenPartition {X : Type*} [TopologicalSpace X]
    {I : Type*} (A : I → Set X) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  ∀ i, IsOpen ((Subtype.val : (⋃ j, A j) → X) ⁻¹' (A i))


/--
**Lemma 2.14 (lem:ContUnion).** If `X` is metrizable, `(A_i)_i` is a countable
relative clopen partition, and each `f_i : A_i → Y` is continuous, then the combined
function on `⋃_i A_i` is continuous (when `X` is metrizable, sequential continuity
suffices).
-/
theorem continuous_of_relativeClopenPartition_seq
    {X Y : Type*} [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y]
    {I : Type*} [Countable I]
    {A : I → Set X} (hA : IsRelativeClopenPartition A)
    {f : (⋃ i, A i) → Y} (hf : ∀ i, Continuous (f ∘ Set.inclusion (Set.subset_iUnion A i))) :
    Continuous f := by
  rw [continuous_def]
  generalize_proofs at *
  intro s hs
  have h_preimage : ∀ i, IsOpen ((f ∘ inclusion (by
  exact Set.subset_iUnion _ _ : A i ⊆ ⋃ i, A i)) ⁻¹' s) := by
    exact fun i => IsOpen.preimage (hf i) hs
  generalize_proofs at *
  choose t ht using h_preimage
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x.val ∈ A i := by
    exact Set.mem_iUnion.mp x.2
  generalize_proofs at *
  refine ⟨Subtype.val ⁻¹' (t i ∩ A i), ?_, ?_, ?_⟩ <;> simp_all +decide [Set.ext_iff]
  · intro y hy; specialize ht i; aesop
  · have := hA.2 i
    exact IsOpen.inter (ht i |>.1.preimage continuous_subtype_val) this



theorem RelativeClopenPartition_stable_by_refine {X : Type*} [TopologicalSpace X] [MetrizableSpace X]
    {I : Type*} [Countable I]
    {A : I → Set X} (hA : IsRelativeClopenPartition A)
    {B : I → Set X} (hB : ∀ i, B i ⊆ A i) :
    IsRelativeClopenPartition B := by
  constructor
  · -- 1. Disjointness
    intro i j hij
    exact (hA.1 i j hij).mono (hB i) (hB j)
  · -- 2. Openness using the Index Function
    intro i
    let UA := ⋃ j, A j
    let UB := ⋃ j, B j

    -- Define the index function ψ : UA → I (I with discrete topology)
    -- This function is continuous because it's constant on each piece of hA
    let ψ : UA → I := fun x => Classical.choose (Set.mem_iUnion.mp x.2)
    -- equip I with discrete topology
    -- 1. Define the topology as discrete (bottom)
    letI : TopologicalSpace I := ⊥
    -- 2. Register that this topology satisfies the DiscreteTopology property
    letI : DiscreteTopology I := ⟨rfl⟩
    have hψ_cont : Continuous ψ := by
      apply continuous_of_relativeClopenPartition_seq hA
      intro j
      -- On piece j, ψ is the constant function j
      apply continuous_const.congr
      intro ⟨x, hxUA⟩
      dsimp [ψ]
      -- Use disjointness of A to show the choose is j
      generalize_proofs h_mem
      have h_piece := Classical.choose_spec h_mem
      by_contra hne
      exact (hA.1 j _ hne).le_bot ⟨hxUA, h_piece⟩

    -- Now consider the inclusion map ι : UB → UA
    let ι : UB → UA := Set.inclusion (Set.iUnion_mono hB)
    have hι_cont : Continuous ι := continuous_inclusion _

    -- B i is the set of points in UB that ψ maps to i
    -- Because I is discrete, {i} is open, so (ψ ∘ ι)⁻¹ {i} is open
    have hBi_eq : (fun x : UB => ψ (ι x)) ⁻¹' {i} = (Set.inclusion (Set.subset_iUnion B i) '' Set.univ) := by
      ext ⟨x, hxUB⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_univ]
      constructor
      · intro hψ
        obtain ⟨j, hxjB⟩ := Set.mem_iUnion.mp hxUB
        have h_index : ψ (ι ⟨x, hxUB⟩) = j := by
          dsimp [ψ, ι]
          generalize_proofs h_mem
          set k := Classical.choose h_mem
          have hk : x ∈ A k := Classical.choose_spec h_mem
          have hj : x ∈ A j := hB j hxjB
          have : k = j := by
            by_contra hne
            exact (hA.1 k j hne).le_bot ⟨hk, hj⟩
          exact this
        -- Since ψ(...) = i (from hψ) and ψ(...) = j (from h_index), we have i = j
        have hij : i = j := hψ.symm.trans h_index
        -- Now substitute j with i in our knowledge that x ∈ B j
        rw [← hij] at hxjB
        -- The goal is ∃ (z : B i), True ∧ inclusion ... z = ⟨x, hxUB⟩
        use ⟨x, hxjB⟩
      · intro hxBi
        -- Unpack the existential: ∃ (z : B i), z.val = x
        obtain ⟨⟨x_val, hx_in_Bi⟩, -, h_eq⟩ := hxBi
        -- h_eq is: x_val = x (after coe simplification)
        simp only [Subtype.mk_eq_mk] at h_eq

        -- Use subst to replace all x_val with x
        subst h_eq
        -- Now hx_in_Bi is automatically transformed into: x ∈ B i

        dsimp [ψ, ι]
        generalize_proofs h_mem
        set k := Classical.choose h_mem
        have hk : x_val ∈ A k := Classical.choose_spec h_mem
        -- hi is proved because x ∈ B i and B i ⊆ A i
        have hi : x_val ∈ A i := hB i hx_in_Bi
        have : k = i := by
          by_contra hne
          exact (hA.1 k i hne).le_bot ⟨hk, hi⟩
        exact this
    -- The goal is to show B i is open in UB.
    -- In Lean, the relative topology means (Subtype.val ⁻¹' B i) is open.
    -- But our hBi_eq is about (inclusion ... '' univ). These are the same!

    have h_iso : Subtype.val ⁻¹' B i = (fun x : UB => ψ (ι x)) ⁻¹' {i} := by
      rw [hBi_eq]
      ext ⟨x, hxUB⟩
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ,
                Subtype.mk_eq_mk]
      constructor
      · intro h
        use ⟨x, h⟩
      · rintro ⟨⟨x_val, h_mem⟩, -, h_eq⟩
        subst h_eq
        exact h_mem

    rw [h_iso]
    apply Continuous.isOpen_preimage
    · exact hψ_cont.comp hι_cont
    · exact isOpen_discrete {i}

end ContinuityOfUnion

section GluingOperation

/-!
## Gluing Operation

The gluing of sets `(A_i)_{i ∈ I}` is `⊔_i (i) ⌢ A_i ⊆ ℕ^ℕ`.
The gluing of functions `(f_i)_{i ∈ I}` maps `(i) ⌢ x ↦ (i) ⌢ f_i(x)`.
-/

/-- Prepend a natural number to an infinite sequence. -/
def prepend (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if k = 0 then n else x (k - 1)

/-- Remove the first element of an infinite sequence (tail). -/
def unprepend (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => x (k + 1)

theorem unprepend_prepend (n : ℕ) (x : ℕ → ℕ) : unprepend (prepend n x) = x := by
  ext k; simp [unprepend, prepend]

theorem prepend_unprepend (x : ℕ → ℕ) : prepend (x 0) (unprepend x) = x := by
  ext k; simp [unprepend, prepend]
  split_ifs with h
  · subst h; rfl
  · congr 1; omega

/-- The gluing of a family of subsets of the Baire space.
`GluingSet A = ⋃_i {(i) ⌢ x | x ∈ A i}`. -/
def GluingSet (A : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  ⋃ i, prepend i '' (A i)


theorem GluingSet_inverse_short (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    ∃ i, x.val 0 = i ∧ unprepend x.val ∈ A i := by
  -- Destructure using the definition of Union and Image directly
  rcases x.prop with ⟨_, ⟨i, rfl⟩, a, ha, h_eq⟩
  use i
  constructor
  · rw [← h_eq]; rfl
  · rw [← h_eq]; exact ha

/-- The gluing of functions on the Baire space.
Given `f_i : A_i → B_i`, the gluing maps `(i) ⌢ x ↦ (i) ⌢ f_i(x)`. -/
def GluingFunVal
    (A : ℕ → Set (ℕ → ℕ)) (B : ℕ → Set (ℕ → ℕ))
    (fi : ∀ i, A i → B i)
    (x : GluingSet A) : ℕ → ℕ :=
  let i := x.val 0
  have hmem : unprepend x.val ∈ A i := by
    have hx := x.prop
    simp only [GluingSet, Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨j, a, ha, hja⟩ := hx

    -- Prove j = i by evaluating the 0th index
    have hij : j = i := by
      -- i is definitionally x.val 0, and hja is `prepend j a = x.val`
      have h0 : (prepend j a) 0 = x.val 0 := by rw [hja]
      exact h0

    subst hij
    rw [← hja, unprepend_prepend]
    exact ha

  -- The returned sequence computes using only the computable parts
  prepend i (fi i ⟨unprepend x.val, hmem⟩).val

end GluingOperation

section GluingBasicFacts

/-!
## Fact 2.16 (BasicsOnGluing)

1. Gluing preserves continuity, injectivity, surjectivity, and scatteredness.
2. CB(⊔_i f_i) = sup_i CB(f_i).
3. Gluing commutes with identity.
-/

/--
These require detailed work with the Baire space topology; statements are recorded.

Gluing commutes with identity: `id_{⊔_i X_i} = ⊔_i id_{X_i}`.
-/
theorem gluingFun_id (A : ℕ → Set (ℕ → ℕ)) :
    GluingFunVal A A (fun _ => id) = Subtype.val := by
  ext x
  unfold GluingFunVal
  unfold prepend; induction ‹ℕ› <;> aesop

/-- **Fact 2.16, Part 1 (continuity).**  The gluing of continuous functions is
continuous.  If each block `fᵢ : Aᵢ → Bᵢ` is continuous, then the glued map
`(i)⌢x ↦ (i)⌢fᵢ(x)` on `GluingSet A` is continuous.

**Proof strategy (informal).**  `GluingSet A` is partitioned by the first
coordinate into the relatively-clopen blocks `{x | x 0 = i}`; on each block the
glued map agrees with `prepend i ∘ fᵢ ∘ unprepend`, a composition of continuous
maps.  Continuity then follows from the pasting lemma
`continuous_of_relativeClopenPartition_seq`.

TODO (geometry, Fact 2.16): discharge this `sorry`. -/
theorem gluingFunVal_preserves_continuity
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun (x : GluingSet A) => GluingFunVal A B f x) := by
  -- Continuity of the basic `prepend`/`unprepend` reindexings (proved here since the named
  -- lemmas live downstream in `Gluing/UpperBound.lean`).
  have hpre : ∀ n, Continuous (prepend n) := by
    intro n; apply continuous_pi; intro k; dsimp [prepend]
    split_ifs with h
    · exact continuous_const
    · exact continuous_apply (k - 1)
  have hunpre : Continuous unprepend := by
    apply continuous_pi; intro k; exact continuous_apply (k + 1)
  -- Present `GluingSet A = ⋃ i, prepend i '' (A i)` as a relative clopen partition by first
  -- coordinate, and use the pasting lemma `continuous_of_relativeClopenPartition_seq`.
  have hpart : IsRelativeClopenPartition (fun i => prepend i '' (A i)) := by
    refine ⟨?_, ?_⟩
    · -- distinct blocks are disjoint: they disagree at coordinate `0`.
      intro i j hij
      rw [Set.disjoint_left]
      rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hjb⟩
      have hji : j = i := by have := congr_fun hjb 0; simpa [prepend] using this
      exact hij hji.symm
    · -- each block is relatively clopen: on the union it is `{z | z 0 = i}`.
      intro i
      have hset : (Subtype.val : (⋃ j, prepend j '' (A j)) → (ℕ → ℕ)) ⁻¹' (prepend i '' (A i))
          = Subtype.val ⁻¹' {z : ℕ → ℕ | z 0 = i} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨a, ha, hax⟩; rw [← hax]; rfl
        · intro hx0
          obtain ⟨j, a, ha, hax⟩ := Set.mem_iUnion.mp x.2
          have hji : j = i := by rw [← hax] at hx0; simpa [prepend] using hx0
          exact ⟨a, hji ▸ ha, hji ▸ hax⟩
      rw [hset]
      exact (baire_fiber_isClopen 0 i).2.preimage continuous_subtype_val
  apply continuous_of_relativeClopenPartition_seq hpart
  intro i
  -- On block `i` the glued map is `prepend i ∘ (·).val ∘ f i ∘ (unprepend into A i)`.
  have hblk : ∀ (y : (prepend i '' (A i) : Set (ℕ → ℕ))), unprepend y.val ∈ A i := by
    rintro ⟨_, a, ha, rfl⟩; rw [unprepend_prepend]; exact ha
  have heq : (fun (x : GluingSet A) => GluingFunVal A B f x) ∘
        Set.inclusion (Set.subset_iUnion (fun i => prepend i '' (A i)) i)
      = fun y => prepend i (f i ⟨unprepend y.val, hblk y⟩).val := by
    funext y
    -- Destructure `y = ⟨prepend i a, …⟩`; then both sides reduce definitionally
    -- (`unprepend (prepend i a) = a`, and the membership proofs are irrelevant).
    obtain ⟨_, a, ha, rfl⟩ := y
    rfl
  rw [heq]
  exact (hpre i).comp (continuous_subtype_val.comp
    ((hf i).comp (Continuous.subtype_mk (hunpre.comp continuous_subtype_val) hblk)))

/-- **Fact 2.16, Part 2 (scatteredness).**  The gluing of scattered functions is
scattered.  If each block `fᵢ : Aᵢ → Bᵢ` is scattered (as a `ℕ → ℕ`-valued map),
then the glued map on `GluingSet A` is scattered.

**Proof strategy (informal).**  Given a nonempty `S ⊆ GluingSet A`, pick any
`y ∈ S`; its first coordinate `i = y 0` selects a block.  Apply scatteredness of
`fᵢ` to the projection of `S ∩ {first coord = i}` into `Aᵢ` to obtain an open set
on which the block — hence the glued map — is constant.  (This mirrors
`pointedGluing_scattered`, without the `0^ω` base-point case.)

TODO (geometry, Fact 2.16): discharge this `sorry`. -/
theorem gluingFun_scattered
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ))) :
    ScatteredFun (fun (x : GluingSet A) => GluingFunVal A B f x) := by
  have hunpre : Continuous unprepend := by
    apply continuous_pi; intro k; exact continuous_apply (k + 1)
  -- `GluingFunVal` on a `prepend i a` reduces definitionally.
  have block_eval : ∀ (i : ℕ) (a : ℕ → ℕ) (ha : a ∈ A i) (hmem : prepend i a ∈ GluingSet A),
      GluingFunVal A B f ⟨prepend i a, hmem⟩ = prepend i (f i ⟨a, ha⟩).val :=
    fun i a ha hmem => by convert rfl
  have mem_Ai : ∀ (i : ℕ) (z : GluingSet A), z.val 0 = i → unprepend z.val ∈ A i := by
    intro i z hz0
    obtain ⟨j, hj0, hji⟩ := GluingSet_inverse_short A z
    rwa [show j = i from by rw [← hj0]; exact hz0] at hji
  intro S hS_nonempty
  obtain ⟨y, hyS⟩ := hS_nonempty
  obtain ⟨i, hi0, hyi⟩ := GluingSet_inverse_short A y
  obtain ⟨V, hV_open, hV_ne, hV_const⟩ := hf_scat i
    {z : A i | ∃ w ∈ S ∩ {z : GluingSet A | z.val 0 = i}, unprepend w.val = z.val}
    ⟨⟨unprepend y.val, hyi⟩, ⟨y, ⟨hyS, hi0⟩, rfl⟩⟩
  obtain ⟨V₀, hV₀_open, rfl⟩ := hV_open
  refine ⟨{z : GluingSet A | z.val 0 = i} ∩ {z : GluingSet A | unprepend z.val ∈ V₀},
    ?_, ?_, ?_⟩
  · -- open: the first-coordinate fibre is clopen; the second factor is a preimage of `V₀`.
    refine IsOpen.inter ?_ (hV₀_open.preimage (hunpre.comp continuous_subtype_val))
    exact (baire_fiber_isClopen 0 i).2.preimage continuous_subtype_val
  · -- the witness set meets `S`.
    obtain ⟨z, hzV, w, ⟨hwS, hwBlock⟩, hwz⟩ := hV_ne
    exact ⟨w, ⟨⟨hwBlock, by show unprepend w.val ∈ V₀; rw [hwz]; exact hzV⟩, hwS⟩⟩
  · -- the glued map is constant on the witness set ∩ S.
    intro x hx x' hx'
    obtain ⟨ax, hax, hxe⟩ : ∃ a ∈ A i, prepend i a = x.val :=
      ⟨unprepend x.val, mem_Ai i x hx.1.1, by rw [← hx.1.1]; exact prepend_unprepend x.val⟩
    obtain ⟨ax', hax', hxe'⟩ : ∃ a ∈ A i, prepend i a = x'.val :=
      ⟨unprepend x'.val, mem_Ai i x' hx'.1.1, by rw [← hx'.1.1]; exact prepend_unprepend x'.val⟩
    have haxeq : ax = unprepend x.val := by rw [← hxe, unprepend_prepend]
    have haxeq' : ax' = unprepend x'.val := by rw [← hxe', unprepend_prepend]
    have ex : GluingFunVal A B f x = prepend i (f i ⟨ax, hax⟩).val := by
      rw [show x = (⟨prepend i ax, by rw [hxe]; exact x.2⟩ : GluingSet A) from Subtype.ext hxe.symm]
      exact block_eval i ax hax _
    have ex' : GluingFunVal A B f x' = prepend i (f i ⟨ax', hax'⟩).val := by
      rw [show x' = (⟨prepend i ax', by rw [hxe']; exact x'.2⟩ : GluingSet A) from
            Subtype.ext hxe'.symm]
      exact block_eval i ax' hax' _
    show GluingFunVal A B f x = GluingFunVal A B f x'
    rw [ex, ex']
    congr 1
    refine hV_const ⟨ax, hax⟩ ⟨?_, ?_⟩ ⟨ax', hax'⟩ ⟨?_, ?_⟩
    · show ax ∈ V₀; rw [haxeq]; exact hx.1.2
    · exact ⟨x, ⟨hx.2, hx.1.1⟩, haxeq.symm⟩
    · show ax' ∈ V₀; rw [haxeq']; exact hx'.1.2
    · exact ⟨x', ⟨hx'.2, hx'.1.1⟩, haxeq'.symm⟩

end GluingBasicFacts
