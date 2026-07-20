import WqoContinuousFunctions.ContinuousReducibility.Gluing.Defs
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Gluing as Upper Bound

This file proves the gluing upper bound characterization: `f ≤ ⊔_i g_i` iff there
is a clopen partition with `f|_{A_i} ≤ g_i`.

## Main results

* `gluingFun_upper_bound_forward` — forward direction
* `gluingFun_upper_bound_backward` — backward direction
* `disjoint_union_reduces_gluing` — any function reduces to its own clopen gluing
* `continuous_prepend` / `continuous_unprepend` — continuity of sequence operations
* `continuous_pasting_on_clopen` — pasting lemma for clopen partitions
-/

section GluingUpperBound

/-!
## Proposition 2.17 (Gluingasupperbound)

`f ≤ ⊔_{i ∈ I} g_i` iff there is a clopen partition `(A_i)` of the domain of `f`
such that `f|_{A_i} ≤ g_i` for all `i`.
-/

/--
**Gluing as upper bound (forward direction).** If `f ≤ ⊔_i g_i`, then there
exists a clopen partition of the domain with `f|_{A_i} ≤ g_i`.
-/
theorem gluingFun_upper_bound_forward
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    {A : ℕ → Set (ℕ → ℕ)} {B : ℕ → Set (ℕ → ℕ)}
    {gi : ∀ i, A i → B i}
    (hred : ContinuouslyReduces f (fun (x : GluingSet A) => (GluingFunVal A B gi x))) :
    ∃ (P : ℕ → Set X),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = univ ∧
      ∀ i, ContinuouslyReduces (f ∘ (Subtype.val : P i → X))
        (fun (a : A i) => (gi i a).val) := by
          obtain ⟨σ, hσ, τ, hτ, h_eq⟩ := hred
          refine ⟨fun i => { x : X | (σ x).1 0 = i }, ?_, ?_, ?_⟩
          · exact fun i j hij => Set.disjoint_left.mpr fun x hx hx' => hij <| hx.symm.trans hx'
          · aesop
          · intro i
            refine ⟨?_, ?_, ?_⟩
            use fun x => ⟨unprepend (σ x |>.val), by
              obtain ⟨j, hj1, hj2⟩ := GluingSet_inverse_short A (σ x.val)
              rwa [show j = i from hj1.symm.trans x.prop] at hj2⟩
            all_goals generalize_proofs at *
            · refine Continuous.subtype_mk ?_ ?_
              refine' continuous_pi fun n => _
              exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| hσ.comp <| continuous_subtype_val
            · refine ⟨fun x => τ (prepend i x), ?_, ?_⟩
              · refine hτ.comp ?_ ?_
                · exact Continuous.continuousOn (by continuity)
                · intro x hx
                  obtain ⟨⟨y, hy⟩, rfl⟩ := hx
                  refine ⟨y, ?_⟩
                  change GluingFunVal A B gi (σ y) = _
                  have : (σ y).val 0 = i := hy
                  subst this
                  rfl
              · intro ⟨x, hx⟩
                change f x = τ (prepend i _)
                rw [h_eq x]
                change τ (GluingFunVal A B gi (σ x)) = _
                have h0 : (σ x).val 0 = i := hx
                subst h0
                rfl

/-- **Gluing as upper bound (backward direction).** If there is a clopen partition
with `f|_{A_i} ≤ g_i`, then `f ≤ ⊔_i g_i`. -/
theorem continuous_prepend (n : ℕ) : Continuous (prepend n) := by
  apply continuous_pi
  intro k
  by_cases hk : k = 0
  · subst hk; simp [prepend]; exact continuous_const
  · simp [prepend, hk]; exact continuous_apply _

theorem continuous_unprepend : Continuous unprepend := by
  apply continuous_pi
  intro k
  exact continuous_apply _

/-- The set {y | y 0 = n} is clopen in the product topology on ℕ → ℕ. -/
theorem isClopen_preimage_zero (n : ℕ) : IsClopen {y : ℕ → ℕ | y 0 = n} := by
  have : {y : ℕ → ℕ | y 0 = n} = (fun y => y 0) ⁻¹' {n} := by ext; simp
  rw [this]
  exact IsClopen.preimage (isClopen_discrete _) (continuous_apply 0)

/-- Helper: membership in GluingSet from prepend. -/
theorem mem_gluingSet_prepend {A : ℕ → Set (ℕ → ℕ)} {i : ℕ} {x : ℕ → ℕ}
    (hx : x ∈ A i) : prepend i x ∈ GluingSet A := by
  simp only [GluingSet, Set.mem_iUnion, Set.mem_image]
  exact ⟨i, x, hx, rfl⟩

/-- The index function for the clopen partition: given the cover, find the index. -/
noncomputable def partitionIndex
    {X : Type*} (P : ℕ → Set X) (hcover : (⋃ i, P i) = univ) (x : X) : ℕ :=
  (Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x : x ∈ ⋃ i, P i)).choose

theorem partitionIndex_mem
    {X : Type*} (P : ℕ → Set X) (hcover : (⋃ i, P i) = univ) (x : X) :
    x ∈ P (partitionIndex P hcover x) := by
  exact (Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x : x ∈ ⋃ i, P i)).choose_spec

/--
On a clopen partition, the partition index is locally constant.
-/
theorem partitionIndex_locallyConstant
    {X : Type*} [TopologicalSpace X]
    (P : ℕ → Set X)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = univ) :
    IsLocallyConstant (partitionIndex P hcover) := by
  refine fun n => ?_
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨P (partitionIndex P hcover x), ?_, ?_, ?_⟩
  · intro y hy; have := partitionIndex_mem P hcover y; simp_all +decide [Set.disjoint_left]
    grind
  · exact IsClopen.isOpen (hclopen _)
  · exact partitionIndex_mem P hcover x


/--
Given a clopen partition covering D and continuous functions on each piece,
    the pasted function into a subtype is continuous.
-/
theorem continuous_pasting_on_clopen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (P : ℕ → Set X) (D : Set X)
    (hclopen : ∀ i, IsClopen (P i))
    (_hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = D)
    (g : ∀ i, P i → Y)
    (hg : ∀ i, Continuous (g i))
    (compat : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i)
      (j : ℕ) (hj : x.val ∈ P j), g i ⟨x.val, hi⟩ = g j ⟨x.val, hj⟩) :
    ∃ h : D → Y, Continuous h ∧
      ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i), h x = g i ⟨x.val, hi⟩ := by
  by_contra! h_not_cont
  obtain ⟨h, hh⟩ : ∃ h : D → Y, ∀ x : D, ∀ i : ℕ, ∀ hi : x.val ∈ P i, h x = g i ⟨x.val, hi⟩ := by
    use fun x => g (Classical.choose (Set.mem_iUnion.mp (hcover ▸ x.2))) ⟨x.val, Classical.choose_spec (Set.mem_iUnion.mp (hcover ▸ x.2))⟩
    exact fun x i hi => compat x _ (Classical.choose_spec (Set.mem_iUnion.mp (hcover ▸ x.2))) _ hi
  -- Since $P_i$ are clopen and form a cover of $D$, the preimages of open sets under $h$ are open.
  have h_preimage_open : ∀ U : Set Y, IsOpen U → IsOpen {x : D | h x ∈ U} := by
    intro U hU
    have h_preimage_open : ∀ i, IsOpen {x : D | x.val ∈ P i ∧ h x ∈ U} := by
      intro i
      have h_preimage_open_i : IsOpen {x : P i | g i x ∈ U} := by
        exact hU.preimage (hg i)
      obtain ⟨t, ht, ht'⟩ := h_preimage_open_i
      refine ⟨t ∩ P i, ht.inter (hclopen i |>.2), ?_⟩
      simp_all +decide [Set.ext_iff]
      grind +ring
    convert isOpen_iUnion fun i => h_preimage_open i using 1
    ext x; simp
    exact fun hx => Set.mem_iUnion.mp (hcover.symm ▸ x.2)
  exact h_not_cont h (continuous_def.mpr h_preimage_open) |> fun ⟨x, i, hi, hx⟩ => hx (hh x i hi)

/--
The GluingFunVal at a prepend element equals prepend of the function value.
-/
theorem GluingFunVal_prepend
    (A : ℕ → Set (ℕ → ℕ)) (B : ℕ → Set (ℕ → ℕ))
    (fi : ∀ i, A i → B i)
    (i : ℕ) (a : A i) (hmem : prepend i a.val ∈ GluingSet A) :
    GluingFunVal A B fi ⟨prepend i a.val, hmem⟩ =
      prepend i (fi i a).val := by
  convert rfl

/--
ContinuousOn for a piecewise function on clopen sets.
-/
theorem continuousOn_piecewise_clopen
    [TopologicalSpace Baire]
    {S : Set Baire}
    (τ_i : ℕ → Baire → Baire)
    (S_i : ℕ → Set Baire)
    (_hS_cover : ∀ z ∈ S, ∃ i, z ∈ S_i i)
    (hS_clopen : ∀ i, IsClopen (S_i i))
    (_hτ_agree : ∀ z ∈ S, ∀ i, z ∈ S_i i →
      ∀ j, z ∈ S_i j → τ_i i z = τ_i j z)
    (hτ_cont : ∀ i, ContinuousOn (τ_i i) (S ∩ S_i i))
    (hτ : ∀ z ∈ S, ∃ i, z ∈ S_i i)
    (τ : Baire → Baire)
    (hτ_def : ∀ z ∈ S, ∀ i, z ∈ S_i i → τ z = τ_i i z) :
    ContinuousOn τ S := by
  intro z hz
  obtain ⟨i, hi⟩ := hτ z hz
  have h_cont_at : ContinuousWithinAt (τ_i i) S z := by
    have := hτ_cont i
    convert this.continuousWithinAt (Set.mem_inter hz hi) |> ContinuousWithinAt.mono_of_mem_nhdsWithin <| ?_ using 1
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨S_i i, IsOpen.mem_nhds (hS_clopen i |>.isOpen) hi, by aesop⟩
  refine h_cont_at.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hS_clopen i |>.isOpen.mem_nhds hi)] with x hx hx' using hτ_def x hx i hx'
  · exact hτ_def z hz i hi

/--
Standalone lemma for the equation in backward direction
-/
theorem gluing_backward_eq
    {f : Baire → Baire}
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    {P : ℕ → Set Baire}
    (hcover : (⋃ i, P i) = D)
    (σ_i : ∀ i, P i → A i)
    (τ_i : ℕ → Baire → Baire)
    (heq_i : ∀ (i : ℕ) (x : P i), (P i).restrict f x = τ_i i ((fun a => (gi i a).val) (σ_i i x)))
    (σ_raw : D → Baire)
    (hσ_raw_eq : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i),
      σ_raw x = prepend i (σ_i i ⟨x.val, hi⟩).val)
    (hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A) :
    ∀ x : D, (D.restrict f) x =
      (fun z => τ_i (z 0) (unprepend z))
        (GluingFunVal A B gi ⟨σ_raw x, hσ_raw_mem x⟩) := by
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x.val ∈ P i := by
    exact Set.mem_iUnion.mp (hcover.symm ▸ x.2)
  convert heq_i i ⟨x.val, hi⟩ using 1
  simp +decide only [hσ_raw_eq x i hi]
  convert rfl

/--
Standalone lemma for τ continuity in backward direction
-/
theorem gluing_backward_tau_cont
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    {P : ℕ → Set Baire}
    (hcover : (⋃ i, P i) = D)
    (σ_i : ∀ i, P i → A i)
    (τ_i : ℕ → Baire → Baire)
    (hτ_i : ∀ i, ContinuousOn (τ_i i) (Set.range ((fun a => (gi i a).val) ∘ σ_i i)))
    (σ_raw : D → Baire)
    (hσ_raw_cont : Continuous σ_raw)
    (hσ_raw_eq : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i),
      σ_raw x = prepend i (σ_i i ⟨x.val, hi⟩).val)
    (hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A) :
    ContinuousOn (fun z => τ_i (z 0) (unprepend z))
      (Set.range (GluingFunVal A B gi ∘ (fun x => ⟨σ_raw x, hσ_raw_mem x⟩))) := by
  have hg : Continuous _root_.unprepend := by
    exact continuous_unprepend
  apply continuousOn_piecewise_clopen
  case S_i => exact fun i => { z : Baire | z 0 = i }
  any_goals tauto
  · intro i; constructor
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · have : {z : ℕ → ℕ | z 0 = i} = (fun z => z 0) ⁻¹' {i} := by ext; simp
      rw [this]; exact (isOpen_discrete {i}).preimage (continuous_apply 0)
  · lia
  · intro i
    refine ContinuousOn.congr (f := fun z => τ_i i (unprepend z)) ?_ ?_
    · refine ContinuousOn.comp (hτ_i i) ?_ ?_
      · exact hg.continuousOn
      · intro z hz
        rcases hz with ⟨⟨x, rfl⟩, hx⟩
        rcases Set.mem_iUnion.mp (hcover.symm.subset x.2) with ⟨j, hj⟩ ; specialize hσ_raw_eq x j hj ; aesop
    · intro z hz; aesop

theorem gluingFun_upper_bound_backward
    {f : Baire → Baire}
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    (P : ℕ → Set Baire)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = D)
    (hred : ∀ i, ContinuouslyReduces ((P i).restrict f) (fun (a : A i) => (gi i a).val)) :
    ContinuouslyReduces (D.restrict f) (fun (x : GluingSet A) => (GluingFunVal A B gi x)) := by
  -- Extract components from hred
  choose σ_i hσ_i τ_i hτ_i heq_i using hred
  -- Step 1: Build σ using continuous_pasting_on_clopen
  set g_raw : ∀ i, P i → Baire := fun i x => prepend i (σ_i i x).val with hg_raw_def
  have hg_raw_cont : ∀ i, Continuous (g_raw i) :=
    fun i => (continuous_prepend i).comp (continuous_subtype_val.comp (hσ_i i))
  have hg_raw_compat : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i)
      (j : ℕ) (hj : x.val ∈ P j), g_raw i ⟨x.val, hi⟩ = g_raw j ⟨x.val, hj⟩ := by
    intro x i hi j hj
    by_cases hij : i = j
    · subst hij; rfl
    · exact absurd hj (Set.disjoint_left.mp (hdisj i j hij) hi)
  obtain ⟨σ_raw, hσ_raw_cont, hσ_raw_eq⟩ :=
    continuous_pasting_on_clopen P D hclopen hdisj hcover g_raw hg_raw_cont hg_raw_compat
  have hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ x.prop : x.val ∈ ⋃ i, P i)
    rw [hσ_raw_eq x i hi]
    exact mem_gluingSet_prepend (σ_i i ⟨x.val, hi⟩).prop
  exact ⟨fun x => ⟨σ_raw x, hσ_raw_mem x⟩,
    continuous_induced_rng.mpr hσ_raw_cont,
    fun z => τ_i (z 0) (unprepend z),
    gluing_backward_tau_cont hcover σ_i τ_i hτ_i σ_raw hσ_raw_cont hσ_raw_eq hσ_raw_mem,
    gluing_backward_eq hcover σ_i τ_i heq_i σ_raw hσ_raw_eq hσ_raw_mem⟩

/--
**Corollary 2.18.** `f = ⊔_{P ∈ 𝒫} f|_P ≤ ⊔_{P ∈ 𝒫} f|_P` for any clopen
partition `𝒫` of the domain.
-/
theorem disjoint_union_reduces_gluing
    {f : (ℕ → ℕ) → (ℕ → ℕ)}
    {P : ℕ → Set (ℕ → ℕ)}
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = univ) :
    ContinuouslyReduces f
      (fun (x : GluingSet (fun i => P i)) =>
        (GluingFunVal (fun i => P i) (fun i => Set.range (f ∘ Subtype.val : P i → (ℕ → ℕ)))
          (fun i x => ⟨f x.val, by exact Set.mem_range.mpr ⟨x, rfl⟩⟩) x)) := by
  refine ⟨fun x => ?_, ?_, ?_⟩ <;> norm_num [GluingFunVal]
  exact ⟨_, mem_gluingSet_prepend (partitionIndex_mem P hcover x)⟩
  generalize_proofs at *
  · have h_cont : Continuous (fun x : ℕ → ℕ =>prepend (partitionIndex P hcover x) x) := by
      have h_partitionIndex : IsLocallyConstant (partitionIndex P hcover) := by
        exact partitionIndex_locallyConstant P hclopen hdisj hcover
      have h_cont : Continuous (fun x : ℕ → ℕ => partitionIndex P hcover x) := by
        exact h_partitionIndex.continuous
      generalize_proofs at *
      exact continuous_pi_iff.mpr fun n => by cases n <;> continuity
    generalize_proofs at *
    exact Continuous.subtype_mk h_cont _
  · refine ⟨fun x => x ∘ Nat.succ, ?_, ?_⟩ <;> norm_num [Function.comp]
    · exact Continuous.continuousOn (by continuity)
    · unfold prepend unprepend; aesop

set_option maxHeartbeats 600000 in
/-- Clopen partition combining: if each piece reduces to `Subtype.val` on `B`,
    then `f` reduces to `Subtype.val` on `GluingSet(fun _ => B)`. -/
lemma clopen_partition_to_gluing_reduces
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (P : ℕ → Set A)
    (hP_clopen : ∀ i, IsClopen (P i))
    (hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hP_cover : ⋃ i, P i = Set.univ)
    {B : Set (ℕ → ℕ)}
    (hred : ∀ i, ContinuouslyReduces (fun x : P i => f x.val) (fun x : B => (x.val : ℕ → ℕ))) :
    ContinuouslyReduces f (fun x : GluingSet (fun _ => B) => (x.val : ℕ → ℕ)) := by
  choose σ hσ using hred
  choose τ hτ₁ hτ₂ using fun i => hσ i |>.2
  obtain ⟨σ', hσ'⟩ : ∃ σ' : A → ℕ → ℕ, Continuous σ' ∧ ∀ x : A, σ' x = prepend (partitionIndex P hP_cover x) (σ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩).val := by
    have h_cont : Continuous (fun x : A => partitionIndex P hP_cover x) := by
      convert partitionIndex_locallyConstant P hP_clopen hP_disj hP_cover using 1
      grind [IsLocallyConstant.iff_continuous]
    have h_cont : ∀ i, Continuous (fun x : P i => prepend i (σ i x).val) := by
      intro i; specialize hσ i; exact (by
      exact Continuous.comp (show Continuous fun x : ℕ → ℕ => prepend i x from by exact continuous_pi fun n => by cases n <;> continuity) (show Continuous fun x : P i => (σ i x : ℕ → ℕ) from by exact Continuous.comp (show Continuous fun x : B => (x : ℕ → ℕ) from by continuity) hσ.1))
    have := continuous_pasting_on_clopen P Set.univ hP_clopen hP_disj hP_cover (fun i => fun x : P i => prepend i (σ i x).val) (fun i => h_cont i)
    simp +zetaDelta only [ne_eq, Subtype.forall, mem_univ, forall_const, forall_true_left] at *
    obtain ⟨h, hh₁, hh₂⟩ := this (by
      intro a ha i hi j hj; have := hP_disj i j; simp_all +decide [Set.disjoint_left]
      grind)
    exact ⟨fun x => h ⟨x, trivial⟩, hh₁.comp <| by continuity, fun a ha => hh₂ a ha _ <| partitionIndex_mem P hP_cover _⟩
  have hτ_cont : ContinuousOn (fun z => τ (z 0) (unprepend z)) (Set.range (fun x => σ' x)) := by
    apply continuousOn_piecewise_clopen
    case τ_i => exact fun i z => τ i (unprepend z)
    case S_i => exact fun i => { z : ℕ → ℕ | z 0 = i }
    all_goals norm_num [isClopen_preimage_zero]
    intro i
    refine ContinuousOn.comp (hτ₁ i) ?_ ?_
    · exact Continuous.continuousOn (by exact continuous_pi fun _ => continuous_apply _)
    · rintro _ ⟨⟨x, rfl⟩, hx⟩
      simp_all +decide [prepend]
      use x.val
      use x.2
      use by
        exact hx ▸ partitionIndex_mem P hP_cover x
      generalize_proofs at *
      unfold unprepend prepend; aesop
  have h_eq : ∀ x : A, f x = τ (σ' x 0) (unprepend (σ' x)) := by
    intro x; specialize hτ₂ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩ ; aesop
  use fun x => ⟨σ' x, by
    exact hσ'.2 x ▸ mem_gluingSet_prepend (σ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩ |>.2)⟩
  generalize_proofs at *
  exact ⟨by exact Continuous.subtype_mk hσ'.1 _, _, hτ_cont, fun x => h_eq x⟩


end GluingUpperBound
