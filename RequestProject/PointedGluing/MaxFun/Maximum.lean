import RequestProject.PointedGluing.ClopenPartitionReduces
import RequestProject.PrelimMemo.Scattered.Decomposition

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Proof of maxFun_is_maximum (Proposition 3.9)

The proof is by strong induction on α.
Item 1 (MaxFun α is maximum for CB ≤ α) uses Item 2 at smaller ordinals.
Item 2 (SuccMaxFun α is maximum for simple functions with CB ≤ α+1) uses Item 1 at α.
-/

/--
CBLevel is invariant under homeomorphisms.
-/
lemma CBLevel_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : Y → Z) (β : Ordinal.{0}) :
    CBLevel (f ∘ e) β = e ⁻¹' (CBLevel f β) := by
  induction' β using Ordinal.limitRecOn with β ih <;> simp_all +decide [CBLevel]
  · congr! 1
    ext; simp +decide [isolatedLocus]
    intro hx
    constructor <;> rintro ⟨U, hU, hx, hU'⟩
    · exact ⟨e '' U, e.isOpen_image.mpr hU, Set.mem_image_of_mem _ hx, by simpa [Set.image_preimage_eq_inter_range] using hU'⟩
    · exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, fun y hy hy' => hU' _ hy hy'⟩
  · simp +decide [Set.preimage_iInter]

/--
The ray function of a scattered function is scattered and has CB ≤ α,
    hence reduces to MaxFun α via h1.
-/
lemma ray_reduces_to_maxFun
    (α : Ordinal.{0}) (_hα : α < omega1)
    (h1 : ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
      ContinuouslyReduces f (MaxFun α))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f) (hscat : ScatteredFun f)
    (β : Ordinal.{0}) (hβ : β ≤ α)
    (y : ℕ → ℕ)
    (hy_simple : ∀ x ∈ CBLevel f β, f x = y)
    (j : ℕ) :
    ContinuouslyReduces
      (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val)
      (MaxFun α) := by
  let A' : Set (ℕ → ℕ) := {x | ∃ (h : x ∈ A), f ⟨x, h⟩ ∈ RaySet Set.univ y j}
  let f' : A' → ℕ → ℕ := fun x => f ⟨x.val, x.prop.choose⟩
  let e : {a : A | f a ∈ RaySet Set.univ y j} → A' :=
    fun x => ⟨x.val.val, ⟨x.val.prop, x.prop⟩⟩
  have hfe : ∀ x, f x.val = f' (e x) := fun x => by simp [f', e]
  have he : Continuous e := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  suffices h : ContinuouslyReduces f' (MaxFun α) by
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := h
    refine ⟨σ ∘ e, hσ.comp he, τ, ?_, fun x => ?_⟩
    · exact hτ.mono (by rintro z ⟨x, rfl⟩; exact ⟨e x, rfl⟩)
    · show f x.val = τ (MaxFun α ((σ ∘ e) x))
      rw [hfe x, Function.comp_apply]
      exact heq (e x)
  apply h1
  · -- f' is continuous
    exact hf.comp (continuous_subtype_val |>.subtype_mk _)
  · -- f' is scattered
    intro S hS
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hscat (Set.image (fun x : A' => ⟨x, x.2.1⟩) S) (Set.Nonempty.image _ hS)
    obtain ⟨x, hx⟩ := hU₂
    obtain ⟨y, hy, rfl⟩ := hx.2
    refine ⟨{ x : A' | ⟨x, x.2.1⟩ ∈ U }, ?_, ?_, ?_⟩
    · exact hU₁.preimage (continuous_subtype_val.subtype_mk _)
    · exact ⟨y, hx.1, hy⟩
    · grind
  · -- CBLevel f' γ = ∅ for γ ≥ α
    intro γ hγ
    -- Build a homeomorphism between the ray subtype and A'
    let e_inv : A' → {a : A | f a ∈ RaySet Set.univ y j} :=
      fun x => ⟨⟨x.val, x.prop.choose⟩, x.prop.choose_spec⟩
    have he_inv : Continuous e_inv := Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val _) _
    have hee : ∀ x, e (e_inv x) = x := fun x => by simp [e, e_inv]
    have hee' : ∀ x, e_inv (e x) = x := fun x => by
      ext; simp [e, e_inv]
    let E : {a : A | f a ∈ RaySet Set.univ y j} ≃ₜ A' :=
      { toFun := e
        invFun := e_inv
        left_inv := hee'
        right_inv := hee
        continuous_toFun := he
        continuous_invFun := he_inv }
    -- f' = (fun x => f x.val) ∘ E.symm, so CBLevel f' = image under E of CBLevel of ray fun
    have hf'_eq : f' = (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val) ∘ E.symm := by
      ext x; simp [f', E, e_inv]
    rw [hf'_eq, CBLevel_homeomorph]
    -- CBLevel of ray function at γ is empty
    have h_ray_empty : CBLevel (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val) β = ∅ :=
      ray_CBLevel_alpha_empty f hf β y hy_simple j
    have h_empty : CBLevel (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val) γ = ∅ :=
      Set.eq_empty_of_subset_empty (h_ray_empty ▸ CBLevel_antitone _ (hβ.trans hγ))
    rw [h_empty]; simp

/--
Helper: ScatteredFun follows from having a finite CB level.
-/
lemma scatteredFun_of_CBLevel_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (β : Ordinal.{0}) (h : CBLevel f β = ∅) : ScatteredFun f := by
  convert scattered_of_empty_perfectKernel f _
  exact Set.eq_empty_of_forall_notMem fun x hx => by have := Set.mem_iInter.mp hx β; aesop

/--
Helper: ray reduces to sub-gluing (for pointedGluing_upper_bound).
-/
lemma ray_to_sub_gluing
    (α : Ordinal.{0}) (hα : α < omega1)
    (h1 : ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
      ContinuouslyReduces f (MaxFun α))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f) (hscat : ScatteredFun f)
    (β : Ordinal.{0}) (hβ : β ≤ α)
    (y : ℕ → ℕ)
    (hy_simple : ∀ x ∈ CBLevel f β, f x = y)
    (j : ℕ) :
    ContinuouslyReduces
      (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val)
      (fun (x : GluingSet (fun i => if i ∈ ({j} : Finset ℕ) then MaxDom α else ∅)) =>
        (x.val : ℕ → ℕ)) := by
  -- Chain: ray ≤ MaxFun α = Subtype.val on MaxDom α ≤ Subtype.val on GluingSet(restricted)
  have h_ray : ContinuouslyReduces
      (fun (x : {a : A | f a ∈ RaySet Set.univ y j}) => f x.val)
      (MaxFun α) :=
    ray_reduces_to_maxFun α hα h1 f hf hscat β hβ y hy_simple j
  have h_embed : ContinuouslyReduces
      (MaxFun α)
      (fun (x : GluingSet (fun i => if i ∈ ({j} : Finset ℕ) then MaxDom α else ∅)) =>
        (x.val : ℕ → ℕ)) := by
    constructor
    swap
    exact fun x => ⟨prepend j x.val, mem_gluingSet_prepend (by simp)⟩
    refine ⟨?_, unprepend, ?_, ?_⟩
    · refine Continuous.subtype_mk ?_ ?_
      exact Continuous.comp (continuous_prepend j) continuous_subtype_val
    · exact continuous_unprepend.continuousOn
    · unfold MaxFun; aesop
  exact h_ray.trans h_embed

/--
Item 2 from Item 1.
-/
lemma maxFun_item2_from_item1'
    (α : Ordinal.{0}) (hα : α < omega1)
    (h1 : ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
      ContinuouslyReduces f (MaxFun α))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (β : Ordinal.{0}) (hβ : β ≤ α)
    (_hcb_ne : (CBLevel f β).Nonempty)
    (hcb_empty : CBLevel f (Order.succ β) = ∅)
    (y : ℕ → ℕ)
    (hy_simple : ∀ x ∈ CBLevel f β, f x = y) :
    ContinuouslyReduces f (SuccMaxFun α) := by
  convert pointedGluing_upper_bound f (fun _ => Set.mem_univ _) hf (fun _ => MaxDom α) (fun _ => MaxDom α) (fun _ => id) y (Set.mem_univ y) _ using 1
  · exact funext fun x => by rw [PointedGluingFun_id] ; rfl
  · refine ⟨fun j => { j }, ?_, ?_⟩ <;> simp +decide
    intro j
    convert ray_to_sub_gluing α hα h1 f hf (scatteredFun_of_CBLevel_empty f (Order.succ β) hcb_empty) β hβ y hy_simple j using 1
    ext ⟨x, hx⟩; simp [GluingFunVal]
    split_ifs <;> simp +decide [*, prepend]
    · cases ‹ℕ› <;> simp +decide [*, unprepend]
    · aesop
    · grind
    · cases hx ; aesop

/--
Helper: Simple function with CB rank ≤ α reduces to MaxFun α
-/
lemma simple_reduces_to_MaxFun
    (α : Ordinal.{0}) (hα : α < omega1)
    (ih2 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f)
      (γ : Ordinal.{0}) (_hγ : γ ≤ β)
      (_hcb_ne : (CBLevel f γ).Nonempty)
      (_hcb_empty : CBLevel f (Order.succ γ) = ∅)
      (y : ℕ → ℕ)
      (_hy_simple : ∀ x ∈ CBLevel f γ, f x = y),
      ContinuouslyReduces f (SuccMaxFun β))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (γ : Ordinal.{0}) (hγ : γ < α)
    (hcb_ne : (CBLevel f γ).Nonempty)
    (hcb_empty : CBLevel f (Order.succ γ) = ∅)
    (y : ℕ → ℕ)
    (hy_simple : ∀ x ∈ CBLevel f γ, f x = y) :
    ContinuouslyReduces f (MaxFun α) := by
  apply Classical.byContradiction
  intro h_contra
  apply_mod_cast h_contra <| ih2 γ hγ f hf γ le_rfl hcb_ne hcb_empty y hy_simple |> fun h => ?_
  convert h.trans _
  -- By definition of SuccMaxFun, we have SuccMaxFun γ = MaxFun (Order.succ γ).
  have h_succ_max : SuccMaxFun γ ≤ MaxFun (Order.succ γ) := by
    use fun x => ⟨prepend 0 x.val, by
      unfold MaxDom; simp +decide [SuccMaxDom]
      exact Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem _ x.2⟩⟩
    generalize_proofs at *
    refine ⟨?_, ?_⟩
    · refine Continuous.subtype_mk ?_ ?_
      exact continuous_prepend 0 |> Continuous.comp <| continuous_subtype_val
    · refine ⟨fun x => unprepend x, ?_, ?_⟩ <;> norm_num [MaxFun]
      · exact continuous_unprepend.continuousOn
      · exact fun x hx => rfl
  refine h_succ_max.trans ?_
  convert MaxFun_monotone _ _ _ _
  rotate_left
  exact Order.succ γ
  exact α
  · exact lt_of_le_of_lt (Order.succ_le_of_lt hγ) hα
  · exact hα
  · exact ⟨fun h => fun _ => h, fun h => h (Order.succ_le_of_lt hγ)⟩

/-- Helper: ContinuouslyReduces from an empty type. -/
lemma continuouslyReduces_of_empty {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    [hX : IsEmpty X] [Inhabited Y]
    (f : X → Y) (g : X' → Y') :
    ContinuouslyReduces f g :=
  ⟨isEmptyElim, continuous_of_discreteTopology,
    fun _ => default,
    by rw [show Set.range (g ∘ (isEmptyElim : X → X')) = ∅ from
        Set.range_eq_empty_iff.mpr ⟨hX.false⟩]; exact continuousOn_empty _,
    isEmptyElim⟩

/--
Helper: If CBLevel f 0 = ∅, the domain is empty (as a type).
-/
lemma isEmpty_of_CBLevel_zero_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : CBLevel f 0 = ∅) : IsEmpty X := by
  unfold CBLevel at h
  simp +zetaDelta at *
  exact h

/-
A simple piece from the decomposition lemma reduces to MaxFun α.
    Uses CBLevel_homeomorph to transfer SimpleFun data from {a ∈ A | a.val ∈ U}
    to A ∩ U, then applies simple_reduces_to_MaxFun, then transfers back.
-/
set_option maxHeartbeats 4000000 in
lemma simple_piece_reduces_to_maxfun
    (α : Ordinal.{0}) (hα : α < omega1)
    (ih2 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f)
      (γ : Ordinal.{0}) (_hγ : γ ≤ β)
      (_hcb_ne : (CBLevel f γ).Nonempty)
      (_hcb_empty : CBLevel f (Order.succ γ) = ∅)
      (y : ℕ → ℕ)
      (_hy_simple : ∀ x ∈ CBLevel f γ, f x = y),
      ContinuouslyReduces f (SuccMaxFun β))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅)
    (hrank_eq : CBRank f = α)
    (U : Set (ℕ → ℕ)) (hU : IsClopen U)
    (h_simple : SimpleFun (f ∘ (Subtype.val : {a : A | (a : ℕ → ℕ) ∈ U} → A))) :
    ContinuouslyReduces (fun a : {a : A | (a : ℕ → ℕ) ∈ U} => f a.val) (MaxFun α) := by
  have := h_simple.2
  obtain ⟨β, hβ_ne, hβ_empty, y, hy_simple⟩ := this
  have hβ_lt_α : β < α := by
    contrapose! hcb
    obtain ⟨x, hx⟩ := hβ_ne
    refine ⟨β, hcb, ?_⟩
    exact ⟨x.val, by simpa using CBLevel_open_restrict f ({ a : A | (a : ℕ → ℕ) ∈ U }) (hU.isOpen.preimage continuous_subtype_val) β x |>.1 hx⟩
  convert simple_reduces_to_MaxFun α hα ih2 _ _ β hβ_lt_α _ _ y _ using 1
  rotate_left
  exact A ∩ U
  use fun x => f ⟨x.val, x.prop.1⟩
  · fun_prop
  · convert hβ_ne using 1
    constructor <;> rintro ⟨x, hx⟩
    · grind
    · use ⟨x.val, x.val.prop, x.prop⟩
      convert CBLevel_homeomorph (subtypeInterHomeo A U) (fun x => f ⟨x.val, x.prop.1⟩) β |>.symm ▸ hx using 1
  · convert hβ_empty using 1
    constructor <;> intro h <;> simp_all +decide [Set.ext_iff]
    convert hβ_empty using 1
    convert Iff.rfl
    convert CBLevel_homeomorph (subtypeInterHomeo A U) (fun x => f ⟨x.val, x.prop.1⟩) (Order.succ β) using 1
    constructor <;> intro h <;> simp_all +decide [Set.ext_iff]
    · grind +suggestions
    · expose_names; exact (iff_false_left (hβ_empty a h_1 h_2)).mp (h a h_1 h_2)
  · convert hy_simple using 1
    constructor <;> intro h x hx
    · exact hy_simple x hx
    · convert h ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩ _
      convert hx using 1
      convert CBLevel_homeomorph (subtypeInterHomeo A U) (fun x => f ⟨x.val, x.prop.1⟩) β using 1
      simp +decide [Set.ext_iff, CBLevel]
      constructor <;> intro h
      · convert CBLevel_homeomorph (subtypeInterHomeo A U) (fun x => f ⟨x.val, x.prop.1⟩) β using 1
        simp +decide [Set.ext_iff, CBLevel]
      · convert h x.val x.prop.1 x.prop.2 using 1
  · ext
    constructor <;> intro h <;> rcases h with ⟨σ, hσ, τ, hτ, h⟩
    · use fun x => σ ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
      refine ⟨?_, τ, ?_, ?_⟩
      · fun_prop
      · convert hτ using 1
        ext; simp [Function.comp]
        exact ⟨fun ⟨a, ha, ha'⟩ => ⟨a, ha.1, ha.2, ha'⟩, fun ⟨a, ha, ha', ha''⟩ => ⟨a, ⟨ha, ha'⟩, ha''⟩⟩
      · exact fun x => h ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
    · use σ ∘ (subtypeInterHomeo A U)
      refine ⟨hσ.comp ?_, τ, ?_, ?_⟩
      · exact Homeomorph.continuous (subtypeInterHomeo A U)
      · convert hτ using 1
        ext; simp [subtypeInterHomeo]
        grind
      · intro x; specialize h (subtypeInterHomeo A U x) ; aesop

/--
Main lemma: the CBRank f = α case.
When CBRank f = α, decompose f into simple pieces using decomposition_lemma_baire,
each reducing to MaxFun α via simple_reduces_to_MaxFun, then combine via gluing.
-/
lemma cbrank_eq_case
    (α : Ordinal.{0}) (hα : α < omega1)
    (_ih1 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ γ : Ordinal.{0}, β ≤ γ → CBLevel f γ = ∅),
      ContinuouslyReduces f (MaxFun β))
    (ih2 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f)
      (γ : Ordinal.{0}) (_hγ : γ ≤ β)
      (_hcb_ne : (CBLevel f γ).Nonempty)
      (_hcb_empty : CBLevel f (Order.succ γ) = ∅)
      (y : ℕ → ℕ)
      (_hy_simple : ∀ x ∈ CBLevel f γ, f x = y),
      ContinuouslyReduces f (SuccMaxFun β))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅)
    (_h_empty : (CBLevel f 0).Nonempty)
    (hrank_eq : CBRank f = α) :
    ContinuouslyReduces f (MaxFun α) := by
  -- Step 1: Get local simplicity from decomposition_lemma_baire
  have h_loc := decomposition_lemma_baire A f hscat
  -- Step 2: Each local piece reduces to MaxFun α
  have hloc_reduces : ∀ x : A, ∃ C : Set A, IsClopen C ∧ x ∈ C ∧
      ContinuouslyReduces (fun a : C => f a.val) (MaxFun α) := by
    intro x
    obtain ⟨U, hU_clopen, hxU, hU_simple⟩ := h_loc x
    refine ⟨Subtype.val ⁻¹' U, hU_clopen.preimage continuous_subtype_val, hxU, ?_⟩
    exact simple_piece_reduces_to_maxfun α hα ih2 f hf hcb hrank_eq U hU_clopen hU_simple
  -- Step 3: Locally reduces → globally reduces
  exact locally_reduces_to_maxfun_implies_reduces α hα f hloc_reduces

/--
Item 1 from IH Item 2.
-/
lemma maxFun_item1_from_ih'
    (α : Ordinal.{0}) (hα : α < omega1)
    (ih1 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ γ : Ordinal.{0}, β ≤ γ → CBLevel f γ = ∅),
      ContinuouslyReduces f (MaxFun β))
    (ih2 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f)
      (γ : Ordinal.{0}) (_hγ : γ ≤ β)
      (_hcb_ne : (CBLevel f γ).Nonempty)
      (_hcb_empty : CBLevel f (Order.succ γ) = ∅)
      (y : ℕ → ℕ)
      (_hy_simple : ∀ x ∈ CBLevel f γ, f x = y),
      ContinuouslyReduces f (SuccMaxFun β))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅) :
    ContinuouslyReduces f (MaxFun α) := by
  -- Case: domain is empty
  by_cases h_empty : CBLevel f 0 = ∅
  · haveI := isEmpty_of_CBLevel_zero_empty f h_empty
    exact continuouslyReduces_of_empty f (MaxFun α)
  -- Case: domain is nonempty, use CBRank < α
  · push_neg at h_empty
    -- CBRank f ≤ α since CBLevel f α = ∅
    have hrank_le : CBRank f ≤ α := CBRank_le_of_CBLevel_empty f α (hcb α le_rfl)
    -- CBRank f < α or CBRank f = α
    rcases hrank_le.lt_or_eq with hrank_lt | hrank_eq
    · -- CBRank f < α: use ih1
      have hcb' : ∀ γ, CBRank f ≤ γ → CBLevel f γ = ∅ := by
        intro γ hγ
        have h_empty := cbLevel_at_cbRank_empty f hscat
        exact Set.eq_empty_of_subset_empty (h_empty ▸ CBLevel_antitone f hγ)
      exact (ih1 (CBRank f) hrank_lt f hf hscat hcb').trans
        (MaxFun_monotone _ α (lt_of_lt_of_le hrank_lt hα.le) hα hrank_lt.le)
    · -- CBRank f = α: decompose into pieces with CB rank < α, combine
      exact cbrank_eq_case α hα ih1 ih2 f hf hscat hcb h_empty hrank_eq

/-- **Proposition 3.9 (Maxfunctions). Maximum functions.** -/
theorem maxFun_is_maximum'
    (α : Ordinal.{0}) (hα : α < omega1) :
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (_hf : Continuous f)
    (_hscat : ScatteredFun f)
    (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
      ContinuouslyReduces f (MaxFun α)) ∧
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (_hf : Continuous f)
    (β: Ordinal.{0}) (_hβ : β ≤ α)
    (_hcb_ne : (CBLevel f β).Nonempty)
    (_hcb_empty : CBLevel f (Order.succ β) = ∅)
    (y: ℕ →ℕ)
    (_hy_simple : ∀ x ∈ CBLevel f β, f x = y),
    ContinuouslyReduces f (SuccMaxFun α)) := by
  induction α using Ordinal.induction with
  | h α ih =>
    have item1 : ∀ {A : Set (ℕ → ℕ)}
        (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
        (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
        ContinuouslyReduces f (MaxFun α) :=
      maxFun_item1_from_ih' α hα
        (fun β hβ {A} f hf hscat hcb =>
          (ih β hβ (hβ.trans hα)).1 f hf hscat hcb)
        (fun β hβ {A} f hf γ hγ hcb_ne hcb_empty y hy_simple =>
          (ih β hβ (hβ.trans hα)).2 f hf γ hγ hcb_ne hcb_empty y hy_simple)
    exact ⟨item1, fun f hf => maxFun_item2_from_item1' α hα item1 f hf⟩

end
