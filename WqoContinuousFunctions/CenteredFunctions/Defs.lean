import WqoContinuousFunctions.PointedGluing.Defs
import WqoContinuousFunctions.ScatFun.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `4_centered_memo.tex` — Definitions

This file contains the definitions from Chapter 4 (Centered Functions) of the memoir
on continuous reducibility between functions.
When it simplifies the formalization,
we restrict definition to functions in ScatFun.


## Main definitions

* `IsCenterFor` — a point `x` is a center for a function `g`
* `IsCentered` — a function admits a center
* `ScatFun.IsRegularSeq` — a sequence in `ScatFun` is regular for continuous reducibility
* `IsMonotoneSeq` — a sequence in `ScatFun` is monotone for continuous reducibility
* `Cocenter` — the cocenter of a centered scattered function
* `IsLocallyCentered` — a function is locally centered
-/

noncomputable section

/-!
## Definition: Center and Centered Functions
-/

/-- A point `x ∈ A` is a *center* for a function `g : A → B` if for every neighbourhood
`U` of `x` we have `g ≤ g|_U` (i.e., `g` continuously reduces to its restriction to
any neighbourhood of `x`). -/
def IsCenterFor {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (g : A → B) (x : A) : Prop :=
  ∀ U : Set A, IsOpen U → x ∈ U →
    ContinuouslyReduces g (g ∘ (Subtype.val : U → A))


/-- `IsCenterFor` is invariant under precomposition by a homeomorphism, transporting
the center point. -/
lemma IsCenterFor.comp_homeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (g : Y → Z) (x : X) :
    IsCenterFor (g ∘ e) x ↔ IsCenterFor g (e x) := by
  constructor
  · intro h V hV_open hexV
    have hU_open : IsOpen (e ⁻¹' V) := e.isOpen_preimage.mpr hV_open
    have hxU : x ∈ e ⁻¹' V := by simpa using hexV
    obtain ⟨σ, hσ, τ, hτ, hστ⟩ := h (e ⁻¹' V) hU_open hxU
    -- hστ : ∀ a, (g ∘ e) a = τ ((g ∘ e ∘ Subtype.val) (σ a))
    -- i.e. g (e a) = τ (g (e (σ a).1))
    -- We want ContinuouslyReduces g (g ∘ Subtype.val : ↑V → Z)
    -- Use σ' = (fun y => e (σ (e.symm y)).1) and τ' = τ
    refine ⟨fun y => ⟨e (σ (e.symm y)).1, (σ (e.symm y)).2⟩,
      ?_, τ, ?_, ?_⟩
    · -- continuity of σ'
      apply Continuous.subtype_mk
      exact e.continuous.comp (continuous_subtype_val.comp
        (hσ.comp e.symm.continuous))
    · -- ContinuousOn τ (range (g ∘ σ'))
      convert hτ using 2
      ext z
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e.symm y, by simp⟩
      · rintro ⟨a, ha⟩
        exact ⟨e a, by simp [e.symm_apply_apply]; exact ha⟩
    · intro y
      have := hστ (e.symm y)
      simp only [Function.comp_apply, e.apply_symm_apply] at this
      convert this using 2
  · intro h V hV_open hxV
    have hV_open' : IsOpen (e '' V) := e.isOpen_image.mpr hV_open
    have hexV : e x ∈ e '' V := Set.mem_image_of_mem e hxV
    obtain ⟨σ, hσ, τ, hτ, hστ⟩ := h (e '' V) hV_open' hexV
    -- hστ : ∀ y, g y = τ (g (σ y).1)
    -- Want ContinuouslyReduces (g ∘ e) ((g ∘ e) ∘ Subtype.val : ↑V → Z)
    -- Use σ' = e.symm ∘ σ ∘ e, τ' = τ
    refine ⟨fun a => ⟨e.symm (σ (e a)).1, ?_⟩, ?_, τ, ?_, ?_⟩
    · -- (e.symm (σ (e a)).1) ∈ V
      have hmem := (σ (e a)).2
      simp only [Set.mem_image] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      rw [← hwe, e.symm_apply_apply]
      exact hw
    · -- continuity
      apply Continuous.subtype_mk
      exact e.symm.continuous.comp (continuous_subtype_val.comp
        (hσ.comp e.continuous))
    · -- ContinuousOn τ range
      convert hτ using 2
      ext z
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨e a, by simp [e.apply_symm_apply]⟩
      · rintro ⟨y, rfl⟩
        exact ⟨e.symm y, by simp [e.apply_symm_apply]⟩
    · intro a
      simp only [Function.comp_apply]
      have := hστ (e a)
      simp only [Function.comp_apply] at this
      convert this using 2
      simp [e.apply_symm_apply]

/-- A function `g : A → B` is *centered* if it admits a center. -/
def IsCentered {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (g : A → B) : Prop :=
  ∃ x : A, IsCenterFor g x

/-- `IsCentered` is invariant under precomposition by a homeomorphism: it transports
along the center bijection. -/
lemma IsCentered_comp_homeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (g : Y → Z) :
    IsCentered (g ∘ e) ↔ IsCentered g := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e x, (IsCenterFor.comp_homeomorph e g x).mp hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, (IsCenterFor.comp_homeomorph e g (e.symm y)).mpr ?_⟩
    rwa [e.apply_symm_apply]

/-!
## Definition: Regular Sequence
-/

/-- A sequence `(f_i)_{i ∈ ℕ}` in `ScatFun` is *regular* (for continuous reducibility)
if for every `i ∈ ℕ`, the set `{j ∈ ℕ | f_i ≤ f_j}` is infinite.  This is the general
`IsRegularSeq` from `BQO/WQO.lean` specialized to `(ScatFun, ScatFun.Reduces)`. -/
def ScatFun.IsRegularSeq (f : ℕ → ScatFun) : Prop :=
  Preorder.IsRegularSeq (Q := ScatFun) ScatFun.Reduces f

/-- A sequence is *monotone* for continuous reducibility:
for all `i ≤ j`, `f_i ≤ f_j`. -/
def IsMonotoneSeq (f : ℕ → ScatFun): Prop :=
  ∀ i j : ℕ, i ≤ j → ScatFun.Reduces (f i) (f j)

/-- A monotone sequence is regular. -/
theorem IsMonotoneSeq.isRegularSeq (f : ℕ → ScatFun)
    (hf : IsMonotoneSeq f) : ScatFun.IsRegularSeq f := fun i =>
  Set.infinite_of_injective_forall_mem (f := fun n => n + i + 1)
    (fun m n (h : m + i + 1 = n + i + 1) => by omega)
    (fun n => hf i (n + i + 1) (by omega))

/-!
## Definition: Cocenter
-/

/-- The *cocenter* of a centered function `f` is the common image of all centers of `f`
under `f`. This is well-defined when `f` is scattered (by Proposition
`scatteredhavecocenter`). -/
noncomputable def cocenter {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hc : IsCentered f) : B :=
  f hc.choose

/-!
## Definition: Locally Centered
-/

/-- A function `f : A → B` is *locally centered* if every point `x ∈ A` admits a
neighbourhood `U` such that `f|_U` is centered. -/
def IsLocallyCentered {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) : Prop :=
  ∀ x : A, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧
    IsCentered (f ∘ (Subtype.val : U → A))



/-- Forward implication of `IsLocallyCentered_comp_homeomorph`: if `f ∘ e` is locally
centered then so is `f`.  Around a point `y`, the witnessing neighbourhood `U ∋ e⁻¹ y`
for `f ∘ e` is carried over to `e '' U ∋ y`, and the restricted homeomorphism
`e.image U : U ≃ₜ e '' U` intertwines the two restrictions, so centeredness transfers
by `IsCentered_comp_homeomorph`. -/
lemma isLocallyCentered_of_comp_homeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y → Z) (H : IsLocallyCentered (f ∘ e)) :
    IsLocallyCentered f := by
  intro y
  obtain ⟨U, hU_open, hxU, hU_cent⟩ := H (e.symm y)
  refine ⟨e '' U, e.isOpen_image.mpr hU_open,
    ⟨e.symm y, hxU, e.apply_symm_apply y⟩, ?_⟩
  -- `(f ∘ val_{e''U}) ∘ e.image U = (f ∘ e) ∘ val_U`
  have heq : (f ∘ (Subtype.val : ↥(e '' U) → Y)) ∘ (e.image U)
      = (f ∘ e) ∘ (Subtype.val : ↥U → X) := by
    ext a; rfl
  rw [← IsCentered_comp_homeomorph (e.image U) (f ∘ (Subtype.val : ↥(e '' U) → Y)), heq]
  exact hU_cent

lemma IsLocallyCentered_comp_homeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y → Z) :
    IsLocallyCentered (f ∘ e) = IsLocallyCentered f := by
  apply propext
  constructor
  · exact isLocallyCentered_of_comp_homeomorph e f
  · intro H
    -- Apply the forward implication to `e.symm` and `f ∘ e`, using `(f ∘ e) ∘ e.symm = f`.
    have key := isLocallyCentered_of_comp_homeomorph e.symm (f ∘ e)
    have hfe : (f ∘ e) ∘ ⇑e.symm = f := by ext y; simp
    rw [hfe] at key
    exact key H

/-!
## Useful abbreviation for rays
-/

/-- The *n*-th ray of `f` at `y`: the restriction of `f` to the set of points
that agree with `y` on the first `n` coordinates but differ at position `n`. -/
abbrev RayFun {A : Type*} [TopologicalSpace A]
    (f : A → ℕ → ℕ) (y : ℕ → ℕ) (n : ℕ) :
    {a : A | (∀ k, k < n → f a k = y k) ∧ f a n ≠ y n} → ℕ → ℕ :=
  f ∘ Subtype.val

end
