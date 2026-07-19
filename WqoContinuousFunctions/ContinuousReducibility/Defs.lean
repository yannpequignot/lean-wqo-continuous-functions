import ZeroDimensionalSpaces.Basics
import BQO.OrdinalBQO
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Formalization of `2_prelim_memo.tex` — Basic Results

## Main definitions

* `WadgeReduces` — Wadge reducibility between subsets
* `TopologicallyEmbedsFun` — topological embeddability between functions
* `corestriction'` — co-restriction of a function to a subset of the codomain

## Main results

* `embedding_iff_id_reduces` — X embeds in Y iff id_X ≤ id_Y
* `restriction_reduces` — f|_A ≤ f for A ⊆ dom f
* `ContinuouslyReduces.sigma_injective` — if f is injective and (σ,τ) reduces f to g,
  then σ is injective
-/

section ContinuousReduction


/-!
## Definition 1 (Continuous Reduction)

Given topological spaces `X, X', Y, Y'`, a function `f : X → Y` *continuously reduces*
to a function `g : X' → Y'` if there exist continuous `σ : X → X'` and a continuous
`τ : im(g ∘ σ) → im(f)` such that `τ(g(σ(x))) = f(x)` for all `x`.

**Note:** Three formulations appear below.  `ContinuouslyReduces_naive` uses a total
*continuous* `τ : Y' → Y` (too strong).  `ContinuouslyReduces_range_based` is the memoir's
formulation, with `τ` defined only between the images `im (g ∘ σ) → im f`.  The primary
definition `ContinuouslyReduces` (carrying the `≤` notation and used throughout) is a
convenient middle ground: a total `τ : Y' → Y` that is only required to be `ContinuousOn`
`im (g ∘ σ)`.  It agrees with the memoir's `ContinuouslyReduces_range_based` whenever the
codomain is nonempty (`continuouslyReduces_iff_range_based`); they differ only for the empty
function — see the discussion above `ContinuouslyReduces.to_range_based`.
-/

/-- `ContinuouslyReduces_naive f g` is the naive (stronger) version of continuous
reducibility using total maps `σ : X → X'` and `τ : Y' → Y`. -/
def ContinuouslyReduces_naive {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ (σ : X → X') (τ : Y' → Y), Continuous σ ∧ Continuous τ ∧ ∀ x, f x = τ (g (σ x))

universe u v w z

variable {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
variable[TopologicalSpace X] [TopologicalSpace X']
variable [TopologicalSpace Y] [TopologicalSpace Y']

/--
A function `f` continuously reduces to `g` if there is a continuous `σ : X → X'`
and a continuous `τ : im(g ∘ σ) → im(f)` such that `τ(g(σ(x))) = f(x)` for all `x`.
-/
def ContinuouslyReduces_range_based (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : C(X, X'),
  ∃ τ : C(Set.range (g ∘ σ), Set.range f),
    ∀ x : X, τ ⟨g (σ x), Set.mem_range_self x⟩ = ⟨f x, Set.mem_range_self x⟩

/--
A function `f` continuously reduces to `g` if there is a continuous `σ : X → X'`
and a function `τ : Y' → Y` that is continuous on `im(g ∘ σ)`
such that `f(x) = τ(g(σ(x)))` for all `x`.
-/
def ContinuouslyReduces {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : X → X', Continuous σ ∧
  ∃ τ : Y' → Y, ContinuousOn τ (Set.range (g ∘ σ)) ∧
    ∀ x : X, f x = τ (g (σ x))

-- Optional: Define the ≤ notation for this relation
infix:50 " ≤ " => ContinuouslyReduces

/-- Continuous reducibility is reflexive: any function reduces to itself via `(id, id)`. -/
theorem ContinuouslyReduces.refl (f : X → Y) : f ≤ f :=
  ⟨id, continuous_id, id, continuousOn_id, fun _ => rfl⟩

/--
Continuous reducibility is transitive. If `f ≤ g` via `(σ₁, τ₁)` and `g ≤ h`
via `(σ₂, τ₂)`, then `f ≤ h` via `(σ₂ ∘ σ₁, τ₁ ∘ τ₂)`.
-/
theorem ContinuouslyReduces.trans {X X' X'' Y Y' Y'' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
  {f : X → Y} {g : X' → Y'} {h : X'' → Y''}
  (hfg : f ≤ g) (hgh : g ≤ h) :
  f ≤ h := by
    obtain ⟨σ₁, hσ₁, τ₁, hτ₁cont, hτ₁eq⟩ := hfg
    obtain ⟨σ₂, hσ₂, τ₂, hτ₂cont, hτ₂eq⟩ := hgh
    refine ⟨σ₂ ∘ σ₁, hσ₂.comp hσ₁, τ₁ ∘ τ₂, ?_, fun x => by simp [Function.comp]; rw [hτ₁eq, ← hτ₂eq]⟩
    apply ContinuousOn.comp hτ₁cont (hτ₂cont.mono (Set.range_comp_subset_range _ _))
    rintro y ⟨x, rfl⟩; simp [Function.comp] at *; rw [← hτ₂eq]; exact Set.mem_range_self x

/-- `ContinuouslyReduces` is invariant under post/pre-composition by homeomorphisms
on either side. -/
lemma ContinuouslyReduces.comp_homeomorph_left
    {X Y X' Y' W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace W]
    {f : X → Y} {g : X' → Y'} (h : ContinuouslyReduces f g) (e : W ≃ₜ X) :
    ContinuouslyReduces (f ∘ e) g := by
  obtain ⟨σ, hσ, τ, hτ, hστ⟩ := h
  refine ⟨σ ∘ e, hσ.comp e.continuous, τ, ?_, fun x => by simp [hστ (e x)]⟩
  have hrange : Set.range (g ∘ (σ ∘ e)) = Set.range (g ∘ σ) := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨w, rfl⟩; exact ⟨e w, rfl⟩
    · rintro _ ⟨w', rfl⟩
      obtain ⟨w, rfl⟩ := e.surjective w'
      exact ⟨w, rfl⟩
  rw [hrange]
  exact hτ


lemma ContinuouslyReduces.comp_homeomorph_right
    {X Y X' Y' W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace W]
    {f : X → Y} {g : X' → Y'} (h : ContinuouslyReduces f g) (e : W ≃ₜ X') :
    ContinuouslyReduces f (g ∘ e) := by
  obtain ⟨σ, hσ, τ, hτ, hστ⟩ := h
  refine ⟨e.symm ∘ σ, e.symm.continuous.comp hσ, τ, ?_, fun x => by
    simp [hστ x, Function.comp]⟩
  -- range (g ∘ e ∘ (e.symm ∘ σ)) = range (g ∘ σ), since e ∘ e.symm = id
  have hrange : Set.range ((g ∘ e) ∘ (e.symm ∘ σ)) = Set.range (g ∘ σ) := by
    congr 1
    ext x
    simp [Function.comp, e.apply_symm_apply]
  rw [hrange]
  exact hτ

/-!
## The image-restricted (memoir) variant and its relation to `ContinuouslyReduces`

`ContinuouslyReduces_range_based` is the definition exactly as it appears in the memoir:
`τ` is only required to be defined (and continuous) on `im (g ∘ σ)`, with values in `im f`.
The definition `ContinuouslyReduces` used throughout this development instead takes a *total*
`τ : Y' → Y` that is merely `ContinuousOn (im (g ∘ σ))`.

The two notions coincide as soon as the codomain `Y` is nonempty
(`continuouslyReduces_iff_range_based`).  They differ *only* for the empty function: if `Y`
is empty (so `X` is empty) and `Y'` is nonempty, then the image-restricted version holds
vacuously (`ContinuouslyReduces_range_based.of_isEmpty_codomain`) while the total version
fails (`not_continuouslyReduces_of_isEmpty_codomain`), because a witness `τ : Y' → Y` would be
a total map from a nonempty type into an empty one.

### Why the total-`τ` definition is the convenient one in Lean

The image-based `τ : C(im (g ∘ σ), im f)` is a *bundled* continuous map whose **domain and
codomain are subtypes depending on the data** `σ, f, g`.  That dependency is exactly what makes
it painful in a proof assistant, whereas the total `τ : Y' → Y` sidesteps all of it:

* **Stable type.**  `ContinuouslyReduces` keeps `τ : Y' → Y`, a fixed type.  Precomposing `σ`
  with a homeomorphism or composing two reductions never changes the type of `τ`.  In the
  image-based version each such step changes `im (g ∘ σ)`, so `τ` must be transported across
  *propositional* equalities `im (g ∘ σ₁) = im (g ∘ σ₂)` (`▸`/`cast`, with motive headaches).

* **Composition is ordinary function composition.**  Transitivity just takes `τ₁ ∘ τ₂` and
  intersects the `ContinuousOn` domains — `refl`, `trans`, `comp_homeomorph_*` are all
  one-liners.  Composing bundled maps between *nested* subtypes (getting `im (h ∘ σ₂ ∘ σ₁) → im f`
  out of `im (g ∘ σ₁) → im f` and `im (h ∘ σ₂) → im g`) needs explicit inclusion/corestriction
  maps plus proofs that the images nest.

* **Mathlib API.**  `ContinuousOn` has a large, ergonomic API (`ContinuousOn.comp`, `.mono`,
  `continuousOn_iff_continuous_restrict`, …).  A subtype-valued `C(_, _)` instead forces
  `Continuous.subtype_mk` together with `Subtype.ext`/`.val` bookkeeping at every step.

* **The witnessing equation lives in `Y`.**  `f x = τ (g (σ x))` is a plain equation in `Y`;
  the image-based `τ ⟨g (σ x), _⟩ = ⟨f x, _⟩` is an equation between proof-carrying subtype
  elements, reachable only through `Subtype.ext`.

The single cost is the degenerate empty-codomain discrepancy isolated above.  We therefore use
`ContinuouslyReduces` throughout the development (the memoir is built on it), while the headline
results — e.g. `MainTheorem3` — are *stated* with `ContinuouslyReduces_range_based`, matching
the paper exactly; the bridge in both directions is `continuouslyReduces_iff_range_based`
(and unconditionally `ContinuouslyReduces.to_range_based`).  Where the empty case could intrude
internally we add `[Nonempty Y]` explicitly. -/

/-- Any map out of an empty space is continuous. -/
lemma continuous_of_isEmpty_dom {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [IsEmpty A] (h : A → B) : Continuous h :=
  continuous_def.mpr fun s _ => by rw [Set.eq_empty_of_isEmpty (h ⁻¹' s)]; exact isOpen_empty

/-- The total-`τ` reduction always restricts to the memoir's image-based one. -/
theorem ContinuouslyReduces.to_range_based {f : X → Y} {g : X' → Y'}
    (h : ContinuouslyReduces f g) : ContinuouslyReduces_range_based f g := by
  obtain ⟨σ, hσ, τ, hτcont, hτeq⟩ := h
  have hτmaps : ∀ y ∈ Set.range (g ∘ σ), τ y ∈ Set.range f := by
    rintro _ ⟨x, rfl⟩; exact ⟨x, hτeq x⟩
  refine ⟨⟨σ, hσ⟩, ⟨fun y => ⟨τ y.val, hτmaps y.val y.2⟩, ?_⟩, fun x => ?_⟩
  · exact (continuousOn_iff_continuous_restrict.mp hτcont).subtype_mk (fun y => hτmaps y.val y.2)
  · exact Subtype.ext (hτeq x).symm

/-- Conversely, when `Y` is nonempty the image-based reduction extends to a total one: off the
image `τ` is filled in with an arbitrary value of `Y` (this is the only use of `[Nonempty Y]`). -/
theorem ContinuouslyReduces_range_based.to_continuouslyReduces [Nonempty Y]
    {f : X → Y} {g : X' → Y'}
    (h : ContinuouslyReduces_range_based f g) : ContinuouslyReduces f g := by
  classical
  obtain ⟨σ, τ, hτeq⟩ := h
  refine ⟨⇑σ, σ.continuous,
    fun y => if hy : y ∈ Set.range (g ∘ σ) then (τ ⟨y, hy⟩).val else Classical.arbitrary Y,
    ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hcongr : (Set.range (g ∘ σ)).restrict
        (fun y => if hy : y ∈ Set.range (g ∘ σ) then (τ ⟨y, hy⟩).val else Classical.arbitrary Y)
        = fun p : Set.range (g ∘ σ) => (τ p).val := by
      funext p; simp only [Set.restrict_apply, dif_pos p.2, Subtype.coe_eta]
    rw [hcongr]
    exact continuous_subtype_val.comp τ.continuous
  · intro x
    have hx : g (σ x) ∈ Set.range (g ∘ σ) := Set.mem_range_self x
    show f x = dite (g (σ x) ∈ Set.range (g ∘ σ))
      (fun hy => (τ ⟨g (σ x), hy⟩).val) (fun _ => Classical.arbitrary Y)
    rw [dif_pos hx]
    exact (congrArg Subtype.val (hτeq x)).symm

/-- For nonempty codomain, the memoir's definition and the total-`τ` definition agree. -/
theorem continuouslyReduces_iff_range_based [Nonempty Y] {f : X → Y} {g : X' → Y'} :
    ContinuouslyReduces f g ↔ ContinuouslyReduces_range_based f g :=
  ⟨ContinuouslyReduces.to_range_based, ContinuouslyReduces_range_based.to_continuouslyReduces⟩

/-- The empty function satisfies the memoir's image-based reduction to *any* `g` (vacuously). -/
theorem ContinuouslyReduces_range_based.of_isEmpty_codomain [IsEmpty Y]
    {f : X → Y} {g : X' → Y'} : ContinuouslyReduces_range_based f g := by
  have : IsEmpty X := Function.isEmpty f
  refine ⟨⟨fun x => isEmptyElim x, continuous_of_isEmpty_dom _⟩, ?_, fun x => isEmptyElim x⟩
  have : IsEmpty (Set.range (g ∘ (fun x : X => (isEmptyElim x : X')))) := by
    rw [Set.isEmpty_coe_sort]; exact Set.range_eq_empty _
  exact ⟨fun p => isEmptyElim p, continuous_of_isEmpty_dom _⟩

/-- The image-based reduction also holds vacuously when the *domain* of the source is empty:
the empty function `∅ → Y` image-reduces to *any* `g`.  (Together with
`of_isEmpty_codomain` — note an empty codomain forces an empty domain — this makes the empty
function a global minimum of `≤ᵣ`.) -/
theorem ContinuouslyReduces_range_based.of_isEmpty_dom [IsEmpty X]
    {f : X → Y} {g : X' → Y'} : ContinuouslyReduces_range_based f g := by
  refine ⟨⟨fun x => isEmptyElim x, continuous_of_isEmpty_dom _⟩, ?_, fun x => isEmptyElim x⟩
  have : IsEmpty (Set.range (g ∘ (fun x : X => (isEmptyElim x : X')))) := by
    rw [Set.isEmpty_coe_sort]; exact Set.range_eq_empty _
  exact ⟨fun p => isEmptyElim p, continuous_of_isEmpty_dom _⟩

/-- Image-based reducibility is reflexive (it contains the reflexive strong reduction). -/
theorem ContinuouslyReduces_range_based.refl (f : X → Y) :
    ContinuouslyReduces_range_based f f :=
  (ContinuouslyReduces.refl f).to_range_based

/-- **Image-based reducibility is transitive**, hence (with `refl`) a quasi-order.

It is reduced to transitivity of the *strong* reduction (`ContinuouslyReduces.trans`) via the
coincidence of the two relations on nonempty codomains (`to_continuouslyReduces`,
`to_range_based`).  The empty function is handled separately: if the source codomain `Y` is
empty the conclusion is `of_isEmpty_codomain`; if the middle codomain `Y'` is empty then the
strong `f ≤ g` factors a `σ : X → X'` through the empty `X'`, so the source domain `X` is empty
and `of_isEmpty_dom` applies. -/
theorem ContinuouslyReduces_range_based.trans
    {X X' X'' Y Y' Y'' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
    [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
    {f : X → Y} {g : X' → Y'} {h : X'' → Y''}
    (hfg : ContinuouslyReduces_range_based f g)
    (hgh : ContinuouslyReduces_range_based g h) :
    ContinuouslyReduces_range_based f h := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · have := hY
    exact ContinuouslyReduces_range_based.of_isEmpty_codomain
  · have := hY
    have hfg_s : ContinuouslyReduces f g := hfg.to_continuouslyReduces
    rcases isEmpty_or_nonempty Y' with hY' | hY'
    · have := hY'
      have : IsEmpty X' := Function.isEmpty g
      obtain ⟨σ, -, -, -, -⟩ := hfg_s
      have : IsEmpty X := Function.isEmpty σ
      exact ContinuouslyReduces_range_based.of_isEmpty_dom
    · have := hY'
      have hgh_s : ContinuouslyReduces g h := hgh.to_continuouslyReduces
      exact (hfg_s.trans hgh_s).to_range_based

/-- …but it does *not* satisfy the total-`τ` reduction whenever the target codomain `Y'` is
nonempty: there is no total map `Y' → Y` into the empty `Y`.  This is exactly the discrepancy
between the two definitions. -/
theorem not_continuouslyReduces_of_isEmpty_codomain [IsEmpty Y] [Nonempty Y']
    {f : X → Y} {g : X' → Y'} : ¬ ContinuouslyReduces f g := by
  rintro ⟨σ, -, τ, -, -⟩
  exact (isEmptyElim (τ (Classical.arbitrary Y')) : False)

end ContinuousReduction


section EquivAndStrict

/-!
## Continuous Equivalence and Strict Reduction

As usual with quasi-orders, we define:
* `f ≡ g` when both `f ≤ g` and `g ≤ f` (continuous equivalence).
* `f < g` when `f ≤ g` but `¬(g ≤ f)` (strict continuous reduction).
* `f` and `g` are *incomparable* when `¬(f ≤ g)` and `¬(g ≤ f)`.
-/

/-- Two functions are continuously equivalent if each reduces to the other. -/
def ContinuouslyEquiv {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ContinuouslyReduces f g ∧ ContinuouslyReduces g f

/-- Strict continuous reduction: `f` reduces to `g` but `g` does not reduce to `f`. -/
def StrictlyContinuouslyReduces {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ContinuouslyReduces f g ∧ ¬ ContinuouslyReduces g f

/-- Two functions are incomparable if neither reduces to the other. -/
def ContinuouslyIncomparable {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ¬ ContinuouslyReduces f g ∧ ¬ ContinuouslyReduces g f

/-- Continuous equivalence is reflexive. -/
theorem ContinuouslyEquiv.refl {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : ContinuouslyEquiv f f :=
  ⟨ContinuouslyReduces.refl f, ContinuouslyReduces.refl f⟩

/-- Continuous equivalence is symmetric. -/
theorem ContinuouslyEquiv.symm {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (h : ContinuouslyEquiv f g) : ContinuouslyEquiv g f :=
  ⟨h.2, h.1⟩

/-- Continuous equivalence is transitive. -/
theorem ContinuouslyEquiv.trans {X X' X'' Y Y' Y'' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
    [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
    {f : X → Y} {g : X' → Y'} {h : X'' → Y''}
    (hfg : ContinuouslyEquiv f g) (hgh : ContinuouslyEquiv g h) :
    ContinuouslyEquiv f h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

end EquivAndStrict


section CoRestriction

/-- The co-restriction of `f : X → Y` to `B ⊆ Y` is the restriction of `f` to `f⁻¹(B)`. -/
def CoRestrict {X Y : Type*} (f : X → Y) (B : Set Y) : f ⁻¹' B → Y :=
  f ∘ Subtype.val

/-- Domain restriction of `g` to the preimage of a set `C` in the codomain. -/
def PreImage (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), g ⟨x, h⟩ ∈ C}

/-- Function `g` restricted to the preimage of `C` in the codomain. -/
def CoRestrict' (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    PreImage B g C → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

lemma CoRestrict_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (C : Set (ℕ → ℕ)) :
    Continuous (CoRestrict' B g C) :=
  hgc.comp (Continuous.subtype_mk continuous_subtype_val _)


end CoRestriction

section WadgeReducibility

/-- `WadgeReduces A B` means that the set `A` Wadge reduces to the set `B`. -/
def WadgeReduces {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) : Prop :=
  ∃ (σ : X → Y), Continuous σ ∧ σ ⁻¹' B = A

end WadgeReducibility

section TopologicalEmbeddabilityFunctions

/-- `TopologicallyEmbedsFun f g` means that `f` topologically embeds in `g`. -/
def TopologicallyEmbedsFun {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ (σ : X → X') (τ : Y' → Y),
    Topology.IsEmbedding σ ∧ Topology.IsEmbedding τ ∧ ∀ x, f x = τ (g (σ x))

theorem TopologicallyEmbedsFun.continuouslyReduces {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (h : TopologicallyEmbedsFun f g) : ContinuouslyReduces f g := by
  obtain ⟨σ, τ, hσ, hτ, hred⟩ := h
  exact ⟨σ, hσ.continuous, τ, hτ.continuous.continuousOn, hred⟩

end TopologicalEmbeddabilityFunctions

section EmbeddingAndReduction

theorem embedding_of_id_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuouslyReduces (@id X) (@id Y)) :
    ∃ (σ : X → Y), Topology.IsEmbedding σ := by
  obtain ⟨σ, τ, hσ, hτ, h⟩ := h
  have h_inj : Function.Injective (fun x : X => ⟨σ x, Set.mem_range_self x⟩ : X → Set.range σ) := by
    intro x y hxy; grind
  have h_embedding : Topology.IsEmbedding (fun x : X => ⟨σ x, Set.mem_range_self x⟩ : X → Set.range σ) := by
    refine ⟨?_, h_inj⟩
    rw [Topology.isInducing_iff_nhds]; intro x
    refine le_antisymm ?_ ?_
    · rw [Filter.le_def]
      simp +decide only [nhds_induced, Filter.mem_comap, forall_exists_index, and_imp]
      intro U V W hW hV hU
      filter_upwards [τ.continuousAt hW] with y hy using hU <| hV <| by simpa using hy
    · intro s hs
      refine ⟨{y : {x // x ∈ range σ} | hσ y.val ∈ s}, ?_, ?_⟩
      · rw [mem_nhds_iff] at hs ⊢
        obtain ⟨t, ht₁, ht₂, ht₃⟩ := hs
        refine ⟨{y : {x // x ∈ range σ} | hσ y.val ∈ t}, fun y hy => ht₁ hy,
          ht₂.preimage (hτ.comp_continuous continuous_subtype_val fun x => by simp +decide),
          by grind +splitImp⟩
      · grind
  refine ⟨?_, ?_⟩
  exact fun x => σ x
  rw [Topology.isEmbedding_iff] at *
  rw [Topology.isInducing_iff_nhds] at *
  convert h_embedding using 1
  · simp +decide [nhds_induced, Filter.comap_comap]
    rfl
  · simp +decide [Function.Injective]

/-- If `σ` and `g ∘ σ` are both topological embeddings, then `id` on the domain of `σ`
continuously reduces to `g`.  The reduction is `(σ, τ)` where `τ` is the inverse of the
embedding `g ∘ σ` on its image (a homeomorphism onto its range), extended arbitrarily off
the image.  This is the bridge turning the `nonscattered_embeds_id…` lemmas into reductions
`id_canonical ≤ f`. -/
lemma id_reduces_of_embedding_pair {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [Nonempty A]
    {g : B → C} {σ : A → B} (hσ : Continuous σ)
    (hgσ : Topology.IsEmbedding (g ∘ σ)) :
    ContinuouslyReduces (@id A) g := by
  classical
  let e : A ≃ₜ ↥(Set.range (g ∘ σ)) := hgσ.toHomeomorph
  refine ⟨σ, hσ,
    fun y => if h : y ∈ Set.range (g ∘ σ) then e.symm ⟨y, h⟩ else Classical.arbitrary A,
    ?_, ?_⟩
  · -- `τ` is `e.symm` on the image, hence continuous there.
    rw [continuousOn_iff_continuous_restrict]
    have hcongr : (Set.range (g ∘ σ)).restrict
        (fun y => if h : y ∈ Set.range (g ∘ σ) then e.symm ⟨y, h⟩ else Classical.arbitrary A)
        = fun p : Set.range (g ∘ σ) => e.symm p := by
      funext p; simp only [Set.restrict_apply, dif_pos p.2, Subtype.coe_eta]
    rw [hcongr]
    exact e.symm.continuous
  · -- correctness: `a = e.symm (e a)`.
    intro a
    have ha : g (σ a) ∈ Set.range (g ∘ σ) := ⟨a, rfl⟩
    show a = dite (g (σ a) ∈ Set.range (g ∘ σ))
      (fun h => e.symm ⟨g (σ a), h⟩) (fun _ => Classical.arbitrary A)
    rw [dif_pos ha]
    exact (e.symm_apply_apply a).symm

end EmbeddingAndReduction

section BasicReductionFacts

theorem restriction_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) :
    ContinuouslyReduces (f ∘ (Subtype.val : A → X)) f :=
  ⟨Subtype.val, continuous_subtype_val, id, continuousOn_id, fun _ => rfl⟩

theorem reduces_to_id_of_retract {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f)
    {σ : X → Z} (hσ : Continuous σ)
    {τ : Z → X} (hτ : Continuous τ)
    (hστ : ∀ x, τ (σ x) = x) :
    ContinuouslyReduces f (@id Z) :=
  ⟨σ, hσ, f ∘ τ, (hf.comp hτ).continuousOn, fun x => by simp [hστ x]⟩

end BasicReductionFacts

section ContRedonEmbed

/-- If `(σ,τ)` reduces an injective `f` to `g`, then `σ` is injective. -/
theorem ContinuouslyReduces.sigma_injective
    {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hf : Injective f)
    (hred : ∀ x, f x = τ (g (σ x))) : Injective σ :=
  fun x1 x2 hσ => hf (by rw [hred x1, hred x2, hσ])

/-- If `(σ,τ)` reduces an injective `f` to `g`, then `τ` is injective on the range
of `g ∘ σ`. -/
theorem ContinuouslyReduces.tau_injective_on_range
    {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hf : Injective f)
    (hred : ∀ x, f x = τ (g (σ x))) : InjOn τ (Set.range (g ∘ σ)) := by
  rintro _ ⟨x1, rfl⟩ _ ⟨x2, rfl⟩ hτ
  simp only [comp_apply] at hτ
  have h1 : f x1 = f x2 := by rw [hred x1, hred x2, hτ]
  rw [hf h1]

/-!
## Helper lemmas for combining clopen partition pieces
-/

/-- ContinuouslyReduces is preserved under restriction to a subtype. -/
lemma ContinuouslyReduces.restrict_subtype
    {A : Type*} [TopologicalSpace A] {Y : Type*} [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : A → Y} {g : X' → Y'} (hfg : ContinuouslyReduces f g)
    (D : Set A) :
    ContinuouslyReduces (fun x : D => f x.val) g := by
  cases hfg
  rename_i h₁ h₂
  use fun x => h₁ x
  refine ⟨h₂.1.comp continuous_subtype_val, h₂.2.choose, ?_, ?_⟩
  · refine' h₂.2.choose_spec.1.mono _
    exact Set.range_subset_iff.2 fun x => ⟨x, rfl⟩
  · exact fun x => h₂.2.choose_spec.2 x

/-- ContinuouslyReduces from a function on D ⊆ C, given a reduction from C. -/
lemma ContinuouslyReduces.restrict_of_subset
    {A : Type*} [TopologicalSpace A] {Y : Type*} [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : A → Y} {g : X' → Y'}
    {C D : Set A} (hDC : D ⊆ C)
    (hfg : ContinuouslyReduces (fun x : C => f x.val) g) :
    ContinuouslyReduces (fun x : D => f x.val) g := by
  obtain ⟨σ, τ, hσ, hτ, h_eq⟩ := hfg
  use fun x => σ ⟨x.val, hDC x.prop⟩
  refine ⟨?_, ?_⟩
  · fun_prop
  · refine ⟨hσ, hτ.mono ?_, ?_⟩
    · grind
    · exact fun x => h_eq ⟨x, hDC x.2⟩


end ContRedonEmbed

section HomeomorphicFunctions

/-- Two functions are homeomorphic if there are homeomorphisms `σ` and `τ` such that
`f = τ ∘ f' ∘ σ`.
-/
def HomeomorphicFun {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (f' : X' → Y') : Prop :=
  ∃ (σ : X ≃ₜ X') (τ : Y' → Y),
    ContinuousOn τ (Set.range f') ∧
    ∃ (τ_inv : Y → Y'), ContinuousOn τ_inv (Set.range f) ∧
      (∀ y' ∈ Set.range f', τ_inv (τ y') = y') ∧
      (∀ y ∈ Set.range f, τ (τ_inv y) = y) ∧
      ∀ x, f x = τ (f' (σ x))

theorem HomeomorphicFun.continuouslyEquiv {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {f' : X' → Y'}
    (h : HomeomorphicFun f f') : ContinuouslyEquiv f f' := by
  obtain ⟨σ, τ, hτ_cont, τ_inv, hτ_inv_cont, hτ_inv_left, hτ_inv_right, hred⟩ := h
  constructor
  · refine ⟨σ, σ.continuous, τ, ?_, hred⟩
    exact hτ_cont.mono (Set.range_comp_subset_range σ f')
  · refine ⟨σ.symm, σ.symm.continuous, τ_inv, ?_, fun x' => ?_⟩
    · exact hτ_inv_cont.mono (Set.range_comp_subset_range σ.symm f)
    · have hmem : f (σ.symm x') ∈ Set.range f := Set.mem_range_self _
      have hfx' : f (σ.symm x') = τ (f' x') := by
        have := hred (σ.symm x')
        simp only [σ.apply_symm_apply] at this
        exact this
      rw [hfx', hτ_inv_left (f' x') (Set.mem_range_self _)]


end HomeomorphicFunctions

section Scattered

/-!
## Scattered Functions

A function `f` between topological spaces is *scattered* if every nonempty subset of its
domain contains a nonempty open set on which `f` is constant.

This parallels the notion of scattered space (every nonempty subset has an isolated point).

Every continuous function with a scattered image is scattered, but scattered continuous
functions may have a non-scattered image or domain.
-/

/-- A function `f : X → Y` is *scattered* if every nonempty subset `S` of `X`
contains a nonempty relatively open subset on which `f` is constant.

More precisely: for every nonempty `S ⊆ X`, there exists a nonempty open set `U` such
that `U ∩ S` is nonempty and `f` is constant on `U ∩ S`. -/
def ScatteredFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ S : Set X, S.Nonempty → ∃ U : Set X, IsOpen U ∧ (U ∩ S).Nonempty ∧
    ∀ x ∈ U ∩ S, ∀ x' ∈ U ∩ S, f x = f x'

/-- `ScatteredFun` is invariant under precomposition with a homeomorphism. -/
lemma ScatteredFun.comp_homeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Z} (hf : ScatteredFun f) (e : Y ≃ₜ X) :
    ScatteredFun (f ∘ e) := by
  intro S hS
  -- push S forward to X via e
  have hSe : (e '' S).Nonempty := hS.image e
  obtain ⟨U, hU_open, hU_ne, hU_const⟩ := hf (e '' S) hSe
  -- pull U back to Y via e
  refine ⟨e ⁻¹' U, e.continuous.isOpen_preimage U hU_open, ?_, ?_⟩
  · obtain ⟨x, hxU, hxS⟩ := hU_ne
    obtain ⟨y, hyS, hye⟩ := hxS
    exact ⟨y, by rw [Set.mem_preimage, hye]; exact hxU, hyS⟩
  · intro y hy y' hy'
    have h1 : e y ∈ U ∩ e '' S := ⟨hy.1, ⟨y, hy.2, rfl⟩⟩
    have h2 : e y' ∈ U ∩ e '' S := ⟨hy'.1, ⟨y', hy'.2, rfl⟩⟩
    have := hU_const (e y) h1 (e y') h2
    simpa [Function.comp] using this

end Scattered

section CantorBendixson

/-!
## Cantor–Bendixson Derivative for Functions

The set of points at which a function `f` is locally constant is open. The restriction
of `f` to the complement of this set defines the *Cantor–Bendixson derivative* of `f`.

The *perfect kernel* of `f` is the fixed point of iterated derivatives, and the
*Cantor–Bendixson rank* is the minimal ordinal at which the fixed point is reached.
-/

/-- The set of points at which `f` is locally constant. -/
def locallyConstantLocus {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x}

/--
The locally constant locus is open.
-/
theorem isOpen_locallyConstantLocus {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsOpen (locallyConstantLocus f) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro x ⟨U, hUo, hxU, hU⟩
  exact ⟨U, fun y hy => ⟨U, hUo, hy, fun z hz => by rw [hU z hz, hU y hy]⟩, hUo, hxU⟩

end CantorBendixson

-- omega1 is defined in BQO.WQO (imported via BQO.OrdinalBQO)
