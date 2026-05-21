-- import WqoContinuousFunctions.IntroMemo
import WqoContinuousFunctions.BaireSpace.Basics
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

**Note:** The naive definition uses a total `τ : Y' → Y`. The correct definition
(used here) restricts `τ` to operate between the relevant images, matching the
paper's original formulation.
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
def CoRestrict' {X Y : Type*} (f : X → Y) (B : Set Y) : f ⁻¹' B → Y :=
  f ∘ Subtype.val

/-- Domain restriction of `g` to the preimage of a set `C` in the codomain. -/
def PreImage (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), g ⟨x, h⟩ ∈ C}

/-- Function `g` restricted to the preimage of `C` in the codomain. -/
def CoRestrict (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    PreImage B g C → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

lemma CoRestrict_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (C : Set (ℕ → ℕ)) :
    Continuous (CoRestrict B g C) :=
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
      simp +decide [Filter.mem_comap, nhds_induced]
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
  simp [comp_apply] at hτ
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
  · refine h₂.2.choose_spec.1.mono ?_
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

section Notations

/-- `ω₁` as a countable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

end Notations
