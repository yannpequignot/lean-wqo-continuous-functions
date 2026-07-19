import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import WqoContinuousFunctions.ContinuousReducibility.Defs
import ZeroDimensionalSpaces.Basics
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.ScatFun.Defs

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Representation of scattered continuous functions by `ScatFun`

This file contains the key representation theorem feeding `MainTheorem3`: every function
satisfying its hypotheses is continuously equivalent to some `ScatFun` (a scattered continuous
function on a subset of Baire space).

**Proof idea.**
1. The domain `X` embeds into Baire via `ZeroDimensionalSpace.embedsBaire`.
2. The range `Set.range f` is countable by `Scattered_countable_range` (which needs
   `TotallyDisconnectedSpace`, supplied by `ZeroDimensionalSpace.totallyDisconnectedSpace`).
3. The range is countable metrizable, hence zero-dimensional
   (`ZeroDimensionalSpace.of_countable_metrizable`), hence embeds into Baire.
4. Conjugating `f` by these two homeomorphisms yields a `ScatFun` `H`.
5. The two homeomorphisms give a `ContinuouslyEquiv` between `f` and `H.func`.
-/

/-- Every scattered continuous function from a zero-dimensional separable metrizable
space to a metrizable space is continuously equivalent to a function in `ScatFun`.

**Note on `[Nonempty Y]`.**  This hypothesis is not a technical convenience; it is the
exact condition under which the statement is true, and it is forced by our definition of
`ContinuouslyReduces`, which uses a *total* map `τ : Y' → Y` (only required to be
`ContinuousOn` the relevant range).  Concretely:

* Every `ScatFun.func` has codomain `Baire`, which is nonempty (e.g. `zeroStream`).
* The direction `f ≤ H.func` therefore requires a total `τ : Baire → Y`.
* If `Y` were empty then `X` is empty and `f` is the empty function `∅ → ∅`; but the type
  `Baire → Y = Baire → ∅` is itself uninhabited, so `f ≤ H.func` fails for *every* `H`
  — not even `ScatFun.empty` works, since its codomain is `Baire`, not `∅`.

Thus an empty-codomain `f` reduces to no `ScatFun` at all (the reverse `ScatFun.empty.func ≤ f`
does hold, via the empty map `∅ → Baire`, which is the source of the asymmetry).  Excluding
this degenerate case with `[Nonempty Y]` is exactly what makes "equivalent to a `ScatFun`"
provable.  In the intended setting (functions into Baire-like, nonempty spaces) the
hypothesis is always satisfied. -/
lemma main3_to_ScatFun
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace X] [MetrizableSpace X] [ZeroDimensionalSpace X]
    [MetrizableSpace Y] [Nonempty Y]
    {f : X → Y} (hfc : Continuous f) (hsc : ScatteredFun f) :
    ∃ H : ScatFun, ContinuouslyEquiv f H.func := by
  classical
  -- Step 1: embed domain X into Baire
  obtain ⟨D, ⟨φ⟩⟩ := ZeroDimensionalSpace.embedsBaire (X := X)
  -- Step 2: range of f is countable
  have hcount : (Set.range f).Countable := Scattered_countable_range f hsc
  -- Step 3: embed range into Baire (range is separable metrizable countable → zero-dim)
  have : Countable (Set.range f) := hcount.to_subtype
  have hSepR : SeparableSpace (Set.range f) :=
    ((isSeparable_range hfc).mono subset_rfl).separableSpace
  obtain ⟨E, ⟨ψ⟩⟩ := ZeroDimensionalSpace.embedsBaire (X := Set.range f)
  -- Step 4: build ScatFun H with domain D ⊆ Baire
  -- H.func d = (ψ ⟨f (φ.symm d), _⟩).val  (conjugate by φ on domain, ψ on range)
  let f_rng : X → Set.range f := fun x => ⟨f x, Set.mem_range_self x⟩
  have hf_rng : Continuous f_rng := hfc.subtype_mk _
  -- scatteredness of H.func: postcompose f_rng with ψ (homeomorphism on range),
  -- then Subtype.val (any postcomposition preserves scatteredness),
  -- then precompose with φ.symm (via ScatteredFun.comp_homeomorph).
  have hH_scat : ScatteredFun (fun d : D => (ψ (f_rng (φ.symm d))).val) := by
    -- f_rng is scattered because f_rng x = y ↔ f x = y.val (same fibers)
    have hf_rng_scat : ScatteredFun f_rng := by
      intro S hS
      obtain ⟨U, hU, hUne, hUconst⟩ := hsc S hS
      -- `f_rng x = ⟨f x, _⟩`, so `f` constant on `U ∩ S` lifts to `f_rng` via `Subtype.ext`.
      exact ⟨U, hU, hUne, fun x hx x' hx' => Subtype.ext (hUconst x hx x' hx')⟩
    -- postcompose with ψ then Subtype.val: constants are preserved
    have hψfr_scat : ScatteredFun (Subtype.val ∘ ψ ∘ f_rng) := by
      intro S hS
      obtain ⟨U, hU, hUne, hUconst⟩ := hf_rng_scat S hS
      exact ⟨U, hU, hUne, fun x hx x' hx' => by
        simp only [Function.comp_apply, hUconst x hx x' hx']⟩
    exact hψfr_scat.comp_homeomorph φ.symm
  let H : ScatFun := {
    domain := D
    func   := fun d => (ψ (f_rng (φ.symm d))).val
    hCont  := (ψ.continuous.comp (hf_rng.comp φ.symm.continuous)).subtype_val
    hScat  := hH_scat }
  -- Step 5: ContinuouslyEquiv f H.func
  refine ⟨H, ?_, ?_⟩
  · -- `f ≤ H.func` via `σ = φ` and `τ = (Subtype.val ∘ ψ.symm)` on `E`, extended off `E`
    -- by an arbitrary value of `Y`.  This total `τ` is the only place `[Nonempty Y]` is used:
    -- without it the target type `Baire → Y` could be empty and no reduction would exist.
    set τ : Baire → Y :=
      fun b => if h : b ∈ E then (ψ.symm ⟨b, h⟩).val else Classical.arbitrary Y with hτ
    refine ⟨φ, φ.continuous, τ, ?_, ?_⟩
    · -- `range (H.func ∘ φ) ⊆ E`, and on `E`, `τ` agrees with the continuous `Subtype.val ∘ ψ.symm`.
      have hsub : Set.range (H.func ∘ φ) ⊆ E := by
        rintro _ ⟨x, rfl⟩; exact (ψ (f_rng (φ.symm (φ x)))).2
      refine ContinuousOn.mono ?_ hsub
      rw [hτ, continuousOn_iff_continuous_restrict]
      have hcongr : E.restrict
          (fun b => if h : b ∈ E then (ψ.symm ⟨b, h⟩).val else Classical.arbitrary Y)
          = fun p : E => (ψ.symm p).val := by
        funext p; simp only [Set.restrict_apply, dif_pos p.2, Subtype.coe_eta]
      rw [hcongr]
      exact continuous_subtype_val.comp ψ.symm.continuous
    · -- correctness: `f x = τ (H.func (φ x))`, using `φ.symm (φ x) = x` and `ψ.symm (ψ _) = _`.
      intro x
      have hHf : H.func (φ x) = (ψ (f_rng x)).val := by
        show (ψ (f_rng (φ.symm (φ x)))).val = (ψ (f_rng x)).val
        rw [φ.symm_apply_apply]
      rw [hHf, hτ]
      simp only [dif_pos (ψ (f_rng x)).2, Subtype.coe_eta]
      exact (congrArg Subtype.val (ψ.symm_apply_apply (f_rng x))).symm
  · -- `H.func ≤ f` via `σ = φ.symm` and `τ = (Subtype.val ∘ ψ)` on `range f`, extended off
    -- `range f` by `zeroStream ∈ Baire` (no nonemptiness assumption needed for this direction).
    set τ : Y → Baire :=
      fun y => if h : y ∈ Set.range f then (ψ ⟨y, h⟩).val else zeroStream with hτ
    refine ⟨φ.symm, φ.symm.continuous, τ, ?_, ?_⟩
    · refine ContinuousOn.mono ?_ (Set.range_comp_subset_range φ.symm f)
      rw [hτ, continuousOn_iff_continuous_restrict]
      have hcongr : (Set.range f).restrict
          (fun y => if h : y ∈ Set.range f then (ψ ⟨y, h⟩).val else zeroStream)
          = fun p : Set.range f => (ψ p).val := by
        funext p; simp only [Set.restrict_apply, dif_pos p.2, Subtype.coe_eta]
      rw [hcongr]
      exact continuous_subtype_val.comp ψ.continuous
    · -- correctness: `H.func d = τ (f (φ.symm d))`, since `f (φ.symm d) ∈ range f`.
      intro d
      rw [hτ]
      simp only [dif_pos (Set.mem_range_self (φ.symm d))]
      rfl
