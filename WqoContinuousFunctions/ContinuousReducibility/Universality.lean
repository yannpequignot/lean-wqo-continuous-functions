import Mathlib
import WqoContinuousFunctions.ContinuousReducibility.Defs
import WqoContinuousFunctions.ContinuousReducibility.Scattered.NonScattered
import ZeroDimensionalSpaces.Universality

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Universality lemmas for continuous reducibility

A few general facts saying that a function reduces to an identity map, used to identify the
*top* elements in the proofs of `MainTheorem1` and `MainTheorem2`:

* `reduces_to_codomain_id` — `f ≤ id_Y` for any continuous `f : X → Y`;
* `id_le_id_of_embedding` — `id_Y ≤ id_Z` when `Y` embeds in `Z`;
* `reduces_to_id_of_domain_embedding` — `f ≤ id_Z` when the *domain* of `f` embeds in `Z`.

These live in their own file (rather than `Defs`) so they do not enter the global environment
of the `PointedGluing` developments, whose `grind +suggestions` proofs are sensitive to the
set of available declarations.

The **universality of `CantorRat`** for countable metrizable spaces
(`countable_metrizable_embeds_cantorRat`) lives in `ZeroDimensionalSpaces.Universality`, derived
from the Sierpiński embedding theorem `sierpinski_universal`. It is imported here for use by
`MainTheorem2`.
-/

/-- Any continuous `f : X → Y` reduces to the identity on its codomain (`σ = f`, `τ = id`). -/
lemma reduces_to_codomain_id {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : ContinuouslyReduces f (@id Y) :=
  ⟨f, hf, id, continuousOn_id, fun _ => rfl⟩

/-- If `Y` embeds in `Z`, then `id_Y` reduces to `id_Z` (special case of
`id_reduces_of_embedding_pair` with `g = id_Z`). -/
lemma id_le_id_of_embedding {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [Nonempty Y] {ι : Y → Z} (hι : Topology.IsEmbedding ι) :
    ContinuouslyReduces (@id Y) (@id Z) :=
  id_reduces_of_embedding_pair (g := @id Z) hι.continuous (by simpa using hι)

/-- If the *domain* of a continuous `f : X → Y` embeds in `Z`, then `f` reduces to `id_Z`:
take `σ` to be the embedding and `τ = f ∘ σ⁻¹` on the image (extended arbitrarily off it).
This is the universality used by `MainTheorem1`, whose Polish domains embed in the Cantor
space. -/
lemma reduces_to_id_of_domain_embedding {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [Nonempty Y]
    {f : X → Y} (hf : Continuous f) {σ : X → Z} (hσ : Topology.IsEmbedding σ) :
    ContinuouslyReduces f (@id Z) := by
  classical
  let e : X ≃ₜ ↥(Set.range σ) := hσ.toHomeomorph
  refine ⟨σ, hσ.continuous,
    fun z => if h : z ∈ Set.range σ then f (e.symm ⟨z, h⟩) else Classical.arbitrary Y, ?_, ?_⟩
  · rw [show Set.range (@id Z ∘ σ) = Set.range σ from by rw [Function.id_comp],
      continuousOn_iff_continuous_restrict]
    have hcongr : (Set.range σ).restrict
        (fun z => if h : z ∈ Set.range σ then f (e.symm ⟨z, h⟩) else Classical.arbitrary Y)
        = fun p : Set.range σ => f (e.symm p) := by
      funext p; simp only [Set.restrict_apply, dif_pos p.2, Subtype.coe_eta]
    rw [hcongr]
    exact hf.comp e.symm.continuous
  · intro x
    have hx : σ x ∈ Set.range σ := ⟨x, rfl⟩
    show f x = dite (σ x ∈ Set.range σ)
      (fun h => f (e.symm ⟨σ x, h⟩)) (fun _ => Classical.arbitrary Y)
    rw [dif_pos hx]
    exact congrArg f (e.symm_apply_apply x).symm

-- `countable_metrizable_embeds_cantorRat` (used by `MainTheorem2`) is provided by
-- `ZeroDimensionalSpaces.Universality` via the import above.