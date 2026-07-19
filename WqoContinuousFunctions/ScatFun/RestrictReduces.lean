import WqoContinuousFunctions.ScatFun.Operations
import WqoContinuousFunctions.ScatFun.Basics
import WqoContinuousFunctions.ContinuousReducibility.Gluing.UpperBound

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# Basic reduction facts for `restrict` and `gl`

Two general-purpose `ScatFun` reduction lemmas, collected here (upstream of the specialized
`Wedge`/`CenteredFunctions` developments that first needed them) so they have a single canonical
home:

* `ScatFun.gl_func_prepend` — the block-preserving action of a plain gluing on a tagged point
  `(i)⌢a`.
* `restrict_reduces_of_subset` — restricting a `ScatFun` to a smaller domain set reduces to
  restricting to a larger one.

Both are pure facts about `gl` / `restrict` (no scattered-successor or wedge structure), so they
belong next to those operations rather than in a downstream file.
-/

namespace ScatFun

/-- The block-preserving glued map on a tagged point `(i)⌢a`. -/
lemma gl_func_prepend (F : ℕ → ScatFun) (i : ℕ) (a : ↥(F i).domain)
    (hmem : prepend i a.val ∈ (gl F).domain) :
    (gl F).func ⟨prepend i a.val, hmem⟩ = prepend i ((F i).func a) := by
  show GluingFunVal (fun i => (F i).domain) (fun _ => Set.univ) (glBlock F)
      ⟨prepend i a.val, hmem⟩ = prepend i ((F i).func a)
  rw [GluingFunVal_prepend (fun i => (F i).domain) (fun _ => Set.univ) (glBlock F) i a hmem]
  rfl

end ScatFun

/-
Restricting a `ScatFun` to a smaller domain set reduces to restricting to a larger one
(via the inclusion).
-/
lemma restrict_reduces_of_subset (g : ScatFun) {S S' : Set ↑g.domain} (hSS : S ⊆ S') :
    ScatFun.Reduces (g.restrict S) (g.restrict S') := by
  use fun x => ⟨x.val, x.property.choose, hSS x.property.choose_spec⟩;
  refine ⟨ ?_, ?_ ⟩;
  · fun_prop;
  · exact ⟨ fun x => x, continuousOn_id, fun x => rfl ⟩


/-! ## Canonical block decomposition of a plain gluing `gl F`

The `k`-th block `glBlockSet F k = {x | x 0 = k}` gives the canonical clopen partition of
`(gl F).domain`, with each block reducing to the component `F k` (reverse of
`reduces_block_gl`). Used to apply the intertwining-piece lemmas to a `gl`/`glWindow`. -/

/-- The `k`-th **block set** of a plain gluing `gl F`: the points whose first coordinate is
`k` (`{x | (x:ℕ→ℕ) 0 = k}`). The canonical clopen partition of `(gl F).domain`. -/
def glBlockSet (F : ℕ → ScatFun) (k : ℕ) : Set ↑(ScatFun.gl F).domain :=
  {x | (x : ℕ → ℕ) 0 = k}

lemma glBlockSet_clopen (F : ℕ → ScatFun) (k : ℕ) : IsClopen (glBlockSet F k) := by
  have hcont : Continuous (fun x : ↑(ScatFun.gl F).domain => (x : ℕ → ℕ) 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have : glBlockSet F k = (fun x : ↑(ScatFun.gl F).domain => (x : ℕ → ℕ) 0) ⁻¹' {k} := by
    ext x; simp [glBlockSet]
  rw [this]; exact (isClopen_discrete _).preimage hcont

lemma gl_isDisjointUnion_blockSet (F : ℕ → ScatFun) :
    (ScatFun.gl F).IsDisjointUnion (glBlockSet F) := by
  refine ⟨glBlockSet_clopen F, ?_, ?_⟩
  · exact fun i j hij => Set.disjoint_left.mpr fun x hi hj =>
      hij ((hi : (x : ℕ → ℕ) 0 = i).symm.trans hj)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨(x : ℕ → ℕ) 0, rfl⟩

lemma glBlockSet_eq_empty (F : ℕ → ScatFun) (k : ℕ) (hk : IsEmpty ↑(F k).domain) :
    glBlockSet F k = ∅ := by
  ext x
  simp only [glBlockSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx0
  obtain ⟨i, hi0, hi⟩ := GluingSet_inverse_short (fun i => (F i).domain) x
  have hik : i = k := by rw [← hi0]; exact hx0
  exact hk.false ⟨unprepend x.val, hik ▸ hi⟩

/-- **Extraction of a `gl`-block.** The block `(gl F).restrict (glBlockSet F k)` reduces to the
`k`-th component `F k` (reverse of `reduces_block_gl`): strip the `k`-prefix (`σ = unprepend`,
`τ = prepend k`). -/
lemma gl_restrict_blockSet_reduces (F : ℕ → ScatFun) (k : ℕ) :
    ScatFun.Reduces ((ScatFun.gl F).restrict (glBlockSet F k)) (F k) := by
  have hmem : ∀ z : ↑((ScatFun.gl F).restrict (glBlockSet F k)).domain,
      unprepend (z : ℕ → ℕ) ∈ (F k).domain := by
    intro z
    obtain ⟨i, hi0, hi⟩ := GluingSet_inverse_short (fun i => (F i).domain) ⟨z.val, z.2.choose⟩
    have hz0 : z.val 0 = k := z.2.choose_spec
    have hik : i = k := by rw [← hi0]; exact hz0
    exact hik ▸ hi
  refine ⟨fun z => ⟨unprepend z.val, hmem z⟩, ?_, prepend k, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_unprepend.comp continuous_subtype_val) _
  · exact (continuous_prepend k).continuousOn
  · intro z
    have hz0 : z.val 0 = k := z.2.choose_spec
    show (ScatFun.gl F).func ⟨z.val, z.2.choose⟩ = prepend k ((F k).func ⟨unprepend z.val, hmem z⟩)
    have hval : z.val = prepend k (unprepend z.val) := by
      conv_lhs => rw [← prepend_unprepend z.val]; rw [hz0]
    have hpt : (⟨z.val, z.2.choose⟩ : ↑(ScatFun.gl F).domain)
        = ⟨prepend k (unprepend z.val), mem_gluingSet_prepend (hmem z)⟩ := Subtype.ext hval
    rw [hpt, ScatFun.gl_func_prepend F k ⟨unprepend z.val, hmem z⟩ (mem_gluingSet_prepend (hmem z))]

end
