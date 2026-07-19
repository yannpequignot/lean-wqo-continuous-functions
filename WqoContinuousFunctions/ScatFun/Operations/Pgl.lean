import WqoContinuousFunctions.ScatFun.Defs
import WqoContinuousFunctions.PointedGluing.Basics.Properties
import WqoContinuousFunctions.PointedGluing.MinFun.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Pointed gluing `pgl`, as an operation on `ScatFun`

Split out of the former monolithic `ScatFun/Operations.lean`.  The pointed gluing `pgl F`
differs from the plain gluing `gl F` (`ScatFun/Gl.lean`) by adding a base point `0^ω`; its
scatteredness and continuity are inherited from the `PointedGluingFun` preservation lemmas.

* `ScatFun.pgl`     — pointed gluing of a sequence of `ScatFun`s
* `ScatFun.rayOn`   — the `i`-th ray of a `ScatFun` at a base point, packaged as a `ScatFun`
* `ScatFun.pgl_reduces_of_local` / `pgl_reduces_of_local_base` — `pgl` as a lower bound
-/

namespace ScatFun

/-- The block functions feeding `PointedGluingFun`: send `a ∈ (F i).domain` to
`(F i).func a`, viewed as landing in the trivial target `univ`.  Keeping the target
as `univ` (rather than a tight `B i`) makes the preservation lemmas apply with no
side conditions, and the underlying `ℕ → ℕ` value is unchanged. -/
def pglBlock (F : ℕ → ScatFun) (i : ℕ) :
    (F i).domain → (Set.univ : Set Baire) :=
  fun a => ⟨(F i).func a, Set.mem_univ _⟩


/-- The `i`-th ray of a `ScatFun` `G` at base point `y`, intersected with a subset `S`
of the domain, packaged as a `ScatFun` via `G.restrict`. -/
noncomputable def rayOn (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (i : ℕ) :
    ScatFun :=
  G.restrict (S ∩ {a | G.func a ∈ RaySet Set.univ y i})


/-- **Pointed gluing of `ScatFun`s.**  `pgl F` has domain
`{0^ω} ∪ ⋃ᵢ (0)^i(1)·(F i).domain` and acts blockwise by `F i` (and fixes `0^ω`).

Scatteredness and continuity are inherited from the corresponding preservation
lemmas for `PointedGluingFun`, so callers never re-establish them. -/
def pgl (F : ℕ → ScatFun) : ScatFun where
  domain := PointedGluingSet (fun i => (F i).domain)
  func := fun x =>
    PointedGluingFun (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) x
  hScat := by
    -- `(pglBlock F i a : ℕ → ℕ)` is definitionally `(F i).func a`, so the
    -- per-block scatteredness hypotheses are exactly `(F i).hScat`.
    exact pointedGluing_scattered (fun i => (F i).domain) (fun _ => Set.univ)
      (pglBlock F) (fun i => (F i).hScat)
  hCont := by
    -- The preservation lemma yields continuity into `PointedGluingSet univ`;
    -- compose with `Subtype.val` to land in `Baire = ℕ → ℕ`.
    have hblock : ∀ i, Continuous (pglBlock F i) :=
      fun i => (F i).hCont.subtype_mk _
    exact continuous_subtype_val.comp
      (pointedGluingFun_preserves_continuity (fun i => (F i).domain)
        (fun _ => Set.univ) (pglBlock F) hblock)

@[simp] lemma pgl_domain (F : ℕ → ScatFun) :
    (pgl F).domain = PointedGluingSet (fun i => (F i).domain) := rfl

/-- `pgl F` fixes the base point `0^ω`. -/
lemma pgl_func_zeroStream (F : ℕ → ScatFun)
    (h : zeroStream ∈ (pgl F).domain) :
    (pgl F).func ⟨zeroStream, h⟩ = zeroStream := by
  show PointedGluingFun (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F)
      ⟨zeroStream, h⟩ = zeroStream
  unfold PointedGluingFun
  simp

/-- `pgl F` on block `j`: it maps `(0)^j(1)·w` to `(0)^j(1)·(F j).func w`. -/
lemma pgl_func_block (F : ℕ → ScatFun) (j : ℕ) (w : (F j).domain) :
    (pgl F).func ⟨prependZerosOne j w.val,
        prependZerosOne_mem_pointedGluingSet _ j w.val w.prop⟩
      = prependZerosOne j ((F j).func w) := by
  have hblk : prependZerosOne j w.val ∈ blockSet j := prependZerosOne_mem_blockSet j w.val
  show PointedGluingFun (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F)
      ⟨prependZerosOne j w.val, _⟩ = _
  rw [pointedGluingFun_block_eq (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) j
    ⟨prependZerosOne j w.val, _⟩ hblk]
  show prependZerosOne j ((F j).func ⟨stripZerosOne j (prependZerosOne j w.val), _⟩) = _
  congr 2
  exact Subtype.ext (stripZerosOne_prependZerosOne j w.val)

/-- **Pointed gluing as a lower bound, `ScatFun` form.**  To prove `pgl F ≤ G` it
suffices to provide, for each block `i` and each open neighbourhood `V` of a fixed
point `x : G.domain`, a continuous reduction of `(F i).func` into `G` whose image stays
in `V` and the closure of whose `G`-image avoids `G.func x`.

This is `pointedGluing_lower_bound` repackaged at the `ScatFun` level: the block
functions read as `(F i).func` and the target as `G.func`, instead of the underlying
`PointedGluingFun`/`pglBlock`.  That identification (and the `↑(pglBlock F i z)`
coercion) is exactly what makes the raw lemma awkward to apply, so callers proving a
pointed gluing is a lower bound should prefer this form. -/
lemma pgl_reduces_of_local (F : ℕ → ScatFun) (G : ScatFun) (x : ↥G.domain)
    (hloc : ∀ (i : ℕ) (V : Set ↥G.domain), IsOpen V → x ∈ V →
      ∃ (σ : (F i).domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        (∀ z, (F i).func z = τ (G.func (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => G.func (σ z))) ∧
        (∀ z, σ z ∈ V) ∧
        G.func x ∉ closure (Set.range (fun z => G.func (σ z)))) :
    Reduces (pgl F) G := by
  show ContinuouslyReduces (pgl F).func G.func
  obtain ⟨σ, hσ, -, τ, hτ, heq⟩ := pointedGluing_lower_bound (A := G.domain) G.func G.hCont
    (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) x hloc
  exact ⟨σ, hσ, τ, hτ, heq⟩

/-- **`pgl_reduces_of_local`, base-point–exposed form.**  Identical hypotheses, but the
conclusion exposes the reduction's `σ` together with `σ ⟨zeroStream,_⟩ = x` — i.e. the gluing's
distinguished point is sent to the anchor `x`.  Needed by `centerInvariance_equiv` to certify
that `x` is a center (used in Theorem 4.7's Case B). -/
lemma pgl_reduces_of_local_base (F : ℕ → ScatFun) (G : ScatFun) (x : ↥G.domain)
    (hloc : ∀ (i : ℕ) (V : Set ↥G.domain), IsOpen V → x ∈ V →
      ∃ (σ : (F i).domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        (∀ z, (F i).func z = τ (G.func (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => G.func (σ z))) ∧
        (∀ z, σ z ∈ V) ∧
        G.func x ∉ closure (Set.range (fun z => G.func (σ z)))) :
    ∃ σ : ↥(pgl F).domain → ↥G.domain, Continuous σ ∧
      σ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ = x ∧
      ∃ τ : Baire → Baire, ContinuousOn τ (Set.range (G.func ∘ σ)) ∧
        ∀ z, (pgl F).func z = τ (G.func (σ z)) :=
  pointedGluing_lower_bound (A := G.domain) G.func G.hCont
    (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) x hloc

end ScatFun

end
