import WqoContinuousFunctions.ScatFun.Defs
import WqoContinuousFunctions.ContinuousReducibility.Gluing.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Plain gluing `gl` and the empty function, as operations on `ScatFun`

Split out of the former monolithic `ScatFun/Operations.lean` so that the many downstream
consumers that only need the **plain gluing** `gl` / `empty` can import this light module
(depending only on `ScatFun.Defs` and the gluing primitives) rather than pulling in the whole
pointed-gluing / `MaxFun` / `MinFun` machinery.

* `ScatFun.gl`     — plain gluing of a sequence of `ScatFun`s
* `ScatFun.empty`  — the empty-domain `ScatFun` (used to pad finite families)
* `ScatFun.reduces_iff` — `Reduces` is definitionally `ContinuouslyReduces` on `.func`s
-/

namespace ScatFun

/-! ## Reduction is definitionally `ContinuouslyReduces` on the underlying functions -/

/-- `ScatFun.Reduces F G` is, by definition, `ContinuouslyReduces F.func G.func`.
This lemma lets the many raw-function reduction results in `PointedGluing/*` be
re-used verbatim against bundled `ScatFun`s. -/
lemma reduces_iff (F G : ScatFun) :
    Reduces F G ↔ ContinuouslyReduces F.func G.func := Iff.rfl

/-! ## Plain gluing as an operation on `ScatFun`

The **plain** gluing `gl F` of a sequence `F : ℕ → ScatFun` adds **no** base point: its domain
is exactly `⊔ᵢ (i)⌢(F i).domain`.  Scatteredness and continuity are inherited from the
plain-gluing preservation lemmas (Fact 2.16). -/

/-- The block functions feeding `GluingFunVal`: send `a ∈ (F i).domain` to `(F i).func a`,
viewed as landing in `univ`. -/
def glBlock (F : ℕ → ScatFun) (i : ℕ) :
    (F i).domain → (Set.univ : Set Baire) :=
  fun a => ⟨(F i).func a, Set.mem_univ _⟩

/-- **Plain gluing of `ScatFun`s.**  `gl F` has domain `⊔ᵢ (i)⌢(F i).domain` and
acts blockwise by `F i`.  Scatteredness and continuity are inherited from the
plain-gluing preservation lemmas `gluingFun_scattered` /
`gluingFunVal_preserves_continuity` (Fact 2.16). -/
def gl (F : ℕ → ScatFun) : ScatFun where
  domain := GluingSet (fun i => (F i).domain)
  func := fun x =>
    GluingFunVal (fun i => (F i).domain) (fun _ => Set.univ) (glBlock F) x
  hScat :=
    -- `(glBlock F i a : ℕ → ℕ)` is definitionally `(F i).func a`, so the
    -- per-block scatteredness hypotheses are exactly `(F i).hScat`.
    gluingFun_scattered (fun i => (F i).domain) (fun _ => Set.univ) (glBlock F)
      (fun i => (F i).hScat)
  hCont :=
    gluingFunVal_preserves_continuity (fun i => (F i).domain) (fun _ => Set.univ)
      (glBlock F) (fun i => (F i).hCont.subtype_mk _)

@[simp] lemma gl_domain (F : ℕ → ScatFun) :
    (gl F).domain = GluingSet (fun i => (F i).domain) := rfl

/-- The trivial **empty** scattered continuous function (empty domain).  Used to
pad the infinite tail of the `ℕ`-indexed family feeding `gl`. -/
def empty : ScatFun where
  domain := ∅
  func   := fun x => (Set.notMem_empty x.1 x.2).elim
  hScat  := fun _ hS => (Set.notMem_empty hS.choose.1 hS.choose.2).elim
  hCont  := continuous_of_const (fun x => (Set.notMem_empty x.1 x.2).elim)

/-- `ScatFun.empty` reduces to any `ScatFun` — its domain is empty, so the
reduction `(σ, τ)` is vacuous. -/
lemma empty_reduces (G : ScatFun) : Reduces empty G := by
  refine ⟨fun x => (Set.notMem_empty x.1 x.2).elim, continuous_of_const fun x => by tauto,
    id, continuousOn_id, fun x => (Set.notMem_empty x.1 x.2).elim⟩

/-- `ScatFun.empty` has CB-rank `0` (its domain is empty). -/
lemma empty_cbRank : CBRank ScatFun.empty.func = 0 := by
  refine le_antisymm ?_ ?_;
  · refine csInf_le ?_ ?_;
    · exact ⟨ 0, fun α hα => zero_le α ⟩;
    · simp +decide [ CBLevel ];
      ext ; aesop;
  · exact zero_le _

end ScatFun

end
