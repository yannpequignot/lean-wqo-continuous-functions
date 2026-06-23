import WqoContinuousFunctions.ScatFun.Defs
import WqoContinuousFunctions.PointedGluing.Basics.Properties
import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers
import WqoContinuousFunctions.PointedGluing.CBRank.Helpers
import WqoContinuousFunctions.PointedGluing.MinFun.Theorems
import WqoContinuousFunctions.ContinuousReducibility.Gluing.Defs
import WqoContinuousFunctions.ContinuousReducibility.Gluing.UpperBound

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Bundled operations on `ScatFun`

This file is the first slice of the **bundled-operations layer** (Option A of the
refactor).  The goal is to make the gluing / pointed-gluing constructions of the
memoir into *closed operations on `ScatFun`*, so that scatteredness and continuity
are discharged **once** here and never re-threaded through the downstream structure
theorems (centered functions, precise structure, double successors).

## Design

A `ScatFun` bundles a domain `A ⊆ Baire`, a function `func : A → Baire`, and proofs
`hScat`/`hCont`.  Every operation in the memoir already lives on
`Set (ℕ → ℕ) = Set Baire` and produces functions into `ℕ → ℕ = Baire`, so these are
genuinely closed operations on `ScatFun` — no universe polymorphism or ad-hoc
topology instances are needed.

Each smart constructor wires its `hScat`/`hCont` fields to the already-proved
preservation lemmas:

* `ScatFun.pgl`     ← `pointedGluing_scattered` + `pointedGluingFun_preserves_continuity`
* `ScatFun.maxFun`  ← `maxfun_is_scatter_leq_α`        (`MaxFun = Subtype.val`)
* `ScatFun.minFun`  ← `minfun_is_scatter_leq_succ_α`   (`MinFun = Subtype.val`)

## Main definitions

* `ScatFun.pgl`    — pointed gluing of a sequence of `ScatFun`s, as a `ScatFun`
* `ScatFun.maxFun` — the maximum function `ℓ_α`, bundled
* `ScatFun.minFun` — the minimum function `k_{α+1}`, bundled
-/

namespace ScatFun

/-! ## Reduction is definitionally `ContinuouslyReduces` on the underlying functions -/

/-- `ScatFun.Reduces F G` is, by definition, `ContinuouslyReduces F.func G.func`.
This lemma lets the many raw-function reduction results in `PointedGluing/*` be
re-used verbatim against bundled `ScatFun`s. -/
lemma reduces_iff (F G : ScatFun) :
    Reduces F G ↔ ContinuouslyReduces F.func G.func := Iff.rfl

/-! ## Pointed gluing as an operation on `ScatFun` -/

/-- The block functions feeding `PointedGluingFun`: send `a ∈ (F i).domain` to
`(F i).func a`, viewed as landing in the trivial target `univ`.  Keeping the target
as `univ` (rather than a tight `B i`) makes the preservation lemmas apply with no
side conditions, and the underlying `ℕ → ℕ` value is unchanged. -/
def pglBlock (F : ℕ → ScatFun) (i : ℕ) :
    (F i).domain → (Set.univ : Set Baire) :=
  fun a => ⟨(F i).func a, Set.mem_univ _⟩

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
  exact pointedGluing_lower_bound (A := G.domain) G.func G.hCont
    (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) x hloc

/-! ## Plain gluing as an operation on `ScatFun`

The **plain** gluing `gl F` of a sequence `F : ℕ → ScatFun` differs from the
pointed gluing `pgl F` in that it adds **no** base point: its domain is exactly
`⊔ᵢ (i)⌢(F i).domain`.  Scatteredness and continuity are inherited from the
plain-gluing preservation lemmas (Fact 2.16), exactly as `pgl` inherits them
from the pointed-gluing versions. -/

/-- The block functions feeding `GluingFunVal`, mirroring `pglBlock`: send
`a ∈ (F i).domain` to `(F i).func a`, viewed as landing in `univ`. -/
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

/-! ## Reduction lemmas for the plain gluing `gl` (and `gl` ↪ `pgl`)

Relocated here (next to `gl`/`pgl`) from `ScatFun/FiniteGluing.lean` so they can be
reused independently of the `FinGl` development. -/

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

/-- **Pasting the per-block `σ`-maps of a gluing reduction.**  Given continuous
block maps `k i : A i → A' i`, there is a continuous map on `GluingSet A` sending
the block-`i` point `(i)⌐a` to `(i)⌐(k i a)`.  (Here it is realised directly as the
gluing of the block maps, whose continuity is `gluingFunVal_preserves_continuity`.) -/
lemma gluedSigma_continuous {A A' : ℕ → Set Baire}
    (k : ∀ i, ↑(A i) → ↑(A' i)) (hk : ∀ i, Continuous (k i)) :
    ∃ s : ↑(GluingSet A) → ↑(GluingSet A'), Continuous s ∧
      ∀ (i : ℕ) (a : ↑(A i)),
        s ⟨prepend i a.val, mem_gluingSet_prepend a.prop⟩
          = ⟨prepend i (k i a).val, mem_gluingSet_prepend (k i a).prop⟩ := by
  refine ⟨fun x => ⟨GluingFunVal A A' k x, ?_⟩, ?_, ?_⟩
  · unfold GluingFunVal; grind +suggestions
  · exact (gluingFunVal_preserves_continuity A A' k hk).subtype_mk _
  · intro i a; unfold GluingFunVal; aesop

/-- **Pasting the per-block `τ`-maps of a gluing reduction.**  If, on each block
`S ∩ {z | z 0 = i}`, the map `z ↦ (i)⌐(k i (unprepend z))` is continuous, then the
blockwise map `y ↦ (y 0)⌐(k (y 0) (unprepend y))` is continuous on `S`.  (Proved by
`continuousOn_piecewise_clopen`.) -/
lemma gluedTau_continuousOn (S : Set Baire) (k : ℕ → Baire → Baire)
    (hk : ∀ i, ContinuousOn (fun z => prepend i (k i (unprepend z))) (S ∩ {z | z 0 = i})) :
    ContinuousOn (fun y => prepend (y 0) (k (y 0) (unprepend y))) S := by
  apply continuousOn_piecewise_clopen
  rotate_left
  rotate_left
  rotate_left
  · convert hk using 1
  · exact fun z hz => ⟨_, rfl⟩
  · aesop
  · exact fun z hz => ⟨z 0, rfl⟩
  · exact fun i => isClopen_preimage_zero i
  · aesop

/-- **Pointwise reduction of plain gluings.**  If block `i` of `F` continuously
reduces to block `i` of `G` for every `i`, then `gl F` reduces to `gl G`.

The reduction keeps the block index fixed: on the (relatively clopen) block
`{x | x.val 0 = i}`, the glued map is `prepend i ∘ (F i).func ∘ unprepend`, which
reduces blockwise to `(G i).func` via the given reductions, pasted together with
`continuous_pasting_on_clopen` / `continuousOn_piecewise_clopen`.
-/
theorem gl_reduces_of_pointwise (F G : ℕ → ScatFun)
    (hred : ∀ i, Reduces (F i) (G i)) :
    Reduces (gl F) (gl G) := by
  choose σ hσ τ hτ h_eq using hred;
  refine' ⟨ _, _, _ ⟩;
  exact fun x => ⟨ prepend ( x.val 0 ) ( σ ( x.val 0 ) ⟨ unprepend x.val, by
    have := GluingSet_inverse_short ( fun i => ( F i ).domain ) x;
    grind ⟩ ).val, by
    all_goals generalize_proofs at *;
    exact mem_gluingSet_prepend ( σ _ ⟨ _, ‹_› ⟩ ).2 ⟩
  all_goals generalize_proofs at *;
  · convert ScatFun.gluedSigma_continuous ( fun i => σ i ) hσ |> Classical.choose_spec |> And.left using 1;
    grind +suggestions;
  · refine' ⟨ fun y => prepend ( y 0 ) ( τ ( y 0 ) ( unprepend y ) ), _, _ ⟩;
    · refine' gluedTau_continuousOn _ _ _;
      intro i;
      refine' ContinuousOn.comp ( continuous_prepend i |> Continuous.continuousOn ) _ _;
      exact Set.range ( τ i );
      · refine' ContinuousOn.comp ( hτ i ) _ _;
        · exact Continuous.continuousOn ( continuous_unprepend );
        · intro z hz;
          obtain ⟨ x, rfl ⟩ := hz.1;
          have := x.2;
          obtain ⟨ j, hj ⟩ := this;
          unfold prepend at *; aesop;
      · exact fun x hx => Set.mem_range_self _;
    · intro x
      simp [gl, GluingFunVal_prepend];
      unfold GluingFunVal glBlock; aesop;

/-- **Reindexing a plain gluing by an injective map.**  For an injective
`e : ℕ → ℕ`, gluing the reindexed family `fun i => G (e i)` reduces to gluing
`G`: block `i` (first coordinate `i`) is relabelled to block `e i` (first
coordinate `e i`), keeping the payload; the inverse `τ` uses `Function.invFun e`,
which is a left inverse of `e` by injectivity. -/
theorem gl_reindex (G : ℕ → ScatFun) (e : ℕ → ℕ) (he : Function.Injective e) :
    Reduces (gl (fun i => G (e i))) (gl G) := by
  refine ⟨fun x => ⟨prepend (e (x.val 0)) (unprepend x.val), mem_gluingSet_prepend ?_⟩,
    ?_, fun y => prepend (Function.invFun e (y 0)) (unprepend y), ?_, ?_⟩
  · obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short (fun i => (G (e i)).domain) x
    rw [hi]; exact hmem
  · refine Continuous.subtype_mk ?_ _
    have hidx : Continuous (fun x : ↑(GluingSet (fun i => (G (e i)).domain)) => e (x.val 0)) :=
      continuous_of_discreteTopology.comp ((continuous_apply 0).comp continuous_subtype_val)
    refine continuous_pi fun i => ?_
    rcases i with _ | i
    · simpa [prepend] using hidx
    · simpa [prepend, unprepend] using (continuous_apply (i + 1)).comp continuous_subtype_val
  · refine Continuous.continuousOn ?_
    have hinv : Continuous (Function.invFun e) := continuous_of_discreteTopology
    have hidx : Continuous (fun y : Baire => Function.invFun e (y 0)) :=
      hinv.comp (continuous_apply 0)
    refine continuous_pi fun i => ?_
    rcases i with _ | i
    · simpa [prepend] using hidx
    · simpa [prepend, unprepend] using continuous_apply (i + 1)
  · intro x
    obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short (fun i => (G (e i)).domain) x
    have hmem' : unprepend x.val ∈ (G (e i)).domain := hmem
    have hxval : x.val = prepend i (unprepend x.val) := by rw [← hi, prepend_unprepend]
    have hlhs : GluingFunVal (fun i => (G (e i)).domain) (fun _ => Set.univ)
        (glBlock (fun i => G (e i))) x = prepend i ((G (e i)).func ⟨unprepend x.val, hmem'⟩) := by
      conv_lhs => rw [show x = ⟨prepend i (unprepend x.val), by rw [← hxval]; exact x.2⟩
        from Subtype.ext hxval]
      rw [GluingFunVal_prepend (fun i => (G (e i)).domain) (fun _ => Set.univ)
        (glBlock (fun i => G (e i))) i ⟨unprepend x.val, hmem'⟩]
      rfl
    have hsig : ∀ (h : prepend (e i) (unprepend x.val) ∈
        GluingSet (fun j => (G j).domain)),
        (gl G).func ⟨prepend (e i) (unprepend x.val), h⟩
          = prepend (e i) ((G (e i)).func ⟨unprepend x.val, hmem'⟩) := by
      intro h
      rw [show (⟨prepend (e i) (unprepend x.val), h⟩ : ↑(GluingSet (fun j => (G j).domain)))
        = ⟨prepend (e i) (⟨unprepend x.val, hmem'⟩ : ↑((G (e i)).domain)).val,
          mem_gluingSet_prepend hmem'⟩ from rfl]
      exact GluingFunVal_prepend (fun j => (G j).domain) (fun _ => Set.univ)
        (glBlock G) (e i) ⟨unprepend x.val, hmem'⟩ (mem_gluingSet_prepend hmem')
    show GluingFunVal _ _ (glBlock (fun i => G (e i))) x
      = prepend (Function.invFun e (((gl G).func _) 0)) (unprepend ((gl G).func _))
    simp only [hi]
    rw [hlhs, hsig, show (prepend (e i) ((G (e i)).func ⟨unprepend x.val, hmem'⟩)) 0 = e i from
      by simp [prepend], Function.leftInverse_invFun he i, unprepend_prepend]

/-- **General block-embedding criterion for plain gluings.**

If there is an injective reindexing `e : ℕ → ℕ` such that block `i` of `F`
continuously reduces to block `e i` of `G`, then the plain gluing `gl F`
continuously reduces to `gl G`.

This is the single reusable geometric input behind `Gl_mono`. -/
theorem gl_reduces_of_blockEmbed (F G : ℕ → ScatFun) (e : ℕ → ℕ)
    (he : Function.Injective e) (hred : ∀ i, Reduces (F i) (G (e i))) :
    Reduces (gl F) (gl G) :=
  (gl_reduces_of_pointwise F (fun i => G (e i)) hred).trans (gl_reindex G e he)

/-
**Joint continuity of the inverse block map** `(d, y) ↦ (invFun e d)⌢(stripZerosOne d y)`.
Again the depth `d` lives in discrete `ℕ`.
-/
lemma continuous_invFunPrependStrip_uncurry (e : ℕ → ℕ) :
    Continuous (fun p : ℕ × Baire =>
      prepend (Function.invFun e p.1) (stripZerosOne p.1 p.2)) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro p;
  refine' ContinuousAt.congr _ _;
  exact fun q => prepend ( invFun e p.1 ) ( stripZerosOne p.1 q.2 );
  · refine' Continuous.continuousAt _;
    exact continuous_prepend ( invFun e p.1 ) |> Continuous.comp <| continuous_stripZerosOne ( p.1 ) |> Continuous.comp <| continuous_snd;
  · filter_upwards [ IsOpen.mem_nhds ( isOpen_discrete { p.1 } |> IsOpen.preimage continuous_fst ) ( Set.mem_singleton p.1 ) ] with q hq using by aesop;

/-
**A plain gluing reduces, deeply, into a pointed gluing.**

Assume an injective reindexing `e` such that each block `C k` is *equal* to block
`D (e k)` or has empty domain.  Then `gl C` reduces to `pgl D`, sending the block-`k`
point `(k)⌢w` of `gl C` to the pointed-gluing block point `(0)^{e k}(1)·w`.  Because
the block maps are identities, the reduction is `σ x = (0)^{e (x.val 0)}(1)·(unprepend x)`
and `τ y = (invFun e (firstNonzero y))⌢(stripZerosOne (firstNonzero y) y)`.
We expose the canonical `σ` together with two pieces of geometric control used by the
`pgl`-lower-bound machinery: every value `σ x` starts with `e (x.val 0)` zeros
(`deep`), and its `pgl D`-image carries a `1` at coordinate `e (x.val 0)` (so the image
stays away from the base point `0^ω`).
-/
lemma gl_reduces_pgl_direct (C D : ℕ → ScatFun) (e : ℕ → ℕ) (he : Function.Injective e)
    (hCD : ∀ k, C k = D (e k) ∨ IsEmpty ↑(C k).domain) :
    ∃ (σ : ↑(gl C).domain → ↑(pgl D).domain) (τ : Baire → Baire),
      Continuous σ ∧
      (∀ x, (gl C).func x = τ ((pgl D).func (σ x))) ∧
      ContinuousOn τ (Set.range (fun x => (pgl D).func (σ x))) ∧
      (∀ x (l : ℕ), l < e (x.val 0) → (σ x).val l = 0) ∧
      (∀ x, ((pgl D).func (σ x)) (e (x.val 0)) = 1) := by
  refine' ⟨ _, _, _, _, _, _, _ ⟩;
  use fun x => ⟨ prependZerosOne ( e ( x.val 0 ) ) ( unprepend x.val ), by
    obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
    cases hCD k <;> simp_all +decide [ prependZerosOne_mem_pointedGluingSet ] ⟩
  all_goals generalize_proofs at *;
  use fun y => prepend ( Function.invFun e ( firstNonzero y ) ) ( stripZerosOne ( firstNonzero y ) y );
  · refine' Continuous.subtype_mk _ _;
    convert continuous_prependZerosOne_uncurry.comp ( Continuous.prodMk ( continuous_of_discreteTopology.comp ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ) ( continuous_unprepend.comp continuous_subtype_val ) ) using 1;
  · intro x
    generalize_proofs at *;
    have h_eq : (gl C).func x = prepend (x.val 0) ((C (x.val 0)).func ⟨unprepend x.val, by
      have := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
      grind⟩) := by
      rfl
    generalize_proofs at *;
    have h_eq : (pgl D).func ⟨prependZerosOne (e (x.val 0)) (unprepend x.val), by
      assumption⟩ = prependZerosOne (e (x.val 0)) ((D (e (x.val 0))).func ⟨unprepend x.val, by
      cases hCD ( x.val 0 ) <;> simp_all +decide [ ScatFun.gl ]; all_goals grind⟩) := by
      all_goals generalize_proofs at *;
      convert ScatFun.pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by assumption ⟩ using 1
    generalize_proofs at *;
    cases hCD ( x.val 0 ) <;> simp_all +decide;
    · rw [ firstNonzero_prependZerosOne ];
      rw [ Function.leftInverse_invFun he ];
      rw [ stripZerosOne_prependZerosOne ];
      grind;
    · grind;
  · refine' ContinuousOn.mono _ _;
    exact { y : Baire | y ≠ zeroStream };
    · convert continuous_invFunPrependStrip_uncurry e |> Continuous.comp_continuousOn <| ContinuousOn.prodMk ( firstNonzero_continuousOn _ ) continuousOn_id using 1;
      exact fun y hy => hy;
    · intro y hy
      obtain ⟨x, hx⟩ := hy
      subst hx;
      simp only [Set.mem_setOf_eq];
      have := pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by
        obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
        cases hCD k <;> aesop ⟩
      generalize_proofs at *;
      intro h; have := congr_fun h ( e ( x.val 0 ) ) ; simp_all +decide [ prependZerosOne_at_i ] ;
      replace this := congr_fun this ( e ( x.val 0 ) ) ; simp_all +decide [ zeroStream, prependZerosOne ] ;
  · unfold prependZerosOne; aesop;
  · intro x;
    convert pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, _ ⟩ using 1;
    all_goals generalize_proofs at *;
    · constructor <;> intro h <;> simp_all +decide [ funext_iff, prependZerosOne ];
      convert pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by assumption ⟩ using 1;
      exact ⟨ fun h => funext fun n => by simpa using h n, fun h => fun n => by simpa using congr_fun h n ⟩;
    · obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
      cases hCD k <;> aesop

/-! ## The bundled generators `ℓ_α` (`maxFun`) and `k_{α+1}` (`minFun`) -/

/-- The bundled **maximum function** `ℓ_α`.  `MaxFun α` is the subtype coercion on
`MaxDom α`, hence continuous for free; scatteredness comes from
`maxfun_is_scatter_leq_α`.  By that lemma all CB-levels strictly above `α` are
empty, so `CBRank (maxFun α).func ≤ α` (see `maxFun_cbRank_le`). -/
def maxFun (α : Ordinal.{0}) (hα : α < omega1) : ScatFun where
  domain := MaxDom α
  func := MaxFun α
  hScat := (maxfun_is_scatter_leq_α α hα).1
  hCont := continuous_subtype_val

@[simp] lemma maxFun_func (α : Ordinal.{0}) (hα : α < omega1) :
    (maxFun α hα).func = MaxFun α := rfl

/-- All CB-levels strictly above `α` are empty for `ℓ_α`. -/
lemma maxFun_cbLevel_empty (α : Ordinal.{0}) (hα : α < omega1)
    {β : Ordinal.{0}} (hβ : α < β) : CBLevel (maxFun α hα).func β = ∅ :=
  (maxfun_is_scatter_leq_α α hα).2 β hβ

/-- `ℓ_α` has CB-rank at most `α + 1` (its level above `α` is already empty). -/
lemma maxFun_cbRank_le (α : Ordinal.{0}) (hα : α < omega1) :
    CBRank (maxFun α hα).func ≤ Order.succ α :=
  CBRank_le_of_CBLevel_empty _ _ (maxFun_cbLevel_empty α hα (Order.lt_succ α))

/-- The bundled **minimum function** `k_{α+1}` (note the index shift: `minFun α`
is `k_{α+1}`, of CB-rank `α + 1`).  Continuity is free (`MinFun = Subtype.val`);
scatteredness comes from `minfun_is_scatter_leq_succ_α`. -/
def minFun (α : Ordinal.{0}) (hα : α < omega1) : ScatFun where
  domain := MinDom α
  func := MinFun α
  hScat := (minfun_is_scatter_leq_succ_α α hα).1
  hCont := continuous_subtype_val

@[simp] lemma minFun_func (α : Ordinal.{0}) (hα : α < omega1) :
    (minFun α hα).func = MinFun α := rfl

/-- All CB-levels strictly above `α + 1` are empty for `k_{α+1}`. -/
lemma minFun_cbLevel_empty (α : Ordinal.{0}) (hα : α < omega1)
    {β : Ordinal.{0}} (hβ : Order.succ α < β) : CBLevel (minFun α hα).func β = ∅ :=
  (minfun_is_scatter_leq_succ_α α hα).2 β hβ

/-- `k_{α+1}` has CB-rank at most `α + 2`. -/
lemma minFun_cbRank_le (α : Ordinal.{0}) (hα : α < omega1) :
    CBRank (minFun α hα).func ≤ Order.succ (Order.succ α) :=
  CBRank_le_of_CBLevel_empty _ _
    (minFun_cbLevel_empty α hα (Order.lt_succ (Order.succ α)))

end ScatFun

end
