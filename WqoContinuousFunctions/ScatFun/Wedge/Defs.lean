import WqoContinuousFunctions.ScatFun.Operations
import WqoContinuousFunctions.ScatFun.RestrictReduces
import WqoContinuousFunctions.ScatFun.Basics
import WqoContinuousFunctions.CenteredFunctions.Helpers
import WqoContinuousFunctions.CenteredFunctions.FinitenessHelpers
import Mathlib.Data.List.GetD

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# The wedge operation on `ScatFun`

This file bundles the memoir's **wedge operation** (`5_precise_struct_memo.tex`,
Definition 5.1 and the matrix reformulation in `rem:infinitewedge`) as a closed
operation on `ScatFun`.

## Inputs (memoir Definition 5.1 shape)

* `v : Fin n → ScatFun` — the **verticals**.  `v j` is a single scattered
  function; inside the wedge its column is the *constant* repetition
  `fun _ => v j`, pointed-glued (`pgl`) into `ʷ(v j)`.
* `d : ScatFun` — the **diagonal**.  The same `d` is placed on every diagonal
  slot.

This is exactly `⋁(v₀,…,v_{n-1} ∣ d)`.  Downstream the finite *sets* of the
memoir are absorbed into single functions by plain gluing: from data
`V : Fin n → List ScatFun` and `D : List ScatFun` one takes `v i := gl (V i)`
and `d := gl D`.

## The construction

The domain is the plain gluing `gl` of the family

* slot `j < n`     : `pgl (fun _ => v j)`   (the `j`-th vertical, ω-repeated and pointed-glued)
* slot `n + i`     : `d`                     (the diagonal, same block on every slot)

so `(wedge v d).domain = (gl (wedgeDomFamily v d)).domain`.  We **reuse** this
existing `gl`, which already discharges scatteredness and continuity of the
block-preserving map `(gl (wedgeDomFamily v d)).func`.

The wedge map is that block-preserving map **post-composed with a retagging**
`retag n`, which transposes the `gl_j ∘ pgl_i` tagging of the domain into the
`pgl_i ∘ gl_j` tagging of the codomain (and collapses the `n` vertical base
points `(j)⌢0^ω` to the single codomain base point `0^ω` — this is the
wedge-sum quotient `π` of `5_precise_struct_memo.tex:117-120`):

```
(j)⌢0^ω           ↦ 0^ω                       -- vertical base point  (j < n)
(j)⌢(0)^l(1)⌢z    ↦ (0)^l(1)(j)⌢z             -- vertical block l     (j < n)
(n+i)⌢z           ↦ (0)^i (1)(n)⌢z            -- diagonal slot i
```

where in the second/third line `z` is the value already produced by the inner
`pgl`/identity block map, i.e. `z = (v j).func y` resp. `z = d.func t`.

## Formal vs. informal proof

The informal definition writes the action by three explicit formulas on Baire
sequences.  Here we factor it as `retag n ∘ (gl …).func`:

* **`hScat`** is then *free*: `ScatteredFun` only constrains the fibres of the
  map (`f x = f x'`), and any post-composition `retag n ∘ f` is constant wherever
  `f` is constant.  So `(gl …).hScat` transports verbatim.
* **`hCont`** is the only genuine work: `retag n` is *not* globally continuous (it
  collapses base points), but the composite is, because in the `pgl` topology the
  blocks `(j)⌢(0)^l(1)⌢z` converge to the base point `(j)⌢0^ω` as `l → ∞`, and
  their images `(0)^l(1)(j)⌢z` converge to `0^ω` — exactly the limit demanded by
  continuity of the quotient.  It is discharged in `wedge_func_continuous` by splitting
  over the clopen first-coordinate slabs and reducing the vertical slabs to
  `pointedGluingFun_preserves_continuity` (see `retag_continuousOn_vertical_slab`).
-/

namespace ScatFun

variable {n : ℕ}

/-- The outer gluing family whose `gl` is the wedge's domain:
slot `j < n` is the pointed gluing `pgl (fun _ => v j)` of the constant `j`-th
vertical column (i.e. `ʷ(v j)`); slot `n + i` is the diagonal block `d` (the same
`d` on every slot, plain, not glued). -/
def wedgeDomFamily (v : Fin n → ScatFun) (d : ScatFun) : ℕ → ScatFun :=
  fun k => if h : k < n then pgl (fun _ => v ⟨k, h⟩) else d

/-- The **retagging** map `π`.  Applied to the output of the block-preserving map
`(gl (wedgeDomFamily v d)).func`, it transposes the domain tagging into the
codomain tagging and collapses the vertical base points to `0^ω`.

Acting on a sequence `w`:

* if `w 0 = j < n` (a vertical output `(j)⌢…`):
  - `(j)⌢0^ω        ↦ 0^ω`;
  - `(j)⌢(0)^l(1)⌢z ↦ (0)^l(1)(j)⌢z`  where `l = firstNonzero (unprepend w)`;
* if `w 0 = n + i` (a diagonal output `(n+i)⌢z`):
  - `(n+i)⌢z        ↦ (0)^i(1)(n)⌢z`. -/
def retag (n : ℕ) (w : ℕ → ℕ) : ℕ → ℕ :=
  if w 0 < n then
    if unprepend w = zeroStream then
      zeroStream
    else
      prependZerosOne (firstNonzero (unprepend w))
        (prepend (w 0) (stripZerosOne (firstNonzero (unprepend w)) (unprepend w)))
  else
    prependZerosOne (w 0 - n) (prepend n (unprepend w))

/-! ## Helper lemmas -/

/-- Transport a `func` value across an equality of `ScatFun`s.  Lets us replace the
abstract slot value `wedgeDomFamily v d k` (a `dite`) by its concrete branch (`pgl …`
or `d`) *inside* a `.func` application without a type-incorrect motive. -/
lemma scatFun_func_cast {F G : ScatFun} (h : F = G) (a : ↥F.domain) :
    F.func a = G.func ⟨a.val, h ▸ a.2⟩ := by subst h; rfl

/-- Slot `j < n` of the gluing family is the constant vertical column `pgl (fun _ => v j)`. -/
lemma wedgeDomFamily_vertical (v : Fin n → ScatFun) (d : ScatFun) (j : Fin n) :
    wedgeDomFamily v d j.val = pgl (fun _ => v j) := by
  simp only [wedgeDomFamily, dif_pos j.isLt, Fin.eta]

/-- Slot `k ≥ n` of the gluing family is the diagonal block `d`. -/
lemma wedgeDomFamily_diag (v : Fin n → ScatFun) (d : ScatFun) (k : ℕ) (hk : ¬ k < n) :
    wedgeDomFamily v d k = d := by
  simp only [wedgeDomFamily, dif_neg hk]

/-! ### `retag` on the three kinds of glued-map output (pure Baire, no subtypes) -/

/-- `retag` collapses a vertical base output `(j)⌢0^ω` (`j < n`) to `0^ω`. -/
lemma retag_vertical_base (n j : ℕ) (hj : j < n) :
    retag n (prepend j zeroStream) = zeroStream := by
  have h0 : (prepend j zeroStream) 0 = j := by simp [prepend]
  unfold retag
  rw [h0, if_pos hj, unprepend_prepend, if_pos rfl]

/-- `retag` transposes a vertical block output `(j)⌢(0)^l(1)⌢z` to `(0)^l(1)(j)⌢z`. -/
lemma retag_vertical_block (n j l : ℕ) (hj : j < n) (z : ℕ → ℕ) :
    retag n (prepend j (prependZerosOne l z)) = prependZerosOne l (prepend j z) := by
  have h0 : (prepend j (prependZerosOne l z)) 0 = j := by simp [prepend]
  have hne : prependZerosOne l z ≠ zeroStream := by
    intro h
    have := congrFun h l
    rw [prependZerosOne_at_i] at this
    simp [zeroStream] at this
  unfold retag
  rw [h0, if_pos hj, unprepend_prepend, if_neg hne, firstNonzero_prependZerosOne,
    stripZerosOne_prependZerosOne]

/-- `retag` transposes a diagonal output `(n+i)⌢z` to `(0)^i(1)(n)⌢z`. -/
lemma retag_diagonal (n i : ℕ) (z : ℕ → ℕ) :
    retag n (prepend (n + i) z) = prependZerosOne i (prepend n z) := by
  have h0 : (prepend (n + i) z) 0 = n + i := by simp [prepend]
  have hnlt : ¬ (n + i < n) := by omega
  unfold retag
  rw [h0, if_neg hnlt, unprepend_prepend, show n + i - n = i from by omega]

/-! ## Continuity of the wedge map (`hCont`) -/

/-- Values of the pointed-gluing map land in the pointed-gluing set (codomain `univ`). -/
lemma pgl_func_mem (F : ℕ → ScatFun) (u : ↥(pgl F).domain) :
    (pgl F).func u ∈ PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)) := by
  show PointedGluingFun (fun i => (F i).domain) (fun _ => Set.univ) (pglBlock F) u ∈ _
  unfold PointedGluingFun
  dsimp only
  split_ifs
  · exact zeroStream_mem_pointedGluingSet _
  · exact prependZerosOne_mem_pointedGluingSet _ _ _ (Set.mem_univ _)
  · exact zeroStream_mem_pointedGluingSet _

/-- The glued map on a general domain point, in tagged form. -/
lemma gl_func_apply (F : ℕ → ScatFun) (x : ↥(gl F).domain)
    (hmem : unprepend x.val ∈ (F (x.val 0)).domain) :
    (gl F).func x = prepend (x.val 0) ((F (x.val 0)).func ⟨unprepend x.val, hmem⟩) := by
  show GluingFunVal (fun i => (F i).domain) (fun _ => Set.univ) (glBlock F) x = _
  rfl

/-- **Vertical-slab continuity (the crux of `hCont`).**  On a vertical slab `{w | w 0 = k}`
(`k < n`) intersected with the range of the glued map, `retag` is the pointed-gluing
collapse `(0)^l(1)⌢z ↦ (0)^l(1)(k)⌢z`, `0^ω ↦ 0^ω`.  This is continuous — including at
the base point `0^ω`, where blocks `(0)^l(1)⌢z` converge as `l → ∞` and their images
`(0)^l(1)(k)⌢z` converge to `0^ω`.

The map is, after `unprepend`, the `PointedGluingFun` with block maps `z ↦ prepend k z`
(continuous), so it is continuous on `PointedGluingSet _` by
`pointedGluingFun_preserves_continuity`; we transfer that subtype continuity to
`ContinuousOn` via `continuousOn_iff_continuous_restrict`, using that every range element
on this slab has `unprepend` in `PointedGluingSet _` (the inner `pgl`'s codomain). -/
lemma retag_continuousOn_vertical_slab (v : Fin n → ScatFun) (d : ScatFun)
    (k : ℕ) (hk : k < n) :
    ContinuousOn (fun w : ℕ → ℕ =>
        if unprepend w = zeroStream then zeroStream
        else prependZerosOne (firstNonzero (unprepend w))
              (prepend k (stripZerosOne (firstNonzero (unprepend w)) (unprepend w))))
      (Set.range (gl (wedgeDomFamily v d)).func ∩ {w | w 0 = k}) := by
  -- the slab map is `Ψ ∘ unprepend`, where `Ψ` is the pointed-gluing collapse
  have hΨcont : ContinuousOn (fun u : ℕ → ℕ =>
      if u = zeroStream then zeroStream
      else prependZerosOne (firstNonzero u) (prepend k (stripZerosOne (firstNonzero u) u)))
      (PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire))) := by
    rw [continuousOn_iff_continuous_restrict]
    have hpg := pointedGluingFun_preserves_continuity (fun _ : ℕ => (Set.univ : Set Baire))
      (fun _ => Set.univ) (fun _ z => (⟨prepend k z.val, Set.mem_univ _⟩ : ↥(Set.univ : Set Baire)))
      (fun _ => ((continuous_prepend k).comp continuous_subtype_val).subtype_mk _)
    refine (continuous_subtype_val.comp hpg).congr (fun x => ?_)
    simp only [Function.comp_apply, Set.restrict_apply]
    unfold PointedGluingFun
    simp [Set.mem_univ]
  -- range slab elements have `unprepend` in the pointed-gluing set
  have hmaps : Set.MapsTo unprepend
      (Set.range (gl (wedgeDomFamily v d)).func ∩ {w | w 0 = k})
      (PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire))) := by
    rintro w ⟨⟨x, rfl⟩, hwk⟩
    simp only [Set.mem_setOf_eq] at hwk
    obtain ⟨i, hi0, himem⟩ :=
      GluingSet_inverse_short (fun j => (wedgeDomFamily v d j).domain) x
    have himem' : unprepend x.val ∈ (wedgeDomFamily v d (x.val 0)).domain := hi0.symm ▸ himem
    have hx0 : x.val 0 = k := by
      rw [gl_func_apply (wedgeDomFamily v d) x himem'] at hwk
      simpa [prepend] using hwk
    have heq : wedgeDomFamily v d (x.val 0) = pgl (fun _ => v ⟨k, hk⟩) := by
      rw [hx0]; exact wedgeDomFamily_vertical v d ⟨k, hk⟩
    rw [gl_func_apply (wedgeDomFamily v d) x himem', unprepend_prepend,
      scatFun_func_cast heq ⟨unprepend x.val, himem'⟩]
    exact pgl_func_mem (fun _ => v ⟨k, hk⟩) _
  exact hΨcont.comp continuous_unprepend.continuousOn hmaps

/-- The underlying glued-then-retagged map is continuous.  Reduces to
`ContinuousOn retag (range glued-map)`, split over the clopen first-coordinate slabs:
the diagonal slabs (`k ≥ n`) carry a globally continuous formula, and the vertical slabs
(`k < n`) are `retag_continuousOn_vertical_slab`. -/
lemma wedge_func_continuous (v : Fin n → ScatFun) (d : ScatFun) :
    Continuous (fun x : ↥(gl (wedgeDomFamily v d)).domain =>
      retag n ((gl (wedgeDomFamily v d)).func x)) := by
  have hcont : ContinuousOn (retag n) (Set.range (gl (wedgeDomFamily v d)).func) := by
    refine continuousOn_piecewise_clopen
      (S := Set.range (gl (wedgeDomFamily v d)).func)
      (fun k w => if k < n then
          (if unprepend w = zeroStream then zeroStream
           else prependZerosOne (firstNonzero (unprepend w))
                  (prepend k (stripZerosOne (firstNonzero (unprepend w)) (unprepend w))))
        else prependZerosOne (k - n) (prepend n (unprepend w)))
      (fun k => {w | w 0 = k})
      (fun z _ => ⟨z 0, rfl⟩)
      (fun k => isClopen_preimage_zero k)
      (fun z _ i hi j hj => ?_)
      ?_
      (fun z _ => ⟨z 0, rfl⟩)
      (retag n)
      ?_
    · -- agreement on overlaps: any two slab indices containing `z` both equal `z 0`
      simp only [Set.mem_setOf_eq] at hi hj
      subst hi; subst hj; rfl
    · -- per-slab continuity
      intro k
      by_cases hk : k < n
      · simp only [hk, if_true]
        exact retag_continuousOn_vertical_slab v d k hk
      · simp only [hk, if_false]
        exact ((continuous_prependZerosOne _).comp
          ((continuous_prepend _).comp continuous_unprepend)).continuousOn
    · -- `retag` agrees with the slab formula at index `z 0`
      intro z _ i hi
      simp only [Set.mem_setOf_eq] at hi
      subst hi; rfl
  exact hcont.comp_continuous (gl (wedgeDomFamily v d)).hCont (fun x => Set.mem_range_self x)

/-- **The wedge operation, bundled.**  `wedge v d` has domain the plain gluing of
the vertical-then-diagonal family `wedgeDomFamily v d`, and acts by the
block-preserving glued map followed by the transposing retag `retag n`. -/
def wedge (v : Fin n → ScatFun) (d : ScatFun) : ScatFun where
  domain := (gl (wedgeDomFamily v d)).domain
  func   := fun x => retag n ((gl (wedgeDomFamily v d)).func x)
  hScat  := by
    -- `ScatteredFun` is preserved under *any* post-composition: a relatively open
    -- set on which `(gl …).func` is constant is also one on which `retag n ∘ …`
    -- is constant.  So the gluing's own `hScat` transports directly.
    intro S hS
    obtain ⟨U, hUopen, hUne, hUconst⟩ := (gl (wedgeDomFamily v d)).hScat S hS
    refine ⟨U, hUopen, hUne, fun x hx x' hx' => ?_⟩
    show retag n ((gl (wedgeDomFamily v d)).func x)
        = retag n ((gl (wedgeDomFamily v d)).func x')
    rw [hUconst x hx x' hx']
  hCont  := wedge_func_continuous v d

@[simp] lemma wedge_domain (v : Fin n → ScatFun) (d : ScatFun) :
    (wedge v d).domain = (gl (wedgeDomFamily v d)).domain := rfl

/-! ## Characterization of `wedge.func` (the three memoir formulas) -/

/-- **Vertical base point.**  `(j)⌢0^ω ↦ 0^ω` for `j < n`. -/
lemma wedge_func_vertical_base (v : Fin n → ScatFun) (d : ScatFun) (j : Fin n)
    (hmem : prepend j.val zeroStream ∈ (wedge v d).domain) :
    (wedge v d).func ⟨prepend j.val zeroStream, hmem⟩ = zeroStream := by
  have hzmem : zeroStream ∈ (wedgeDomFamily v d j.val).domain := by
    rw [wedgeDomFamily_vertical]; exact zeroStream_mem_pointedGluingSet _
  show retag n ((gl (wedgeDomFamily v d)).func ⟨prepend j.val zeroStream, hmem⟩) = zeroStream
  rw [gl_func_prepend (wedgeDomFamily v d) j.val ⟨zeroStream, hzmem⟩ hmem,
    scatFun_func_cast (wedgeDomFamily_vertical v d j) ⟨zeroStream, hzmem⟩,
    pgl_func_zeroStream]
  exact retag_vertical_base n j.val j.isLt

/-- **Vertical block.**  `(j)⌢(0)^l(1)⌢x ↦ (0)^l(1)(j)⌢(v j).func x` for `j < n`. -/
lemma wedge_func_vertical_block (v : Fin n → ScatFun) (d : ScatFun) (j : Fin n)
    (l : ℕ) (y : ↥(v j).domain)
    (hmem : prepend j.val (prependZerosOne l y.val) ∈ (wedge v d).domain) :
    (wedge v d).func ⟨prepend j.val (prependZerosOne l y.val), hmem⟩
      = prependZerosOne l (prepend j.val ((v j).func y)) := by
  have hblkmem : prependZerosOne l y.val ∈ (wedgeDomFamily v d j.val).domain := by
    rw [wedgeDomFamily_vertical]
    exact prependZerosOne_mem_pointedGluingSet _ l y.val y.2
  show retag n ((gl (wedgeDomFamily v d)).func
      ⟨prepend j.val (prependZerosOne l y.val), hmem⟩) = _
  rw [gl_func_prepend (wedgeDomFamily v d) j.val ⟨prependZerosOne l y.val, hblkmem⟩ hmem,
    scatFun_func_cast (wedgeDomFamily_vertical v d j) ⟨prependZerosOne l y.val, hblkmem⟩,
    pgl_func_block (fun _ => v j) l y]
  exact retag_vertical_block n j.val l j.isLt ((v j).func y)

/-- **Diagonal slot.**  `(n+i)⌢x ↦ (0)^i(1)(n)⌢d.func x`. -/
lemma wedge_func_diagonal (v : Fin n → ScatFun) (d : ScatFun) (i : ℕ) (t : ↥d.domain)
    (hmem : prepend (n + i) t.val ∈ (wedge v d).domain) :
    (wedge v d).func ⟨prepend (n + i) t.val, hmem⟩
      = prependZerosOne i (prepend n (d.func t)) := by
  have htmem : t.val ∈ (wedgeDomFamily v d (n + i)).domain := by
    rw [wedgeDomFamily_diag _ _ _ (by omega)]; exact t.2
  show retag n ((gl (wedgeDomFamily v d)).func ⟨prepend (n + i) t.val, hmem⟩) = _
  rw [gl_func_prepend (wedgeDomFamily v d) (n + i) ⟨t.val, htmem⟩ hmem,
    scatFun_func_cast (wedgeDomFamily_diag v d (n + i) (by omega)) ⟨t.val, htmem⟩]
  exact retag_diagonal n i (d.func t)

/-! ## CB-rank invariance under injective post-composition

`isolatedLocus` (hence `CBLevel`, `CBRank`) only constrains *value-equality* `f y = f x`, so it
is unchanged by post-composing `f` with a map injective on `range f`.  This is the per-slab tool
for the wedge's CB-rank: `retag` is injective within each clopen slab even though it collapses
base points across slabs.  (Generalizes `cbLevel_comp_injective_left` from `Injective` to
`InjOn (range f)`.) -/
lemma cbLevel_comp_injOn {X : Type} {Y Z : Type*} [TopologicalSpace X]
    (h : Y → Z) (f : X → Y) (hh : Set.InjOn h (Set.range f)) (β : Ordinal.{0}) :
    CBLevel (fun x => h (f x)) β = CBLevel f β := by
  have hiso : ∀ A : Set X, isolatedLocus (fun x => h (f x)) A = isolatedLocus f A := by
    intro A; ext x
    simp only [isolatedLocus, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxA, U, hUo, hxU, hc⟩
      exact ⟨hxA, U, hUo, hxU,
        fun y hy => hh (Set.mem_range_self y) (Set.mem_range_self x) (hc y hy)⟩
    · rintro ⟨hxA, U, hUo, hxU, hc⟩
      exact ⟨hxA, U, hUo, hxU, fun y hy => congrArg h (hc y hy)⟩
  induction' β using Ordinal.limitRecOn with β ih β hβ ih
  · simp [CBLevel]
  · rw [CBLevel_succ', CBLevel_succ', ih, hiso]
  · rw [CBLevel_limit _ _ hβ, CBLevel_limit _ _ hβ]
    exact Set.iInter₂_congr (fun γ hγ => ih γ hγ)

/-- `CBRank` is unchanged by post-composing with a map injective on `range f`. -/
lemma cbRank_comp_injOn {X : Type} {Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y → Z) (f : X → Y) (hh : Set.InjOn h (Set.range f)) :
    CBRank (fun x => h (f x)) = CBRank f := by
  unfold CBRank
  congr 1
  ext β
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
    cbLevel_comp_injOn h f hh β, cbLevel_comp_injOn h f hh (Order.succ β)]

/-! ### Slab homeomorphism: the `k`-slab of `gl F` ≃ₜ block `F k`

The plain gluing `gl F` is partitioned by the first coordinate into the relatively clopen
slabs `S k = {x | x₀ = k}`.  Each slab is homeomorphic to the block domain `(F k).domain`
via `unprepend`/`prepend k`, and under that homeomorphism the glued map is
`prepend k ∘ (F k).func`.  This is the bridge that lets us compute the CB-rank slab by slab. -/

/-- A slab point's `unprepend` lands in the block domain `(F k).domain`. -/
lemma slab_unprepend_mem (F : ℕ → ScatFun) (k : ℕ)
    (x : {x : ↥(gl F).domain // x.val 0 = k}) :
    unprepend x.val.val ∈ (F k).domain := by
  obtain ⟨i, hi0, hmem⟩ := GluingSet_inverse_short (fun i => (F i).domain) x.val
  have hik : i = k := by rw [← hi0]; exact x.2
  exact hik ▸ hmem

/-- The `k`-slab `{x ∈ gl F | x₀ = k}` is homeomorphic to the block domain `(F k).domain`,
via `unprepend` (forward) and `prepend k` (backward). -/
def slabHomeo (F : ℕ → ScatFun) (k : ℕ) :
    {x : ↥(gl F).domain // x.val 0 = k} ≃ₜ ↥(F k).domain where
  toFun x := ⟨unprepend x.val.val, slab_unprepend_mem F k x⟩
  invFun a := ⟨⟨prepend k a.val, mem_gluingSet_prepend a.2⟩, by simp [prepend]⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    show prepend k (unprepend x.val.val) = x.val.val
    conv_rhs => rw [← prepend_unprepend x.val.val]
    rw [x.2]
  right_inv a := by
    apply Subtype.ext
    show unprepend (prepend k a.val) = a.val
    rw [unprepend_prepend]
  continuous_toFun :=
    (continuous_unprepend.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (((continuous_prepend k).comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-! ### CB-rank of a plain gluing `gl`

General fact (not specific to the wedge): the plain gluing `gl F` is partitioned by the first
coordinate into the slabs `S k`, each homeomorphic to the block `(F k).domain` via `slabHomeo`,
on which the glued map is `prepend k ∘ (F k).func` with `prepend k` injective. Summing CB-rank
over the clopen slab cover gives `CBRank (gl F).func = ⨆ k, CBRank (F k).func`. -/

/-- **CB-rank of a single slab of a plain gluing.** -/
lemma gl_cbRank_slab (F : ℕ → ScatFun) (k : ℕ) :
    CBRank (fun x : {x : ↥(gl F).domain // x.val 0 = k} => (gl F).func x.val)
      = CBRank (F k).func := by
  have hfactor : (fun x : {x : ↥(gl F).domain // x.val 0 = k} => (gl F).func x.val)
      = (fun a : ↥(F k).domain => prepend k ((F k).func a)) ∘ (slabHomeo F k) := by
    funext x
    have hmem := slab_unprepend_mem F k x
    have hxv : x.val = (⟨prepend k (unprepend x.val.val), mem_gluingSet_prepend hmem⟩
        : ↥(gl F).domain) := by
      apply Subtype.ext
      show x.val.val = prepend k (unprepend x.val.val)
      conv_lhs => rw [← prepend_unprepend x.val.val]
      rw [x.2]
    have hgl : (gl F).func x.val
        = prepend k ((F k).func ⟨unprepend x.val.val, hmem⟩) := by
      conv_lhs => rw [hxv]
      exact gl_func_prepend F k ⟨unprepend x.val.val, hmem⟩ (mem_gluingSet_prepend hmem)
    show (gl F).func x.val = prepend k ((F k).func (slabHomeo F k x))
    rw [hgl]; rfl
  rw [hfactor, CBRank_comp_homeomorph]
  have hinj : Function.Injective (fun w : ℕ → ℕ => prepend k w) := by
    intro a b h
    have := congrArg unprepend h
    rwa [unprepend_prepend, unprepend_prepend] at this
  exact cbRank_comp_injOn (fun w => prepend k w) (F k).func hinj.injOn

/-- **CB-rank of a plain gluing.** -/
lemma gl_cbRank_eq (F : ℕ → ScatFun) :
    CBRank (gl F).func = ⨆ k, CBRank (F k).func := by
  rw [cb_rank_of_clopen_union (gl F).func (gl F).hScat
      (fun k => {x : ↥(gl F).domain | x.val 0 = k})
      (fun x => ⟨x.val 0, rfl⟩)
      (fun k => (isClopen_preimage_zero k).isOpen.preimage continuous_subtype_val)]
  exact iSup_congr (fun k => gl_cbRank_slab F k)

/-! ### `retag ∘ prepend k` is injective on the relevant slab values

**The wedge as a disjoint union of injective maps.**  The domain `gl (wedgeDomFamily v d)` is
partitioned into the clopen first-coordinate slabs `S k = {x | x₀ = k}`, and on each slab the
wedge map is `retag n ∘ (gl F).func`, i.e. `(retag n ∘ prepend k) ∘ (F k).func` composed with
the slab homeomorphism.  The two lemmas below show that the residual relabelling
`retag n ∘ prepend k` is **injective on each slab's values** — vertical slabs (`k < n`) carry
pointed-gluing outputs (`PointedGluingSet`), diagonal slabs (`k ≥ n`) carry arbitrary values —
each witnessed by an explicit left inverse.  So *slab by slab* the wedge is an injective map;
this slab-local injectivity is all the CB-rank computation needs.

**But the global wedge map is injective iff `n ≤ 1`.**  `retag` collapses every vertical base
point `(j)⌢0^ω` (`j < n`) to the single codomain base point `0^ω` (the wedge-sum quotient `π`).
For `n > 1` the distinct domain points `(0)⌢0^ω` and `(1)⌢0^ω` are thus identified, so the map
fails to be injective.  For `n ≤ 1` there is at most one vertical base point, no two slabs share
an image (vertical block images `(0)^l(1)(j)⌢z`, diagonal images `(0)^i(1)(n)⌢z`, and `0^ω` are
pairwise distinguished by their first nonzero coordinate), and the map is injective.  This is
exactly why CB-rank invariance must be argued per slab (`cbRank_comp_injOn` with `InjOn`) rather
than through a single global injectivity (`cbRank_comp_injective`). -/

/-- On a vertical slab (`k < n`), `u ↦ retag n (prepend k u)` is injective on pointed-gluing
outputs.  Left inverse: `0^ω ↦ 0^ω`, and `(0)^l(1)w ↦ (0)^l(1)(unprepend w)`. -/
lemma retag_prepend_injOn_vertical (k : ℕ) (hk : k < n) :
    Set.InjOn (fun u => retag n (prepend k u))
      (PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire))) := by
  have key : ∀ u ∈ PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)),
      (if retag n (prepend k u) = zeroStream then zeroStream
       else prependZerosOne (firstNonzero (retag n (prepend k u)))
         (unprepend (stripZerosOne (firstNonzero (retag n (prepend k u)))
            (retag n (prepend k u))))) = u := by
    intro u hu
    rcases hu with h0 | hblk
    · rw [Set.mem_singleton_iff] at h0
      subst h0
      rw [retag_vertical_base n k hk]; simp
    · rw [Set.mem_iUnion] at hblk
      obtain ⟨i, z, -, rfl⟩ := hblk
      rw [retag_vertical_block n k i hk z]
      have hne : prependZerosOne i (prepend k z) ≠ zeroStream := by
        intro h; have := congrFun h i
        rw [prependZerosOne_at_i] at this; simp [zeroStream] at this
      rw [if_neg hne, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne,
        unprepend_prepend]
  intro u1 hu1 u2 hu2 hsame
  replace hsame : retag n (prepend k u1) = retag n (prepend k u2) := hsame
  rw [← key u1 hu1, hsame, key u2 hu2]

/-- On a diagonal slab (`k ≥ n`), `z ↦ retag n (prepend k z)` is injective (everywhere):
`retag n (prepend k z) = (0)^{k-n}(1)(n)⌢z`, from which `z` is recovered by stripping. -/
lemma retag_prepend_injOn_diagonal (k : ℕ) (hk : ¬ k < n) :
    Set.InjOn (fun z => retag n (prepend k z)) (Set.univ : Set Baire) := by
  have hretag : ∀ z, retag n (prepend k z) = prependZerosOne (k - n) (prepend n z) := by
    intro z; unfold retag
    rw [show (prepend k z) 0 = k from by simp [prepend], if_neg hk, unprepend_prepend]
  intro z1 _ z2 _ hsame
  replace hsame : retag n (prepend k z1) = retag n (prepend k z2) := hsame
  rw [hretag z1, hretag z2] at hsame
  have h1 := prependZerosOne_injective (k - n) hsame
  have h2 := congrArg unprepend h1
  rwa [unprepend_prepend, unprepend_prepend] at h2

/-! ### CB-rank of `pgl` of a constant column -/

/-- The pointed gluing of a *constant* column `(fun _ => w)` has CB-rank `succ (CB w)`:
it is the regular-sequence rank (`cbRank_pgl_regular`) with a constant supremum. -/
lemma cbRank_pgl_const (w : ScatFun) :
    CBRank (pgl (fun _ : ℕ => w)).func = Order.succ (CBRank w.func) := by
  rw [cbRank_pgl_regular _ (scatFun_const_isRegularSeq w), ciSup_const]

/-! ### CB-rank of a single slab of the wedge

On slab `k`, the wedge map is `retag n ∘ (gl F).func`, which factors as
`(retag n ∘ prepend k) ∘ (F k).func ∘ (slab homeomorphism)`.  Precomposition with the
homeomorphism (`CBRank_comp_homeomorph`) and post-composition with the slab-injective
`retag n ∘ prepend k` (`cbRank_comp_injOn`) both preserve CB-rank, so the slab has rank
`CB (F k)`. -/
lemma cbRank_wedge_slab (v : Fin n → ScatFun) (d : ScatFun) (k : ℕ) :
    CBRank (fun x : {x : ↥(gl (wedgeDomFamily v d)).domain // x.val 0 = k} =>
        retag n ((gl (wedgeDomFamily v d)).func x.val))
      = CBRank (wedgeDomFamily v d k).func := by
  -- factor the slab map through the slab homeomorphism
  have hfactor : (fun x : {x : ↥(gl (wedgeDomFamily v d)).domain // x.val 0 = k} =>
        retag n ((gl (wedgeDomFamily v d)).func x.val))
      = (fun a : ↥(wedgeDomFamily v d k).domain =>
          retag n (prepend k ((wedgeDomFamily v d k).func a)))
        ∘ (slabHomeo (wedgeDomFamily v d) k) := by
    funext x
    show retag n ((gl (wedgeDomFamily v d)).func x.val)
       = retag n (prepend k ((wedgeDomFamily v d k).func (slabHomeo (wedgeDomFamily v d) k x)))
    have hmem := slab_unprepend_mem (wedgeDomFamily v d) k x
    have hxv : x.val = (⟨prepend k (unprepend x.val.val), mem_gluingSet_prepend hmem⟩
        : ↥(gl (wedgeDomFamily v d)).domain) := by
      apply Subtype.ext
      show x.val.val = prepend k (unprepend x.val.val)
      conv_lhs => rw [← prepend_unprepend x.val.val]
      rw [x.2]
    have hgl : (gl (wedgeDomFamily v d)).func x.val
        = prepend k ((wedgeDomFamily v d k).func ⟨unprepend x.val.val, hmem⟩) := by
      conv_lhs => rw [hxv]
      exact gl_func_prepend (wedgeDomFamily v d) k ⟨unprepend x.val.val, hmem⟩
        (mem_gluingSet_prepend hmem)
    rw [hgl]; rfl
  rw [hfactor, CBRank_comp_homeomorph]
  -- the residual post-composition `retag n ∘ prepend k` is injective on the slab values
  have hinj : Set.InjOn (fun w => retag n (prepend k w))
      (Set.range (wedgeDomFamily v d k).func) := by
    by_cases hk : k < n
    · have hsub : Set.range (wedgeDomFamily v d k).func ⊆
          PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)) := by
        rintro w ⟨a, rfl⟩
        have heq : wedgeDomFamily v d k = pgl (fun _ => v ⟨k, hk⟩) := by
          simp only [wedgeDomFamily, dif_pos hk]
        rw [scatFun_func_cast heq a]
        exact pgl_func_mem _ _
      exact (retag_prepend_injOn_vertical k hk).mono hsub
    · exact (retag_prepend_injOn_diagonal k hk).mono (Set.subset_univ _)
  exact cbRank_comp_injOn (fun w => retag n (prepend k w)) (wedgeDomFamily v d k).func hinj

/-! ### Splitting the slab supremum into verticals and diagonal -/

/-- The supremum of the block CB-ranks of `wedgeDomFamily v d` splits as the max of the
successor vertical ranks (slots `< n`, each a constant `pgl`) and the diagonal rank `CB d`
(slots `≥ n`, all equal to `d`). -/
lemma iSup_wedgeDomFamily_cbRank (v : Fin n → ScatFun) (d : ScatFun) :
    ⨆ k, CBRank (wedgeDomFamily v d k).func
      = max (⨆ i : Fin n, Order.succ (CBRank (v i).func)) (CBRank d.func) := by
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro k
    by_cases hk : k < n
    · have hval : CBRank (wedgeDomFamily v d k).func = Order.succ (CBRank (v ⟨k, hk⟩).func) := by
        rw [show wedgeDomFamily v d k = pgl (fun _ => v ⟨k, hk⟩) from by
          simp only [wedgeDomFamily, dif_pos hk]]
        exact cbRank_pgl_const _
      rw [hval]
      exact le_trans (Ordinal.le_iSup (fun i : Fin n => Order.succ (CBRank (v i).func)) ⟨k, hk⟩)
        (le_max_left _ _)
    · rw [wedgeDomFamily_diag v d k hk]
      exact le_max_right _ _
  · apply max_le
    · apply Ordinal.iSup_le
      intro i
      have hval : CBRank (wedgeDomFamily v d i.val).func = Order.succ (CBRank (v i).func) := by
        rw [show wedgeDomFamily v d i.val = pgl (fun _ => v i) from
          wedgeDomFamily_vertical v d i]
        exact cbRank_pgl_const _
      rw [← hval]
      exact Ordinal.le_iSup (fun k => CBRank (wedgeDomFamily v d k).func) i.val
    · rw [← show CBRank (wedgeDomFamily v d n).func = CBRank d.func from by
        rw [wedgeDomFamily_diag v d n (lt_irrefl n)]]
      exact Ordinal.le_iSup (fun k => CBRank (wedgeDomFamily v d k).func) n

/-! ## Cantor–Bendixson rank of the wedge (`BasicfactsWedge` item 3)

Memoir Fact `BasicfactsWedge`(3): for verticals `(f_i)_{i ≤ k}` and diagonal `f_{k+1} = g`,
$$\mathrm{CB}(f) = \max\big(\{\mathrm{CB}(f_i)+1 : i \le k\} \cup \{\mathrm{CB}(g)\}\big).$$

In our `ScatFun` rendering the verticals are `v : Fin n → ScatFun` (`n = k+1`) and the diagonal
is `d`.  The `+1` on each vertical (`Order.succ`, which is `· + 1` on ordinals) is exactly the
successor introduced by the internal pointed gluing `pgl (fun _ => v i)`; the diagonal slots
host `d` directly (no `+1`); and the whole domain is the plain gluing of all slots, whose rank
is the supremum.  Hence the maximum. -/
theorem wedge_CBRank (v : Fin n → ScatFun) (d : ScatFun) :
    CBRank (wedge v d).func
      = max (⨆ i : Fin n, Order.succ (CBRank (v i).func)) (CBRank d.func) := by
  -- PROOF STRATEGY (clopen-union framing, per `cb_rank_of_clopen_union`):
  -- (1) Cover `dom (wedge v d) = dom (gl F)` by the clopen first-coordinate slabs
  --     `S k = {x | x₀ = k}`.  Then `CB(wedge v d) = ⨆ k, CB((wedge v d)|_{S k})`.
  -- (2) On slab `k`, `(wedge v d).func = retag n ∘ (gl F).func` and the slab is homeomorphic
  --     to the block `F k`, on which `retag n ∘ prepend k` is injective: so the slab has
  --     CB-rank `CB(F k)` (`cbRank_wedge_slab`).
  -- (3) Split the slab supremum into the `n` verticals (each a constant `pgl`, rank
  --     `succ (CB v i)`) and the diagonal tail (all `d`, rank `CB d`) — `iSup_wedgeDomFamily_cbRank`.
  rw [← iSup_wedgeDomFamily_cbRank v d,
    cb_rank_of_clopen_union (wedge v d).func (wedge v d).hScat
      (fun k => {x : ↥(wedge v d).domain | x.val 0 = k})
      (fun x => ⟨x.val 0, rfl⟩)
      (fun k => (isClopen_preimage_zero k).isOpen.preimage continuous_subtype_val)]
  exact iSup_congr (fun k => cbRank_wedge_slab v d k)

/-! ## List wrapper: wedge of finite sets of functions

Downstream the verticals and diagonal are given by **finite lists** `V i, D : List ScatFun`,
each collapsed into a single `ScatFun` by plain gluing.  The raw `wedge` then repeats each
vertical (`pgl (fun _ => v i)`) and the diagonal, so the lists supply the *contents* and the
operation supplies the *repetition*. -/

/-- Plain gluing of a finite list of scattered functions, as a single `ScatFun`.
The `ℕ`-indexed family feeding `gl` is the list padded with `empty` (the `getD … empty`
idiom of `copiesSeq` in `FiniteGluing`). -/
def glList (l : List ScatFun) : ScatFun :=
  gl (fun k => l.getD k empty)

@[simp] lemma glList_domain (l : List ScatFun) :
    (glList l).domain = (gl (fun k => l.getD k empty)).domain := rfl

/-- **Wedge of finite sets of functions.**  From verticals `V i` (finite lists) and a diagonal
list `D`, take `v i := glList (V i)`, `d := glList D` and apply the raw `wedge`.  This is the
memoir's wedge with each vertical/diagonal a finite gluing of generators. -/
def wedgeList (V : Fin n → List ScatFun) (D : List ScatFun) : ScatFun :=
  wedge (fun i => glList (V i)) (glList D)

/-- `wedgeList` unfolded to the raw `wedge` (for applying the `wedge_func_*` API). -/
lemma wedgeList_eq (V : Fin n → List ScatFun) (D : List ScatFun) :
    wedgeList V D = wedge (fun i => glList (V i)) (glList D) := rfl

@[simp] lemma wedgeList_domain (V : Fin n → List ScatFun) (D : List ScatFun) :
    (wedgeList V D).domain
      = (gl (wedgeDomFamily (fun i => glList (V i)) (glList D))).domain := rfl


end ScatFun
