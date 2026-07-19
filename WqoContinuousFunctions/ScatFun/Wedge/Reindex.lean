import WqoContinuousFunctions.ScatFun.Wedge.Monotone
import WqoContinuousFunctions.DoubleSuccessor.PseudoCentered
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.LamOne

/-!
# Reindexing the vertical columns of a `wedge` (`cor:wedgeSets`)

The memoir's `cor:wedgeSets` (`5_precise_struct_memo.tex:186`) states that, up to continuous
equivalence, a wedge `⋀(f_0,…,f_k ∣ g)` depends only on the *domination class* of its set of
vertical columns `{f_i}`: if `{f_i}` and `{h_j}` are equivalent for domination (each `f_i` is
`≤` some `h_j` and each `h_j` is `≤` some `f_i`), then
`⋀(f_0,…,f_k ∣ g) ≡ ⋀(h_0,…,h_l ∣ g)`.

In particular this makes `wedge` invariant (up to `Equiv`) under permuting, deduplicating, and
dropping empty (`≤` everything) vertical columns — exactly the invariance used to recognise a
concrete wedge as a `genStep` generator.
-/

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

/-! ## The pure column-reindexing lemma `wedge_reindex_reduces` and its supporting obligations

**Pure column-reindexing of a `wedge`** (the geometric core of `cor:wedgeSets`). Precomposing
the vertical-column family with *any* `φ : Fin n → Fin m` — which permutes, duplicates and drops
columns — never makes the wedge harder: `⋀(v' ∘ φ ∣ d) ≤ ⋀(v' ∣ d)` (same diagonal `d`).

This is the one genuinely geometric fact behind `cor:wedgeSets`; the domination direction reduces
to it (`wedge_domination_reduces`).

**Provided solution** (memoir `5_precise_struct_memo.tex:189-193`). Let `G = wedge (v' ∘ φ) d`, so
`G.domain = (gl (wedgeDomFamily (v'∘φ) d)).domain` and `G.func = retag n ∘ (gl …).func` (`wedge`,
`ScatFun/Wedge/Defs.lean`). Apply `ScatFun.wedge_upper_bound G v' d zeroStream A` with the following.

1. **Disjoint union `A`.** The slabs `glBlockSet (wedgeDomFamily (v'∘φ) d) k = {x | x 0 = k}` give
   `G.IsDisjointUnion` (via `gl_isDisjointUnion_blockSet`, `ScatFun/RestrictReduces.lean` — note
   `IsDisjointUnion` constrains only the *domain*, which `wedge` shares with `gl`, so it transfers).
   Regroup along `t : ℕ → ℕ`, `t k = φ ⟨k,·⟩` for `k < n` and `t (n+s) = m+s`, using
   `ScatFun.IsDisjointUnion.regroup` (`ScatFun/LevelsFinitelyGenerated/GlList.lean:624`): then
   `A j = ⋃_{k : φ k = j} slab k` (`j < m`, grouped verticals) and `A (m+s) = slab (n+s)` (diagonals).
2. **`h_diag`.** For `i = m+s`, `A i = slab (n+s)`; `wedgeDomFamily_diag` says slot `n+s` is `d`, so
   `Reduces (G.restrict (A i)) (glList (List.replicate 1 d))` (single copy) — the wedge-diagonal-slab
   analogue of `gl_restrict_blockSet_reduces` (`RestrictReduces.lean`), composed through `retag`
   (`wedge_func_diagonal`, `retag_diagonal`, `ScatFun/Wedge/Defs.lean`).
3. **`h_vertical` — the genuine ray computation.** For `i < m`, `A i = ⋃_{φ k = i} slab k`, and each
   slab `k` is `pgl (fun _ => v' i)` (`wedgeDomFamily_vertical`, since `φ k = i`). Need
   `∃ r, Reduces (G.rayOn zeroStream (A i) j) (glList (List.replicate r (v' i)))`. The ray over the
   grouped slabs is `gl_{k : φ k = i} (v' i) ≤ |φ⁻¹(i)| · (v' i)` — assembled from the single-slab
   ray (a `pgl`-ray, cf. `RayFun_pgl_zeroStream_reduces_block` / `pgl_rayOn_zeroStream_finImage`,
   `SimpleSuccessor/LamOne.lean`) via `gl_reduces_of_pointwise`. **No lemma computes the ray of a
   `wedge` over a union of vertical slabs yet**; this must be built from `retag ∘ gl` on the slab
   union interacting with `RaySet` — the sole remaining piece of infrastructure.
4. **`h_ranges`.** `SetsConvergeTo (fun i => Set.range (G.restrict (A i)).func) zeroStream`: every
   wedge slot shares the base point `prepend · zeroStream ↦ zeroStream` (`wedge_func_vertical_base`),
   so deep slabs converge to `zeroStream` — the same convergence bookkeeping as in
   `wedge_reduces_of_reduces`' `hconv`/`hbase_cont` obligations (`ScatFun/Wedge/Monotone.lean`).

The columns `v i` of the *source* dominate as `v i ≤ v' (φ i)` (used by `wedge_domination_reduces`);
here every source column is *equal* to a target column, so step 3's `r`-copies bound is exact. -/

/-- Regrouping index for `cor:wedgeSets`. A source vertical slot `k < n` is sent to the target
column `φ k < m`; a source diagonal slot `n + s` is sent to the target diagonal slot `m + s`.
This is the index map `t` fed to `IsDisjointUnion.regroup`. -/
def reindexColIdx {n m : ℕ} (φ : Fin n → Fin m) (k : ℕ) : ℕ :=
  if h : k < n then (φ ⟨k, h⟩).val else m + (k - n)

/-- The regrouped clopen partition of the *source* wedge's domain used to invoke
`wedge_upper_bound`. Grouping the first-coordinate slabs of `wedge (v' ∘ φ) d` by
`reindexColIdx φ`: slot `i < m` collects all vertical slabs `k` with `φ k = i`, and slot
`m + s` is the single diagonal slab `n + s`. -/
noncomputable def reindexPartition {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun)
    (φ : Fin n → Fin m) (i : ℕ) : Set ↑(wedge (fun k => v' (φ k)) d).domain :=
  ⋃ k ∈ {k | reindexColIdx φ k = i}, glBlockSet (wedgeDomFamily (fun k => v' (φ k)) d) k

/-
**Disjoint-union obligation.** The regrouped partition is a disjoint union of the source
wedge's domain. Follows from `gl_isDisjointUnion_blockSet` (the source wedge shares its domain
with `gl (wedgeDomFamily …)`) and `IsDisjointUnion.regroup` along `reindexColIdx φ`.
-/
lemma reindex_isDisjointUnion {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun) (φ : Fin n → Fin m) :
    (wedge (fun k => v' (φ k)) d).IsDisjointUnion (reindexPartition v' d φ) := by
  exact IsDisjointUnion.regroup _ _ ( gl_isDisjointUnion_blockSet _ ) _

/-
**Diagonal-block obligation.** For `i ≥ m` the regrouped block is the single diagonal slab
`n + (i - m)`, on which the source wedge acts by `retag ∘ gl`; it reduces to one copy of `d`.
-/
lemma reindex_diag_reduces {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun) (φ : Fin n → Fin m)
    (i : ℕ) (hi : m ≤ i) :
    ∃ mult, Reduces ((wedge (fun k => v' (φ k)) d).restrict (reindexPartition v' d φ i))
      (glList (List.replicate mult d)) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, i = m + s := by
    exact Nat.exists_eq_add_of_le hi;
  use 1; simp_all +decide [ reindexPartition ] ;
  rw [ show ( ⋃ k, ⋃ ( _ : reindexColIdx φ k = m + s ), glBlockSet ( wedgeDomFamily ( fun k => v' ( φ k ) ) d ) k ) = glBlockSet ( wedgeDomFamily ( fun k => v' ( φ k ) ) d ) ( n + s ) from ?_ ];
  · have h_reduces : Reduces ((gl (wedgeDomFamily (fun k => v' (φ k)) d)).restrict (glBlockSet (wedgeDomFamily (fun k => v' (φ k)) d) (n + s))) d := by
      convert gl_restrict_blockSet_reduces ( wedgeDomFamily ( fun k => v' ( φ k ) ) d ) ( n + s ) using 1;
      exact Eq.symm ( wedgeDomFamily_diag _ _ _ ( by linarith ) );
    have h_reduces : Reduces ((wedge (fun k => v' (φ k)) d).restrict (glBlockSet (wedgeDomFamily (fun k => v' (φ k)) d) (n + s))) d := by
      obtain ⟨ σ, hσ, τ, hτ, h_eq ⟩ := h_reduces;
      refine ⟨ σ, hσ, fun x => retag n ( τ x ), ?_, ?_ ⟩;
      · refine' ContinuousOn.comp ( retag_continuousOn_range _ _ ) hτ _;
        exact fun k => v' ( φ k );
        exact d;
        intro x hx; obtain ⟨ y, rfl ⟩ := hx; specialize h_eq y; simp_all +decide [ ScatFun.restrict ] ;
        grind;
      · intro x; convert congr_arg ( fun y => retag n y ) ( h_eq x ) using 1;
    convert h_reduces.trans _ using 1;
    exact ScatFun.glList_single_equiv d |>.1;
  · ext x; simp [reindexColIdx];
    grind

/-- **Single vertical slab, single ray.** For a source vertical slot `k < n` with `φ k = i`, the
`j`-th ray (base `0^ω`) of the source wedge restricted to that slab reduces to a *single* copy of
the target column `v' i`.

On the slab `{a | a 0 = k}` the wedge acts as `retag ∘ gl`, i.e. it sends
`(k)⌢(0)^l(1)⌢y ↦ (0)^l(1)(k)⌢((v' i).func y)` (`wedge_func_vertical_block`, since the slot family
is `pgl (fun _ => v' i)`) and the base `(k)⌢0^ω ↦ 0^ω`. An output lies in `RaySet univ 0^ω j`
(starts with exactly `j` zeros, then nonzero) **iff** `l = j`; so the ray-`j` restriction is exactly
`{(k)⌢(0)^j(1)⌢y : y ∈ (v' i).domain}`, on which the wedge value is `(0)^j(1)(k)⌢((v' i).func y)`.
This is a single copy of `v' i` reduced through the continuous tagging `τ w := (0)^j(1)(k)⌢w`:
take `σ a := y` (recovered by `stripZerosOne j` after `unprepend`), `τ := prependZerosOne j ∘ prepend k`. -/
lemma reindex_single_slab_ray_reduces {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun)
    (φ : Fin n → Fin m) (j : ℕ) (κ : Fin n) :
    Reduces ((wedge (fun k => v' (φ k)) d).restrict
        (glBlockSet (wedgeDomFamily (fun k => v' (φ k)) d) κ.val ∩
          {a | (wedge (fun k => v' (φ k)) d).func a ∈ RaySet Set.univ zeroStream j}))
      (v' (φ κ)) := by
  classical
  set W := wedge (fun k => v' (φ k)) d with hW
  set F := wedgeDomFamily (fun k => v' (φ k)) d with hF
  set col := v' (φ κ) with hcol
  set S : Set ↑W.domain :=
    glBlockSet F κ.val ∩ {a | W.func a ∈ RaySet Set.univ zeroStream j} with hS
  -- Characterisation of the wedge value on a ray-`j` point of the slab `κ`.
  have hchar : ∀ (a : Baire) (hgmem : a ∈ W.domain), a 0 = κ.val →
      W.func ⟨a, hgmem⟩ ∈ RaySet Set.univ zeroStream j →
      ∃ y : ↑col.domain, unprepend a = prependZerosOne j y.val ∧
        W.func ⟨a, hgmem⟩ = prependZerosOne j (prepend κ.val (col.func y)) := by
    intro a hgmem ha0 hray
    have haeq : a = prepend κ.val (unprepend a) := by
      conv_lhs => rw [← prepend_unprepend a]
      rw [ha0]
    have hFeq : F κ.val = pgl (fun _ => col) := by
      rw [hF]; exact wedgeDomFamily_vertical (fun k => v' (φ k)) d κ
    have hpmem : unprepend a ∈ (pgl (fun _ => col)).domain := by
      rw [← hFeq]; exact slab_unprepend_mem F κ.val ⟨⟨a, hgmem⟩, ha0⟩
    rw [pgl_domain] at hpmem
    rcases hpmem with hz | hU
    · -- base point: value is `0^ω`, not in ray `j`
      exfalso
      rw [Set.mem_singleton_iff] at hz
      have haeq0 : a = prepend κ.val zeroStream := by rw [haeq, hz]
      have hmem0 : prepend κ.val zeroStream ∈ W.domain := haeq0 ▸ hgmem
      have hval0 : W.func ⟨a, hgmem⟩ = zeroStream := by
        rw [show (⟨a, hgmem⟩ : ↑W.domain) = ⟨prepend κ.val zeroStream, hmem0⟩ from
          Subtype.ext haeq0]
        exact wedge_func_vertical_base (fun k => v' (φ k)) d κ hmem0
      rw [hval0] at hray
      exact hray.2.2 rfl
    · -- block `l`: value is `(0)^l(1)(κ)⌢…`, in ray `j` forces `l = j`
      obtain ⟨l, hlU⟩ := Set.mem_iUnion.mp hU
      obtain ⟨y0, hy0mem, hy0eq⟩ := hlU
      have haeq' : a = prepend κ.val (prependZerosOne l y0) := by rw [haeq, hy0eq]
      have hmem' : prepend κ.val (prependZerosOne l y0) ∈ W.domain := haeq' ▸ hgmem
      have hfunc : W.func ⟨a, hgmem⟩
          = prependZerosOne l (prepend κ.val (col.func ⟨y0, hy0mem⟩)) := by
        rw [show (⟨a, hgmem⟩ : ↑W.domain)
            = ⟨prepend κ.val (prependZerosOne l y0), hmem'⟩ from Subtype.ext haeq']
        exact wedge_func_vertical_block (fun k => v' (φ k)) d κ l ⟨y0, hy0mem⟩ hmem'
      rw [hfunc] at hray
      obtain ⟨-, hr1, hr2⟩ := hray
      have hlj : l = j := by
        rcases lt_trichotomy l j with h | h | h
        · exfalso
          have := hr1 l h
          rw [prependZerosOne_at_i] at this
          simp [zeroStream] at this
        · exact h
        · exfalso
          rw [prependZerosOne_head_eq_zero l _ j h] at hr2
          exact hr2 rfl
      refine ⟨⟨y0, hy0mem⟩, ?_, ?_⟩
      · rw [← hy0eq, hlj]
      · rw [hfunc, hlj]
  -- Package the characterisation over the restricted domain.
  have key : ∀ z : ↑(W.restrict S).domain, ∃ y : ↑col.domain,
      unprepend z.val = prependZerosOne j y.val ∧
      (W.restrict S).func z = prependZerosOne j (prepend κ.val (col.func y)) := by
    intro z
    obtain ⟨hgmem, hmemS⟩ := z.2
    have ha0 : z.val 0 = κ.val := hmemS.1
    have hray : W.func ⟨z.val, hgmem⟩ ∈ RaySet Set.univ zeroStream j := hmemS.2
    obtain ⟨y, hy1, hy2⟩ := hchar z.val hgmem ha0 hray
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  refine ⟨y, ?_, fun w => prependZerosOne j (prepend κ.val w), ?_, fun z => hy2 z⟩
  · rw [continuous_induced_rng]
    have hval : (Subtype.val ∘ y) = fun z => stripZerosOne j (unprepend z.val) := by
      funext z; rw [Function.comp_apply, hy1 z, stripZerosOne_prependZerosOne]
    rw [hval]
    exact (continuous_stripZerosOne j).comp (continuous_unprepend.comp continuous_subtype_val)
  · exact ((continuous_prependZerosOne j).comp (continuous_prepend κ.val)).continuousOn

/-- **Vertical-ray obligation (the geometric core).** For `i < m`, the regrouped block is the
union of the vertical slabs `k` with `φ k = i`, each a constant column `pgl (fun _ => v' i)`; the
`j`-th ray of the source wedge over this block reduces to finitely many copies of `v' i`. -/
lemma reindex_vertical_ray_reduces {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun)
    (φ : Fin n → Fin m) (i : ℕ) (hi : i < m) (j : ℕ) :
    ∃ mult, Reduces ((wedge (fun k => v' (φ k)) d).rayOn zeroStream
        (reindexPartition v' d φ i) j)
      (glList (List.replicate mult (v' ⟨i, hi⟩))) := by
  classical
  set W := wedge (fun k => v' (φ k)) d with hW
  set F := wedgeDomFamily (fun k => v' (φ k)) d with hF
  set pred : Set ↑W.domain := {a | W.func a ∈ RaySet Set.univ zeroStream j} with hpred
  set Q : Fin n → Set ↑W.domain :=
    fun k => if (φ k).val = i then glBlockSet F k.val ∩ pred else ∅ with hQ
  -- The ray over the regrouped vertical block is `W.restrict (⋃ k, Q k)`.
  have hunion : W.rayOn zeroStream (reindexPartition v' d φ i) j = W.restrict (⋃ k, Q k) := by
    show W.restrict (reindexPartition v' d φ i ∩ pred) = W.restrict (⋃ k, Q k)
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_iUnion, hQ]
    constructor
    · rintro ⟨haA, hap⟩
      obtain ⟨k', hk', hak'⟩ := Set.mem_iUnion₂.mp haA
      simp only [Set.mem_setOf_eq] at hk'
      have hk'n : k' < n := by
        by_contra h
        push_neg at h
        rw [reindexColIdx, dif_neg (by omega)] at hk'
        omega
      rw [reindexColIdx, dif_pos hk'n] at hk'
      exact ⟨⟨k', hk'n⟩, by rw [if_pos hk']; exact ⟨hak', hap⟩⟩
    · rintro ⟨k, hk⟩
      by_cases hcond : (φ k).val = i
      · rw [if_pos hcond] at hk
        obtain ⟨hslab, hp⟩ := hk
        refine ⟨Set.mem_iUnion₂.mpr ⟨k.val, ?_, hslab⟩, hp⟩
        simp only [Set.mem_setOf_eq]
        rw [reindexColIdx, dif_pos k.isLt]; exact hcond
      · rw [if_neg hcond] at hk; exact absurd hk (Set.notMem_empty _)
  rw [hunion]
  -- Assemble the finitely many single-slab rays into one `FinGl {v' i}` member.
  have hcl : ∀ k, IsClopen (Q k) := by
    intro k
    by_cases hcond : (φ k).val = i
    · simp only [hQ, hcond, if_true]
      exact (glBlockSet_clopen F k.val).inter ((isClopen_raySet zeroStream j).preimage W.hCont)
    · simp only [hQ, hcond, if_false]; exact isClopen_empty
  have hdisj : Pairwise (Disjoint on Q) := by
    intro k k' hkk'
    simp only [Function.onFun, hQ]
    by_cases hc : (φ k).val = i <;> by_cases hc' : (φ k').val = i
    · rw [if_pos hc, if_pos hc']
      have hne : k.val ≠ k'.val := fun h => hkk' (Fin.ext h)
      exact ((gl_isDisjointUnion_blockSet F).2.1 k.val k'.val hne).mono
        (Set.inter_subset_left) (Set.inter_subset_left)
    · rw [if_pos hc, if_neg hc']; exact Set.disjoint_empty _
    · rw [if_neg hc, if_pos hc']; exact (Set.disjoint_empty _).symm
    · rw [if_neg hc, if_neg hc']; exact Set.disjoint_empty _
  have hpiece : ∀ k, ∃ mm ∈ FinGl ({v' ⟨i, hi⟩} : Finset ScatFun).toFinFun,
      Reduces (W.restrict (Q k)) mm := by
    intro k
    by_cases hcond : (φ k).val = i
    · have hφk : φ k = ⟨i, hi⟩ := Fin.ext hcond
      refine ⟨v' (φ k), finGl_single_of_equiv ?_ (Equiv.refl _), ?_⟩
      · rw [hφk]; exact Finset.mem_singleton_self _
      simp only [hQ, hcond, if_true]
      exact reindex_single_slab_ray_reduces v' d φ j k
    · refine ⟨W.restrict (Q k), empty_mem_FinGl _ ?_, ContinuouslyReduces.refl _⟩
      simp only [hQ, hcond, if_false]
      refine ⟨fun a => ?_⟩
      obtain ⟨_, hmem⟩ := a.2
      exact absurd hmem (Set.notMem_empty _)
  obtain ⟨hh, hhmem, hhred⟩ := reduces_finGl_of_finite_union Q hcl hdisj {v' ⟨i, hi⟩} hpiece
  obtain ⟨L, hL, hEq⟩ := exists_glList_of_finGl hhmem
  have hLrep : L = List.replicate L.length (v' ⟨i, hi⟩) := by
    rw [List.eq_replicate_iff]
    exact ⟨rfl, fun w hw => Finset.mem_singleton.mp (hL w hw)⟩
  exact ⟨L.length, by rw [← hLrep]; exact hhred.trans hEq.1⟩

/-
**Convergence obligation.** The images of the regrouped blocks converge to `0^ω`: every
wedge slot shares the base point mapped to `0^ω`, so deep slabs converge to `zeroStream`.
-/
lemma reindex_ranges_converge {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun) (φ : Fin n → Fin m) :
    SetsConvergeTo
      (fun i => Set.range ((wedge (fun k => v' (φ k)) d).restrict (reindexPartition v' d φ i)).func)
      zeroStream := by
  intro U hUopen hU0
  obtain ⟨M, hM⟩ := baire_cylinder_mem_nhds zeroStream U hUopen hU0
  refine ⟨m + M, fun i hi => ?_⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨hgmem, hAi⟩ := z.2
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hAi
  simp only [Set.mem_setOf_eq] at hk
  have hz0 : z.val 0 = k := hzk
  have hkn : n ≤ k := by
    by_contra h
    push_neg at h
    rw [reindexColIdx, dif_pos h] at hk
    have := (φ ⟨k, h⟩).isLt
    omega
  have hik : m + (k - n) = i := by
    have h2 := hk
    rw [reindexColIdx, dif_neg (by omega)] at h2
    exact h2
  set s := k - n with hs
  have hpayd : unprepend z.val ∈ d.domain := by
    have h1 := slab_unprepend_mem (wedgeDomFamily (fun k => v' (φ k)) d) k ⟨⟨z.val, hgmem⟩, hz0⟩
    rwa [wedgeDomFamily_diag _ _ k (by omega)] at h1
  have hval : z.val = prepend (n + s) (unprepend z.val) := by
    conv_lhs => rw [← prepend_unprepend z.val]
    rw [hz0]; congr 1; omega
  have hgmem' : prepend (n + s) (unprepend z.val) ∈ (wedge (fun k => v' (φ k)) d).domain :=
    hval ▸ hgmem
  apply hM
  intro j hj
  simp only [Finset.mem_range] at hj
  show (wedge (fun k => v' (φ k)) d).func ⟨z.val, hgmem⟩ j = zeroStream j
  rw [show (⟨z.val, hgmem⟩ : ↑(wedge (fun k => v' (φ k)) d).domain)
      = ⟨prepend (n + s) (unprepend z.val), hgmem'⟩ from Subtype.ext hval,
    wedge_func_diagonal (fun k => v' (φ k)) d s ⟨unprepend z.val, hpayd⟩ hgmem',
    prependZerosOne_head_eq_zero s _ j (by omega)]
  rfl

lemma wedge_reindex_reduces {n m : ℕ} (v' : Fin m → ScatFun) (d : ScatFun) (φ : Fin n → Fin m) :
    Reduces (wedge (fun i => v' (φ i)) d) (wedge v' d) :=
  wedge_upper_bound (wedge (fun k => v' (φ k)) d) v' d zeroStream (reindexPartition v' d φ)
    (reindex_isDisjointUnion v' d φ)
    (fun i hi j => reindex_vertical_ray_reduces v' d φ i hi j)
    (fun i hi => reindex_diag_reduces v' d φ i hi)
    (reindex_ranges_converge v' d φ)

/-- **One direction of `cor:wedgeSets`.** If every source vertical column `v i` reduces to some
target vertical column `v' j` (i.e. `{v i}` is dominated by `{v' j}`), then `⋀(v ∣ d)` reduces to
`⋀(v' ∣ d)` (same diagonal `d`).

The domination content is fully discharged here from two existing pieces: the same-arity
monotonicity `wedge_reduces_of_reduces` handles `v i ≤ v' (φ i)` column-by-column (with `φ` chosen
from `h1`), and the pure reindexing `wedge_reindex_reduces` collapses the reindexed family
`v' ∘ φ` back onto `v'`. Thus the *only* remaining geometric obligation is `wedge_reindex_reduces`. -/
lemma wedge_domination_reduces {n m : ℕ} (v : Fin n → ScatFun) (v' : Fin m → ScatFun)
    (d : ScatFun) (h1 : ∀ i, ∃ j, Reduces (v i) (v' j)) :
    Reduces (wedge v d) (wedge v' d) := by
  classical
  -- Pick, for each source column `i`, a dominating target column `φ i`.
  choose φ hφ using h1
  -- Step 1 (same arity): `⋀(v ∣ d) ≤ ⋀(v' ∘ φ ∣ d)`, column-by-column via `hφ`.
  have hstep1 : Reduces (wedge v d) (wedge (fun i => v' (φ i)) d) :=
    wedge_reduces_of_reduces hφ (ContinuouslyReduces.refl d.func)
  -- Step 2 (reindexing): `⋀(v' ∘ φ ∣ d) ≤ ⋀(v' ∣ d)`.
  exact hstep1.trans (wedge_reindex_reduces v' d φ)

/-- **`cor:wedgeSets`.** If the source and target vertical-column families are mutually dominating,
the wedges (with the same diagonal) are continuously equivalent. -/
lemma wedge_domination_equiv {n m : ℕ} (v : Fin n → ScatFun) (v' : Fin m → ScatFun)
    (d : ScatFun) (h1 : ∀ i, ∃ j, Reduces (v i) (v' j))
    (h2 : ∀ j, ∃ i, Reduces (v' j) (v i)) :
    Equiv (wedge v d) (wedge v' d) :=
  ⟨wedge_domination_reduces v v' d h1, wedge_domination_reduces v' v d h2⟩

end ScatFun

end