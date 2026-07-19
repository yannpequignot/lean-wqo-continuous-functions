import WqoContinuousFunctions.ScatFun.IntertwineReductions
import WqoContinuousFunctions.ScatFun.Basics
import WqoContinuousFunctions.CenteredFunctions.Theorems

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# Intertwining reductions for `ω` of centered functions

Memoir Lemma `Intertwinereductionsforomegacentered` (`5_precise_struct_memo.tex`), **first part**.

> Let `f ∈ ℕ^ℕ` be continuous and `G ⊆ ℕ^ℕ` a finite set of *centered* functions.
> If `ω g ≤ f` for all `g ∈ G`, then `ω G ≤ f`.

Here everything is rendered at the `ScatFun` level (cf. `ScatFun/IntertwineReductions.lean`): the
finite set `G` is a family `G : Fin n → ScatFun`, each `G k` is centered (`IsCentered (G k).func`),
`ω (G k)` is `ScatFun.omega (G k)`, and `ω G = ω (gl G)` is `ScatFun.omega (ScatFun.glFin G)`.
(`f` is already continuous since every `ScatFun` bundles continuity.)

## Informal proof (memoir)

This is a corollary of the general intertwining lemma `intertwine_reductions`
(`ScatFun/IntertwineReductions.lean`): it suffices to show that for each block `G k` the set
`IntertwineSet f (G k) = {y | ∀ V ∈ 𝓝 y, G k ≤ f ↾ V}` is infinite.

Fix `g = G k` with a center `c` and a continuous reduction `(σ, τ) : ω g ≤ f`.  Composing the
block-`n` embedding `g ≤ ω g` (`z ↦ (n)⌢z`) with `(σ, τ)` gives, for every `n`, a reduction
`g ≤ f` whose `σ`-component sends `c` to `σ((n)⌢c)`.  By `centerInvariance_reduce` (Fact 4.2),
`g ≤ f ↾ V` for every neighbourhood `V` of `σ((n)⌢c)`; by continuity of `f` this gives
`g ≤ f ↾ U` (corestriction) for every neighbourhood `U` of `y_n := f(σ((n)⌢c))`, i.e.
`y_n ∈ IntertwineSet f g`.  Finally the points `y_n` are pairwise distinct: applying `τ`,
`τ(y_n) = (ω g)((n)⌢c) = (n)⌢(g c)` is injective in `n` (the glued output records the block
index), so `n ↦ y_n` is injective and `IntertwineSet f g ⊇ {y_n}` is infinite.
-/

namespace ScatFun

/-
**The key ingredient.**  If `g` is centered and `ω g ≤ f`, then the intertwine set
`IntertwineSet f g = {y | ∀ V ∈ 𝓝 y, g ≤ f ↾ V}` is infinite.
-/
lemma intertwineSet_infinite_of_centered (f g : ScatFun)
    (hg : IsCentered g.func) (hred : Reduces (omega g) f) :
    (IntertwineSet f g).Infinite := by
  obtain ⟨c, hc⟩ := hg;
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred; set y : ℕ → Baire := fun n => f.func (σ ⟨prepend n c.val, mem_gluingSet_prepend c.prop⟩); (
  refine Set.infinite_of_injective_forall_mem ( fun m n hmn => ?_ ) fun n => show y n ∈ f.IntertwineSet g from ?_;
  · -- `τ ∘ y` records the block index: `τ (y k) = (n)⌢(g c)`, injective in `k`.
    have key : ∀ k, prepend k (g.func c) = τ (y k) := fun k => by
      rw [← omega_func_prepend g k c]; exact heq _
    have h_eq : prepend m (g.func c) = prepend n (g.func c) := by
      rw [key m, key n, hmn];
    simpa using congr_fun h_eq 0;
  · intro V hV; rw [ mem_nhds_iff ] at hV; obtain ⟨ V₀, hV₀, hV₀' ⟩ := hV;
    -- Apply `centerInvariance_reduce` to obtain the reduction.
    have h_centerInvariance : ContinuouslyReduces g.func (f.func ∘ (Subtype.val : ↑{w : ↑f.domain | f.func w ∈ V₀} → ↑f.domain)) := by
      have h_centerInvariance : ∃ σc : ↑g.domain → ↑f.domain, Continuous σc ∧ ∃ τc : Baire → Baire, ContinuousOn τc (Set.range (f.func ∘ σc)) ∧ ∀ z, g.func z = τc (f.func (σc z)) ∧ σc c ∈ {w : ↑f.domain | f.func w ∈ V₀} := by
        refine ⟨ fun z => σ ⟨ prepend n z.val, mem_gluingSet_prepend z.prop ⟩, ?_, fun z => unprepend ( τ z ), ?_, ?_ ⟩;
        · exact hσ.comp ( Continuous.subtype_mk ( continuous_prepend n |> Continuous.comp <| continuous_subtype_val ) _ );
        · refine ContinuousOn.comp ( show ContinuousOn ( fun z => unprepend z ) ( Set.univ : Set Baire ) from ?_ ) ?_ ?_;
          · exact continuous_unprepend.continuousOn;
          · refine' hτ.mono _;
            exact Set.range_subset_iff.mpr fun x => ⟨ _, rfl ⟩;
          · exact fun x hx => Set.mem_univ _;
        · intro z
          refine ⟨?_, hV₀'.2⟩
          show g.func z
            = unprepend (τ (f.func (σ ⟨prepend n z.val, mem_gluingSet_prepend z.prop⟩)))
          rw [← heq ⟨prepend n z.val, mem_gluingSet_prepend z.prop⟩, omega_func_prepend g n z,
            unprepend_prepend]
      obtain ⟨ σc, hσc, τc, hτc, h ⟩ := h_centerInvariance; exact centerInvariance_reduce hc hσc hτc ( fun z => h z |>.1 ) ( hV₀'.1.preimage f.hCont ) ( h c |>.2 ) ;
    exact ScatFun.reduces_coRestrict_of_subtype f g V₀ h_centerInvariance |> fun h => h.trans ( ScatFun.coRestrict_reduces_of_subset f hV₀ ));

/-- **Lemma `Intertwinereductionsforomegacentered`, first part (`ScatFun` form).**

Let `f : ScatFun` and `G : Fin n → ScatFun` with every `G k` centered.  If `ω (G k) ≤ f` for all
`k`, then `ω (gl G) ≤ f`. -/
theorem intertwine_reductions_omega_centered {n : ℕ} (f : ScatFun) (G : Fin n → ScatFun)
    (hG_cent : ∀ k, IsCentered (G k).func)
    (hG_red : ∀ k, Reduces (omega (G k)) f) :
    Reduces (omega (glFin G)) f :=
  intertwine_reductions f G
    (fun k => intertwineSet_infinite_of_centered f (G k) (hG_cent k) (hG_red k))

/-! ## Second part, item 1 (`5_precise_struct_memo.tex`, Lemma `Intertwinereductionsforomegacentered`)

> Moreover, if `f = ⊔_{i=0}^n f_i` for some `n ∈ ℕ`, then: if `g` is centered and `ω g ≤ f`, then
> `ω g ≤ f_i` for some `i ≤ n`.

Here `f = ⊔_i f_i` is rendered as `ScatFun.IsDisjointUnion` (memoir's `f = ⊔ᵢ fᵢ`,
`ScatFun/Basics.lean`): an `ℕ`-indexed clopen domain partition `A`, specialised to a finite
family by requiring blocks past index `n` to be empty (the same convention already used
elsewhere for finite disjoint unions, e.g. `CenteredFunctions/SimpleSuccessor/LamOne.lean`).
The blocks `f_i` are the restrictions `f.restrict (A i)`.

## Informal proof (memoir)

Take a center `c` for `g` and a continuous reduction `(σ, τ)` witnessing `ω g ≤ f`.  As
`f = ⊔_{i ≤ n} f_i`, there is `i ≤ n` such that `dom f_i` contains `σ((k)⌢c)` for infinitely many
`k`.  We conclude as before (the argument of the first part, `intertwineSet_infinite_of_centered`)
with `f_i` in place of `f`.

## Lean proof sketch

* Pigeonhole (`Finite.exists_infinite_fiber`) on the block index of `σ((k)⌢c)` gives an `i₀ ≤ n`
  with infinitely many `k` landing in `A i₀`.
* For each such `k`, `centerInvariance_reduce` is applied exactly as in the first part, but with
  the smaller *open* set `A i₀ ∩ f⁻¹(V₀)` (rather than just `f⁻¹(V₀)`), landing the reduction
  inside the block: `g ≤ f.restrict (A i₀ ∩ f⁻¹(V₀))`.
* The bridge lemma `restrict_inter_reduces_coRestrict_restrict` identifies this (up to the same
  underlying `Baire` points) with `g ≤ (f.restrict (A i₀)).coRestrict V₀`, i.e. membership in
  `IntertwineSet (f.restrict (A i₀)) g`.
* `intertwine_reductions` (single-block family `Fin 1`) then gives
  `ω (glFin (fun _ : Fin 1 => g)) ≤ f.restrict (A i₀)`; composing with the block-0 embedding
  `g ≤ glFin (fun _ : Fin 1 => g)` (`reduces_block_gl`) gives `ω g ≤ f.restrict (A i₀)`.
-/

/-- **A single block reduces to the plain gluing.**  For any family `F : ℕ → ScatFun` and index
`i`, `F i ≤ gl F` via the block-`i` embedding `z ↦ (i)⌢z`.  A basic companion to `gl_func_prepend`
that (unlike `pgl`'s analogous `block_reduces_pgl`) does not yet have a home for plain `gl`. -/
lemma reduces_block_gl (F : ℕ → ScatFun) (i : ℕ) : Reduces (F i) (gl F) := by
  refine ⟨fun z => ⟨prepend i z.val, mem_gluingSet_prepend z.prop⟩, ?_, unprepend, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_prepend i |>.comp continuous_subtype_val) _
  · exact continuous_unprepend.continuousOn
  · intro z
    show (F i).func z = unprepend ((gl F).func ⟨prepend i z.val, mem_gluingSet_prepend z.prop⟩)
    rw [gl_func_prepend F i z (mem_gluingSet_prepend z.prop), unprepend_prepend]

/-- **Bridge lemma.**  For `A ⊆ ↑f.domain` and `V ⊆ Baire`, the restriction of `f` to
`A ∩ f⁻¹(V)` reduces to the corestriction (to `V`) of the block `f.restrict A` — indeed both
sides realize the same underlying set of `Baire` points, just via different nestings of
`ScatFun.restrict`.  Needed to convert the domain-side output of `centerInvariance_reduce`
(landing in `f.restrict (A ∩ f⁻¹ V)`) into the codomain-side `IntertwineSet`-membership
statement for the block `f.restrict A`. -/
lemma restrict_inter_reduces_coRestrict_restrict (f : ScatFun) (A : Set ↑f.domain)
    (V : Set Baire) :
    Reduces (f.restrict (A ∩ {w : ↑f.domain | f.func w ∈ V})) ((f.restrict A).coRestrict V) := by
  have hmem : ∀ x : ↑(f.restrict (A ∩ {w : ↑f.domain | f.func w ∈ V})).domain,
      ∃ h : x.val ∈ (f.restrict A).domain,
        (⟨x.val, h⟩ : ↑(f.restrict A).domain) ∈
          {z : ↑(f.restrict A).domain | (f.restrict A).func z ∈ V} := by
    intro x
    obtain ⟨h, hU⟩ := x.property
    refine ⟨⟨h, hU.1⟩, ?_⟩
    show (f.restrict A).func ⟨x.val, ⟨h, hU.1⟩⟩ ∈ V
    have : (f.restrict A).func ⟨x.val, ⟨h, hU.1⟩⟩ = f.func ⟨x.val, h⟩ := rfl
    rw [this]
    exact hU.2
  refine ⟨fun x => ⟨x.val, hmem x⟩, Continuous.subtype_mk continuous_subtype_val _,
    id, continuousOn_id, fun x => ?_⟩
  rfl

/-- **Lemma `Intertwinereductionsforomegacentered`, second part, item 1 (`ScatFun` form).**

Let `f g : ScatFun` with `g` centered, `ω g ≤ f`, and `A : ℕ → Set ↑f.domain` a finite clopen
domain partition of `f` (`f.IsDisjointUnion A`, with blocks past index `n` empty).  Then
`ω g ≤ f.restrict (A i)` for some `i ≤ n`. -/
theorem intertwine_reductions_omega_centered_piece {n : ℕ} (f g : ScatFun) (A : ℕ → Set ↑f.domain)
    (hdu : f.IsDisjointUnion A) (hAn : ∀ i, n < i → A i = ∅)
    (hg_cent : IsCentered g.func) (hred : Reduces (omega g) f) :
    ∃ i ≤ n, Reduces (omega g) (f.restrict (A i)) := by
  obtain ⟨c, hc⟩ := hg_cent
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred
  set y : ℕ → Baire := fun k => f.func (σ ⟨prepend k c.val, mem_gluingSet_prepend c.prop⟩)
    with hy_def
  -- The block index containing the point `σ ((k)⌢c)`.
  have hidx : ∀ k : ℕ, ∃ i : Fin (n + 1),
      σ ⟨prepend k c.val, mem_gluingSet_prepend c.prop⟩ ∈ A i := by
    intro k
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (hdu.2.2 ▸ Set.mem_univ (σ ⟨prepend k c.val, mem_gluingSet_prepend c.prop⟩) :
        σ ⟨prepend k c.val, mem_gluingSet_prepend c.prop⟩ ∈ ⋃ j, A j)
    by_cases hin : i ≤ n
    · exact ⟨⟨i, by omega⟩, hi⟩
    · exact absurd hi (by rw [hAn i (by omega)]; exact Set.notMem_empty _)
  choose idx hidx using hidx
  obtain ⟨i₀, hi₀⟩ := Finite.exists_infinite_fiber idx
  have hX : {k : ℕ | idx k = i₀}.Infinite := Set.infinite_coe_iff.mp hi₀
  refine ⟨i₀.val, Nat.lt_succ_iff.mp i₀.isLt, ?_⟩
  set F := f.restrict (A (i₀ : ℕ)) with hF_def
  -- `y` is injective (same argument as the first part: `τ` records the block index).
  have hinj : Function.Injective y := by
    intro m k hmk
    have key : ∀ j, prepend j (g.func c) = τ (y j) := fun j => by
      rw [← omega_func_prepend g j c]; exact heq _
    have h_eq : prepend m (g.func c) = prepend k (g.func c) := by rw [key m, key k, hmk]
    simpa using congr_fun h_eq 0
  -- Each `y k` with `k ∈ {idx = i₀}` lies in `IntertwineSet F g`.
  have hmapsto : Set.MapsTo y {k : ℕ | idx k = i₀} (IntertwineSet F g) := by
    intro k hk V hV
    rw [mem_nhds_iff] at hV
    obtain ⟨V₀, hV₀, hV₀'⟩ := hV
    set U : Set ↑f.domain := A (i₀ : ℕ) ∩ {w : ↑f.domain | f.func w ∈ V₀} with hU_def
    have hU_open : IsOpen U := (hdu.1 (i₀ : ℕ)).isOpen.inter (hV₀'.1.preimage f.hCont)
    have hσk_mem : σ ⟨prepend k c.val, mem_gluingSet_prepend c.prop⟩ ∈ U :=
      ⟨hk ▸ hidx k, hV₀'.2⟩
    have h_centerInvariance : ContinuouslyReduces g.func
        (f.func ∘ (Subtype.val : ↥U → ↑f.domain)) := by
      have h_centerInvariance :
          ∃ σc : ↑g.domain → ↑f.domain, Continuous σc ∧ ∃ τc : Baire → Baire,
            ContinuousOn τc (Set.range (f.func ∘ σc)) ∧
            ∀ z, g.func z = τc (f.func (σc z)) ∧ σc c ∈ U := by
        refine ⟨fun z => σ ⟨prepend k z.val, mem_gluingSet_prepend z.prop⟩, ?_,
          fun z => unprepend (τ z), ?_, ?_⟩
        · exact hσ.comp (Continuous.subtype_mk
            (continuous_prepend k |> Continuous.comp <| continuous_subtype_val) _)
        · refine ContinuousOn.comp
            (show ContinuousOn (fun z => unprepend z) (Set.univ : Set Baire) from
              continuous_unprepend.continuousOn)
            (hτ.mono (Set.range_subset_iff.mpr fun x => ⟨_, rfl⟩)) (fun x _ => Set.mem_univ _)
        · intro z
          refine ⟨?_, hσk_mem⟩
          show g.func z
            = unprepend (τ (f.func (σ ⟨prepend k z.val, mem_gluingSet_prepend z.prop⟩)))
          rw [← heq ⟨prepend k z.val, mem_gluingSet_prepend z.prop⟩,
            omega_func_prepend g k z, unprepend_prepend]
      obtain ⟨σc, hσc, τc, hτc, h⟩ := h_centerInvariance
      exact centerInvariance_reduce hc hσc hτc (fun z => (h z).1) hU_open (h c).2
    have hred_block : Reduces g (f.restrict U) :=
      h_centerInvariance.comp_homeomorph_right (f.restrictEquiv U)
    have hred_V₀ : Reduces g (F.coRestrict V₀) :=
      hred_block.trans (restrict_inter_reduces_coRestrict_restrict f (A (i₀ : ℕ)) V₀)
    exact hred_V₀.trans (F.coRestrict_reduces_of_subset hV₀)
  have hIS : (IntertwineSet F g).Infinite := by
    set e := Set.Infinite.natEmbedding {k : ℕ | idx k = i₀} hX with he_def
    have hinj' : Function.Injective (fun j => y (e j).val) :=
      fun a b hab => e.injective (Subtype.ext (hinj hab))
    exact Set.infinite_of_injective_forall_mem hinj' (fun j => hmapsto (e j).prop)
  have hstep : Reduces (omega (glFin (fun _ : Fin 1 => g))) F :=
    intertwine_reductions F (fun _ : Fin 1 => g) (fun _ => hIS)
  have hg_block : Reduces g (glFin (fun _ : Fin 1 => g)) :=
    reduces_block_gl (fun k => if h : k < 1 then (fun _ : Fin 1 => g) ⟨k, h⟩ else empty) 0
  exact (gl_reduces_of_pointwise (fun _ => g) (fun _ => glFin (fun _ : Fin 1 => g))
    (fun _ => hg_block)).trans hstep

end ScatFun

end
