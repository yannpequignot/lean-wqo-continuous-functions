import WqoContinuousFunctions.ScatFun.PreciseStructure.IntertwineOmegaCentered
import WqoContinuousFunctions.ScatFun.Wedge.Defs
import Mathlib.Data.Nat.Nth

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# Intertwining reductions for `Maximalfct{λ}` (limit case)

Memoir Lemma `Intertwinereductionsforomegacentered` (`5_precise_struct_memo.tex`), **second
part, item 2**.

> Moreover, if `f = ⊔_{i=0}^n f_i` for some `n ∈ ℕ`, then: if `λ` is limit and
> `Maximalfct{λ} ≤ f`, then `Maximalfct{λ} ≤ f_i` for some `i ≤ n`.

Here everything is rendered at the `ScatFun` level (cf. `ScatFun/PreciseStructure/IntertwineOmegaCentered.lean`
for item 1, the analogous statement for `ω g` with `g` centered): `Maximalfct{λ}` is
`ScatFun.maxFun lam hlam_lt`, and `f = ⊔_{i≤n} f_i` is `f.IsDisjointUnion A` with blocks past
index `n` empty (same finite-union convention as item 1).

## Informal proof (memoir)

Using `Gluingcohomomorphism` and `JSLgeneralstructure`, notice that for every sequence `(β_k)`
cofinal in `λ`, `Maximalfct{λ} ≡ gl_{k ∈ ℕ} Minimalfct{β_k}`. Choose an increasing sequence
`(β_k)` cofinal in `λ` and recall that `⟨0⟩` is a center for each `Minimalfct{β_k}`. If `(σ, τ)`
witness `gl_{k∈ℕ} Minimalfct{β_k} ≤ ⊔_{i≤n} f_i`, then there exists `i ≤ n` such that
`X = {k ∈ ℕ | σ((k)⌢⟨0⟩) ∈ dom f_i}` is infinite. Note that the subsequence `(β_k)_{k∈X}` is
cofinal in `λ`, so `Maximalfct{λ} ≡ gl_{k∈X} Minimalfct{β_k} ≤ f_i`, as before.

## Lean proof, and where its pieces live

The two extra ingredients beyond item 1 (`intertwine_reductions_omega_centered_piece`) are the
plain-gluing CB-rank formula and the infinite-index intertwining machinery. Both are general
enough that they were factored out to their natural homes rather than kept local to this file:

* `CBRank (gl F).func = ⨆ k, CBRank (F k).func` — `ScatFun.gl_cbRank_eq`
  (`ScatFun/Wedge/Defs.lean`, next to the `slabHomeo`/`cbRank_wedge_slab` infrastructure it
  reuses; `ScatFun.empty_cbRank` is the `CBRank ScatFun.empty.func = 0` fact it needs, in
  `ScatFun/Operations/Gl.lean` next to `ScatFun.empty`).
* The monotone cofinal sequence `monoCofinal` and the two-valued supremum lemma
  `iSup_two_valued_infinite` — `CenteredFunctions/Theorems.lean` (`ConseqMinFunAux` namespace,
  next to `iSup_succ_cofinalSeq`), pure ordinal combinatorics with no `ScatFun` dependence.
* `ScatFun.exists_infinite_disjoint_open_nhds` and `ScatFun.intertwine_gl_subseq` — the
  infinite-index analogue of the finite intertwining machinery, in
  `ScatFun/IntertwineReductions.lean` next to `gl_coRestrict_disjoint_open_reduces` /
  `intertwine_reductions`.
-/

namespace ScatFun

open ConseqMinFunAux

/-- **Lemma `Intertwinereductionsforomegacentered`, second part, item 2 (`ScatFun` form).**

Let `f : ScatFun`, `lam` a nonzero limit ordinal `< ω₁`, and `A : ℕ → Set ↑f.domain` a finite
clopen domain partition of `f` (`f.IsDisjointUnion A`, with blocks past index `n` empty).  If
`Maximalfct{lam} ≤ f`, then `Maximalfct{lam} ≤ f.restrict (A i)` for some `i ≤ n`. -/
theorem intertwine_reductions_maxFun_limit_piece {n : ℕ} (f : ScatFun) (lam : Ordinal.{0})
    (hlam_lt : lam < omega1) (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0)
    (A : ℕ → Set ↑f.domain) (hdu : f.IsDisjointUnion A) (hAn : ∀ i, n < i → A i = ∅)
    (hred : Reduces (maxFun lam hlam_lt) f) :
    ∃ i ≤ n, Reduces (maxFun lam hlam_lt) (f.restrict (A i)) := by
  -- The base family: `M k = k_{monoCofinal lam k + 1}`, centered, of CB-rank `succ (γ k)`.
  set M : ℕ → ScatFun :=
    fun k => minFun (monoCofinal lam k) (lt_trans (monoCofinal_lt lam hlim hne k) hlam_lt)
    with hM_def
  -- `gl M ≡ maxFun lam` since `CB (gl M) = ⨆ succ (γ k) = lam`.
  have hMrank : ∀ k, CBRank (M k).func = Order.succ (monoCofinal lam k) := fun k =>
    minFun_cbRank_eq _ _
  have hglMrank : CBRank (gl M).func = lam := by
    rw [gl_cbRank_eq]
    rw [show (⨆ k, CBRank (M k).func) = ⨆ k, Order.succ (monoCofinal lam k) from
      iSup_congr hMrank]
    exact monoCofinal_iSup_succ lam hlam_lt hlim hne
  have hequivM : Equiv (gl M) (maxFun lam hlam_lt) :=
    limit_rank_equiv_maxFun (gl M) lam hlam_lt hlim hglMrank
  have hredM : Reduces (gl M) f := hequivM.1.trans hred
  obtain ⟨σ, hσ, τ, hτ, heqσ⟩ := hredM
  -- A center for each block.
  have hcent : ∀ k, ∃ x : ↥(M k).domain, IsCenterFor (M k).func x := fun k =>
    minFun_isCentered (monoCofinal lam k) (lt_trans (monoCofinal_lt lam hlim hne k) hlam_lt)
  choose c hc using hcent
  -- The domain point `p k = σ ((k)⌢c k)`.
  set p : ℕ → ↥f.domain :=
    fun k => σ ⟨prepend k (c k).val, mem_gluingSet_prepend (c k).prop⟩ with hp_def
  -- Pigeonhole on the block index containing `p k`.
  have hidx : ∀ k : ℕ, ∃ i : Fin (n + 1), p k ∈ A i := by
    intro k
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (hdu.2.2 ▸ Set.mem_univ (p k) : p k ∈ ⋃ j, A j)
    by_cases hin : i ≤ n
    · exact ⟨⟨i, by omega⟩, hi⟩
    · exact absurd hi (by rw [hAn i (by omega)]; exact Set.notMem_empty _)
  choose idx hidx using hidx
  obtain ⟨i₀, hi₀⟩ := Finite.exists_infinite_fiber idx
  have hX : {k : ℕ | idx k = i₀}.Infinite := Set.infinite_coe_iff.mp hi₀
  refine ⟨i₀.val, Nat.lt_succ_iff.mp i₀.isLt, ?_⟩
  set F := f.restrict (A (i₀ : ℕ)) with hF_def
  -- Enumerate `X = {k | idx k = i₀}` strictly monotonically.
  set e : ℕ → ℕ := Nat.nth (fun k => idx k = i₀) with he_def
  have he : StrictMono e := Nat.nth_strictMono hX
  have hmem_e : ∀ j, idx (e j) = i₀ := Nat.nth_mem_of_infinite hX
  -- The block family and codomain points along `X`.
  set Nseq : ℕ → ScatFun := fun j => M (e j) with hNseq_def
  set wpt : ℕ → Baire := fun j => f.func (p (e j)) with hwpt_def
  -- `wpt` is injective (`τ` records the block index `e j`).
  have hwpt_inj : Function.Injective wpt := by
    have key : ∀ j, τ (wpt j) = prepend (e j) ((M (e j)).func (c (e j))) := by
      intro j
      have h1 := heqσ ⟨prepend (e j) (c (e j)).val, mem_gluingSet_prepend (c (e j)).prop⟩
      rw [gl_func_prepend M (e j) (c (e j)) (mem_gluingSet_prepend (c (e j)).prop)] at h1
      exact h1.symm
    intro a b hab
    have h2 : prepend (e a) ((M (e a)).func (c (e a)))
        = prepend (e b) ((M (e b)).func (c (e b))) := by rw [← key a, ← key b, hab]
    have h0 : e a = e b := by have := congrFun h2 0; simpa [prepend] using this
    exact he.injective h0
  -- Each `wpt j` lies in `IntertwineSet F (Nseq j)` (center-invariance argument, item 1 style).
  have hwpt_mem : ∀ j, wpt j ∈ IntertwineSet F (Nseq j) := by
    intro j V hV
    rw [mem_nhds_iff] at hV
    obtain ⟨V₀, hV₀, hV₀'⟩ := hV
    set U : Set ↑f.domain := A (i₀ : ℕ) ∩ {w : ↑f.domain | f.func w ∈ V₀} with hU_def
    have hU_open : IsOpen U := (hdu.1 (i₀ : ℕ)).isOpen.inter (hV₀'.1.preimage f.hCont)
    have hpj : p (e j) ∈ A (i₀ : ℕ) := (hmem_e j) ▸ hidx (e j)
    have hσk_mem : p (e j) ∈ U := ⟨hpj, hV₀'.2⟩
    have h_centerInvariance : ContinuouslyReduces (Nseq j).func
        (f.func ∘ (Subtype.val : ↥U → ↑f.domain)) := by
      have h_ci :
          ∃ σc : ↑(Nseq j).domain → ↑f.domain, Continuous σc ∧ ∃ τc : Baire → Baire,
            ContinuousOn τc (Set.range (f.func ∘ σc)) ∧
            ∀ z, (Nseq j).func z = τc (f.func (σc z)) ∧ σc (c (e j)) ∈ U := by
        refine ⟨fun z => σ ⟨prepend (e j) z.val, mem_gluingSet_prepend z.prop⟩, ?_,
          fun z => unprepend (τ z), ?_, ?_⟩
        · exact hσ.comp (Continuous.subtype_mk
            (continuous_prepend (e j) |> Continuous.comp <| continuous_subtype_val) _)
        · refine ContinuousOn.comp
            (show ContinuousOn (fun z => unprepend z) (Set.univ : Set Baire) from
              continuous_unprepend.continuousOn)
            (hτ.mono (Set.range_subset_iff.mpr fun x => ⟨_, rfl⟩)) (fun x _ => Set.mem_univ _)
        · intro z
          refine ⟨?_, hσk_mem⟩
          show (Nseq j).func z
            = unprepend (τ (f.func (σ ⟨prepend (e j) z.val, mem_gluingSet_prepend z.prop⟩)))
          rw [← heqσ ⟨prepend (e j) z.val, mem_gluingSet_prepend z.prop⟩,
            gl_func_prepend M (e j) z (mem_gluingSet_prepend z.prop), unprepend_prepend]
      obtain ⟨σc, hσc, τc, hτc, h⟩ := h_ci
      exact centerInvariance_reduce (hc (e j)) hσc hτc (fun z => (h z).1) hU_open (h (c (e j))).2
    have hred_block : Reduces (Nseq j) (f.restrict U) :=
      h_centerInvariance.comp_homeomorph_right (f.restrictEquiv U)
    have hred_V₀ : Reduces (Nseq j) (F.coRestrict V₀) :=
      hred_block.trans (restrict_inter_reduces_coRestrict_restrict f (A (i₀ : ℕ)) V₀)
    exact hred_V₀.trans (F.coRestrict_reduces_of_subset hV₀)
  -- Assemble the infinite gluing reduction and read off its CB-rank.
  obtain ⟨N, hNred, hNinf, hNcases⟩ := intertwine_gl_subseq F Nseq wpt hwpt_inj hwpt_mem
  have hNrank : CBRank (gl N).func = lam := by
    rw [gl_cbRank_eq]
    apply iSup_two_valued_infinite (t := fun k => Order.succ (monoCofinal lam (e k)))
      (lam := lam) (w := fun k => CBRank (N k).func) (S := {k | N k = Nseq k})
    · -- `t` monotone
      exact fun a b hab => Order.succ_le_succ (monoCofinal_mono lam (he.monotone hab))
    · exact iSup_succ_monoCofinal_comp lam hlam_lt hlim hne e he
    · -- pointwise `≤`
      intro k
      show CBRank (N k).func ≤ Order.succ (monoCofinal lam (e k))
      rcases hNcases k with hk | hk
      · rw [hk]; exact le_of_eq (hMrank (e k))
      · rw [hk, empty_cbRank]; exact zero_le _
    · exact hNinf
    · intro k hk
      show CBRank (N k).func = Order.succ (monoCofinal lam (e k))
      rw [hk]; exact hMrank (e k)
  -- `maxFun lam ≡ gl N`, and `gl N ≤ F`, so `maxFun lam ≤ F`.
  have hequivN : Equiv (gl N) (maxFun lam hlam_lt) :=
    limit_rank_equiv_maxFun (gl N) lam hlam_lt hlim hNrank
  exact hequivN.2.trans hNred

end ScatFun

end
