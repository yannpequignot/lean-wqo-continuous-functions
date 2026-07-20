import WqoContinuousFunctions.ScatFun.Wedge.LowerBound
import WqoContinuousFunctions.ScatFun.Wedge.UpperBound
import WqoContinuousFunctions.ScatFun.FiniteGluing
import WqoContinuousFunctions.ScatFun.IntertwineReductions
import WqoContinuousFunctions.ScatFun.Operations.MaxMinFun
import WqoContinuousFunctions.CenteredFunctions.Theorems
import WqoContinuousFunctions.ScatFun.PreciseStructure.IntertwineOmegaCentered
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.Shared
import WqoContinuousFunctions.ContinuousReducibility.Scattered.Decomposition
import GeneralTopology.ClopenPartitions

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# The diagonal case at `λ+1` (`Diagonalforlambda+1`)

Memoir Lemma `Diagonalforlambda+1` (`5_precise_struct_memo.tex:356`), the one place where the
wedge operation is needed to finitely generate `𝒞_{λ+1}` (`FGatsuccessoroflimit`).

> Suppose that `f = ⊔_{n∈ℕ} f_n : A_n → B` for simple functions `f_n ∈ 𝒞_{λ+1}` with pairwise
> distinct distinguished points `y_n`. Assume that:
> 1. `f_0 ≡ pgl Maximalfct{λ}`,
> 2. `f_n ≤ Minimalfct{λ+1} ⊕ Maximalfct{λ}` whenever `n > 0`, and
> 3. `(y_n)_{n>0}` converges to `y_0`.
>
> Then for all clopen neighborhood `U` of `y_0` we have
> `f ≤ ⋁(Maximalfct{λ} ∣ Minimalfct{λ+1}) ≤ f ↾ U`.

## Rendering at the `ScatFun` level

* `Maximalfct{λ}` is `ScatFun.maxFun lam hlam_lt` (`CBRank = lam`).
* `Minimalfct{λ+1}` is `ScatFun.minFun lam hlam_lt` (`CBRank = lam + 1`; the memoir indexes
  `Minimalfct` by the rank it realises, `minFun`'s Lean argument is the ordinal *below* the
  successor — same convention as `simple_below_max_dichotomy`/`simple_dichotomy_lam_one` in
  `CenteredFunctions/SimpleSuccessorOfLimit.lean`, which produce exactly
  `minFun lam hlam_lt ⊕ maxFun lam hlam_lt` for "`k_{λ+1} ⊕ ℓ_λ`").
* `pgl Maximalfct{λ}` is `ScatFun.succMaxFun lam hlam_lt` (`= pgl (fun _ => maxFun lam hlam_lt)`
  definitionally, `ScatFun/Operations/MaxMinFun.lean`).
* `Minimalfct{λ+1} ⊕ Maximalfct{λ}` (memoir `\glbin`, binary finite gluing) is
  `ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt` (`ScatFun.glBin`, notation `⊕`,
  `= Gl ![minFun lam hlam_lt, maxFun lam hlam_lt] ![1, 1]`).
* `⋁(Maximalfct{λ} ∣ Minimalfct{λ+1})` (single vertical, `k = 0` in the memoir's
  `⋁(f_0,…,f_k ∣ f_{k+1})`) is `ScatFun.wedge (fun _ : Fin 1 => maxFun lam hlam_lt)
  (minFun lam hlam_lt)`.
* `f = ⊔_{n∈ℕ} f_n` is `F.IsDisjointUnion A` with blocks `f_n = F.restrict (A n)`; unlike the
  finite-union convention used elsewhere in this development (e.g.
  `intertwine_reductions_maxFun_limit_piece`), here **all** blocks may be nonempty — no padding
  by `ScatFun.empty` — matching `ScatFun.IsDisjointUnion`'s genuinely countable partition.
* "`f_n` simple in `𝒞_{λ+1}` with distinguished point `y_n`" is rendered as the pair
  `CBRank (F.restrict (A n)).func = lam + 1` together with `∀ x ∈ CBLevel (F.restrict (A n)).func
  lam, (F.restrict (A n)).func x = y n` — this is exactly the data produced by
  `simple_lam_data lam (F.restrict (A n)) hrank hsimple` (`CenteredFunctions/SimpleSuccessor/
  Shared.lean`) once the (derivable) `SimpleFun` witness is pinned to the specific point `y n`;
  no separate `SimpleFun` hypothesis is needed since `hrank` + `hy` already forces it (`CBLevel
  (succ lam) = ∅` from `CBLevel_eq_empty_at_rank`, and nonemptiness at `lam` from
  `CBLevel_nonempty_below_rank`).

PROVIDED SOLUTION

The memoir proof has two parts, matching the two inequalities:

1. **`⋁(Maximalfct{λ} ∣ Minimalfct{λ+1}) ≤ f ↾ U`** via the Disjointification Lemma
   (memoir `DisjointificationLemma`, Lean `ScatFun.wedge_lower_bound` in
   `ScatFun/Wedge/LowerBound.lean`, fully proved) with anchor `y = y 0`. The vertical anchor
   `x` comes from centeredness of `f_0 ≡ pgl Maximalfct{λ}` (`Centerinvariance`,
   Lean `centerInvariance_reduce`) plus rigidity of the cocenter (Lean
   `rigidityOfCocenter_separation`, `CenteredFunctions/Theorems.lean`) to get the separation
   clause `y 0 ∉ closure (range (F.func ∘ σ))`. The diagonal reduction comes from
   `CBRank (F.restrict W).func = lam + 1` on shrinking clopen neighbourhoods `W` of some
   `y n ∈ V` (`n > 0`, using hypothesis 3) via `minFun_is_minimum`/`minFun_reduces_simple`.

2. **`f ≤ ⋁(Maximalfct{λ} ∣ Minimalfct{λ+1})`** via the Wedge-as-upper-bound criterion (memoir
   `Wedgeasupperbound`, Lean `ScatFun.wedge_upper_bound` in `ScatFun/Wedge/UpperBound.lean`,
   fully proved). This needs a *finite* re-partition `Ã_0 = A_0 ∪ A^0`, `Ã_n = A^1_n` (`n>0`)
   built by peeling off, from each `f_n` (`n>0`), a piece landing in a shrinking clopen
   neighbourhood of `y 0` that reduces to `Minimalfct{λ+1}` (`ScatFun.gl` upper-bound
   criterion, memoir `Gluingasupperbound`, Lean `gluingFun_upper_bound_*` in
   `ContinuousReducibility/Gluing/UpperBound.lean`), leaving an `A^0_n` piece of `CB`-rank
   `≤ lam`; the union `A^0 = ⋃_{n>0} A^0_n` then has `CB`-rank `≤ lam` by the clopen-union
   formula (memoir `CBrankofclopenunion`, Lean `cb_rank_of_clopen_union`).

Both halves are substantial (each rests on an already-proved but intricate wedge bound); this
file only records the statement for now.

Write two lemmas, one for each inequality.
-/

namespace ScatFun

/-
A `ScatFun` of CB-rank `lam + 1` that is constant (`= y`) on its top CB-level `lam`
is a simple function.  This packages `hrank`+`hdistinguished` into the `SimpleFun` predicate
needed by `minFun_reduces_simple`, `simple_reduces_succMaxFun`, etc.
-/
lemma simpleFun_of_rank_of_const (g : ScatFun) (lam : Ordinal.{0})
    (hrank : CBRank g.func = lam + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y) :
    SimpleFun g.func := by
  refine ⟨ lam, ?_, ?_, y, hconst ⟩;
  · have := CBLevel_nonempty_below_rank g.func g.hScat lam;
    exact this ( hrank.symm ▸ lt_add_one lam );
  · have h_empty : CBLevel g.func (CBRank g.func) = ∅ := by
      apply CBLevel_eq_empty_at_rank;
      exact g.hScat;
    aesop

/-
**Localized minimality of `minFun`.**  For a simple `ScatFun` `g` of CB-rank `lam+1`
with distinguished value `y0`, and a clopen neighbourhood `W` of `y0`, the minimum
`minFun lam` reduces into `g` with *all values landing in `W`*.  (Corestrict `g` to the
clopen `g⁻¹ W`; its top CB-level survives since the top-level value `y0 ∈ W`, so
`minFun_is_minimum` applies, and every value of the corestriction lies in `W`.)
-/
lemma minFun_reduces_into_clopen (g : ScatFun) (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y0 : Baire) (hne : (CBLevel g.func lam).Nonempty)
    (hdist : ∀ x ∈ CBLevel g.func lam, g.func x = y0)
    (W : Set Baire) (hW : IsClopen W) (hy0W : y0 ∈ W) :
    ∃ (σ : ↑(minFun lam hlam_lt).domain → ↑g.domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun z => g.func (σ z)) ∧
      (∀ z, (minFun lam hlam_lt).func z = τ (g.func (σ z))) ∧
      (∀ z, g.func (σ z) ∈ W) := by
  -- Let `S : Set ↑g.domain := {a | g.func a ∈ W}`. Note `S = g.func ⁻¹' W` is open in `g.domain` since `g.hCont` is continuous and `W` is open (`hW.isOpen`).
  set S : Set g.domain := {a | g.func a ∈ W}
  have hS_open : IsOpen S := by
    exact IsOpen.preimage g.hCont hW.2;
  -- By `local_cb_derivative`, we have `CBLevel (g.func ∘ (Subtype.val : S → g.domain)) lam = CBLevel g.func lam ∩ S`.
  have h_local_cb_derivative : CBLevel (g.func ∘ (Subtype.val : S → g.domain)) lam = CBLevel g.func lam ∩ S := by
    rw [ local_cb_derivative _ hS_open ];
  -- By `CBLevel_homeomorph`, we have `CBLevel g'.func lam = (g.restrictEquiv S).symm '' CBLevel (g.func ∘ (Subtype.val : S → g.domain)) lam`.
  set g' := g.restrict S
  have h_cbLevel_g' : CBLevel g'.func lam = (g.restrictEquiv S).symm '' CBLevel (g.func ∘ (Subtype.val : S → g.domain)) lam := by
    have h_cbLevel_g' : CBLevel ((g.func ∘ (Subtype.val : S → g.domain)) ∘ (g.restrictEquiv S)) lam = (g.restrictEquiv S).symm '' CBLevel (g.func ∘ (Subtype.val : S → g.domain)) lam := by
      convert CBLevel_homeomorph _ _ _;
      exact Homeomorph.image_symm (g.restrictEquiv S)
    convert h_cbLevel_g' using 1;
  -- By `minFun_is_minimum`, we have `ContinuouslyReduces (MinFun lam) g'.func`.
  obtain ⟨σ0, τ0, hσ0, hτ0, h_eq⟩ : ∃ σ0 : (minFun lam hlam_lt).domain → g'.domain,
    ∃ τ0 : Baire → Baire,
    Continuous σ0 ∧
    ContinuousOn τ0 (range (fun z => g'.func (σ0 z))) ∧
    ∀ z, (minFun lam hlam_lt).func z = τ0 (g'.func (σ0 z)) := by
      have h_minFun_is_minimum : ContinuouslyReduces (MinFun lam) g'.func := by
        have h_top_level_nonempty : (CBLevel g'.func lam).Nonempty := by
          obtain ⟨ x, hx ⟩ := hne;
          simp_all +decide [ Set.ext_iff ];
          exact ⟨ _, h_cbLevel_g' _ _ |>.2 ⟨ _, _, _, h_local_cb_derivative _ _ |>.2 ⟨ hx, by aesop ⟩ |>.2, rfl ⟩ ⟩
        apply minFun_is_minimum lam hlam_lt g'.domain g'.func g'.hCont g'.hScat h_top_level_nonempty;
      obtain ⟨ σ0, hσ0, τ0, hτ0, h_eq ⟩ := h_minFun_is_minimum;
      exact ⟨ σ0, τ0, hσ0, hτ0, fun z => by simpa [ minFun_func ] using h_eq z ⟩;
  refine ⟨ fun z => ( g.restrictEquiv S ( σ0 z ) ).val, τ0, ?_, ?_, ?_, ?_ ⟩;
  · exact Continuous.comp ( continuous_subtype_val ) ( g.restrictEquiv S |> Homeomorph.continuous |> Continuous.comp <| hσ0 );
  · convert hτ0 using 1;
  · convert h_eq using 3;
  · grind +qlia

/-
**Transport a block reduction into the corestriction.**  If a continuous `σ1` sends
`h.domain` into the block `F.restrict An` with all values in `U`, then the same underlying
points live in `(F.coRestrict U).domain`, giving a continuous `σ` with matching values.
-/
lemma reduces_block_into_coRestrict (F : ScatFun) (An : Set ↑F.domain) (U : Set Baire)
    (h : ScatFun) (σ1 : ↑h.domain → ↑(F.restrict An).domain)
    (hσ1 : Continuous σ1) (hval : ∀ z, (F.restrict An).func (σ1 z) ∈ U) :
    ∃ σ : ↑h.domain → ↑(F.coRestrict U).domain,
      Continuous σ ∧
      (∀ z, ((σ z : ↑(F.coRestrict U).domain) : Baire) = ((σ1 z : ↑(F.restrict An).domain) : Baire)) ∧
      ∀ z, (F.coRestrict U).func (σ z) = (F.restrict An).func (σ1 z) := by
  refine' ⟨ fun z => ⟨ ( σ1 z ).val, ⟨ ( σ1 z ).2.1, hval z ⟩ ⟩, _, fun z => rfl, _ ⟩;
  · fun_prop;
  · unfold ScatFun.restrict; aesop;

/-
**Diagonal clause of `wedge_lower_bound`** for the diagonal case: for every open
neighbourhood `V` of `y 0`, the minimum `minFun lam` reduces into `F.coRestrict U` with all
values in `V` and cocenter separation `y 0 ∉ closure`.
-/
lemma diagonal_wedge_diag_clause (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdistinguished : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = y n)
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0)))
    (U : Set Baire) (hU : IsClopen U) (hyU : y 0 ∈ U)
    (V : Set Baire) (hV : IsOpen V) (hyV : y 0 ∈ V) :
    ∃ (σ : ↑(minFun lam hlam_lt).domain → ↑(F.coRestrict U).domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict U).func (σ z)) ∧
      (∀ z, (minFun lam hlam_lt).func z = τ ((F.coRestrict U).func (σ z))) ∧
      (∀ z, (F.coRestrict U).func (σ z) ∈ V) ∧
      y 0 ∉ closure (Set.range fun z => (F.coRestrict U).func (σ z)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N > 0 ∧ y N ∈ V ∧ y N ∈ U := by
    have := hconv.eventually ( hV.mem_nhds hyV |> Filter.Eventually.and <| hU.2.mem_nhds hyU ) ; obtain ⟨ n, hn ⟩ := this.exists; exact ⟨ n + 1, Nat.succ_pos _, hn ⟩ ;
  obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ y N ∈ W ∧ W ⊆ (V ∩ U) ∧ y 0 ∉ W := by
    have := baire_exists_clopen_subset_of_open ( y N ) ( ( V ∩ U ) \ { y 0 } ) ?_ ?_;
    · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, fun x hx => this.choose_spec.2.2 hx |>.1, fun hx => this.choose_spec.2.2 hx |>.2 rfl ⟩;
    · exact IsOpen.sdiff ( hV.inter hU.isOpen ) ( isClosed_singleton );
    · exact ⟨ ⟨ hN.2.1, hN.2.2 ⟩, fun h => by have := hy_inj ( by aesop : y N = y 0 ) ; linarith ⟩;
  -- Localized minFun reduction into the block.
  obtain ⟨σ1, τ, hσ1, hτ, hred, hval⟩ : ∃ σ1 : ↑(minFun lam hlam_lt).domain → ↑(F.restrict (A N)).domain, ∃ τ : Baire → Baire,
    Continuous σ1 ∧ ContinuousOn τ (Set.range fun z => (F.restrict (A N)).func (σ1 z)) ∧
    (∀ z, (minFun lam hlam_lt).func z = τ ((F.restrict (A N)).func (σ1 z))) ∧
    (∀ z, (F.restrict (A N)).func (σ1 z) ∈ W) := by
      apply minFun_reduces_into_clopen;
      exact CBLevel_nonempty_below_rank _ ( F.restrict ( A N ) |> ScatFun.hScat ) _ ( by simp +decide [ hrank ] );
      exacts [ hdistinguished N, hW.1, hW.2.1 ];
  obtain ⟨σ, hσc, hσval, hσeq⟩ :=
    reduces_block_into_coRestrict F (A N) U (minFun lam hlam_lt) σ1 hσ1
      (fun z => (hW.2.2.1 (hval z)).2)
  refine ⟨ σ, τ, hσc, ?_, ?_, ?_, ?_ ⟩;
  · simp only [hσeq]; exact hτ;
  · intro z; simp only [hσeq]; exact hred z;
  · exact fun z => hσeq z ▸ hW.2.2.1 ( hval z ) |>.1;
  · simp only [hσeq];
    exact fun h => hW.2.2.2 <| closure_minimal ( Set.range_subset_iff.mpr fun z => hval z ) hW.1.isClosed h

/-
A `ScatFun` whose CB-rank is `≤ lam` reduces to `maxFun lam` (`ℓ_λ` is the maximum of
`𝒞_{≤λ}`).  Direct from `maxFun_is_maximum` item 1.
-/
lemma reduces_maxFun_of_rank_le (h : ScatFun) (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hle : CBRank h.func ≤ lam) : Reduces h (maxFun lam hlam_lt) := by
  apply (maxFun_is_maximum lam hlam_lt).1 h.func h.hCont h.hScat (fun β hβ => by
    -- Since $CBLevel h.func (CBRank h.func) = \emptyset$ and $CBRank h.func \leq \beta$, we have $CBLevel h.func \beta \subseteq CBLevel h.func (CBRank h.func) = \emptyset$.
    have h_subset : CBLevel h.func β ⊆ CBLevel h.func (CBRank h.func) := by
      exact CBLevel_antitone _ ( le_trans hle hβ );
    exact Set.eq_empty_of_subset_empty ( h_subset.trans ( CBLevel_eq_empty_at_rank h.func h.hScat ▸ Set.Subset.refl _ ) ))

/-! ### Generic building blocks for the `wedge_upper_bound` (first inequality) direction -/

/-- Reducing to a single generator gives a reduction to the one-element gluing list. -/
lemma reduces_glList_one (g d : ScatFun) (h : Reduces g d) :
    Reduces g (glList (List.replicate 1 d)) := by
  have hb : Reduces d (glList (List.replicate 1 d)) := by
    have := reduces_block_gl (fun k => (List.replicate 1 d).getD k ScatFun.empty) 0
    simpa [ScatFun.glList] using this
  exact h.trans hb

/-
A `ScatFun` that reduces to `empty` has empty domain.
-/
lemma domain_isEmpty_of_reduces_empty (H : ScatFun) (h : Reduces H empty) :
    H.domain = ∅ := by
  obtain ⟨σ, τ, hσ, hτ, h⟩ := h;
  exact Set.eq_empty_of_forall_notMem fun x hx => by have := σ ⟨ x, hx ⟩ ; cases this ; tauto;

/-
**Split a reduction to a plain gluing.**  If `H` reduces to `gl F`, then `↑H.domain` splits
into a clopen partition `(P k)` with `H.restrict (P k)` reducing to `F k` for every `k`.
Generalises `reduces_replicate_split` (`ScatFun/Wedge/UpperBound.lean`).
-/
lemma reduces_gl_split (H : ScatFun) (F : ℕ → ScatFun) (hred : Reduces H (gl F)) :
    ∃ P : ℕ → Set ↑H.domain,
      (∀ k, IsClopen (P k)) ∧ (∀ k l, k ≠ l → Disjoint (P k) (P l)) ∧
      (⋃ k, P k = Set.univ) ∧ (∀ k, Reduces (H.restrict (P k)) (F k)) := by
  obtain ⟨ σ, τ, hσ, hτ, h_eq ⟩ := hred;
  refine ⟨ fun k => { x : H.domain | ( σ x : Baire ) 0 = k }, ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ Set.ext_iff ];
  · intro k;
    constructor;
    · exact isClosed_eq ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val.comp τ ) continuous_const;
    · convert isOpen_discrete { k } |> IsOpen.preimage ( show Continuous fun x : H.domain => ( σ x : Baire ) 0 from ?_ ) using 1;
      exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val.comp τ;
  · exact fun k l hkl => Set.disjoint_left.mpr fun x hxk hxl => hkl <| hxk.symm.trans hxl;
  · intro k
    set Pk : Set H.domain := {x | (σ x).val 0 = k};
    -- Define σ' : ↑(Pk) → ↑(F k).domain by σ' w := ⟨unprepend (σ w).val, _⟩.
    obtain ⟨σ', hσ'⟩ : ∃ σ' : ↑Pk → ↑(F k).domain, Continuous σ' ∧ ∀ w : ↑Pk, (σ w).val = prepend k (σ' w).val := by
      have h_unprepend : ∀ w : Pk, ∃ a : Baire, (σ w).val = prepend k a ∧ a ∈ (F k).domain := by
        intro w
        obtain ⟨a, ha⟩ : ∃ a : Baire, (σ w).val = prepend k a := by
          use unprepend (σ w).val;
          rw [ ← w.2, prepend_unprepend ];
        have := σ w |>.2; simp_all +decide [ GluingSet ] ;
        obtain ⟨ i, x, hx, h ⟩ := this; have := congr_fun h 0; simp_all +decide [ prepend ] ;
        exact ⟨ x, h.symm, hx ⟩;
      choose a ha using h_unprepend;
      use fun w => ⟨a w, ha w |>.2⟩;
      have h_unprepend_cont : Continuous (fun w : Pk => unprepend (σ w).val) := by
        exact continuous_unprepend.comp ( continuous_subtype_val.comp ( τ.comp continuous_subtype_val ) );
      convert h_unprepend_cont using 1;
      constructor <;> intro h <;> rw [ continuous_induced_rng ] at * <;> aesop;
    -- Define τ' : Baire → Baire by τ' b := hσ (prepend k b).
    obtain ⟨τ', hτ'⟩ : ∃ τ' : Baire → Baire, ContinuousOn τ' (Set.range (fun z => (F k).func (σ' z))) ∧ ∀ z : ↑Pk, hσ ((gl F).func (σ z)) = τ' ((F k).func (σ' z)) := by
      refine ⟨ fun b => hσ ( prepend k b ), ?_, ?_ ⟩;
      · refine hτ.comp ?_ ?_;
        · exact Continuous.continuousOn ( continuous_prepend k );
        · intro x hx; obtain ⟨ z, rfl ⟩ := hx; use ⟨ z, by
            exact z.1.2 ⟩ ; simp +decide ;
          convert gl_func_prepend F k ( σ' z ) _ using 1;
          exact congr_arg _ ( Subtype.ext <| hσ'.2 z );
          exact hσ'.2 z ▸ ( σ z ).2;
      · intro z
        have h_eq : (gl F).func (σ z) = prepend k ((F k).func (σ' z)) := by
          convert gl_func_prepend F k ( σ' z ) _ using 1;
          exact congr_arg _ ( Subtype.ext <| hσ'.2 z );
          exact hσ'.2 z ▸ ( σ z ).2
        simp [h_eq];
    have h_cont : ContinuouslyReduces (H.func ∘ Subtype.val : ↑Pk → Baire) ((F k).func : ↑(F k).domain → Baire) := by
      use σ', hσ'.1, τ', hτ'.1;
      grind;
    convert h_cont.comp_homeomorph_left ( H.restrictEquiv Pk ) using 1

/-
**Split a reduction to a binary gluing.**  If `G.restrict S` (with `S` clopen) reduces to
`a ⊕ b`, then `S` splits into two clopen pieces `Sa, Sb` (as subsets of `↑G.domain`) with
`G.restrict Sa ≤ a` and `G.restrict Sb ≤ b`.  (`gluingFun_upper_bound_forward` on the
re-realized domain, then `clopen_partition_restrict_transport` back to `↑G.domain`.)
-/
lemma reduces_glBin_split (G a b : ScatFun) (S : Set ↑G.domain) (hS : IsClopen S)
    (hred : Reduces (G.restrict S) (a ⊕ b)) :
    ∃ Sa Sb : Set ↑G.domain, Sa ⊆ S ∧ Sb ⊆ S ∧ IsClopen Sa ∧ IsClopen Sb ∧
      Disjoint Sa Sb ∧ Sa ∪ Sb = S ∧
      Reduces (G.restrict Sa) a ∧ Reduces (G.restrict Sb) b := by
  -- Apply `reduces_gl_split` to obtain the clopen partition `P` and the reductions.
  obtain ⟨P, hP⟩ := reduces_gl_split (G.restrict S) (fun k => if k = 0 then a else if k = 1 then b else ScatFun.empty) (by
  convert hred using 1;
  exact congr_arg _ ( funext fun k => by rcases k with ( _ | _ | k ) <;> rfl ));
  obtain ⟨Q, hQ⟩ := clopen_partition_restrict_transport G S hS P hP.left hP.right.left hP.right.right.left;
  refine ⟨ Q 0, Q 1, hQ.1 0, hQ.1 1, hQ.2.1 0, hQ.2.1 1, hQ.2.2.1 0 1 ( by decide ), ?_, ?_, ?_ ⟩;
  · have hQ_empty : ∀ k ≥ 2, P k = ∅ := by
      intros k hk
      have h_empty : Reduces ((G.restrict S).restrict (P k)) empty := by
        grind;
      have := domain_isEmpty_of_reduces_empty _ h_empty;
      simp_all +decide [ Set.ext_iff, ScatFun.restrict ];
    simp_all +decide [ Set.ext_iff ];
    grind;
  · exact hQ.2.2.2.2.1 0 |> fun h => h.trans ( hP.2.2.2 0 ) |> fun h => by simpa using h;
  · exact hP.2.2.2 1 |> fun h => hQ.2.2.2.2.1 1 |> fun h' => h'.trans h |> fun h'' => by aesop;

/-
**Shrinking clopen neighbourhoods** isolating the limit `y 0` of an injective sequence
`(y n)` with `y (n+1) → y 0`.  Each `B n` is a clopen neighbourhood of `y n` avoiding `y 0`
(for `n > 0`), and the tail `(B (n+1))` converges to `y 0`.
-/
lemma exists_shrinking_clopen (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0))) :
    ∃ B : ℕ → Set Baire,
      (∀ n, IsClopen (B n)) ∧ (∀ n, y n ∈ B n) ∧ (∀ n, 0 < n → y 0 ∉ B n) ∧
      SetsConvergeTo (fun n => B (n + 1)) (y 0) := by
  -- Define p n as the least coordinate where y n and y 0 differ.
  have hp : ∀ n > 0, ∃ k, y n k ≠ y 0 k := by
    exact fun n hn => Function.ne_iff.mp ( hy_inj.ne hn.ne' );
  choose! p hp using hp; use fun n => { x : Baire | ∀ k ≤ p n, x k = y n k } ; simp_all +decide [ IsClopen ] ;
  refine ⟨ ?_, ?_, ?_ ⟩;
  · intro n
    have h_closed : IsClosed {x : Baire | ∀ k ≤ p n, x k = y n k} := by
      simp +decide only [setOf_forall];
      exact isClosed_iInter fun i => isClosed_iInter fun hi => isClosed_eq ( continuous_apply i ) continuous_const
    have h_open : IsOpen {x : Baire | ∀ k ≤ p n, x k = y n k} := by
      refine isOpen_pi_iff.mpr ?_;
      intro f hf; use Finset.Iic ( p n ), fun k => { x | x = y n k } ; aesop;
    exact ⟨h_closed, h_open⟩;
  · exact fun n hn => ⟨ p n, le_rfl, Ne.symm ( hp n hn ) ⟩;
  · intro U hU hyU;
    -- Since $U$ is open and contains $y 0$, there exists $m$ such that the cylinder of $y 0$ of length $m$ is contained in $U$.
    obtain ⟨m, hm⟩ : ∃ m, ∀ x, (∀ k < m, x k = y 0 k) → x ∈ U := by
      rw [ isOpen_pi_iff ] at hU;
      obtain ⟨ I, u, hu₁, hu₂ ⟩ := hU _ hyU;
      use I.sup id + 1;
      intro x hx; exact hu₂ fun i hi => by have := hx i ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hi ) ) ; aesop;
    -- Since $y (n + 1) \to y 0$, there exists $N$ such that for all $n \geq N$, $y (n + 1)$ agrees with $y 0$ on all coordinates less than $m$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ k < m, y (n + 1) k = y 0 k := by
      have h_conv : ∀ k < m, ∃ N, ∀ n ≥ N, y (n + 1) k = y 0 k := by
        intro k hk; have := hconv; simp_all +decide [ tendsto_pi_nhds ] ;
      choose! N hN using h_conv; exact ⟨ Finset.sup ( Finset.range m ) N, fun n hn k hk => hN k hk n ( le_trans ( Finset.le_sup ( f := N ) ( Finset.mem_range.mpr hk ) ) hn ) ⟩ ;
    use N + m; intros n hn; intro x hx; exact hm x fun k hk => by
      grind +qlia;

/-
**Distinguished value passes to clopen subsets.**  If, on the top CB-level `lam` of
`G.restrict A`, the function is constant `= yn`, and `T ⊆ A` is a clopen subset, then the same
holds for `G.restrict T`.
-/
lemma cbLevel_distinguished_subset (G : ScatFun) (A T : Set ↑G.domain)
    (hTA : T ⊆ A) (hA : IsClopen A) (hT : IsClopen T) (lam : Ordinal.{0}) (yn : Baire)
    (hdist : ∀ x ∈ CBLevel (G.restrict A).func lam, (G.restrict A).func x = yn) :
    ∀ x ∈ CBLevel (G.restrict T).func lam, (G.restrict T).func x = yn := by
  intro x hx;
  -- By `cbLevel_block_iff` for `G` and `A`, the point `z := (G.restrictEquiv A x : ↑G.domain)` satisfies `z ∈ CBLevel G.func lam`.
  obtain ⟨z, hz⟩ : ∃ z : G.domain, z ∈ CBLevel G.func lam ∧ z ∈ A ∧ (G.restrictEquiv T x : G.domain) = z := by
    have := cbLevel_block_iff G T hT.isOpen lam x; aesop;
  obtain ⟨z', hz'⟩ : ∃ z' : ↥(G.restrict A).domain, (G.restrictEquiv A z' : G.domain) = z := by
    simp +decide only [restrict, coe_setOf, mem_setOf_eq, restrictEquiv, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Subtype.exists];
    grind;
  convert hdist z' _ using 1;
  · convert congr_arg ( fun x : G.domain => G.func x ) ( hz.2.2.trans hz'.symm ) using 1;
  · convert cbLevel_block_iff G A hA.isOpen lam z' |>.2 _;
    grind

/-
**Corestricting away the distinguished value drops the rank.**  If `G.restrict T` has all
of its top CB-level `lam` mapping to `yn`, and `V` is a clopen codomain set avoiding `yn`, then
the corestriction of `G.restrict T` to `V` has CB-rank `≤ lam` (its top level is removed).
-/
lemma cbRank_corestrict_avoid_le (G : ScatFun) (T : Set ↑G.domain) (hT : IsClopen T)
    (lam : Ordinal.{0}) (yn : Baire)
    (hdist : ∀ x ∈ CBLevel (G.restrict T).func lam, (G.restrict T).func x = yn)
    (V : Set Baire) (hV : IsClopen V) (hyn : yn ∉ V) :
    CBRank (G.restrict (T ∩ {a : ↑G.domain | G.func a ∈ V})).func ≤ lam := by
  -- Let $W := T \cap \{a : ↑G.domain | G.func a ∈ V\}$, which is clopen.
  set W := T ∩ {a : ↑G.domain | G.func a ∈ V} with hW_def
  have hW_clopen : IsClopen W := by
    exact hT.inter ( hV.preimage G.hCont );
  refine csInf_le' ?_;
  -- To show emptiness, suppose `x ∈ CBLevel (G.restrict W).func lam`. By `cbLevel_block_iff G W hW.isOpen`, the point `z := (G.restrictEquiv W x : ↑G.domain)` lies in `CBLevel G.func lam` and `z ∈ W`, so `z ∈ T` and `G.func z ∈ V`.
  have hW_empty : ∀ x : ↑(G.restrict W).domain, x ∈ CBLevel (G.restrict W).func lam → False := by
    intros x hx
    obtain ⟨z, hz⟩ : ∃ z : ↑G.domain, z ∈ CBLevel G.func lam ∧ z ∈ W ∧ (G.restrict W).func x = G.func z := by
      have := cbLevel_block_iff G W hW_clopen.isOpen lam x;
      exact ⟨ _, this.mp hx, by simp, rfl ⟩;
    -- Since `z ∈ T`, form `z' : ↑(G.restrict T).domain := ⟨z, _⟩`; by `cbLevel_block_iff G T hT.isOpen` (reverse direction, using `(G.restrictEquiv T z').val = z ∈ CBLevel G.func lam`), `z' ∈ CBLevel (G.restrict T).func lam`.
    obtain ⟨z', hz'⟩ : ∃ z' : ↑(G.restrict T).domain, (G.restrictEquiv T z').val = z ∧ z' ∈ CBLevel (G.restrict T).func lam := by
      obtain ⟨z', hz'⟩ : ∃ z' : ↑(G.restrict T).domain, (G.restrictEquiv T z').val = z := by
        exact ⟨ ( G.restrictEquiv T ).symm ⟨ z, hz.2.1.1 ⟩, by simp +decide ⟩;
      have := cbLevel_block_iff G T hT.isOpen lam z';
      grind;
    have := hdist z' hz'.2; simp_all +decide [ ScatFun.restrict ] ;
  refine Set.Subset.antisymm ?_ ?_ <;> intro x hx <;> simp_all +decide [ CBLevel ]

/-
CB-rank of a restriction to a countable clopen union is `≤ lam` when every piece is.
-/
lemma cbRank_restrict_iUnion_le (G : ScatFun) (R : ℕ → Set ↑G.domain)
    (hR : ∀ i, IsClopen (R i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (R i) (R j)) (lam : Ordinal.{0})
    (hRr : ∀ i, CBRank (G.restrict (R i)).func ≤ lam) :
    CBRank (G.restrict (⋃ i, R i)).func ≤ lam := by
  -- Apply the rank monotonicity lemma to each restriction.
  have h_monotone : ∀ i, CBRank ((G.restrict (⋃ i, R i)).restrict {w | (G.restrictEquiv (⋃ i, R i) w : ↑G.domain) ∈ R i}).func ≤ lam := by
    intro i
    have h_monotone : CBRank ((G.restrict (⋃ i, R i)).restrict {w | (G.restrictEquiv (⋃ i, R i) w : ↑G.domain) ∈ R i}).func ≤ CBRank (G.restrict (R i)).func := by
      apply_rules [ ContinuouslyReduces.rank_monotone ];
      · exact ((G.restrict (⋃ i, R i)).restrict {w | ↑((G.restrictEquiv (⋃ i, R i)) w) ∈ R i}).hScat;
      · grind [hScat];
      · refine ⟨ ?_, ?_, ?_, ?_ ⟩;
        use fun x => ⟨ x.val, by
          convert x.2 using 1;
          simp +decide only [restrict, coe_setOf, mem_setOf_eq, mem_iUnion];
          ext; aesop; ⟩
        all_goals generalize_proofs at *;
        fun_prop;
        exact fun x => x;
        exact ⟨ continuousOn_id, fun x => rfl ⟩
    exact le_trans h_monotone (hRr i);
  convert ciSup_le h_monotone using 1;
  apply cbRank_eq_iSup_restrict;
  constructor;
  · intro i;
    exact IsClopen.preimage ( hR i ) ( by continuity );
  · simp_all +decide [ Set.ext_iff, Set.disjoint_left ];
    exact ⟨ fun i j hij a ha => hdisj i j hij a _, fun a ha => by rcases Set.mem_iUnion.mp ( Subtype.mem ( G.restrictEquiv ( ⋃ i, R i ) ⟨ a, ha ⟩ ) ) with ⟨ i, hi ⟩ ; exact ⟨ i, hi ⟩ ⟩

/-
CB-rank of a restriction to a binary disjoint clopen union is `≤ lam` when both pieces are.
-/
lemma cbRank_restrict_union_le (G : ScatFun) (P Q : Set ↑G.domain)
    (hP : IsClopen P) (hQ : IsClopen Q) (hPQ : Disjoint P Q) (lam : Ordinal.{0})
    (hPr : CBRank (G.restrict P).func ≤ lam) (hQr : CBRank (G.restrict Q).func ≤ lam) :
    CBRank (G.restrict (P ∪ Q)).func ≤ lam := by
  by_contra h_contra;
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Set ↑G.domain, (∀ k, IsClopen (R k)) ∧ (∀ k l, k ≠ l → Disjoint (R k) (R l)) ∧ (⋃ k, R k = P ∪ Q) ∧ (∀ k, CBRank (G.restrict (R k)).func ≤ lam) := by
    refine ⟨ fun k => if k = 0 then P else if k = 1 then Q else ∅, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Set.disjoint_left ];
    · intro k; split_ifs <;> simp_all +decide [ IsClopen ] ;
    · grind;
    · ext x; simp [Set.mem_iUnion];
      exact ⟨ fun ⟨ i, hi ⟩ => by rcases i with ( _ | _ | i ) <;> tauto, fun hx => hx.elim ( fun hx => ⟨ 0, hx ⟩ ) fun hx => ⟨ 1, hx ⟩ ⟩;
    · grind [cbRank_restrict_eq, CBRank_le_of_CBLevel_empty, func.hcongr_1];
  convert ScatFun.cbRank_restrict_iUnion_le G R hR.1 hR.2.1 lam hR.2.2.2 using 1;
  rw [ hR.2.2.1 ] ; tauto;

/-
**Leftover block has CB-rank `≤ lam`.**  A block `An = Amin ∪ Amax` (disjoint clopen) with
`Amax ≤ maxFun` and `Amin` distinguished `= yn` on its top CB-level, minus the piece of `Amin`
landing in a clopen neighbourhood `Bn ∈ yn`, has CB-rank `≤ lam`.
-/
lemma leftover_block_rank_le (F : ScatFun) (An Amin Amax : Set ↑F.domain)
    (hpart : Amin ∪ Amax = An) (hdisjmm : Disjoint Amin Amax)
    (hAmincl : IsClopen Amin) (hAmaxcl : IsClopen Amax)
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (yn : Baire)
    (hAmax_red : Reduces (F.restrict Amax) (maxFun lam hlam_lt))
    (hAmin_dist : ∀ x ∈ CBLevel (F.restrict Amin).func lam, (F.restrict Amin).func x = yn)
    (Bn : Set Baire) (hBncl : IsClopen Bn) (hyn : yn ∈ Bn) :
    CBRank (F.restrict (An \ (Amin ∩ {a : ↑F.domain | F.func a ∈ Bn}))).func ≤ lam := by
  have h_union : An \ (Amin ∩ {a | F.func a ∈ Bn}) = Amax ∪ (Amin ∩ {a | F.func a ∈ Bnᶜ}) := by
    simp +decide only [← hpart, mem_compl_iff, Set.ext_iff, mem_diff, mem_union, mem_inter_iff, mem_setOf_eq, not_and, Subtype.forall];
    grind;
  convert cbRank_restrict_union_le F Amax ( Amin ∩ { a | F.func a ∈ Bnᶜ } ) hAmaxcl _ _ lam _ _ using 1;
  · rw [h_union];
  · exact hAmincl.inter ( hBncl.compl.preimage F.hCont );
  · exact hdisjmm.symm.mono_right ( Set.inter_subset_left );
  · convert ContinuouslyReduces.rank_monotone _ _ hAmax_red using 1;
    · exact Eq.symm ( maxFun_cbRank_eq lam hlam_lt );
    · exact (F.restrict Amax).hScat;
    · exact (maxFun lam hlam_lt).hScat;
  · convert ScatFun.cbRank_corestrict_avoid_le F Amin hAmincl lam yn hAmin_dist Bnᶜ hBncl.compl (by
    exact fun h => h hyn) using 1

/-
**Vertical ray has CB-rank `≤ lam`.**  With the re-partition's vertical block
`Atil0 = Set.univ \ ⋃ E` (where `E i ⊆ A i`, `E 0 = ∅`, and each block-complement `A k \ E k`
(`k > 0`) has CB-rank `≤ lam`, while `A 0` is distinguished `= y0`), every ray of `Atil0` at
`y0` has CB-rank `≤ lam`.
-/
lemma ray_vertical_rank_le (F : ScatFun) (A E : ℕ → Set ↑F.domain)
    (hA : F.IsDisjointUnion A) (hEcl : ∀ i, IsClopen (E i)) (hEsub : ∀ i, E i ⊆ A i)
    (hE0 : E 0 = ∅) (lam : Ordinal.{0}) (y0 : Baire)
    (hleft : ∀ k, 0 < k → CBRank (F.restrict (A k \ E k)).func ≤ lam)
    (hdist0 : ∀ x ∈ CBLevel (F.restrict (A 0)).func lam, (F.restrict (A 0)).func x = y0)
    (j : ℕ) :
    CBRank (F.restrict ((Set.univ \ ⋃ n, E n) ∩
      {a : ↑F.domain | F.func a ∈ RaySet Set.univ y0 j})).func ≤ lam := by
  obtain ⟨haclopen, hadisj, hamax⟩ := hA;
  rw [ setdiff_iUnion_eq_iUnion_diff A E hamax hadisj hEsub ];
  rw [ Set.iUnion_inter ];
  apply cbRank_restrict_iUnion_le F (fun k => (A k \ E k) ∩ {a : F.domain | F.func a ∈ RaySet Set.univ y0 j}) (fun k => IsClopen.inter (IsClopen.diff (haclopen k) (hEcl k)) (IsClopen.preimage (isClopen_raySet y0 j) F.hCont)) (fun k l hkl => ?_) lam (fun k => ?_);
  · exact Set.disjoint_left.mpr fun x hxk hxl => Set.disjoint_left.mp ( hadisj k l hkl ) ( hxk.1.1 ) ( hxl.1.1 );
  · by_cases hk : 0 < k <;> simp_all +decide;
    · refine le_trans ?_ ( hleft k hk );
      apply restrict_reduces_of_subset F (Set.inter_subset_left) |> fun h => h.rank_monotone;
      · exact F.restrict _ |>.hScat;
      · exact (F.restrict (A k \ E k)).hScat;
    · convert ScatFun.cbRank_corestrict_avoid_le F ( A 0 ) ( haclopen 0 ) lam y0 _ ( RaySet Set.univ y0 j ) ( isClopen_raySet y0 j ) _ using 1;
      · rw [ hk, hE0, Set.diff_empty ];
      · exact fun x hx => hdist0 _ _ hx;
      · unfold RaySet; aesop;

/-
**First inequality of Lemma `Diagonalforlambda+1`** (`5_precise_struct_memo.tex:356`):
`f ≤ ⋁(Maximalfct{λ} ∣ Minimalfct{λ+1})`, i.e. the wedge is an upper bound of `f`.

This is the `wedge_upper_bound` direction.  It cannot be applied to the given partition `A`
directly (the `SetsConvergeTo` hypothesis fails), so it requires a *finite re-partition* `Ã`:
for each `n > 0`, peel from `A n` the clopen sub-piece whose `F`-image lands in a shrinking
clopen neighbourhood `B (k n)` of `y 0` and reduces to `Minimalfct{λ+1}` (the `minFun`-column
of the gluing `minFun ⊕ maxFun`, extracted via `gluingFun_upper_bound_forward` +
`clopen_partition_restrict_transport`), leaving an `A⁰_n` piece of CB-rank `≤ lam`.  Then
`Ã 0 = A 0 ∪ ⋃_{n>0} A⁰_n` (rank `≤ lam` rays, via `reduces_maxFun_of_rank_le`) and
`Ã (n+1) = A¹_n` (reduces to `minFun`, images `⊆ B (k n) → {y 0}`), and `wedge_upper_bound`
applies.  (This direction needs neither the exact CB-rank `λ+1` of each block nor the
`f_0 ≡ pgl Maximalfct{λ}` equivalence — only that each block ≤ `minFun ⊕ maxFun`, that block `0`
is distinguished `= y 0` on its top level, and the convergence — so `hrank` and `h0` are dropped
from this half's hypotheses.) -/
lemma diagonal_f_le_wedge (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hdistinguished : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = y n)
    (hpos : ∀ n, 0 < n →
      Reduces (F.restrict (A n)) (minFun lam hlam_lt ⊕ maxFun lam hlam_lt))
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0))) :
    Reduces F (wedge (fun _ : Fin 1 => maxFun lam hlam_lt) (minFun lam hlam_lt)) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set Baire, (∀ n, IsClopen (B n)) ∧ (∀ n, y n ∈ B n) ∧ (∀ n, 0 < n → y 0 ∉ B n) ∧ SetsConvergeTo (fun n => B (n + 1)) (y 0) := by
    exact exists_shrinking_clopen y hy_inj hconv;
  obtain ⟨Amin, Amax, hAmin_sub, hAmax_sub, hAmin_cl, hAmax_cl, hmm_disj, hmm_union, hAmin_red, hAmax_red⟩ : ∃ Amin Amax : ℕ → Set ↑F.domain, (∀ n, Amin n ⊆ A n) ∧ (∀ n, Amax n ⊆ A n) ∧ (∀ n, IsClopen (Amin n)) ∧ (∀ n, IsClopen (Amax n)) ∧ (∀ n, Disjoint (Amin n) (Amax n)) ∧ (∀ n, Amin n ∪ Amax n = A n) ∧ (∀ n, 0 < n → Reduces (F.restrict (Amin n)) (minFun lam hlam_lt)) ∧ (∀ n, 0 < n → Reduces (F.restrict (Amax n)) (maxFun lam hlam_lt)) := by
    choose! Amin Amax hAmin_sub hAmax_sub hAmin_cl hAmax_cl hmm_disj hmm_union hAmin_red hAmax_red using fun n hn => reduces_glBin_split F (minFun lam hlam_lt) (maxFun lam hlam_lt) (A n) (hdu.1 n) (hpos n hn);
    refine ⟨ fun n => if 0 < n then Amin n else ∅, fun n => if 0 < n then Amax n else A n, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ * ];
    grind;
    · grind;
    · intro n; split_ifs <;> simp_all +decide [ IsClopen ] ;
    · intro n; split_ifs <;> simp_all +decide [ IsClopen ] ;
      exact ⟨ hdu.1 0 |>.1, hdu.1 0 |>.2 ⟩;
    · aesop;
    · grind +revert;
  set E : ℕ → Set ↑F.domain := fun n => if 0 < n then Amin n ∩ {a : ↑F.domain | F.func a ∈ B n} else ∅
  set Atil : ℕ → Set ↑F.domain := fun i => if i = 0 then Set.univ \ ⋃ n, E n else E i;
  apply ScatFun.wedge_upper_bound F (fun _ : Fin 1 => maxFun lam hlam_lt) (ScatFun.minFun lam hlam_lt) (y 0) Atil;
  · refine ⟨ ?_, ?_, ?_ ⟩;
    · intro i; by_cases hi : i = 0 <;> simp +decide [ hi, Atil ] ;
      · have hEcl : ∀ n, IsClopen (E n) := by
          intro n; by_cases hn : 0 < n <;> simp +decide [ hn, E ] ;
          · exact IsClopen.inter ( hAmin_cl n ) ( IsClopen.preimage ( hB.1 n ) F.hCont );
          · exact isClopen_empty;
        have hEcl : IsClopen (⋃ n, E n) := by
          apply isClopen_iUnion_sub_partition;
          exact fun n => hdu.1 n;
          · exact hdu.2.2;
          · exact fun i j hij => hdu.2.1 i j hij;
          · exact hEcl;
          · grind;
        exact ⟨ isClosed_univ.sdiff hEcl.2, isOpen_univ.sdiff hEcl.1 ⟩;
      · simp +zetaDelta at *;
        split_ifs;
        · exact IsClopen.inter ( hAmin_cl i ) ( IsClopen.preimage ( hB.1 i ) F.hCont );
        · exact isClopen_empty;
    · intro i j hij; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp +decide [ hi, hj, Atil ] ;
      · bv_omega;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.2 <| Set.mem_iUnion_of_mem j hx₂;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2 <| Set.mem_iUnion_of_mem i hx₁;
      · simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ Set.disjoint_left ];
        intro a ha ha' ha'' ha''' ha''''; have := hdu.2.1 i j hij; simp_all +decide [ Set.disjoint_left ] ;
        exact this a ha ( hAmin_sub i ha' ) ( hAmin_sub j ha''' );
    · ext x; simp [Atil];
      by_cases hx : x ∈ ⋃ n, E n;
      · obtain ⟨ n, hn ⟩ := Set.mem_iUnion.mp hx; use n; aesop;
      · exact ⟨ 0, by simpa using hx ⟩;
  · intro i hi j;
    have h_leftover_block_rank_le : CBRank (F.restrict (Atil 0 ∩ {a : ↑F.domain | F.func a ∈ RaySet Set.univ (y 0) j})).func ≤ lam := by
      apply ray_vertical_rank_le;
      exact hdu;
      · simp +zetaDelta at *;
        intro n; split_ifs <;> simp_all +decide [ IsClopen ] ;
        exact ⟨ IsClosed.inter ( hAmin_cl n |>.1 ) ( IsClosed.preimage F.hCont ( hB.1 n |>.1 ) ), IsOpen.inter ( hAmin_cl n |>.2 ) ( IsOpen.preimage F.hCont ( hB.1 n |>.2 ) ) ⟩;
      · grind;
      · exact image_val_inj.mp rfl;
      · intro k hk_pos
        have hAmin_dist : ∀ x ∈ CBLevel (F.restrict (Amin k)).func lam, (F.restrict (Amin k)).func x = y k := by
          apply cbLevel_distinguished_subset F (A k) (Amin k) (hAmin_sub k) (hdu.1 k) (hAmin_cl k) lam (y k) (hdistinguished k);
        convert leftover_block_rank_le F ( A k ) ( Amin k ) ( Amax k ) ( hmm_union k ) ( hmm_disj k ) ( hAmin_cl k ) ( hAmax_cl k ) lam hlam_lt ( y k ) ( hAmax_red k hk_pos ) hAmin_dist ( B k ) ( hB.1 k ) ( hB.2.1 k ) using 1;
        lia;
      · exact hdistinguished 0;
    use 1;
    interval_cases i ; simp_all +decide [ ScatFun.rayOn ];
    convert ScatFun.reduces_glList_one _ _ ( ScatFun.reduces_maxFun_of_rank_le _ _ _ h_leftover_block_rank_le ) using 1;
  · intro i hi
    use 1
    simp only [List.replicate_one, Atil, E];
    split_ifs <;> simp_all +decide [ Nat.succ_le_iff ];
    have h_reduces : Reduces (F.restrict (Amin i ∩ {a | F.func a ∈ B i})) (F.restrict (Amin i)) := by
      apply restrict_reduces_of_subset;
      exact Set.inter_subset_left;
    exact ScatFun.reduces_glList_one _ _ ( hAmin_red i ‹_› |> fun h => h_reduces.trans h );
  · intro U hU hyU; rcases hB.2.2.2 U hU hyU with ⟨ m, hm ⟩ ; use m + 1; intro i hi; simp_all +decide [ Set.subset_def ] ;
    intro x y hy hx; rcases i with ( _ | i ) <;> simp_all +decide [ ScatFun.restrict ] ;
    grind +extAll

/-
**Heart of the vertical clause** (single-domain form).  For a scattered `ScatFun` `g` of
CB-rank `lam+1`, constant `= y0` on its top CB-level, and equivalent to `succMaxFun lam`, there
is a center `x0` with value `y0`, and for every open Baire neighbourhood `V0` of `x0.val` and
open Baire neighbourhood `W` of `y0`, the maximum `maxFun lam` reduces into `g` with all
domain-points inside `V0`, all values inside `W`, and cocenter separation `y0 ∉ closure`.
The construction takes a deep ray `(0)ʲ(1)·` of `g ≡ succMaxFun`; deep rays are close to the
base, hence map (through the equivalence) near the center `x0` and to values near `y0`, while
rigidity of the cocenter (`rigidityOfCocenter_separation`) supplies the separation.
-/
lemma maxFun_reduces_centered_near_center (g : ScatFun) (lam : Ordinal.{0})
    (hlam_lt : lam < omega1) (y0 : Baire)
    (hrank : CBRank g.func = lam + 1)
    (hdist : ∀ x ∈ CBLevel g.func lam, g.func x = y0)
    (h0 : Equiv g (succMaxFun lam hlam_lt)) :
    ∃ x0 : ↑g.domain, g.func x0 = y0 ∧
      ∀ (V0 W : Set Baire), IsOpen V0 → (x0 : Baire) ∈ V0 → IsOpen W → y0 ∈ W →
        ∃ (σ : ↑(maxFun lam hlam_lt).domain → ↑g.domain) (τ : Baire → Baire),
          Continuous σ ∧ ContinuousOn τ (Set.range fun z => g.func (σ z)) ∧
          (∀ z, (maxFun lam hlam_lt).func z = τ (g.func (σ z))) ∧
          (∀ z, ((σ z : ↑g.domain) : Baire) ∈ V0) ∧
          (∀ z, g.func (σ z) ∈ W) ∧
          y0 ∉ closure (Set.range fun z => g.func (σ z)) := by
  obtain ⟨σ2, hσ2c, τ2, hτ2c, heq2⟩ : ∃ σ2 : ↑(succMaxFun lam hlam_lt).domain → ↑g.domain, ∃ τ2 : Baire → Baire, Continuous σ2 ∧ ContinuousOn τ2 (Set.range fun a => g.func (σ2 a)) ∧ (∀ a, (succMaxFun lam hlam_lt).func a = τ2 (g.func (σ2 a))) := by
    obtain ⟨ σ2, hσ2c, τ2, hτ2c, heq2 ⟩ := h0.2; exact ⟨ σ2, τ2, hσ2c, hτ2c, heq2 ⟩ ;
  refine ⟨ σ2 ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩, ?_, ?_ ⟩;
  · have := center_in_CBLevel g.func (σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) (centerInvariance_equiv (succMaxFun_base_isCenter lam hlam_lt) ⟨h0.2, h0.1⟩ τ2 (by
    exact hτ2c) heq2) lam (by
    exact CBLevel_nonempty_below_rank g.func g.hScat lam ( by rw [ hrank ] ; exact lt_add_one lam ));
    exact hdist _ this;
  · intro V0 W hV0 hV0' hW hy0W
    obtain ⟨d, hd⟩ : ∃ d, ∀ a : ↑(succMaxFun lam hlam_lt).domain, a ∈ nbhd' (succMaxFun lam hlam_lt).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ d → (σ2 a : Baire) ∈ V0 ∧ g.func (σ2 a) ∈ W := by
      have h_cont : Continuous (fun a : ↑(succMaxFun lam hlam_lt).domain => (σ2 a : Baire)) ∧ Continuous (fun a : ↑(succMaxFun lam hlam_lt).domain => g.func (σ2 a)) := by
        exact ⟨ continuous_subtype_val.comp τ2, g.hCont.comp τ2 ⟩;
      obtain ⟨U, hU⟩ : ∃ U : Set ↑(succMaxFun lam hlam_lt).domain, IsOpen U ∧ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ∈ U ∧ ∀ a ∈ U, (σ2 a : Baire) ∈ V0 ∧ g.func (σ2 a) ∈ W := by
        have h_cont : Continuous (fun a : ↑(succMaxFun lam hlam_lt).domain => (σ2 a : Baire)) ∧ Continuous (fun a : ↑(succMaxFun lam hlam_lt).domain => g.func (σ2 a)) ∧ (σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ : Baire) ∈ V0 ∧ g.func (σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) ∈ W := by
          have h_center : IsCenterFor g.func (σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) := by
            apply centerInvariance_equiv (succMaxFun_base_isCenter lam hlam_lt) ⟨h0.2, h0.1⟩ τ2 hτ2c heq2;
          have h_center_in_CBLevel : σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ∈ CBLevel g.func lam := by
            apply center_in_CBLevel g.func (σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) h_center lam (CBLevel_nonempty_below_rank g.func g.hScat lam (by rw[hrank]; exact lt_add_one lam));
          grind;
        exact ⟨ { a : ↑ ( succMaxFun lam hlam_lt ).domain | ( σ2 a : Baire ) ∈ V0 ∧ g.func ( σ2 a ) ∈ W }, IsOpen.inter ( h_cont.1.isOpen_preimage _ hV0 ) ( h_cont.2.1.isOpen_preimage _ hW ), h_cont.2.2, fun a ha => ha ⟩;
      obtain ⟨ d, hd ⟩ := nbhd_basis' ( succMaxFun lam hlam_lt ).domain ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩ U hU.1 hU.2.1;
      exact ⟨ d, fun a ha => hU.2.2 a ( hd ha ) ⟩;
    obtain ⟨σB, τB, hσBc, hτBc, heqB, hσBval, hσBfunc⟩ := pgl_block_reduction_explicit (fun _ => maxFun lam hlam_lt) d;
    refine ⟨ fun z => σ2 ( σB z ), fun w => τB ( hσ2c w ), ?_, ?_, ?_, ?_, ?_ ⟩;
    · exact τ2.comp hσBc;
    · refine ContinuousOn.comp hτBc ?_ ?_;
      · refine' hτ2c.mono _;
        exact Set.range_subset_iff.mpr fun z => ⟨ σB z, rfl ⟩;
      · intro x hx;
        obtain ⟨ z, rfl ⟩ := hx;
        use z;
        convert heq2 ( σB z ) using 1;
    · grind [succMaxFun_eq];
    · intro z
      apply (hd (σB z) (by
      intro i hi; simp +decide [ hσBval, prependZerosOne ] ;
      exact if_pos ( Finset.mem_range.mp hi ))).left;
    · refine' ⟨ fun z => hd _ _ |>.2, _ ⟩;
      · simp +decide [ nbhd', hσBval ];
        exact fun i hi => if_pos hi;
      · intro hy0_closure
        obtain ⟨z_i, hz_i⟩ : ∃ z_i : ℕ → ↑(maxFun lam hlam_lt).domain, Filter.Tendsto (fun i => g.func (σ2 (σB (z_i i)))) Filter.atTop (nhds y0) := by
          rw [ mem_closure_iff_seq_limit ] at hy0_closure;
          obtain ⟨ x, hx₁, hx₂ ⟩ := hy0_closure; choose z hz using hx₁; exact ⟨ z, hx₂.congr fun n => hz n ▸ rfl ⟩ ;
        have h_contra : Filter.Tendsto (fun i => (succMaxFun lam hlam_lt).func (σB (z_i i))) Filter.atTop (nhds (hσ2c y0)) := by
          convert hτ2c.continuousWithinAt _ |> fun h => h.tendsto.comp ( show Filter.Tendsto ( fun i => g.func ( σ2 ( σB ( z_i i ) ) ) ) Filter.atTop ( nhdsWithin y0 ( range fun a => g.func ( σ2 a ) ) ) from ?_ ) using 1;
          · exact funext fun i => heq2 _;
          · use ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩;
            convert hdist _ _;
            apply center_in_CBLevel;
            · apply centerInvariance_equiv (succMaxFun_base_isCenter lam hlam_lt) ⟨h0.2, h0.1⟩ τ2 hτ2c heq2;
            · exact CBLevel_nonempty_below_rank g.func g.hScat lam ( by rw [ hrank ] ; exact lt_add_one lam );
          · rw [ tendsto_nhdsWithin_iff ];
            exact ⟨ hz_i, Filter.Eventually.of_forall fun n => ⟨ σB ( z_i n ), rfl ⟩ ⟩;
        have hty : hσ2c y0 = zeroStream :=
          succMaxFun_tau_cocenter_eq g lam hlam_lt y0 hrank hdist h0 σ2 τ2 hσ2c hτ2c heq2
        have hcoord := (tendsto_pi_nhds.mp h_contra) d
        have hval1 : ∀ i, (succMaxFun lam hlam_lt).func (σB (z_i i)) d = 1 := by
          intro i
          have h : (succMaxFun lam hlam_lt).func (σB (z_i i))
              = prependZerosOne d ((maxFun lam hlam_lt).func (z_i i)) := hσBfunc (z_i i)
          rw [h]; exact prependZerosOne_at_i d _
        have hcoord2 : Filter.Tendsto (fun _ : ℕ => (1 : ℕ)) Filter.atTop (nhds (hσ2c y0 d)) :=
          hcoord.congr hval1
        have huniq := tendsto_nhds_unique tendsto_const_nhds hcoord2
        rw [hty] at huniq
        exact absurd huniq (by simp [zeroStream])

/-
**Vertical clause + anchor of `wedge_lower_bound`** for the diagonal case.  There is an
anchor point `x0 ∈ (F.coRestrict U).domain` with value `y 0` (a center of `f_0`), and for every
open neighbourhood `U'` of `x0` the maximum `maxFun lam` reduces into `F.coRestrict U` with
domain-image inside `U'` and cocenter separation `y 0 ∉ closure`.
-/
lemma diagonal_wedge_vertical (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y : ℕ → Baire)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdistinguished : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = y n)
    (h0 : Equiv (F.restrict (A 0)) (succMaxFun lam hlam_lt))
    (U : Set Baire) (hU : IsClopen U) (hyU : y 0 ∈ U) :
    ∃ x0 : ↑(F.coRestrict U).domain, (F.coRestrict U).func x0 = y 0 ∧
      ∀ U' : Set ↑(F.coRestrict U).domain, IsOpen U' → x0 ∈ U' →
        ∃ (σ : ↑(maxFun lam hlam_lt).domain → ↑(F.coRestrict U).domain) (τ : Baire → Baire),
          Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict U).func (σ z)) ∧
          (∀ z, (maxFun lam hlam_lt).func z = τ ((F.coRestrict U).func (σ z))) ∧
          (∀ z, σ z ∈ U') ∧
          y 0 ∉ closure (Set.range fun z => (F.coRestrict U).func (σ z)) := by
  obtain ⟨x0f, hx0fval, hmain⟩ := maxFun_reduces_centered_near_center (F.restrict (A 0)) lam hlam_lt (y 0) (hrank 0) (hdistinguished 0) h0;
  refine ⟨ ⟨ x0f.val, ⟨ by
    exact x0f.2.1, by
    grind [restrict_func_eq] ⟩ ⟩, ?_, ?_ ⟩
  all_goals generalize_proofs at *;
  · convert hx0fval using 1;
  · intro U' hU' hx0fU'
    obtain ⟨V0, hV0open, hV0U'⟩ : ∃ V0 : Set Baire, IsOpen V0 ∧ U' = Subtype.val ⁻¹' V0 := by
      obtain ⟨ V0, hV0open, hV0U' ⟩ := hU';
      exact ⟨ V0, hV0open, hV0U'.symm ⟩
    generalize_proofs at *;
    obtain ⟨σ_f0, τ, hσ_f0c, hτc, hσ_f0eq, hσ_f0V0, hσ_f0U, hσ_f0sep⟩ := hmain V0 U hV0open (by
    exact hV0U'.subset hx0fU') hU.isOpen hyU
    generalize_proofs at *;
    obtain ⟨σ, hσc, hσval, hσeq⟩ := reduces_block_into_coRestrict F (A 0) U (maxFun lam hlam_lt) σ_f0 hσ_f0c hσ_f0U
    generalize_proofs at *;
    refine ⟨ σ, τ, hσc, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ * ]

/-- **Second inequality of Lemma `Diagonalforlambda+1`** (`5_precise_struct_memo.tex:356`):
`⋁(Maximalfct{λ} ∣ Minimalfct{λ+1}) ≤ f ↾ U` for every clopen neighbourhood `U` of `y 0`.
Proved via `ScatFun.wedge_lower_bound`. -/
lemma diagonal_wedge_le_restrict (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdistinguished : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = y n)
    (h0 : Equiv (F.restrict (A 0)) (succMaxFun lam hlam_lt))
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0)))
    (U : Set Baire) (hU : IsClopen U) (hyU : y 0 ∈ U) :
    Reduces (wedge (fun _ : Fin 1 => maxFun lam hlam_lt) (minFun lam hlam_lt))
      (F.coRestrict U) := by
  obtain ⟨x0, hx0val, hvert⟩ :=
    diagonal_wedge_vertical F A lam hlam_lt y hrank hdistinguished h0 U hU hyU
  refine wedge_lower_bound (F.coRestrict U) (fun _ : Fin 1 => maxFun lam hlam_lt)
    (minFun lam hlam_lt) (y 0) ⟨x0, hx0val⟩ (fun _ => x0) (fun _ => hx0val) ?_ ?_
  · intro i U' hU'open hx0U'
    exact hvert U' hU'open hx0U'
  · intro V hV hyV
    exact diagonal_wedge_diag_clause F A lam hlam_lt y hy_inj hrank hdistinguished hconv U hU hyU
      V hV hyV

/-- **Lemma `Diagonalforlambda+1`** (`5_precise_struct_memo.tex:356`). -/
theorem diagonal_for_lambda_plus_one (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    -- `(f_n)` are simple of CB-rank `λ+1` with pairwise distinct distinguished points `(y_n)`.
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdistinguished : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = y n)
    -- 1. `f_0 ≡ pgl Maximalfct{λ}`.
    (h0 : Equiv (F.restrict (A 0)) (succMaxFun lam hlam_lt))
    -- 2. `f_n ≤ Minimalfct{λ+1} ⊕ Maximalfct{λ}` for `n > 0`.
    (hpos : ∀ n, 0 < n →
      Reduces (F.restrict (A n)) (minFun lam hlam_lt ⊕ maxFun lam hlam_lt))
    -- 3. `(y_n)_{n>0}` converges to `y_0`.
    (hconv : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (y 0))) :
    ∀ U : Set Baire, IsClopen U → y 0 ∈ U →
      Reduces F (wedge (fun _ : Fin 1 => maxFun lam hlam_lt) (minFun lam hlam_lt)) ∧
        Reduces (wedge (fun _ : Fin 1 => maxFun lam hlam_lt) (minFun lam hlam_lt))
          (F.coRestrict U) := by
  refine fun U hU hyU => ⟨?_, ?_⟩
  · exact diagonal_f_le_wedge F A hdu lam hlam_lt y hy_inj hdistinguished hpos hconv
  · exact diagonal_wedge_le_restrict F A lam hlam_lt y hy_inj hrank hdistinguished h0
      hconv U hU hyU

end ScatFun

end