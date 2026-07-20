import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.Prop411
import WqoContinuousFunctions.ScatFun.RestrictReduces

/-!
# §4.3 — Theorem 4.12 machinery shared by the λ-limit and λ=1 cases

Extracted from `SimpleSuccessorOfLimit.lean`.  Case-A reduction, ray helpers, the
prefix-cylinder strengthening of local centeredness, and the diagonal pieces common to
both the limit and the `λ=1` arguments.
-/

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section


/-!
## Theorem 4.12 (`simplefunctionslambda+1damuddafuckaz`)

The minimal/maximal data are `k_{λ+1} = ScatFun.minFun lam`, `ℓ_λ = ScatFun.maxFun lam`,
and `pgl ℓ_λ = ScatFun.succMaxFun lam`.  The middle generator `k_{λ+1} ⊕ ℓ_λ` is the
binary finite gluing `ScatFun.glBin minFun maxFun` (notation `minFun ⊕ maxFun`).
-/

/-
The witnessing ordinal of `SimpleFun g.func` is exactly `lam` when `CBRank g.func = lam+1`:
so `g` is constant `= y` on its last nonempty CB-level `CBLevel g.func lam`, which is nonempty
while `CBLevel g.func (lam+1)` is empty.
-/
lemma simple_lam_data (lam : Ordinal.{0}) (g : ScatFun)
    (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func) :
    (CBLevel g.func lam).Nonempty ∧ CBLevel g.func (Order.succ lam) = ∅ ∧
      ∃ y : Baire, ∀ x ∈ CBLevel g.func lam, g.func x = y := by
  exact SimpleFun.top_level_scatFun g hg_simple hg_rank


/-
`g ≤ pgl ℓ_λ`: a simple function of CB-rank `lam+1` reduces to the maximum
`pgl ℓ_λ = succMaxFun lam` (`maxFun_is_maximum`, item 2).
-/
lemma simple_reduces_succMaxFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (g : ScatFun)
    (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func) :
    ScatFun.Reduces g (ScatFun.succMaxFun lam hlam_lt) := by
  -- By definition of `Reduces`, we need to show that `g.func` continuously reduces to `succMaxFun lam`.
  unfold ScatFun.Reduces;
  -- Extract the CB-level data from `simple_lam_data`.
  obtain ⟨hne, hempty, y, hconst⟩ := simple_lam_data lam g hg_rank hg_simple;
  convert maxFun_is_maximum lam hlam_lt |>.2 g.func g.hCont lam le_rfl hne hempty y hconst using 1;
  -- By definition of `succMaxFun`, we know that its function is `SuccMaxFun lam`.
  apply succMaxFun_func


/-
`k_{λ+1} ≤ g`: the minimum `k_{λ+1} = minFun lam` reduces to any simple function of
CB-rank `lam+1` (`minFun_is_minimum`).
-/
lemma minFun_reduces_simple (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (g : ScatFun)
    (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func) :
    ScatFun.Reduces (ScatFun.minFun lam hlam_lt) g := by
  have hne := ( simple_lam_data lam g hg_rank hg_simple ).left;
  convert minFun_is_minimum lam hlam_lt g.domain g.func g.hCont g.hScat hne using 1


/-
**Case A of Theorem 4.12.**  A simple `ScatFun` `g` of CB-rank `lam+1` with distinguished
point `y` (constant on the top CB-level) all of whose rays at `y` have CB-rank `< lam` is
equivalent to the minimum `k_{λ+1} = minFun lam`.
-/
lemma simple_caseA_equiv_minFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlam_cases : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hlow : ∀ n, CBRank (g.rayOn y Set.univ n).func < lam) :
    ScatFun.Equiv g (ScatFun.minFun lam hlam_lt) := by
  apply Classical.byContradiction
  intro h_contra;
  cases' hlam_cases with hlam_cases hlam_cases;
  · have h_contra : ∀ n, (g.rayOn y Set.univ n).domain = ∅ := by
      intro n
      by_contra h_nonempty
      have h_rank : CBRank (g.rayOn y Set.univ n).func = 1 := by
        have h_rank : CBRank (g.rayOn y Set.univ n).func ≠ 0 := by
          intro h_rank_zero
          have h_empty : (g.rayOn y Set.univ n).domain = ∅ := by
            have h_empty : ∀ {f : ScatFun}, CBRank f.func = 0 → f.domain = ∅ := by
              intros f hf_rank_zero
              have h_empty : CBLevel f.func 0 = ∅ := by
                -- `CBLevel f (CBRank f) = ∅` at the rank, here `CBRank f.func = 0`.
                have := CBLevel_eq_empty_at_rank f.func f.hScat
                rwa [hf_rank_zero] at this
              simp_all +decide [ CBLevel ];
            exact h_empty h_rank_zero
          contradiction;
        exact le_antisymm ( by simpa [ hlam_cases ] using hlow n |> le_of_lt ) ( Ordinal.one_le_iff_ne_zero.mpr h_rank );
      exact absurd ( hlow n ) ( by simp +decide [ h_rank, hlam_cases ] );
    have h_contra : ScatFun.Reduces g (ScatFun.pgl (fun i => g.rayOn y Set.univ i)) := by
      apply ScatFun.reduces_pgl_rays;
    have h_contra : CBRank g.func ≤ CBRank (ScatFun.pgl (fun i => g.rayOn y Set.univ i)).func := by
      apply_rules [ ContinuouslyReduces.rank_monotone ];
      · exact g.hScat;
      · exact ScatFun.pgl ( fun i => g.rayOn y univ i ) |>.hScat;
    have h_contra : CBRank (ScatFun.pgl (fun i => g.rayOn y Set.univ i)).func ≤ 1 := by
      have h_contra : ScatFun.Equiv (ScatFun.pgl (fun i => g.rayOn y Set.univ i)) (ScatFun.minFun 0 zero_lt_omega1) := by
        apply pgl_allEmpty_equiv_minFun_zero;
        aesop;
      have h_contra : CBRank (ScatFun.pgl (fun i => g.rayOn y Set.univ i)).func = CBRank (ScatFun.minFun 0 zero_lt_omega1).func := by
        apply cbRank_eq_of_equiv h_contra;
      rw [h_contra];
      rw [ minFun_cbRank_eq ] ; norm_num;
    simp_all +decide [ ScatFun.Reduces ];
    exact absurd h_contra ( not_le_of_gt ( lt_of_lt_of_le ( by norm_num ) ‹2 ≤ CBRank ( ScatFun.pgl fun i => g.rayOn y univ i ).func› ) );
  · have hP_le_minFun : ScatFun.Reduces (ScatFun.pgl (fun i => g.rayOn y Set.univ i)) (ScatFun.minFun lam hlam_lt) := by
      apply consequencesGeneralStructure_pgl_le_minFun lam hlam_lt hlam_cases.left hlam_cases.right (fun i => g.rayOn y Set.univ i) hlow;
    have h_minFun_le_g : ScatFun.Reduces (ScatFun.minFun lam hlam_lt) g := by
      apply minFun_reduces_simple lam hlam_lt g hg_rank hg_simple;
    apply h_contra;
    exact ⟨ ScatFun.reduces_pgl_rays g y |> fun h => h.trans hP_le_minFun, h_minFun_le_g ⟩


/-- The CB-rank of a ray is monotone under shrinking the domain set: a smaller domain set
gives a ray of `≤` CB-rank. -/
lemma rayOn_cbRank_mono (g : ScatFun) (y : Baire) {S S' : Set ↑g.domain} (hSS : S' ⊆ S)
    (n : ℕ) :
    CBRank (g.rayOn y S' n).func ≤ CBRank (g.rayOn y S n).func :=
  ContinuouslyReduces.rank_monotone (g.rayOn y S' n).hScat (g.rayOn y S n).hScat
    (g.rayOn_reduces_mono y hSS n)


/-- The `n`-th ray of `g` at `y` (on `univ`) is the corestriction of `g` to the clopen
codomain piece `RaySet univ y n`. -/
lemma rayOn_eq_corestrict (g : ScatFun) (y : Baire) (n : ℕ) :
    g.rayOn y Set.univ n
      = g.restrict {z : ↑g.domain | g.func z ∈ RaySet Set.univ y n} := by
  rw [ScatFun.rayOn, Set.univ_inter]



/-
`RaySet Set.univ y n` is clopen in Baire (the topology is the product of discrete
`ℕ`).
-/
lemma isClopen_raySet (y : Baire) (n : ℕ) : IsClopen (RaySet Set.univ y n) := by
  unfold RaySet;
  constructor;
  · refine isClosed_of_closure_subset ?_;
    intro x hx;
    rw [ mem_closure_iff_seq_limit ] at hx;
    rcases hx with ⟨ f, hf, hf' ⟩ ; have := tendsto_pi_nhds.mp hf' ; simp_all +decide [ Filter.Tendsto ] ;
    exact ⟨ fun k hk => by obtain ⟨ a, ha ⟩ := this k; specialize ha ( Max.max a n ) ( le_max_left _ _ ) ; specialize hf ( Max.max a n ) ; aesop, by obtain ⟨ a, ha ⟩ := this n; specialize ha ( Max.max a n ) ( le_max_left _ _ ) ; specialize hf ( Max.max a n ) ; aesop ⟩;
  · simp +decide [ isOpen_iff_mem_nhds ];
    intro x hx₁ hx₂; rw [ nhds_pi ] ; simp_all +decide [ Filter.mem_pi ] ;
    refine ⟨ Finset.range ( n + 1 ), ?_, fun i => if i < n then { y i } else { x i }, ?_, ?_ ⟩ <;> simp_all +decide [ Set.subset_def ];
    · aesop;
    · grind


/-- A ray of `g` at `y` whose clopen codomain piece `RaySet univ y n` is contained in a set
`B` reduces to the corestriction of `g` to `B`. -/
lemma rayOn_reduces_corestrict (g : ScatFun) (y : Baire) (n : ℕ) (B : Set Baire)
    (hsub : RaySet Set.univ y n ⊆ B) :
    ScatFun.Reduces (g.rayOn y Set.univ n)
      (g.restrict {z : ↑g.domain | g.func z ∈ B}) := by
  rw [rayOn_eq_corestrict]
  exact restrict_reduces_of_subset g (fun z hz => hsub hz)


/-
The corestriction of `g` to the (finite) union of the high rays `⋃ n ∈ Jf, RaySet univ y n`
has CB-rank `≤ lam`, whenever every ray of `g` at `y` has CB-rank `≤ lam`.
-/
lemma cbRank_corestrict_W_le (g : ScatFun) (y : Baire) (lam : Ordinal.{0})
    (hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam)
    (Jf : Finset ℕ) :
    CBRank (g.restrict {z : ↑g.domain | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func
      ≤ lam := by
  have := @cbRank_eq_iSup_restrict;
  refine' le_trans ( this _ _ _ |> le_of_eq ) _;
  use fun n => { w : ↑( g.restrict { z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n } ).domain | ( g.restrict { z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n } ).func w ∈ RaySet univ y n };
  · refine ⟨ ?_, ?_, ?_ ⟩;
    · intro n;
      refine ⟨ ?_, ?_ ⟩;
      · refine IsClosed.preimage ?_ ?_;
        · exact g.restrict _ |>.hCont;
        · exact isClopen_raySet y n |>.1;
      · refine IsOpen.preimage ?_ ?_;
        · exact g.restrict _ |>.hCont;
        · exact IsClopen.isOpen ( isClopen_raySet y n );
    · intro i j hij; rw [ Set.disjoint_left ] ; intro w hw hw'; simp_all +decide [ RaySet ] ;
      cases lt_or_gt_of_ne hij <;> tauto;
    · ext w; simp [RaySet];
      have := w.2;
      obtain ⟨ i, hi, hi' ⟩ := this;
      unfold RaySet at hi'; aesop;
  · refine ciSup_le fun n => ?_;
    refine le_trans ?_ ( hray_le n );
    apply_rules [ ContinuouslyReduces.rank_monotone ];
    · exact ScatFun.hScat _;
    · grind [ScatFun.hScat];
    · refine ⟨ ?_, ?_, ?_ ⟩;
      use fun x => ⟨ x.val, by
        convert x.2 using 1;
        ext; simp [ScatFun.rayOn, ScatFun.restrict];
        simp +decide only [ScatFun.restrictEquiv, mem_setOf_eq, coe_setOf, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk];
        constructor <;> intro h <;> rcases h with ⟨ h₁, h₂ ⟩ <;> simp_all +decide [ RaySet ];
        · contrapose! h₂;
          intro h; have := x.2; simp_all +decide [ RaySet ] ;
          simp_all +decide [ ScatFun.restrict ];
          obtain ⟨ ⟨ h₁, i, hi₁, hi₂, hi₃ ⟩, hi₄, hi₅ ⟩ := this; specialize hi₁; specialize hi₄; specialize hi₅; simp_all +decide [ ScatFun.restrictEquiv ] ;
          grind;
        · exact h₁.choose ⟩
      all_goals generalize_proofs at *;
      · fun_prop;
      · use fun x => x;
        exact ⟨ continuousOn_id, fun x => rfl ⟩


/-
A ray (at `y`) of a codomain-corestriction `g│_B` reduces to the corresponding ray of
`g`: shrinking the domain via a codomain condition can only shrink each ray.
-/
lemma corestrict_rayOn_reduces (g : ScatFun) (y : Baire) (B : Set Baire) (n : ℕ) :
    ScatFun.Reduces
      ((g.restrict {z : ↑g.domain | g.func z ∈ B}).rayOn y Set.univ n)
      (g.rayOn y Set.univ n) := by
  refine ⟨ ?_, ?_, ?_ ⟩
  all_goals generalize_proofs at *;
  refine' fun x => ⟨ x.val, _ ⟩;
  exact ⟨ x.2.1.1, x.2.2 ⟩;
  · fun_prop (disch := solve_by_elim);
  · refine ⟨ fun x => x, continuousOn_id, ?_ ⟩ ; aesop


/-
**Block `Wᶜ`.**  The corestriction of `g` to the complement of the union `W` of the
top-rank rays is again simple of rank `lam+1` with distinguished point `y`, and all of its
rays have CB-rank `< lam` (the top-rank rays of `g` have been removed), hence it is `≡ k_{λ+1}`
by `simple_caseA_equiv_minFun`.
-/
lemma corestrict_Wc_equiv_minFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (Jf : Finset ℕ)
    (hJf : ∀ n, n ∈ Jf ↔ lam ≤ CBRank (g.rayOn y Set.univ n).func) :
    ScatFun.Equiv
      (g.restrict {z | g.func z ∈ (⋃ n ∈ Jf, RaySet Set.univ y n)ᶜ})
      (ScatFun.minFun lam hlam_lt) := by
  refine ⟨ ?_, ?_ ⟩;
  · refine' ScatFun.reduces_pgl_rays _ _ |> fun h => h.trans _;
    exact y;
    convert consequencesGeneralStructure_pgl_le_minFun lam hlam_lt hlim hlam_ne _ _ using 1;
    intro n
    by_cases hn : n ∈ Jf;
    · refine' lt_of_le_of_lt ( csInf_le _ _ ) _;
      exact 0;
      · exact ⟨ 0, fun α hα => zero_le α ⟩;
      · ext; simp;
        rename_i x;
        obtain ⟨ hx₁, hx₂ ⟩ := x.2;
        exact False.elim <| hx₁.2 <| Set.mem_iUnion₂.mpr ⟨ n, by aesop ⟩;
      · finiteness;
    · refine' lt_of_le_of_lt _ ( lt_of_not_ge fun h => hn <| hJf n |>.2 h );
      exact (corestrict_rayOn_reduces g y ( ( ⋃ n ∈ Jf, RaySet Set.univ y n ) ᶜ ) n).rank_monotone
        (ScatFun.hScat _) (ScatFun.hScat _)
  · convert minFun_is_minimum lam hlam_lt _ _ _ _ using 1;
    any_goals exact ( g.restrict { z | g.func z ∈ ( ⋃ n ∈ Jf, RaySet univ y n ) ᶜ } ).func;
    · constructor;
      · intro h1 h2;
        convert h1 using 1;
      · intro h;
        convert h _ using 1;
        obtain ⟨ x₀, hx₀ ⟩ := simple_lam_data lam g hg_rank hg_simple |>.1;
        use ⟨ x₀, by
          simp +decide only [ScatFun.restrict, mem_setOf_eq, coe_setOf, compl_iUnion, mem_iInter, mem_compl_iff, Subtype.coe_eta, hconst x₀ hx₀, Subtype.coe_prop, exists_const];
          simp +decide [ RaySet ] ⟩
        generalize_proofs at *;
        convert cbLevel_block_iff g { z : g.domain | g.func z ∈ ( ⋃ n ∈ Jf, RaySet univ y n ) ᶜ } _ lam ⟨ x₀, by
          assumption ⟩ |>.2 hx₀ using 1
        generalize_proofs at *;
        refine' IsOpen.preimage g.hCont _;
        exact isOpen_compl_iff.mpr ( isClosed_biUnion_finset fun n hn => isClopen_raySet y n |>.1 );
    · exact g.restrict _ |>.hCont;
    · exact g.restrict _ |>.hScat


/-
**Block `W`.**  The corestriction of `g` to the union `W` of the finitely many top-rank
rays has CB-rank exactly `lam`, hence is `≡ ℓ_λ = maxFun lam`.
-/
lemma corestrict_W_equiv_maxFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam)
    (g : ScatFun) (y : Baire)
    (hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam)
    (Jf : Finset ℕ)
    (hJf : ∀ n, n ∈ Jf ↔ lam ≤ CBRank (g.rayOn y Set.univ n).func)
    (hJne : Jf.Nonempty) :
    ScatFun.Equiv
      (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n})
      (ScatFun.maxFun lam hlam_lt) := by
  obtain ⟨ n, hn ⟩ := hJne;
  -- We use transitivity: maxFun ≤ rayOn ≤ corestriction F. We already have `rayOn_reduces_corestrict g y n (⋃ m ∈ Jf, RaySet univ y m) ...`
  -- which is `ScatFun.Reduces (g.rayOn y Set.univ n) gW`. `ScatFun.Reduces` is `ContinuouslyReduces F.func G.func`.
  apply And.intro;
  · apply (maxFun_is_maximum lam hlam_lt).1;
    · grind [ScatFun.hCont];
    · grind [ScatFun.hScat];
    · -- By `cbRank_corestrict_W_le`, since `CBRank (g.rayOn y Set.univ n).func ≤ lam` for all `n`, we have `CBRank F.func ≤ lam`.
      have hCBRank_le : CBRank (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func ≤ lam := by
        apply cbRank_corestrict_W_le g y lam hray_le Jf;
      -- For `β ≥ lam ≥ CBRank F`, `CBLevel F β ⊆ CBLevel F (CBRank F) = ∅` by antitonicity.
      intro β hβ
      have hr : CBRank (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func ≤ β :=
        le_trans hCBRank_le hβ
      have hempty := CBLevel_eq_empty_at_rank
        (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func
        (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).hScat
      exact Set.subset_empty_iff.mp (hempty ▸ CBLevel_antitone _ hr)
  · have h_equiv : ScatFun.Equiv (g.rayOn y Set.univ n) (ScatFun.maxFun lam hlam_lt) := by
      apply limit_rank_equiv_maxFun;
      · assumption;
      · exact le_antisymm ( hray_le n ) ( hJf n |>.1 hn );
    exact h_equiv.2.trans ( rayOn_reduces_corestrict g y n ( ⋃ m ∈ Jf, RaySet Set.univ y m ) ( fun v hv => Set.mem_biUnion hn hv ) )


/-! ### Centered disjoint-union decomposition (recursive route)

Building `g = ⊔ centered` for the diagonal argument.  The first atomic step: a Case-B top
point gets a *centered clopen* neighbourhood.  (Top points are separated, each gets such a
basin; the rank-`≤ β` remainder is recursed on.) -/

/-- **Case-B centered clopen neighbourhood of a top point.**  For a simple `G` of rank `β+1`
with top level constant `= y`, a top-level point `x` all of whose cylinder neighbourhoods keep
full rank has a *clopen* (in Baire) neighbourhood `N` on which `G` is centered.

`caseB_pgl_equiv_exists` gives the open Case-B neighbourhood `U` with `G|_U ≡ pgl ρ` centered
(some center `c`).  Writing `U = val⁻¹ W`, take a clopen `N = Cx ∪ Cc ⊆ W` containing both `x`
and `c`; `isCenterFor_restrict` keeps `c` a center of `G|_N`, and `isCentered_subtypeSubtype`
flattens the nested subtype. -/
lemma caseB_centered_clopen_nbhd
    (β : Ordinal.{0}) (hβ : β < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ β)))
    (G : ScatFun) (hG_rank : CBRank G.func = Order.succ β)
    (yb : Baire) (hy : ∀ a ∈ CBLevel G.func β, G.func a = yb)
    (ih : ∀ δ < Order.succ β, ∀ (g : ScatFun), CBRank g.func = δ → IsLocallyCentered g.func)
    (x : ↑G.domain) (hx_top : x ∈ CBLevel G.func β)
    (hcyl : ∀ n, Order.succ β ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain))) :
    ∃ N : Set Baire, IsClopen N ∧ (x : Baire) ∈ N ∧
      IsCentered (G.func ∘
        (Subtype.val : ↥{a : ↑G.domain | (a : Baire) ∈ N} → ↑G.domain)) := by
  obtain ⟨ρ, U, hρ, hU_open, hxU, hequiv⟩ :=
    caseB_pgl_equiv_exists β hβ h2bqo G hG_rank yb hy ih x hx_top hcyl
  have hcent : IsCentered (G.func ∘ (Subtype.val : ↥U → ↑G.domain)) :=
    isCentered_of_equiv
      ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, pgluingOfRegularIsCentered ρ hρ⟩ hequiv
  obtain ⟨c, hc⟩ := hcent
  obtain ⟨W, hW_open, hUW⟩ : ∃ W : Set Baire, IsOpen W ∧ U = Subtype.val ⁻¹' W := by
    obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU_open
    exact ⟨W, hW, hWU.symm⟩
  have hxW : (x : Baire) ∈ W := hUW.le hxU
  have hcW : ((c : ↑G.domain) : Baire) ∈ W := hUW.le c.2
  obtain ⟨Cx, hCx, hxCx, hCxW⟩ :=
    baire_exists_clopen_subset_of_open (x : Baire) W hW_open hxW
  obtain ⟨Cc, hCc, hcCc, hCcW⟩ :=
    baire_exists_clopen_subset_of_open ((c : ↑G.domain) : Baire) W hW_open hcW
  refine ⟨Cx ∪ Cc, hCx.union hCc, Or.inl hxCx, ?_⟩
  -- `V := {u : U | u.val ∈ Cx ∪ Cc}` is an open neighbourhood of `c` in `U`.
  set V : Set ↥U := {u : ↥U | ((u : ↑G.domain) : Baire) ∈ Cx ∪ Cc} with hV
  have hV_open : IsOpen V :=
    (hCx.union hCc).isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hcV : c ∈ V := Or.inr hcCc
  -- `c` remains a center of `(G|_U)|_V`; flatten the nested subtype.
  have hcenterV : IsCentered ((G.func ∘ (Subtype.val : ↥U → ↑G.domain)) ∘
      (Subtype.val : ↥V → ↥U)) :=
    ⟨⟨c, hcV⟩, isCenterFor_restrict hc hV_open hcV⟩
  have hflat := isCentered_subtypeSubtype G.func U hU_open V hV_open hcenterV
  -- Identify `U ∩ (val '' V)` with `{a | a.val ∈ Cx ∪ Cc}`.
  have hset : {a : ↑G.domain | ((a : ↑G.domain) : Baire) ∈ Cx ∪ Cc}
      = U ∩ (Subtype.val '' V) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_image]
    constructor
    · intro ha
      have haU : a ∈ U := by
        rw [hUW]; rcases ha with h | h
        · exact hCxW h
        · exact hCcW h
      exact ⟨haU, ⟨a, haU⟩, ha, rfl⟩
    · rintro ⟨-, u, hu, rfl⟩; exact hu
  rw [hset]; exact hflat


/-! ### Prefix-cylinder strengthening of local centeredness

The memoir's `0dimanddisjointunion` (Prop 2.14) tree proof needs, for every `x`, a *basic
prefix-cylinder* neighbourhood `N_s` (`s ⊏ x`) with `f|_{N_s}` centered — strictly stronger than
the open-neighbourhood `IsLocallyCentered` that `localCenterednessFromTwoBQO_scatFun` delivers.
With the prefix witness, the minimal-prefix construction gives the centered disjoint union with NO
Kechris/discreteness/pointed-refinement (cylinders for incomparable prefixes are automatically
disjoint).  We strengthen local centeredness to this prefix form. -/

/-- **Case B, prefix-cylinder form.**  Under the Case-B hypotheses, some prefix cylinder
`G.cyl x n` around `x` carries a centered restriction of `G`.

## Provided solution

The key point (observed by the author): in Case B the point `x` is itself a **center** of its
basin `caseB_U`, so any cylinder around `x` inside the basin is centered by `isCenterFor_restrict`
— no need to argue about the whole cylinder or `pgl` of all rays.

1. `caseB_pgl_equiv_exists` gives `m, j`, a regular `ρ`, and `G|_{caseB_U} ≡ pgl ρ`, where
   `caseB_U = (G.cyl x m) ∩ {avoid low rays 0..j-1}` and `x ∈ caseB_U` (`mem_caseB_U`, as
   `G.func x = y`).
2. **`x` is a center of `G|_{caseB_U}`.**  On the upper side (`caseB_upper`, via
   `pgl_reduces_of_rays`/`raySigma0`) the reduction `σ` sends every `y`-point to `zeroStream`,
   so `σ x = zeroStream`; on the lower side (`caseB_lower`) the reduction `pgl ρ ≤ G|_{caseB_U}`
   is `pgl_reduces_of_local` **anchored at `x`**, so it sends `zeroStream ↦ x`.  Since `zeroStream`
   is the center of `pgl ρ` (`pgluingOfRegularIsCentered`), `centerInvariance_equiv` transports it
   to give `IsCenterFor (G|_{caseB_U}) x`.  (This needs exposing the center-at-`x` from the caseB
   construction, e.g. a helper `caseB_x_isCenter`.)
3. Pick `n` with `G.cyl x n ⊆ caseB_U` (`baire_subspace_cylinder_mem_nhds`, as `caseB_U` is open
   and `x ∈ caseB_U`).  By `isCenterFor_restrict`, `x` is a center of `G|_{G.cyl x n}`, so it is
   centered.  `G.cyl x n` is a basic prefix cylinder — the tree-proof witness. -/
lemma caseB_centered_cylinder
    (β : Ordinal.{0}) (_hβ : β < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ β)))
    (G : ScatFun) (_hG_rank : CBRank G.func = Order.succ β)
    (yb : Baire) (hy : ∀ a ∈ CBLevel G.func β, G.func a = yb)
    (_ih : ∀ δ < Order.succ β, ∀ (g : ScatFun), CBRank g.func = δ → IsLocallyCentered g.func)
    (x : ↑G.domain) (hx_top : x ∈ CBLevel G.func β)
    (_hcyl : ∀ n, Order.succ β ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain))) :
    ∃ n : ℕ, IsCentered (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain)) := by
  have hfx : G.func x = yb := hy x hx_top
  -- Re-run the Case-B regular-ray selection (as in `caseB_pgl_equiv_exists`) to get `m, j`.
  set s : ℕ → ℕ → ScatFun.LevelLT (Order.succ β) :=
    fun n i => ⟨G.rayOn yb (G.cyl x n) i,
      G.rayOn_cbRank_lt β yb hy (G.cyl x n) (G.cyl_isOpen x n) i⟩ with hs
  have hdec : ∀ m n i : ℕ, m ≤ n →
      ScatFun.LevelLT.reduces (Order.succ β) (s n i) (s m i) :=
    fun m n i hmn => G.rayOn_reduces_mono yb (G.cyl_subset_of_le x hmn) i
  obtain ⟨m, j, hreg, hdom⟩ := wqo_double_selection h2bqo s hdec
  -- `x` is a center of its basin `caseB_U`.
  have hcenter : IsCenterFor (G.func ∘ (Subtype.val : ↥(caseB_U G yb x m j) → ↑G.domain))
      ⟨x, mem_caseB_U G yb x m j hfx⟩ :=
    caseB_x_isCenter G yb x m j hfx (fun i => hreg i) (by
      intro n hn i; obtain ⟨i', hi', hred⟩ := hdom n hn i; exact ⟨i', hi', hred⟩)
  -- A cylinder around `x` sits inside the (open) basin.
  obtain ⟨n, hn⟩ := baire_subspace_cylinder_mem_nhds x (caseB_U G yb x m j)
    (caseB_U_isOpen G yb x m j) (mem_caseB_U G yb x m j hfx)
  refine ⟨n, ?_⟩
  -- Restrict the center to the cylinder via `isCenterFor_restrict`, then flatten the subtype.
  set V : Set ↥(caseB_U G yb x m j) := {p | (p : ↑G.domain) ∈ G.cyl x n} with hV
  have hV_open : IsOpen V := (G.cyl_isOpen x n).preimage continuous_subtype_val
  have hxV : (⟨x, mem_caseB_U G yb x m j hfx⟩ : ↥(caseB_U G yb x m j)) ∈ V := G.mem_cyl x n
  have hcV : IsCentered ((G.func ∘ (Subtype.val : ↥(caseB_U G yb x m j) → ↑G.domain)) ∘
      (Subtype.val : ↥V → ↥(caseB_U G yb x m j))) :=
    ⟨⟨⟨x, mem_caseB_U G yb x m j hfx⟩, hxV⟩, isCenterFor_restrict hcenter hV_open hxV⟩
  have hflat := isCentered_subtypeSubtype G.func (caseB_U G yb x m j)
    (caseB_U_isOpen G yb x m j) V hV_open hcV
  have hset : G.cyl x n = caseB_U G yb x m j ∩ (Subtype.val '' V) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · intro ha; exact ⟨hn ha, ⟨a, hn ha⟩, ha, rfl⟩
    · rintro ⟨-, u, hu, rfl⟩; exact hu
  rw [hset]; exact hflat


/-
**Cylinder transfer.**  A centered cylinder of the restriction `F.restrict (F.cyl x n)`
around the realized point of `x` transfers to a centered cylinder of `F` itself.  The cylinder
`(F.restrict (F.cyl x n)).cyl x' m` realizes (as a subset of `F.domain`) as `F.cyl x (max n m)`
— the intersection of two cylinders at the same centre `x` — and the function is unchanged up
to the realization homeomorphism `restrictEquiv`.
-/
lemma cyl_restrict_witness_transfer (F : ScatFun) (x : ↑F.domain) (n m : ℕ)
    (h : IsCentered ((F.restrict (F.cyl x n)).func ∘
        (Subtype.val :
          ↥((F.restrict (F.cyl x n)).cyl
              ((F.restrictEquiv (F.cyl x n)).symm ⟨x, F.mem_cyl x n⟩) m)
          → ↑(F.restrict (F.cyl x n)).domain))) :
    IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x (max n m)) → ↑F.domain)) := by
  convert isCentered_of_homeomorph _ _ _ _ h;
  refine ⟨ ?_, ?_, ?_ ⟩;
  use fun z => ⟨ ⟨ z.val, by
    have := z.2;
    exact ⟨ z.1.2, fun i hi => this i ( Finset.mem_range.mpr ( lt_of_lt_of_le ( Finset.mem_range.mp hi ) ( le_max_left _ _ ) ) ) ⟩ ⟩, by
    simp +decide only [ScatFun.cyl, nbhd', coe_setOf, mem_setOf_eq, Finset.mem_range] at *;
    exact fun i hi => z.2 i ( Finset.mem_range.mpr ( lt_of_lt_of_le hi ( le_max_right _ _ ) ) ) ⟩;
  use fun z => ⟨ ⟨ z.val.val, by
    grind ⟩, by
    intro i hi;
    by_cases hi' : i < n <;> simp_all +decide [ ScatFun.cyl ];
    · have := z.1.2; simp_all +decide [ ScatFun.cyl, nbhd' ] ;
      exact this.2 i hi';
    · have := z.2 i ( by aesop ) ; aesop; ⟩;
  all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
  · fun_prop;
  · fun_prop;
  · aesop


/-
**Cylinder transfer, CB-rank version.**  Same realization as `cyl_restrict_witness_transfer`:
the cylinder `(F.restrict (F.cyl x n)).cyl x' m` realizes as `F.cyl x (max n m)` with the
function unchanged up to the realization homeomorphism, so the two restrictions have equal
CB-rank.
-/
lemma cbRank_cyl_restrict_eq (F : ScatFun) (x : ↑F.domain) (n m : ℕ) :
    CBRank ((F.restrict (F.cyl x n)).func ∘
        (Subtype.val :
          ↥((F.restrict (F.cyl x n)).cyl
              ((F.restrictEquiv (F.cyl x n)).symm ⟨x, F.mem_cyl x n⟩) m)
          → ↑(F.restrict (F.cyl x n)).domain))
      = CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x (max n m)) → ↑F.domain)) := by
  have h_homeo : ∃ e : ↥(F.cyl x (max n m)) ≃ₜ ↥((F.restrict (F.cyl x n)).cyl ((F.restrictEquiv (F.cyl x n)).symm ⟨x, F.mem_cyl x n⟩) m), ∀ y : ↥(F.cyl x (max n m)), F.func y.val = ((F.restrict (F.cyl x n)).func ∘ Subtype.val) (e y) := by
    unfold ScatFun.cyl at *;
    unfold nbhd' at *; simp_all +decide [ ScatFun.restrict, ScatFun.restrictEquiv ] ;
    refine ⟨ ?_, ?_ ⟩;
    refine ⟨ ?_, ?_, ?_ ⟩;
    refine ⟨ fun y => ⟨ ⟨ y.val, ?_ ⟩, ?_ ⟩, fun y => ⟨ ⟨ y.val, ?_ ⟩, ?_ ⟩, ?_, ?_ ⟩;
    grind;
    grind +revert;
    grind;
    grind;
    all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
    · fun_prop (disch := solve_by_elim);
    · fun_prop;
  obtain ⟨ e, he ⟩ := h_homeo;
  rw [ ← CBRank_comp_homeomorph e ];
  exact congr_arg _ ( funext fun y => he y ▸ rfl )


/-
**Rank-preserving open restriction of a simple function is simple.**  If `g` is simple and an
open restriction `g ∘ val` keeps the full CB-rank of `g`, then it is again simple: the top level
of the restriction is `CBLevel g (CBRank g - 1)` intersected with the open set, which is nonempty
(rank preserved), one level higher is empty, and `g`'s constancy on its top level is inherited.
-/
lemma simpleFun_restrict_open_of_rank_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g : X → Y) (hg : SimpleFun g) (S : Set X) (hS : IsOpen S)
    (hrank : CBRank (g ∘ (Subtype.val : ↥S → X)) = CBRank g) :
    SimpleFun (g ∘ (Subtype.val : ↥S → X)) := by
  -- By definition of SimpleFun, obtain the witness `⟨α, hne, hempty, c, hc⟩` with `Order.succ α = CBRank g`.
  obtain ⟨α, hα_ne, hα_empty, c, hc⟩ : ∃ α, (CBLevel g α).Nonempty ∧ CBLevel g (Order.succ α) = ∅ ∧ ∃ c, ∀ x ∈ CBLevel g α, g x = c := hg
  -- Use `hrank` to check the CB-level of the restriction at `α` and `Order.succ α`.
  have hlevel_ne : (CBLevel (g ∘ Subtype.val : ↥S → Y) α).Nonempty := by
    by_contra hlevel_empty;
    simp_all +decide [ Set.not_nonempty_iff_eq_empty ];
    have hlevel_empty : CBRank (g ∘ Subtype.val : ↥S → Y) ≤ α :=
      CBRank_le_of_CBLevel_empty (g ∘ Subtype.val) α hlevel_empty
    have hlevel_empty : CBRank g ≤ α := by
      exact hrank ▸ hlevel_empty;
    have hlevel_empty : CBLevel g (CBRank g) = ∅ :=
      CBLevel_eq_empty_at_rank g (scatteredFun_of_CBLevel_empty g (Order.succ α) hα_empty)
    obtain ⟨ x, hx ⟩ := hα_ne;
    have hlevel_empty : CBLevel g (CBRank g) ⊇ CBLevel g α := by
      apply CBLevel_antitone;
      assumption;
    exact absurd ( hlevel_empty hx ) ( by simp +decide [ * ] )
  have hlevel_empty : CBLevel (g ∘ Subtype.val : ↥S → Y) (Order.succ α) = ∅ := by
    grind [CBLevel_const_succ_empty, CBLevel_open_restrict];
  refine ⟨ α, hlevel_ne, hlevel_empty, c, ?_ ⟩;
  intro x hx; specialize hc ( x : X ) ; simp_all +decide [ CBLevel_open_restrict ] ;


/-
**Rank-preserving open restriction to a subset of a simple set is simple.**  If `f ∘ val` is
simple on an open `W` and `S ⊆ W` is open with the same CB-rank, then `f ∘ val` is simple on `S`.
Reduces to `simpleFun_restrict_open_of_rank_eq` applied to the simple function `f ∘ val_W` and the
open subset `{w : ↥W | w.val ∈ S}`, transported back along the homeomorphism with `S`.
-/
lemma simpleFun_restrict_open_subset_of_rank_eq {A : Set Baire} (f : A → Baire)
    (W S : Set A) (hSW : S ⊆ W)
    (hWsimple : SimpleFun (f ∘ (Subtype.val : ↥W → A))) (hS : IsOpen S)
    (hrank : CBRank (f ∘ (Subtype.val : ↥S → A))
      = CBRank (f ∘ (Subtype.val : ↥W → A))) :
    SimpleFun (f ∘ (Subtype.val : ↥S → A)) := by
  revert hWsimple hS hrank;
  intro hWsimple hS hrank
  set g : W → Baire := f ∘ Subtype.val
  set S' : Set W := {w : W | (w : A) ∈ S};
  have hS'_open : IsOpen S' := by
    exact hS.preimage ( continuous_subtype_val );
  have hS'_rank : CBRank (g ∘ (Subtype.val : ↥S' → ↑W)) = CBRank g := by
    convert hrank using 1;
    convert CBRank_comp_homeomorph _ _ using 2;
    swap;
    refine ⟨ ?_, ?_, ?_ ⟩;
    refine ⟨ fun x => ⟨ x.val, x.property ⟩, fun x => ⟨ ⟨ x.val, hSW x.property ⟩, x.property ⟩, ?_, ?_ ⟩ <;> simp +decide [ Function.LeftInverse, Function.RightInverse ];
    fun_prop;
    fun_prop;
    ext; simp [g];
  convert SimpleFun.comp_homeomorph ( show S ≃ₜ S' from ?_ ) ( g ∘ Subtype.val ) ( simpleFun_restrict_open_of_rank_eq g hWsimple S' hS'_open hS'_rank ) using 1;
  swap;
  refine ⟨ ?_, ?_, ?_ ⟩;
  refine ⟨ fun x => ⟨ ⟨ x.val, hSW x.prop ⟩, x.prop ⟩, fun x => ⟨ x.val, x.prop ⟩, ?_, ?_ ⟩;
  all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
  · fun_prop;
  · fun_prop;
  · exact funext fun x => rfl


/-- **Case B of the cylinder-witness theorem.**  When every cylinder around `x` keeps the full
rank `β+1`, the decomposition lemma (`decomposition_lemma_baire`) makes `F` simple on a clopen
neighbourhood `W ∋ x`; restricting to `W` and re-running the Case-B regular-ray selection
(`caseB_x_isCenter` / `caseB_pgl_equiv_exists`) shows the realized point of `x` is a centre of
its basin, so every deep enough cylinder around `x` (eventually contained in `W`, where it
coincides with a cylinder of the restriction) is centered. -/
lemma scatFun_centered_cylinder_caseB
    (β : Ordinal.{0}) (hβ : Order.succ β < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ β)))
    (F : ScatFun) (hF_rank : CBRank F.func = Order.succ β)
    (x : ↑F.domain)
    (hcaseB : ∀ n, Order.succ β ≤
        CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain))) :
    ∃ n, IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain)) := by
  have hβ' : β < omega1 := lt_trans (Order.lt_succ β) hβ
  -- open-form local centeredness for ranks `< β + 1`
  have ih_open : ∀ δ < Order.succ β, ∀ (g : ScatFun), CBRank g.func = δ →
      IsLocallyCentered g.func := by
    intro δ hδ g hg
    exact localCenterednessFromTwoBQO_scatFun δ (lt_trans hδ hβ)
      (hbqo.comap (fun G : ScatFun.LevelLT δ =>
        (⟨G.val, lt_of_lt_of_le G.prop hδ.le⟩ : ScatFun.LevelLT (Order.succ β)))) g hg
  -- `F` is simple on a clopen neighbourhood `W ∋ x`
  obtain ⟨U0, hU0_clopen, hxU0, hsimpleU0⟩ :=
    decomposition_lemma_baire F.domain F.func F.hScat x
  set W : Set ↑F.domain := {a : ↑F.domain | (a : Baire) ∈ U0} with hW
  have hW_open : IsOpen W := hU0_clopen.2.preimage continuous_subtype_val
  have hxW : x ∈ W := hxU0
  -- a cylinder around `x` inside `W`
  obtain ⟨n0, hn0⟩ := baire_subspace_cylinder_mem_nhds x W hW_open hxW
  have hn0' : F.cyl x n0 ⊆ W := hn0
  set G : ScatFun := F.restrict (F.cyl x n0) with hG
  set x' : ↑G.domain := (F.restrictEquiv (F.cyl x n0)).symm ⟨x, F.mem_cyl x n0⟩ with hx'
  -- the cylinder restriction has full rank `β + 1`
  have hcylrank : CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain))
      = Order.succ β := by
    refine le_antisymm ?_ (hcaseB n0)
    calc CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain))
        ≤ CBRank F.func :=
          CBRank_open_restrict_le F.func F.hScat (F.cyl x n0) (F.cyl_isOpen x n0)
      _ = Order.succ β := hF_rank
  have hG_rank : CBRank G.func = Order.succ β := by
    rw [show CBRank G.func
        = CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain)) from
      cbRank_restrict_eq F (F.cyl x n0)]
    exact hcylrank
  -- the rank of `F` on `W` is also `β + 1`
  have hWrank : CBRank (F.func ∘ (Subtype.val : ↥W → ↑F.domain)) = Order.succ β := by
    refine le_antisymm ?_ ?_
    · calc CBRank (F.func ∘ (Subtype.val : ↥W → ↑F.domain))
          ≤ CBRank F.func := CBRank_open_restrict_le F.func F.hScat W hW_open
        _ = Order.succ β := hF_rank
    · have hmono : CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain))
          ≤ CBRank (F.func ∘ (Subtype.val : ↥W → ↑F.domain)) := by
        have hred : ScatFun.Reduces (F.restrict (F.cyl x n0)) (F.restrict W) :=
          restrict_reduces_of_subset F hn0'
        have := ContinuouslyReduces.rank_monotone
          (F.restrict (F.cyl x n0)).hScat (F.restrict W).hScat hred
        rwa [cbRank_restrict_eq F (F.cyl x n0), cbRank_restrict_eq F W] at this
      rw [← hcylrank]; exact hmono
  -- the restriction is simple
  have hG_simple : SimpleFun G.func := by
    have hbase : SimpleFun (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain)) :=
      simpleFun_restrict_open_subset_of_rank_eq F.func W (F.cyl x n0) hn0' hsimpleU0
        (F.cyl_isOpen x n0) (by rw [hcylrank, hWrank])
    exact SimpleFun.comp_homeomorph (F.restrictEquiv (F.cyl x n0))
      (F.func ∘ (Subtype.val : ↥(F.cyl x n0) → ↑F.domain)) hbase
  -- constancy on the top level
  obtain ⟨_, _, y, hy⟩ := hG_simple.top_level_scatFun G hG_rank
  -- cylinders of `G` keep full rank
  have hcylG : ∀ k, Order.succ β ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x' k) → ↑G.domain)) := by
    intro k
    have he : CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x' k) → ↑G.domain))
        = CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x (max n0 k)) → ↑F.domain)) :=
      cbRank_cyl_restrict_eq F x n0 k
    rw [he]; exact hcaseB (max n0 k)
  -- `x'` lies in the top CB-level of `G`
  have hx'_top : x' ∈ CBLevel G.func β := mem_CBLevel_of_cyl_rank G β hG_rank x' hcylG
  -- Case-B kernel produces a centered cylinder of `G`
  obtain ⟨N, hN⟩ :=
    caseB_centered_cylinder β hβ' hbqo G hG_rank y hy ih_open x' hx'_top hcylG
  -- transfer the centered cylinder back to `F`
  refine ⟨max n0 N, ?_⟩
  have hN' : IsCentered ((F.restrict (F.cyl x n0)).func ∘
      (Subtype.val :
        ↥((F.restrict (F.cyl x n0)).cyl
            ((F.restrictEquiv (F.cyl x n0)).symm ⟨x, F.mem_cyl x n0⟩) N)
        → ↑(F.restrict (F.cyl x n0)).domain)) := hN
  exact cyl_restrict_witness_transfer F x n0 N hN'


/-- **Prefix-cylinder local centeredness from 2-BQO.**  Strengthens
`localCenterednessFromTwoBQO_scatFun`: every point has a *basic prefix cylinder* on which the
function is centered (not merely some open neighbourhood).

## Provided solution

Same induction on `α` as `localCenterednessFromTwoBQO_scatFun`, tracking that the witness is a
cylinder `F.cyl x n`:
* `α = 0` / rank `0`: the domain is empty, vacuous.
* `α` limit: `F` is locally `𝒞_{<α}`; on a cylinder of rank `< α` apply `ih`.
* `α = β+1`: by `decomposition_lemma_baire`, a clopen cylinder `V ∋ x` has `G = F|_V` simple of
  rank `≤ β+1`.  Per point of `G`:
  - **caseA** (some `G.cyl x n` has rank `< β+1`): apply `ih` to that lower-rank cylinder — its
    prefix-cylinder witness transports back (a cylinder of a cylinder is a cylinder).
  - **caseB** (`x ∈ CB_β`, all cylinders full rank): `caseB_centered_cylinder` gives a centered
    `G.cyl x n` directly.
  Composing the two cylinder layers (`V`-cylinder then the inner cylinder) yields a single prefix
  cylinder of `F` around `x` on which `F` is centered.

This is the exact analogue of the existing proof with `IsCenterFor`/`IsCentered` on cylinders
replacing the open-neighbourhood conclusion; the BQO content stays inside `caseB_centered_cylinder`. -/
theorem scatFun_centered_cylinder_witness
    (α : Ordinal.{0}) (hα : α < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces α)) :
    ∀ (F : ScatFun), CBRank F.func = α →
      ∀ x : ↑F.domain,
        ∃ n : ℕ, IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain)) := by
  induction α using Ordinal.induction with
  | _ α ih =>
  intro F hF_rank x
  have hbqo_le : ∀ γ, γ ≤ α → TwoBQO (ScatFun.LevelLT.reduces γ) :=
    fun γ hγα => hbqo.comap
      (fun G : ScatFun.LevelLT γ => (⟨G.val, lt_of_lt_of_le G.prop hγα⟩ : ScatFun.LevelLT α))
  have h_ind : ∀ δ < α, ∀ (g : ScatFun), CBRank g.func = δ →
      ∀ x' : ↑g.domain,
        ∃ m, IsCentered (g.func ∘ (Subtype.val : ↥(g.cyl x' m) → ↑g.domain)) :=
    fun δ hδ g hg x' => ih δ hδ (hδ.trans hα) (hbqo_le δ hδ.le) g hg x'
  rcases eq_or_ne α 0 with hα0 | hα0
  · -- rank `0`: the domain is empty, contradicting the given point `x`.
    exfalso
    have h1 : CBLevel F.func (CBRank F.func) = ∅ := CBLevel_eq_empty_at_rank F.func F.hScat
    rw [hF_rank, hα0, CBLevel_zero] at h1
    exact Set.notMem_empty x (h1 ▸ Set.mem_univ x)
  · by_cases hlim : Order.IsSuccLimit α
    · -- limit case: `F` is locally of lower rank on a cylinder; recurse and transfer.
      obtain ⟨U, hU_open, hxU, hU_rank⟩ :=
        limit_locally_lower F.hScat α hF_rank.symm hlim x
      obtain ⟨m, hm⟩ := baire_subspace_cylinder_mem_nhds x U hU_open hxU
      have hcyl_sub : F.cyl x m ⊆ U := hm
      have hδ_lt : CBRank (F.restrict (F.cyl x m)).func < α := by
        have h1 : ScatFun.Reduces (F.restrict (F.cyl x m)) (F.restrict U) :=
          restrict_reduces_of_subset F hcyl_sub
        have h2 : CBRank (F.restrict (F.cyl x m)).func ≤ CBRank (F.restrict U).func :=
          ContinuouslyReduces.rank_monotone
            (F.restrict (F.cyl x m)).hScat (F.restrict U).hScat h1
        have h3 : CBRank (F.restrict U).func
            = CBRank (F.func ∘ (Subtype.val : ↥U → ↑F.domain)) := cbRank_restrict_eq F U
        rw [h3] at h2
        exact lt_of_le_of_lt h2 hU_rank
      obtain ⟨k, hk⟩ := h_ind _ hδ_lt (F.restrict (F.cyl x m)) rfl
        ((F.restrictEquiv (F.cyl x m)).symm ⟨x, F.mem_cyl x m⟩)
      exact ⟨max m k, cyl_restrict_witness_transfer F x m k hk⟩
    · -- successor case `α = β + 1`.
      obtain ⟨β, rfl⟩ : ∃ β, α = Order.succ β := by
        contrapose! hlim
        exact ⟨fun h => hα0 h.eq_bot, fun γ hγ => hlim γ hγ.succ_eq.symm⟩
      by_cases hA : ∃ k, CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x k) → ↑F.domain))
          < Order.succ β
      · -- Case A: a cylinder of strictly lower rank; recurse and transfer.
        obtain ⟨k, hk⟩ := hA
        have hδ_lt : CBRank (F.restrict (F.cyl x k)).func < Order.succ β := by
          have h3 : CBRank (F.restrict (F.cyl x k)).func
              = CBRank (F.func ∘ (Subtype.val : ↥(F.cyl x k) → ↑F.domain)) :=
            cbRank_restrict_eq F (F.cyl x k)
          rw [h3]; exact hk
        obtain ⟨j, hj⟩ := h_ind _ hδ_lt (F.restrict (F.cyl x k)) rfl
          ((F.restrictEquiv (F.cyl x k)).symm ⟨x, F.mem_cyl x k⟩)
        exact ⟨max k j, cyl_restrict_witness_transfer F x k j hj⟩
      · -- Case B: every cylinder keeps full rank.
        push_neg at hA
        exact scatFun_centered_cylinder_caseB β hα hbqo F hF_rank x hA


/-! ### Diagonal argument (Case B upper bound) — supporting lemmas

The memoir's reverse inequality `g ≤ k_{λ+1} ⊕ ℓ_λ` is the *diagonal argument*.  We isolate
its ingredients below. -/

/-
A domain-restriction reduces to the whole function (inclusion of the subset).
-/
lemma restrict_le_self (g : ScatFun) (S : Set ↑g.domain) :
    ScatFun.Reduces (g.restrict S) g := by
  use fun x => (g.restrictEquiv S x : ↑g.domain);
  refine ⟨ ?_, ?_ ⟩;
  · exact continuous_subtype_val.comp ( g.restrictEquiv S |>.continuous_toFun );
  · exact ⟨ fun x => x, continuousOn_id, fun x => rfl ⟩


/-
**The cocenter equals the distinguished point.**  For a centered scattered `F` of
CB-rank `lam+1` that is constant `= y` on its top CB-level `CBLevel F lam`, the cocenter
of `F` is `y`.
-/
lemma cocenter_eq_distinguished (F : ScatFun) (hF_cent : IsCentered F.func)
    (lam : Ordinal.{0}) (hF_rank : CBRank F.func = lam + 1)
    (y : Baire) (hy : ∀ a ∈ CBLevel F.func lam, F.func a = y) :
    cocenter F.func hF_cent = y := by
  convert hy _ _;
  convert center_in_CBLevel F.func ( hF_cent.choose ) ( hF_cent.choose_spec ) lam ( CBLevel_nonempty_below_rank F.func F.hScat lam ( by
    exact hF_rank.symm ▸ Order.lt_succ lam ) ) using 1


/-
**The cocenter of a pointed gluing of a regular value-sequence is `zeroStream`.**
-/
lemma cocenter_pgl_eq_zeroStream (s : ℕ → ScatFun)
    (hreg : Preorder.IsRegularSeq ScatFun.Reduces s)
    (hval : ∀ (i : ℕ) (a : ↑(s i).domain), (s i).func a = (a : ℕ → ℕ))
    (hcent : IsCentered (ScatFun.pgl s).func) :
    cocenter (ScatFun.pgl s).func hcent = zeroStream := by
  have h_center : ∃ z0 : ↑(ScatFun.pgl s).domain, z0.val = zeroStream ∧ IsCenterFor (ScatFun.pgl s).func z0 := by
    obtain ⟨z0, hz0⟩ : ∃ z0 : ↑(ScatFun.pgl s).domain, z0.val = zeroStream := by
      exact ⟨ ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩, rfl ⟩;
    grind [pgluingOfRegularIsCentered];
  convert scatteredHaveCocenter ( ScatFun.pgl s ).func ( ScatFun.pgl s ).hScat ( hcent.choose ) ( h_center.choose ) hcent.choose_spec h_center.choose_spec.2 using 1;
  have := scatFun_pgl_func_eq_val s hval h_center.choose;
  exact this.symm ▸ h_center.choose_spec.1.symm


/-
The base point `0^ω` is a center of `succMaxFun lam` (the canonical center of a pointed
gluing of a regular sequence).  (Relocated from `DiagonalForLambdaPlusOne.lean`: a generic
`succMaxFun` fact, not specific to the diagonal argument.)
-/
open ScatFun in
lemma succMaxFun_base_isCenter (lam : Ordinal.{0}) (hlam_lt : lam < omega1) :
    IsCenterFor (succMaxFun lam hlam_lt).func
      ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ := by
  apply pgl_isCenterFor_of_local;
  intro i V hV hzV
  obtain ⟨n, hn⟩ := nbhd_basis' (pgl (fun _ => maxFun lam hlam_lt)).domain ⟨zeroStream, by
    grind⟩ V hV hzV
  use fun z => ⟨prependZerosOne n z.val, by
    unfold pgl;
    unfold PointedGluingSet; aesop;⟩, fun y => stripZerosOne n y
  generalize_proofs at *;
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact Continuous.subtype_mk ( continuous_prependZerosOne n |> Continuous.comp <| continuous_subtype_val ) _;
  · intro z
    simp [pgl_func_block, stripZerosOne_prependZerosOne];
  · exact Continuous.continuousOn ( continuous_stripZerosOne n );
  · intro z; exact hn (by
    unfold nbhd';
    simp +decide only [pgl_domain, Finset.mem_range, mem_setOf_eq, prependZerosOne];
    exact fun i hi => by rw [ if_pos hi ] ; rfl;);
  · simp +decide [ mem_closure_iff ];
    refine ⟨ { y : Baire | y n = 0 }, ?_, ?_, ?_ ⟩;
    · convert isOpen_pi_iff.mpr _;
      exact fun f hf => ⟨ { n }, fun _ => { 0 }, by aesop ⟩;
    · show zeroStream n = 0; rfl;
    · simp +decide [ Set.Nonempty, pgl_func_block ];
      intro x hx; rw [ prependZerosOne_at_i ] ; simp +decide ;

open ScatFun in
/-- For the equivalence `g ≡ succMaxFun lam` with reduction data `(σ2, τ2)` witnessing
`Reduces (succMaxFun lam) g`, the map `τ2` sends the distinguished value `y0` of `g` to the
cocenter `zeroStream` of `succMaxFun lam`.  (Relocated from `DiagonalForLambdaPlusOne.lean`:
a generic cocenter-rigidity fact, not specific to the diagonal argument.) -/
lemma succMaxFun_tau_cocenter_eq (g : ScatFun) (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (y0 : Baire) (hrank : CBRank g.func = lam + 1)
    (hdist : ∀ x ∈ CBLevel g.func lam, g.func x = y0)
    (h0 : Equiv g (succMaxFun lam hlam_lt))
    (σ2 : ↑(succMaxFun lam hlam_lt).domain → ↑g.domain) (hσ2c : Continuous σ2)
    (τ2 : Baire → Baire) (hτ2c : ContinuousOn τ2 (Set.range fun a => g.func (σ2 a)))
    (heq2 : ∀ a, (succMaxFun lam hlam_lt).func a = τ2 (g.func (σ2 a))) :
    τ2 y0 = zeroStream := by
  have hequiv : ContinuouslyEquiv (succMaxFun lam hlam_lt).func g.func := ⟨h0.2, h0.1⟩
  have hf_cent : IsCentered (succMaxFun lam hlam_lt).func :=
    ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, succMaxFun_base_isCenter lam hlam_lt⟩
  have hg_cent : IsCentered g.func :=
    ⟨σ2 ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩,
      centerInvariance_equiv (succMaxFun_base_isCenter lam hlam_lt) hequiv hσ2c hτ2c heq2⟩
  have hy : cocenter g.func hg_cent = y0 :=
    cocenter_eq_distinguished g hg_cent lam hrank y0 hdist
  have hz : cocenter (succMaxFun lam hlam_lt).func hf_cent = zeroStream :=
    cocenter_pgl_eq_zeroStream (fun _ => maxFun lam hlam_lt) (scatFun_const_isRegularSeq _)
      (fun i a => by rw [maxFun_func]; rfl) hf_cent
  have key := rigidityOfCocenter_tau (succMaxFun lam hlam_lt).hScat g.hScat hf_cent hg_cent
    hequiv hσ2c hτ2c heq2
  rw [hy, hz] at key
  exact key


/-
**ℕ-indexed disjoint-union form of Proposition 2.14** (for a *restriction-closed* class
over a *nonempty* domain).  If `f : A → Baire` (with `A` nonempty) is locally in a class `F`
that is closed under restriction to clopen subsets, then there is an `ℕ`-indexed clopen
partition `(Pᵢ)` of `A` with each block in `F`.

The nonemptiness hypothesis is essential: for an empty `A` the conclusion would force a block
of the (necessarily nonempty, `ℕ`-indexed) family into `F`, but `IsLocallyInClass` is vacuous
and gives no witness.  Equivalently, this is the price of insisting on an `ℕ` index rather than
the possibly-empty index type of `locally_implies_disjoint_union_baire`.  Note also that
*centeredness* is **not** a restriction-closed class, so this lemma does not apply to it; the
centered decomposition instead uses the prefix-cylinder strengthening
`scatFun_centered_cylinder_witness`.
-/
lemma locally_implies_disjointUnion_nat {A : Set Baire} (f : A → Baire)
    (hAne : Nonempty A)
    (F : (S : Set A) → (S → Baire) → Prop)
    (hloc : IsLocallyInClass f F)
    (hF_restrict : ∀ (C D : Set A), D ⊆ C → IsClopen D →
      F C (fun a => f a.val) → F D (fun a => f a.val)) :
    ∃ P : ℕ → Set A, (∀ i, IsClopen (P i)) ∧ (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i = Set.univ) ∧ ∀ i, F (P i) (fun a => f a.val) := by
  have := @locally_implies_disjoint_union_baire A f;
  obtain ⟨I, P, fi, hP⟩ := this F hloc hF_restrict;
  obtain ⟨I_countable, hI_countable⟩ : ∃ I_countable : Set I, I_countable.Countable ∧ ⋃ i ∈ I_countable, P i = Set.univ := by
    have := hP.1.2.2;
    have := isLindelof_univ.elim_countable_subcover ( fun i => P i ) ( fun i => ( hP.1.1 i ).isOpen ) ( fun x _ => Set.mem_iUnion_of_mem ( Classical.choose ( Set.mem_iUnion.mp ( this.1.symm ▸ Set.mem_univ x ) ) ) ( Classical.choose_spec ( Set.mem_iUnion.mp ( this.1.symm ▸ Set.mem_univ x ) ) ) );
    exact ⟨ this.choose, this.choose_spec.1, Set.Subset.antisymm ( Set.subset_univ _ ) ( this.choose_spec.2 ) ⟩;
  obtain ⟨g, hg⟩ : ∃ g : ℕ → I, I_countable = Set.range g := by
    have := hI_countable.1.exists_eq_range;
    by_cases hI_empty : I_countable = ∅;
    · simp_all +decide [ Set.ext_iff ];
    · exact this <| Set.nonempty_iff_ne_empty.mpr hI_empty;
  refine ⟨ fun n => disjointed ( fun n => P ( g n ) ) n, ?_, ?_, ?_, ?_ ⟩;
  · apply_rules [ disjointed_clopen, hP.1.1 ];
    exact fun n => hP.1.1 ( g n );
  · exact fun i j hij => disjoint_disjointed _ hij;
  · convert hI_countable.2 using 1;
    rw [ hg, iUnion_disjointed ];
    simp +decide;
  · intro n;
    convert hF_restrict ( P ( g n ) ) ( disjointed ( fun n => P ( g n ) ) n ) ( disjointed_subset _ _ ) _ _ using 1;
    · exact disjointed_clopen _ ( fun n => hP.1.1 _ ) _;
    · convert hP.2 ( g n ) using 1;
      exact funext fun x => hP.1.2.2.2 ( g n ) x


/-
**Domain-partition gluing reduction.**  If `(Pᵢ)` is a countable clopen partition of
`g.domain`, then `g` reduces to the plain gluing `gl (fun i => g.restrict (Pᵢ))` of its
blocks (keeping the block index in the codomain).
-/
lemma scatFun_reduces_gl_of_domain_partition (g : ScatFun) (P : ℕ → Set ↑g.domain)
    (hdu : g.IsDisjointUnion P) :
    ScatFun.Reduces g (ScatFun.gl (fun i => g.restrict (P i))) := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ prepend ( partitionIndex P hdu.2.2 x ) x.val, by
    apply mem_gluingSet_prepend;
    convert partitionIndex_mem P hdu.2.2 x using 1;
    simp +decide [ ScatFun.restrict ] ⟩;
  · refine Continuous.subtype_mk ?_ ?_;
    refine continuous_pi fun n => ?_;
    by_cases hn : n = 0;
    · convert partitionIndex_locallyConstant P hdu.1 hdu.2.1 hdu.2.2 using 1;
      · ext;
        constructor <;> intro h <;> rw [ continuous_def ] at * <;> aesop;
      · exact funext fun x => by simp +decide [ hn, prepend ] ;
    · simp +decide [ hn, prepend ];
      exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val;
  · refine ⟨ unprepend, ?_, ?_ ⟩;
    · exact continuous_unprepend.continuousOn;
    · intro x
      simp only [ScatFun.gl];
      convert rfl


/-
**Diagonal upper piece `C₀ ≤ ℓ_λ`.**  The "super-diagonal" set
`C₀ = ⋃ᵢ (Aᵢ ∩ {g.func ∈ ⋃_{j<i} ray j})` avoids the `y`-fibre (every point maps into some ray,
so `≠ y`); since `g` is constant `= y` on its top CB-level `CBLevel g lam`, that top level is
empty on `C₀`, so `CBRank (g│_{C₀}) ≤ lam` and `g│_{C₀}` reduces to `ℓ_λ = maxFun lam`.
-/
lemma caseB_C0_reduces_maxFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (g : ScatFun) (y : Baire)
    (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (A : ℕ → Set ↑g.domain) (hdu : g.IsDisjointUnion A) :
    ScatFun.Reduces
      (g.restrict (⋃ i, A i ∩
        {z : ↑g.domain | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j}))
      (ScatFun.maxFun lam hlam_lt) := by
  have h_empty_level : CBLevel (g.restrict (⋃ i, A i ∩ {z : ↑g.domain | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j})).func lam = ∅ := by
    ext w;
    simp +zetaDelta only [Subtype.forall, mem_empty_iff_false, iff_false] at *;
    intro hw;
    have := cbLevel_block_iff g ( ⋃ i, A i ∩ { z : ↑g.domain | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j } ) ( by
      refine isOpen_iUnion fun i => IsOpen.inter ( hdu.1 i |>.2 ) ?_;
      refine' g.hCont.isOpen_preimage _ _;
      exact isOpen_biUnion fun j hj => isClopen_raySet y j |>.2 ) lam w;
    have := hconst _ _ ( this.mp hw );
    have := w.2;
    simp_all +decide [ Set.mem_iUnion ];
    obtain ⟨ i, hi ⟩ := this;
    simp_all +decide [ RaySet ];
  have h_rank_le : ∀ β, lam ≤ β → CBLevel (g.restrict (⋃ i, A i ∩ {z : ↑g.domain | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j})).func β = ∅ := by
    exact fun β hβ => Set.eq_empty_of_subset_empty <| CBLevel_antitone _ hβ |> Set.Subset.trans <| h_empty_level.le;
  have := maxFun_is_maximum lam hlam_lt;
  exact this.1 _ (ScatFun.restrict _ _).hCont (ScatFun.restrict _ _).hScat h_rank_le

end
