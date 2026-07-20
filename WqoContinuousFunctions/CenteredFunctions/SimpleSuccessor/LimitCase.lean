import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.Shared

/-!
# §4.3 — Theorem 4.12, λ a non-zero limit (Case B diagonal)

Extracted from `SimpleSuccessorOfLimit.lean`.  The limit-only diagonal: rays `< λ`,
`twoBQO_levelLT_succ`, and the equivalence `simple_caseB_equiv_Gl`.
-/

open scoped Topology ScatFun
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section


/-
**Case B, lower bound `k_{λ+1} ⊕ ℓ_λ ≤ g`.**  Using a *single* rank-`lam` ray
`W = RaySet univ y N` (clopen codomain piece), `g` is the codomain gluing of `g│_{Wᶜ}` and
`g│_W`.  Here `k_{λ+1} = minFun ≤ g│_{Wᶜ}` (the minimum reduces into the corestriction, whose
top CB-level survives), and `ℓ_λ = maxFun ≤ g│_W` (the ray has rank `lam`, so is `≡ ℓ_λ` for
limit `lam`).  Block-monotonicity of `gl` then gives `gl ![k, ℓ] = k ⊕ ℓ ≤ g`.

This direction needs only *one* top-rank ray, so it is valid even when there are infinitely
many top-rank rays.
-/
lemma simple_caseB_Gl_reduces_g (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam)
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam)
    (hJne : ∃ N, lam ≤ CBRank (g.rayOn y Set.univ N).func) :
    ScatFun.Reduces
      (ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt) g := by
  obtain ⟨N, hN⟩ := hJne
  set W : Set Baire := RaySet Set.univ y N
  set B : ℕ → Set Baire := fun i => if i = 0 then Wᶜ else if i = 1 then W else (∅ : Set Baire);
  have h_equiv : ScatFun.Equiv g (ScatFun.gl (fun i => Fb g B i)) := by
    apply equiv_gl_of_codomain_clopen_partition g (fun i => Fb g B i) B (by
    simp +zetaDelta only [Ordinal.add_one_eq_succ, Subtype.forall] at *;
    intro i; split_ifs <;> [ exact IsClopen.compl ( isClopen_raySet y N ) ; exact isClopen_raySet y N; exact isClopen_empty ] ;) (by
    grind +qlia) (by
    ext x; simp [B, W];
    exact ⟨ if x ∈ RaySet univ y N then 1 else 0, by aesop ⟩) (by
    intro i; exact (by
    exact Fb_func_eq g B i ▸ ContinuouslyEquiv.refl _););
  have h_red : ∀ i, ScatFun.Reduces (ScatFun.copiesSeq ![ScatFun.minFun lam hlam_lt, ScatFun.maxFun lam hlam_lt] ![1, 1] i) (Fb g B i) := by
    intro i
    rcases i with ( _ | _ | i ) <;> simp_all +decide [ ScatFun.copiesSeq ];
    · obtain ⟨ x₀, hx₀ ⟩ := simple_lam_data lam g hg_rank hg_simple |>.1;
      convert minFun_is_minimum lam hlam_lt ( Fb g B 0 |> ScatFun.domain ) ( Fb g B 0 |> ScatFun.func ) ( Fb g B 0 |> ScatFun.hCont ) ( Fb g B 0 |> ScatFun.hScat ) _ using 1;
      use ⟨x₀, by
        simp +zetaDelta only at *;
        simp +decide only [Fb, ↓reduceIte, RaySet, mem_univ, ne_eq, true_and, mem_compl_iff, mem_setOf_eq, not_and, Decidable.not_not];
        simp +decide [ ScatFun.restrict, hconst _ x₀.2 hx₀ ]⟩
      generalize_proofs at *;
      convert cbLevel_block_iff g { z : g.domain | g.func z ∈ Wᶜ } _ lam ⟨ x₀, by assumption ⟩ |>.2 hx₀ using 1;
      exact IsOpen.preimage ( g.hCont ) ( isClopen_raySet y N |> IsClopen.compl |> IsClopen.isOpen );
    · convert limit_rank_equiv_maxFun ( g.rayOn y Set.univ N ) lam hlam_lt hlim ( le_antisymm ( hray_le N ) hN ) |> fun h => h.2 using 1;
      exact rayOn_eq_corestrict g y N ▸ rfl;
    · convert ScatFun.empty_reduces _ using 1;
  have h_red_gl : ScatFun.Reduces (ScatFun.gl (ScatFun.copiesSeq ![ScatFun.minFun lam hlam_lt, ScatFun.maxFun lam hlam_lt] ![1, 1])) (ScatFun.gl (fun i => Fb g B i)) := by
    grind [ScatFun.gl_reduces_of_pointwise];
  exact h_red_gl.trans h_equiv.2


/-! ### 2-BQO propagation `𝒞_{<λ} → 𝒞_{≤λ}` (one successor step)

The diagonal argument's prerequisite — decomposing `g` (rank `λ+1`) into centered blocks via
Thm 4.7 (`localCenterednessFromTwoBQO_scatFun`) — needs 2-BQO *at level `λ+1`*
(`TwoBQO (LevelLT.reduces (λ+1))`, i.e. on rank `≤ λ`), whereas Theorem 4.12 only hands us
2-BQO at level `λ` (rank `< λ`).  The memoir bridges this with the General Structure Theorem:
"≤ is bqo on `𝒞_{<λ}`, hence on `𝒞_{≤λ}`".

The two general facts used — `TwoBQO.union` (union of two 2-BQO parts) and
`TwoBQO.of_finite_coloring` (finite up-to-equivalence ⟹ 2-BQO) — live in `BQO/TwoBQO.lean`.
Here we only assemble the `ScatFun` instance. -/

/-- **2-BQO propagates across one successor at a non-zero limit `λ`.**
`𝒞_{<λ} → 𝒞_{≤λ} = 𝒞_{<λ+1}`.  Every rank-exactly-`λ` function is `≡ ℓ_λ` so `Level λ` is a
single `≡`-class, hence 2-BQO by `of_finite_coloring`; `LevelLE λ = LevelLT λ ∪ Level λ` is then
2-BQO by `union`.  Feeds `localCenterednessFromTwoBQO_scatFun` at `λ+1` to decompose a
rank-`λ+1` function into centered blocks. -/
lemma twoBQO_levelLT_succ (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam)) :
    TwoBQO (ScatFun.LevelLT.reduces (lam + 1)) := by
  -- `Level λ` (rank = λ) is one ≡-class: all such functions are `≡ ℓ_λ`.
  have hLevel : TwoBQO (ScatFun.Level.reduces lam) :=
    TwoBQO.of_finite_coloring (ScatFun.Level.reduces lam) (fun _ => (0 : Fin 1))
      (fun a b _ => ContinuouslyReduces.trans
        (limit_rank_equiv_maxFun a.val lam hlam_lt hlim a.prop).1
        (limit_rank_equiv_maxFun b.val lam hlam_lt hlim b.prop).2)
  -- `LevelLE λ = (rank < λ) ∪ (rank = λ)`, both parts 2-BQO.
  have hLE : TwoBQO (ScatFun.LevelLE.reduces lam) :=
    TwoBQO.union (ScatFun.LevelLE.reduces lam)
      (fun F => CBRank F.val.func < lam) (fun F => CBRank F.val.func = lam)
      (fun F => lt_or_eq_of_le F.prop)
      (hbqo.comap (fun F : {x : ScatFun.LevelLE lam // CBRank x.val.func < lam} =>
        ⟨F.val.val, F.prop⟩))
      (hLevel.comap (fun F : {x : ScatFun.LevelLE lam // CBRank x.val.func = lam} =>
        ⟨F.val.val, F.prop⟩))
  -- `LevelLT (λ+1) ↪ LevelLE λ` since `rank < λ+1 ↔ rank ≤ λ`.
  exact hLE.comap (fun F : ScatFun.LevelLT (lam + 1) => ⟨F.val,
    Order.lt_succ_iff.mp (by rw [← Ordinal.add_one_eq_succ]; exact F.prop)⟩)


/-
**Strict finite-union bound on CB-rank.**  If every ray of `g` at `y` has CB-rank
`< lam` (and `lam ≠ 0`), then the corestriction of `g` to a *finite* union of rays
has CB-rank `< lam`.  This is the strict analogue of `cbRank_corestrict_W_le`.
-/
lemma cbRank_corestrict_W_lt (g : ScatFun) (y : Baire) (lam : Ordinal.{0})
    (hlam_ne : lam ≠ 0)
    (hray_lt : ∀ n, CBRank (g.rayOn y Set.univ n).func < lam)
    (Jf : Finset ℕ) :
    CBRank (g.restrict {z : ↑g.domain | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func
      < lam := by
  by_contra h_contra;
  have h_sup_lt : ⨆ n, CBRank ((g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).rayOn y Set.univ n).func < lam := by
    have h_sup_lt : ∀ n, CBRank ((g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).rayOn y Set.univ n).func ≤ CBRank (g.rayOn y Set.univ n).func := by
      intro n;
      apply_rules [ ContinuouslyReduces.rank_monotone, corestrict_rayOn_reduces ]; all_goals grind [ScatFun.hScat];
    have h_sup_lt : ∀ n ∉ Jf, CBRank ((g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).rayOn y Set.univ n).func = 0 := by
      intro n hn_not_in_Jf
      have h_empty : {z : ↑(g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).domain | (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).func z ∈ RaySet Set.univ y n} = ∅ := by
        ext z
        simp only [RaySet, ne_eq, mem_univ, true_and, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, Decidable.not_not];
        intro hz; have := z.2; simp_all +decide [ Set.mem_iUnion ] ;
        obtain ⟨ i, hi, hi' ⟩ := this.2; simp_all +decide [ RaySet ] ;
        grind [restrict_func_eq];
      simp_all +decide [ ScatFun.rayOn ];
      rw [ show ( univ ∩ { a : ↑ ( g.restrict { z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n } ).domain | ( g.restrict { z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n } ).func a ∈ RaySet univ y n } ) = ∅ by simpa [ Set.ext_iff ] using h_empty ];
      unfold ScatFun.restrict; simp +decide [ CBRank ] ;
      unfold CBLevel; simp +decide [ Set.ext_iff ] ;
    have h_sup_lt : ⨆ n, CBRank ((g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).rayOn y Set.univ n).func ≤ Jf.sup (fun n => CBRank (g.rayOn y Set.univ n).func) := by
      apply ciSup_le;
      intro n; by_cases hn : n ∈ Jf <;> simp_all +decide ;
      exact le_trans ( by solve_by_elim ) ( Finset.le_sup ( f := fun n => CBRank ( g.rayOn y univ n ).func ) hn );
    refine lt_of_le_of_lt h_sup_lt ?_;
    rw [ Finset.sup_lt_iff ];
    · exact fun n hn => hray_lt n;
    · exact lt_of_le_of_ne bot_le hlam_ne.symm;
  refine h_contra <| lt_of_le_of_lt ?_ h_sup_lt;
  apply le_of_eq;
  apply cbRank_eq_iSup_restrict;
  constructor <;> simp +decide [ Set.ext_iff ];
  · intro n; exact (by
    convert isClopen_raySet y n |> IsClopen.preimage <| show Continuous fun a : ↥(g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).domain => (g.restrict {z | g.func z ∈ ⋃ n ∈ Jf, RaySet univ y n}).func a from ?_ using 1;
    exact (g.restrict _).hCont);
  · simp +decide [ Set.disjoint_left, RaySet ];
    constructor <;> intros <;> simp_all +decide [ ScatFun.restrict ];
    · grind;
    · rename_i x hx;
      obtain ⟨ i, hi, hi' ⟩ := hx.2;
      use i;
      convert hi' using 1


/-
The CB-rank of the `j`-th `rayOn`-ray of `G` at `y` (over `univ`) equals the CB-rank of
the `RayFun` form of the same ray (their domains agree by `RaySet` membership).
-/
lemma rayOn_cbRank_eq_rayFun (G : ScatFun) (y : Baire) (j : ℕ) :
    CBRank (G.rayOn y Set.univ j).func = CBRank (RayFun G.func y j) := by
  -- By definition of `rayOn`, we have `G.rayOn y univ j = G.restrict {z | G.func z ∈ RaySet Set.univ y j}`.
  have h_rayOn_def : G.rayOn y Set.univ j = G.restrict {z : ↑G.domain | G.func z ∈ RaySet Set.univ y j} := by
    exact rayOn_eq_corestrict G y j;
  rw [ h_rayOn_def, cbRank_restrict_eq ];
  convert CBRank_comp_homeomorph _ _;
  swap;
  refine Homeomorph.setCongr ?_;
  all_goals norm_num [ Set.ext_iff, RaySet ];
  congr! 1


/-
**Rays of a pointed gluing (at `zeroStream`) inherit the block CB-ranks.**  If every
block `s i` has CB-rank `< lam`, then every `rayOn`-ray of `pgl s` at `zeroStream` has
CB-rank `< lam`.
-/
lemma pgl_rayOn_zeroStream_cbRank_lt (s : ℕ → ScatFun) (lam : Ordinal.{0})
    (hs_lt : ∀ i, CBRank (s i).func < lam) :
    ∀ j, CBRank ((ScatFun.pgl s).rayOn zeroStream Set.univ j).func < lam := by
  intro j;
  convert hs_lt j using 1;
  convert rayOn_cbRank_eq_rayFun _ _ _;
  rw [ ← cbRank_rayFun_pgl s j ]


/-
**Rigidity of the cocenter, rank form.**  A centered scattered function `F` of CB-rank
`λ+1` (`λ` a non-zero limit) that is *not* above the maximum `pgl ℓ_λ` has all its rays at
the distinguished point `y` (which is forced to be its cocenter) of CB-rank `< λ`.

## Provided solution

By `centeredSuccessor` (`λ` limit case) `F ≡ k_{λ+1}` or `F ≡ pgl ℓ_λ`; the latter would give
`pgl ℓ_λ ≤ F` (`hnotmax`), so `F ≡ k_{λ+1} = minFun lam`.  Its cocenter is `y` (the value on
the top CB-level `CBLevel F lam`).  By `rigidityOfCocenter_finiteGluing` applied to
`F ≡ minFun lam`, each ray `Ray(F, y, n)` reduces to a *finite* gluing `⊔_{i=m}^{M}` of rays
of `minFun lam` at its cocenter; those rays each have rank `< λ` (canonical pgl form of
`minFun lam`, `minFun_limit_equiv_pgl` + `cbRank_rayFun_pgl`), and a finite gluing of `< λ`
ranks has rank `< λ` (`λ` limit).  Hence `CBRank (Ray(F, y, n)) < λ` by rank monotonicity.
-/
lemma centered_lamPlusOne_rayOn_lt
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (F : ScatFun) (hF_rank : CBRank F.func = lam + 1) (hF_cent : IsCentered F.func)
    (y : Baire) (hy : ∀ a ∈ CBLevel F.func lam, F.func a = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) F) :
    ∀ n, CBRank (F.rayOn y Set.univ n).func < lam := by
  have hFmin : ScatFun.Equiv F (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))) := by
    -- Apply the lemma `centeredSuccessor` to conclude that F is equivalent to either the minimum function or the successor maximum function.
    have hFmin_or_succMax : ScatFun.Equiv F (ScatFun.minFun lam hlam_lt) ∨ ScatFun.Equiv F (ScatFun.succMaxFun lam hlam_lt) := by
      apply centeredSuccessor lam hlam_lt (Or.inr ⟨hlim, hlam_ne⟩) F hF_rank hF_cent
    generalize_proofs at *; (
    obtain h | h := hFmin_or_succMax <;> simp_all +decide [ ScatFun.Equiv ];
    exact ⟨ h.1.trans ( minFun_limit_equiv_pgl lam hlam_lt hlim hlam_ne |>.1 ), ( minFun_limit_equiv_pgl lam hlam_lt hlim hlam_ne |>.2 ).trans h.2 ⟩);
  have hcoc_pgl : cocenter (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))).func (pgl_isCentered_of_regular (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt)) (minFun_cofinalSeq_isRegularSeq lam hlam_lt hlim hlam_ne)) = zeroStream := by
    apply cocenter_pgl_eq_zeroStream;
    · exact minFun_cofinalSeq_isRegularSeq lam hlam_lt hlim hlam_ne;
    · exact fun i a => rfl;
  have hcoc_F : cocenter F.func hF_cent = y := by
    apply cocenter_eq_distinguished F hF_cent lam hF_rank y hy;
  intro n
  obtain ⟨I, hI_disj, hI_red⟩ := rigidityOfCocenter_reducibleByPieces F (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))) hF_cent (pgl_isCentered_of_regular (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt)) (minFun_cofinalSeq_isRegularSeq lam hlam_lt hlim hlam_ne)) (by
  exact ⟨ hFmin.1, hFmin.2 ⟩);
  have hCBRank_Ffun : CBRank (F.rayOn y Set.univ n).func ≤ CBRank ((ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))).restrict {a : ↑(ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))).domain | (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))).func a ∈ ⋃ i ∈ I n, RaySet Set.univ zeroStream i}).func := by
    convert ContinuouslyReduces.rank_monotone _ _ ( hI_red n ) using 1;
    · convert rayOn_cbRank_eq_rayFun F y n using 1;
      unfold RayFun; aesop;
    · convert cbRank_restrict_eq _ _ using 1;
      convert rfl;
      · simp +decide [ RaySet, hcoc_pgl ];
        exact ⟨ fun ⟨ i, hi₁, hi₂, hi₃ ⟩ => ⟨ i, hi₂, hi₁, hi₃ ⟩, fun ⟨ i, hi₂, hi₁, hi₃ ⟩ => ⟨ i, hi₁, hi₂, hi₃ ⟩ ⟩;
      · simp +decide [ RaySet, hcoc_pgl ];
        exact ⟨ fun ⟨ i, hi₁, hi₂, hi₃ ⟩ => ⟨ i, hi₂, hi₁, hi₃ ⟩, fun ⟨ i, hi₂, hi₁, hi₃ ⟩ => ⟨ i, hi₁, hi₂, hi₃ ⟩ ⟩;
      · simp +decide [ RaySet, hcoc_pgl ];
        exact ⟨ fun ⟨ i, hi₁, hi₂, hi₃ ⟩ => ⟨ i, hi₂, hi₁, hi₃ ⟩, fun ⟨ i, hi₂, hi₁, hi₃ ⟩ => ⟨ i, hi₁, hi₂, hi₃ ⟩ ⟩;
    · exact scattered_restrict _ F.hScat _;
    · exact scattered_restrict _ ( ScatFun.pgl _ |> ScatFun.hScat ) _;
  refine lt_of_le_of_lt hCBRank_Ffun ?_;
  apply cbRank_corestrict_W_lt;
  · exact hlam_ne;
  · apply pgl_rayOn_zeroStream_cbRank_lt;
    intro i
    have hCBRank_minFun : CBRank (ScatFun.minFun (cofinalSeq lam i) (lt_trans (cofinalSeq_lt lam hlim hlam_ne i) hlam_lt)).func = Order.succ (cofinalSeq lam i) := by
      apply minFun_cbRank_eq;
    exact hCBRank_minFun.symm ▸ hlim.succ_lt ( cofinalSeq_lt lam hlim hlam_ne i )


/-
CB-rank of a restricted ray is invariant under re-realizing the restriction:
the `j`-th ray of the block `g│_C` (computed over `univ`) has the same CB-rank as the
`j`-th ray of `g` taken over the set `C`.
-/
lemma rayOn_restrict_cbRank_eq (g : ScatFun) (y : Baire) (C : Set ↑g.domain) (j : ℕ) :
    CBRank ((g.restrict C).rayOn y Set.univ j).func = CBRank (g.rayOn y C j).func := by
  rw [ScatFun.rayOn, ScatFun.rayOn];
  unfold ScatFun.restrict;
  unfold ScatFun.restrictEquiv;
  simp +decide only [coe_setOf, mem_setOf_eq, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, RaySet, ne_eq, comp_apply];
  convert CBRank_comp_homeomorph _ _ using 2;
  rotate_left;
  refine ⟨ ?_, ?_, ?_ ⟩;
  refine ⟨ fun x => ⟨ x.val, ?_ ⟩, fun x => ⟨ x.val, ?_ ⟩, ?_, ?_ ⟩;
  all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
  grind;
  exact ⟨ ⟨ x.2.1, x.2.2.1 ⟩, x.2.2.2.2.1, x.2.2.2.2.2 ⟩;
  · fun_prop;
  · fun_prop;
  · grind +splitImp


/-
On a clopen set `C` carrying a centered restriction of `g`, every restricted ray
`g.rayOn y C j` has CB-rank `< λ`.

## Provided solution

Let `H = g│_C` (centered by `hcent`, transported across `restrictEquiv`).  Its rank is
`≤ λ+1`.  If `CBRank H < λ+1` then, `H` being centered, its rank is a successor `≤ λ`, hence
`< λ` (`λ` limit); every restricted ray `g.rayOn y C j` reduces to `H` (`restrict_le_self`,
`restrict_reduces_of_subset`), so has rank `< λ`.  If `CBRank H = λ+1`, then `H ≤ g` gives
`¬ pgl ℓ_λ ≤ H`, the top CB-level of `H` embeds in that of `g` (where `g = y`) so `H`'s
distinguished point is `y`, and `centered_lamPlusOne_rayOn_lt` bounds `H`'s rays;
`rayOn_restrict_cbRank_eq` transports the bound to `g.rayOn y C j`.
-/
lemma caseB_block_rayOn_lt
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g)
    (C : Set ↑g.domain) (hC : IsOpen C)
    (hcent : IsCentered (g.func ∘ (Subtype.val : ↥C → ↑g.domain))) :
    ∀ j, CBRank (g.rayOn y C j).func < lam := by
  -- Set `H := g.restrict C`. Note `H.func = (g.func ∘ Subtype.val) ∘ (g.restrictEquiv C)`, so `hH_cent : IsCentered H.func` follows from `hcent` by `IsCentered_comp_homeomorph` (composition with the homeomorphism `g.restrictEquiv C`).
  set H := g.restrict C
  have hH_cent : IsCentered H.func := by
    convert hcent using 1;
    convert IsCentered_comp_homeomorph ( g.restrictEquiv C ) ( g.func ∘ Subtype.val ) using 1;
  -- `H` reduces to `g`: `hHg : ScatFun.Reduces H g := restrict_le_self g C`. Hence `CBRank H.func ≤ CBRank g.func = lam + 1` by `ContinuouslyReduces.rank_monotone H.hScat g.hScat hHg`.
  have hH_rank_le : CBRank H.func ≤ lam + 1 := by
    convert ContinuouslyReduces.rank_monotone H.hScat g.hScat (restrict_le_self g C) using 1;
    exact hg_rank.symm;
  -- Since `H` is centered, `centered_scatFun_rank_succ H hH_cent` gives `β` with `CBRank H.func = β + 1`.
  obtain ⟨β, hβ⟩ : ∃ β, CBRank H.func = β + 1 := centered_scatFun_rank_succ H hH_cent;
  cases lt_or_eq_of_le ( show β ≤ lam from by
                          aesop ) <;> simp_all +decide ;
  · -- Since `β < lam`, we have `CBRank H.func = β + 1 < lam`.
    have hH_rank_lt : CBRank H.func < lam := by
      exact hβ.symm ▸ hlim.succ_lt ‹_›;
    -- The ray `g.rayOn y C j = g.restrict (C ∩ {a | g.func a ∈ RaySet Set.univ y j})` (by `ScatFun.rayOn`), and `C ∩ {…} ⊆ C`, so `ScatFun.Reduces (g.rayOn y C j) H` by `restrict_reduces_of_subset g (Set.inter_subset_left)` (after rewriting `rayOn`).
    have h_ray_reduces_H : ∀ j, ScatFun.Reduces (g.rayOn y C j) H := by
      intro j;
      convert restrict_reduces_of_subset g ( Set.inter_subset_left ) using 1;
    exact fun j => lt_of_le_of_lt ( ContinuouslyReduces.rank_monotone ( g.rayOn y C j |> ScatFun.hScat ) H.hScat ( h_ray_reduces_H j ) ) hH_rank_lt;
  · --Establish `hH_notmax` and `hH_const`.
    have hH_notmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) H := by
      contrapose! hnotmax;
      exact hnotmax.trans ( restrict_le_self g C )
    have hH_const : ∀ a ∈ CBLevel H.func lam, H.func a = y := by
      intro a ha; specialize hconst ( g.restrictEquiv C a ) ; simp_all +decide ;
      exact hconst ( by simpa using cbLevel_block_iff g C hC lam a |>.1 ha );
    convert centered_lamPlusOne_rayOn_lt lam hlam_lt hlim hlam_ne H hβ hH_cent y hH_const hH_notmax using 1;
    rw [ rayOn_restrict_cbRank_eq ]


/-
**Local membership in the bounded-ray class.**  Every point of `g.domain` has a clopen
cylinder neighbourhood on which all restricted rays of `g` (at `y`) have CB-rank `< λ`.

## Provided solution

`twoBQO_levelLT_succ` upgrades the `λ`-level 2-BQO to `λ+1`; `scatFun_centered_cylinder_witness`
then yields, for each `x`, a (clopen) cylinder `g.cyl x n` on which `g` is centered; conclude
with `caseB_block_rayOn_lt`.
-/
lemma caseB_local_in_class
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g) :
    IsLocallyInClass g.func
      (fun (C : Set ↑g.domain) (_ : ↥C → Baire) =>
        ∀ j, CBRank (g.rayOn y C j).func < lam) := by
  intro x;
  -- By `scatFun_centered_cylinder_witness (lam + 1) hsucc_lt hbqo' g hg_rank x` obtain `n` with `hn : IsCentered (g.func ∘ (Subtype.val : ↥(g.cyl x n) → ↑g.domain))`.
  obtain ⟨n, hn⟩ : ∃ n, IsCentered (g.func ∘ (Subtype.val : ↥(g.cyl x n) → ↑g.domain)) := by
    convert scatFun_centered_cylinder_witness ( lam + 1 ) _ _ g hg_rank x;
    · convert omega1_add_nat lam hlam_lt 1 using 1;
      norm_num;
    · exact twoBQO_levelLT_succ lam hlam_lt hlim hbqo;
  refine ⟨ g.cyl x n, ?_, ?_, ?_ ⟩;
  · convert baire_nbhd'_isClopen g.domain x n using 1;
  · exact g.mem_cyl x n;
  · apply caseB_block_rayOn_lt lam hlam_lt hlim hlam_ne g hg_rank y hconst hnotmax (g.cyl x n) (g.cyl_isOpen x n) hn


/-
**Case-B block decomposition.**  There is a countable clopen partition `(Aᵢ)` of
`g.domain` such that every restricted ray `g.rayOn y (Aᵢ) j` has CB-rank `< λ`.

## Provided solution

The class `F C _ := ∀ j, CBRank (g.rayOn y C j) < λ` is closed under restriction to clopen
subsets (rays only shrink as the domain set shrinks), so `caseB_local_in_class` +
`locally_implies_disjoint_union_baire` give the partition.  The domain is nonempty (rank
`λ+1 > 0`), so the index type is `ℕ`.
-/
lemma caseB_decomposition
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g) :
    ∃ A : ℕ → Set ↑g.domain, g.IsDisjointUnion A ∧
      ∀ i j, CBRank (g.rayOn y (A i) j).func < lam := by
  convert locally_implies_disjointUnion_nat g.func _ _ _ _ using 1;
  rotate_left;
  rotate_left;
  use fun C _ => ∀ j, CBRank ( g.rayOn y C j ).func < lam;
  · apply caseB_local_in_class lam hlam_lt hlim hlam_ne hbqo g hg_rank y hconst hnotmax;
  · exact fun C D hCD hD hC j => lt_of_le_of_lt ( rayOn_cbRank_mono g y hCD j ) ( hC j );
  · exact Set.ext fun x => ⟨ fun hx => ⟨ hx.1.1, hx.1.2.1, hx.1.2.2, hx.2 ⟩, fun hx => ⟨ ⟨ hx.1, hx.2.1, hx.2.2.1 ⟩, hx.2.2.2 ⟩ ⟩;
  · have h_nonempty : (CBLevel g.func 0).Nonempty := by
      apply CBLevel_nonempty_below_rank g.func g.hScat 0;
      exact hg_rank.symm ▸ Ordinal.succ_pos _;
    exact ⟨ h_nonempty.some, h_nonempty.choose_spec |> fun h => by simp ⟩


/-
**Restrict-of-restrict realization** (for `U ⊆ T`).  Restricting `g│_T` to the points whose
`g`-realization lies in `U ⊆ T` reduces to `g│_U` (both evaluate to `g` on the same underlying
points).  The hypothesis `U ⊆ T` is essential: in general the source is `g│_{U ∩ T}`, which only
coincides with `g│_U` when `U ⊆ T`.
-/
lemma restrict_restrict_realize_reduces (g : ScatFun) (T U : Set ↑g.domain) (_hUT : U ⊆ T) :
    ScatFun.Reduces
      ((g.restrict T).restrict
        {w : ↑(g.restrict T).domain | (g.restrictEquiv T w : ↑g.domain) ∈ U})
      (g.restrict U) := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  refine fun x => ⟨ x.val, ?_ ⟩;
  exact ⟨ x.2.1.1, by simpa using x.2.2 ⟩;
  · fun_prop;
  · refine ⟨ fun x => x, continuousOn_id, ?_ ⟩;
    simp +decide [ ScatFun.restrict, ScatFun.restrictEquiv ]

/-
**Restrict-of-restrict realization, reverse direction** (for `U ⊆ T`).  The companion to
`restrict_restrict_realize_reduces`: `g│_U` reduces back to `(g│_T)│_{...∈U}`. Combined, the
two give a genuine `Equiv` between the doubly-restricted function and the plain restriction.
-/
lemma restrict_reduces_restrict_restrict (g : ScatFun) (T U : Set ↑g.domain) (hUT : U ⊆ T) :
    ScatFun.Reduces (g.restrict U)
      ((g.restrict T).restrict
        {w : ↑(g.restrict T).domain | (g.restrictEquiv T w : ↑g.domain) ∈ U}) := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  refine fun x => ⟨ x.val, ⟨ x.2.choose, hUT x.2.choose_spec ⟩, ?_ ⟩;
  · simp +decide [ ScatFun.restrictEquiv ]
    exact x.2.choose_spec
  · fun_prop;
  · refine ⟨ fun x => x, continuousOn_id, ?_ ⟩;
    simp +decide [ ScatFun.restrict, ScatFun.restrictEquiv ]

/-- The doubly-restricted `(g│_T)│_{...∈U}` and the plain restriction `g│_U` are `Equiv`
(given `U ⊆ T`), by combining the two directions above. -/
lemma equiv_restrict_restrict_of_subset (g : ScatFun) (T U : Set ↑g.domain) (hUT : U ⊆ T) :
    ScatFun.Equiv
      ((g.restrict T).restrict
        {w : ↑(g.restrict T).domain | (g.restrictEquiv T w : ↑g.domain) ∈ U})
      (g.restrict U) :=
  ⟨restrict_restrict_realize_reduces g T U hUT, restrict_reduces_restrict_restrict g T U hUT⟩


/-
**Strict finite-union bound on CB-rank, domain-block form.**  If `(Sᵢ)` is a clopen,
pairwise-disjoint family of subsets of `g.domain` with every block `g│_{Sᵢ}` of CB-rank
`< lam` (and `lam ≠ 0`), then the restriction of `g` to any *finite* sub-union has CB-rank
`< lam`.
-/
lemma cbRank_restrict_iUnion_finset_lt (g : ScatFun) (lam : Ordinal.{0}) (hlam_ne : lam ≠ 0)
    (S : ℕ → Set ↑g.domain) (hcl : ∀ i, IsClopen (S i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (S i) (S i'))
    (hlt : ∀ i, CBRank (g.restrict (S i)).func < lam) (J : Finset ℕ) :
    CBRank (g.restrict (⋃ i ∈ J, S i)).func < lam := by
  by_contra h_contra;
  -- Apply `cbRank_eq_iSup_restrict` to `g.restrict (⋃ i ∈ J, S i)` with the ℕ-indexed partition `Q i := {w : ↑(g.restrict (⋃ i ∈ J, S i)).domain | (g.restrictEquiv (⋃ i ∈ J, S i) w : ↑g.domain) ∈ S i}`.
  have hQ_partition : (g.restrict (⋃ i ∈ J, S i)).IsDisjointUnion (fun i => {w : ↑(g.restrict (⋃ i ∈ J, S i)).domain | (g.restrictEquiv (⋃ i ∈ J, S i) w : ↑g.domain) ∈ S i}) := by
    constructor;
    · intro i;
      convert IsClopen.preimage ( hcl i ) ( continuous_subtype_val.comp ( g.restrictEquiv ( ⋃ i ∈ J, S i ) |> Homeomorph.continuous ) ) using 1;
    · simp_all +decide [ Set.ext_iff, Set.disjoint_left ];
      constructor;
      · grind;
      · intro a ha; have := ha; simp_all +decide [ ScatFun.restrictEquiv ] ;
        exact Exists.elim ( Set.mem_iUnion₂.mp ha.2 ) fun i hi => ⟨ i, hi.2 ⟩;
  have hQ_bound : ∀ i, CBRank ((g.restrict (⋃ i ∈ J, S i)).restrict {w : ↑(g.restrict (⋃ i ∈ J, S i)).domain | (g.restrictEquiv (⋃ i ∈ J, S i) w : ↑g.domain) ∈ S i}).func ≤ if i ∈ J then CBRank (g.restrict (S i)).func else 0 := by
    intro i
    by_cases hi : i ∈ J;
    · convert restrict_restrict_realize_reduces g ( ⋃ i ∈ J, S i ) ( S i ) _ |> fun h => h.rank_monotone using 1;
      · grind [ScatFun.hScat];
      · exact Set.subset_iUnion₂_of_subset i hi ( Set.Subset.refl _ );
    · have h_empty : {w : ↑(g.restrict (⋃ i ∈ J, S i)).domain | (g.restrictEquiv (⋃ i ∈ J, S i) w : ↑g.domain) ∈ S i} = ∅ := by
        ext w
        simp only [coe_setOf, mem_setOf_eq, mem_empty_iff_false, iff_false];
        intro hw;
        have := w.2;
        simp_all +decide [ ScatFun.restrict ];
        obtain ⟨ h, j, hj, hj' ⟩ := this; specialize hdisj i j; simp_all +decide [ Set.disjoint_left ] ;
        exact hdisj ( by rintro rfl; exact hi hj ) _ h hw hj';
      grind [CBRank_le_of_CBLevel_empty, cbLevel_block_iff];
  have hQ_sup_bound : ⨆ i, CBRank ((g.restrict (⋃ i ∈ J, S i)).restrict {w : ↑(g.restrict (⋃ i ∈ J, S i)).domain | (g.restrictEquiv (⋃ i ∈ J, S i) w : ↑g.domain) ∈ S i}).func < lam := by
    refine' lt_of_le_of_lt ( ciSup_le fun i => _ ) _;
    exact Finset.sup J ( fun i => CBRank ( g.restrict ( S i ) ).func );
    · by_cases hi : i ∈ J <;> simp_all +decide ;
      · exact le_trans ( hQ_bound i ) ( by rw [ if_pos hi ] ; exact Finset.le_sup ( f := fun i => CBRank ( g.restrict ( S i ) ).func ) hi );
      · exact le_trans ( hQ_bound i ) ( by simp +decide [ hi ] );
    · convert Finset.sup_lt_iff _ |>.2 _;
      · exact bot_lt_iff_ne_bot.mpr hlam_ne;
      · exact fun i hi => hlt i;
  exact h_contra <| by rw [ cbRank_eq_iSup_restrict _ _ hQ_partition ] ; exact hQ_sup_bound;


/-- **Diagonal lower piece `C₁ ≤ k_{λ+1}`.**  With a clopen domain partition `(Aᵢ)` whose blocks
have all rays `< lam`, the "sub-diagonal" set `C₁ = ⋃ᵢ (Aᵢ ∩ {g.func ∉ ⋃_{j<i} ray j})` carries a
restriction of `g` all of whose rays (at `y`) have CB-rank `< lam` (for ray index `j`, only
blocks `i ≤ j` contribute, a finite union), hence reduces to `k_{λ+1} = minFun lam`. -/
lemma caseB_C1_reduces_minFun (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (g : ScatFun) (y : Baire)
    (A : ℕ → Set ↑g.domain) (hdu : g.IsDisjointUnion A)
    (hray : ∀ i j, CBRank (g.rayOn y (A i) j).func < lam) :
    ScatFun.Reduces
      (g.restrict (⋃ i, A i ∩
        {z : ↑g.domain | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}))
      (ScatFun.minFun lam hlam_lt) := by
  set C1 : Set ↑g.domain :=
    ⋃ i, A i ∩ {z : ↑g.domain | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}
    with hC1def
  have hrays : ∀ j, CBRank ((g.restrict C1).rayOn y Set.univ j).func < lam := by
    intro j
    rw [rayOn_restrict_cbRank_eq]
    have hset : g.rayOn y C1 j
        = g.restrict (⋃ i ∈ Finset.range (j + 1),
            (A i ∩ {z : ↑g.domain | g.func z ∈ RaySet Set.univ y j})) := by
      unfold ScatFun.rayOn
      congr 1
      ext z
      simp only [hC1def, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq,
        Finset.mem_range, Set.mem_compl_iff]
      constructor
      · rintro ⟨⟨i, hzi, hnotlt⟩, hzj⟩
        refine ⟨i, ?_, hzi, hzj⟩
        by_contra hcon
        exact hnotlt ⟨j, by omega, hzj⟩
      · rintro ⟨i, hilt, hzi, hzj⟩
        refine ⟨⟨i, hzi, ?_⟩, hzj⟩
        rintro ⟨k, hk, hzk⟩
        have : k = j := by
          have h1 := firstDiff_eq_of_mem y (g.func z) k hzk
          have h2 := firstDiff_eq_of_mem y (g.func z) j hzj
          omega
        omega
    rw [hset]
    refine cbRank_restrict_iUnion_finset_lt g lam hlam_ne
      (fun i => A i ∩ {z : ↑g.domain | g.func z ∈ RaySet Set.univ y j})
      (fun i => (hdu.1 i).inter ((isClopen_raySet y j).preimage g.hCont))
      (fun i i' hii => (hdu.2.1 i i' hii).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i => ?_) (Finset.range (j + 1))
    have : g.restrict (A i ∩ {z : ↑g.domain | g.func z ∈ RaySet Set.univ y j})
        = g.rayOn y (A i) j := by rw [ScatFun.rayOn]
    rw [this]; exact hray i j
  exact (ScatFun.reduces_pgl_rays (g.restrict C1) y).trans
    (consequencesGeneralStructure_pgl_le_minFun lam hlam_lt hlim hlam_ne _ hrays)


/-
**Case B, upper bound `g ≤ k_{λ+1} ⊕ ℓ_λ` (the diagonal argument).**

This is the genuinely hard direction of Case B.  Following the memoir, write
`g = ⊔_{i ∈ I} f_i` as a disjoint union of centered blocks (local centeredness, Thm 4.7 +
Prop 2.14).  For `j ∈ ℕ` put `g_j = ⊔_{i ≤ j} ray(f_i, j)` and `h_j = ⊔_{i > j} ray(f_i, j)`,
with clopen pieces `C^j_i = A_i ∩ g⁻¹(RaySet univ y j)`.  Set `C₀ = ⋃ {C^j_i | i > j}` and
`C₁ = A ∖ C₀`.  Then `CB(h_j) ≤ lam` gives `g│_{C₀} ≤ ℓ_λ`, while each `g_j` has `CB < lam`
and the `g_j` are the rays of `g│_{C₁}` at `y`, so `g│_{C₁} ≤ pgl_j g_j ≤ k_{λ+1}`.  As
`A = C₀ ⊔ C₁` is a clopen partition, `clopen_partition_to_gluing_reduces` yields
`g ≤ gl ![k, ℓ] = k ⊕ ℓ`.

The proof rests on the centered disjoint-union decomposition (`g = ⊔_i f_i`, Prop 2.14).

**Important:** the hypothesis `hnotmax` (`g` is *not* the maximum `pgl ℓ_λ`) is genuinely
required.  Without it the statement is false: `g = pgl ℓ_λ = succMaxFun` is simple of rank
`λ+1`, has all rays of rank `≤ λ` (in fact `= λ`), yet `pgl ℓ_λ ⋠ k_{λ+1} ⊕ ℓ_λ`.  The
hypothesis is used to rule out blocks `f_i ≡ pgl ℓ_λ` (which, being `≤ g`, would force
`pgl ℓ_λ ≤ g`), so every rank-`λ+1` block is `≡ k_{λ+1}` and its rays are `< λ`.
-/
lemma simple_caseB_g_reduces_Gl (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (_hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (_hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam)
    (hJne : ∃ N, lam ≤ CBRank (g.rayOn y Set.univ N).func)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g) :
    ScatFun.Reduces g
      (ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt) := by
  obtain ⟨A, hdu, hray⟩ := caseB_decomposition lam hlam_lt hlim hlam_ne hbqo g hg_rank y hconst hnotmax;
  obtain ⟨C0, C1, hC0, hC1, hC⟩ : ∃ C0 C1 : Set ↑g.domain, IsClopen C0 ∧ IsClopen C1 ∧ C0 ∪ C1 = Set.univ ∧ Disjoint C0 C1 ∧
    ScatFun.Reduces (g.restrict C0) (ScatFun.maxFun lam hlam_lt) ∧
    ScatFun.Reduces (g.restrict C1) (ScatFun.minFun lam hlam_lt) := by
      refine' ⟨ _, _, _, _, _, _, caseB_C0_reduces_maxFun lam hlam_lt g y hconst A hdu, caseB_C1_reduces_minFun lam hlam_lt hlim hlam_ne g y A hdu hray ⟩;
      · refine ⟨ ?_, ?_ ⟩;
        · refine isClosed_of_closure_subset ?_;
          intro x hx;
          rw [ mem_closure_iff ] at hx;
          contrapose! hx;
          refine ⟨ { z : ↑g.domain | ∃ i, z ∈ A i ∧ ∀ j < i, g.func z ∉ RaySet univ y j }, ?_, ?_, ?_ ⟩;
          · simp +decide [ Set.setOf_exists ];
            refine isOpen_iUnion fun i => ?_;
            simp +decide only [setOf_and, setOf_forall];
            refine IsOpen.inter ?_ ?_;
            · exact hdu.1 i |>.2;
            · refine isOpen_iff_forall_mem_open.mpr ?_;
              intro x hx;
              refine ⟨ ⋂ j < i, { z : ↑g.domain | g.func z ∉ RaySet univ y j }, ?_, ?_, ?_ ⟩;
              · exact Set.Subset.rfl;
              · rw [ show ( ⋂ j : ℕ, ⋂ ( _ : j < i ), { z : ↑g.domain | g.func z ∉ RaySet univ y j } ) = ⋂ j ∈ Finset.range i, { z : ↑g.domain | g.func z ∉ RaySet univ y j } by ext; simp +decide [ Finset.mem_range ] ];
                exact isOpen_biInter_finset fun j hj => IsOpen.preimage g.hCont <| isOpen_compl_iff.mpr <| isClopen_raySet y j |>.1;
              · exact hx;
          · simp_all +decide ;
            obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ x ) ; exact ⟨ i, hi, hx i hi ⟩ ;
          · simp_all +decide [ Set.ext_iff ];
            intro a ha i hi hi' j hj hj';
            cases eq_or_ne i j <;> simp_all +decide ;
            exact False.elim <| hdu.2.1 i j ‹_› |> fun h => h.le_bot ⟨ hi, hj ⟩;
        · refine isOpen_iUnion fun i => ?_;
          refine IsOpen.inter ( hdu.1 i |>.2 ) ?_;
          refine' IsOpen.preimage g.hCont _;
          exact isOpen_biUnion fun j hj => isClopen_raySet y j |>.2;
      · have hC0_open : IsOpen (⋃ i, A i ∩ {z | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}) := by
          refine isOpen_iUnion fun i => ?_;
          refine IsOpen.inter ( hdu.1 i |>.2 ) ?_;
          refine IsOpen.preimage g.hCont ?_;
          refine' isOpen_compl_iff.mpr _;
          exact isClosed_biUnion_finset fun j _ => isClopen_raySet y j |>.1;
        have hC0_closed : IsClosed (⋃ i, A i ∩ {z | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}) := by
          have hC0_compl_open : IsOpen (⋃ i, A i ∩ {z | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j}) := by
            refine isOpen_iUnion fun i => ?_;
            refine' IsOpen.inter ( hdu.1 i |>.2 ) _;
            exact g.hCont.isOpen_preimage _ ( isClopen_biUnion_finset ( fun j hj => isClopen_raySet y j ) |> IsClopen.isOpen )
          convert hC0_compl_open.isClosed_compl using 1;
          ext; simp [Set.mem_compl_iff, Set.mem_iUnion];
          constructor;
          · rintro ⟨ i, hi, hi' ⟩ j hj k hk; have := hdu.2.1 i j; simp_all +decide [ Set.disjoint_left ] ;
            grind;
          · intro hx;
            obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ _ );
            exact ⟨ i, hi, hx i hi ⟩;
        constructor <;> assumption;
      · ext x; simp ;
        obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ x ) ; exact if hi' : ∃ j < i, g.func x ∈ RaySet univ y j then Or.inl ⟨ i, hi, hi' ⟩ else Or.inr ⟨ i, hi, fun j hj => by aesop ⟩ ;
      · simp +contextual [ Set.disjoint_left ];
        intro a ha x hx y hy hxy z hz; have := hdu.2.1 x z; simp_all +decide [ Set.disjoint_left ] ;
        grind +revert;
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Set ↑g.domain, g.IsDisjointUnion P ∧ P 0 = C1 ∧ P 1 = C0 ∧ ∀ i ≥ 2, P i = ∅ := by
    refine ⟨ fun i => if i = 0 then C1 else if i = 1 then C0 else ∅, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ ScatFun.IsDisjointUnion ];
    · refine ⟨ ?_, ?_, ?_ ⟩;
      · intro i; split_ifs <;> simp_all +decide [ IsClopen ] ;
      · grind +locals;
      · simp_all +decide [ Set.ext_iff ];
        exact fun a ha => by rcases hC.1 a ha with h | h <;> [ exact ⟨ 1, by simpa using h ⟩ ; exact ⟨ 0, by simpa using h ⟩ ] ;
    · grind;
  refine ( scatFun_reduces_gl_of_domain_partition g P hP.1 ).trans ?_;
  refine ScatFun.gl_reduces_of_pointwise ?_ ?_ ?_;
  intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ *, ScatFun.copiesSeq ] ;
  · exact hC.2.2.2;
  · exact hC.2.2.1;
  · use fun x => x.2.choose_spec.elim;
    simp +decide only [ScatFun.empty, Subtype.forall];
    exact ⟨ continuous_of_const fun x y => by tauto, fun _ => 0, continuousOn_const, fun x hx => by tauto ⟩


/-- **Case B of Theorem 4.12.**  If `g` is simple of rank `lam+1` (`lam` a non-zero limit)
with distinguished point `y`, all rays of CB-rank `≤ lam`, and at least one ray of rank
`= lam`, then `g ≡ k_{λ+1} ⊕ ℓ_λ`.  Combines the lower bound `simple_caseB_Gl_reduces_g`
and the diagonal upper bound `simple_caseB_g_reduces_Gl`. -/
lemma simple_caseB_equiv_Gl (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func lam, g.func x = y)
    (hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam)
    (hJne : ∃ N, lam ≤ CBRank (g.rayOn y Set.univ N).func)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g) :
    ScatFun.Equiv g
      (ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt) :=
  ⟨simple_caseB_g_reduces_Gl lam hlam_lt hlim hlam_ne hbqo g hg_rank hg_simple y hconst
      hray_le hJne hnotmax,
   simple_caseB_Gl_reduces_g lam hlam_lt hlim g hg_rank hg_simple y hconst
      hray_le hJne⟩

end
