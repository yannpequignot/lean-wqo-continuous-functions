import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LevelsFinitelyGenerated
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.GlList
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.Sandwich_lemma
import WqoContinuousFunctions.ScatFun.Wedge.Monotone
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessorOfLimit
import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalForLambdaPlusOne
import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalClassReduces
import ZeroDimensionalSpaces.IsolatingSequences

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Finite generation at a successor of a limit (memoir `FGatsuccessoroflimit`, case `λ` limit)

`FGatsuccessoroflimit` (`5_precise_struct_memo.tex:378`) states `FG(λ+1)` for `λ` limit *or*
`1`, assuming `FG(<λ)` (i.e. continuous reducibility is `BQO` on `𝒞_{<λ}`).  This file covers
the `λ` non-zero-limit case; together with `Generators_two_finitely_generates`
(`ScatFun/LevelsFinitelyGenerated/Two.lean`, the `λ = 1` case) it covers the full
successor-of-(limit-or-`1`) statement.
-/

namespace ScatFun

/-! ## Scaffolding for the `λ+1` finite-generation proof -/

/-- Limit part of `lam + 1` for `lam` a nonzero limit is `lam`. -/
lemma limitPart_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) :
    (lam + 1).limitPart = lam := by
  have h1 : lam + 1 = lam + ((1 : ℕ) : Ordinal.{0}) := by simp
  rw [h1]; exact Ordinal.limitPart_add_natCast lam 1 (Or.inl hlim)

/-- Nat part of `lam + 1` for `lam` a nonzero limit is `1`. -/
lemma natPart_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) :
    (lam + 1).natPart = 1 := by
  have h1 : lam + 1 = lam + ((1 : ℕ) : Ordinal.{0}) := by simp
  rw [h1]; exact Ordinal.natPart_add_natCast lam 1 (Or.inl hlim)

/-- Unfolding of `Generators (lam+1)` for `lam` a nonzero limit into its base level and the
single `genStep`. -/
lemma Generators_add_one_eq (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) :
    Generators (lam + 1)
      = genBase lam ∪ genStep (centBase1 lam) (genBase lam) := by
  rw [Generators, limitPart_add_one lam hlim, natPart_add_one lam hlim,
      show (1 : ℕ) = 0 + 1 from rfl]
  simp only [GenBlock, CentBlock]

/-- `centBase1 lam` (for `lam` a nonzero limit `< ω₁`) is `{minFun lam, succMaxFun lam}`. -/
lemma centBase1_of_limit (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1) :
    centBase1 lam = {minFun lam hlam, succMaxFun lam hlam} := by
  rw [centBase1, if_neg (show lam ≠ 0 from by simpa using hlim.ne_bot), dif_pos hlam]

/-- `genBase lam` (for `lam` a nonzero limit `< ω₁`) is `{maxFun lam}`. -/
lemma genBase_of_limit (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1) :
    genBase lam = {maxFun lam hlam} := by
  rw [genBase, if_neg (show lam ≠ 0 from by simpa using hlim.ne_bot), dif_pos hlam]

/-- Membership: `omega (succMaxFun lam) ∈ Generators (lam+1)`. -/
lemma omega_succMaxFun_mem_Generators_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) : omega (succMaxFun lam hlam) ∈ Generators (lam + 1) := by
  rw [Generators_add_one_eq lam hlim, genStep]
  refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  rw [omegaImage, centBase1_of_limit lam hlim hlam]
  exact Finset.mem_image_of_mem omega (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- Membership: `omega (minFun lam) ∈ Generators (lam+1)`. -/
lemma omega_minFun_mem_Generators_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) : omega (minFun lam hlam) ∈ Generators (lam + 1) := by
  rw [Generators_add_one_eq lam hlim, genStep]
  refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  rw [omegaImage, centBase1_of_limit lam hlim hlam]
  exact Finset.mem_image_of_mem omega (Finset.mem_insert_self _ _)

/-- Membership: `succMaxFun lam ∈ Generators (lam+1)`. -/
lemma succMaxFun_mem_Generators_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) : succMaxFun lam hlam ∈ Generators (lam + 1) := by
  rw [Generators_add_one_eq lam hlim, genStep]
  refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  rw [centBase1_of_limit lam hlim hlam]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Membership: `minFun lam ∈ Generators (lam+1)`. -/
lemma minFun_mem_Generators_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) : minFun lam hlam ∈ Generators (lam + 1) := by
  rw [Generators_add_one_eq lam hlim, genStep]
  refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  rw [centBase1_of_limit lam hlim hlam]
  exact Finset.mem_insert_self _ _

/-- Membership: `maxFun lam ∈ Generators (lam+1)`. -/
lemma maxFun_mem_Generators_add_one (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) : maxFun lam hlam ∈ Generators (lam + 1) := by
  rw [Generators_add_one_eq lam hlim]
  refine Finset.mem_union_left _ ?_
  rw [genBase_of_limit lam hlim hlam]
  exact Finset.mem_singleton_self _

/-- The wedge `⋀(ℓ_λ ∣ k_{λ+1})` (single vertical `maxFun lam`, diagonal `minFun lam`) is, up to
continuous equivalence, the `genStep`-produced generator `wedgeFinset [[maxFun]] [minFun]`, hence
lies (up to `Equiv`) in `Generators (lam+1)`. -/
lemma wedge_maxFun_minFun_mem_Generators_add_one (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1) :
    ∃ w ∈ Generators (lam + 1),
      Equiv (wedge (fun _ : Fin 1 => maxFun lam hlam) (minFun lam hlam)) w := by
  refine ⟨wedgeFinset [[maxFun lam hlam]] [minFun lam hlam], ?_, ?_⟩
  · rw [Generators_add_one_eq lam hlim, genStep]
    refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
    rw [Finset.mem_biUnion]
    refine ⟨{{maxFun lam hlam}}, ?_, ?_⟩
    · rw [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset]
      refine ⟨by simp, ?_⟩
      intro x hx
      rw [Finset.mem_singleton] at hx; subst hx
      rw [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset, genBase_of_limit lam hlim hlam]
      exact ⟨by simp, Finset.Subset.refl _⟩
    · rw [Finset.mem_image]
      refine ⟨{minFun lam hlam}, ?_, ?_⟩
      · rw [Finset.mem_powerset, centBase1_of_limit lam hlim hlam]
        intro x hx
        rw [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _
      · simp [Finset.toList_singleton]
  · have hw : wedgeFinset [[maxFun lam hlam]] [minFun lam hlam]
        = wedge (fun _ : Fin 1 => glList [maxFun lam hlam]) (glList [minFun lam hlam]) := by
      unfold wedgeFinset wedgeList
      congr 1
      funext i
      fin_cases i
      rfl
    rw [hw]
    exact wedge_congr_equiv (fun _ => glList_single_equiv (maxFun lam hlam))
      (glList_single_equiv (minFun lam hlam))

/-
For a simple rank-`(lam+1)` block equivalent to `succMaxFun lam`, its distinguished point
lies in the intertwine set of `succMaxFun lam` with `F`.
-/
lemma succMaxFun_yn_mem_intertwineSet (F : ScatFun) (An : Set ↑F.domain) (lam : Ordinal.{0})
    (hlam : lam < omega1) (yn : Baire)
    (hrank : CBRank (F.restrict An).func = lam + 1)
    (hdist : ∀ x ∈ CBLevel (F.restrict An).func lam, (F.restrict An).func x = yn)
    (heq : Equiv (F.restrict An) (succMaxFun lam hlam)) :
    yn ∈ IntertwineSet F (succMaxFun lam hlam) := by
  obtain ⟨σ, hσ, τ, hτ, hval_eq⟩ := heq.2;
  intro V hV;
  have h_center : σ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ∈ CBLevel (F.restrict An).func lam := by
    apply center_in_CBLevel;
    · apply centerInvariance_equiv (succMaxFun_base_isCenter lam hlam) ⟨heq.2, heq.1⟩ hσ hτ hval_eq;
    · apply CBLevel_nonempty_below_rank;
      · exact F.restrict An |>.hScat;
      · exact hrank.symm ▸ Order.lt_succ lam;
  obtain ⟨U, hU⟩ : ∃ U : Set (↥(F.restrict An).domain), IsOpen U ∧ σ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ∈ U ∧ ∀ x ∈ U, (F.restrict An).func x ∈ V := by
    have h_cont : Continuous (F.restrict An).func := (F.restrict An).hCont
    exact ⟨ _, h_cont.isOpen_preimage _ ( isOpen_interior ), by simpa [ hdist _ h_center ] using mem_interior_iff_mem_nhds.mpr hV, fun x hx => interior_subset hx ⟩;
  have h_center_invariant : ContinuouslyReduces (succMaxFun lam hlam).func ((F.restrict An).func ∘ (Subtype.val : U → ↑(F.restrict An).domain)) := by
    apply centerInvariance_reduce (succMaxFun_base_isCenter lam hlam) hσ hτ hval_eq hU.left hU.right.left;
  obtain ⟨σ', hσ', hτ', hval_eq'⟩ := h_center_invariant;
  obtain ⟨σ'', hσ'', hval_eq''⟩ := ScatFun.reduces_block_into_coRestrict F An V (succMaxFun lam hlam) (fun z => (σ' z : ↥(F.restrict An).domain)) (by
  exact continuous_subtype_val.comp hσ') (by
  exact fun z => hU.2.2 _ ( σ' z |>.2 ));
  use σ'', hσ'', hτ', by
    convert hval_eq'.1 using 1;
    ext; simp [hval_eq''];
  grind

/-
Lower-bound piece: the distinguished point of a simple rank-`(lam+1)` block lies in the
intertwine set of `minFun lam` with `F`.
-/
lemma minFun_yn_mem_intertwineSet (F : ScatFun) (An : Set ↑F.domain) (lam : Ordinal.{0})
    (hlam : lam < omega1) (yn : Baire)
    (hrank : CBRank (F.restrict An).func = lam + 1)
    (hdist : ∀ x ∈ CBLevel (F.restrict An).func lam, (F.restrict An).func x = yn) :
    yn ∈ IntertwineSet F (minFun lam hlam) := by
  intro V hV;
  obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ yn ∈ W ∧ W ⊆ V := by
    obtain ⟨U, hU⟩ : ∃ U : Set Baire, IsOpen U ∧ yn ∈ U ∧ U ⊆ V := by
      exact Exists.imp ( by tauto ) ( mem_nhds_iff.mp hV );
    obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ yn ∈ W ∧ W ⊆ U := by
      convert baire_exists_clopen_subset_of_open yn U hU.1 hU.2.1;
    exact ⟨ W, hW.1, hW.2.1, hW.2.2.trans hU.2.2 ⟩;
  obtain ⟨σ, τ, hσ, hτ, hστ, hσW⟩ := ScatFun.minFun_reduces_into_clopen (F.restrict An) lam hlam yn (CBLevel_nonempty_below_rank (F.restrict An).func (F.restrict An).hScat lam (by
  exact hrank.symm ▸ lt_add_one lam)) hdist W hW.left hW.right.left;
  obtain ⟨σ', hσ', hσ'W⟩ := ScatFun.reduces_block_into_coRestrict F An W (minFun lam hlam) σ hσ (by
  assumption);
  obtain ⟨σ'', hσ'', hσ''V⟩ : ∃ σ'' : ↑(minFun lam hlam).domain → ↑(F.coRestrict V).domain, Continuous σ'' ∧ (∀ z, ((σ'' z : ↑(F.coRestrict V).domain) : Baire) = ((σ' z : ↑(F.coRestrict W).domain) : Baire)) ∧ ∀ z, (F.coRestrict V).func (σ'' z) = (F.coRestrict W).func (σ' z) := by
    apply ScatFun.reduces_block_into_coRestrict;
    · exact hσ';
    · exact fun z => hW.2.2 ( hσ'W.2 z ▸ hσW z );
  use σ'', hσ'', τ, by
    refine hτ.mono ?_;
    grind;
  grind

/-
Every simple rank-`(lam+1)` block that is not equivalent to `succMaxFun lam` reduces to
`minFun lam ⊕ maxFun lam`.
-/
lemma block_reduces_glBin_of_not_succMaxFun (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (hg_not : ¬ Equiv g (succMaxFun lam hlam)) :
    Reduces g (minFun lam hlam ⊕ maxFun lam hlam) := by
  obtain ⟨h1, h2⟩ := simpleFunctionsLambdaPlusOne lam hlam (Or.inr ⟨hlim, hlim.ne_bot⟩) hbqo g hg_rank hg_simple;
  · have h3 : Reduces (minFun lam hlam) (minFun lam hlam ⊕ maxFun lam hlam) := by
      have h4 : Reduces (minFun lam hlam) (Gl ![minFun lam hlam, maxFun lam hlam] ![1, 1]) := by
        convert ScatFun.reduces_block_gl _ 0 using 1;
        unfold copiesSeq; aesop;
      convert h4 using 1;
    exact h1.trans h3;
  · exact ‹g.Equiv ( minFun lam hlam ⊕ maxFun lam hlam ) ∨ g.Equiv ( succMaxFun lam hlam ) ›.resolve_right hg_not |>.1

/-
`ω (minFun lam ⊕ maxFun lam)` reduces to `ω (minFun lam)` (using `ℓ_λ ≤ k_{λ+1}`).
-/
lemma omega_glBin_minFun_maxFun_reduces_omega_minFun (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1) :
    Reduces (omega (minFun lam hlam ⊕ maxFun lam hlam)) (omega (minFun lam hlam)) := by
  -- By `omega_glFin_reduces_reindex`, `omega (glFin (fun _ : Fin 2 => minFun lam hlam))` reduces to `omega (minFun lam hlam)`.
  have h2 : Reduces (omega (glFin (fun _ : Fin 2 => minFun lam hlam))) (omega (minFun lam hlam)) := by
    convert omega_glFin_reduces_reindex ( fun _ : Fin 2 => minFun lam hlam ) ( fun k => if k % 2 = 0 then 0 else 1 ) _ using 1;
    exact fun k N => ⟨ if k = 0 then 2 * N else 2 * N + 1, by split_ifs <;> linarith, by fin_cases k <;> simp +decide ⟩;
  convert ScatFun.gl_reduces_of_pointwise _ _ _ |> fun h => ScatFun.omega_reduces_of_reduces h |> fun h' => h'.trans h2 using 1;
  intro i; split_ifs <;> simp_all +decide [ copiesSeq ] ;
  · interval_cases i <;> simp +decide [ copiesList ];
    · constructor;
      exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
    · exact maxFun_reduces_minFun_of_limit lam hlam ( Or.inl hlim );
  · rcases i with ( _ | _ | i ) <;> simp_all +decide [ copiesList ];
    exact empty_reduces _

/-! ### Scaffolding for the finite-degree case -/

/-- **Weakening the induction hypothesis one successor down.** `2-BQO` on `𝒞_{<λ+1}` restricts to
`2-BQO` on `𝒞_{<λ}`, since `rank < λ ⇒ rank < λ+1`. -/
lemma twoBQO_levelLT_of_add_one (lam : Ordinal.{0})
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (lam + 1))) :
    TwoBQO (ScatFun.LevelLT.reduces lam) :=
  hbqo.comap (fun F : ScatFun.LevelLT lam =>
    ⟨F.val, lt_trans F.prop (lt_add_one lam)⟩)

/-- `omega1` is a limit ordinal, so `lam < omega1` implies `lam + 1 < omega1`. -/
lemma add_one_lt_omega1 (lam : Ordinal.{0}) (hlam : lam < omega1) : lam + 1 < omega1 := by
  have h := (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)).succ_lt hlam
  rwa [Order.succ_eq_add_one] at h

/-- **Isolating codomain-corestriction is a finite gluing of generators.**  Under the isolating
hypotheses of `coRestrict_isolated_rank_const`, `coRestrict F C` is a simple rank-`λ+1` function,
hence (by `simpleFunctionsLambdaPlusOne`) equivalent to `minFun`, `minFun ⊕ maxFun`, or
`succMaxFun` — in every case a `glList` of generators of `Generators (λ+1)`. -/
lemma Fb_isolated_glList (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    (C : Set Baire) (hC : IsClopen C) (s : Baire) (hsC : s ∈ C)
    (htop : ∃ x, x ∈ CBLevel F.func lam ∧ F.func x = s)
    (hother : ∀ x, x ∈ CBLevel F.func lam → F.func x ∈ C → F.func x = s) :
    ∃ L : List ScatFun, (∀ w ∈ L, w ∈ Generators (lam + 1)) ∧
      Equiv (coRestrict F C) (glList L) := by
  obtain ⟨hrank, hconst⟩ :=
    coRestrict_isolated_rank_const lam F hFrank C hC s hsC htop hother
  have hsimple : SimpleFun (coRestrict F C).func :=
    simpleFun_of_rank_of_const (coRestrict F C) lam hrank s hconst
  rcases simpleFunctionsLambdaPlusOne lam hlam (Or.inr ⟨hlim, hlim.ne_bot⟩) hbqo
      (coRestrict F C) hrank hsimple with h | h | h
  · refine ⟨[minFun lam hlam], ?_, h.1.trans (glList_single_equiv _).1,
      (glList_single_equiv _).2.trans h.2⟩
    intro w hw; simp only [List.mem_singleton] at hw; subst hw
    exact minFun_mem_Generators_add_one lam hlim hlam
  · refine ⟨[minFun lam hlam, maxFun lam hlam], ?_, ?_⟩
    · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact minFun_mem_Generators_add_one lam hlim hlam
      · exact maxFun_mem_Generators_add_one lam hlim hlam
    · have hbin : Equiv (minFun lam hlam ⊕ maxFun lam hlam)
          (glList [minFun lam hlam, maxFun lam hlam]) :=
        finGl_glBin_equiv_glList (minFun lam hlam) (maxFun lam hlam)
      exact ⟨h.1.trans hbin.1, hbin.2.trans h.2⟩
  · refine ⟨[succMaxFun lam hlam], ?_, h.1.trans (glList_single_equiv _).1,
      (glList_single_equiv _).2.trans h.2⟩
    intro w hw; simp only [List.mem_singleton] at hw; subst hw
    exact succMaxFun_mem_Generators_add_one lam hlim hlam

/-
**Finite-degree functions of `CB`-rank `λ+1` (`λ` a non-zero limit) are finitely
generated** (memoir Corollary `finitedegreedamuddafuckaz`, `4_centered_memo.tex:372`, `λ`
non-zero-limit instance).

"Finite degree" is stated directly as: the image of the last non-empty `CB`-level
(`CBLevel F.func lam`, since `CBRank F.func = lam + 1`) is finite — matching the definition of
`N_f` in `2_prelim_memo.tex:413` (the `CB`-degree primitive itself, `N_f`, is not yet in the
Lean development; see the note at `CenteredFunctions/SimpleSuccessor/Prop411.lean:37`).

**On `hbqo`'s scope**: stated here as `TwoBQO (LevelLT.reduces (lam+1))`, i.e. 2-BQO on
`𝒞_{≤λ}` (not just `𝒞_{<λ}`) — the natural induction hypothesis at this level, matching what
is actually needed twice over: `simpleFunctionsLambdaPlusOne` only needs the weaker `𝒞_{<λ}`
instance (obtained from `hbqo` by restriction, e.g. `TwoBQO.comap`/`.subtype`), but *our own*
decomposition of `F` into countably many centered blocks (`localCenterednessFromTwoBQO_scatFun`,
Theorem 4.7) needs 2-BQO on ranks `< CBRank F.func = lam + 1`, i.e. exactly `𝒞_{≤λ}`. Consolidating
both into one hypothesis avoids re-deriving `𝒞_{≤λ}`-BQO from `𝒞_{<λ}`-BQO via the General
Structure Theorem (which the informal proof does inline, `4_centered_memo.tex:329`) as a
separate step. Compare `Two.lean`'s `twoBQO_levelLT_two`, where this same fact (`𝒞_{≤1}`-BQO)
is *derivable* rather than assumed, since `𝒞_{≤1}` is already known finitely generated.

## Proof strategy (now formalised)

The proof below implements this strategy: `exists_isolating_assign` builds the finite clopen
codomain partition isolating each top-level image point; `Fb_isolated_glList`
(via `coRestrict_isolated_rank_const` + `simpleFunctionsLambdaPlusOne`) classifies each piece as
a `glList` of generators; `equiv_gl_of_codomain_clopen_partition` reassembles `F` as their
gluing; and `gl_dite_glList_flatten_equiv` + `finGl_of_equiv_glList` place the result in
`FinGl (Generators (lam+1)).toFinFun`.

* **Decomposition into simple pieces** (memoir Corollary `FiniteDegreeAreFinGl`,
  `2_prelim_memo.tex:684`): a finite clopen partition `(Bᵢ)_{i≤n}` of the codomain, each piece
  containing exactly one point of `F.func '' CBLevel F.func lam`, gives corestrictions
  `F ↾ Bᵢ` that are simple of rank `lam + 1` (their own last CB-level is a singleton).
  Assembling these via `reduces_F_gl_of_codomain`/`reduces_gl_F_of_codomain`
  (`CenteredFunctions/SimpleSuccessor/Prop411.lean:298,433`, currently stated for `ℕ`-indexed
  families — padding the finite partition with `∅` pieces beyond index `n` reduces to that
  case) yields `F ≡ Gl (fun i => Fᵢ) ![1,…,1]` for these simple `Fᵢ`.
* **Classifying each simple piece** (`simpleFunctionsLambdaPlusOne`,
  `CenteredFunctions/SimpleSuccessorOfLimit.lean:232`, fed the `𝒞_{<λ}` restriction of `hbqo`
  below): each `Fᵢ ≡ minFun lam h`, `minFun lam h ⊕ maxFun lam h`, or `succMaxFun lam h` — the
  three candidate generators of `AlreadyKnownGenerators` at this `λ`.
* **Placing the three generators in `Generators (lam+1)`**: `maxFun lam h`, `minFun lam h`
  and `succMaxFun lam h` are already literally present, since `Generators (lam+1) =
  GenBlock (genBase lam) (centBase1 lam) 1 ⊇ genBase lam ∪ centBase1 lam = {maxFun lam h} ∪
  {minFun lam h, succMaxFun lam h}` (unfolding `GenBlock`/`Generators` at `n = 0`, as
  `(lam+1).limitPart = lam` and `(lam+1).natPart = 1`). The remaining glued generator
  `minFun lam h ⊕ maxFun lam h` needs to be located inside the `genStep`-produced wedge terms
  (still to be checked, mirroring how `Generators_one_eq` pins down `Generators 1`); then
  transfer each `Fᵢ`'s `FinGl`-membership along `Finset.exists_toFinFun_eq` as in
  `Generators_one_finitely_generates`.
-/
theorem Generators_lambdaPlusOne_finitely_generates_of_finite_degree (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (lam + 1))) :
    ∀ F : ScatFun, CBRank F.func = lam + 1 → (F.func '' CBLevel F.func lam).Finite →
      F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  intro F hFrank hSfin
  classical
  -- The finite set of top-level image points.
  set S : Finset Baire := hSfin.toFinset with hSdef
  have hlevelne : (CBLevel F.func lam).Nonempty :=
    CBLevel_nonempty_below_rank F.func F.hScat lam (hFrank.symm ▸ lt_add_one lam)
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hlevelne
    exact ⟨F.func x, by rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨x, hx, rfl⟩⟩
  obtain ⟨assign, hassign_cont, hassign_lt, hassign_inj, hassign_surj⟩ :=
    exists_isolating_assign S hSne
  -- The clopen codomain partition indexed by the assignment value.
  set B : ℕ → Set Baire := fun i => {x | assign x = i} with hBdef
  have hB_clopen : ∀ i, IsClopen (B i) := by
    intro i
    have hpre : B i = assign ⁻¹' {i} := rfl
    rw [hpre]
    exact ⟨(isClosed_discrete _).preimage hassign_cont,
      (isOpen_discrete _).preimage hassign_cont⟩
  have hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    rw [Set.disjoint_left]; intro x hx hx'
    exact hij (hx.symm.trans hx')
  have hB_cover : ⋃ i, B i = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact ⟨assign x, rfl⟩
  -- Per-block classification into a finite gluing of generators.
  have hclass : ∀ i : Fin S.card, ∃ L : List ScatFun,
      (∀ w ∈ L, w ∈ Generators (lam + 1)) ∧ Equiv (coRestrict F (B i.val)) (glList L) := by
    intro i
    obtain ⟨s, hsS, hsi⟩ := hassign_surj i.val i.isLt
    have hsC : s ∈ B i.val := hsi
    have hsimg : s ∈ (F.func '' CBLevel F.func lam) :=
      (hSdef ▸ Set.Finite.mem_toFinset hSfin).mp hsS
    obtain ⟨x0, hx0lev, hx0⟩ := hsimg
    have hother : ∀ x, x ∈ CBLevel F.func lam → F.func x ∈ B i.val → F.func x = s := by
      intro x hxlev hxB
      have hfxS : F.func x ∈ S := by
        rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨x, hxlev, rfl⟩
      have heq : assign (F.func x) = assign s := by
        have : assign (F.func x) = i.val := hxB
        rw [this, hsi]
      exact hassign_inj (Finset.mem_coe.mpr hfxS) (Finset.mem_coe.mpr hsS) heq
    exact Fb_isolated_glList lam hlim hlam (twoBQO_levelLT_of_add_one lam hbqo) F hFrank
      (B i.val) (hB_clopen i.val) s hsC ⟨x0, hx0lev, hx0⟩ hother
  choose Lf hLf_mem hLf_eq using hclass
  -- The finitely-supported family of block gluings.
  have hequiv : ∀ i, ContinuouslyEquiv (CoRestrict' F.domain F.func (B i))
      ((fun i : ℕ => if h : i < S.card then glList (Lf ⟨i, h⟩) else empty) i).func := by
    intro i
    simp only []
    by_cases h : i < S.card
    · rw [dif_pos h]; exact hLf_eq ⟨i, h⟩
    · rw [dif_neg h]
      have hFbEmpty : IsEmpty ↑(coRestrict F (B i)).domain := by
        constructor
        rintro ⟨x, hxdom, hmem⟩
        have hyi : assign (F.func ⟨x, hxdom⟩) = i := hmem
        have := hassign_lt (F.func ⟨x, hxdom⟩); omega
      exact ⟨reduces_of_isEmpty_domain hFbEmpty, empty_reduces (coRestrict F (B i))⟩
  have hFgl : Equiv F
      (gl (fun i : ℕ => if h : i < S.card then glList (Lf ⟨i, h⟩) else empty)) :=
    equiv_gl_of_codomain_clopen_partition F _ B hB_clopen hB_disj hB_cover hequiv
  have hflat := gl_dite_glList_flatten_equiv S.card Lf
  refine finGl_of_equiv_glList ?_ ⟨hFgl.1.trans hflat.1, hflat.2.trans hFgl.2⟩
  intro w hw
  rw [List.mem_flatMap] at hw
  obtain ⟨i, _, hwi⟩ := hw
  exact hLf_mem i w hwi

/-! ## The infinite-`CB`-degree case

This is the bulk of the proof of `FGatsuccessoroflimit` (`5_precise_struct_memo.tex:385-422`):
once the finite-degree case has been peeled off (`Generators_lambdaPlusOne_finitely_generates_of_finite_degree`
above, memoir corollary `finitedegreedamuddafuckaz`), every remaining `F` of `CB`-rank `lam+1`
decomposes as a countable disjoint union `F = ⊔ₙ Fₙ` of *simple* blocks of rank `lam+1` with
*pairwise distinct* distinguished points `yₙ` (memoir's Decomposition Lemma `JSLdecompositionlemma`,
`2_prelim_memo.tex:478`, Lean `decomposition_lemma_baire`/`IsLocallyInClass`,
`ContinuousReducibility/Scattered/Decomposition.lean`, refined to a countable clopen partition via
the `ℕ`-indexed machinery `locally_implies_disjointUnion_nat`
(`CenteredFunctions/SimpleSuccessor/Shared.lean:908`) already used for the analogous Case-B
decomposition of `simpleFunctionsLambdaPlusOne`; merging same-distinguished-point blocks together,
as the memoir remarks, needs the restriction-closed refinement of "simple of rank `lam+1`"
analogous to the prefix-cylinder strengthening `scatFun_centered_cylinder_witness` used for the
centered decomposition (Theorem 4.7) — this refinement is not yet in the Lean development, and is
the first genuinely new piece of infrastructure this case needs).

By `simpleFunctionsLambdaPlusOne` (Theorem 4.12, fed the `𝒞_{<lam}` restriction of `hbqo`), each
block `Fₙ` is equivalent to one of the three generators `minFun lam h`, `minFun lam h ⊕ maxFun lam h`,
or `succMaxFun lam h`. Set `N₁ := {n | Equiv (F.restrict (A n)) (succMaxFun lam h)}` — the memoir's
`N_1` — and split on its cardinality. -/

/-
**Self-similarity bridge: `maxFun (lam+1) ≤ ω (succMaxFun lam)`.**

The informal proof's "`N₁` infinite" case (below) needs `Maximalfct{λ+1} ≤ f` from
`ω (pgl Maximalfct{λ}) ≤ f`; the missing link is this reduction, which is *not* yet in the Lean
development (no `maxFun`/`succMaxFun` successor-self-similarity lemma currently exists — the
closest relatives, `succMaxFun_le_maxFun_succ` (`CenteredFunctions/Helpers.lean:699`) and
`gluingSet_copies_reduces_to_MaxFun_succ` (`PointedGluing/SelfSimilarity.lean:43`), give only the
easy direction `succMaxFun lam ≤ maxFun (lam+1)` and an unrelated idempotency fact
`ω (maxFun (lam+1)) ≤ maxFun (lam+1)`, respectively).

## Provided solution

By definition (`PointedGluing/Defs.lean:180`, unfolded via `Ordinal.limitRecOn_succ` as the lemma
`MaxDom_succ`), `MaxDom (Order.succ lam) = GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom
lam)) = GluingSet (fun _ => SuccMaxDom lam)` **literally** (`SuccMaxDom lam` is definitionally
`PointedGluingSet (fun _ => MaxDom lam)`), i.e. exactly the domain of `gl (fun _ : ℕ => SuccMaxFun
lam)` at the raw (unbundled) level. On this domain, `MaxFun (Order.succ lam) = Subtype.val` (the
identity, as in `h_maxFun_succ` inside `MaxFun_le_MinFun_succ`,
`PointedGluing/Basics/GluingInjection.lean:30`), while `gl (fun _ => SuccMaxFun lam)`'s own value at
a point `(i)⌢z` is `(i)⌢(SuccMaxFun lam z) = (i)⌢z` since `SuccMaxFun lam = Subtype.val` too — so
`gl (fun _ => SuccMaxFun lam)` is *also* the identity on the same domain (`gl_func_prepend` +
`prepend_unprepend`). Hence the raw statement
`ContinuouslyReduces (fun x : GluingSet (fun _ => SuccMaxDom lam) => (x.val : ℕ → ℕ)) (MaxFun
(Order.succ lam))` should follow by the same short `convert … using 1; norm_num […]`-style argument
already used for `gluingSet_copies_reduces_to_MaxFun_succ`, transported to the `ScatFun` level
(`omega (succMaxFun lam h) = gl (fun _ => succMaxFun lam h)`, `Order.succ lam = lam + 1`) via
`Order.succ_eq_add_one`. Only the direction stated below (`≤`) is needed downstream; the converse
`ω (succMaxFun lam) ≤ maxFun (lam+1)` should hold by the same argument read backwards but is not
recorded here since it is unused.
-/
lemma maxFun_reduces_omega_succMaxFun (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlam1 : lam + 1 < omega1) :
    Reduces (maxFun (lam + 1) hlam1) (omega (succMaxFun lam hlam)) := by
  have hdom : (maxFun (lam + 1) hlam1).domain = (omega (succMaxFun lam hlam)).domain := by
    show MaxDom (lam + 1) = GluingSet (fun _ => (succMaxFun lam hlam).domain)
    rw [← Order.succ_eq_add_one, MaxDom_succ]
    rfl
  have gval : ∀ z : ↥(omega (succMaxFun lam hlam)).domain,
      (omega (succMaxFun lam hlam)).func z = (z : ℕ → ℕ) := by
    intro z
    obtain ⟨i, hi0, hmem⟩ :=
      GluingSet_inverse_short (fun _ => (succMaxFun lam hlam).domain) z
    show (gl (fun _ => succMaxFun lam hlam)).func z = (z : ℕ → ℕ)
    rw [gl_func_apply (fun _ => succMaxFun lam hlam) z hmem, succMaxFun_func]
    exact prepend_unprepend z.val
  refine ⟨Homeomorph.setCongr hdom, (Homeomorph.setCongr hdom).continuous,
    id, continuousOn_id, ?_⟩
  intro x
  show MaxFun (lam + 1) x = (omega (succMaxFun lam hlam)).func (Homeomorph.setCongr hdom x)
  rw [gval]
  rfl

/-- **Case `N₁` infinite** (`5_precise_struct_memo.tex:394-395`): "By centeredness of
`pgl Maximalfct{λ}` we can use `Intertwinereductionsforomegacentered` again and get
`Maximalfct{λ+1} ≤ f`. As we know that `f ≤ Maximalfct{λ+1}` … we obtain `f ≡ Maximalfct{λ+1}`."

## Provided solution

* **`ω (succMaxFun lam h) ≤ F`.** `succMaxFun lam h` is centered with center `c₀ = zeroStream`
  (`succMaxFun_base_isCenter`, `CenteredFunctions/SimpleSuccessor/Shared.lean:836`). For each
  `n ∈ N₁`, unpacking `succMaxFun lam h ≤ F.restrict (A n)` as `(σ, τ, heq)` and transporting the
  center along it (`centerInvariance_equiv`) gives `IsCenterFor (F.restrict (A n)).func (σ c₀)`;
  since centers lie in every nonempty `CB`-level (`center_in_CBLevel`,
  `CenteredFunctions/Helpers.lean:147`) and `CBLevel (F.restrict (A n)).func lam` is nonempty
  (`Fₙ` simple of rank `lam+1`), `σ c₀ ∈ CBLevel (F.restrict (A n)).func lam`, so by the block's
  distinguishedness `(F.restrict (A n)).func (σ c₀) = y n`. Then `centerInvariance_reduce` gives
  `succMaxFun lam h ≤ (F.restrict (A n)).coRestrict V` for every open `V ∋ y n`, and the bridge
  lemma `reduces_block_into_coRestrict` (`ScatFun/PreciseStructure/DiagonalForLambdaPlusOne.lean:166`)
  upgrades this to `succMaxFun lam h ≤ F.coRestrict V`, i.e. `y n ∈ IntertwineSet F (succMaxFun lam
  h)`. Since `N₁` is infinite and the `y n` (`n ∈ ℕ`) are pairwise distinct, `IntertwineSet F
  (succMaxFun lam h)` is infinite, and `intertwine_reductions`
  (`ScatFun/IntertwineReductions.lean:509`, single-generator family `Fin 1`) gives
  `ω (succMaxFun lam h) ≤ F` (after collapsing `glFin (fun _ : Fin 1 => succMaxFun lam h) ≡
  succMaxFun lam h`, as in `glList_single_equiv`).
* **`F ≤ ω (succMaxFun lam h)`.** Always `F ≤ maxFun (lam + 1) hlam1` (`Maxfunctions` item 1,
  Lean `maxFun_is_maximum`, already used in `Generators_lambda_finitely_generates`), and
  `maxFun (lam + 1) hlam1 ≤ ω (succMaxFun lam h)` by the bridge lemma
  `maxFun_reduces_omega_succMaxFun` above; chain by transitivity.
* Combining the two bounds, `F ≡ ω (succMaxFun lam h)`. Since `succMaxFun lam h ∈ centBase1 lam`
  (`ScatFun/Generators/Defs.lean:166`), `ω (succMaxFun lam h) ∈ omegaImage (centBase1 lam) ⊆
  Generators (lam + 1)` **literally** (unfolding `Generators`/`GenBlock`/`genStep` at
  `n = 1`, exactly as in the existing docstring of
  `Generators_lambdaPlusOne_finitely_generates_of_finite_degree` above), so `F ∈ FinGl (Generators
  (lam+1)).toFinFun` by the usual single-generator transfer
  (`Finset.exists_toFinFun_eq` + `glList_single_equiv`, as in `Generators_lambda_finitely_generates`
  / `Generators_one_finitely_generates`). -/
theorem case_N1_infinite (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hlam1 : lam + 1 < omega1) (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (hFrank : CBRank F.func = lam + 1)
    (hN1_inf : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Infinite) :
    F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  refine finGl_single_of_equiv (omega_succMaxFun_mem_Generators_add_one lam hlim hlam) ⟨?_, ?_⟩
  · exact (reduces_maxFun_of_rank_le F (lam + 1) hlam1 (le_of_eq hFrank)).trans
      (maxFun_reduces_omega_succMaxFun lam hlam hlam1)
  · apply omega_reduces_of_intertwineSet_infinite
    have hsub : y '' {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}
        ⊆ IntertwineSet F (succMaxFun lam hlam) := by
      rintro _ ⟨n, hn, rfl⟩
      exact succMaxFun_yn_mem_intertwineSet F (A n) lam hlam (y n) (hrank n) (hdist n) hn
    exact (hN1_inf.image hy_inj.injOn).mono hsub

/-- **Case `N₁` empty** (`5_precise_struct_memo.tex:397-400`): "by
`simplefunctionslambda+1damuddafuckaz`, for all `i` we actually have either `fᵢ ≡ Minimalfct{λ+1}`
or `fᵢ ≡ Minimalfct{λ+1} ⊕ Maximalfct{λ}`, but in both cases `fᵢ ≤ Minimalfct{λ+1} ⊕ Maximalfct{λ}
≤ 2 Minimalfct{λ+1}`. Therefore … `ω Minimalfct{λ+1} ≤ f ≤ gl_i f_i ≤ ω(Minimalfct{λ+1} ⊕
Maximalfct{λ}) ≤ ω(2 Minimalfct{λ+1}) ≡ ω Minimalfct{λ+1}`, so `f ≡ ω Minimalfct{λ+1}`."

## Provided solution

* **`ω (minFun lam h) ≤ F`.** For every `n` and clopen neighbourhood `V ∋ y n`, `CBRank (F.restrict
  V-preimage).func = lam + 1` (the block keeps its top level, since `y n` is exactly the value
  there), so `minFun lam h ≤` that corestriction by `Minfunctions`/`minFun_is_minimum`
  (`PointedGluing/MinFun/Theorems.lean:573`). Since the `y n` are pairwise distinct, this is
  precisely the hypothesis of `intertwine_reductions` (single-generator family), giving
  `ω (minFun lam h) ≤ F` directly (this half does *not* need `N₁` empty).
* **`F ≤ ω (2 • minFun lam h)`.** `F ≤ gl (fun n => F.restrict (A n))` always
  (`scatFun_reduces_gl_of_domain_partition`, `CenteredFunctions/SimpleSuccessor/Shared.lean:946`).
  Since `N₁ = ∅`, `simpleFunctionsLambdaPlusOne` forces every block to be `≡ minFun lam h` or
  `≡ minFun lam h ⊕ maxFun lam h`; either way `F.restrict (A n) ≤ minFun lam h ⊕ maxFun lam h`
  (`minFun lam h` trivially embeds in the binary gluing), so `gl (fun n => F.restrict (A n)) ≤
  gl (fun _ => minFun lam h ⊕ maxFun lam h) = ω (minFun lam h ⊕ maxFun lam h)` by
  `gl_reduces_of_pointwise` (`ScatFun/Operations/GlReduces.lean:67`).
* **The needed bound `maxFun lam h ≤ minFun lam h`** (i.e. `ℓ_λ ≤ k_{λ+1}`), used to get
  `minFun lam h ⊕ maxFun lam h ≤ 2 • minFun lam h` and hence, blockwise via
  `gl_reduces_of_pointwise` again, `ω (minFun lam h ⊕ maxFun lam h) ≤ ω (2 • minFun lam h) ≡
  ω (minFun lam h)` (the last equivalence a routine reindexing, `omega_glFin_reduces_reindex`
  style). **This bound is not yet available in the Lean development**: it is *not* an instance of
  `general_structure_theorem`'s item 2 (`PointedGluing/GeneralStructure.lean:311`), whose successor
  clause needs `CBRank g ≥ η + 2n + 1` — far more than `CBRank (minFun lam h).func = lam + 1`
  provides against `CBRank (maxFun lam h).func = lam` (`maxFun_cbRank_eq`,
  `CenteredFunctions/Helpers.lean:733`) — so it needs its own argument, still to be supplied.
* Combining, `F ≡ ω (minFun lam h) ∈ Generators (lam + 1)` (`minFun lam h ∈ centBase1 lam`, so
  `ω (minFun lam h) ∈ omegaImage (centBase1 lam) ⊆ Generators (lam + 1)` literally), giving
  `FinGl`-membership as in `case_N1_infinite` above. -/
theorem case_N1_empty (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (F : ScatFun) (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (hN1_empty : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)} = ∅) :
    F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  refine finGl_single_of_equiv (omega_minFun_mem_Generators_add_one lam hlim hlam) ⟨?_, ?_⟩
  · -- `Reduces F (omega (minFun lam hlam))`
    have h1 : Reduces F (gl (fun n => F.restrict (A n))) :=
      scatFun_reduces_gl_of_domain_partition F A hdu
    have h2 : Reduces (gl (fun n => F.restrict (A n)))
        (omega (minFun lam hlam ⊕ maxFun lam hlam)) := by
      show Reduces _ (gl (fun _ : ℕ => minFun lam hlam ⊕ maxFun lam hlam))
      refine gl_reduces_of_pointwise _ _ (fun n => ?_)
      refine block_reduces_glBin_of_not_succMaxFun lam hlim hlam hbqo _ (hrank n)
        (simpleFun_of_rank_of_const _ lam (hrank n) (y n) (hdist n)) (fun hEq => ?_)
      have hn : n ∈ {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)} := hEq
      rw [hN1_empty] at hn; exact hn
    exact (h1.trans h2).trans
      (omega_glBin_minFun_maxFun_reduces_omega_minFun lam hlim hlam)
  · -- `Reduces (omega (minFun lam hlam)) F`
    apply omega_reduces_of_intertwineSet_infinite
    have hsub : Set.range y ⊆ IntertwineSet F (minFun lam hlam) := by
      rintro _ ⟨n, rfl⟩
      exact minFun_yn_mem_intertwineSet F (A n) lam hlam (y n) (hrank n) (hdist n)
    exact (Set.infinite_range_of_injective hy_inj).mono hsub

/-! ### Generic gluing/corestriction helpers for the wedge-assembly (`N₁` finite nonempty) case -/

/-- **Intertwine sets pass to corestrictions along open sets.**  If `p` lies in the open set `V₀`
and in `IntertwineSet F w`, then `p ∈ IntertwineSet (F.coRestrict V₀) w`. -/
lemma mem_intertwineSet_coRestrict_of_open (F w : ScatFun) (V₀ : Set Baire) (hV₀ : IsOpen V₀)
    {p : Baire} (hp : p ∈ V₀) (hpint : p ∈ IntertwineSet F w) :
    p ∈ IntertwineSet (F.coRestrict V₀) w := by
  intro V hV
  have hV₀' : V₀ ∩ V ∈ nhds p := Filter.inter_mem (hV₀.mem_nhds hp) hV
  have := hpint (V₀ ∩ V) hV₀'
  obtain ⟨σ, τ, hσ, hτ, h⟩ := this
  use fun x => ⟨σ x, by exact ⟨⟨_, σ x |>.2.2.1⟩, σ x |>.2.2.2⟩⟩
  generalize_proofs at *
  refine ⟨?_, hσ, ?_, ?_⟩
  · fun_prop
  · convert hτ using 1
  · convert h using 1

/-
**Prefix ⊕ tail.**  The gluing of a family that is `a` on the first `m` slots and `c` afterwards
reduces to the finite gluing of `m` copies of `a` glued with `ω c`.
-/
lemma reduces_gl_ite_glBin_replicate_omega (a c : ScatFun) (m : ℕ) :
    Reduces (gl (fun k => if k < m then a else c))
      ((glList (List.replicate m a)) ⊕ omega c) := by
  -- Define the nested family H.
  set H : ℕ → ℕ → ScatFun := fun i k => if i = 0 then if k < m then a else empty else if i = 1 then c else empty;
  -- Show that the inserted family is equivalent to the original family.
  have h_inserted_eq_original : Reduces (gl (fun k => if k < m then a else c)) (gl (fun p => H (Nat.unpair p).1 (Nat.unpair p).2)) := by
    convert ScatFun.gl_reindex ( fun p => H ( Nat.unpair p ).1 ( Nat.unpair p ).2 ) ( fun k => if k < m then Nat.pair 0 k else Nat.pair 1 ( k - m ) ) _ using 1;
    · congr! 2;
      split_ifs <;> simp +decide [ *, Nat.unpair_pair ];
      · grind;
      · aesop;
    · intro k l hkl; simp_all +decide ;
      split_ifs at hkl <;> simp_all +decide [ Nat.pair_eq_pair ];
      omega;
  -- Show that the inserted family reduces to the gluing of the nested family.
  have h_inserted_reduces_nested : Reduces (gl (fun p => H (Nat.unpair p).1 (Nat.unpair p).2)) (gl (fun i => gl (H i))) := by
    convert ScatFun.gl_flat_reduces_gl_gl H using 1;
  -- Show that the gluing of the nested family reduces to the finite gluing of m copies of a glued with ω c.
  have h_nested_reduces_finite : Reduces (gl (fun i => gl (H i))) (glList [glList (List.replicate m a), omega c]) := by
    apply gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ H ] ;
    · convert gl_reindex ( fun k => List.getD ( List.replicate m a ) k empty ) ( fun k => k ) ( by intros k l hkl; aesop ) using 1;
      grind;
    · constructor;
      swap;
      exact fun x => ⟨ x, by
        grind ⟩
      generalize_proofs at *;
      refine ⟨ ?_, ?_ ⟩;
      · exact Continuous.subtype_mk ( continuous_subtype_val ) _;
      · use fun x => x;
        exact ⟨ continuousOn_id, fun x => rfl ⟩;
    · apply reduces_of_isEmpty_domain; exact gluingSet_empty_isEmpty;
  convert h_inserted_eq_original.trans ( h_inserted_reduces_nested.trans h_nested_reduces_finite ) using 1

/-
**Reindexing a finite/cofinite split.**  For a finite `I ⊆ ℕ`, the gluing of the family that is
`a` on `I` and `c` off `I` reduces to the gluing of the family that is `a` on the first `I.card`
slots and `c` afterwards.  (A block relabelling by any bijection `ℕ ≃ ℕ` sending `I` onto
`{0,…,I.card-1}`.)
-/
lemma reduces_gl_mem_gl_lt (a c : ScatFun) (I : Finset ℕ) :
    Reduces (gl (fun n => if n ∈ I then a else c))
      (gl (fun k => if k < I.card then a else c)) := by
  have h_reindex : ∃ e : ℕ → ℕ, Function.Injective e ∧ ∀ n, (if n ∈ I then a else c) = (fun k => if k < I.card then a else c) (e n) := by
    refine ⟨ fun n => if n ∈ I then Finset.card ( Finset.filter ( · < n ) I ) else I.card + n, ?_, ?_ ⟩;
    · intro n m; by_cases hn : n ∈ I <;> by_cases hm : m ∈ I <;> simp +decide [ hn, hm ] ;
      · intro hnm
        have h_eq : Finset.filter (fun x => x < n) I = Finset.filter (fun x => x < m) I := by
          have h_eq : Finset.filter (fun x => x < n) I ⊆ Finset.filter (fun x => x < m) I ∨ Finset.filter (fun x => x < m) I ⊆ Finset.filter (fun x => x < n) I := by
            grind;
          cases h_eq <;> [ exact Finset.eq_of_subset_of_card_le ‹_› ( by linarith ) ; exact Finset.eq_of_subset_of_card_le ‹_› ( by linarith ) |> Eq.symm ];
        grind [Finset.card_filter_eq_iff, Finset.filter_card_eq, Finset.filter_inj'];
      · exact fun h => absurd h ( by linarith [ show Finset.card ( Finset.filter ( fun x => x < n ) I ) < Finset.card I from Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ n, by aesop ⟩ ) ] );
      · exact fun h => absurd h ( by linarith [ show Finset.card ( Finset.filter ( fun x => x < m ) I ) < I.card from Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ m, hm, by aesop ⟩ ) ] );
    · intro n; split_ifs <;> simp_all +decide ;
      exact fun h => absurd h ( not_le_of_gt ( Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ n, by aesop ⟩ ) ) );
  obtain ⟨ e, he₁, he₂ ⟩ := h_reindex; convert gl_reindex _ _ he₁ using 1; aesop;

/-- **Upper-bound regrouping.**  If a countable family of blocks `g` reduces, on a finite index
set `I`, into `a`, and off `I` into `c`, then the whole gluing reduces to the finite gluing of
`I.card` copies of `a` together with `ω c`.  (Memoir `Gluingasupperbound`; the `N₀`-blocks are
absorbed into the `ω c` tail.) -/
lemma reduces_gl_glBin_replicate_omega (g : ℕ → ScatFun) (a c : ScatFun) (I : Finset ℕ)
    (hin : ∀ n ∈ I, Reduces (g n) a) (hout : ∀ n, n ∉ I → Reduces (g n) c) :
    Reduces (gl g) ((glList (List.replicate I.card a)) ⊕ omega c) := by
  have hstep1 : Reduces (gl g) (gl (fun n => if n ∈ I then a else c)) := by
    refine gl_reduces_of_pointwise _ _ (fun n => ?_)
    by_cases hn : n ∈ I
    · rw [if_pos hn]; exact hin n hn
    · rw [if_neg hn]; exact hout n hn
  exact hstep1.trans ((reduces_gl_mem_gl_lt a c I).trans
    (reduces_gl_ite_glBin_replicate_omega a c I.card))

/-- **Lower bound: gluing succ-copies into a corestriction.**  If `pts` is a finite set of points
of a clopen `U`, and each `p ∈ pts` lies in the intertwine set `IntertwineSet F w` (so `w` reduces
into every neighbourhood corestriction of `F` at `p`), then the finite gluing of `pts.card` copies
of `w` reduces into `F.coRestrict U`.  (Memoir `Gluingaslowerbound`, using pairwise-disjoint clopen
neighbourhoods of the distinct points inside `U`.) -/
lemma glList_replicate_reduces_coRestrict_of_intertwine (F w : ScatFun) (U : Set Baire)
    (hU : IsClopen U) (pts : Finset Baire) (hpts : ↑pts ⊆ U)
    (hint : ∀ p ∈ pts, p ∈ IntertwineSet F w) :
    Reduces (glList (List.replicate pts.card w)) (F.coRestrict U) := by
  by_cases hpts_nonempty : pts.Nonempty
  · obtain ⟨assign, hassign_cont, hassign_card, hassign_inj, hassign_surj⟩ :=
      exists_isolating_assign pts hpts_nonempty
    set W : ℕ → Set Baire := fun k => {x | assign x = k} ∩ U with hW
    have hWopen : ∀ k, IsOpen (W k) :=
      fun k => IsOpen.inter (hassign_cont.isOpen_preimage {k} (isOpen_discrete _)) hU.isOpen
    have hWdisj : Pairwise (Disjoint on W) := by
      intro i j hij
      refine Set.disjoint_left.mpr fun x hx hx' => hij ?_
      have h1 : assign x = i := hx.1
      have h2 : assign x = j := hx'.1
      omega
    have hpint' : ∀ p ∈ pts, p ∈ IntertwineSet (F.coRestrict U) w :=
      fun p hp => mem_intertwineSet_coRestrict_of_open F w U hU.isOpen (hpts hp) (hint p hp)
    have hstep1 : Reduces (glList (List.replicate pts.card w))
        (gl (fun k => (F.coRestrict U).coRestrict (W k))) := by
      show Reduces (gl (fun k => (List.replicate pts.card w).getD k empty)) _
      refine gl_reduces_of_pointwise _ _ (fun k => ?_)
      by_cases hk : k < pts.card
      · have hval : (List.replicate pts.card w).getD k empty = w := by
          rw [List.getD_eq_getElem, List.getElem_replicate]
          simpa using hk
        rw [hval]
        obtain ⟨s, hs, hsk⟩ := hassign_surj k hk
        have hsW : s ∈ W k := ⟨by simp [hsk], hpts hs⟩
        exact hpint' s hs (W k) ((hWopen k).mem_nhds hsW)
      · have hval : (List.replicate pts.card w).getD k empty = empty := by
          rw [List.getD_eq_default]; simpa using hk
        rw [hval]
        exact empty_reduces _
    exact hstep1.trans (gl_coRestrict_disjoint_open_reduces (F.coRestrict U) W hWopen hWdisj)
  · rw [Finset.not_nonempty_iff_eq_empty] at hpts_nonempty
    subst hpts_nonempty
    refine reduces_of_isEmpty_domain ?_
    simp only [Finset.card_empty, List.replicate_zero]
    exact gluingSet_empty_isEmpty

/-- **Monotonicity of `⊕`.**  If `a ≤ a'` and `b ≤ b'` then `a ⊕ b ≤ a' ⊕ b'`. -/
lemma glBin_reduces_of_reduces {a a' b b' : ScatFun} (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (a ⊕ b) (a' ⊕ b') := by
  refine ((finGl_glBin_equiv_glList a b).1).trans (?_ )
  refine (?_ : Reduces (glList [a, b]) (glList [a', b'])).trans ((finGl_glBin_equiv_glList a' b').2)
  show Reduces (gl (fun k => ([a, b] : List ScatFun).getD k empty))
    (gl (fun k => ([a', b'] : List ScatFun).getD k empty))
  refine gl_reduces_of_pointwise _ _ (fun k => ?_)
  match k with
  | 0 => exact ha
  | 1 => exact hb
  | (n+2) => exact empty_reduces _

/-
**`FinGl S` is closed under finite replicate gluing.**
-/
lemma finGl_glList_replicate_mem {S : Finset ScatFun} {a : ScatFun}
    (ha : a ∈ FinGl S.toFinFun) (m : ℕ) :
    glList (List.replicate m a) ∈ FinGl S.toFinFun := by
  obtain ⟨La, hLa, haE⟩ := exists_glList_of_finGl ha
  have h_equiv : Equiv (glList (List.replicate m a)) (glList (List.replicate m (glList La))) := by
    refine ⟨ ?_, ?_ ⟩;
    · refine gl_reduces_of_pointwise ?_ ?_ ?_;
      intro i; by_cases hi : i < m <;> simp_all +decide ;
      · exact haE.1;
      · constructor;
        exact ⟨ continuous_id, fun _ => 0, continuousOn_const, by simp +decide [ empty ] ⟩;
    · apply ScatFun.gl_reduces_of_pointwise;
      intro i; by_cases hi : i < m <;> simp_all +decide ;
      · exact haE.symm.1;
      · constructor;
        exact ⟨ continuous_id, fun _ => 0, continuousOn_const, by simp +decide [ empty ] ⟩;
  apply finGl_of_equiv_glList;
  any_goals exact List.replicate m La |>.flatten;
  · aesop;
  · convert h_equiv.trans _ using 1;
    convert glList_map_glList_flatten ( List.replicate m La ) using 1;
    rw [ List.map_replicate ]

/-
**Binary codomain split.**  For a clopen `U`, the plain gluing of the two corestrictions
`F ↾ U` and `F ↾ Uᶜ` reduces to `F`.  (Memoir `Gluingaslowerbound2` for the two disjoint opens
`U`, `Uᶜ`.)
-/
lemma glBin_coRestrict_compl_reduces (F : ScatFun) (U : Set Baire) (hU : IsClopen U) :
    Reduces ((F.coRestrict U) ⊕ (F.coRestrict Uᶜ)) F := by
  -- Use `gl_coRestrict_disjoint_open_reduces F W` with the ℕ-indexed family
  -- `W : ℕ → Set Baire`, `W 0 = U`, `W 1 = Uᶜ`, `W k = ∅` for `k ≥ 2`.
  set W : ℕ → Set Baire := fun k => if k = 0 then U else if k = 1 then Uᶜ else ∅;
  have h_step : Reduces ((F.coRestrict (W 0)) ⊕ (F.coRestrict (W 1))) (gl (fun k => F.coRestrict (W k))) := by
    have h_step : Reduces (gl (fun i => if i = 0 then F.coRestrict (W 0) else if i = 1 then F.coRestrict (W 1) else empty)) (gl (fun k => F.coRestrict (W k))) := by
      apply ScatFun.gl_reduces_of_pointwise;
      intro i; split_ifs <;> simp_all +decide [ ScatFun.coRestrict ] ;
      · exact restrict_reduces_of_subset F fun ⦃a⦄ a_1 => a_1
      · constructor;
        exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
      · exact ScatFun.reduces_of_isEmpty_domain ( by aesop );
    convert h_step using 1;
    unfold ScatFun.glBin; simp +decide [ ScatFun.gl ] ;
    congr! 1;
    · ext; simp [Gl, GluingSet];
      constructor <;> rintro ⟨ i, x, hx, rfl ⟩ <;> use i <;> use x <;> simp_all +decide [ copiesSeq ];
      · rcases i with ( _ | _ | i ) <;> tauto;
      · rcases i with ( _ | _ | i ) <;> simp_all +decide [ copiesList ];
        · exact hx;
        · exact hx;
        · cases hx;
    · unfold Gl; simp +decide [ GluingFunVal, glBlock ] ;
      unfold ScatFun.gl; simp +decide [ GluingFunVal ] ;
      unfold glBlock; simp +decide [ copiesSeq ] ;
      unfold copiesList; simp +decide [ List.getD ] ;
      congr! 2;
      · congr! 1;
      · congr! 1;
        · rename_i k hk₁ hk₂ hk₃;
          rcases hk₁ with ⟨ i, hi ⟩ ; rcases hk₂ with ⟨ j, hj ⟩ ; simp_all +decide [ List.finRange ] ;
          grind;
        · grind +revert;
  convert h_step.trans _ using 1;
  convert ScatFun.gl_coRestrict_disjoint_open_reduces F W _ _ using 1;
  · simp +zetaDelta at *;
    intro k; split_ifs <;> simp_all +decide [ IsClopen.isOpen ] ;
  · intro i j hij; simp +decide [ W ] ;
    grind +splitIndPred

/-
**A finite-support plain gluing of generators lies in `FinGl`.**
-/
lemma finGl_gl_ite_of_forall_mem {S : Finset ScatFun} (I : Finset ℕ) (g : ℕ → ScatFun)
    (hg : ∀ i ∈ I, g i ∈ S) :
    gl (fun n => if n ∈ I then g n else empty) ∈ FinGl S.toFinFun := by
  have h_equiv : Reduces (gl (fun n => if n ∈ I then g n else empty)) (glList (I.toList.map g)) := by
    convert gl_reindex _ _ _;
    rotate_left;
    use fun n => if h : n ∈ I then List.idxOf n I.toList else I.card + n;
    · intro n m hnm; by_cases hn : n ∈ I <;> by_cases hm : m ∈ I <;> simp_all +decide [ List.idxOf_inj ] ;
      · grind [List.idxOf_eq_length_iff, Finset.length_toList, Finset.mem_toList, List.idxOf_lt_length_iff];
      · linarith [ List.idxOf_lt_length_iff.mpr ( show m ∈ I.toList from by simpa using hm ), show List.length I.toList = I.card from by simp +decide ];
    · split_ifs <;> simp_all +decide ;
  convert finGl_of_equiv_glList _ _;
  exact I.toList.map g;
  · aesop;
  · exact ⟨ h_equiv, by
      obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, Function.Injective e ∧ ∀ k, (fun n => if n ∈ I then g n else empty) (e k) = (I.toList.map g).getD k empty := by
        obtain ⟨eC, heC⟩ : ∃ eC : ℕ → ℕ, Function.Injective eC ∧ ∀ k, eC k ∉ I := by
          have h_compl : Set.Infinite {n : ℕ | n ∉ I} := by
            exact Set.infinite_of_finite_compl ( I.finite_toSet.subset fun x hx => by simpa using hx );
          exact ⟨ fun k => Nat.nth ( fun n => n ∉ I ) k, Nat.nth_injective h_compl, fun k => Nat.nth_mem_of_infinite h_compl _ ⟩;
        use fun k => if h : k < I.card then I.toList.get ⟨k, by simpa using h⟩ else eC (k - I.card);
        refine ⟨ ?_, ?_ ⟩;
        · intro k l hkl;
          by_cases hk : k < I.card <;> by_cases hl : l < I.card <;> simp_all +decide [ heC.1.eq_iff ];
          · have := List.nodup_iff_injective_get.mp ( Finset.nodup_toList I ) hkl; aesop;
          · exact False.elim <| heC.2 _ <| hkl ▸ Finset.mem_toList.mp ( List.getElem_mem _ );
          · exact False.elim <| heC.2 _ <| hkl.symm ▸ Finset.mem_toList.mp ( List.getElem_mem _ );
          · omega;
        · intro k; by_cases hk : k < I.card <;> simp +decide [ hk, heC.2 ] ;
          exact fun h => False.elim <| h <| Finset.mem_toList.mp <| by simp;
      convert gl_reindex _ _ he.1 using 1;
      unfold glList; aesop; ⟩

/-
**Case `N₁` finite and non-empty** (`5_precise_struct_memo.tex:401-422`), the case where the
wedge operation genuinely enters. Two sub-cases, on whether some clopen `U ⊇ Y₁ := y '' N₁` still
excludes infinitely many `n ∈ N₀ := ℕ ∖ N₁`:

## Provided solution

* **Sub-case (a): some clopen `U ⊇ Y₁` has `{n ∈ N₀ | y n ∉ U}` infinite.** Then
  `ω (minFun lam h) ≤ F.corestrict (Bᶜ)` (via the `N₀`-blocks avoiding `U`, `case_N1_empty`'s
  first bullet localised to `Bᶜ`) and `|N₁| • succMaxFun lam h ≤ F.corestrict U` (centeredness of
  `succMaxFun lam h` + `Gluingaslowerbound`,
  `PointedGluing/Basics/Properties.lean`/`GeneralStructure.lean`, applied to the finitely many
  blocks in `N₁`), so gluing the two corestrictions via `Gluingasupperbound`/`Gluingaslowerbound`
  (`ContinuousReducibility/Gluing/UpperBound.lean:340` `clopen_partition_to_gluing_reduces`, plus
  the reverse `disjoint_union_reduces_gluing`) gives
  `F ≡ (|N₁| • succMaxFun lam h) ⊕ ω (minFun lam h)`, a finite gluing of the two generators
  `succMaxFun lam h` and `minFun lam h` (both already in `Generators (lam+1)` as in
  `case_N1_infinite`/`case_N1_empty`), hence `F ∈ FinGl (Generators (lam+1)).toFinFun`.
* **Sub-case (b): every clopen `U ⊇ Y₁` contains all but finitely many `y n` (`n ∈ N₀`).** Choose
  pairwise disjoint clopen `Uᵢ ∋ yᵢ` (`i ∈ N₁`) with each fibre `Pᵢ = {n | y n ∈ Uᵢ}` either
  infinite or `= {i}` (possible since `Y₁` is finite and covered by `⋃ Uᵢ`, so only finitely many
  `n ∈ N₀` fall outside `⋃ Uᵢ`, and these can be folded into one infinite `Pᵢ`). For `Pᵢ = {i}`,
  `Fⁱ := F.restrict (A i) ≡ succMaxFun lam h ≤ F.coRestrict Uᵢ` directly (centeredness). For `Pᵢ`
  infinite, `(y n)_{n ∈ Pᵢ ∖ {i}} → y i` and `Fⁱ := F.restrict (⋃_{n ∈ Pᵢ} A n)` falls exactly
  under `diagonal_for_lambda_plus_one` (`ScatFun/PreciseStructure/DiagonalForLambdaPlusOne.lean:786`,
  fully proved): `Fⁱ ≤ wedge (fun _ : Fin 1 => maxFun lam h) (minFun lam h) ≤ F.coRestrict Uᵢ`.
  Assembling over the finite index set `N₁` via `Gluingasupperbound`/`Gluingaslowerbound`
  (as above) gives `F` a finite gluing of `succMaxFun lam h` and
  `wedge (fun _ => maxFun lam h) (minFun lam h)` — the latter is *literally* in
  `Generators (lam+1)` (the `genStep`-produced wedge term with vertical set `{maxFun lam h}` and
  diagonal `{minFun lam h}`, per the existing note in
  `Generators_lambdaPlusOne_finitely_generates_of_finite_degree`'s docstring above) — so
  `F ∈ FinGl (Generators (lam+1)).toFinFun`.

Both sub-cases require the same finite-clopen-partition bookkeeping already carried out (in a
closely related but not identical setting) by `diagonal_for_lambda_plus_one`'s own supporting
lemmas in `DiagonalForLambdaPlusOne.lean`; adapting them to the present two-level case split
(rather than that file's single fixed diagonal point `y 0`) is the main remaining work.

**Sub-case (a)** of `case_N1_finite_nonempty`: there is a clopen `U ⊇ Y₁ := y '' N₁` for which
infinitely many `N₀`-blocks have distinguished point outside `U`.  Then
`|N₁| • succMaxFun ⊕ ω (minFun) ≡ F`, a finite gluing of generators.
-/
theorem case_N1_finite_nonempty_subcase_a (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (_hFrank : CBRank F.func = lam + 1)
    (hN1_fin : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Finite)
    (_hN1_ne : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Nonempty)
    (hU : ∃ U : Set Baire, IsClopen U ∧
      (∀ n, Equiv (F.restrict (A n)) (succMaxFun lam hlam) → y n ∈ U) ∧
      {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ U}.Infinite) :
    F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  obtain ⟨ U, hUcl, hUsub, hUinf ⟩ := hU;
  obtain ⟨T, hT⟩ : ∃ T : ScatFun, Equiv F T ∧ T = (glList (List.replicate hN1_fin.toFinset.card (succMaxFun lam hlam))) ⊕ omega (minFun lam hlam) := by
    refine' ⟨ _, _, rfl ⟩;
    constructor;
    · refine scatFun_reduces_gl_of_domain_partition F A hdu |> fun h => h.trans ?_;
      convert reduces_gl_glBin_replicate_omega _ _ _ _ _ using 1;
      rotate_left;
      use fun n => F.restrict ( A n );
      exact succMaxFun lam hlam;
      exact minFun lam hlam ⊕ maxFun lam hlam;
      exact hN1_fin.toFinset;
      · exact fun n hn => ( hN1_fin.mem_toFinset.mp hn ).1;
      · constructor <;> intro h;
        · convert reduces_gl_glBin_replicate_omega _ _ _ _ _ using 1;
          exact fun n hn => ( hN1_fin.mem_toFinset.mp hn ).1;
        · convert h _ |> fun h => h.trans _ using 1;
          · intro n hn; exact block_reduces_glBin_of_not_succMaxFun lam hlim hlam hbqo (F.restrict (A n)) (hrank n) (simpleFun_of_rank_of_const _ lam (hrank n) (y n) (hdist n)) (by
            exact fun h => hn <| hN1_fin.mem_toFinset.mpr h);
          · convert glBin_reduces_of_reduces ( ContinuouslyReduces.refl _ ) ( omega_glBin_minFun_maxFun_reduces_omega_minFun lam hlim hlam ) using 1;
    · refine ScatFun.glBin_reduces_of_reduces ?_ ?_ |> fun h => h.trans ( ScatFun.glBin_coRestrict_compl_reduces F U hUcl );
      · convert ScatFun.glList_replicate_reduces_coRestrict_of_intertwine F ( succMaxFun lam hlam ) U hUcl ( hN1_fin.toFinset.image y ) _ _ using 1;
        · rw [ Finset.card_image_of_injective _ hy_inj ];
        · simp +decide [ Set.subset_def ];
          exact fun n hn => hUsub n hn;
        · simp +zetaDelta at *;
          intro n hn; exact (by
          exact succMaxFun_yn_mem_intertwineSet F ( A n ) lam hlam ( y n ) ( hrank n ) ( fun x hx => hdist n _ _ hx ) hn);
      · apply omega_reduces_of_intertwineSet_infinite;
        refine' Set.Infinite.mono _ ( hUinf.image _ );
        rotate_left;
        use y;
        · exact hy_inj.injOn;
        · intro p hp
          obtain ⟨n, hn, rfl⟩ := hp
          have hyn : y n ∈ IntertwineSet F (minFun lam hlam) := by
            apply minFun_yn_mem_intertwineSet F (A n) lam hlam (y n) (hrank n) (hdist n)
          exact mem_intertwineSet_coRestrict_of_open F (minFun lam hlam) Uᶜ hUcl.compl.isOpen (by
          exact hn.2) hyn;
  apply finGl_of_equiv_glList;
  case L => exact List.replicate hN1_fin.toFinset.card ( succMaxFun lam hlam ) ++ [ ( minFun lam hlam ).omega ];
  · simp ;
    rintro w ( ⟨ hw₁, rfl ⟩ | rfl ) <;> [ exact succMaxFun_mem_Generators_add_one lam hlim hlam; exact omega_minFun_mem_Generators_add_one lam hlim hlam ];
  · have := glList_append_equiv ( List.replicate hN1_fin.toFinset.card ( succMaxFun lam hlam ) ) [ ( minFun lam hlam ).omega ];
    have := glList_single_equiv ( ( minFun lam hlam ).omega );
    have := glBin_congr ( show Equiv ( glList ( List.replicate hN1_fin.toFinset.card ( succMaxFun lam hlam ) ) ) ( glList ( List.replicate hN1_fin.toFinset.card ( succMaxFun lam hlam ) ) ) from ?_ ) this;
    · exact hT.1.trans ( hT.2.symm ▸ this.trans ( Equiv.symm ‹_› ) );
    · exact ⟨ ContinuouslyReduces.refl _, ContinuouslyReduces.refl _ ⟩

/-- **Sub-case (b)** of `case_N1_finite_nonempty`: every clopen `U ⊇ Y₁ := y '' N₁` contains all
but finitely many `N₀`-distinguished points.  Then `F` is a finite gluing of `succMaxFun` and the
wedge generator `⋁(maxFun ∣ minFun)`, via `diagonal_for_lambda_plus_one`. -/
theorem case_N1_finite_nonempty_subcase_b (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (_hFrank : CBRank F.func = lam + 1)
    (hN1_fin : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Finite)
    (_hN1_ne : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Nonempty)
    (hU : ∀ U : Set Baire, IsClopen U →
      (∀ n, Equiv (F.restrict (A n)) (succMaxFun lam hlam) → y n ∈ U) →
      {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ U}.Finite) :
    F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  set I := hN1_fin.toFinset with hIdef
  obtain ⟨K, hiso, hdisj⟩ := exists_uniform_isolating_or_infinite_clopen y hy_inj I
  set U : ℕ → Set Baire := fun i => nbhd (y i) K with hUdef
  have hUcl : ∀ i, IsClopen (U i) := fun i => baire_nbhd_isClopen (y i) K
  have hUmem : ∀ i, y i ∈ U i := fun i j _ => rfl
  set Ubig : Set Baire := ⋃ i ∈ I, U i with hUbigdef
  have hUbigcl : IsClopen Ubig := isClopen_biUnion_finset (fun i _ => hUcl i)
  have hUbigsub : ∀ n, Equiv (F.restrict (A n)) (succMaxFun lam hlam) → y n ∈ Ubig := by
    intro n hn
    exact Set.mem_biUnion (hN1_fin.mem_toFinset.mpr hn) (hUmem n)
  have hL : {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ Ubig}.Finite :=
    hU Ubig hUbigcl hUbigsub
  -- N₀ is cofinite in ℕ, hence infinite.
  have hN0_inf : {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Infinite := by
    have hcompl : {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam)} = (↑I : Set ℕ)ᶜ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.mem_coe]
      rw [hIdef, hN1_fin.mem_toFinset, Set.mem_setOf_eq]
    rw [hcompl]
    exact (Finset.finite_toSet I).infinite_compl
  -- Removing the (finite) stragglers, infinitely many N₀-points land inside `Ubig`.
  have hN0_in_Ubig_inf :
      {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ Ubig}.Infinite := by
    have heq : {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam)} \
        {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ Ubig} =
        {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ Ubig} := by
      ext n
      simp only [Set.mem_diff, Set.mem_setOf_eq]
      tauto
    rw [← heq]
    exact hN0_inf.diff hL
  -- Pigeonhole over the finite index set `I`: some `U i₀` catches infinitely many N₀-points.
  obtain ⟨i₀, hi₀I, hi₀inf⟩ :
      ∃ i ∈ I, {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ U i}.Infinite := by
    by_contra hcon
    push_neg at hcon
    have hall_fin : ∀ i ∈ I,
        {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ U i}.Finite :=
      fun i hi => hcon i hi
    apply hN0_in_Ubig_inf
    have hsub : {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ Ubig} ⊆
        ⋃ i ∈ I, {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∈ U i} := by
      rintro n ⟨hnE, hnU⟩
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hnU
      exact Set.mem_biUnion hi ⟨hnE, hyi⟩
    exact (Set.Finite.biUnion (Finset.finite_toSet I) hall_fin).subset hsub
  -- The infinite branch holds at `i₀`, and every point it catches beyond `i₀` itself is in N₀.
  have hPi0_inf : {n | y n ∈ U i₀}.Infinite :=
    Set.Infinite.mono (fun n hn => hn.2) hi₀inf
  -- Partition `ℕ` by folding the leftover stragglers `R` into `P i₀`.
  set P : ℕ → Set ℕ := fun i => {n | y n ∈ U i} with hPdef
  set R : Set ℕ := {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ Ubig} with hRdef
  set P' : ℕ → Set ℕ := fun i => if i = i₀ then P i₀ ∪ R else P i with hP'def
  have hP_disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j) := by
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro n hnPi hnPj
    exact (Set.disjoint_left.mp (hdisj i hi j hj hij) hnPi) hnPj
  have hR_disj_P : ∀ j ∈ I, Disjoint R (P j) := by
    intro j hj
    rw [Set.disjoint_left]
    intro n hnR hnPj
    exact hnR.2 (Set.mem_biUnion hj hnPj)
  have hP'_pairwiseDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P' i) (P' j) := by
    intro i hi j hj hij
    by_cases hii0 : i = i₀
    · by_cases hji0 : j = i₀
      · exact absurd (hii0.trans hji0.symm) hij
      · simp only [hP'def, if_pos hii0, if_neg hji0]
        have hd : Disjoint (P i₀) (P j) := by rw [← hii0]; exact hP_disj i hi j hj hij
        exact Disjoint.union_left hd (hR_disj_P j hj)
    · by_cases hji0 : j = i₀
      · simp only [hP'def, if_neg hii0, if_pos hji0]
        have hd : Disjoint (P i) (P i₀) := by rw [← hji0]; exact hP_disj i hi j hj hij
        have hr : Disjoint (P i) R := (hR_disj_P i hi).symm
        exact Disjoint.union_right hd hr
      · simp only [hP'def, if_neg hii0, if_neg hji0]
        exact hP_disj i hi j hj hij
  have hP'_cover : (⋃ i ∈ I, P' i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    by_cases hnI : Equiv (F.restrict (A n)) (succMaxFun lam hlam)
    · have hnImem : n ∈ I := hN1_fin.mem_toFinset.mpr hnI
      refine Set.mem_biUnion hnImem ?_
      by_cases hni0 : n = i₀
      · simp only [hP'def, if_pos hni0]
        left
        rw [hni0]
        exact hUmem i₀
      · simp only [hP'def, if_neg hni0]
        exact hUmem n
    · by_cases hnUbig : y n ∈ Ubig
      · obtain ⟨j, hjI, hyj⟩ := Set.mem_iUnion₂.mp hnUbig
        refine Set.mem_biUnion hjI ?_
        by_cases hji0 : j = i₀
        · simp only [hP'def, if_pos hji0]
          left
          rw [← hji0]
          exact hyj
        · simp only [hP'def, if_neg hji0]
          exact hyj
      · refine Set.mem_biUnion hi₀I ?_
        simp only [hP'def, if_pos rfl]
        right
        exact ⟨hnI, hnUbig⟩
  -- For any `i ∈ I` and clopen `V ∋ y i`, `W := V ∪ ⋃_{j ∈ I, j ≠ i} U j` is clopen `⊇ Y₁`.
  -- Since the `U j` are pairwise disjoint, any `n ∈ P i \ {i}` has `y n ∈ W ↔ y n ∈ V`, and such
  -- `n` is automatically in `N₀`. So `hU` (applied to `W`) shows cofinitely many `n ∈ P i \ {i}`
  -- land in `V` — genuine convergence of the *whole* family, not a subsequence. Folding the
  -- (already finite) stragglers `R` into `i`'s own fibre (when `i = i₀`) costs nothing extra.
  have hconv_family' : ∀ i ∈ I, ∀ V : Set Baire, IsClopen V → y i ∈ V →
      {n | n ∈ P' i ∧ n ≠ i ∧ y n ∉ V}.Finite := by
    intro i hi V hVcl hVmem
    set W : Set Baire := V ∪ ⋃ j ∈ I.erase i, U j with hWdef
    have hWcl : IsClopen W := hVcl.union (isClopen_biUnion_finset (fun j _ => hUcl j))
    have hWsub : ∀ n, Equiv (F.restrict (A n)) (succMaxFun lam hlam) → y n ∈ W := by
      intro n hn
      rcases eq_or_ne n i with rfl | hne
      · exact Or.inl hVmem
      · exact Or.inr (Set.mem_biUnion
          (Finset.mem_erase.mpr ⟨hne, hN1_fin.mem_toFinset.mpr hn⟩) (hUmem n))
    have hWfin := hU W hWcl hWsub
    have hPi_sub : {n | n ∈ P i ∧ n ≠ i ∧ y n ∉ V} ⊆
        {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ W} := by
      rintro n ⟨hnPi, hne, hnV⟩
      have hnI : ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) := by
        intro hnE
        exact (Set.disjoint_left.mp (hdisj n (hN1_fin.mem_toFinset.mpr hnE) i hi hne)
          (hUmem n)) hnPi
      refine ⟨hnI, ?_⟩
      rintro (hnV' | hnU')
      · exact hnV hnV'
      · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hnU'
        obtain ⟨hjne, hjI⟩ := Finset.mem_erase.mp hj
        exact (Set.disjoint_left.mp (hdisj j hjI i hi hjne) hyj) hnPi
    by_cases hii0 : i = i₀
    · have hsub : {n | n ∈ P' i ∧ n ≠ i ∧ y n ∉ V} ⊆
          {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ W} ∪ R := by
        rintro n ⟨hnP'i, hne, hnV⟩
        simp only [hP'def, if_pos hii0, Set.mem_union] at hnP'i
        rcases hnP'i with hnPi | hnR
        · left
          have hnPi' : n ∈ P i := by rw [hii0]; exact hnPi
          exact hPi_sub ⟨hnPi', hne, hnV⟩
        · right; exact hnR
      exact (hWfin.union hL).subset hsub
    · apply Set.Finite.subset hWfin
      intro n hn
      apply hPi_sub
      simpa only [hP'def, if_neg hii0] using hn
  -- `P i₀ \ {i₀}` is infinite, hence so is the folded `P' i₀ \ {i₀}`.
  have hPi0_minus_inf : {n | y n ∈ U i₀ ∧ n ≠ i₀}.Infinite := by
    have heq : {n | y n ∈ U i₀ ∧ n ≠ i₀} = {n | y n ∈ U i₀} \ {i₀} := by
      ext n; simp [Set.mem_diff, and_comm]
    rw [heq]
    exact hPi0_inf.diff (Set.finite_singleton i₀)
  have hP'i0_minus_inf : {n | n ∈ P' i₀ ∧ n ≠ i₀}.Infinite := by
    have hsub : {n | y n ∈ U i₀ ∧ n ≠ i₀} ⊆ {n | n ∈ P' i₀ ∧ n ≠ i₀} := by
      intro n hn
      refine ⟨?_, hn.2⟩
      simp only [hP'def, if_pos rfl, Set.mem_union]
      left; exact hn.1
    exact Set.Infinite.mono hsub hPi0_minus_inf
  set A' : ℕ → Set ↑F.domain := fun i => ⋃ n ∈ P' i, A n with hA'def
  have hA'_eq_of_singleton : ∀ i, P' i = {i} → A' i = A i := by
    intro i hPi
    simp [hA'def, hPi]
  have hreduces_of_singleton : ∀ i ∈ I, P' i = {i} →
      Reduces (F.restrict (A' i)) (succMaxFun lam hlam) := by
    intro i hi hPi
    rw [hA'_eq_of_singleton i hPi]
    exact (hN1_fin.mem_toFinset.mp hi).1
  have hreduces_of_singleton_low : ∀ i ∈ I, P' i = {i} →
    Reduces (succMaxFun lam hlam) (F.coRestrict (U i)) := by
    intro i hi hPi
    have heq : Equiv (F.restrict (A i)) (succMaxFun lam hlam) := hN1_fin.mem_toFinset.mp hi
    have hyi_intertwine : y i ∈ IntertwineSet F (succMaxFun lam hlam) :=
      succMaxFun_yn_mem_intertwineSet F (A i) lam hlam (y i) (hrank i) (hdist i) heq
    have hstep : Reduces
        (glList (List.replicate ({y i} : Finset Baire).card (succMaxFun lam hlam)))
        (F.coRestrict (U i)) := by
      apply glList_replicate_reduces_coRestrict_of_intertwine F (succMaxFun lam hlam) (U i)
        (hUcl i) ({y i} : Finset Baire)
      · rw [Finset.coe_singleton]
        exact Set.singleton_subset_iff.mpr (hUmem i)
      · intro p hp
        rw [Finset.mem_singleton] at hp
        rw [hp]
        exact hyi_intertwine
    rw [Finset.card_singleton, List.replicate_one] at hstep
    exact (glList_single_equiv (succMaxFun lam hlam)).1.trans hstep
  -- General dichotomy: each `i ∈ I` has either an isolated fibre or an infinite one.
  have hPfin_or_inf : ∀ i ∈ I, P i = {i} ∨ (P i).Infinite := fun i hi =>
    (hiso i hi).imp id (fun h => h K)
  -- `i₀` is never a singleton fibre (it was chosen with an infinite one).
  have hi₀_not_singleton : P i₀ ≠ {i₀} := by
    intro heq
    have hcontra : ({i₀} : Set ℕ).Infinite := heq ▸ hPi0_inf
    exact (Set.finite_singleton i₀).not_infinite hcontra
  -- Any off-`I` block reduces to `minFun lam ⊕ maxFun lam`.
  have hoffI_reduces : ∀ n, ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) →
      Reduces (F.restrict (A n)) (minFun lam hlam ⊕ maxFun lam hlam) := fun n hn =>
    block_reduces_glBin_of_not_succMaxFun lam hlim hlam hbqo (F.restrict (A n)) (hrank n)
      (simpleFun_of_rank_of_const _ lam (hrank n) (y n) (hdist n)) hn
  -- Per-class sandwich: `succMaxFun lam` (singleton fibre) or the wedge generator (infinite
  -- fibre, via `diagonal_class_reduces_wedge`), each already known to lie in
  -- `FinGl (Generators (lam+1))`.
  have hclass : ∀ i ∈ I, ∃ g : ScatFun, g ∈ FinGl (Generators (lam + 1)).toFinFun ∧
      Reduces (F.restrict (A' i)) g ∧ Reduces g (F.coRestrict (U i)) := by
    intro i hi
    rcases hPfin_or_inf i hi with hsing | hinf
    · have hP'sing : P' i = {i} := by
        by_cases hii0 : i = i₀
        · exact absurd (by rw [← hii0]; exact hsing) hi₀_not_singleton
        · simpa only [hP'def, if_neg hii0] using hsing
      exact ⟨succMaxFun lam hlam,
        finGl_single_of_equiv (succMaxFun_mem_Generators_add_one lam hlim hlam) (Equiv.refl _),
        hreduces_of_singleton i hi hP'sing, hreduces_of_singleton_low i hi hP'sing⟩
    · set S : Set ℕ := {n | n ∈ P' i ∧ n ≠ i} with hSdef
      have hiP' : i ∈ P' i := by
        by_cases hii0 : i = i₀
        · simp only [hP'def, if_pos hii0, Set.mem_union]
          left
          rw [hii0]
          exact hUmem i₀
        · simp only [hP'def, if_neg hii0]
          exact hUmem i
      have hSinf : S.Infinite := by
        by_cases hii0 : i = i₀
        · have hSeq : S = {n | n ∈ P' i₀ ∧ n ≠ i₀} := by rw [hSdef, hii0]
          rw [hSeq]
          exact hP'i0_minus_inf
        · have hP'eq : P' i = P i := by simp only [hP'def, if_neg hii0]
          have hSeq : S = P i \ {i} := by
            rw [hSdef, hP'eq]; ext n; simp [Set.mem_diff, and_comm]
          rw [hSeq]
          exact hinf.diff (Set.finite_singleton i)
      have h0 : Equiv (F.restrict (A i)) (succMaxFun lam hlam) := hN1_fin.mem_toFinset.mp hi
      have hiS : i ∉ S := fun hmem => hmem.2 rfl
      have hSclass : ∀ n ∈ S, Reduces (F.restrict (A n)) (minFun lam hlam ⊕ maxFun lam hlam) := by
        intro n hn
        obtain ⟨hnP', hne⟩ := hn
        apply hoffI_reduces
        intro hnE
        have hnI : n ∈ I := hN1_fin.mem_toFinset.mpr hnE
        by_cases hii0 : i = i₀
        · simp only [hP'def, if_pos hii0, Set.mem_union] at hnP'
          rcases hnP' with hnP | hnR
          · exact (Set.disjoint_left.mp
              (hdisj n hnI i₀ hi₀I (by rw [← hii0]; exact hne)) (hUmem n)) hnP
          · exact hnR.1 hnE
        · simp only [hP'def, if_neg hii0] at hnP'
          exact (Set.disjoint_left.mp (hdisj n hnI i hi hne) (hUmem n)) hnP'
      have hSconv : ∀ V : Set Baire, IsClopen V → y i ∈ V → {n | n ∈ S ∧ y n ∉ V}.Finite := by
        intro V hVcl hVmem
        have hSVeq : {n | n ∈ S ∧ y n ∉ V} = {n | n ∈ P' i ∧ n ≠ i ∧ y n ∉ V} := by
          ext n; simp [hSdef, and_assoc]
        rw [hSVeq]
        exact hconv_family' i hi V hVcl hVmem
      have hdiag := diagonal_class_reduces_wedge lam hlam F A hdu y hy_inj hrank hdist i h0
        S hiS hSinf hSclass hSconv (U i) (hUcl i) (hUmem i)
      have hA'eq : A' i = A i ∪ ⋃ n ∈ S, A n := by
        rw [hA'def]
        apply Set.Subset.antisymm
        · rintro x hx
          obtain ⟨n, hnmem, hxn⟩ := Set.mem_iUnion₂.mp hx
          by_cases hni : n = i
          · exact Or.inl (hni ▸ hxn)
          · exact Or.inr (Set.mem_biUnion (show n ∈ S from ⟨hnmem, hni⟩) hxn)
        · rintro x (hx | hx)
          · exact Set.mem_biUnion hiP' hx
          · obtain ⟨n, hnS, hxn⟩ := Set.mem_iUnion₂.mp hx
            exact Set.mem_biUnion hnS.1 hxn
      obtain ⟨w, hw, hweq⟩ := wedge_maxFun_minFun_mem_Generators_add_one lam hlim hlam
      refine ⟨wedge (fun _ : Fin 1 => maxFun lam hlam) (minFun lam hlam),
        finGl_single_of_equiv hw hweq, ?_, hdiag.2⟩
      rw [hA'eq]
      exact hdiag.1
  -- Assemble via the finite fibre-family lemma.
  choose g hgmem hgup hglow using hclass
  have ht_mem : ∀ n, ∃ i, i ∈ I ∧ n ∈ P' i := by
    intro n
    have hn : n ∈ ⋃ i ∈ I, P' i := by rw [hP'_cover]; exact Set.mem_univ n
    simpa using Set.mem_iUnion₂.mp hn
  choose t htI htP' using ht_mem
  set A'' : ℕ → Set ↑F.domain := fun i => ⋃ k ∈ {k | t k = i}, A k with hA''def
  have hdu'' : F.IsDisjointUnion A'' := ScatFun.IsDisjointUnion.regroup F A hdu t
  have hA''_eq : ∀ i ∈ I, A'' i = A' i := by
    intro i hi
    rw [hA''def, hA'def]
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
      have hk' : t k = i := hk
      refine Set.mem_biUnion ?_ hxk
      rw [← hk']
      exact htP' k
    · rintro x hx
      obtain ⟨n, hnP', hxn⟩ := Set.mem_iUnion₂.mp hx
      have htn : t n = i := by
        by_contra hne
        exact (Set.disjoint_left.mp
          (hP'_pairwiseDisjoint (t n) (htI n) i hi hne) (htP' n)) hnP'
      exact Set.mem_biUnion htn hxn
  have hA''_empty : ∀ n, n ∉ I → A'' n = ∅ := by
    intro n hn
    rw [hA''def]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k, hk, _⟩ := Set.mem_iUnion₂.mp hx
    have hk' : t k = n := hk
    exact hn (by rw [← hk']; exact htI k)
  set U'' : ℕ → Set Baire := fun i => if i ∈ I then U i else ∅ with hU''def
  have hU''cl : ∀ i, IsClopen (U'' i) := by
    intro i
    by_cases hi : i ∈ I
    · simp only [hU''def, if_pos hi]
      exact hUcl i
    · simp only [hU''def, if_neg hi]
      exact isClopen_empty
  have hU''disj : Pairwise (Disjoint on U'') := by
    intro i j hij
    by_cases hi : i ∈ I
    · by_cases hj : j ∈ I
      · simp only [Function.onFun, hU''def, if_pos hi, if_pos hj]
        exact hdisj i hi j hj hij
      · simp [Function.onFun, hU''def, if_pos hi, if_neg hj]
    · simp [Function.onFun, hU''def, if_neg hi]
  set g' : ℕ → ScatFun := fun i => if hi : i ∈ I then g i hi else succMaxFun lam hlam with hg'def
  apply finGl_sandwich F I A'' hdu'' hA''_empty U'' hU''cl hU''disj g'
  · intro i hi
    rw [hA''_eq i hi]
    have hg'eq : g' i = g i hi := by simp only [hg'def, dif_pos hi]
    rw [hg'eq]
    exact hgup i hi
  · intro i hi
    have hUeq : U'' i = U i := by simp only [hU''def, if_pos hi]
    have hg'eq : g' i = g i hi := by simp only [hg'def, dif_pos hi]
    rw [hUeq, hg'eq]
    exact hglow i hi
  · intro i hi
    have hg'eq : g' i = g i hi := by simp only [hg'def, dif_pos hi]
    rw [hg'eq]
    exact hgmem i hi

theorem case_N1_finite_nonempty (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam : lam < omega1) (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (hFrank : CBRank F.func = lam + 1)
    (hN1_fin : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Finite)
    (hN1_ne : {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)}.Nonempty) :
    F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  by_cases hcase : ∃ U : Set Baire, IsClopen U ∧
      (∀ n, Equiv (F.restrict (A n)) (succMaxFun lam hlam) → y n ∈ U) ∧
      {n | ¬ Equiv (F.restrict (A n)) (succMaxFun lam hlam) ∧ y n ∉ U}.Infinite
  · exact case_N1_finite_nonempty_subcase_a lam hlim hlam hbqo F A hdu y hy_inj hrank hdist hFrank
      hN1_fin hN1_ne hcase
  · refine case_N1_finite_nonempty_subcase_b lam hlim hlam hbqo F A hdu y hy_inj hrank hdist hFrank
      hN1_fin hN1_ne ?_
    push_neg at hcase
    intro U hUcl hUsub
    exact hcase U hUcl hUsub

/-
**Finite-degree functions of `CB`-rank `λ+1` (`λ` a non-zero limit) with *infinite*
`CB`-degree are finitely generated** — the complementary case to
`Generators_lambdaPlusOne_finitely_generates_of_finite_degree`, together covering all of
`5_precise_struct_memo.tex:385-422`.

## Provided solution

Decompose `F` into simple blocks `Fₙ = F.restrict (A n)` of rank `lam+1` with pairwise distinct
distinguished points `(y n)` (the Decomposition Lemma step described above the three case
theorems). Classify each block via `simpleFunctionsLambdaPlusOne`
(`CenteredFunctions/SimpleSuccessorOfLimit.lean:232`, fed the `𝒞_{<lam}` restriction of `hbqo`, as
already noted for the finite-degree theorem above). Set `N₁ := {n | Equiv (F.restrict (A n))
(succMaxFun lam h)}` and dispatch on `Set.Infinite N₁ ∨ N₁ = ∅ ∨ (N₁.Finite ∧ N₁.Nonempty)`
(`Set.eq_empty_or_nonempty` + `Set.finite_or_infinite`) to `case_N1_infinite`, `case_N1_empty`, or
`case_N1_finite_nonempty` respectively.
-/

/-
**Countable clopen partition into top-level-constant pieces.**  Every scattered `F` admits a
countable clopen partition `(Q k)` of its domain such that on each piece the function is constant
along the top `CB`-level `CBLevel F.func lam`.  Obtained from `decomposition_lemma_baire` (simple
neighbourhoods), a Lindelöf countable subcover, and `disjointed`: each piece lies inside a single
simple neighbourhood, and a piece meeting `CBLevel F.func lam` must sit around a genuine top
point, forcing the top value to be constant there.
-/
lemma exists_clopen_partition_topconst (F : ScatFun) (lam : Ordinal.{0})
    (hF : CBRank F.func = lam + 1) :
    ∃ Q : ℕ → Set ↑F.domain,
      (∀ k, IsClopen (Q k)) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
      (⋃ k, Q k = Set.univ) ∧
      (∀ k, ∃ w : Baire, ∀ x ∈ Q k, x ∈ CBLevel F.func lam → F.func x = w) := by
  -- For each point $x$ in the domain of $F$, there exists a clopen neighborhood $U_x$ such that the restriction of $F$ to $U_x$ is constant on the top level of the CB derivative.
  have h_neighborhood : ∀ x : F.domain, ∃ U : Set F.domain, IsClopen U ∧ x ∈ U ∧ ∃ w, ∀ z ∈ CBLevel (F.func ∘ (Subtype.val : ↥U → F.domain)) lam, F.func z.val = w := by
    intro x
    obtain ⟨Ub, hUbcl, hxUb, hw'⟩ := decomposition_lemma_baire F.domain F.func F.hScat x
    use Subtype.val ⁻¹' Ub
    simp only [mem_preimage, hxUb, Subtype.forall, true_and];
    refine ⟨ ?_, ?_ ⟩;
    · exact ⟨ hUbcl.1.preimage continuous_subtype_val, hUbcl.2.preimage continuous_subtype_val ⟩;
    · obtain ⟨ α, hα_ne, hα_succ_empty, w, hw ⟩ := hw';
      -- Since $CBLevel (F.func ∘ Subtype.val) (lam + 1) = ∅$, we have $α ≤ lam$.
      have hα_le_lam : α ≤ lam := by
        have hα_le_lam : CBLevel (F.func ∘ (Subtype.val : ↥(Subtype.val ⁻¹' Ub) → F.domain)) (lam + 1) = ∅ := by
          have hα_le_lam : CBLevel (F.func ∘ (Subtype.val : ↥(Subtype.val ⁻¹' Ub) → F.domain)) (lam + 1) = CBLevel F.func (lam + 1) ∩ (Subtype.val ⁻¹' Ub) := by
            convert local_cb_derivative ( Subtype.val ⁻¹' Ub ) ( hUbcl.2.preimage continuous_subtype_val ) ( lam + 1 ) using 1;
            exact inferInstance;
          have := cbLevel_at_cbRank_empty F.func F.hScat; aesop;
        contrapose! hα_le_lam;
        exact hα_ne.mono ( CBLevel_antitone _ <| by simpa using hα_le_lam );
      use w;
      intro a ha ha' ha''; specialize hw ⟨ ⟨ a, ha ⟩, ha' ⟩ ; simp_all +decide [ CBLevel ] ;
      apply hw;
      convert CBLevel_antitone ( F.func ∘ Subtype.val ) hα_le_lam ha'' using 1;
  choose U hU using h_neighborhood;
  obtain ⟨g, hg⟩ : ∃ g : ℕ → F.domain, ⋃ k, U (g k) = Set.univ := by
    have h_countable_subcover : ∃ (s : Set F.domain), s.Countable ∧ ⋃ x ∈ s, U x = Set.univ := by
      have h_lindelof : IsLindelof (Set.univ : Set F.domain) := isLindelof_univ
      have := h_lindelof.elim_countable_subcover ( fun x => U x );
      exact Exists.elim ( this ( fun x => hU x |>.1.isOpen ) ( fun x _ => Set.mem_iUnion_of_mem x ( hU x |>.2.1 ) ) ) fun s hs => ⟨ s, hs.1, Set.Subset.antisymm ( Set.subset_univ _ ) hs.2 ⟩;
    obtain ⟨ s, hs₁, hs₂ ⟩ := h_countable_subcover;
    have := hs₁.exists_eq_range;
    rcases s.eq_empty_or_nonempty with ( rfl | hs₃ ) <;> simp_all +decide [ Set.ext_iff ];
    · contrapose! hs₂;
      by_cases h : F.domain = ∅;
      · simp_all +decide [ CBRank ];
        simp_all +decide [ Set.ext_iff ];
        exact absurd hF ( ne_of_lt ( Ordinal.succ_pos _ ) );
      · exact Set.nonempty_iff_ne_empty.mpr h;
    · obtain ⟨ f, hf ⟩ := this;
      exact ⟨ f, fun a b => by obtain ⟨ i, hi ⟩ := hs₂ a b; obtain ⟨ j, hj ⟩ := hf _ _ |>.1 hi.2.1; exact ⟨ j, hj ▸ hi.2.2 ⟩ ⟩;
  refine ⟨ fun k => disjointed ( fun k => U ( g k ) ) k, ?_, ?_, ?_, ?_ ⟩;
  · intro k;
    convert disjointed_clopen ( fun k => U ( g k ) ) ( fun k => hU ( g k ) |>.1 ) k using 1;
  · exact fun i j hij => disjoint_disjointed _ hij;
  · rw [ ← hg, iUnion_disjointed ];
  · intro k;
    obtain ⟨ w, hw ⟩ := hU ( g k ) |>.2.2;
    use w;
    intro x hx hx';
    convert hw ⟨ x, by
      exact Set.mem_of_mem_of_subset hx ( disjointed_subset _ _ ) ⟩ _
    generalize_proofs at *;
    convert local_cb_derivative _ _ _ |>.symm.subset ( Set.mem_inter hx' ‹_› ) using 1;
    · grind;
    · exact hU _ |>.1.2

universe u

/-
**Rank from top level.**  A scattered `f` whose `lam`-th `CB`-level is nonempty but whose
`(lam+1)`-th level is empty has `CB`-rank exactly `lam+1`.
-/
lemma cbRank_eq_add_one_of_levels {X : Type u} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (lam : Ordinal.{u})
    (hne : (CBLevel f lam).Nonempty) (hempty : CBLevel f (lam + 1) = ∅) :
    CBRank f = lam + 1 := by
  refine le_antisymm ?_ ?_;
  · refine csInf_le' ?_;
    simp_all +decide [ CBLevel ];
  · refine le_csInf ?_ ?_;
    · exact cb_stabilizing_set_nonempty f hf;
    · intro α hα;
      contrapose! hne;
      have h_le : CBLevel f lam ⊆ CBLevel f α := by
        apply CBLevel_antitone f;
        exact Order.le_of_lt_succ hne;
      grind [CBLevel_eq_of_stable]

/-
**Per-block rank and distinguished value.**  For `F` of `CB`-rank `lam+1`, a clopen block `A`
that meets the top level `CBLevel F.func lam` and on which the top-level value is constantly `w`
gives a block `F.restrict A` of rank `lam+1` whose distinguished value is `w`.
-/
lemma block_rank_dist (F : ScatFun) (lam : Ordinal.{0}) (hF : CBRank F.func = lam + 1)
    (A : Set ↑F.domain) (hAcl : IsClopen A)
    (hne : (CBLevel F.func lam ∩ A).Nonempty)
    (w : Baire) (hw : ∀ x ∈ A, x ∈ CBLevel F.func lam → F.func x = w) :
    CBRank (F.restrict A).func = lam + 1 ∧
    (∀ x ∈ CBLevel (F.restrict A).func lam, (F.restrict A).func x = w) := by
  have h_restrict_eq : (F.restrict A).func '' CBLevel (F.restrict A).func lam = {w} := by
    have h_subset : (F.restrict A).func '' CBLevel (F.restrict A).func lam ⊆ {w} := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      have h_eq : F.func (F.restrictEquiv A x) = w := by
        apply hw;
        · exact ( F.restrictEquiv A ).toEquiv x |>.2;
        · have := CBLevel_homeomorph ( F.restrictEquiv A ) ( F.func ∘ ( Subtype.val : ↑A → ↑F.domain ) ) lam;
          convert this.subset hx using 1;
          convert local_cb_derivative _ hAcl.isOpen lam using 1;
          rotate_left;
          exact Baire;
          exact inferInstance;
          exact F.func;
          constructor <;> intro h;
          · convert local_cb_derivative _ hAcl.isOpen lam using 1;
            exact inferInstance;
          · replace h := Set.ext_iff.mp h ( F.restrictEquiv A x ) ; aesop;
      exact h_eq ▸ rfl;
    refine Set.Subset.antisymm h_subset ?_;
    obtain ⟨ x, hx ⟩ := hne;
    obtain ⟨ y, hy ⟩ := F.restrictEquiv A |>.surjective ⟨ x, hx.2 ⟩;
    have h_y_in_CBLevel : y ∈ CBLevel (F.restrict A).func lam := by
      convert CBLevel_homeomorph ( F.restrictEquiv A ) ( F.func ∘ Subtype.val ) lam |>.symm.subset _;
      convert local_cb_derivative A hAcl.isOpen lam |>.symm.subset _;
      rotate_left;
      exact Baire;
      exact inferInstance;
      exact F.func;
      exact x;
      · exact hx;
      · grind;
    have h_y_in_CBLevel : (F.restrict A).func y = w := by
      exact h_subset ⟨ y, h_y_in_CBLevel, rfl ⟩;
    exact Set.singleton_subset_iff.mpr ⟨ y, by assumption, h_y_in_CBLevel ⟩;
  refine ⟨ ?_, ?_ ⟩;
  · apply cbRank_eq_add_one_of_levels (F.restrict A).func (F.restrict A).hScat lam;
    · contrapose! h_restrict_eq; aesop;
    · have h_empty : CBLevel F.func (lam + 1) = ∅ := by
        exact hF ▸ cbLevel_at_cbRank_empty F.func F.hScat;
      convert CBLevel_homeomorph ( F.restrictEquiv A ) ( F.func ∘ Subtype.val ) ( lam + 1 ) using 1;
      ext; simp;
      convert Set.notMem_empty _;
      convert local_cb_derivative ( A : Set ↑F.domain ) hAcl.isOpen ( Order.succ lam ) using 1;
      rotate_left;
      exact Baire;
      exact Pi.topologicalSpace;
      exact F.func;
      aesop;
  · exact fun x hx => h_restrict_eq.subset ⟨ x, hx, rfl ⟩

/-
**Decomposition into simple blocks with pairwise-distinct distinguished points.**
Every `F` of `CB`-rank `lam+1` (`lam` a non-zero limit) whose last-level image is infinite
decomposes as a countable disjoint union `F = ⊔ₙ Fₙ` of *simple* blocks `Fₙ = F.restrict (A n)`,
each of rank `lam+1`, whose distinguished points `y n` (the constant value taken on the top
level `CBLevel Fₙ lam`) are pairwise distinct.  This is the memoir's Decomposition Lemma step
(`JSLdecompositionlemma`, `2_prelim_memo.tex:478`) refined to a countable clopen partition.
-/
set_option maxHeartbeats 1000000 in
lemma exists_simple_block_decomposition (lam : Ordinal.{0})
    (F : ScatFun) (hF : CBRank F.func = lam + 1)
    (hinf : (F.func '' CBLevel F.func lam).Infinite) :
    ∃ (A : ℕ → Set ↑F.domain) (y : ℕ → Baire),
      F.IsDisjointUnion A ∧ Function.Injective y ∧
      (∀ n, CBRank (F.restrict (A n)).func = lam + 1) ∧
      (∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n) := by
  obtain ⟨Q, hQcl, hQdis, hQcov, hQw⟩ := exists_clopen_partition_topconst F lam hF
  generalize_proofs at *;
  -- Set V := CBLevel F.func lam and consider the following finite/enumerative setup:
  set T := CBLevel F.func lam
  set V := F.func '' T with hV
  have hVinf : V.Infinite := by
    exact hinf
  have hVcount : V.Countable := by
    choose w hw using hQw;
    exact Set.Countable.mono ( Set.image_subset_iff.mpr fun x hx => by rcases Set.mem_iUnion.mp ( hQcov.symm ▸ Set.mem_univ x ) with ⟨ k, hk ⟩ ; exact Set.mem_range.mpr ⟨ k, hw k x hk hx ▸ rfl ⟩ ) ( Set.countable_range w )
  have hVinfc : Infinite V := Set.infinite_coe_iff.mpr hVinf
  have hVcountc : Countable V := Set.countable_coe_iff.mpr hVcount
  obtain ⟨e⟩ : Nonempty (V ≃ ℕ) := nonempty_equiv_of_countable
  set y : ℕ → Baire := fun n => e.symm n |>.val with hy
  set idx : Baire → ℕ := fun v => if hv : v ∈ V then e ⟨v, hv⟩ else 0 with hidx
  set t : ℕ → ℕ := fun k => idx (Classical.choose (hQw k)) with ht
  set A : ℕ → Set ↑F.domain := fun n => ⋃ k ∈ {k | t k = n}, Q k with hA;
  refine ⟨ A, y, ?_, ?_, ?_, ?_ ⟩;
  · refine ⟨ ?_, ?_, ?_ ⟩;
    · exact fun n => clopen_regroup Q hQcl hQdis hQcov t n;
    · intro i j hij; rw [ Set.disjoint_left ] ; intro x hx hx'; simp_all +decide [ Set.mem_iUnion ] ;
      obtain ⟨ k, hk₁, hk₂ ⟩ := hx; obtain ⟨ k', hk₁', hk₂' ⟩ := hx'; specialize hQdis k k'; simp_all +decide [ Set.disjoint_left ] ;
      exact hQdis ( by rintro rfl; exact hij <| hk₁.symm.trans hk₁' ) _ _ hk₂ hk₂';
    · convert hQcov using 1;
      ext x; simp [A];
  · exact fun a b hab => by simpa using Subtype.ext hab;
  · intro n
    have hne_n : (T ∩ A n).Nonempty := by
      obtain ⟨z, hz⟩ : ∃ z ∈ T, F.func z = y n := by
        exact e.symm n |>.2;
      obtain ⟨k, hk⟩ : ∃ k, z ∈ Q k := by
        exact Set.mem_iUnion.mp ( hQcov.symm ▸ Set.mem_univ z );
      have htk : t k = n := by
        have := Classical.choose_spec ( hQw k ) z hk hz.1; aesop;
      exact ⟨ z, hz.1, Set.mem_iUnion₂.mpr ⟨ k, htk, hk ⟩ ⟩
    have hw_n : ∀ x ∈ A n, x ∈ T → F.func x = y n := by
      intro x hx hxT
      obtain ⟨k, hk⟩ : ∃ k, t k = n ∧ x ∈ Q k := by
        simp +zetaDelta only [Ordinal.add_one_eq_succ, ne_eq, countable_coe_iff, mem_image, Subtype.exists, Subtype.forall, mem_setOf_eq, mem_iUnion, exists_prop] at *;
        exact hx;
      grind +extAll
    exact (block_rank_dist F lam hF (A n) (by
    convert clopen_regroup Q hQcl hQdis hQcov t n using 1) hne_n (y n) hw_n).left;
  · -- By definition of $y$, we know that $y n = w k$ for some $k$ such that $t k = n$ and $w k \in V$.
    intro n
    obtain ⟨k, hk⟩ : ∃ k, t k = n ∧ Classical.choose (hQw k) ∈ V := by
      have := e.surjective n;
      obtain ⟨ a, ha ⟩ := this;
      obtain ⟨ x, hx ⟩ := a.2;
      obtain ⟨ k, hk ⟩ := Set.mem_iUnion.mp ( hQcov.symm ▸ Set.mem_univ x );
      use k;
      have := Classical.choose_spec ( hQw k ) x hk hx.1; aesop;
    -- By definition of $y$, we know that $y n = w k$ for some $k$ such that $t k = n$ and $w k \in V$. Therefore, $F.func x = w k$ for all $x \in A n$.
    have hF_eq_wk : ∀ x ∈ A n, x ∈ T → F.func x = Classical.choose (hQw k) := by
      intros x hx hxT
      obtain ⟨k', hk'⟩ : ∃ k', t k' = n ∧ x ∈ Q k' := by
        exact Set.mem_iUnion₂.mp hx |> fun ⟨ k', hk' ⟩ => ⟨ k', hk'.1, hk'.2 ⟩;
      have hF_eq_wk : F.func x = Classical.choose (hQw k') := by
        exact Classical.choose_spec ( hQw k' ) x hk'.2 hxT;
      have hF_eq_wk : Classical.choose (hQw k') ∈ V := by
        exact ⟨ x, hxT, hF_eq_wk ⟩;
      have hF_eq_wk : e ⟨Classical.choose (hQw k'), hF_eq_wk⟩ = e ⟨Classical.choose (hQw k), hk.2⟩ := by
        grind;
      exact ‹F.func x = choose ( hQw k' ) ›.trans ( by simpa using e.injective hF_eq_wk );
    have hF_eq_wk : ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = Classical.choose (hQw k) := by
      apply block_rank_dist F lam hF (A n) (clopen_regroup Q hQcl hQdis hQcov t n) (by
      obtain ⟨ x, hx ⟩ := hk.2;
      obtain ⟨ k', hk' ⟩ := Set.mem_iUnion.mp ( hQcov.symm ▸ Set.mem_univ x );
      have h_t_k'_eq_n : t k' = n := by
        grind;
      exact ⟨ x, hx.1, Set.mem_iUnion₂.mpr ⟨ k', h_t_k'_eq_n, hk' ⟩ ⟩) (Classical.choose (hQw k)) (by
      exact hF_eq_wk) |>.2;
    grind

theorem Generators_lambdaPlusOne_finitely_generates_of_infinite_degree (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (lam + 1))) :
    ∀ F : ScatFun, CBRank F.func = lam + 1 → (F.func '' CBLevel F.func lam).Infinite →
      F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  intro F hF hinf
  obtain ⟨A, y, hdu, hy_inj, hrank, hdist⟩ :=
    exists_simple_block_decomposition lam F hF hinf
  rcases Set.finite_or_infinite {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)} with
    hfin | hinf'
  · rcases Set.eq_empty_or_nonempty {n | Equiv (F.restrict (A n)) (succMaxFun lam hlam)} with
      hempty | hne
    · exact case_N1_empty lam hlim hlam (twoBQO_levelLT_of_add_one lam hbqo) F A hdu y hy_inj
        hrank hdist hempty
    · exact case_N1_finite_nonempty lam hlim hlam (twoBQO_levelLT_of_add_one lam hbqo) F A hdu y
        hy_inj hrank hdist hF hfin hne
  · exact case_N1_infinite lam hlim hlam (add_one_lt_omega1 lam hlam) F A y hy_inj hrank hdist
      hF hinf'

/-
**Every successor `λ+1` of a non-zero limit `λ` is finitely generated by `𝒢_{λ+1}`.**
The `λ` non-zero-limit instance of `FGatsuccessoroflimit` (`5_precise_struct_memo.tex:377-423`),
combining the finite- and infinite-`CB`-degree cases.

Takes the same `hbqo : TwoBQO (LevelLT.reduces (lam+1))` induction hypothesis as
`Generators_lambdaPlusOne_finitely_generates_of_finite_degree` above (2-BQO on `𝒞_{≤λ}`); see
that theorem's docstring for why this (rather than the nominally weaker `𝒞_{<λ}`) is the
natural hypothesis to carry at this level.

## Provided solution

By `finitedegreedamuddafuckaz` (`4_centered_memo.tex:372`), split on whether the last `CB`-level's
image `F.func '' CBLevel F.func lam` is finite or infinite
(`Set.finite_or_infinite`) and dispatch to
`Generators_lambdaPlusOne_finitely_generates_of_finite_degree` or
`Generators_lambdaPlusOne_finitely_generates_of_infinite_degree` respectively.
-/
theorem Generators_lambdaPlusOne_finitely_generates (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam : lam < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (lam + 1))) :
    ∀ F : ScatFun, CBRank F.func = lam + 1 → F ∈ FinGl (Generators (lam + 1)).toFinFun := by
  intro F hF;
  have := Generators_lambdaPlusOne_finitely_generates_of_infinite_degree lam hlim hlam hbqo F hF;
  by_cases h : Set.Finite ( F.func '' CBLevel F.func lam ) <;> simp_all +decide;
  apply Generators_lambdaPlusOne_finitely_generates_of_finite_degree lam hlim hlam hbqo F hF h

end ScatFun

end