import WqoContinuousFunctions.DoubleSuccessor.Diagonal.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Diagonal theorem, second case — wedge membership (`6_double_successor_memo.tex`)

Shows the wedge generator assembled in the second case lands in the double-successor generator
set `𝒢_{α+2}` (`secondCase_wedge_mem`), via the chain: the centered level `𝒞_{α+1}` and its
`ω`-image sit inside `𝒢_{α+1}`, so their `wedge`/`pglFinset` combinations lie in a `genStep`
producing `𝒢_{α+2}`. Also provides the nonempty-column witness `secondCase_exists_nonempty_column`.
-/

/-
The centered level `𝒞_{α+1}` together with its `ω`-image is contained in the generator
level `𝒢_{α+1}` (both appear as the first two clauses of the `genStep` producing `𝒢_{α+1}`).
-/
lemma centered_union_omegaImage_subset_generators (α : Ordinal.{0}) (_hα : α < omega1) :
    ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)) ⊆
      ScatFun.Generators (α + 1) := by
  have hlim : Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 :=
    Ordinal.limitPart_isLimit_or_zero α
  have hsum : α.limitPart + (α.natPart : Ordinal.{0}) = α :=
    (Ordinal.eq_limitPart_add_natPart α).symm
  have key := ScatFun.Generators_add_succ_eq hlim α.natPart
  rw [hsum] at key
  rw [key, ScatFun.genStep]
  refine Finset.union_subset (fun a ha => ?_) (fun a ha => ?_)
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ ha))

/-
Pure `genStep`-bookkeeping: a `wedgeFinset` built from a nonempty finite set `S` of nonempty
subsets of `Gprev` and a diagonal subset `D ⊆ Cn` lies in `genStep Cn Gprev`. This is the
`Finset.mem_biUnion` + `Finset.mem_image` unfolding of `genStep`.
-/
lemma wedgeFinset_mem_genStep_of_mem {Cn Gprev : Finset ScatFun}
    {S : Finset (Finset ScatFun)}
    (hS : S ∈ ScatFun.nonemptySubsets (ScatFun.nonemptySubsets Gprev))
    {D : Finset ScatFun} (hD : D ⊆ Cn) :
    ScatFun.wedgeFinset (S.toList.map Finset.toList) D.toList ∈ ScatFun.genStep Cn Gprev := by
  exact Finset.mem_union_right _ ( Finset.mem_biUnion.mpr ⟨ S, hS, Finset.mem_image.mpr ⟨ D, Finset.mem_powerset.mpr hD, rfl ⟩ ⟩ )

/-
Transport `genStep`-membership at the double successor back to `𝒢_{α+2}`, via
`Generators_add_succ_eq`.
-/
lemma mem_generators_doubleSucc_of_mem_genStep (α : Ordinal.{0}) (_hα : α < omega1)
    {x : ScatFun}
    (hx : x ∈ ScatFun.genStep (ScatFun.Centered (α + 1 + 1)) (ScatFun.Generators (α + 1))) :
    x ∈ ScatFun.Generators (α + 1 + 1) := by
  by_contra h_contra;
  simp_all +decide [ ScatFun.Generators ];
  convert ScatFun.Generators_add_succ_eq ( show Order.IsSuccLimit ( Order.succ α |> Ordinal.limitPart ) ∨ ( Order.succ α |> Ordinal.limitPart ) = 0 from ?_ ) ( Order.succ α |> Ordinal.natPart ) using 1;
  · simp_all +decide [ ScatFun.Generators ];
    grind +suggestions;
  · grind +suggestions

/-
**Second case — membership of the wedge half** (`6_double_successor_memo.tex:305`). The
diagonal wedge `⋀((Mg i) ∣ gl D)` — vertical columns `v i = gl (Mg i)` with each
`Mg i ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}` and diagonal `gl D` with `D ⊆ 𝒞_{α+2}` — is a `genStep` wedge
generator (up to column dedup/reorder and dropping empty columns), hence lies in `FinGl 𝒢_{α+2}`.
This is the `case hwedge` obligation of `diagonalTheorem_secondCase_construction`.

**Provided solution.** Model on `wedge_maxFun_minFun_mem_Generators_add_one`
(`ScatFun/LevelsFinitelyGenerated/LambdaPlusOne.lean:105`).

1. **Reduce to distinct nonempty columns.** Let `S = {Mg i | i} \ {∅}` as a `Finset (Finset ScatFun)`
   (dedup + drop empties) and enumerate it as `v' : Fin S.card → ScatFun`, `v' j = glList (Sⱼ)`.
   The source columns `v i = glList (Mg i)` and `v'` are mutually dominating, so
   `ScatFun.wedge_domination_equiv` (`ScatFun/Wedge/Reindex.lean`) gives
   `Equiv (wedge v (glList D)) (wedge v' (glList D))`. *(Depends on `wedge_reindex_reduces`,
   the open geometric core of `Reindex.lean`.)*
2. **Recognise the `genStep` generator.** With `α+1+1` a successor, `Generators_add_one_eq`
   (via `Generators_add_succ_eq`) unfolds `𝒢_{α+2} = genStep (𝒞_{α+2}) (𝒢_{α+1})`. Each `Mg i` is a
   nonempty subset of `𝒢_{α+1}` (since `𝒞_{α+1} ⊆ 𝒢_{α+1}` and `ω{𝒞_{α+1}} ⊆ 𝒢_{α+1}` by the
   `omegaImage` clause of `genStep`, `hMgsub`), and `D ⊆ 𝒞_{α+2} = Cn` (`hDsub`). So
   `S ∈ nonemptySubsets (nonemptySubsets 𝒢_{α+1})` and `D ∈ 𝒞_{α+2}.powerset`, exhibiting
   `wedgeFinset (S.toList.map Finset.toList) D.toList ∈ genStep …` (`Finset.mem_biUnion` +
   `Finset.mem_image`, exactly as in `wedge_maxFun_minFun_mem_Generators_add_one`).
3. **Close.** `wedgeFinset … ≡ wedge v' (glList D)` by `wedge_congr_equiv` (+ `glList_single_equiv`
   bookkeeping), so with step 1 `wedge v (glList D) ≡ wedgeFinset … ∈ 𝒢_{α+2}`; conclude via
   `finGl_single_of_equiv`.
-/
theorem secondCase_wedge_mem
    (α : Ordinal.{0}) (hα : α < omega1)
    {n : ℕ} (Mg : Fin n → Finset ScatFun) (D : Finset ScatFun)
    (hMgsub : ∀ i, Mg i ⊆
      ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)))
    (hDsub : D ⊆ ScatFun.Centered (α + 1 + 1))
    (hne : ((Finset.univ.image Mg).erase ∅).Nonempty) :
    ScatFun.wedge (fun i => ScatFun.glList (Mg i).toList) (ScatFun.glList D.toList) ∈
      ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
  convert ScatFun.finGl_single_of_equiv _ _;
  exact ScatFun.wedgeFinset ( ( Finset.univ.image Mg ).erase ∅ |> Finset.toList |> List.map Finset.toList ) D.toList;
  · exact mem_generators_doubleSucc_of_mem_genStep α hα ( wedgeFinset_mem_genStep_of_mem ( by
      refine Finset.mem_erase_of_ne_of_mem hne.ne_empty ( Finset.mem_powerset.mpr ?_ );
      simp +decide only [ScatFun.nonemptySubsets, Ordinal.add_one_eq_succ, Finset.subset_iff, Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_powerset, and_imp, forall_exists_index];
      exact fun x hx i hi => ⟨ hx, fun y hy => by have := hMgsub i ( hi ▸ hy ) ; exact centered_union_omegaImage_subset_generators α hα this ⟩ ) ( by
      assumption ) );
  · convert ScatFun.wedge_domination_equiv _ _ _ _ _;
    · intro i;
      by_cases hi : Mg i = ∅;
      · obtain ⟨ j, hj ⟩ := hne;
        obtain ⟨ k, hk ⟩ := Finset.mem_image.mp ( Finset.mem_of_mem_erase hj );
        use ⟨ List.idxOf j ( ( Finset.image Mg Finset.univ ).erase ∅ |> Finset.toList ), by
          exact List.idxOf_lt_length_iff.mpr ( by aesop ) |> lt_of_lt_of_le <| by simp +decide ; ⟩
        generalize_proofs at *;
        convert ScatFun.reduces_of_isEmpty_domain _;
        simp +decide only [ScatFun.glList, hi, Finset.toList_empty, List.getD_eq_getElem?_getD, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, ScatFun.gl_domain, isEmpty_coe_sort];
        ext; simp [GluingSet];
        exact fun x y hy => False.elim <| hy.elim;
      · obtain ⟨ j, hj ⟩ := Finset.exists_toFinFun_eq ( Finset.erase ( Finset.image Mg Finset.univ ) ∅ ) ( show Mg i ∈ Finset.erase ( Finset.image Mg Finset.univ ) ∅ from Finset.mem_erase_of_ne_of_mem hi ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) );
        use ⟨ j, by
          simp ⟩
        generalize_proofs at *;
        simp +decide only [← hj, Finset.toFinFun, List.get_eq_getElem, Fin.val_cast, List.getElem_map];
        exact ScatFun.Equiv.refl _ |>.1;
    · intro j;
      have := List.get_mem ( List.map Finset.toList ( Finset.toList ( Finset.erase ( Finset.image Mg Finset.univ ) ∅ ) ) ) j;
      simp +zetaDelta only [Ordinal.add_one_eq_succ, List.get_eq_getElem, List.getElem_map, List.mem_map, Finset.mem_toList, Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_univ, true_and, ↓existsAndEq, and_true] at *;
      obtain ⟨ i, hi, hi' ⟩ := this; use i; simp +decide [ hi' ] ;
      convert ScatFun.Equiv.refl _ |>.1 using 1

/-
The pointed gluing of the empty finite set is the pointed gluing of copies of the trivial
function `glList [] (≡ empty)`, hence has CB-rank `succ 0 = 1`.
-/
lemma pglFinset_empty_cbRank :
    CBRank (ScatFun.pglFinset (∅ : Finset ScatFun)).func = 1 := by
  convert cbRank_pgl_regular ( fun _ => ScatFun.glList [] ) ( scatFun_const_isRegularSeq ( ScatFun.glList [] ) ) using 1;
  · unfold ScatFun.pglFinset ScatFun.glList;
    grind +extAll;
  · -- Since the function is constant, its CB-rank is the same as the CB-rank of its value.
    have h_const : CBRank (ScatFun.glList []).func = 0 := by
      convert ScatFun.empty_cbRank using 1;
      convert cbRank_eq_of_equiv _;
      exact ScatFun.gl_equiv_empty_of_forall_empty fun _ => rfl;
    aesop

/-
**Second case — a genuine (nonempty) vertical column exists.** In the second case (`hcase`,
some cocenter-`y` piece has rank `> λ+1`), at least one representative `gM i` has a nonempty
`pgl`-decomposition `Mg i`. This is the honest hypothesis of `secondCase_wedge_mem`: the memoir's
wedge always has at least one genuine vertical column (a purely trivial wedge would fail to be a
`genStep` generator).
-/
lemma secondCase_exists_nonempty_column
    (α : Ordinal.{0}) (_hα : α < omega1)
    (F : ScatFun) (_hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire}
    (hfine : ∀ P ∈ Part, α.limitPart < CBRank (F.restrict P).func)
    (hcase : ¬ ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1)
    {n : ℕ} (gM : Fin n → ScatFun) (Mg : Fin n → Finset ScatFun)
    (hgpgl : ∀ i, ScatFun.Equiv (gM i) (ScatFun.pglFinset (Mg i)))
    (hMcover : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
        α.limitPart + 1 < CBRank (F.restrict P).func →
          ∃ i, ScatFun.Equiv (F.restrict P) (gM i)) :
    ((Finset.univ.image Mg).erase ∅).Nonempty := by
  obtain ⟨P, hP⟩ : ∃ P : Set ↑F.domain, ∃ hP : P ∈ Part, hA.cocenterOf hP = y ∧ α.limitPart + 1 < CBRank (F.restrict P).func := by
    push_neg at hcase;
    obtain ⟨ P, hP₁, hP₂, hP₃ ⟩ := hcase; exact ⟨ P, hP₁, hP₂, lt_of_le_of_ne ( by simpa using Order.add_one_le_of_lt ( hfine P hP₁ ) ) ( Ne.symm hP₃ ) ⟩ ;
  obtain ⟨hP, hPcocenter, hPrank⟩ := hP
  obtain ⟨i, hi⟩ := hMcover P hP hPcocenter hPrank;
  refine ⟨ Mg i, ?_ ⟩;
  by_cases hi_empty : Mg i = ∅;
  · have h_contra : CBRank (F.restrict P).func = 1 := by
      have h_contra : ScatFun.Equiv (F.restrict P) (ScatFun.pglFinset (∅ : Finset ScatFun)) := by
        exact ScatFun.Equiv.trans hi ( hgpgl i |> fun h => by simpa [ hi_empty ] using h );
      exact cbRank_eq_of_equiv h_contra ▸ pglFinset_empty_cbRank;
    simp_all +decide [ Ordinal.add_one_eq_succ ];
    exact absurd hPrank ( ne_of_gt ( Ordinal.succ_pos _ ) );
  · exact Finset.mem_erase_of_ne_of_mem hi_empty ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) )


end
