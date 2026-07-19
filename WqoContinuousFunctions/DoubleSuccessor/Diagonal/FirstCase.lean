import WqoContinuousFunctions.DoubleSuccessor.Diagonal.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-! ## The Diagonal Theorem (`6_double_successor_memo.tex:272-386`)

The memoir proof (`:277-386`) writes `α = λ + n` (`λ = α.limitPart`), sets
`𝒫_M = 𝒫 \ 𝒫^{≠y}` (pieces with cocenter `y`), `𝒫_D = 𝒫^{≠y}`, and **distinguishes two cases** on
the `CB`-ranks of the `𝒫_M`-pieces. We mirror this with a `by_cases` in `diagonalTheorem`
dispatching to two statement-lemmas, one per case, each proving the *full* conclusion
(`∃ g ∈ FinGl 𝒢_{α+2}, F ≤ g ∧ ∀ U ∋ y, g ≤ F⇂U`). Both cases are fully proved; the second case's
construction is developed in `Diagonal/SecondCase/` (`diagonalTheorem_secondCase_setup`). Their
docstrings record the memoir's construction of `g` and the two reductions it needs. -/

/-! ### First case (`6_double_successor_memo.tex:287-297`)

The hypothesis `hcase` is the memoir's "`CB(F↾P) = λ+1` for all `P ∈ 𝒫_M`" (`𝒫_M` = pieces with
cocenter `y`, here `hA.cocenterOf hP = y`).

## Provided solution (`:287-297`)

Since `CB(F) = α+2 = λ+n+2`, some `P ∈ 𝒫_D` has `CB(F↾P) = α+2` (`CBRankofclopenunion`). Choose
a finite set of representatives `D ⊆ 𝒞_{α+2}` for `{F↾P | P ∈ 𝒫_D}` (`FGconsequences`) and pick
`h ∈ D` with `CB(h) = α+2`. Set **`g := ω D`** (`ScatFun.omega (ScatFun.glList D.toList)`, or the
`ω`-image of the finite gluing). Then:

* **`F ≤ g`** (`:293`): `F ≤ gl_{P∈𝒫} F↾P ≤ (gl_{P∈𝒫_D} F↾P) ⊕ (gl_{P∈𝒫_M} F↾P) ≤ ω D ⊕
  ω(pgl ℓ_λ) ≤ ω D`, where each `𝒫_M`-piece satisfies `F↾P ≤ pgl ℓ_λ ≤ h` (`Maxfunctions` +
  `ConsequencesGeneralStructureThm`, since `CB(F↾P) = λ+1`), via `Gluingasupperbound`(`_cor`).
* **`g ≤ F⇂U`** for every clopen `U ∋ y` (`:295`): strong solvability (clause 2) makes, for each
  `g' ∈ D`, the set `{y_P | P ∈ 𝒫_D, y_P ∈ U, g' ≤ F↾P}` infinite; then `ω D ≤ F⇂U` by
  `intertwine_reductions_omega_centered` (`ScatFun/PreciseStructure/IntertwineOmegaCentered.lean`,
  proved).

Membership `ω D ∈ FinGl 𝒢_{α+2}` is the `ω`-image generator clause (`ScatFun/Generators/Defs.lean`).

## Scaffold

Following the `verticalTheorem` dispatcher style, `diagonalTheorem_firstCase` is assembled from a
representative-selection lemma and the three conjunct-lemmas below (all now proved), with
`g = ω D = ScatFun.omega (ScatFun.glList D.toList)`:

* `diagonalTheorem_firstCase_representatives` — the `FGconsequences`/`CBRankofclopenunion` content:
  a finite `D ⊆ 𝒞_{α+2}` representing `{F↾P | P ∈ 𝒫_D}`, with a rank-`α+2` element.
* `diagonalTheorem_firstCase_omegaD_mem` — `ω D ∈ FinGl 𝒢_{α+2}`.
* `diagonalTheorem_firstCase_left` — `F ≤ ω D`.
* `diagonalTheorem_firstCase_right` — `ω D ≤ F⇂U` for every clopen `U ∋ y`. -/

/--
**A `𝒫_D`-piece attains the top rank `α+2`.** Since `CB(F) = α+2` is the supremum of the
piece ranks (`cbRank_eq_iSup_restrict`) and every `𝒫_M`-piece (cocenter `y`) has rank `λ+1 < α+2`
(`hcase`), some piece with cocenter `≠ y` must have rank exactly `α+2`.
-/
lemma exists_piece_cocenter_ne_rank_doubleSucc
    (α : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1) :
    ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ CBRank (F.restrict P).func = α + 1 + 1 := by
  obtain ⟨P, hP⟩ : ∃ P : Set (↥F.domain), P ∈ Part ∧ CBRank (F.restrict P).func = α + 1 + 1 := by
    obtain ⟨A, hdu, hAmem⟩ : ∃ A : ℕ → Set (↥F.domain), F.IsDisjointUnion A ∧ ∀ i, A i ∈ Part ∨ A i = ∅ := by
      obtain ⟨P₀, hP₀⟩ : ∃ P₀ ∈ Part, True := by
        contrapose! hFrank; simp_all +decide ;
        cases hA;
        cases isEmpty_or_nonempty F.domain <;> simp_all +decide [ Set.ext_iff ];
        rw [ show F.func = fun _ => Classical.choice ( show Nonempty Baire from ⟨ y ⟩ ) from funext fun x => False.elim <| ‹∀ x : Baire, x∉F.domain› _ x.2 ] ; simp +decide [ CBRank ];
        rw [ show { α : Ordinal.{0} | CBLevel ( fun _ => choice ( show Nonempty Baire from ⟨ y ⟩ ) ) α = CBLevel ( fun _ => choice ( show Nonempty Baire from ⟨ y ⟩ ) ) ( Order.succ α ) } = Set.univ from ?_ ] ; simp +decide ;
        · exact ne_of_lt ( Ordinal.succ_pos _ );
        · grind;
      obtain ⟨A, hdu, hAmem, -⟩ := exists_partition_enumeration hA P₀ hP₀.1
      exact ⟨A, hdu, hAmem⟩;
    obtain ⟨i, hi⟩ : ∃ i : ℕ, CBRank (F.restrict (A i)).func = α + 1 + 1 := by
      have h_sup : ⨆ i, CBRank (F.restrict (A i)).func = α + 1 + 1 := by
        rw [ ← hFrank, cbRank_eq_iSup_restrict F A hdu ];
      by_contra h_contra;
      have h_le : ∀ i, CBRank (F.restrict (A i)).func ≤ α + 1 := by
        intro i
        by_cases h_eq : CBRank (F.restrict (A i)).func = α + 1 + 1;
        · exact False.elim <| h_contra ⟨ i, h_eq ⟩;
        · have h_le : CBRank (F.restrict (A i)).func ≤ α + 1 + 1 := by
            exact h_sup ▸ Ordinal.le_iSup _ _;
          cases h_le.eq_or_lt <;> simp_all +decide [ Order.lt_succ_iff ];
      exact absurd ( h_sup ▸ ciSup_le h_le ) ( by simp +decide );
    cases hAmem i <;> simp_all +decide;
    · exact ⟨ _, ‹_›, hi ⟩;
    · simp_all +decide [ ScatFun.restrict ];
      simp_all +decide [ ScatFun.restrictEquiv ];
      simp_all +decide [ Function.comp_def ];
      contrapose! hi;
      convert ScatFun.empty_cbRank.symm ▸ show 0 ≠ Order.succ ( Order.succ α ) from ne_of_lt ( Ordinal.succ_pos _ ) using 1;
      convert rfl;
      · simp +decide [ ScatFun.empty, ‹A i = ∅› ];
        exact fun h => h.elim;
      · aesop;
      · grind +splitImp;
      · aesop;
  refine ⟨ P, hP.1, ?_, hP.2 ⟩;
  intro hy
  have := hcase P hP.left hy
  simp only [hP.right, Ordinal.add_one_eq_succ, Order.succ_eq_succ_iff] at this;
  rw [ eq_comm ] at this;
  rw [ Ordinal.eq_limitPart_add_natPart α ] at this;
  rw [ Ordinal.limitPart_add_natCast ] at this;
  · rw [ eq_comm, Order.succ_eq_add_one ] at this;
    exact absurd this ( ne_of_gt ( lt_of_le_of_lt ( by norm_num ) ( Order.lt_succ _ ) ) );
  · exact Ordinal.limitPart_isLimit_or_zero α

/-- **First-case representatives** (`6_double_successor_memo.tex:288-290`, `FGconsequences` +
`CBRankofclopenunion`). Under `FG(≤α+1)` and `CB(F) = α+2`, with every `𝒫_M`-piece of rank `λ+1`
(`hcase`), there is a finite `D ⊆ 𝒞_{α+2}` such that (i) some `h ∈ D` has rank `α+2` (a `𝒫_D`-piece
attains `CB(F) = α+2`, all `𝒫_M`-pieces being of rank `λ+1 < α+2`), (ii) every `𝒫_D`-piece is
`≡` to some `g ∈ D`, and (iii) every `g ∈ D` is realised by a `𝒫_D`-piece. **Proved**: the
finiteness comes from `𝒞_{α+2}` being a `Finset` — `D` is the subset of `𝒞_{α+2}` realised by a
`𝒫_D`-piece (`centered_equiv_mem_Centered_le_doubleSucc` places each piece there, using the
fineness hypothesis `hfine` for the required rank lower bound), and the rank-`α+2` witness comes
from `exists_piece_cocenter_ne_rank_doubleSucc` via `cbRank_eq_iSup_restrict`.

Note: this needs the **fineness** hypothesis `hfine` (every piece has rank `> λ`), which the
original scaffold omitted. It is genuinely required: `𝒞_{α+2}` has minimum rank `λ+1`, so a
cocenter-`≠ y` piece of rank `≤ λ` could not be represented. At the call site
(`diagonalTheorem_firstCase`) `hfine` is supplied by strong solvability (`hss.1.2`, fineness). -/
theorem diagonalTheorem_firstCase_representatives
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1)
    (hfine : ∀ P ∈ Part, α.limitPart < CBRank (F.restrict P).func) :
    -- D is a set of representatives for the restrictions of F to the pieces of 𝒫_D (the pieces with cocenter ≠ y)
    ∃ D : Finset ScatFun, D ⊆ ScatFun.Centered (α + 1 + 1) ∧
      (∃ h ∈ D, CBRank h.func = α + 1 + 1) ∧
      (∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
        ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g) ∧
      (∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g) := by
  classical
  obtain ⟨P₀, hP₀mem, hP₀ne, hP₀rank⟩ :=
    exists_piece_cocenter_ne_rank_doubleSucc α F hFrank hA hcase
  -- Every piece has rank `≤ α+2` (it reduces into `F`).
  have hrank_le : ∀ P : Set ↑F.domain, CBRank (F.restrict P).func ≤ α + 1 + 1 := by
    intro P
    have h1 : (F.restrict P).Reduces (F.restrict Set.univ) :=
      restrict_reduces_of_subset F (Set.subset_univ P)
    have h2 : CBRank (F.restrict P).func ≤ CBRank (F.restrict Set.univ).func :=
      ContinuouslyReduces.rank_monotone (F.restrict P).hScat (F.restrict Set.univ).hScat h1
    have h3 : CBRank (F.restrict Set.univ).func = CBRank F.func := by
      rw [cbRank_restrict_eq]
      exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
    rw [h3, hFrank] at h2; exact h2
  -- `D` = the (finite) set of `𝒞_{α+2}`-members realised by a `𝒫_D`-piece.
  refine ⟨(ScatFun.Centered (α + 1 + 1)).filter
      (fun g => ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g),
    Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · -- (i) the top-rank piece `P₀` supplies a rank-`α+2` member.
    obtain ⟨h, hhmem, hhequiv⟩ :=
      centered_equiv_mem_Centered_le_doubleSucc α hα hFG (F.restrict P₀)
        (hfine P₀ hP₀mem) (le_of_eq hP₀rank) (hA.centered P₀ hP₀mem)
    refine ⟨h, Finset.mem_filter.mpr ⟨hhmem, P₀, hP₀mem, hP₀ne, hhequiv⟩, ?_⟩
    rw [← cbRank_eq_of_equiv hhequiv]; exact hP₀rank
  · -- (ii) every `𝒫_D`-piece is `≡` to a member.
    intro P hP hPy
    obtain ⟨h, hhmem, hhequiv⟩ :=
      centered_equiv_mem_Centered_le_doubleSucc α hα hFG (F.restrict P)
        (hfine P hP) (hrank_le P) (hA.centered P hP)
    exact ⟨h, Finset.mem_filter.mpr ⟨hhmem, P, hP, hPy, hhequiv⟩, hhequiv⟩
  · -- (iii) every member is realised, by construction of the filter.
    intro g hg
    exact (Finset.mem_filter.mp hg).2

/-- **First case, membership** (`6_double_successor_memo.tex:297`): `ω D ∈ FinGl 𝒢_{α+2}`.
`ω D = ω(gl D) ≡ gl_{d ∈ D} (ω d)` (`omega_glList_equiv_glList_omega`), and each `ω d` (for
`d ∈ 𝒞_{α+2}`) is *itself* a generator — the `ω`-image clause of `genStep`
(`omegaImage (Centered (α+2)) ⊆ Generators (α+2)`) — so `ω D` is `≡` a finite gluing of
`𝒢_{α+2}`-members (`finGl_of_equiv_glList`). No `FG` hypothesis needed. -/
theorem diagonalTheorem_firstCase_omegaD_mem
    (α : Ordinal.{0}) (_hα : α < omega1) {D : Finset ScatFun}
    (hDsub : D ⊆ ScatFun.Centered (α + 1 + 1)) (_hDne : D.Nonempty) :
    ScatFun.omega (ScatFun.glList D.toList) ∈
      ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
  set lam := α.limitPart with hlamdef
  set m := α.natPart with hmdef
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hαsucc : (α + 1 : Ordinal) = lam + ↑(m + 1) := by
    rw [Ordinal.eq_limitPart_add_natPart α, Nat.cast_add, Nat.cast_one, add_assoc]
  -- `ω(gl D) ≡ gl (map ω D)`; reduce to: each `ω d` is a generator.
  refine ScatFun.finGl_of_equiv_glList ?_ (ScatFun.omega_glList_equiv_glList_omega D.toList)
  intro w hw
  simp only [List.mem_map, Finset.mem_toList] at hw
  obtain ⟨d, hdD, rfl⟩ := hw
  have hdC : d ∈ ScatFun.Centered (α + 1 + 1) := hDsub hdD
  -- `ω d ∈ omegaImage (𝒞_{α+2}) ⊆ genStep ⊆ 𝒢_{α+2}`.
  rw [hαsucc] at hdC ⊢
  rw [ScatFun.Generators_add_succ_eq hlim (m + 1)]
  refine Finset.mem_union_right _ ?_
  unfold ScatFun.genStep
  exact Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem ScatFun.omega hdC))

/-- **First case, `𝒫_M`-piece bound** (`6_double_successor_memo.tex:291-292`, `Maxfunctions` +
`ConsequencesGeneralStructureThm`). A piece `P` with cocenter `y` (so `CB(F↾P) = λ+1`, `hPrank`)
reduces into `gl D` along `F↾P ≤ pgl ℓ_λ ≤ h ≤ gl D`:

* `F↾P ≤ pgl ℓ_λ = succMaxFun λ` — `F↾P` is centered, hence *simple* (`scatteredCentered_isSimple`),
  and a simple function of rank `λ+1` reduces to the maximum `succMaxFun λ`
  (`simple_reduces_succMaxFun`, from `maxFun_is_maximum` item 2);
* `succMaxFun λ ≤ h` — the rank-`α+2` element `h ∈ D` has `CB(h) = α+2 ≥ λ+2`, so
  `consequencesGeneralStructure_succMaxFun_le` (item 2) applies;
* `h ≤ gl D` — `mem_reduces_glList`. -/
theorem diagonalTheorem_firstCase_pieceM_reduces_glList
    (α : Ordinal.{0}) (hα : α < omega1)
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {D : Finset ScatFun} (_hDsub : D ⊆ ScatFun.Centered (α + 1 + 1))
    (hDrank : ∃ h ∈ D, CBRank h.func = α + 1 + 1)
    {P : Set ↑F.domain} (hP : P ∈ Part)
    (hPrank : CBRank (F.restrict P).func = α.limitPart + 1) :
    ScatFun.Reduces (F.restrict P) (ScatFun.glList D.toList) := by
  set lam := α.limitPart with hlamdef
  have hlamlt : lam < omega1 :=
    lt_of_le_of_lt le_self_add (Ordinal.eq_limitPart_add_natPart α ▸ hα)
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hsimple : SimpleFun (F.restrict P).func :=
    scatteredCentered_isSimple (F.restrict P).func (F.restrict P).hScat (hA.centered P hP)
  obtain ⟨h, hhD, hhrank⟩ := hDrank
  refine (simple_reduces_succMaxFun lam hlamlt (F.restrict P) hPrank hsimple).trans
    ((consequencesGeneralStructure_succMaxFun_le lam hlamlt hlim h ?_).trans
      (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hhD)))
  -- `succ (succ λ) = λ+2 ≤ λ+n+2 = α+2 = CB(h)`.
  rw [hhrank, ← Ordinal.add_one_eq_succ, ← Ordinal.add_one_eq_succ,
    Ordinal.eq_limitPart_add_natPart α]
  gcongr
  exact le_self_add

/-- **First case, left reduction** `F ≤ ω D` (`6_double_successor_memo.tex:291-293`). Each piece
reduces into `gl D` — `𝒫_D`-pieces by `≡` to some `g ∈ D` (`hDrep`), `𝒫_M`-pieces by
`diagonalTheorem_firstCase_pieceM_reduces_glList` — so `F ≤ ω(gl D)` by
`ScatFun.IsCPartition.reduces_omega_of_forall_piece_le`. **Proved** modulo the isolated
`𝒫_M`-piece structure lemma. -/
theorem diagonalTheorem_firstCase_left
    (α : Ordinal.{0}) (hα : α < omega1)
    (F : ScatFun) (_hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1)
    {D : Finset ScatFun} (hDsub : D ⊆ ScatFun.Centered (α + 1 + 1))
    (hDrank : ∃ h ∈ D, CBRank h.func = α + 1 + 1)
    (hDrep : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g) :
    ScatFun.Reduces F (ScatFun.omega (ScatFun.glList D.toList)) := by
  refine hA.reduces_omega_of_forall_piece_le (fun P hP => ?_)
  by_cases hPy : hA.cocenterOf hP = y
  · exact diagonalTheorem_firstCase_pieceM_reduces_glList α hα F hA hDsub hDrank hP
      (hcase P hP hPy)
  · obtain ⟨g, hgD, hPg⟩ := hDrep P hP hPy
    exact hPg.1.trans (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hgD))

/-- **First case, right reduction — core infiniteness step** (`6_double_successor_memo.tex:295`).
For `g ∈ D` (realised by some `P₀ ∈ 𝒫_D` via `hDreal`) and any clopen `U ∋ y`, the intertwine set
`IntertwineSet (F⇂U) g = {z | ∀ V ∈ 𝓝 z, g ≤ (F⇂U)⇂V}` is **infinite**.

Memoir argument: strong solvability clause 2 iterated on `P₀` gives, inside every clopen `V ∋ y`
with `V ⊆ U`, a piece `Q ∈ 𝒫_D` with `y_Q ∈ V` and `F↾P₀ ≤ F↾Q`, hence `g ≤ F↾Q`. As `V` shrinks
to `y` (the unique accumulation point), the cocenters `y_Q` are infinitely many distinct points of
`U`; and each such `y_Q ∈ IntertwineSet (F⇂U) g` because `F↾Q` is centered with cocenter `y_Q ∈ U`,
so `g ≤ F↾Q ≤ (F↾Q)⇂V' ≤ (F⇂U)⇂W` for a clopen `V' ∋ y_Q` inside `U ∩ W`
(`reduces_coRestrict_cocenter_nbhd` + `coRestrict_restrict_reduces` + `coRestrict_inter_reduces`).
**Proved.** -/
theorem diagonalTheorem_firstCase_intertwineSet_infinite
    (α : Ordinal.{0})
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hss : hA.IsStronglySolvableAt α.limitPart y)
    {D : Finset ScatFun}
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    {g : ScatFun} (hg : g ∈ D) {U : Set Baire} (hUcl : IsClopen U) (hyU : y ∈ U) :
    (ScatFun.IntertwineSet (F.coRestrict U) g).Infinite := by
  classical
  obtain ⟨P₀, hP₀, hP₀y, hP₀equiv⟩ := hDreal g hg
  have hgP₀ : ScatFun.Reduces g (F.restrict P₀) := hP₀equiv.2
  -- The set of qualifying cocenters `{y_Q | Q ∈ 𝒫_D, y_Q ∈ U, g ≤ F↾Q}`.
  set S : Set Baire := {z | ∃ (Q : Set ↑F.domain) (hQ : Q ∈ Part),
      hA.cocenterOf hQ = z ∧ hA.cocenterOf hQ ≠ y ∧ hA.cocenterOf hQ ∈ U ∧
      ScatFun.Reduces g (F.restrict Q)} with hSdef
  -- (1) Each qualifying cocenter lies in the intertwine set.
  have hSsub : S ⊆ ScatFun.IntertwineSet (F.coRestrict U) g := by
    intro z hz
    obtain ⟨Q, hQ, hQz, hQy, hQU, hgQ⟩ := hz
    intro W hW
    -- Pick a clopen `V' ⊆ W ∩ U` around `z`.
    have hUnhds : U ∈ 𝓝 z := hUcl.isOpen.mem_nhds (hQz ▸ hQU)
    obtain ⟨O, hOsub, hOopen, hzO⟩ := mem_nhds_iff.mp (Filter.inter_mem hW hUnhds)
    obtain ⟨V', hV'cl, hzV', hV'O⟩ := baire_exists_clopen_subset_of_open z O hOopen hzO
    have hV'U : V' ⊆ U := fun a ha => (hOsub (hV'O ha)).2
    have hV'W : V' ⊆ W := fun a ha => (hOsub (hV'O ha)).1
    -- `F↾Q` is centered with cocenter `z ∈ V'`.
    have hcent : IsCentered (F.restrict Q).func := hA.centered Q hQ
    have hcocV' : cocenter (F.restrict Q).func hcent ∈ V' := by
      rw [show cocenter (F.restrict Q).func hcent = z from hQz]; exact hzV'
    have h1 : ScatFun.Reduces (F.restrict Q) ((F.restrict Q).coRestrict V') :=
      reduces_coRestrict_cocenter_nbhd (F.restrict Q) hcent hV'cl.isOpen hcocV'
    have h2 : ScatFun.Reduces ((F.restrict Q).coRestrict V') (F.coRestrict V') :=
      ScatFun.coRestrict_restrict_reduces F Q V'
    have h3 : ScatFun.Reduces (F.coRestrict V') ((F.coRestrict U).coRestrict W) :=
      coRestrict_inter_reduces F hV'U hV'W
    exact hgQ.trans (h1.trans (h2.trans h3))
  -- (2) The set of qualifying cocenters is infinite (strong solvability, as for `Y'`).
  have hSinf : S.Infinite := by
    intro hfin
    have hyS : y ∉ S := fun ⟨_, _, hQz, hQy, _, _⟩ => hQy hQz
    obtain ⟨V, hVcl, hyV, hVdisj⟩ := exists_clopen_nbhd_disjoint_finite hfin hyS
    obtain ⟨Q, hQ, hQyne, hQVU, hP₀Q⟩ :=
      (hss.2.2 (V ∩ U) (hVcl.inter hUcl) ⟨hyV, hyU⟩).2 P₀ hP₀ hP₀y
    have hQmemS : hA.cocenterOf hQ ∈ S := ⟨Q, hQ, rfl, hQyne, hQVU.2, hgP₀.trans hP₀Q⟩
    exact (Set.disjoint_left.mp hVdisj hQVU.1) hQmemS
  exact Set.Infinite.mono hSsub hSinf

/-- **First case, right reduction** `ω D ≤ F⇂U` (`6_double_successor_memo.tex:295`). Fix clopen
`U ∋ y`. Enumerating `D.toList` as a `Fin`-family `G` and feeding the raw intertwining lemma
`intertwine_reductions` the per-`g` infiniteness of `IntertwineSet (F⇂U) g`
(`diagonalTheorem_firstCase_intertwineSet_infinite`) gives `ω(gl G) ≤ F⇂U`; and `gl G = gl D`
(`glFin G = glList D.toList`, the padded family being pointwise the `getD` family). **Proved**
modulo the isolated infiniteness sub-lemma. -/
theorem diagonalTheorem_firstCase_right
    (α : Ordinal.{0})
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hss : hA.IsStronglySolvableAt α.limitPart y)
    {D : Finset ScatFun}
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g) :
    ∀ U : Set Baire, IsClopen U → y ∈ U →
      ScatFun.Reduces (ScatFun.omega (ScatFun.glList D.toList)) (F.coRestrict U) := by
  intro U hUcl hyU
  -- Enumerate `D.toList` as a `Fin`-family and feed the raw intertwining lemma.
  set L : List ScatFun := D.toList with hLdef
  set G : Fin L.length → ScatFun := fun k => L.getD (k : ℕ) ScatFun.empty with hGdef
  have hGmem : ∀ k : Fin L.length, G k ∈ D := by
    intro k
    have hmem : G k ∈ L := by
      rw [hGdef]; simp only [List.getD_eq_getElem L ScatFun.empty k.isLt]
      exact List.getElem_mem k.isLt
    rwa [hLdef, Finset.mem_toList] at hmem
  have hGinf : ∀ k : Fin L.length,
      (ScatFun.IntertwineSet (F.coRestrict U) (G k)).Infinite := fun k =>
    diagonalTheorem_firstCase_intertwineSet_infinite α F hA hss hDreal (hGmem k) hUcl hyU
  have hmain : ScatFun.Reduces (ScatFun.omega (ScatFun.glFin G)) (F.coRestrict U) :=
    ScatFun.intertwine_reductions (F.coRestrict U) G hGinf
  -- `glFin G = glList L`: the two `gl`-families agree pointwise (`dite` vs out-of-range `getD`).
  have hbridge : ScatFun.glFin G = ScatFun.glList L := by
    show ScatFun.gl (fun k => if h : k < L.length then G ⟨k, h⟩ else ScatFun.empty)
      = ScatFun.gl (fun k => L.getD k ScatFun.empty)
    congr 1
    funext k
    by_cases hk : k < L.length
    · rw [dif_pos hk, hGdef]
    · rw [dif_neg hk]
      exact (List.getD_eq_default L ScatFun.empty (not_lt.mp hk)).symm
  rw [hbridge] at hmain
  exact hmain

theorem diagonalTheorem_firstCase
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → y ∈ U → ScatFun.Reduces g (F.coRestrict U) := by
  -- Assemble from the representative-selection lemma and the three conjunct-lemmas; `g = ω D`.
  obtain ⟨D, hDsub, hDrank, hDrep, hDreal⟩ :=
    diagonalTheorem_firstCase_representatives α hα hFG F hFrank hA hcase hss.1.2
  exact ⟨ScatFun.omega (ScatFun.glList D.toList),
    diagonalTheorem_firstCase_omegaD_mem α hα hDsub (hDrank.imp fun _ h => h.1),
    diagonalTheorem_firstCase_left α hα F hFrank hA hcase hDsub hDrank hDrep,
    diagonalTheorem_firstCase_right α F hA hss hDreal⟩


end
