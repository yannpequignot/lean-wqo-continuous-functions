import WqoContinuousFunctions.DoubleSuccessor.Solvable

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Finite generation at double successors — the chapter capstone

The memoir's Theorem `FGatdoublesuccessors` (`6_double_successor_memo.tex:549-551`): `FG(<α+2)`
implies `FG(α+2)`. This is the last missing case of `ScatFun.levels_finitely_generated`
(`LevelsFinitelyGenerated/Induction.lean`), which consumes it for `α = γ+1+1`, `γ ≠ 0`
(the cases `α ∈ {0, 1, 2}` and `α` limit / successor-of-limit are proved in
`Two.lean` / `LambdaPlusOne.lean` / `LevelsFinitelyGenerated.lean`).

Placed here — not in `DoubleSuccessor/` — to sit next to its per-case siblings
(`Generators_two_finitely_generates`, `Generators_lambdaPlusOne_finitely_generates`, …), and
because it is the only result of the chapter whose statement mentions no partition vocabulary.

## The remaining dependency checklist (deepest first)

1. `refiningBy1_exists_regularizing_nbhd`, `refiningBy1` tail — `Fine.lean` (§6.1, lump
   dissolution), plus `exists_countable_clopen_centered_cover` (`FGBelow.lean`, the laminar
   cylinder selection).
2. `existenceFinePartitions_dissolveAll` / `_gobble` / `existenceFinePartitions` /
   `existenceFinePartitions_zero` / `existenceFinePartitions_all` — `Fine.lean` (§6.1).
3. `exists_pglFinset_decomp_of_centered_doubleSucc` (the isolated `FGconsequences` item-5
   structure lemma, on which the now-proved `verticalTheorem_setup` rests) + the Vertical
   Theorem hard case — `PseudoCentered.lean` (§6.2).
4. `diagonalTheorem` — `Partitions/Diagonal.lean` (§6.3).
5. `solvableDecomposition`, `solvable_lambdaPlusOne`, `finiteGenerationForSolvable` —
   `Partitions/Solvable.lean` (§6.4).
6. This file's assembly — mechanical once 1–5 are in place.
-/

namespace ScatFun

/-! ## Countable sandwich collapse -/

/-- **Countable fibre-family assembly (countable "sandwich lemma").**  The countable analogue of
`finGl_sandwich`.  If `(D i)` is an `F`-domain partition, `(U i)` are pairwise-disjoint clopen
codomain sets, each `g i` is sandwiched `F.restrict (D i) ≤ g i ≤ F.coRestrict (U i)` and lies in
`FinGl S.toFinFun`, **and** `FinGl S.toFinFun` is closed under countable plain gluing
(`hcollapse` — supplied at the call site by `generators_gl_mem_finGl`), then `F ∈ FinGl S`. -/
lemma finGl_sandwich_countable {S : Finset ScatFun}
    (hcollapse : ∀ f : ℕ → ScatFun, (∀ i, f i ∈ FinGl S.toFinFun) →
        ∃ g ∈ FinGl S.toFinFun, Equiv (gl f) g)
    (F : ScatFun) (D : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion D)
    (U : ℕ → Set Baire) (hUcl : ∀ i, IsClopen (U i))
    (hUdisj : Pairwise (Function.onFun Disjoint U))
    (g : ℕ → ScatFun)
    (hup : ∀ i, Reduces (F.restrict (D i)) (g i))
    (hlow : ∀ i, Reduces (g i) (F.coRestrict (U i)))
    (hgen : ∀ i, g i ∈ FinGl S.toFinFun) :
    F ∈ FinGl S.toFinFun := by
  have hfwd : Reduces F (gl g) :=
    (scatFun_reduces_gl_of_domain_partition F D hdu).trans
      (gl_reduces_of_pointwise _ _ hup)
  have hbwd : Reduces (gl g) F :=
    (gl_reduces_of_pointwise _ _ hlow).trans
      (gl_coRestrict_disjoint_open_reduces F U (fun k => (hUcl k).isOpen) hUdisj)
  obtain ⟨h, hmem, heq⟩ := hcollapse g hgen
  exact finGl_closed_equiv _ hmem ⟨heq.2.trans hbwd, hfwd.trans heq.1⟩

/-
**Enumerate a countable pairwise-disjoint family as a padded `ℕ`-sequence.** A countable
family `𝒰` of pairwise-disjoint sets can be listed as `U : ℕ → Set X` (padding unused indices with
`∅`) so that distinct indices give disjoint sets and `⋃₀ 𝒰 ⊆ ⋃ n, U n`. General-purpose helper
for feeding a countable solvable decomposition into `finGl_sandwich_countable` (the capstone below
inlines an equivalent enumeration; this standalone form is kept for reuse).
-/
lemma exists_seq_enum_of_countable_pairwiseDisjoint {X : Type*} (𝒰 : Set (Set X))
    (hc : 𝒰.Countable) (hd : 𝒰.PairwiseDisjoint id) :
    ∃ U : ℕ → Set X, (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (∀ n, U n ∈ 𝒰 ∨ U n = ∅) ∧ ⋃₀ 𝒰 ⊆ ⋃ n, U n := by
  obtain ⟨finj, hfinj⟩ : ∃ finj : Set X → ℕ, Set.InjOn finj 𝒰 :=
    Set.countable_iff_exists_injOn.mp hc
  refine ⟨ fun n => if h : ∃ s ∈ 𝒰, finj s = n then h.choose else ∅, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ Set.disjoint_left ];
  · intro i j hij x hx hy;
    split_ifs at hx hy <;> simp_all +decide [ Set.InjOn ];
    have := hd ( Classical.choose_spec ‹∃ s ∈ 𝒰, finj s = i› |>.1 ) ( Classical.choose_spec ‹∃ s ∈ 𝒰, finj s = j› |>.1 );
    grind;
  · grind +qlia;
  · intro t' ht' x hx; rw [Set.mem_iUnion];
    use finj t';
    split_ifs with h;
    · have := h.choose_spec.2; have := hfinj h.choose_spec.1 ht' this; aesop;
    · exact False.elim ( h ⟨ t', ht', rfl ⟩ )

/-! ## The domain partition induced by a clopen codomain cover -/

/-
The blocks `A^{U i}_𝒫 = domainOver (U i)` of a `c`-partition, indexed by a countable
family `(U i)` of pairwise-disjoint clopen codomain sets that covers the cocenter set, form a
disjoint (clopen) partition of `F.domain`.
-/
lemma isDisjointUnion_domainOver {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (U : ℕ → Set Baire)
    (hUdisj : Pairwise (Function.onFun Disjoint U))
    (hcover : hA.cocenterSet ⊆ ⋃ i, U i) :
    F.IsDisjointUnion (fun i => hA.domainOver (U i)) := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  · intro i
    have h_open : IsOpen (hA.domainOver (U i)) := by
      have h_open : ∀ P ∈ hA.piecesOver (U i), IsOpen P := by
        exact fun P hP => hA.isClopen P ( hP.choose ) |> IsClopen.isOpen;
      exact isOpen_sUnion h_open
    have h_closed : IsClosed (hA.domainOver (U i)) := by
      have h_closed : (hA.domainOver (U i))ᶜ = ⋃₀ {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ∉ U i} := by
        ext x; simp [ScatFun.IsCPartition.domainOver, ScatFun.IsCPartition.piecesOver];
        constructor;
        · obtain ⟨P, hP⟩ : ∃ P ∈ Part, x ∈ P := by
            exact Set.mem_sUnion.mp ( hA.sUnion_eq.symm ▸ Set.mem_univ x );
          exact fun h => ⟨ P, ⟨ hP.1, fun h' => h P hP.1 h' hP.2 ⟩, hP.2 ⟩;
        · rintro ⟨ t, ⟨ ht, ht' ⟩, hx ⟩ s hs hs' hx';
          have := hA.pairwiseDisjoint ht hs; simp_all +decide [ Set.disjoint_left ] ;
          exact this ( by rintro rfl; exact ht' hs' ) _ x.2 hx hx';
      convert h_closed.symm ▸ isOpen_sUnion ( fun P hP => ?_ ) |> IsOpen.isClosed_compl using 1;
      · rw [ compl_compl ];
      · exact hA.isClopen P hP.choose |> IsClopen.isOpen
    exact ⟨h_closed, h_open⟩;
  · intro i j hij; simp_all +decide [ Set.disjoint_left, ScatFun.IsCPartition.domainOver, ScatFun.IsCPartition.piecesOver ] ;
    intro a ha x hx hx' hx'' y hy hy' hy''; have := hUdisj hij; simp_all +decide [ Set.disjoint_left ] ;
    have h_unique : x = y := by
      exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( hA.pairwiseDisjoint hx hy h ) hx'' hy'';
    generalize_proofs at *; (
    grind +ring);
  · ext x; simp [ScatFun.IsCPartition.domainOver];
    obtain ⟨ P, hP₁, hP₂ ⟩ := hA.sUnion_eq.symm.subset ( Set.mem_univ x );
    exact Exists.elim ( Set.mem_iUnion.mp ( hcover ( Set.mem_range.mpr ⟨ ⟨ P, hP₁ ⟩, rfl ⟩ ) ) ) fun i hi => ⟨ i, P, ⟨ hP₁, hi ⟩, hP₂ ⟩

/-! ## Per-block finite generation -/

/-
**Per-block dispatch.**  A block `F'` (a restriction of the rank-`α+2` function `F`, so of
rank `≤ α+2`) that is solvable at `y` relative to `α.limitPart` lies, up to the codomain
sandwich, in `FinGl 𝒢_{α+2}`.  The block rank is some `β ∈ (λ, α+2]` (`λ = α.limitPart`), so
`β = λ+1` (dispatch to `solvable_lambdaPlusOne`) or `β = δ+2` (`finiteGenerationForSolvable`
at `δ`); the resulting `g ∈ FinGl 𝒢_β` is lifted to `FinGl 𝒢_{α+2}` by cross-level generator
monotonicity (`Generators_mono_of_le` / `FinGl_mono_of_subset`).
-/
lemma block_finGl (α : Ordinal.{0}) (hα_lt : α + 1 + 1 < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F' : ScatFun) (hrank_le : CBRank F'.func ≤ α + 1 + 1)
    {Part' : Set (Set ↑F'.domain)} (hA' : F'.IsCPartition Part') {y : Baire}
    (hsolv : hA'.IsSolvableAt α.limitPart y) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      Reduces F' g ∧
        ∀ U : Set Baire, IsClopen U → hA'.cocenterSet ⊆ U → Reduces g (F'.coRestrict U) := by
  have hlam_lt : α.limitPart < CBRank F'.func := by
    obtain ⟨g, hg⟩ : ∃ g : {P // P ∈ Part'}, hA'.cocenterOf g.2 = y := by
      exact Set.mem_range.mp hsolv.2.1;
    obtain ⟨hA'_fine, hy, hsol⟩ := hsolv;
    obtain ⟨hA'_fine, hA'_sol⟩ := hA'_fine;
    exact lt_of_lt_of_le ( hA'_sol _ g.2 ) ( ContinuouslyReduces.rank_monotone ( F'.restrict g.1 ).hScat F'.hScat ( restrict_le_self F' g.1 ) );
  -- Set `N := α.natPart + 2` (a `ℕ`). Then `α + 1 + 1 = lam + (N : Ordinal)`.
  set N := α.natPart + 2
  have hN : α + 1 + 1 = α.limitPart + N := by
    rw [ Ordinal.eq_limitPart_add_natPart α ] ; norm_num [ add_assoc ];
    rw [ Ordinal.limitPart_add_natCast ];
    · norm_cast;
    · exact Ordinal.limitPart_isLimit_or_zero α
  obtain ⟨k, hk⟩ : ∃ k : ℕ, CBRank F'.func = α.limitPart + k ∧ 1 ≤ k ∧ k ≤ N := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, CBRank F'.func = α.limitPart + k := by
      have := exists_add_of_le hlam_lt.le;
      obtain ⟨ c, hc ⟩ := this;
      have hc_nat : c < Ordinal.omega0 := by
        have hc_nat : c ≤ N := by
          rw [hc] at hrank_le;
          rw [hN] at hrank_le;
          exact (add_le_add_iff_left α.limitPart).mp hrank_le
        exact lt_of_le_of_lt hc_nat ( Ordinal.nat_lt_omega0 _ );
      rw [ Ordinal.lt_omega0 ] at hc_nat ; aesop;
    refine ⟨ k, hk, Nat.pos_of_ne_zero ?_, ?_ ⟩ <;> simp_all +decide;
    linarith;
  by_cases hk1 : k = 1;
  · obtain ⟨g, hg, hred, hbound⟩ := solvable_lambdaPlusOne α.limitPart (Ordinal.limitPart_isLimit_or_zero α) (by
    grind +qlia) (hFG.mono (by
    rw [ hN ] ; norm_num [ hk1 ];
    exact Nat.succ_pos _)) F' (by
    aesop) hA' hsolv;
    refine ⟨ g, ?_, hred, hbound ⟩;
    convert FinGl_mono_of_subset _ hg using 1;
    convert Generators_mono_of_le ( Ordinal.limitPart_isLimit_or_zero α ) ( show 1 ≤ N from by linarith ) using 1;
    · norm_num;
    · rw [hN];
  · -- Set `δ := lam + ((k-2 : ℕ) : Ordinal)`. Then `δ.limitPart = lam` by `Ordinal.limitPart_add_natCast lam (k-2) hlim`.
    set δ := α.limitPart + (k - 2 : ℕ) with hδ_def
    have hδ_limitPart : δ.limitPart = α.limitPart := by
      apply Ordinal.limitPart_add_natCast;
      exact Ordinal.limitPart_isLimit_or_zero α
    have hδ_lt : δ < omega1 := by
      grind [omega1_add_nat]
    have hδ_rank : CBRank F'.func = δ + 1 + 1 := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ add_assoc ];
      norm_cast
    have hδ_solvable : hA'.IsSolvableAt δ.limitPart y := by
      exact hδ_limitPart.symm ▸ hsolv;
    have := finiteGenerationForSolvable δ hδ_lt (hFG.mono (by
    grind +qlia)) F' hδ_rank hA' hδ_solvable;
    refine this.imp fun g hg => ⟨ ?_, hg.2.1, hg.2.2 ⟩;
    refine FinGl_mono_of_subset ?_ hg.1;
    convert Generators_mono_of_le ( show Order.IsSuccLimit δ.limitPart ∨ δ.limitPart = 0 from ?_ ) ( show k ≤ N from hk.2.2 ) using 1;
    · grind;
    · rw [ hδ_limitPart, hN ];
    · exact hδ_limitPart.symm ▸ Ordinal.limitPart_isLimit_or_zero α

/-! ## The capstone -/

/-
**Finite generation at double successors** (memoir `FGatdoublesuccessors`,
`6_double_successor_memo.tex:549-551`): if `FG(<α+2)` holds then every `F : ScatFun` of
`CB`-rank `α+2` lies in `FinGl 𝒢_{α+2}`.

Stated for *all* `α < ω₁` as in the memoir (for `α = 0` it duplicates the independently
proved `Generators_two_finitely_generates`, keeping that rank-`2` case complete);
`Induction.lean` invokes it only for `α = γ+1 ≠ 1`.

## Provided solution (`6_double_successor_memo.tex:553-564`)

Write `λ = α.limitPart` (possibly `0`). Given `F` of rank `α+2`:

1. `existenceFinePartitions_all` gives a fine `c`-partition `𝒫` of `F`.
2. `solvableDecomposition` splits the codomain into countably many disjoint clopen `U ∈ 𝒰`
   covering `Y_𝒫`, with each block `F_U = F↾A^U_𝒫` solvable.  The blocks' domains partition
   `F.domain` (`isDisjointUnion_domainOver`).
3. Per block, `block_finGl` gives `g_U ∈ FinGl 𝒢_{α+2}` with `F_U ≤ g_U ≤ F_U⇂U ≤ F⇂U`.
4. `finGl_sandwich_countable` (fed `generators_gl_mem_finGl`) collapses the countable gluing
   back into `FinGl 𝒢_{α+2}`.
-/
theorem Generators_doubleSuccessor_finitely_generates (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1) :
    F ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
  have hα1 : α + 1 < omega1 := by
    exact add_one_lt_omega1 α hα
  have hα2 : α + 1 + 1 < omega1 := by
    convert omega1_add_nat ( α + 1 ) hα1 1 using 1;
    norm_num
  have hlam_lt : α.limitPart < omega1 := by
    refine lt_of_le_of_lt ?_ hα1;
    rw [ Ordinal.eq_limitPart_add_natPart α ];
    rw [ Ordinal.limitPart_add_natCast ];
    · exact le_add_of_le_of_nonneg ( le_add_of_nonneg_right <| by positivity ) zero_le_one;
    · exact Ordinal.limitPart_isLimit_or_zero α
  have hlim : Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 := by
    exact Ordinal.limitPart_isLimit_or_zero α
  -- Let `lam := α.limitPart` and `hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α`, and `hlam_lt :lam < omega1` (from `lam ≤ α < omega1`, using `Ordinal.eq_limitPart_add_natPart` and `le_self_add`).
  obtain ⟨Part, hA, hfine⟩ := existenceFinePartitions_all α hα2 hFG F hFrank
  obtain ⟨𝒰, hcount, hUcl𝒰, hUdisj𝒰, hcov𝒰, hblocks⟩ := solvableDecomposition α hα hFG F hFrank hA hfine;
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Set Baire, (∀ i, U i ∈ 𝒰 ∨ U i = ∅) ∧ (∀ i, IsClopen (U i)) ∧ Pairwise (Function.onFun Disjoint U) ∧ hA.cocenterSet ⊆ ⋃ i, U i := by
    obtain ⟨e, he⟩ : ∃ e : ↥𝒰 → ℕ, Function.Injective e := by
      exact Set.countable_iff_exists_injective.mp hcount
    refine ⟨ fun i => if hi : ∃ s : ↥𝒰, e s = i then ( Classical.choose hi : ↥𝒰 ).1 else ∅, ?_, ?_, ?_, ?_ ⟩;
    · intro i; by_cases hi : ∃ s : ↥𝒰, e s = i <;> simp +decide [ hi ] ;
    · intro i; by_cases hi : ∃ s : ↥𝒰, e s = i <;> simp +decide [ hi, hUcl𝒰 ] ;
      exact isClopen_empty
    · intro i j hij; by_cases hi : ∃ s : ↥𝒰, e s = i <;> by_cases hj : ∃ s : ↥𝒰, e s = j <;> simp_all +decide ;
      · obtain ⟨ a, ha, rfl ⟩ := hi; obtain ⟨ b, hb, rfl ⟩ := hj; simp +decide [ he.eq_iff ] at hij ⊢;
        simp +decide only [onFun, he.eq_iff, Subtype.mk.injEq, exists_prop, exists_eq_right, choose_eq, dite_eq_ite];
        rw [ if_pos ha, if_pos hb ] ; exact hUdisj𝒰 ha hb hij;
      · simp +decide [ hi, hj, Function.onFun ];
      · simp +decide [ hi, hj, Function.onFun ];
      · simp +decide [ hi, hj, Function.onFun ];
    · intro x hx;
      obtain ⟨ U, hU, hxU ⟩ := hcov𝒰 hx;
      simp +zetaDelta only [Ordinal.add_one_eq_succ, exists_and_left, Subtype.exists, mem_iUnion] at *;
      use e ⟨ U, hU ⟩;
      split_ifs <;> simp_all +decide [ he.eq_iff ];
  obtain ⟨g, hg_mem, hg_up, hg_low⟩ : ∃ g : ℕ → ScatFun, (∀ i, g i ∈ FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun) ∧ (∀ i, ScatFun.Reduces (F.restrict (hA.domainOver (U i))) (g i)) ∧ (∀ i, ScatFun.Reduces (g i) (F.coRestrict (U i))) := by
    have hgi : ∀ i, ∃ gi ∈ FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun, ScatFun.Reduces (F.restrict (hA.domainOver (U i))) gi ∧ ScatFun.Reduces gi (F.coRestrict (U i)) := by
      intro i
      by_cases hU_i : U i ∈ 𝒰;
      · obtain ⟨Part', hA', y, hcocU, hsolv⟩ := hblocks (U i) hU_i;
        obtain ⟨gi, hgi_mem, hgi_up, hgi_low⟩ := block_finGl α hα2 hFG (F.restrict (hA.domainOver (U i))) (by
        exact hFrank ▸ ContinuouslyReduces.rank_monotone ( F.restrict ( hA.domainOver ( U i ) ) ).hScat F.hScat ( restrict_le_self F ( hA.domainOver ( U i ) ) )) hA' hsolv;
        exact ⟨ gi, hgi_mem, hgi_up, hgi_low ( U i ) ( hU.2.1 i ) hcocU |> fun h => h.trans ( coRestrict_restrict_reduces F ( hA.domainOver ( U i ) ) ( U i ) ) ⟩;
      · use ScatFun.empty;
        have h_empty_mem : ScatFun.empty ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
          apply empty_mem_FinGl;
          exact ⟨ fun x => x.2 ⟩;
        have h_empty_reduces : ScatFun.Reduces (F.restrict (hA.domainOver (U i))) ScatFun.empty := by
          have h_empty_reduces : IsEmpty (F.restrict (hA.domainOver (U i))).domain := by
            simp +decide only [IsCPartition.domainOver, IsCPartition.piecesOver, hU.1 i |> Or.resolve_left <| hU_i, mem_empty_iff_false, exists_false, setOf_false, sUnion_empty, isEmpty_coe_sort];
            simp +decide [ ScatFun.restrict ];
          exact reduces_of_isEmpty_domain h_empty_reduces
        exact ⟨ h_empty_mem, h_empty_reduces, ScatFun.empty_reduces _ ⟩;
    exact ⟨ fun i => Classical.choose ( hgi i ), fun i => Classical.choose_spec ( hgi i ) |>.1, fun i => Classical.choose_spec ( hgi i ) |>.2.1, fun i => Classical.choose_spec ( hgi i ) |>.2.2 ⟩;
  convert finGl_sandwich_countable _ F ( fun i => hA.domainOver ( U i ) ) _ U hU.2.1 hU.2.2.1 g hg_up hg_low hg_mem;
  · convert generators_gl_mem_finGl hlam_lt hlim ( α.natPart + 1 ) _ using 1;
    · rw [ show α + 1 + 1 = α.limitPart + ( α.natPart + 1 ) + 1 from ?_ ];
      · norm_cast;
      · rw [ ← add_assoc, ← Ordinal.eq_limitPart_add_natPart α ];
    · convert hFG using 1;
      rw [ Ordinal.eq_limitPart_add_natPart α ] ; norm_num [ add_assoc ];
      grind [Ordinal.eq_limitPart_add_natPart];
  · exact isDisjointUnion_domainOver hA U hU.2.2.1 hU.2.2.2

end ScatFun

end