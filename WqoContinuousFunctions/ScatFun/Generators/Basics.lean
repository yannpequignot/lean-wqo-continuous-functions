import WqoContinuousFunctions.ScatFun.Generators.Defs
import WqoContinuousFunctions.ScatFun.Generators.BasicsHelpers
import WqoContinuousFunctions.CenteredFunctions.Finiteness
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.FGBelow

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Basic combinatorial facts on generators (memoir Prop. `BasicsOnGenerators`, items 4–6)

`5_precise_struct_memo.tex:474-521` states six basic facts about `𝒞_α`/`𝒢_α`. Items 1–3
(monotonicity, level bounds, finiteness) are already available: item 1 is
`CentBlock_subset_succ`/`GenBlock_subset_succ` (`ScatFun/Generators/Defs.lean`), item 3 is free
(`Finset.finite_toSet`), and item 2 is not needed downstream yet. This file proves the
remaining three items (`wedgeGenerator_bounding`, `generator_omega_equiv`,
`generators_gl_mem_finGl`), each with a "provided solution" docstring recording the proof
strategy and where it departs from the informal memoir proof. All declarations here are now
fully proved (the former open leaf, the per-generator structural transport feeding
`wedge_columns_centered_reps`, is discharged via `generator_centered_pieces` and
`pglFinset_equiv_of_finGl`).

## A genuine subtlety surfaced while stating these

The memoir's proof of item 4 sets `F := {pgl F_i : i ≤ k}` for a wedge generator
`g = ⋁(F_0,…,F_k ∣ F_{k+1})` (`F_i ∈ 𝒫⁺(𝒢_{α-1})`) and asserts `F ⊆ 𝒞_α` *literally*, citing
only `Gluingasupperbound_cor`. But `Centered α` (`centStep`) is built as a `pgl` of subsets of
`Centered (α-1) ∪ ω{Centered (α-1)}` **only** — not of all of `Generators (α-1)`, which is
strictly larger whenever `α-1` itself has wedge generators. So `pgl F_i` need not be a literal
member of `Centered α` by unfolding `centStep`; establishing `F ⊆ Centered α` genuinely needs
the memoir's Theorem 4.9 (`finitenessOfCenteredfunctions`, already in
`CenteredFunctions/Finiteness.lean`) plus the hypothesis that `Generators (α-1)` finitely
generates the level interval below it (an `FG(<α)`-style hypothesis, not otherwise assumed
here). This is exactly the content the memoir defers to and re-derives in the harder
`FGconsequences` item 5 (`5_precise_struct_memo.tex:530-547`). So items 4 and 5 below carry an
explicit `hgen` hypothesis playing that role, rather than silently assuming it.

A second, smaller subtlety: item 5 as literally stated ("for all `g ∈ Generators α`…") would
be **false** at the pure base/limit case `g = ℓ_λ` (`n = 0`): there `Centered λ = ∅`, so the
only possible witness is `H = ∅`, giving `ω H ≡ empty`, but `ω ℓ_λ` is certainly not equivalent
to the empty function. The memoir's own proof of item 5 only ever discusses the three
`genStep` clauses (centered / `ω`-image / wedge generator) and never touches `ℓ_λ`, so this
looks like an implicit restriction rather than a real counterexample to the intended claim.
Item 5 below is accordingly stated for `g ∈ genStep Cn Gprev` (the elements *genuinely produced
at a `genStep`*), which excludes `ℓ_λ` and matches what the memoir's proof actually handles.
-/

namespace ScatFun

/-! ## Theorem 4.9 specialised to the generator family (`finitenessOfCenteredFunctions`)

The wedge-generator bound (item 4) below, and every later consumer, applies Theorem 4.9
(`finitenessOfCenteredFunctions`, `CenteredFunctions/Finiteness.lean`) with the *specific*
generating family `B := (Generators (λ+n)).toFinFun`.  We fix that choice once here so callers
need not re-thread `m := (Generators (λ+n)).card` and the family every time.

The finite-generation hypothesis is taken as **`FG(<λ+n+1)`** (`ScatFun.FGBelow (λ+n+1)`): every
`ScatFun` of `CB`-rank strictly below `λ+n+1` is a finite gluing of the generators of its own
level.  This is the uniform standing assumption for the results in this file, matching the
induction hypothesis available at the call sites.  The interval form
`LevelInter λ (λ+n) ⊆ FinGl (Generators (λ+n)).toFinFun` that `finitenessOfCenteredFunctions`
actually consumes is derived from it internally by `LevelInter_finitelyGenerated`
(`ScatFun/LevelsFinitelyGenerated/LevelLTTwoBQO.lean`): `FG(<λ+n+1)` covers the whole closed
interval `[λ, λ+n]` (finite generation *at* level `λ+n` is included, since `λ+n < λ+n+1`), which
is exactly what decomposing a centered function of rank `λ+n+1` requires (its monotone blocks
`sᵢ` can reach rank exactly `λ+n`). -/
theorem finitenessOfCenteredFunctions_generators
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (g : ScatFun) (hg_lvl : g ∈ LevelInter lam (lam + ↑n + 1)) (hg_cent : IsCentered g.func) :
    Equiv g (minFun lam hlam) ∨
      ∃ (k : ℕ) (ι : Fin k → Fin (Generators (lam + ↑n)).card), 0 < k ∧
        Equiv g (pgl (repSeq ((Generators (lam + ↑n)).toFinFun ∘ ι))) := by
  have hgen : LevelInter lam (lam + ↑n) ⊆ FinGl (Generators (lam + ↑n)).toFinFun := by
    apply LevelInter_finitelyGenerated hlim n
    intro k hkn F hF
    refine hFG (lam + ↑k) ?_ F hF
    have h1 : lam + (↑k : Ordinal) ≤ lam + ↑n :=
      (add_le_add_iff_left lam).mpr (by exact_mod_cast hkn)
    have h2 : lam + (↑n : Ordinal) < lam + ↑n + 1 := by
      rw [Ordinal.add_one_eq_succ]; exact Order.lt_succ _
    exact lt_of_le_of_lt h1 h2
  exact finitenessOfCenteredFunctions hlam hlim (Generators (lam + ↑n)).toFinFun hgen g hg_lvl
    hg_cent

/-
**Successor-block unfolding of `Generators`.**  At a limit-or-zero base `lam`, the generator
level `lam + n + 1` is the previous level together with one `genStep` built from the centered
level `Centered (lam + n + 1)` and the previous generator level.
-/
lemma Generators_add_succ_eq {lam : Ordinal.{0}} (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) :
    Generators (lam + ↑n + 1) =
      Generators (lam + ↑n) ∪ genStep (Centered (lam + ↑n + 1)) (Generators (lam + ↑n)) := by
  rw [ Generators, Generators, Centered ];
  rw [ show ( lam + n + 1 : Ordinal ) = lam + ( n + 1 ) by simp +decide [ add_assoc ] ];
  rw [ show ( lam + ( n + 1 ) : Ordinal ).limitPart = lam from ?_, show ( lam + ( n + 1 ) : Ordinal ).natPart = n + 1 from ?_ ];
  · rw [ show ( lam + n : Ordinal ).limitPart = lam from Ordinal.limitPart_add_natCast lam n hlim,
      show ( lam + n : Ordinal ).natPart = n from Ordinal.natPart_add_natCast lam n hlim ]
    simp only [GenBlock, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  · convert Ordinal.natPart_add_natCast lam ( n + 1 ) hlim using 1;
  · rw [ ← Nat.cast_succ, Ordinal.limitPart_add_natCast ] ; aesop

/-- **`ω ℓ_α ≡ ℓ_α`.**  The max function absorbs its own `ω`-gluing. -/
lemma omega_maxFun_equiv_self (α : Ordinal.{0}) (hα : α < omega1) :
    Equiv (omega (maxFun α hα)) (maxFun α hα) :=
  ⟨omega_maxFun_reduces_self α hα, reduces_block_gl (fun _ => maxFun α hα) 0⟩

/-! ## Item 4: bounding a wedge generator (`BasicsOnGenerators_boundingwedge`,
`5_precise_struct_memo.tex:480`) -/

/-! ### Supporting lemmas for `wedgeGenerator_centered_witness` -/

/-
Every element of `Centered (lam+k) ∪ ω{Centered (lam+k)}` has CB-rank `> lam` (for `lam` a
limit).  Centered functions have successor CB-rank `≥ lam+1 > lam`, and `ω` preserves CB-rank.
-/
lemma piece_lam_lt_rank {lam : Ordinal.{0}} (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (k : ℕ) (x : ScatFun)
    (hx : x ∈ Centered (lam + ↑k) ∪ omegaImage (Centered (lam + ↑k))) :
    lam < CBRank x.func := by
  rcases k with ( _ | k ) <;> simp_all +decide;
  · exfalso
    have hnp : lam.natPart = 0 := by
      have := Ordinal.natPart_add_natCast lam 0 (Or.inl hlim); simpa using this
    rw [Centered, if_pos hnp] at hx
    simp [omegaImage] at hx
  · -- By definition of $CentBlock$, we know that every element in $CentBlock (centBase1 lam) k$ has a rank greater than $lam$.
    have h_centBlock_rank : ∀ y ∈ CentBlock (centBase1 lam) k, lam < CBRank y.func := by
      refine Nat.recOn k ?_ ?_ <;> simp_all +decide [ CentBlock ];
      · unfold centBase1; simp +decide [ hlam ] ;
        split_ifs <;> simp_all +decide;
        constructor;
        · exact minFun_cbRank_eq lam hlam ▸ Order.lt_succ lam;
        · rw [ cbRank_pgl_regular ] <;> norm_num [ scatFun_const_isRegularSeq, maxFun_cbRank_eq ];
          rw [ maxFun_cbRank_eq ];
          exact hlam;
      · intro n hn y hy; simp_all +decide [ centStep ] ;
        rcases hy with ( hy | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ nonemptySubsets ];
        -- Since $a$ is nonempty, there exists some $b \in a$.
        obtain ⟨b, hb⟩ : ∃ b ∈ a, lam < CBRank b.func := by
          obtain ⟨ b, hb ⟩ := Finset.nonempty_of_ne_empty ha.1; use b; simp_all +decide [ Finset.subset_iff ] ;
          cases ha.2 hb <;> simp_all +decide [ omegaImage ];
          obtain ⟨ c, hc, rfl ⟩ := ‹_›; exact hn c hc |> lt_of_lt_of_le <| by
            apply_rules [ ContinuouslyReduces.rank_monotone ];
            · exact c.hScat;
            · exact c.omega.hScat;
            · exact ScatFun.reduces_block_gl ( fun _ => c ) 0;
        -- Since $b \in a$, we have $b \leq glList a.toList$.
        have h_b_le_glList : Reduces b (glList a.toList) := by
          have h_b_le_glList : ∀ {L : List ScatFun}, b ∈ L → Reduces b (glList L) :=
            fun {L} a => mem_reduces_glList a
          exact h_b_le_glList ( by simpa using hb.1 );
        -- Since $b \leq glList a.toList$, we have $CBRank b.func \leq CBRank (glList a.toList).func$.
        have h_b_rank_le_glList_rank : CBRank b.func ≤ CBRank (glList a.toList).func := by
          apply_rules [ ContinuouslyReduces.rank_monotone ];
          · exact b.hScat;
          · exact (glList a.toList).hScat;
        -- Since $pglFinset a = pgl (fun _ => glList a.toList)$, we have $CBRank (pglFinset a).func = Order.succ (CBRank (glList a.toList).func)$.
        have h_pglFinset_rank : CBRank (pglFinset a).func = Order.succ (CBRank (glList a.toList).func) := by
          convert cbRank_pgl_regular ( fun _ => glList a.toList ) _ using 1;
          · simp +decide [ ciSup_const ];
          · exact scatFun_const_isRegularSeq _;
        exact h_pglFinset_rank.symm ▸ lt_of_lt_of_le hb.2 ( le_trans h_b_rank_le_glList_rank ( Order.le_succ _ ) );
    rcases hx with ( hx | hx ) <;> simp_all +decide;
    · convert h_centBlock_rank x _;
      convert hx using 1;
      convert Centered_lam_add_succ ( Or.inl hlim ) k |> Eq.symm using 1;
      norm_num [ add_assoc ];
    · obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx;
      have h_omega_rank : CBRank y.omega.func ≥ CBRank y.func := by
        apply le_of_not_gt; intro h_contra;
        exact h_contra.not_ge ( by simpa using ContinuouslyReduces.rank_monotone y.hScat y.omega.hScat ( ScatFun.reduces_block_gl ( fun _ => y ) 0 ) );
      exact lt_of_lt_of_le ( h_centBlock_rank y ( by
        convert hy using 1;
        convert Centered_lam_add_succ ( Or.inl hlim ) k |> Eq.symm using 1;
        norm_num [ add_assoc ] ) ) h_omega_rank

/-
`ℓ_lam` reduces to any scattered function of CB-rank `> lam` (for `lam` a limit): chain
`ℓ_lam ≤ k_{lam+1} ≤ y` via `maxFun_reduces_minFun_of_limit` and `minFun_is_minimum`.
-/
lemma maxFun_reduces_of_lam_lt_rank {lam : Ordinal.{0}} (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (y : ScatFun) (h : lam < CBRank y.func) :
    Reduces (maxFun lam hlam) y := by
  have h_min : Reduces (minFun lam hlam) y := by
    have h_min : (CBLevel y.func lam).Nonempty := by
      apply CBLevel_nonempty_below_rank y.func y.hScat lam h;
    have := minFun_is_minimum lam hlam y.domain y.func y.hCont y.hScat h_min; aesop;
  have h_max : Reduces (maxFun lam hlam) (minFun lam hlam) := by
    convert maxFun_reduces_minFun_of_limit lam hlam ( Or.inl hlim ) using 1;
  exact h_max.trans h_min

/-
**Centered pieces of a `genStep` generator** (the three `genStep` clauses of memoir item 5).
Given the *bounding* conclusion at level `m`, any `g ∈ genStep (Centered (lam+m+1)) (Generators
(lam+m))` admits a nonempty list `l` of blocks in `Centered (lam+m+1) ∪ ω{Centered (lam+m+1)}` with
each `x ∈ l` reducing to `g` and `g` reducing to `glList l`.  Centered clause: `l = [g]`; `ω`-image
clause: `l = [g]`; wedge clause: `l = L ++ D.map ω` from `hbnd`.
-/
lemma genStep_centered_pieces
    {lam : Ordinal.{0}} (m : ℕ)
    (hbnd : ∀ (S : Finset (Finset ScatFun)),
        S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑m))) →
        ∀ (D : Finset ScatFun), D ⊆ Centered (lam + ↑m + 1) →
          ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑m + 1)) ∧
            (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
            Reduces (omega (glList D.toList)) (wedgeFinset (S.toList.map Finset.toList) D.toList) ∧
            Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
              (glBin (glList L) (omega (glList D.toList))))
    (g : ScatFun) (hg : g ∈ genStep (Centered (lam + ↑m + 1)) (Generators (lam + ↑m))) :
    ∃ l : List ScatFun, l ≠ [] ∧
      (∀ x ∈ l, x ∈ Centered (lam + ↑m + 1) ∪ omegaImage (Centered (lam + ↑m + 1))) ∧
      (∀ x ∈ l, Reduces x g) ∧ Reduces g (glList l) := by
  unfold genStep at hg; simp_all +decide [ Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powerset ] ;
  rcases hg with ( hg | hg | ⟨ S, hS, D, hD, rfl ⟩ );
  · refine ⟨ [ g ], ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ ScatFun.Reduces ];
    · exact ContinuouslyReduces.refl g.func;
    · exact ScatFun.glList_single_equiv g |>.1;
  · obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hg; use [ omega x ] ; simp +decide [ * ] ;
    exact ⟨ by exact Equiv.refl _ |>.1, by exact ( ScatFun.glList_single_equiv x.omega ).1 ⟩;
  · obtain ⟨ L, hL₁, hL₂, hL₃, hL₄ ⟩ := hbnd S hS D hD;
    refine ⟨ L ++ D.toList.map omega, ?_, ?_, ?_, ?_ ⟩;
    · intro hL_empty;
      have h_empty_domain : IsEmpty (wedgeFinset (List.map Finset.toList S.toList) D.toList).domain := by
        have h_empty_domain : IsEmpty (glList L ⊕ (glList D.toList).omega).domain := by
          simp_all +decide [ List.append_eq_nil_iff ];
          convert Set.eq_empty_of_forall_notMem _;
          intro x hx; obtain ⟨ y, hy ⟩ := hx; simp_all +decide [ glList ] ;
          obtain ⟨ ⟨ y, rfl ⟩, hy ⟩ := hy; simp_all +decide [ copiesSeq ] ;
          rcases y with ( _ | _ | y ) <;> simp_all +decide [ copiesList ];
          · simp_all +decide [ List.finRange ];
            simp_all +decide [ GluingSet ];
            exact hy.elim fun i hi => hi.elim fun x hx => by cases hx.1;
          · simp_all +decide [ List.finRange ];
            obtain ⟨ y, hy, rfl ⟩ := hy; simp_all +decide [ ScatFun.omega ] ;
            simp_all +decide [ ScatFun.empty, GluingSet ];
          · exact hy.elim fun x hx => hx.1;
        obtain ⟨ σ, τ, hσ, hτ, h ⟩ := hL₄;
        exact ⟨ fun x => h_empty_domain.elim ( σ x ) ⟩;
      have h_nonempty_domain : ∃ i : Fin (List.map Finset.toList S.toList).length, (pgl (fun _ : ℕ => glList ((List.map Finset.toList S.toList).get i))).domain.Nonempty := by
        exact ⟨ ⟨ 0, by
          simp +zetaDelta only [List.append_eq_nil_iff, List.map_eq_nil_iff, Finset.toList_eq_nil, isEmpty_coe_sort, List.length_map, Finset.length_toList, Finset.card_pos] at *;
          exact Finset.nonempty_of_ne_empty ( by rintro rfl; simp +decide [ nonemptySubsets ] at hS ) ⟩, by
          exact ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩ ⟩;
      obtain ⟨ i, hi ⟩ := h_nonempty_domain;
      have h_nonempty_domain : Reduces (pgl (fun _ : ℕ => glList ((List.map Finset.toList S.toList).get i))) (wedgeFinset (List.map Finset.toList S.toList) D.toList) := by
        convert column_reduces_wedge _ _ _ using 1;
        convert rfl;
      obtain ⟨ σ, hσ ⟩ := h_nonempty_domain;
      exact h_empty_domain.elim ( σ ⟨ hi.some, hi.choose_spec ⟩ );
    · simp +zetaDelta at *;
      rintro x ( hx | ⟨ a, ha, rfl ⟩ ) <;> [ exact Or.inl ( hL₁ x hx ) ; exact Or.inr ( Finset.mem_image.mpr ⟨ a, hD ha, rfl ⟩ ) ];
    · simp +zetaDelta at *;
      rintro x ( hx | ⟨ a, ha, rfl ⟩ ) <;> [ exact hL₂ _ hx; exact ScatFun.omega_reduces_of_reduces ( ScatFun.mem_reduces_glList ( Finset.mem_toList.mpr ha ) ) |> fun h => h.trans hL₃ ];
    · have h_equiv : Equiv (glList L ⊕ (glList D.toList).omega) (glList (L ++ D.toList.map omega)) := by
        have h_equiv : Equiv (glList L ⊕ (glList D.toList).omega) (glList L ⊕ glList (D.toList.map omega)) := by
          have h_equiv : Equiv ((glList D.toList).omega) (glList (D.toList.map omega)) :=
            omega_glList_equiv_glList_omega D.toList
          exact ScatFun.glBin_congr ( ScatFun.Equiv.refl _ ) h_equiv;
        exact h_equiv.trans ( glList_append_equiv _ _ |> Equiv.symm );
      exact hL₄.trans h_equiv.1

/-- **Per-generator centered pieces** (memoir item 5, structural transport of one generator).
Given the *bounding* conclusion at all levels `m < N`, any generator `g ∈ Generators (lam+k)`
(`k ≤ N`) that is not the base maximal function `ℓ_lam` admits a nonempty list `l` of blocks in
`Centered (lam+k) ∪ ω{Centered (lam+k)}` with each `x ∈ l` reducing to `g` and `g` reducing to the
finite gluing `glList l`.  Proved by strong induction on `k` via `Generators_add_succ_eq`: the
`genStep` clauses are the centered generator (`l = [g]`), the `ω`-image (`l = [g]`), and the wedge
generator (apply `hbound (k-1)` and set `l = L ++ D.map ω`, using `omega_glList_equiv_glList_omega`
and `glList_append_equiv`); generators inherited from `Generators (lam+(k-1))` recurse (pieces cast
up by `CentBlock` monotonicity). -/
lemma generator_centered_pieces
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (N : ℕ)
    (hbound : ∀ m, m < N → ∀ (S : Finset (Finset ScatFun)),
        S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑m))) →
        ∀ (D : Finset ScatFun), D ⊆ Centered (lam + ↑m + 1) →
          ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑m + 1)) ∧
            (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
            Reduces (omega (glList D.toList)) (wedgeFinset (S.toList.map Finset.toList) D.toList) ∧
            Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
              (glBin (glList L) (omega (glList D.toList)))) :
    ∀ k, k ≤ N → ∀ g ∈ Generators (lam + ↑k),
      (∀ (_hl : Order.IsSuccLimit lam), g ≠ maxFun lam hlam) →
      ∃ l : List ScatFun, l ≠ [] ∧
        (∀ x ∈ l, x ∈ Centered (lam + ↑k) ∪ omegaImage (Centered (lam + ↑k))) ∧
        (∀ x ∈ l, Reduces x g) ∧ Reduces g (glList l) := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  intro hk g hg hne
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [Nat.cast_zero, add_zero] at hg
    rcases hlim with hlim | hlz
    · rw [Generators_lam_limit hlam hlim, Finset.mem_singleton] at hg
      exact absurd hg (hne hlim)
    · rw [hlz, Generators_zero] at hg
      exact absurd hg (Finset.notMem_empty g)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hcast : (lam + ↑(j + 1) : Ordinal) = lam + ↑j + 1 := by push_cast; rw [add_assoc]
    rw [hcast] at hg ⊢
    rw [Generators_add_succ_eq hlim j, Finset.mem_union] at hg
    rcases hg with hg | hg
    · obtain ⟨l, hl0, hlmem, hlred, hgred⟩ :=
        ih j (Nat.lt_succ_self j) (by omega) g hg hne
      refine ⟨l, hl0, fun x hx => ?_, hlred, hgred⟩
      have hsub : Centered (lam + ↑j) ∪ omegaImage (Centered (lam + ↑j)) ⊆
          Centered (lam + ↑j + 1) ∪ omegaImage (Centered (lam + ↑j + 1)) :=
        Finset.union_subset_union (Centered_add_nat_subset_succ hlim j)
          (Finset.image_subset_image (Centered_add_nat_subset_succ hlim j))
      exact hsub (hlmem x hx)
    · exact genStep_centered_pieces j (fun S hS D hD => hbound j (by omega) S hS D hD) g hg

/-
A `pglFinset` of a nonempty subset of `Centered (lam+n) ∪ ω{Centered (lam+n)}` is a member of
`Centered (lam+n+1)` (it is one of the `centStep` generators).
-/
lemma pglFinset_mem_Centered_of_subset {lam : Ordinal.{0}}
    (hlim : Order.IsSuccLimit lam ∨ lam = 0) (n : ℕ)
    (F' : Finset ScatFun) (hF'ne : F'.Nonempty)
    (hF'sub : F' ⊆ Centered (lam + ↑n) ∪ omegaImage (Centered (lam + ↑n))) :
    pglFinset F' ∈ Centered (lam + ↑n + 1) := by
  -- By definition of `Centered`, we know that `pglFinset F' ∈ Centered (lam + n + 1)` if and only if `pglFinset F' ∈ centStep (Centered (lam + n))`.
  rw [Centered_lam_add_succ hlim n];
  rcases n with ( _ | n ) <;> simp_all +decide [ CentBlock, centStep ];
  · rcases hlim with ( hlim | rfl ) <;> simp_all +decide [ Centered ];
    · have h_empty : lam.natPart = 0 := by
        grind +suggestions;
      simp_all +decide [ omegaImage ];
    · simp_all +decide [ omegaImage ];
  · refine Or.inr ⟨ F', ?_, rfl ⟩;
    convert Finset.mem_erase_of_ne_of_mem hF'ne.ne_empty ( Finset.mem_powerset.mpr _ ) using 1;
    convert hF'sub using 1;
    convert rfl;
    · convert ScatFun.Centered_lam_add_succ hlim n using 1;
      norm_num [ add_assoc ];
    · convert ScatFun.Centered_lam_add_succ hlim n using 1;
      norm_num [ add_assoc ]

/-! ## Transporting a `pgl` of generators into `Centered` (memoir items 4 & 5 core)

The transport primitive `pglFinset_generators_equiv_mem_Centered` and `wedgeGenerator_bounding`
are proved *simultaneously* by strong induction on `n` (`transport_and_bounding`, below).  The two
parametrized helpers here (`wedge_columns_centered_reps_of_transport`) and above
(`wedgeGenerator_centered_witness_of_reps`) feed the induction; the standalone primitive and
`wedge_columns_centered_reps` are then extracted from it. -/

/-- **Column reps from a transport function.**  Given a way (`htrans`) to transport any `pglFinset`
of a nonempty subset of `Generators (λ+n)` into `Centered (λ+n+1)`, produce per-vertical
`Centered (λ+n+1)` representatives for the columns of the wedge over `S`.  Each column
`pgl (fun _ => glList ((S.toList.map Finset.toList).get i))` is `pglFinset P` for `P` the `i`-th
vertical Finset, so `htrans` applies directly.

Only the per-column `Equiv` is recorded (no self-absorption clause): the witness consumes the reps
as an aligned *list* `List.ofFn rep`, so duplicate representatives across distinct verticals never
need to collapse onto a single block (which would need the false `rep ⊕ rep ≤ rep`). -/
lemma wedge_columns_centered_reps_of_transport
    {lam : Ordinal.{0}} (n : ℕ)
    (S : Finset (Finset ScatFun))
    (hS : S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑n))))
    (htrans : ∀ F : Finset ScatFun, F.Nonempty → F ⊆ Generators (lam + ↑n) →
        ∃ h ∈ Centered (lam + ↑n + 1), Equiv (pglFinset F) h) :
    ∃ rep : Fin (S.toList.map Finset.toList).length → ScatFun,
      (∀ i, rep i ∈ Centered (lam + ↑n + 1)) ∧
      (∀ i, Equiv (pgl (fun _ => glList ((S.toList.map Finset.toList).get i))) (rep i)) := by
  -- `S` is a nonempty set of nonempty subsets of `Generators (λ+n)`.
  have hSsub : S ⊆ nonemptySubsets (Generators (lam + ↑n)) :=
    Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
  -- Each vertical column is `pglFinset P` for `P` the corresponding vertical Finset; transport it.
  have key : ∀ i : Fin (S.toList.map Finset.toList).length,
      ∃ h ∈ Centered (lam + ↑n + 1),
        Equiv (pgl (fun _ => glList ((S.toList.map Finset.toList).get i))) h := by
    intro i
    set P : Finset ScatFun := S.toList.get (i.cast (by simp)) with hP
    have hPS : P ∈ S := by rw [hP]; exact Finset.mem_toList.mp (List.get_mem _ _)
    have hPmem : P ∈ nonemptySubsets (Generators (lam + ↑n)) := hSsub hPS
    have hPne : P.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hPmem).1
    have hPsub : P ⊆ Generators (lam + ↑n) :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp hPmem).2
    have hcol : pgl (fun _ => glList ((S.toList.map Finset.toList).get i)) = pglFinset P := by
      have hlist : (S.toList.map Finset.toList).get i = P.toList := by
        rw [hP]; simp [List.get_eq_getElem, List.getElem_map]
      rw [pglFinset, hlist]
    obtain ⟨h, hmem, heq⟩ := htrans P hPne hPsub
    exact ⟨h, hmem, hcol ▸ heq⟩
  choose rep hmem heq using key
  exact ⟨rep, hmem, heq⟩

/-
**The `Centered`-facing content of `wedgeGenerator_bounding` (memoir steps 2–3).**  Provides an
aligned *list* `L ⊆ Centered (lam+n+1)` of per-vertical representatives together with the two
`L`-facing reductions: every `x ∈ L` reduces to the wedge generator `g`, and `g` reduces to
`glBin (glList L) (ω (gl D))`.  (The third reduction of the parent statement, `ω(gl D) ≤ g`, is
elementary and discharged separately in `wedgeGenerator_bounding` by `omega_diag_reduces_wedge`.)

## Status

Proved.  The per-column Centered upgrade + transport (memoir steps 2–3, the part the informal
proof compresses into "Set `F = {pgl F_i}`") is discharged by `generator_centered_pieces` and
`pglFinset_equiv_of_finGl`.

### Why a *list*, not a `Finset`
The columns are `columns i = pgl (fun _ => v i)` with `v i = glList ((S.toList.map Finset.toList).get i)`,
one per vertical `i : Fin n`.  Two distinct verticals `P_i ≠ P_j` may have `Centered`-equivalent
columns (`rep i = rep j`).  If we glued the *set* of representatives, those duplicates would have
to collapse onto one block of `gl F`, which needs `rep ⊕ rep ≤ rep` — false for a pointed gluing
(a single top-`CB` point cannot receive two). Keeping `L = List.ofFn rep` aligned with the
columns avoids any collapse: `glList (List.ofFn columns) ≤ glList (List.ofFn rep)` is a plain
slot-for-slot block embed (`glList_reduces_glList_ofFn`), and the downstream consumer routes the
repeats into the diagonal `ω d` summand (which has room for infinitely many copies), never into a
single de-duplicated block.

### Tools used
* `wedge_reduces_glBin_columns v d` (`BasicsHelpers`): `g ≤ glBin (glList (List.ofFn columns)) (ω d)`.
* `column_reduces_wedge v d i` (`BasicsHelpers`): each `columns i` reduces to `g`.
* `glList_reduces_glList_ofFn` (above) + `glBin_reduces_of_reduces`: transport columns to reps.
-/
lemma wedgeGenerator_centered_witness_of_reps
    {lam : Ordinal.{0}} (n : ℕ)
    (S : Finset (Finset ScatFun)) (D : Finset ScatFun)
    (hreps : ∃ rep : Fin (S.toList.map Finset.toList).length → ScatFun,
      (∀ i, rep i ∈ Centered (lam + ↑n + 1)) ∧
      (∀ i, Equiv (pgl (fun _ => glList ((S.toList.map Finset.toList).get i))) (rep i))) :
    ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑n + 1)) ∧
      (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
      Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
        (glBin (glList L) (omega (glList D.toList))) := by
  obtain ⟨rep, hrep_mem, hrep_equiv⟩ := hreps
  refine ⟨List.ofFn rep, ?_, ?_, ?_⟩
  · intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx; exact hrep_mem i
  · intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx
    have h_col_reduces_wedge :
        Reduces (pgl (fun _ => glList ((S.toList.map Finset.toList).get i)))
          (wedgeFinset (S.toList.map Finset.toList) D.toList) := by
      convert column_reduces_wedge _ _ i
      rfl
    exact (hrep_equiv i).2.trans h_col_reduces_wedge
  · refine' (wedge_reduces_glBin_columns _ _).trans _
    exact glBin_reduces_of_reduces
      (glList_reduces_glList_ofFn _ rep (fun i => (hrep_equiv i).1))
      (ContinuouslyReduces.refl _)

/-
**The mutual induction** (memoir items 4 & 5, `5_precise_struct_memo.tex:493-546`), by strong
induction on `n`, proving simultaneously:
* **transport(n)** — `pglFinset F ≡` a member of `Centered(λ+n+1)`, for `F ⊆ Generators(λ+n)`
  nonempty;
* **bounding(n)** — the `wedgeGenerator_bounding` conclusion at level `λ+n+1`.

At step `n`: **(1)** prove `transport(n)` from the induction hypothesis `ih` (which yields
`bounding(m)` for every `m < n`) — a wedge generator `φ ∈ Generators(λ+n)` is transported by
`bounding` at its own level; **(2)** prove `bounding(n)` from `transport(n)` via
`wedge_columns_centered_reps_of_transport` + `wedgeGenerator_centered_witness_of_reps` +
`omega_diag_reduces_wedge`.

Both steps are complete: step 1 (the per-generator structural transport) is discharged from
`ih` via `generator_centered_pieces`, `pglFinset_equiv_of_finGl`, and the base/`ℓ_λ` case. -/
private theorem transport_and_bounding
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0) :
    ∀ n : ℕ, FGBelow (lam + ↑n + 1) →
      (∀ F : Finset ScatFun, F.Nonempty → F ⊆ Generators (lam + ↑n) →
         ∃ h ∈ Centered (lam + ↑n + 1), Equiv (pglFinset F) h)
      ∧ (∀ (S : Finset (Finset ScatFun)),
           S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑n))) →
           ∀ (D : Finset ScatFun), D ⊆ Centered (lam + ↑n + 1) →
          ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑n + 1)) ∧
            (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
            Reduces (omega (glList D.toList))
              (wedgeFinset (S.toList.map Finset.toList) D.toList) ∧
            Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
              (glBin (glList L) (omega (glList D.toList)))) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro hFG
  -- **Step 1**: `transport(n)`.  The per-generator structural transport, using `ih` (i.e.
  -- `bounding(m)` for `m < n`) on the wedge-generator case.
  have htransport : ∀ F : Finset ScatFun, F.Nonempty → F ⊆ Generators (lam + ↑n) →
      ∃ h ∈ Centered (lam + ↑n + 1), Equiv (pglFinset F) h := by
    intro F hFne hFsub
    set F₀ := F.filter (fun g => ∀ (hl : Order.IsSuccLimit lam), g ≠ maxFun lam hlam) with hF₀_def
    by_cases hF₀ne : F₀.Nonempty;
    · -- For each `g ∈ F₀`, choose `l g` such that `l g ≠ []` and `l g ⊆ Centered (lam + n) ∪ omegaImage (Centered (lam + n))`.
      obtain ⟨l, hl⟩ : ∃ l : ScatFun → List ScatFun, (∀ g ∈ F₀, l g ≠ [] ∧ (∀ x ∈ l g, x ∈ Centered (lam + n) ∪ omegaImage (Centered (lam + n))) ∧ (∀ x ∈ l g, Reduces x g) ∧ Reduces g (glList (l g))) := by
        have hpieces : ∀ g ∈ F₀, ∃ l : List ScatFun, l ≠ [] ∧ (∀ x ∈ l, x ∈ Centered (lam + n) ∪ omegaImage (Centered (lam + n))) ∧ (∀ x ∈ l, Reduces x g) ∧ Reduces g (glList l) := by
          intros g hg₀
          obtain ⟨l, hl⟩ := generator_centered_pieces hlam hlim n (fun m hm => ih m hm (hFG.mono (by
          gcongr)) |>.2) n le_rfl g (hFsub (Finset.mem_filter.mp hg₀ |>.1)) (Finset.mem_filter.mp hg₀ |>.2);
          use l;
        choose! l hl₁ hl₂ hl₃ hl₄ using hpieces;
        exact ⟨ l, fun g hg => ⟨ hl₁ g hg, hl₂ g hg, hl₃ g hg, hl₄ g hg ⟩ ⟩;
      set F' := F₀.biUnion (fun g => (l g).toFinset) with hF'_def;
      refine ⟨ pglFinset F', pglFinset_mem_Centered_of_subset hlim n F' ?_ ?_, pglFinset_equiv_of_finGl ?_ ?_ ?_ ?_ ⟩;
      exact ⟨ _, Finset.mem_biUnion.mpr ⟨ _, hF₀ne.choose_spec, List.mem_toFinset.mpr ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( hl _ hF₀ne.choose_spec |>.1 ) ) ) ) ⟩ ⟩;
      · exact fun x hx => by obtain ⟨ g, hg, hx ⟩ := Finset.mem_biUnion.mp hx; exact hl g hg |>.2.1 x ( List.mem_toFinset.mp hx ) ;
      · exact hFne;
      · exact ⟨ _, Finset.mem_biUnion.mpr ⟨ _, hF₀ne.choose_spec, List.mem_toFinset.mpr ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( hl _ hF₀ne.choose_spec |>.1 ) ) ) ) ⟩ ⟩;
      · intro g hg
        by_cases hg₀ : g ∈ F₀;
        · use glList (l g);
          exact ⟨ glList_mem_FinGl_of_subset _ _ fun x hx => Finset.mem_biUnion.mpr ⟨ g, hg₀, List.mem_toFinset.mpr hx ⟩, hl g hg₀ |>.2.2.2 ⟩;
        · -- Since `g ∉ F₀`, we have `g = maxFun lam hlam` and `lam` is limit.
          obtain ⟨hlam_lim, hg_eq⟩ : Order.IsSuccLimit lam ∧ g = maxFun lam hlam := by
            grind;
          refine ⟨ glList F'.toList, ?_, ?_ ⟩;
          · exact glList_mem_FinGl_of_subset _ _ fun x hx => by aesop;
          · convert maxFun_reduces_of_lam_lt_rank hlam hlam_lim _ _ using 1;
            obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ F', lam < CBRank x₀.func := by
              obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ F₀, ∃ x₁ ∈ l x₀, lam < CBRank x₁.func := by
                exact ⟨ hF₀ne.choose, hF₀ne.choose_spec, Classical.choose ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( hl _ hF₀ne.choose_spec |>.1 ) ) ), Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( hl _ hF₀ne.choose_spec |>.1 ) ) ), piece_lam_lt_rank hlam hlam_lim n _ ( hl _ hF₀ne.choose_spec |>.2.1 _ ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr ( hl _ hF₀ne.choose_spec |>.1 ) ) ) ) ) ⟩;
              exact ⟨ hx₀.2.choose, Finset.mem_biUnion.mpr ⟨ x₀, hx₀.1, List.mem_toFinset.mpr hx₀.2.choose_spec.1 ⟩, hx₀.2.choose_spec.2 ⟩;
            exact lt_of_lt_of_le hx₀.2 ( ContinuouslyReduces.rank_monotone x₀.hScat ( glList F'.toList |> ScatFun.hScat ) ( mem_reduces_glList ( Finset.mem_toList.mpr hx₀.1 ) ) );
      · simp +zetaDelta at *;
        exact fun x y hy hy' hx => ⟨ y, hy, hl y hy hy' |>.2.2.1 x hx ⟩;
    · by_cases hlam_lim : Order.IsSuccLimit lam <;> simp_all +decide [ Finset.Nonempty ];
      refine ⟨ succMaxFun lam hlam, succMaxFun_mem_Centered hlam hlam_lim n, ?_ ⟩;
      rw [ show F = { maxFun lam hlam } from Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ hFne, hF₀ne ⟩ ] ; simp +decide [ pglFinset, succMaxFun_eq ] ;
      convert ScatFun.pgl_const_equiv_congr ( ScatFun.glList_single_equiv ( ScatFun.maxFun lam hlam ) |> Equiv.symm ) using 1
  -- **Step 2**: `bounding(n)` from `transport(n)`.
  refine ⟨htransport, ?_⟩
  intro S hS D _hD
  obtain ⟨L, hLmem, hLred, hgle⟩ :=
    wedgeGenerator_centered_witness_of_reps n S D
      (wedge_columns_centered_reps_of_transport n S hS htransport)
  exact ⟨L, hLmem, hLred,
    omega_diag_reduces_wedge (fun i => glList ((S.toList.map Finset.toList).get i))
      (glList D.toList),
    hgle⟩

/-- **Transport primitive** (memoir item 5 core, `5_precise_struct_memo.tex:544-546`): a `pglFinset`
of a nonempty `F ⊆ Generators (λ+n)` is `≡` a member of `Centered (λ+n+1)`.  Extracted from
`transport_and_bounding`. -/
lemma pglFinset_generators_equiv_mem_Centered
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (F : Finset ScatFun) (hFne : F.Nonempty) (hFsub : F ⊆ Generators (lam + ↑n)) :
    ∃ h ∈ Centered (lam + ↑n + 1), Equiv (pglFinset F) h :=
  (transport_and_bounding hlam hlim n hFG).1 F hFne hFsub

/-- **`Centered`-representatives for the vertical columns of a wedge generator** (memoir steps 2–3),
the standalone form used by the witness wrapper.  Direct application of the transport primitive to
each vertical Finset. -/
lemma wedge_columns_centered_reps
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (S : Finset (Finset ScatFun))
    (hS : S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑n)))) :
    ∃ rep : Fin (S.toList.map Finset.toList).length → ScatFun,
      (∀ i, rep i ∈ Centered (lam + ↑n + 1)) ∧
      (∀ i, Equiv (pgl (fun _ => glList ((S.toList.map Finset.toList).get i))) (rep i)) :=
  wedge_columns_centered_reps_of_transport n S hS
    (pglFinset_generators_equiv_mem_Centered hlam hlim n hFG)

/-- Wrapper: the reps come from `wedge_columns_centered_reps`. -/
lemma wedgeGenerator_centered_witness
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (S : Finset (Finset ScatFun))
    (hS : S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑n))))
    (D : Finset ScatFun) (_hD : D ⊆ Centered (lam + ↑n + 1)) :
    ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑n + 1)) ∧
      (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
      Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
        (glBin (glList L) (omega (glList D.toList))) :=
  wedgeGenerator_centered_witness_of_reps n S D
    (wedge_columns_centered_reps hlam hlim n hFG S hS)

/-- **Bounding a wedge generator.** Let `g` be a wedge generator built from a nonempty finite
set `S` of nonempty finite subsets of `Generators (lam + n)` (the verticals) and a finite
diagonal set `D ⊆ Centered (lam + (n+1))`. Then there is a finite set `F ⊆ Centered (lam+(n+1))`
such that every `f ∈ F` reduces to `g`, `ω(gl D)` reduces to `g`, and `g` reduces to the binary
gluing of `gl F` and `ω(gl D)`.

## Provided solution

Memoir proof (`5_precise_struct_memo.tex:494`): with `F := {pgl F_i : i ≤ k}` and `H := D`,
all three reductions come from `Gluingasupperbound_cor`
(`f = ⨆_{P ∈ 𝒫} f↾P ≤ gl_{P ∈ 𝒫} f↾P`) applied to the wedge's *own* domain, which is literally
`gl (wedgeDomFamily v d)` up to the `retag` reparametrisation (`Wedge/Defs.lean`): slot `i < n`
is `pgl (fun _ => v i) = pglFinset F_i` (giving `F ≤ g`) and slot `n + i` (for every `i : ℕ`) is
the diagonal `d = glList D.toList`, i.e. `ω`-many copies of it (giving `ω(gl D) ≤ g` and,
combined with the finitely-many vertical slots, `g ≤ (gl F) glbin (ω H)`).

Formalisation split.  The three reductions decompose into one elementary piece, discharged
here, and the `Centered`-facing content, factored into `wedgeGenerator_centered_witness`:

* **`ω(gl D) ≤ g` (diagonal).**  Elementary — `omega_diag_reduces_wedge`
  (`BasicsHelpers`): the diagonal slots of the wedge host `ω`-many copies of `d = gl D`, so
  `ω d` embeds into `g`.  Discharged in this proof.
* **`L ⊆ Centered (lam+n+1)`, `∀ x ∈ L, x ≤ g`, and `g ≤ glBin (glList L) (ω(gl D))`.**  This is
  the memoir's steps 2 (Centered upgrade via `finitenessOfCenteredFunctions_generators`) and 3
  (transport), factored into `wedgeGenerator_centered_witness`.  Proved there via the
  per-column transport `wedge_columns_centered_reps` (now fully discharged).

`L` is a *list* (not a de-duplicated `Finset`): distinct verticals may share a representative,
and collapsing the repeats onto a single block would need the false `rep ⊕ rep ≤ rep`.  The
consumer (`generator_omega_equiv`) takes `L.toFinset`, where repeats are harmless since the
`ω`-gluing there has infinitely many slots. -/
theorem wedgeGenerator_bounding
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (S : Finset (Finset ScatFun))
    (hS : S ∈ nonemptySubsets (nonemptySubsets (Generators (lam + ↑n))))
    (D : Finset ScatFun) (hD : D ⊆ Centered (lam + ↑n + 1)) :
    ∃ L : List ScatFun, (∀ x ∈ L, x ∈ Centered (lam + ↑n + 1)) ∧
      (∀ x ∈ L, Reduces x (wedgeFinset (S.toList.map Finset.toList) D.toList)) ∧
      Reduces (omega (glList D.toList)) (wedgeFinset (S.toList.map Finset.toList) D.toList) ∧
      Reduces (wedgeFinset (S.toList.map Finset.toList) D.toList)
        (glBin (glList L) (omega (glList D.toList))) := by
  obtain ⟨L, hLsub, hLred, hg_le⟩ :=
    wedgeGenerator_centered_witness hlam hlim n hFG S hS D hD
  exact ⟨L, hLsub, hLred,
    omega_diag_reduces_wedge (fun i => glList ((S.toList.map Finset.toList).get i))
      (glList D.toList),
    hg_le⟩

/-! ## Item 5: `ω g` is equivalent to `ω H` for `H ⊆ Centered α`
(`5_precise_struct_memo.tex:481`) -/

/-- **`ω` of a generator collapses to `ω` of a centered set.** For `g` genuinely produced by one
step of `genStep` (i.e. `g ∈ Centered (lam+(n+1))`, or `g ∈ ω{Generators (lam+n)}`'s… no: `g` is
one of the *three* `genStep` clauses at `Cn := Centered (lam+(n+1))`, `Gprev := Generators
(lam+n)`), `ω g` is equivalent to `ω (gl H)` for some finite `H ⊆ Centered (lam+(n+1))`.

(See the file docstring for why this is stated for `g ∈ genStep Cn Gprev` rather than for
arbitrary `g ∈ Generators (lam+(n+1))`: the latter is false at the base/limit generator `ℓ_λ`.)

## Provided solution

Memoir proof (`5_precise_struct_memo.tex:496`) case-splits on which `genStep` clause `g`
belongs to:
* **`g ∈ Cn` (centered clause).** Take `H := {g}`; `ω g ≡ ω (gl {g})` is immediate since
  `gl {g} ≡ g` (a one-element finite gluing is equivalent to its sole block).
* **`g ∈ ω{Cn}` clause, i.e. `g = ω c` for some `c ∈ Cn`.** Take `H := {c}`. Need
  `ω (ω c) ≡ ω c`: this is the "`ω` idempotent under re-indexing" fact (`ℕ × ℕ ≃ ℕ` shuffles a
  gluing-of-gluings-of-`c` into a single gluing of `c`'s); not yet in the codebase under this
  name, closest existing machinery is the reindexing argument in
  `exists_deep_reindex`/`omega_glFin_reduces_reindex` (`IntertwineReductions.lean:461`).
* **`g` a wedge generator.** Apply `wedgeGenerator_bounding` above (with the same `hgen`) to get
  `F, D` (renaming the memoir's `H` to `D` to avoid clashing with this lemma's own `H`) with
  `{ω(gl D)} ∪ F ≤ g ≤ (gl F) glbin (ω(gl D))`. Take `H := F ∪ D`. The memoir then invokes
  `Gluingasupperbound`/`Gluingaslowerbound2` to get `ω g ≡ ω (gl (F ∪ D))`: monotonicity of `ω`
  (not yet in the codebase — needs `Reduces a b → Reduces (omega a) (omega b)`, straightforward
  from `omega_func_prepend`, `IntertwineReductions.lean:100`) applied to both inequalities
  bounding `g`, plus a lemma commuting `ω` with `glBin`/`gl` on unions of finite sets (also not
  yet in the codebase, but should follow the same reindexing pattern as the previous bullet). -/
theorem generator_omega_equiv
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (g : ScatFun) (hg : g ∈ genStep (Centered (lam + ↑n + 1)) (Generators (lam + ↑n))) :
    ∃ H : Finset ScatFun, H ⊆ Centered (lam + ↑n + 1) ∧
      Equiv (omega g) (omega (glList H.toList)) := by
  classical
  simp only [genStep, omegaImage, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_powerset] at hg
  rcases hg with (hCn | hOmega) | hWedge
  · -- `g ∈ 𝒞_{λ+n+1}` (centered clause): take `H = {g}`.
    refine ⟨{g}, Finset.singleton_subset_iff.mpr hCn, ?_⟩
    rw [Finset.toList_singleton]
    exact omega_equiv_congr (glList_single_equiv g)
  · -- `g = ω c` with `c ∈ 𝒞_{λ+n+1}`: take `H = {c}`, use `ω (ω c) ≡ ω c`.
    obtain ⟨c, hc, rfl⟩ := hOmega
    refine ⟨{c}, Finset.singleton_subset_iff.mpr hc, ?_⟩
    rw [Finset.toList_singleton]
    exact (omega_omega_equiv c).trans (omega_equiv_congr (glList_single_equiv c))
  · -- wedge generator: bound it via `wedgeGenerator_bounding`, take `H = L.toFinset ∪ D`.
    obtain ⟨S, hS, D, hD, rfl⟩ := hWedge
    obtain ⟨L, hLsub, hLred, homegaD, hglBin⟩ :=
      wedgeGenerator_bounding hlam hlim n hFG S hS D hD
    set g := wedgeFinset (S.toList.map Finset.toList) D.toList with hgdef
    set H : Finset ScatFun := L.toFinset ∪ D with hHdef
    refine ⟨H, Finset.union_subset (fun x hx => hLsub x (List.mem_toFinset.mp hx)) hD, ?_⟩
    -- every element of `H` reduces into `glList H`
    have hwtoH : ∀ w, w ∈ H → Reduces w (glList H.toList) :=
      fun w hw => mem_reduces_glList (Finset.mem_toList.mpr hw)
    -- every `d ∈ D` reduces to `g` (through `ω (gl D) ≤ g`)
    have hd_le_g : ∀ w ∈ D, Reduces w g := by
      intro w hw
      have h1 : Reduces w (glList D.toList) := mem_reduces_glList (Finset.mem_toList.mpr hw)
      have h2 : Reduces (glList D.toList) (omega (glList D.toList)) :=
        reduces_block_gl (fun _ => glList D.toList) 0
      exact (h1.trans h2).trans homegaD
    -- every element of `H` reduces to `g`
    have hHle_g : ∀ w ∈ H, Reduces w g := by
      intro w hw
      rcases Finset.mem_union.mp hw with hwL | hwD
      · exact hLred w (List.mem_toFinset.mp hwL)
      · exact hd_le_g w hwD
    -- `ω (gl H) ≤ ω g`
    have dir2 : Reduces (omega (glList H.toList)) (omega g) :=
      (omega_reduces_of_reduces (glList_reduces_omega_of_forall
        (fun w hw => hHle_g w (Finset.mem_toList.mp hw)))).trans
        (omega_omega_equiv g).1
    -- `ω g ≤ ω (gl H)`; the columns list `L` reduces in blockwise (repeats land on ω-slots)
    have hA : Reduces (glList L) (omega (glList H.toList)) :=
      glList_reduces_omega_of_forall (fun w hw =>
        hwtoH w (Finset.mem_union_left _ (List.mem_toFinset.mpr hw)))
    have hB : Reduces (omega (glList D.toList)) (omega (glList H.toList)) := by
      have hglD : Reduces (glList D.toList) (omega (glList H.toList)) :=
        glList_reduces_omega_of_forall (fun w hw =>
          hwtoH w (Finset.mem_union_right _ (Finset.mem_toList.mp hw)))
      exact (gl_reduces_omega_of_forall (fun _ => hglD)).trans (omega_omega_equiv _).1
    have hglBin_le :
        Reduces (glBin (glList L) (omega (glList D.toList)))
          (omega (glList H.toList)) := by
      have hlist :
          Reduces (glList [glList L, omega (glList D.toList)])
            (omega (omega (glList H.toList))) := by
        apply glList_reduces_omega_of_forall
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hA
        · rcases List.mem_singleton.mp hw with rfl
          exact hB
      exact ((finGl_glBin_equiv_glList (glList L)
        (omega (glList D.toList))).1.trans hlist).trans (omega_omega_equiv _).1
    have hg_le : Reduces g (omega (glList H.toList)) := hglBin.trans hglBin_le
    have dir1 : Reduces (omega g) (omega (glList H.toList)) :=
      (omega_reduces_of_reduces hg_le).trans (omega_omega_equiv _).1
    exact ⟨dir1, dir2⟩

/-! ## Item 6: countably many finite gluings of generators collapse to one
(`trickforfinalproof`, `5_precise_struct_memo.tex:482`) -/

/-! ### Scaffold of `generators_gl_mem_finGl` (memoir `trickforfinalproof` steps 1–4)

The theorem below is assembled from three steps, each isolated as its own lemma (all now
proved).  Steps 1 and 2/4 are generic in the generating `Finset S` (lam-agnostic);
step 3 is the level-specific `ω`-closure that feeds them. -/

/-
**Step 1 (flatten to honest generators).**  A countable gluing of `FinGl S`-members is
equivalent to a countable gluing of an honest sequence valued in `S ∪ {empty}`.  Expand each
`f i ≡ glList L_i` with `L_i ⊆ S` (`exists_glList_of_finGl`) and flatten the double index
`(i, block-within-f i)` through a `ℕ × ℕ ≃ ℕ` pairing (`gl_gl_flatten_equiv`), padding the ragged
tails with `empty`.  Generic in `S`.  Proved.
-/
lemma gl_finGl_seq_flatten {S : Finset ScatFun} (f : ℕ → ScatFun)
    (hf : ∀ i, f i ∈ FinGl S.toFinFun) :
    ∃ h : ℕ → ScatFun, (∀ k, h k ∈ S ∨ h k = empty) ∧ Equiv (gl f) (gl h) := by
  revert hf;
  intro hf
  have h_exists_glList : ∀ i, ∃ Li : List ScatFun, Li ⊆ S.toList ∧ ScatFun.Equiv (f i) (ScatFun.glList Li) := by
    intro i
    obtain ⟨L, hL, hEq⟩ := exists_glList_of_finGl (hf i)
    exact ⟨L, fun w hw => Finset.mem_toList.mpr (hL w hw), hEq⟩
  choose Li hLi_sub hLi_equiv using h_exists_glList;
  -- Flatten the double index (i, block-within-f i) through a ℕ × ℕ ≃ ℕ pairing using `gl_gl_flatten_equiv`, padding ragged tails with empty so that every h k is either a member of S (a genuine block) or empty (padding).
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ScatFun, (∀ k, h k ∈ S ∨ h k = empty) ∧ ScatFun.Equiv (ScatFun.gl (fun i => ScatFun.glList (Li i))) (ScatFun.gl h) := by
    have := @ScatFun.gl_gl_flatten_equiv;
    use fun m => if h : m.unpair.2 < (Li m.unpair.1).length then (Li m.unpair.1).get ⟨m.unpair.2, h⟩ else empty;
    refine ⟨ ?_, ?_ ⟩;
    · intro m; by_cases h : ( Nat.unpair m ).2 < ( Li ( Nat.unpair m ).1 ).length <;> simp +decide [ h ] ;
      exact Or.inl <| Finset.mem_toList.mp <| hLi_sub _ <| List.getElem_mem _;
    · convert this _ using 1;
      grind;
  refine ⟨ h, hh.1, ?_ ⟩;
  have h_gl_equiv : ∀ (f g : ℕ → ScatFun), (∀ i, ScatFun.Equiv (f i) (g i)) → ScatFun.Equiv (ScatFun.gl f) (ScatFun.gl g) := by
    intros f g hfg;
    have h_gl_equiv : ∀ (f g : ℕ → ScatFun), (∀ i, ScatFun.Reduces (f i) (g i)) → ScatFun.Reduces (ScatFun.gl f) (ScatFun.gl g) := by
      exact fun f g a => gl_reduces_of_blockEmbed f g (fun ⦃a₁⦄ => a₁) (fun ⦃a₁ a₂⦄ a => a) a
    exact ⟨ h_gl_equiv f g fun i => hfg i |>.1, h_gl_equiv g f fun i => hfg i |>.2 ⟩;
  exact h_gl_equiv _ _ hLi_equiv |> ScatFun.Equiv.trans <| hh.2

/-- **Step 3 (`ω` of a generator stays in `FinGl (Generators (λ+n+1))`).**  Every
`s ∈ Generators (λ+n+1)` has `omega s ∈ FinGl (Generators (λ+n+1)).toFinFun`.  For an `s` produced
by `genStep`, `generator_omega_equiv` gives `omega s ≡ omega (gl H)` with `H ⊆ Centered (λ+n+1)`,
and `omega (gl H)` is a finite gluing of `Generators (λ+n+1)`-members (`Centered ⊆ Generators`
via `genStep`'s first clause, plus one `ω`/`gl` commutation); a carried-over
`s ∈ Generators (λ+n)` recurses via `Generators_mono_of_le`/`FinGl_mono_of_subset`.  This is the
infinite-fibre input to step 2/4.  Proved. -/
lemma omega_gen_mem_finGl
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1)) :
    ∀ s ∈ Generators (lam + ↑n + 1),
      omega s ∈ FinGl (Generators (lam + ↑n + 1)).toFinFun := by
  classical
  have hFGmono : ∀ β : Ordinal.{0}, β ≤ lam + (n : Ordinal.{0}) + 1 → FGBelow β := by
    intro β hβ γ hγ G hG
    exact hFG γ (lt_of_lt_of_le hγ hβ) G hG
  have hGen0 : Generators (lam + ((0 : ℕ) : Ordinal.{0})) = genBase lam := by
    unfold Generators
    rw [Ordinal.limitPart_add_natCast lam 0 hlim, Ordinal.natPart_add_natCast lam 0 hlim]
    rfl
  have key : ∀ m : ℕ, m ≤ n + 1 → ∀ s ∈ Generators (lam + (m : Ordinal.{0})),
      omega s ∈ FinGl (Generators (lam + (m : Ordinal.{0}))).toFinFun := by
    intro m
    induction m with
    | zero =>
      intro _ s hs
      refine finGl_of_equiv_glList (L := [s]) (fun w hw => ?_) ?_
      · rw [List.mem_singleton] at hw; rw [hw]; exact hs
      · have hseq : s = maxFun lam hlam := by
          rcases hlim with hl | hl
          · have hlne : lam ≠ 0 := by simpa using hl.ne_bot
            rw [hGen0, genBase, if_neg hlne, dif_pos hlam, Finset.mem_singleton] at hs
            exact hs
          · rw [hGen0, genBase, if_pos hl] at hs
            exact absurd hs (Finset.notMem_empty _)
        rw [hseq]
        exact (omega_maxFun_equiv_self lam hlam).trans (glList_single_equiv _)
    | succ m ih =>
      intro hm s hs
      have hmn : m ≤ n + 1 := le_trans (Nat.le_succ m) hm
      have hcast : (lam + ↑(m + 1) : Ordinal) = lam + ↑m + 1 := by push_cast; rw [add_assoc]
      rw [hcast] at hs ⊢
      rw [Generators_add_succ_eq hlim m] at hs
      rcases Finset.mem_union.mp hs with hs1 | hs2
      · have hsub : Generators (lam + ↑m) ⊆ Generators (lam + ↑m + 1) := by
          have hmono := Generators_mono_of_le (lam := lam) hlim (k := m) (n := m + 1)
            (Nat.le_succ m)
          rwa [hcast] at hmono
        exact FinGl_mono_of_subset hsub (ih hmn s hs1)
      · have hmle : (m : Ordinal.{0}) ≤ (n : Ordinal.{0}) := by
          exact_mod_cast (by omega : (m : ℕ) ≤ n)
        have hFGm : FGBelow (lam + ↑m + 1) := by
          apply hFGmono
          gcongr
        obtain ⟨H, hHsub, hHeq⟩ := generator_omega_equiv hlam hlim m hFGm s hs2
        have hmemL : ∀ w ∈ H.toList.map omega, w ∈ Generators (lam + ↑m + 1) := by
          intro w hw
          simp only [List.mem_map, Finset.mem_toList] at hw
          obtain ⟨c, hcH, rfl⟩ := hw
          have hc : c ∈ Centered (lam + ↑m + 1) := hHsub hcH
          have homc : omega c ∈ genStep (Centered (lam + ↑m + 1)) (Generators (lam + ↑m)) := by
            unfold genStep
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image_of_mem omega hc))
          rw [Generators_add_succ_eq hlim m]
          exact Finset.mem_union_right _ homc
        have hglmem : omega (glList H.toList) ∈ FinGl (Generators (lam + ↑m + 1)).toFinFun :=
          finGl_of_equiv_glList hmemL (omega_glList_equiv_glList_omega H.toList)
        exact finGl_closed_equiv _ hglmem hHeq.symm
  have hcastn : (lam + ↑n + 1 : Ordinal) = lam + ↑(n + 1) := by push_cast; rw [add_assoc]
  rw [hcastn]
  exact key (n + 1) (le_refl _)

/-- **Steps 2 & 4 (pigeonhole + reassembly).**  Given an honest sequence `h` valued in
`S ∪ {empty}` and the `ω`-closure `∀ s ∈ S, omega s ∈ FinGl S`, the countable gluing `gl h` lies
in `FinGl S`.  Partition `ℕ` by the (finite) value set `S`: each *finite* fibre is a finite gluing
of a single `s ∈ S` (so already in `FinGl S`), each *infinite* fibre collapses to `omega s`
(all blocks equal, via the `omega`/reindexing machinery) which is in `FinGl S` by `homega`;
reassemble the finitely many pieces by finite `glBin`-closure (`finGl_glBin_mem`).  Generic in
`S`.  Proved. -/
lemma gl_mem_or_empty_seq_mem_finGl {S : Finset ScatFun} (h : ℕ → ScatFun)
    (hmem : ∀ k, h k ∈ S ∨ h k = empty)
    (homega : ∀ s ∈ S, omega s ∈ FinGl S.toFinFun) :
    ∃ g : ScatFun, g ∈ FinGl S.toFinFun ∧ Equiv (gl h) g := by
  classical
  suffices H : ∀ (T : Finset ScatFun), T ⊆ S → ∀ (h' : ℕ → ScatFun),
      (∀ k, h' k ∈ T ∨ h' k = empty) →
      ∃ g : ScatFun, g ∈ FinGl S.toFinFun ∧ Equiv (gl h') g by
    exact H S (le_refl S) h hmem
  intro T
  induction T using Finset.induction with
  | empty =>
    intro _ h' hh'
    refine' ⟨empty, empty_mem_FinGl S.toFinFun (Set.isEmpty_coe_sort.mpr rfl), _⟩
    apply gl_equiv_empty_of_forall_empty
    intro k
    rcases hh' k with hk | hk
    · exact absurd hk (Finset.notMem_empty _)
    · exact hk
  | @insert s T' hsT' ih =>
    intro hsub h' hh'
    have hsS : s ∈ S := hsub (Finset.mem_insert_self s T')
    have hT'S : T' ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    set A' : ℕ → ScatFun := fun k => if h' k = s then h' k else empty with hA'
    set B' : ℕ → ScatFun := fun k => if h' k = s then empty else h' k with hB'
    have hsplit : Equiv (gl h') ((gl A') ⊕ (gl B')) := by
      have hh := gl_split_predicate (fun k => h' k = s) h'
      simpa only [hA', hB'] using hh
    -- `gl A'` lies in `FinGl S`
    have hA'const : (fun k => if h' k = s then h' k else empty)
        = (fun k => if h' k = s then s else empty) := by
      funext k; by_cases hk : h' k = s <;> simp [hk]
    have hgA' : gl A' ∈ FinGl S.toFinFun := by
      rw [hA', hA'const]
      by_cases hinf : {k | h' k = s}.Infinite
      · have heq := gl_indicator_infinite_equiv_omega s (fun k => h' k = s) hinf
        exact finGl_closed_equiv S.toFinFun (homega s hsS) heq.symm
      · rw [Set.not_infinite] at hinf
        have hcond : (fun k => if h' k = s then s else empty)
            = (fun n => if n ∈ hinf.toFinset then (fun _ => s) n else empty) := by
          funext k
          by_cases hk : h' k = s <;> simp [hk, Set.Finite.mem_toFinset]
        rw [hcond]
        refine finGl_of_equiv_glList ?_ (gl_ite_equiv_glList_map hinf.toFinset (fun _ => s))
        intro w hw
        simp only [List.mem_map] at hw
        obtain ⟨_, _, rfl⟩ := hw
        exact hsS
    -- `gl B'` handled by the induction hypothesis on `T'`
    have hB'mem : ∀ k, B' k ∈ T' ∨ B' k = empty := by
      intro k
      simp only [hB']
      by_cases hk : h' k = s
      · right; simp [hk]
      · simp only [hk, if_false]
        rcases hh' k with hkt | hke
        · rcases Finset.mem_insert.mp hkt with rfl | hkt'
          · exact absurd rfl hk
          · exact Or.inl hkt'
        · exact Or.inr hke
    obtain ⟨g', hg'mem, hg'eq⟩ := ih hT'S B' hB'mem
    exact ⟨(gl A') ⊕ g', finGl_glBin_mem hgA' hg'mem,
      hsplit.trans (glBin_congr (Equiv.refl (gl A')) hg'eq)⟩

/-- **Countable gluing of `FinGl (Generators (λ+n+1))` members collapses back into it** (memoir
`trickforfinalproof`, `5_precise_struct_memo.tex:519`).

Parametrised at `α = λ+n+1` for convenience, **not** out of necessity.  The reason is step 3: to
bound `ω` of a *wedge* generator it invokes `generator_omega_equiv → wedgeGenerator_bounding`,
which needs the finite-generation hypothesis `hFG : FGBelow (λ+n+1)` — a hypothesis the original
`(α)(f)(hf)` stub omitted entirely.  The `λ+n+1` form supplies it cleanly and matches the other
lemmas in this file.  The collapse itself holds at *every* level, including limits: at `α = λ`,
`Generators λ = {maxFun λ}` and `omega (maxFun λ) ≡ maxFun λ` (`omega` is the *plain* gluing `gl`,
whose CB-rank is the block supremum `λ`, and `maxFun λ` is the maximum at rank `λ`), so `gl f`
lands back in `FinGl {maxFun λ}`.  A fully general `(α)(hα)(FGBelow α)` form is therefore also
true, just more awkward to parametrise (`limitPart`/`natPart` bookkeeping).
(An earlier draft of this docstring wrongly asserted `omega (maxFun λ)` has rank `λ+1`; that
confuses the plain gluing `omega`/`gl` with the *pointed* gluing `pgl`, which is what bumps rank.)

Assembled from the three scaffolded steps above: `gl_finGl_seq_flatten` (step 1) then
`gl_mem_or_empty_seq_mem_finGl` (steps 2 & 4) fed the level-specific `ω`-closure
`omega_gen_mem_finGl` (step 3). -/
theorem generators_gl_mem_finGl
    {lam : Ordinal.{0}} (hlam : lam < omega1) (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) (hFG : FGBelow (lam + ↑n + 1))
    (f : ℕ → ScatFun) (hf : ∀ i, f i ∈ FinGl (Generators (lam + ↑n + 1)).toFinFun) :
    ∃ g : ScatFun, g ∈ FinGl (Generators (lam + ↑n + 1)).toFinFun ∧ Equiv (gl f) g := by
  obtain ⟨h, hmem, hequiv⟩ := gl_finGl_seq_flatten f hf
  obtain ⟨g, hg, hgeq⟩ :=
    gl_mem_or_empty_seq_mem_finGl h hmem (omega_gen_mem_finGl hlam hlim n hFG)
  exact ⟨g, hg, hequiv.trans hgeq⟩

end ScatFun

end