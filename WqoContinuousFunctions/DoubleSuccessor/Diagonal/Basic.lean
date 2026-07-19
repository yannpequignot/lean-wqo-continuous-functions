import WqoContinuousFunctions.DoubleSuccessor.PseudoCentered
import WqoContinuousFunctions.ScatFun.Wedge.Reindex

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-- A point of the Baire space can be separated from any finite set not containing it by a
basic clopen neighbourhood `nbhd y N`: take a level `N` past the first coordinate where `y`
differs from each of the finitely many points. Used to prove `Y_𝒫 \ {y}` is infinite (a finite
`Y'` could be dodged by a clopen `V ∋ y`, contradicting strong solvability clause 2). -/
lemma exists_clopen_nbhd_disjoint_finite {S : Set Baire} (hS : S.Finite) {y : Baire}
    (hy : y ∉ S) : ∃ V : Set Baire, IsClopen V ∧ y ∈ V ∧ Disjoint V S := by
  classical
  -- `nbhd` is antitone in the level: a larger level is a smaller (more constrained) set.
  have hmono : ∀ {a b : ℕ}, a ≤ b → nbhd y b ⊆ nbhd y a := fun {a b} hab h hh i hi =>
    hh i (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hab))
  -- For each `s ≠ y`, a level `lvl s` at which `s ∉ nbhd y (lvl s)`.
  have hsep : ∀ s : Baire, s ≠ y → ∃ k, s ∉ nbhd y k := fun s hne => by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i + 1, fun hmem => hi (hmem i (Finset.mem_range.mpr (Nat.lt_succ_self i)))⟩
  set lvl : Baire → ℕ := fun s => if h : s ≠ y then (hsep s h).choose else 0 with hlvldef
  have hlvl : ∀ s, s ≠ y → s ∉ nbhd y (lvl s) := fun s hne => by
    simpa [hlvldef, hne] using (hsep s hne).choose_spec
  -- A single level `N` beating every `lvl s` for `s ∈ S`.
  refine' ⟨nbhd y (hS.toFinset.sup lvl), baire_nbhd_isClopen _ _, fun i _ => rfl, _⟩
  rw [Set.disjoint_left]
  intro s hsV hsS
  have hne : s ≠ y := fun h => hy (h ▸ hsS)
  exact hlvl s hne (hmono (Finset.le_sup (hS.mem_toFinset.mpr hsS)) hsV)
/-! ## Strongly solvable functions (`6_double_successor_memo.tex:254-264`) -/

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- `F` together with a fine `c`-partition `𝒫` (fine relative to `lam`) is **strongly
solvable at `y`** (memoir Definition, `6_double_successor_memo.tex:258-264`): `y ∈ Y_𝒫` and
for every clopen neighbourhood `V` of `y`,

1. the set `{y_P | P ∈ 𝒫, y_P ∉ V}` of cocenters outside `V` is finite, and
2. for every `P ∈ 𝒫^{≠y}` (i.e. `P ∈ 𝒫` with `y_P ≠ y`) there is `Q ∈ 𝒫^{≠y}` with `y_Q ∈ V`
   and `F↾P ≤ F↾Q`.

As with `IsPseudoCenteredAt` (`PseudoCentered.lean`), fineness (`IsFine lam`) is bundled in —
the memoir's definition applies to "`f` together with a fine `c`-partition" — and `lam` is
carried explicitly; call sites for `F` of rank `α+2` instantiate `lam = α.limitPart`. -/
def IsStronglySolvableAt (hA : F.IsCPartition Part) (lam : Ordinal.{0}) (y : Baire) : Prop :=
  hA.IsFine lam ∧ y ∈ hA.cocenterSet ∧
    ∀ V : Set Baire, IsClopen V → y ∈ V →
      (hA.cocenterSet \ V).Finite ∧
      ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
        ∃ (Q : Set ↑F.domain) (hQ : Q ∈ Part), hA.cocenterOf hQ ≠ y ∧ hA.cocenterOf hQ ∈ V ∧
          ScatFun.Reduces (F.restrict P) (F.restrict Q)

/-- A pseudo-centered function is strongly solvable at its cocenter (the degenerate case
`𝒫^{≠y} = ∅`, `Y_𝒫 = {y}`; cf. the memoir's remark before the Diagonal Theorem,
`6_double_successor_memo.tex:266`): clause 1 holds because `Y_𝒫 \ V ⊆ {y} \ V = ∅`, and
clause 2 is vacuous because every piece has cocenter `y`. -/
lemma IsPseudoCenteredAt.isStronglySolvableAt {hA : F.IsCPartition Part}
    {lam : Ordinal.{0}} {y : Baire} (h : hA.IsPseudoCenteredAt lam y) :
    hA.IsStronglySolvableAt lam y := by
  refine ⟨h.1, by rw [h.2.1]; exact Set.mem_singleton y,
    fun V hV hyV => ⟨?_, fun P hP hPy => ?_⟩⟩
  · exact (Set.finite_singleton y).subset (h.2.1 ▸ Set.diff_subset)
  · have hmem : hA.cocenterOf hP ∈ hA.cocenterSet := ⟨⟨P, hP⟩, rfl⟩
    rw [h.2.1] at hmem
    exact absurd hmem hPy

/-- **The remark before the Diagonal Theorem** (`6_double_successor_memo.tex:277`): if `𝒫^{≠y}` is
non-empty (some piece has cocenter `≠ y`), then `Y' = Y_𝒫 \ {y}` is **infinite**, by strong
solvability of `F` at `y`.

Proof (contrapositive): were `Y'` finite, then — since `y ∉ Y'` — we could pick a clopen `V ∋ y`
disjoint from `Y'` (`exists_clopen_nbhd_disjoint_finite`). Feeding `V` to strong solvability
clause 2 with any witness piece `P ∈ 𝒫^{≠y}` yields `Q ∈ 𝒫^{≠y}` with `y_Q ∈ V`; but `y_Q ∈ Y'`
(it is a cocenter `≠ y`), contradicting `V ∩ Y' = ∅`.

(The memoir also calls `Y'` *discrete*; that is clause 1 — for every clopen `V ∋ y` only finitely
many cocenters lie outside `V`, so `y` is the sole accumulation point — and is recorded directly
by `hss.2.2 V _ _ |>.1` at each use site. We isolate only the infiniteness here, which is what the
two-case proof actually enumerates.) -/
lemma IsStronglySolvableAt.cocenterSet_diff_singleton_infinite {hA : F.IsCPartition Part}
    {lam : Ordinal.{0}} {y : Baire} (hss : hA.IsStronglySolvableAt lam y)
    (hne : ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y) :
    (hA.cocenterSet \ {y}).Infinite := by
  obtain ⟨P, hP, hPy⟩ := hne
  intro hfin
  -- Separate `y` from the (assumed finite) `Y'` by a clopen `V`.
  obtain ⟨V, hVcl, hyV, hVdisj⟩ :=
    exists_clopen_nbhd_disjoint_finite hfin (fun h => h.2 rfl)
  -- Strong solvability clause 2 at `V` and `P` produces a cocenter `y_Q ≠ y` inside `V`.
  obtain ⟨Q, hQ, hQy, hQV, _⟩ := (hss.2.2 V hVcl hyV).2 P hP hPy
  -- But `y_Q ∈ Y'`, contradicting `V ∩ Y' = ∅`.
  have hQ' : hA.cocenterOf hQ ∈ hA.cocenterSet \ {y} := ⟨⟨⟨Q, hQ⟩, rfl⟩, hQy⟩
  exact (Set.disjoint_left.mp hVdisj hQV) hQ'

/-- **`y` is the unique accumulation point of `Y_𝒫`** — the *discrete* half of the memoir remark
(`6_double_successor_memo.tex:277`), packaged as a topological statement. Given strong solvability
at `y` and `𝒫^{≠y} ≠ ∅`, a point `z` is an accumulation point of `Y_𝒫` (`AccPt z (𝓟 Y_𝒫)`) iff
`z = y`.

* **`z ≠ y` is not an accumulation point** (this half uses only clause 1, not `𝒫^{≠y} ≠ ∅`):
  separate `z` from `y` by a clopen `V ∋ y` with `z ∉ V` (`exists_clopen_nbhd_disjoint_finite`);
  clause 1 makes `Y_𝒫 \ V` finite, so `z`'s clopen neighbourhood `Vᶜ` meets `Y_𝒫` in the finite
  set `Y_𝒫 ∩ Vᶜ = Y_𝒫 \ V` — an accumulation point would force it infinite
  (`Set.Infinite.of_accPt`).
* **`y` is an accumulation point** (needs `𝒫^{≠y} ≠ ∅`): `Y' = Y_𝒫 \ {y}` is infinite
  (`cocenterSet_diff_singleton_infinite`) while, by clause 1, every clopen `V ∋ y` omits only
  finitely many cocenters, so `V ∩ Y'` is infinite (infinite minus finite), hence nonempty.

Downstream this is the topological form behind "`y_n → y`" for any injective enumeration of `Y'`. -/
lemma IsStronglySolvableAt.accPt_cocenterSet_iff {hA : F.IsCPartition Part}
    {lam : Ordinal.{0}} {y : Baire} (hss : hA.IsStronglySolvableAt lam y)
    (hne : ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y) (z : Baire) :
    AccPt z (Filter.principal hA.cocenterSet) ↔ z = y := by
  constructor
  · -- Forward: only `y` can be an accumulation point.
    intro hAcc
    by_contra hzy
    obtain ⟨V, hVcl, hyV, hVdisj⟩ :=
      exists_clopen_nbhd_disjoint_finite (Set.finite_singleton z)
        (fun h => hzy ((Set.mem_singleton_iff.mp h).symm))
    have hzV : z ∉ V := Set.disjoint_singleton_right.mp hVdisj
    have hfin : (hA.cocenterSet \ V).Finite := (hss.2.2 V hVcl hyV).1
    have hVc_nhds : Vᶜ ∈ nhds z := hVcl.isClosed.isOpen_compl.mem_nhds hzV
    -- `Y_𝒫 ∩ Vᶜ` inherits the accumulation but is finite — contradiction.
    have hacc' : AccPt z (Filter.principal (hA.cocenterSet ∩ Vᶜ)) := by
      rw [accPt_iff_frequently] at hAcc ⊢
      rw [Filter.frequently_iff] at hAcc ⊢
      intro U hU
      obtain ⟨x, hxW, hxne, hxc⟩ := hAcc (Filter.inter_mem hU hVc_nhds)
      exact ⟨x, hxW.1, hxne, hxc, hxW.2⟩
    have hfin' : (hA.cocenterSet ∩ Vᶜ).Finite := hfin.subset (fun x hx => ⟨hx.1, hx.2⟩)
    exact absurd (Set.Infinite.of_accPt hacc') hfin'.not_infinite
  · -- Backward: `y` is an accumulation point since `Y'` is infinite.
    rintro rfl
    rw [accPt_iff_frequently, Filter.frequently_iff]
    intro U hU
    obtain ⟨O, hOsub, hOopen, hzO⟩ := mem_nhds_iff.mp hU
    obtain ⟨V, hVcl, hzV, hVO⟩ := baire_exists_clopen_subset_of_open z O hOopen hzO
    have hfin : (hA.cocenterSet \ V).Finite := (hss.2.2 V hVcl hzV).1
    have hYinf : (hA.cocenterSet \ {z}).Infinite := hss.cocenterSet_diff_singleton_infinite hne
    -- `(Y' \ (Y_𝒫 \ V)) ⊆ Y' ∩ V`, and the left side is infinite (infinite minus finite).
    have hsub : (hA.cocenterSet \ {z}) \ (hA.cocenterSet \ V) ⊆ (hA.cocenterSet \ {z}) ∩ V :=
      fun x hx => ⟨hx.1, by by_contra hxV; exact hx.2 ⟨hx.1.1, hxV⟩⟩
    obtain ⟨x, ⟨hxc, hxz⟩, hxV⟩ := (Set.Infinite.mono hsub (hYinf.diff hfin)).nonempty
    exact ⟨x, hOsub (hVO hxV), hxz, hxc⟩

end ScatFun.IsCPartition
/--
**Centered functions of rank in `(λ, α+2]` have a `Centered (α+2)` representative.** Given
`FG(≤α+1)` (`ScatFun.FGBelow (α+1+1)`), every centered `f` whose rank satisfies
`λ < CB(f) ≤ α+2` (`λ = α.limitPart`) is `≡` to some member of `𝒞_{α+2}`. The lower bound
`λ < CB(f)` is essential (and is exactly what fineness of a `c`-partition supplies): `𝒞_{α+2}`
has *minimum* rank `λ+1`, so functions of rank `≤ λ` cannot be represented there. This is the
finiteness engine behind representative selection: since `𝒞_{α+2}` is a `Finset`, only finitely
many `≡`-classes of pieces can occur.
-/
lemma centered_equiv_mem_Centered_le_doubleSucc
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (f : ScatFun) (hlb : α.limitPart < CBRank f.func) (hrank : CBRank f.func ≤ α + 1 + 1)
    (hcent : IsCentered f.func) :
    ∃ h ∈ ScatFun.Centered (α + 1 + 1), ScatFun.Equiv f h := by
  revert f;
  intro f hlb hrank hcent
  set lam := α.limitPart
  set m := α.natPart
  have hlam_lt : lam < omega1 := by
    exact lt_of_le_of_lt le_self_add ( Ordinal.eq_limitPart_add_natPart α ▸ hα )
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hlam_eq : lam + (m + 1 : Ordinal.{0}) = α + 1 := by
    rw [ ← add_assoc, Ordinal.eq_limitPart_add_natPart α ]
  have hlam_succ_eq : lam + (m + 1 : Ordinal.{0}) + 1 = α + 1 + 1 := by
    rw [hlam_eq]
  generalize_proofs at *;
  have := ScatFun.finitenessOfCenteredFunctions_generators hlam_lt hlim ( m + 1 ) ( by
    convert hFG using 1 ) f ⟨ by
    exact le_of_lt hlb, by
    convert hrank using 1 ⟩ hcent
  generalize_proofs at *;
  rcases this with ( h | ⟨ k, ι, hk, h ⟩ );
  · exact ⟨ _, ScatFun.minFun_mem_Centered hlam_lt ( by aesop ) ( m + 1 ) |> fun h => by aesop, h ⟩;
  · have := ScatFun.pglFinset_generators_equiv_mem_Centered hlam_lt hlim ( m + 1 ) ( by
      convert hFG using 1 ) ( Finset.image ( ( ScatFun.Generators ( lam + ( m + 1 : Ordinal.{0} ) ) ).toFinFun ∘ ι ) Finset.univ ) ( by
      exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hk ⟩ ) ⟩ ) ( by
      simp +decide only [Ordinal.add_one_eq_succ, Nat.cast_add, Nat.cast_one, Finset.image_subset_iff, Finset.mem_univ, comp_apply, forall_const];
      exact fun x => Finset.mem_toList.mp ( List.get_mem _ _ ) )
    generalize_proofs at *;
    obtain ⟨ h, hh₁, hh₂ ⟩ := this; use h; simp_all +decide ;
    exact h.trans ( ScatFun.pgl_repSeq_equiv_pglFinset_image _ hk |> ScatFun.Equiv.trans <| hh₂ )

/-- **`c`-partition upper bound into `ω g`** (memoir `Gluingasupperbound` at the `ScatFun` level).
If every piece of a `c`-partition reduces into `g`, then `F ≤ ω g`. Proof: enumerate `𝒫`
injectively as an `ℕ`-family padded by `∅` (a genuine disjoint union, `F.IsDisjointUnion`), so
`F ≤ gl_i F↾A_i` (`scatFun_reduces_gl_of_domain_partition`); each block reduces into `g`
(a piece, or `∅` which reduces to anything), hence `gl_i F↾A_i ≤ ω g` (`gl_reduces_omega_of_forall`).
Reusable (the second case's `F↾A⁰ ≤ w` step is the same shape). -/
theorem ScatFun.IsCPartition.reduces_omega_of_forall_piece_le
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} (hpiece : ∀ P ∈ Part, ScatFun.Reduces (F.restrict P) g) :
    ScatFun.Reduces F (ScatFun.omega g) := by
  classical
  rcases Part.eq_empty_or_nonempty with hPempty | hPne
  · -- Empty partition ⟹ `F.domain = univ = ∅`.
    have huniv : (Set.univ : Set ↑F.domain) = ∅ := by rw [← hA.sUnion_eq, hPempty]; simp
    exact ScatFun.reduces_of_isEmpty_domain (Set.univ_eq_empty_iff.mp huniv)
  · have : Countable ↑Part := hA.countable.to_subtype
    obtain ⟨e, he⟩ := Countable.exists_injective_nat ↑Part
    set A : ℕ → Set ↑F.domain :=
      fun n => if h : ∃ p : ↑Part, e p = n then (Classical.choose h).val else ∅ with hAdef
    have hdu : F.IsDisjointUnion A := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        by_cases h : ∃ p : ↑Part, e p = i
        · simp only [hAdef, dif_pos h]; exact hA.isClopen _ (Classical.choose h).2
        · simp only [hAdef, dif_neg h]; exact isClopen_empty
      · intro i j hij
        by_cases hi : ∃ p : ↑Part, e p = i
        · by_cases hj : ∃ q : ↑Part, e q = j
          · simp only [hAdef, dif_pos hi, dif_pos hj]
            have hne : (Classical.choose hi).val ≠ (Classical.choose hj).val := by
              intro hval
              have : Classical.choose hi = Classical.choose hj := Subtype.ext hval
              exact hij (by rw [← (Classical.choose_spec hi), ← (Classical.choose_spec hj), this])
            exact hA.pairwiseDisjoint (Classical.choose hi).2 (Classical.choose hj).2 hne
          · simp only [hAdef, dif_pos hi, dif_neg hj]; exact disjoint_bot_right
        · simp only [hAdef, dif_neg hi]; exact disjoint_bot_left
      · rw [← hA.sUnion_eq]
        ext x
        simp only [Set.mem_iUnion, Set.mem_sUnion]
        constructor
        · rintro ⟨i, hxi⟩
          by_cases h : ∃ p : ↑Part, e p = i
          · rw [hAdef] at hxi; simp only [dif_pos h] at hxi
            exact ⟨(Classical.choose h).val, (Classical.choose h).2, hxi⟩
          · rw [hAdef] at hxi; simp only [dif_neg h] at hxi; exact absurd hxi (Set.notMem_empty x)
        · rintro ⟨P, hP, hxP⟩
          refine ⟨e ⟨P, hP⟩, ?_⟩
          have hex : ∃ p : ↑Part, e p = e ⟨P, hP⟩ := ⟨⟨P, hP⟩, rfl⟩
          rw [hAdef]; simp only [dif_pos hex]
          have : Classical.choose hex = ⟨P, hP⟩ := he (Classical.choose_spec hex)
          rwa [this]
    refine (scatFun_reduces_gl_of_domain_partition F A hdu).trans ?_
    apply gl_reduces_omega_of_forall
    intro i
    by_cases h : ∃ p : ↑Part, e p = i
    · have : A i = (Classical.choose h).val := by simp only [hAdef, dif_pos h]
      rw [this]; exact hpiece _ (Classical.choose h).2
    · have hempty : IsEmpty ↑(F.restrict (A i)).domain := by
        have : A i = ∅ := by simp only [hAdef, dif_neg h]
        rw [this]; exact Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])
      exact ScatFun.reduces_of_isEmpty_domain hempty

/-- **Double-corestriction bridge.** If `V' ⊆ U` and `V' ⊆ W`, then `F⇂V'` reduces into
`(F⇂U)⇂W`: both are restrictions of `F↾{F.func ∈ U}` to nested domain sets, so `restrict`
monotonicity + `restrict_reduces_restrict_restrict` give the reduction. -/
lemma coRestrict_inter_reduces (F : ScatFun) {U W V' : Set Baire}
    (hV'U : V' ⊆ U) (hV'W : V' ⊆ W) :
    ScatFun.Reduces (F.coRestrict V') ((F.coRestrict U).coRestrict W) := by
  have hA0T : {z : ↑F.domain | F.func z ∈ V'} ⊆ {z : ↑F.domain | F.func z ∈ U} :=
    fun z hz => hV'U hz
  refine (restrict_reduces_restrict_restrict F {z | F.func z ∈ U}
    {z | F.func z ∈ V'} hA0T).trans ?_
  apply restrict_reduces_of_subset
  intro w hw
  show (F.restrict {z | F.func z ∈ U}).func w ∈ W
  exact hV'W hw


end
