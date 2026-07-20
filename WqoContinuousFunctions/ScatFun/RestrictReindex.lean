import WqoContinuousFunctions.ScatFun.Basics

set_option autoImplicit false

/-!
# Restricting to a reindexed subfamily

Deliberately kept out of `ScatFun/Basics.lean` (which is imported almost everywhere): these
lemmas are only needed at the specific site of `case_N1_finite_nonempty_subcase_b_two`
(`LevelsFinitelyGenerated/Two.lean`) for wiring `diagonal_for_lambda_plus_one` onto a domain
restricted to a reindexed sub-collection of an ambient disjoint union. Adding them to `Basics`
previously broke an unrelated `grind` proof in `ScatFun/PreciseStructure/DiagonalForLambdaPlusOne.lean`
(grind's search is sensitive to the global declaration environment) — see the "grind env
sensitivity" project note. Import this file only where actually needed.

## Main results

* `ScatFun.restrict_iUnion_comp_isDisjointUnion` — restricting `F` to the union of a reindexed
  subfamily `A ∘ nSeq` (`nSeq` injective) of an existing disjoint union `A` again yields a
  disjoint union, via the pulled-back blocks.
* `ScatFun.restrict_restrict_transfer` — the reusable "no mathematical content, pure bookkeeping"
  transfer lemma: `CBRank`/`CBLevel`/`hdist` facts move for free across the restrict-of-restrict
  boundary via `Homeomorph.setCongr` + `CBRank_comp_homeomorph`/`CBLevel_homeomorph`.
-/

/-- Restricting `F` to the union of a *reindexed subfamily* `A ∘ nSeq` (`nSeq` injective, not
necessarily surjective) of an existing disjoint union `A` again yields a disjoint union, via the
pulled-back blocks `{w | (F.restrictEquiv _ w : F.domain) ∈ A (nSeq m)}`. -/
lemma ScatFun.restrict_iUnion_comp_isDisjointUnion (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) (nSeq : ℕ → ℕ) (hnSeq_inj : Function.Injective nSeq) :
    (F.restrict (⋃ m, A (nSeq m))).IsDisjointUnion
      (fun m => {w : ↑(F.restrict (⋃ m, A (nSeq m))).domain |
        (F.restrictEquiv (⋃ m, A (nSeq m)) w : ↑F.domain) ∈ A (nSeq m)}) := by
  obtain ⟨hAcl, hAdisj, _hAcover⟩ := hdu
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact IsClopen.preimage (hAcl (nSeq m))
      (continuous_subtype_val.comp (F.restrictEquiv (⋃ m, A (nSeq m))).continuous)
  · intro m m' hmm'
    rw [Set.disjoint_left]
    intro w hw hw'
    exact (Set.disjoint_left.mp
      (hAdisj (nSeq m) (nSeq m') (fun heq => hmm' (hnSeq_inj heq))) hw) hw'
  · ext w
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Set.mem_iUnion.mp (Subtype.mem (F.restrictEquiv (⋃ m, A (nSeq m)) w))

/-- **Purely bookkeeping**: `(F.restrict D).restrict {w | ... ∈ A0}` and `F.restrict A0`
(for `A0 ⊆ D`) describe the exact same set of Baire points — they only differ in how the
subtype is packaged (a nested existential vs. a single one). -/
lemma ScatFun.restrict_restrict_domain_eq (F : ScatFun) (D A0 : Set ↑F.domain) (hA0D : A0 ⊆ D) :
    ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).domain
      = (F.restrict A0).domain := by
  ext x
  constructor
  · rintro ⟨h, hmem⟩
    refine ⟨h.choose, ?_⟩
    simpa [ScatFun.restrictEquiv] using hmem
  · rintro ⟨h, hmem⟩
    refine ⟨⟨h, hA0D hmem⟩, ?_⟩
    simpa [ScatFun.restrictEquiv] using hmem

/-- The `.func`s of the two ScatFuns from `restrict_restrict_domain_eq` agree across the
homeomorphism induced by that domain equality — both just evaluate `F.func` at the same
underlying Baire point. -/
lemma ScatFun.restrict_restrict_func_eq (F : ScatFun) (D A0 : Set ↑F.domain) (hA0D : A0 ⊆ D) :
    ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func
      = (F.restrict A0).func ∘
        (Homeomorph.setCongr (ScatFun.restrict_restrict_domain_eq F D A0 hA0D)) := by
  funext x
  simp only [ScatFun.restrict, ScatFun.restrictEquiv, Homeomorph.setCongr, Function.comp_apply]
  rfl

/-- **The reusable transfer lemma**: `CBRank` and any "constant `yn` on the top `lam`-level"
fact (`hdist`) transport for free from `F.restrict A0` to the doubly-restricted
`(F.restrict D).restrict {w | ... ∈ A0}`, via `CBRank_comp_homeomorph`/`CBLevel_homeomorph`
along the domain-identifying homeomorphism. Pure bookkeeping, no mathematical content — this
is the single place that cost is paid, reusable at every future restrict-of-restrict site. -/
lemma ScatFun.restrict_restrict_transfer (F : ScatFun) (D A0 : Set ↑F.domain) (hA0D : A0 ⊆ D)
    (lam : Ordinal.{0}) (yn : Baire)
    (hdist : ∀ x ∈ CBLevel (F.restrict A0).func lam, (F.restrict A0).func x = yn) :
    (CBRank ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func
      = CBRank (F.restrict A0).func) ∧
    (∀ x ∈ CBLevel ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func lam,
      ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func x = yn) := by
  have hFunc := ScatFun.restrict_restrict_func_eq F D A0 hA0D
  set e := Homeomorph.setCongr (ScatFun.restrict_restrict_domain_eq F D A0 hA0D)
  refine ⟨?_, ?_⟩
  · rw [hFunc]; exact CBRank_comp_homeomorph e (F.restrict A0).func
  · intro x hx
    have hCBLevelEq : CBLevel ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func lam
        = e ⁻¹' (CBLevel (F.restrict A0).func lam) := by
      rw [hFunc]; exact CBLevel_homeomorph e (F.restrict A0).func lam
    rw [hCBLevelEq] at hx
    rw [hFunc]
    exact hdist (e x) hx
