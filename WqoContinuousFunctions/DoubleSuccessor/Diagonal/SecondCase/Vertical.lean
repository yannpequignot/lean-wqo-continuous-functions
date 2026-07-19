import WqoContinuousFunctions.DoubleSuccessor.PseudoCentered
import WqoContinuousFunctions.ScatFun.Wedge.Reindex

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Diagonal theorem, second case — vertical repackaging (`6_double_successor_memo.tex`)

`U`-independent restatements of the Vertical Theorem (`verticalTheorem`, from `PseudoCentered`).
`verticalTheorem'` and `verticalTheorem'_withRep` pull the `U`-independent data (the clopen split
`A0 ⊔ A1 = univ` and the three reductions) outside the per-neighbourhood `U` quantifier, leaving
only the genuinely `U`-dependent clopen datum inside — the form consumed by the second-case
diagonal construction.
-/

/-- **Vertical Theorem, U-independent repackaging.** Same content as `verticalTheorem`, but with
the clopen split `A0 ⊔ A1 = univ` and the reductions `F↾A0 ≤ glList H`, `F↾A1 ≤ g`,
`glList H ≤ g`, and `∀ V clopen ∋ y, g ≤ F⇂V` pulled *outside* the per-`U` quantifier (they are
U-independent in `verticalTheorem`'s proof; the only genuinely `U`-dependent datum is the clopen
`W ⊆ U` with `y ∉ W` and `glList H ≤ F⇂W`). This is the form consumed by the Diagonal Theorem's
second case, where a single `A0/A1` split per representative `g ∈ M` is needed for the left
reduction while the `W`'s are chosen per clopen `U ∋ y` for the right reduction. Derived by
instantiating `verticalTheorem` at `U = univ` for the split and per `U` for the `W`. -/
theorem verticalTheorem'
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y) :
    ∃ g : ScatFun, g ∈ ScatFun.Centered (α + 1 + 1) ∧
      ∃ H : Finset ScatFun, H ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧
        A0 ∪ A1 = Set.univ ∧ Disjoint A0 A1 ∧
        ScatFun.Reduces (F.restrict A0) (ScatFun.glList H.toList) ∧
        ScatFun.Reduces (F.restrict A1) g ∧
        ScatFun.Reduces (ScatFun.glList H.toList) g ∧
        (∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V)) ∧
        (∀ U : Set Baire, IsClopen U → y ∈ U →
          ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
            ScatFun.Reduces (ScatFun.glList H.toList) (F.coRestrict W)) := by
  obtain ⟨g, hgC, _, H, hHsub, hφ⟩ := verticalTheorem α hα hFG F hFrank hA y hpc
  obtain ⟨W0, -, -, A0, A1, hA0cl, hA1cl, hcover, hdisj, ⟨-, hA0red, -⟩, hVblock, hwg, -, -⟩ :=
    hφ Set.univ isClopen_univ (Set.mem_univ y)
  refine ⟨g, hgC, H, hHsub, A0, A1, hA0cl, hA1cl, hcover, hdisj, hA0red,
    (hVblock Set.univ isClopen_univ (Set.mem_univ y)).1, hwg,
    fun V hVcl hyV => (hVblock V hVcl hyV).2, ?_⟩
  intro U hUcl hyU
  obtain ⟨W, hWU, hWcl, _, _, _, _, _, _, ⟨hyW, _, hWred⟩, _, _, _, _⟩ := hφ U hUcl hyU
  exact ⟨W, hWU, hWcl, hyW, hWred⟩

/-- **Vertical Theorem, representative-exposing form.** Identical conclusion to `verticalTheorem'`,
but additionally returns the piece-equivalence `∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g`.

This datum is *already produced* by `verticalTheorem_setup` (`PseudoCentered.lean:766`, the final
conjunct `∀ P ∈ Part, Equiv (F.restrict P) g`) — it is the very reason the centered representative
`g` is canonical for the pseudo-centered partition — but `verticalTheorem`/`verticalTheorem'`
existentially discard it. The Diagonal Theorem's second case (`secondCase_singleBlockData`) needs it
to identify the vertical representative with the *externally fixed* block representative: the block's
induced pieces are `Equiv (F.restrict P) g_block`, and this conjunct says they are also
`Equiv (F.restrict P) g_vertical`, whence `g_vertical ≡ g_block` by symmetry+transitivity.

**Leaf.** Proving this is *not* new mathematics: it re-runs the exact assembly of `verticalTheorem'`
while threading `verticalTheorem_setup`'s last conjunct through the easy/hard-case split (both
branches return the same `g`). It is separated out here (rather than strengthening the existing
`verticalTheorem'` statement, which other call sites consume) as a dedicated packaging lemma. -/
theorem verticalTheorem'_withRep
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y) :
    ∃ g : ScatFun, g ∈ ScatFun.Centered (α + 1 + 1) ∧
      ∃ H : Finset ScatFun, H ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧
        A0 ∪ A1 = Set.univ ∧ Disjoint A0 A1 ∧
        ScatFun.Reduces (F.restrict A0) (ScatFun.glList H.toList) ∧
        ScatFun.Reduces (F.restrict A1) g ∧
        ScatFun.Reduces (ScatFun.glList H.toList) g ∧
        (∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V)) ∧
        (∀ U : Set Baire, IsClopen U → y ∈ U →
          ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
            ScatFun.Reduces (ScatFun.glList H.toList) (F.coRestrict W)) ∧
        (∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g) ∧
        ScatFun.Reduces g (F.restrict A1) ∧
        (∀ (h : IsCentered (F.restrict A1).func), cocenter (F.restrict A1).func h = y) := by
  obtain ⟨g, hgC, hgP, H, hHsub, hφ⟩ :=
    verticalTheorem α hα hFG F hFrank hA y hpc
  obtain ⟨W0, -, -, A0, A1, hA0cl, hA1cl, hcover, hdisj, ⟨-, hA0red, -⟩,
      hVblock, hwg, hgA1, hcoc⟩ :=
    hφ Set.univ isClopen_univ (Set.mem_univ y)
  refine ⟨g, hgC, H, hHsub, A0, A1, hA0cl, hA1cl, hcover, hdisj, hA0red,
    (hVblock Set.univ isClopen_univ (Set.mem_univ y)).1, hwg,
    fun V hVcl hyV => (hVblock V hVcl hyV).2, ?_, hgP, hgA1, hcoc⟩
  intro U hUcl hyU
  obtain ⟨W, hWU, hWcl, _, _, _, _, _, _, ⟨hyW, _, hWred⟩, _, _, _, _⟩ := hφ U hUcl hyU
  exact ⟨W, hWU, hWcl, hyW, hWred⟩


end
