import WqoContinuousFunctions.DoubleSuccessor.Diagonal.FirstCase
import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.Construction

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Formalization of `6_double_successor_memo.tex`, §6.3 — Strongly solvable functions

Scaffold matching the phase-lemma style of `PseudoCentered.lean` and `Fine.lean`: the
definitions are complete and the Diagonal Theorem's **first case is fully proved**. The second
case (`diagonalTheorem_secondCase`) is likewise fully proved, via `diagonalTheorem_secondCase_setup`
and `diagonalTheorem_secondCase_construction`. `secondCase_singleBlockData`
(the per-block Vertical-Theorem core) reduces to the *existing* `verticalTheorem'` re-instantiated
at a smaller base ordinal `β` (sharing `α`'s limit part), so there is **no** variable-rank Vertical
Theorem to build — only routine plumbing leaves (`limitPart` squeeze ①, generator-level
monotonicity ②, representative identification ③, and the restrict-of-restrict domain transport ④),
plus the `verticalTheorem'_withRep` packaging leaf that re-exposes the piece-equivalence
`verticalTheorem_setup` already proves. The two Disjointification clauses
`secondCase_wedge_vertical_clause`/`secondCase_wedge_diag_clause` and the two reductions inside
`diagonalTheorem_secondCase_construction` (left `F↾A¹ ≤ ⋀(v ∣ gl D)` and right `w ≤ F⇂W`) rest on
the wedge upper/lower bounds and cocenter-rigidity machinery.

## Contents

* `ScatFun.IsCPartition.IsStronglySolvableAt` — memoir Definition
  (`6_double_successor_memo.tex:258-264`): `F` with a fine `c`-partition `𝒫` is *strongly
  solvable at `y ∈ Y_𝒫`* if for every clopen `V ∋ y` (1) only finitely many cocenters lie
  outside `V`, and (2) every piece with cocenter `≠ y` reduces into a piece with cocenter
  `≠ y` inside `V`.
* `ScatFun.IsCPartition.IsPseudoCenteredAt.isStronglySolvableAt` — a pseudo-centered
  function is (degenerately) strongly solvable: `Y_𝒫 = {y}`, so both clauses are vacuous.
  **Proved** — a sanity check that the definition composes with `PseudoCentered.lean`'s.
* `diagonalTheorem` — the **Diagonal Theorem** (memoir `DiagonalTheorem`,
  `6_double_successor_memo.tex:272-276`). **Proved by dispatch**: a
  `by_cases` on "`CB(F↾P) = λ+1` for all `P ∈ 𝒫_M`" delegating to the two case-lemmas below.
* `diagonalTheorem_firstCase` — memoir first case (`:287-297`), `g = ω D`. **Proved** (all of
  its ingredients, including the representative selection `diagonalTheorem_firstCase_representatives`,
  are proved).
* `diagonalTheorem_secondCase` — memoir second case (`:301-386`), `g = w ⊕ ⋀(...∣D)` via the
  Vertical Theorem + Disjointification/wedge bounds. **Proved by dispatch** to
  `diagonalTheorem_secondCase_setup` (itself proved by dispatch to
  `diagonalTheorem_secondCase_construction`). See each leaf's docstring for the construction
  and the status of every ingredient.

## Conventions

As in `verticalTheorem` (`PseudoCentered.lean`), `F` has `CB`-rank `α+2` (spelled
`α + 1 + 1`, matching `FGBelow`'s successor bookkeeping), fineness is relative to
`α.limitPart` (which also covers *finite* `α`, where `limitPart = 0`), the hypothesis
`FG(≤α+1) = FG(<α+2)` is `ScatFun.FGBelow (α+1+1)`, and the memoir's `𝒫^{≠y}` ("pieces whose
cocenter differs from `y`") is rendered pointwise as `hA.cocenterOf hP ≠ y`.
-/

/-- **The Diagonal Theorem** (memoir `DiagonalTheorem`, `6_double_successor_memo.tex:272-276`).
Let `α < ω₁` and assume `FG(≤α+1)` (`ScatFun.FGBelow (α+1+1)`). If `F : ScatFun` with
`CB(F) = α+2` is strongly solvable at `y` (witnessed by a fine `c`-partition `Part`), then
there is `g ∈ FinGl 𝒢_{α+2}` with `F ≤ g` and `g ≤ F⇂U` for every clopen `U ∋ y`.

## Provided solution (`6_double_successor_memo.tex:278-386`)

Write `α = λ + n` (`λ = α.limitPart`, possibly `0`). Let `𝒫_M = 𝒫 \ 𝒫^{≠y}` (pieces with
cocenter `y`) and `𝒫_D = 𝒫^{≠y}`; if `𝒫_D ≠ ∅` then `Y' = Y_𝒫 \ {y}` is infinite and discrete
(strong solvability, clause 1). Split:

* **First case** (`:287-297`): `CB(F↾P) = λ+1` for all `P ∈ 𝒫_M`. Choose a finite set
  `D ⊆ 𝒞_{α+2}` of representatives for `{F↾P | P ∈ 𝒫_D}` and pick `h ∈ D` of rank `α+2`;
  then `g := ω D` works: `F ≤ ω D ⊕ ω(pgl ℓ_λ) ≤ ω D` (each `𝒫_M`-piece is `≤ pgl ℓ_λ ≤ h`),
  and `ω D ≤ F⇂U` since each `g' ∈ D` recurs with cocenters accumulating at `y` inside `U`
  (strong solvability clause 2 + `intertwine_reductions_omega_centered`,
  `ScatFun/PreciseStructure/IntertwineOmegaCentered.lean`, fully proved).
* **Second case** (`:301-386`): some `P ∈ 𝒫_M` has `CB(F↾P) > λ+1`. Choose representatives
  `M ⊆ 𝒞_{α+2}` for those pieces, with `g' = pgl M_{g'}` for each `g' ∈ M`; each
  `F↾A_{g'}` (`A_{g'}` = union of the `𝒫_M`-pieces `≡ g'`) is *pseudo-centered*, so the
  **Vertical Theorem** (`verticalTheorem`, `PseudoCentered.lean` — fully proved) yields
  `H_{g'}`, a clopen `W_{g'}` avoiding `y`, and a splitting
  `A_{g'} = A⁰_{g'} ⊔ A¹_{g'}`. Set `w = gl_{g' ∈ M} ω H_{g'}` and `D` = representatives of
  `{F↾P | P ∈ 𝒫_D}`. Then `F ≤ w ⊕ ⋀((M_{g'})_{g' ∈ M} ∣ D) ≤ F⇂U`:
  - *right reduction* (`:321-346`) via the **Disjointification Lemma**
    (`ScatFun.wedge_lower_bound`, `ScatFun/Wedge/LowerBound.lean`, **fully proved**), its two
    premises supplied by center-invariance (`Centerinvariance`, Fact 4.2) and cocenter
    rigidity (Prop 4.4, `rigidityOfCocenter_*`, `CenteredFunctions/Theorems.lean`, proved),
    plus strong solvability clause 2 for the diagonal input;
  - *left reduction* (`:349-386`) via the **wedge upper bound**
    (`ScatFun.wedge_upper_bound`, `ScatFun/Wedge/UpperBound.lean`, **fully proved**): the
    vertical columns are the `A¹_{g'}` (rays reducible by pieces to `M_{g'}` by rigidity;
    a possible rank-`λ+1` residue `A¹_0` is absorbed into some column, `:355-359`), and the
    diagonal is the `𝒫_D`-part cut along rays of `y` (`A^D_n` construction, `:364-385`),
    each `F↾A^D_n ≤ FinGl D` via the Vertical Theorem again (case `n > 0`) or the residual
    corestriction of a centered function (case `n = 0`, memoir `ResidualCorestrictionOfCentered`
    — Lean counterpart in `CenteredFunctions/Theorems.lean`'s rigidity section).

## Formalization notes

* The representative-selection steps ("choose `D ⊆ 𝒞_{α+2}` for `{F↾P | ...}` by
  `FGconsequences`") rest on `ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc`
  (`PseudoCentered.lean`, **proved**, its `G`-decomposition relaxed to `𝒞_{α+1} ∪ ω{𝒞_{α+1}}`) via
  the wrapper `centered_equiv_mem_Centered_le_doubleSucc`, and are carried out for the second case
  by the proved `diagonalTheorem_secondCase_representatives_{M,D}` above.
* Membership `w ⊕ ⋀(... ∣ D) ∈ FinGl 𝒢_{α+2}` comes from the `genStep` wedge and `ω`-image
  clauses (`ScatFun/Generators/Defs.lean`) — the same bookkeeping as
  `wedgeGenerator_centered_witness` (`ScatFun/Generators/Basics.lean`, proved).
* Only the *existence* of `g` uniform in `U` matters downstream
  (`finiteGenerationForSolvable`, `Partitions/Solvable.lean`): quantifier order is
  `∃ g, F ≤ g ∧ ∀ U, g ≤ F⇂U`, exactly as in the memoir. -/
theorem diagonalTheorem
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → y ∈ U → ScatFun.Reduces g (F.coRestrict U) := by
  by_cases hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1
  · -- First case (`:287-297`): all `𝒫_M`-pieces have rank `λ+1`; take `g = ω D`.
    exact diagonalTheorem_firstCase α hα hFG F hFrank hA hss hcase
  · -- Second case (`:301-386`): some `𝒫_M`-piece has rank `> λ+1`; take `g = w ⊕ ⋀(...∣D)`.
    exact diagonalTheorem_secondCase α hα hFG F hFrank hA hss hcase


end
