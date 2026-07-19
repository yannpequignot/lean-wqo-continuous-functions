import WqoContinuousFunctions.DoubleSuccessor.Diagonal
import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalForLambdaPlusOne
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessorOfLimit
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LambdaPlusOne
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LambdaPlusOne
import WqoContinuousFunctions.ScatFun.PreciseStructure.Strictness

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Formalization of `6_double_successor_memo.tex`, §6.4 — Solvable functions

The definitions are complete and the trivial implication is proved. `solvable_lambdaPlusOne`
is proved by dispatch (`g := F`): the membership half `solvable_lambdaPlusOne_mem` and the
corestriction sandwich `solvable_lambdaPlusOne_reduces_coRestrict` are assembled, with the
`λ = 0` corestriction (`solvable_lambdaPlusOne_reduces_coRestrict_zero`) and all piece-
classification helpers proved; the only remaining leaf is the `λ`-limit corestriction
`solvable_lambdaPlusOne_reduces_coRestrict_limit`, which dispatches to the still-open
`solvable_lambdaPlusOne_reduces_coRestrict_limit_secondCase`. `solvableDecomposition` is proved;
`finiteGenerationForSolvable` remains open (via its block-decomposition sub-lemma). These two open
leaves — the `λ`-limit corestriction and the `finiteGenerationForSolvable` sub-lemma — are the only
remaining gaps in the chapter, scaffolded for aristotle.
The chapter capstone (`FGatdoublesuccessors`) lives in
`ScatFun/LevelsFinitelyGenerated/DoubleSuccessor.lean`, next to its per-case siblings.

## Contents

* `ScatFun.IsCPartition.IsSolvableAt` — memoir Definition (`6_double_successor_memo.tex:393-396`):
  strong solvability minus the finiteness clause.
* `ScatFun.IsCPartition.IsStronglySolvableAt.isSolvableAt` — **proved** (drop clause 1).
* `ScatFun.IsCPartition.piecesOver` / `.domainOver` — the memoir's `𝒫⇂U` and `A^U_𝒫`
  (`6_double_successor_memo.tex:398-399`).
* `solvableDecomposition` — Theorem `SolvableDecomposition` (`:403-410`). **Proved**.
* `solvable_lambdaPlusOne` — Proposition `solvablelambda+1` (`:456-460`), the memoir's
  `S(λ)` for `λ` limit or null (`:438-441`). **Proved** modulo the single leaf
  `solvable_lambdaPlusOne_reduces_coRestrict_limit` (the `λ`-limit corestriction, still open).
* `finiteGenerationForSolvable` — Theorem `FiniteGenerationForSolvable` (`:503-506`), the
  memoir's `S(α+1)`. **Open**.

## Conventions

Same as `Diagonal.lean`: rank `α+2` is spelled `α+1+1`, fineness/solvability are relative to
`α.limitPart` (covering finite `α` with `limitPart = 0`), and `FG(≤α+1)` is
`ScatFun.FGBelow (α+1+1)`.
-/

/-! ## Solvable functions and the corestricted partition (`6_double_successor_memo.tex:389-400`) -/

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- `F` together with a fine `c`-partition `𝒫` (fine relative to `lam`) is **solvable at
`y ∈ Y_𝒫`** (memoir Definition, `6_double_successor_memo.tex:393-396`): every piece with
cocenter `≠ y` reduces, inside any clopen `V ∋ y`, into a piece with cocenter `≠ y` —
i.e. clause 2 of `IsStronglySolvableAt` alone, with the finitely-many-cocenters-outside-`V`
clause dropped.

The memoir quantifies the witness `y` existentially ("solvable *with* `𝒫`"); here `y` is a
parameter, as in `IsStronglySolvableAt`/`IsPseudoCenteredAt`, and consumers carry
`hsolv : hA.IsSolvableAt lam y`. If `F` is solvable at `y` then `Y_𝒫` is `{y}` or infinite
(memoir remark, `:397` — a good candidate first lemma when proofs start here). -/
def IsSolvableAt (hA : F.IsCPartition Part) (lam : Ordinal.{0}) (y : Baire) : Prop :=
  hA.IsFine lam ∧ y ∈ hA.cocenterSet ∧
    ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∀ V : Set Baire, IsClopen V → y ∈ V →
        ∃ (Q : Set ↑F.domain) (hQ : Q ∈ Part), hA.cocenterOf hQ ≠ y ∧ hA.cocenterOf hQ ∈ V ∧
          ScatFun.Reduces (F.restrict P) (F.restrict Q)

/-- Strongly solvable implies solvable (memoir, `6_double_successor_memo.tex:390`: solvability
is obtained "by dropping the first requirement"). -/
lemma IsStronglySolvableAt.isSolvableAt {hA : F.IsCPartition Part}
    {lam : Ordinal.{0}} {y : Baire} (h : hA.IsStronglySolvableAt lam y) :
    hA.IsSolvableAt lam y :=
  ⟨h.1, h.2.1, fun P hP hPy V hV hyV => (h.2.2 V hV hyV).2 P hP hPy⟩

/-- `𝒫⇂U` (memoir, `6_double_successor_memo.tex:399`): the pieces whose cocenter lies in
`U`. -/
def piecesOver (hA : F.IsCPartition Part) (U : Set Baire) : Set (Set ↑F.domain) :=
  {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ∈ U}

/-- `A^U_𝒫` (memoir, `6_double_successor_memo.tex:399`): the union of the pieces whose
cocenter lies in `U`. Clopen whenever `Part` is a `c`-partition (both it and its complement
are unions of clopen pieces) — a good candidate first lemma when proofs start here. -/
def domainOver (hA : F.IsCPartition Part) (U : Set Baire) : Set ↑F.domain :=
  ⋃₀ hA.piecesOver U

/-- `A^U_𝒫 = domainOver U` is clopen: it and its complement are each a union of (clopen)
pieces of `𝒫` (those whose cocenter lies in, resp. outside, `U`). -/
lemma domainOver_isClopen (hA : F.IsCPartition Part) (U : Set Baire) :
    IsClopen (hA.domainOver U) := by
  have h_open : IsOpen (hA.domainOver U) :=
    isOpen_sUnion fun P hP => (hA.isClopen P hP.choose).isOpen
  have hcompl : (hA.domainOver U)ᶜ =
      ⋃₀ {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ∉ U} := by
    ext x
    simp only [domainOver, piecesOver, Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq,
      not_exists]
    constructor
    · intro h
      obtain ⟨P, hP, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
        Set.mem_sUnion.mp (hA.sUnion_eq.symm ▸ Set.mem_univ x)
      exact ⟨P, ⟨hP, fun hc => h P ⟨⟨hP, hc⟩, hxP⟩⟩, hxP⟩
    · rintro ⟨P, ⟨hP, hPU⟩, hxP⟩ Q ⟨⟨hQmem, hQU⟩, hxQ⟩
      rcases eq_or_ne P Q with rfl | hne
      · exact hPU hQU
      · exact Set.disjoint_left.mp (hA.pairwiseDisjoint hP hQmem hne) hxP hxQ
  have h_closed : IsClosed (hA.domainOver U) := by
    rw [← compl_compl (hA.domainOver U), hcompl]
    exact (isOpen_sUnion fun P hP => (hA.isClopen P hP.choose).isOpen).isClosed_compl
  exact ⟨h_closed, h_open⟩

end ScatFun.IsCPartition

/-! ## The solvable decomposition (`6_double_successor_memo.tex:403-424`) -/

/-- **Sub-lemma A of the local observation** — the `Dₙ`-eventually-constant combinatorial core
(`6_double_successor_memo.tex:414-418`). Along a clopen neighbourhood basis `(Uₙ)` at `y`, the
sets `Dₙ = {g ∈ 𝒞_{α+2} | ∃ P ∈ 𝒫^{≠y}, y_P ∈ Uₙ, F↾P ≡ g}` are decreasing subsets of the finite
reference set `𝒞_{α+2}` (matching each `F↾P` to a member of `𝒞_{α+2}` uses `FG(<α+2)` via
`exists_pglFinset_decomp_of_centered_doubleSucc`), hence eventually constant `D_M`; take
`U := U_M ∩ W`. Then every off-`y` piece class recurring in `U` recurs in *every* clopen
`V ∋ y`: given `P` with `y_P ∈ U`, `y_P ≠ y`, and clopen `V ∋ y`, the class `[F↾P] ∈ D_M`, and
choosing `n ≥ M` with `Uₙ ⊆ U ∩ V` and `D_n = D_M` produces `Q ∈ 𝒫^{≠y}` with `y_Q ∈ Uₙ ⊆ U ∩ V`
and `F↾P ≡ F↾Q` (hence `F↾P ≤ F↾Q`). This is the sole analytic content of the observation; the
remaining transport to `𝒫⇂U` is `solvableDecomposition_transport`.

**Fully proved.** The clopen neighbourhood basis is `Uₙ = nbhd y n ∩ W` (`baire_nbhd_isClopen`,
`nbhd_basis`, both antitone in `n`); `Dₙ` is a genuine `Finset` — the subset of `𝒞_{α+2}`
of classes represented by an off-`y` piece with cocenter in `Uₙ` — hence its cardinality is an
antitone `ℕ → ℕ`, so it stabilises at `M := argmin` (`Nat.sInf_mem` on the range of cards, then
`Finset.eq_of_subset_of_card_le`). Matching `F↾P` to a member of `𝒞_{α+2}` uses
`centered_equiv_mem_Centered_le_doubleSucc` (needs `λ < CB(F↾P) ≤ α+2`, from fineness and
`restrict_le_self`). -/
theorem solvableDecomposition_stableNbhd
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    (y : Baire) (_hy : y ∈ hA.cocenterSet)
    (W : Set Baire) (hWcl : IsClopen W) (hyW : y ∈ W) :
    ∃ U : Set Baire, IsClopen U ∧ y ∈ U ∧ U ⊆ W ∧
      ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ∈ U → hA.cocenterOf hP ≠ y →
        ∀ V : Set Baire, IsClopen V → y ∈ V →
          ∃ (Q : Set ↑F.domain) (hQ : Q ∈ Part), hA.cocenterOf hQ ≠ y ∧
            hA.cocenterOf hQ ∈ U ∧ hA.cocenterOf hQ ∈ V ∧
            ScatFun.Reduces (F.restrict P) (F.restrict Q) := by
  classical
  -- Clopen neighbourhood basis at `y`, all inside `W`, antitone in `n`.
  set U : ℕ → Set Baire := fun n => nbhd y n ∩ W with hUdef
  have hUcl : ∀ n, IsClopen (U n) := fun n => (baire_nbhd_isClopen y n).inter hWcl
  have hyU : ∀ n, y ∈ U n := fun n => ⟨fun i _ => rfl, hyW⟩
  have hUanti : ∀ {m n : ℕ}, m ≤ n → U n ⊆ U m := by
    intro m n hmn z hz
    exact ⟨fun i hi => hz.1 i
      (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn)), hz.2⟩
  -- `Dₙ` : the classes of `𝒞_{α+2}` represented by an off-`y` piece with cocenter in `Uₙ`.
  set D : ℕ → Finset ScatFun := fun n =>
    (ScatFun.Centered (α + 1 + 1)).filter
      (fun g => ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ∈ U n ∧ hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    with hDdef
  -- Decreasing: `Uₙ ⊆ U_m` for `m ≤ n` shrinks the witness set.
  have hDanti : ∀ {m n : ℕ}, m ≤ n → D n ⊆ D m := by
    intro m n hmn g hg
    rw [hDdef, Finset.mem_filter] at hg ⊢
    obtain ⟨hgC, P, hP, hcoc, hne, heq⟩ := hg
    exact ⟨hgC, P, hP, hUanti hmn hcoc, hne, heq⟩
  -- The card sequence is antitone, so `D` stabilises from some `M`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n : ℕ, M ≤ n → D n = D M := by
    set c : ℕ → ℕ := fun n => (D n).card with hc
    have hmem : sInf (Set.range c) ∈ Set.range c := Nat.sInf_mem ⟨c 0, 0, rfl⟩
    obtain ⟨M, hMc⟩ := hmem
    refine ⟨M, fun n hn => Finset.eq_of_subset_of_card_le (hDanti hn) ?_⟩
    have hle : sInf (Set.range c) ≤ c n := Nat.sInf_le ⟨n, rfl⟩
    rw [← hMc] at hle
    exact hle
  -- Take `U := U M`.
  refine ⟨U M, hUcl M, hyU M, Set.inter_subset_right, ?_⟩
  intro P hP hPU hPne V hVcl hyV
  -- `F↾P` is centered of rank in `(λ, α+2]`, so it is `≡` to some `g ∈ 𝒞_{α+2}`.
  have hcent : IsCentered (F.restrict P).func := hA.centered P hP
  have hlb : α.limitPart < CBRank (F.restrict P).func := hfine.2 P hP
  have hub : CBRank (F.restrict P).func ≤ α + 1 + 1 := by
    rw [← hFrank]
    exact ContinuouslyReduces.rank_monotone (F.restrict P).hScat F.hScat (restrict_le_self F P)
  obtain ⟨g, hgmem, hgeq⟩ :=
    centered_equiv_mem_Centered_le_doubleSucc α hα hFG (F.restrict P) hlb hub hcent
  -- Hence `g ∈ D M` (witnessed by `P` itself).
  have hgDM : g ∈ D M := by
    rw [hDdef, Finset.mem_filter]
    exact ⟨hgmem, P, hP, hPU, hPne, hgeq⟩
  -- Choose `n ≥ M+1` with `U n ⊆ V`, using the neighbourhood basis at `y`.
  obtain ⟨N, hN⟩ := nbhd_basis y V hVcl.isOpen hyV
  set n := max (M + 1) N with hn_def
  have hnM : M ≤ n := le_trans (Nat.le_succ M) (le_max_left _ _)
  have hUnV : U n ⊆ V := fun z hz => hN (fun i hi =>
    hz.1 i (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le (le_max_right _ _))))
  -- `g ∈ D n = D M`, so unpack a `Q` with cocenter in `U n ⊆ U M ∩ V`, off `y`, `F↾Q ≡ g`.
  rw [← hM n hnM, hDdef, Finset.mem_filter] at hgDM
  obtain ⟨_, Q, hQ, hcocQ, hQne, hgeqQ⟩ := hgDM
  refine ⟨Q, hQ, hQne, hUanti hnM hcocQ, hUnV hcocQ, ?_⟩
  exact hgeq.1.trans hgeqQ.2

/-- **`𝒲`-regularity transports down restrict-of-restrict re-realizations.** If `A0 ⊆ D`,
the doubly-restricted `(F↾D)↾{w | w ∈ A0}` is `𝒲`-regular at `z` whenever `F↾A0` is: the two
functions differ only by the domain re-realization homeomorphism of
`ScatFun.restrict_restrict_domain_eq`, so they have the same `CB`-rank
(`CBRank_comp_homeomorph`, hence the same reference set `𝒲`) and `Equiv`-alent rays
(`rayOn_restrict_equiv` on both sides, glued through `restrict_restrict_equiv` at
`A0 ∩ ray-preimage`), so the qualifying ray-index sets coincide. Companion to
`cocenter_restrict_restrict_eq` (`Diagonal/SecondCase/BlockData.lean`); kept here (a leaf
file) rather than in `Fine.lean` to avoid touching a widely-imported hub. -/
lemma ScatFun.isOmegaRegularAt_restrict_restrict (F : ScatFun) (D A0 : Set ↑F.domain)
    (hA0D : A0 ⊆ D) (z : Baire)
    (h : IsOmegaRegularAt (F.restrict A0) z) :
    IsOmegaRegularAt ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}) z := by
  set S' : Set ↑(F.restrict D).domain :=
    {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0} with hS'def
  set G : ScatFun := (F.restrict D).restrict S' with hGdef
  -- Same `CB`-rank (the two funcs agree across the re-realization homeomorphism).
  have hrank : CBRank G.func = CBRank (F.restrict A0).func := by
    rw [hGdef, ScatFun.restrict_restrict_func_eq F D A0 hA0D]
    exact CBRank_comp_homeomorph _ _
  -- `Equiv`-alent rays.
  have hray : ∀ j : ℕ, ScatFun.Equiv (G.rayOn z Set.univ j)
      ((F.restrict A0).rayOn z Set.univ j) := by
    intro j
    -- `G.ray_j ≡ (F↾D).rayOn z S' j` (ray of a restriction).
    have h1 := ScatFun.rayOn_restrict_equiv (F.restrict D) S' z j
    -- `(F↾D).rayOn z S' j ≡ F.rayOn z A0 j` (its defining set is the transported
    -- `A0 ∩ ray-preimage`, so `restrict_restrict_equiv` applies).
    have h2 : ScatFun.Equiv ((F.restrict D).rayOn z S' j) (F.rayOn z A0 j) := by
      have hset : S' ∩ {a : ↑(F.restrict D).domain |
            (F.restrict D).func a ∈ RaySet Set.univ z j}
          = {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain)
              ∈ A0 ∩ {a : ↑F.domain | F.func a ∈ RaySet Set.univ z j}} := rfl
      show ScatFun.Equiv ((F.restrict D).restrict (S' ∩ {a : ↑(F.restrict D).domain |
        (F.restrict D).func a ∈ RaySet Set.univ z j})) (F.rayOn z A0 j)
      rw [hset]
      exact ScatFun.restrict_restrict_equiv F D _ (Set.inter_subset_left.trans hA0D)
    -- `(F↾A0).ray_j ≡ F.rayOn z A0 j` (ray of a restriction again).
    have h3 := ScatFun.rayOn_restrict_equiv F A0 z j
    exact (h1.trans h2).trans h3.symm
  -- Transport the reference-set membership across the rank equality; the qualifying
  -- ray-index sets are then literally equal.
  intro w hw
  have hsets : omegaRegularSet (CBRank G.func) (CBRank_lt_omega1 G.hScat)
      = omegaRegularSet (CBRank (F.restrict A0).func)
          (CBRank_lt_omega1 (F.restrict A0).hScat) := by
    generalize_proofs h1 h2
    revert h1
    rw [hrank]
    intro h1
    rfl
  rw [hsets] at hw
  have hJ : {j : ℕ | ScatFun.Reduces w (G.rayOn z Set.univ j)}
      = {j : ℕ | ScatFun.Reduces w ((F.restrict A0).rayOn z Set.univ j)} := by
    ext j
    exact ⟨fun hr => hr.trans (hray j).1, fun hr => hr.trans (hray j).2⟩
  rw [hJ]
  exact h w hw

/-- **Sub-lemma B of the local observation** — the partition transport (`:400`, `:418`). Given a
clopen `U ∋ y` on which the off-`y` piece classes recur (the `hrec` hypothesis, produced by
`solvableDecomposition_stableNbhd`), transport `𝒫⇂U` to a genuine `c`-partition `Part'` of the
block `F↾A^U_𝒫 = F.restrict (hA.domainOver U)` and package the recurrence as solvability at `y`.

Concretely: pieces of `Part'` are the (`restrictEquiv`-transported) pieces `P ∈ 𝒫` with
`y_P ∈ U` (`cPartition_restrict_transport` from `Fine.lean`); `Part'` inherits fineness from
`hfine` (the memoir's remark `:400`, "any `𝒫⇂U`-lump is a `𝒫`-lump"), its cocenters equal the
transported `y_P ∈ U` (so `cocenterSet ⊆ U`), `y` is among them (the `𝒫`-piece with cocenter
`y` lies over `U` since `y ∈ U`), and `hrec` transports to the recurrence clause of
`IsSolvableAt`. Independent of the `CB`-rank of `F` and of `FG` — pure partition plumbing.

**Fully proved**, mirroring `block_induced_isCPartition` (`Diagonal/SecondCase/BlockData.lean`)
with `piecesOver U` in place of `blockPieces g y`: the five `c`-partition clauses transport
through the re-realization homeomorphism, cocenters via `cocenter_restrict_restrict_eq`,
ranks via `cbRank_eq_of_equiv` + `restrict_restrict_equiv`, and the no-lumps clause via the
`(g, z)`-block correspondence (every ambient block piece has cocenter `z ∈ U`, so the two
blocks re-realize each other) + the new `isOmegaRegularAt_restrict_restrict`. -/
theorem solvableDecomposition_transport
    (lam : Ordinal.{0})
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine lam)
    (y : Baire) (hy : y ∈ hA.cocenterSet)
    (U : Set Baire) (_hUcl : IsClopen U) (hyU : y ∈ U)
    (hrec : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ∈ U → hA.cocenterOf hP ≠ y →
        ∀ V : Set Baire, IsClopen V → y ∈ V →
          ∃ (Q : Set ↑F.domain) (hQ : Q ∈ Part), hA.cocenterOf hQ ≠ y ∧
            hA.cocenterOf hQ ∈ U ∧ hA.cocenterOf hQ ∈ V ∧
            ScatFun.Reduces (F.restrict P) (F.restrict Q)) :
    ∃ (Part' : Set (Set ↑(F.restrict (hA.domainOver U)).domain))
      (hA' : (F.restrict (hA.domainOver U)).IsCPartition Part'),
        hA'.cocenterSet ⊆ U ∧ hA'.IsSolvableAt lam y := by
  classical
  set A : Set ↑F.domain := hA.domainOver U with hAdef
  have hAeq : A = ⋃₀ hA.piecesOver U := rfl
  -- The transport map: pull an ambient piece back through the re-realization homeomorphism.
  set S : Set ↑F.domain → Set ↑(F.restrict A).domain :=
    fun P => {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ P} with hSdef
  set Part' : Set (Set ↑(F.restrict A).domain) := S '' hA.piecesOver U with hPart'def
  have hsubA : ∀ P ∈ hA.piecesOver U, P ⊆ A := fun P hP => by
    rw [hAeq]; exact Set.subset_sUnion_of_mem hP
  -- Each transported piece re-realizes the original one.
  have hequiv : ∀ P ∈ hA.piecesOver U,
      ScatFun.Equiv ((F.restrict A).restrict (S P)) (F.restrict P) := fun P hP =>
    ScatFun.restrict_restrict_equiv F A P (hsubA P hP)
  -- `Part'` is a `c`-partition of the block (mirror of `block_induced_isCPartition`).
  have hA' : (F.restrict A).IsCPartition Part' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (hA.countable.mono (fun P hP => hP.choose)).image S
    · rintro _ ⟨P, hP, rfl⟩
      exact (hA.isClopen P hP.choose).preimage
        (continuous_subtype_val.comp (F.restrictEquiv A).continuous)
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      have hPQ : P ≠ Q := fun h => hne (by rw [h])
      have hdisj := hA.pairwiseDisjoint hP.choose hQ.choose hPQ
      simp only [Function.onFun, id] at hdisj ⊢
      rw [Set.disjoint_left] at hdisj ⊢
      intro w hwP hwQ
      exact hdisj hwP hwQ
    · ext w
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      have hwA : (F.restrictEquiv A w : ↑F.domain) ∈ ⋃₀ hA.piecesOver U :=
        (F.restrictEquiv A w).2
      obtain ⟨P, hP, hwP⟩ := hwA
      exact ⟨S P, ⟨P, hP, rfl⟩, hwP⟩
    · rintro _ ⟨P, hP, rfl⟩
      exact isCentered_of_equiv (hA.centered P hP.choose) (hequiv P hP)
  -- Cocenters transport (`cocenter_restrict_restrict_eq`).
  have hcoc : ∀ (P : Set ↑F.domain) (hPU : P ∈ hA.piecesOver U) (h' : S P ∈ Part'),
      hA'.cocenterOf h' = hA.cocenterOf hPU.choose := fun P hPU h' =>
    ScatFun.cocenter_restrict_restrict_eq F A P (hsubA P hPU) _ _
  -- All transported cocenters lie in `U`.
  have hcocsub : hA'.cocenterSet ⊆ U := by
    rintro z ⟨⟨P', hP'⟩, hP'coc⟩
    have hP'coc' : hA'.cocenterOf hP' = z := hP'coc
    obtain ⟨P, hPU, hSP⟩ := id hP'
    subst hSP
    rw [hcoc P hPU hP'] at hP'coc'
    rw [← hP'coc']
    exact hPU.choose_spec
  -- `y` is a cocenter of the transported partition.
  obtain ⟨⟨P₀, hP₀⟩, hP₀y⟩ := hy
  have hP₀y' : hA.cocenterOf hP₀ = y := hP₀y
  have hP₀U : P₀ ∈ hA.piecesOver U := ⟨hP₀, by
    show hA.cocenterOf hP₀ ∈ U
    rw [hP₀y']; exact hyU⟩
  have hymem : y ∈ hA'.cocenterSet := by
    refine ⟨⟨S P₀, Set.mem_image_of_mem S hP₀U⟩, ?_⟩
    show hA'.cocenterOf (Set.mem_image_of_mem S hP₀U) = y
    rw [hcoc P₀ hP₀U _]
    exact hP₀y'
  -- Fineness transports: ranks via the piece `Equiv`s, and any `𝒫⇂U`-lump is a `𝒫`-lump
  -- (memoir remark `:400`) since the two `(g, z)`-blocks re-realize each other.
  have hfine' : hA'.IsFine lam := by
    constructor
    · -- No lumps.
      rintro g z ⟨hz, hgcent, hirr⟩
      have hzU : z ∈ U := hcocsub hz
      -- `z` is an ambient cocenter.
      have hzamb : z ∈ hA.cocenterSet := by
        obtain ⟨⟨P', hP'⟩, hP'coc⟩ := hz
        have hP'coc' : hA'.cocenterOf hP' = z := hP'coc
        obtain ⟨P, hPU, hSP⟩ := id hP'
        subst hSP
        rw [hcoc P hPU hP'] at hP'coc'
        exact ⟨⟨P, hPU.choose⟩, hP'coc'⟩
      -- The ambient `(g, z)`-block is `𝒲`-regular (no `𝒫`-lump).
      have hreg : IsOmegaRegularAt (hA.piece g z) z := by
        by_contra hnreg
        exact hfine.1 g z ⟨hzamb, hgcent, hnreg⟩
      -- The two blocks re-realize each other.
      have hBA : ⋃₀ hA.blockPieces g z ⊆ A := by
        rintro x ⟨P, hPblock, hxP⟩
        refine hsubA P ⟨hPblock.choose, ?_⟩ hxP
        rw [hPblock.choose_spec.2]; exact hzU
      have hblocks : ⋃₀ hA'.blockPieces g z
          = {w : ↑(F.restrict A).domain |
              (F.restrictEquiv A w : ↑F.domain) ∈ ⋃₀ hA.blockPieces g z} := by
        ext w
        constructor
        · rintro ⟨P', hP'block, hwP'⟩
          obtain ⟨hP'mem, hP'eq, hP'coc⟩ := hP'block
          obtain ⟨P, hPU, hSP⟩ := id hP'mem
          subst hSP
          rw [hcoc P hPU hP'mem] at hP'coc
          exact ⟨P, ⟨hPU.choose, (hequiv P hPU).symm.trans hP'eq, hP'coc⟩, hwP'⟩
        · rintro ⟨P, hPblock, hwP⟩
          obtain ⟨hPmem, hPg, hPcoc⟩ := hPblock
          have hPU : P ∈ hA.piecesOver U := ⟨hPmem, by rw [hPcoc]; exact hzU⟩
          have hSPmem : S P ∈ Part' := Set.mem_image_of_mem S hPU
          refine ⟨S P, ⟨hSPmem, (hequiv P hPU).trans hPg, ?_⟩, hwP⟩
          rw [hcoc P hPU hSPmem]
          exact hPcoc
      -- Transport `𝒲`-regularity and contradict the lump.
      apply hirr
      show IsOmegaRegularAt ((F.restrict A).restrict (⋃₀ hA'.blockPieces g z)) z
      rw [hblocks]
      exact ScatFun.isOmegaRegularAt_restrict_restrict F A (⋃₀ hA.blockPieces g z) hBA z hreg
    · -- Ranks.
      rintro _ ⟨P, hP, rfl⟩
      rw [cbRank_eq_of_equiv (hequiv P hP)]
      exact hfine.2 P hP.choose
  -- The recurrence clause of solvability, transported from `hrec`.
  have hrecur : ∀ (P' : Set ↑(F.restrict A).domain) (hP' : P' ∈ Part'),
      hA'.cocenterOf hP' ≠ y → ∀ V : Set Baire, IsClopen V → y ∈ V →
        ∃ (Q' : Set ↑(F.restrict A).domain) (hQ' : Q' ∈ Part'),
          hA'.cocenterOf hQ' ≠ y ∧ hA'.cocenterOf hQ' ∈ V ∧
          ScatFun.Reduces ((F.restrict A).restrict P') ((F.restrict A).restrict Q') := by
    intro P' hP' hne V hVcl hyV
    obtain ⟨P, hPU, hSP⟩ := id hP'
    subst hSP
    rw [hcoc P hPU hP'] at hne
    obtain ⟨Q, hQ, hQne, hQU, hQV, hred⟩ :=
      hrec P hPU.choose hPU.choose_spec hne V hVcl hyV
    have hQU' : Q ∈ hA.piecesOver U := ⟨hQ, hQU⟩
    have hSQmem : S Q ∈ Part' := Set.mem_image_of_mem S hQU'
    refine ⟨S Q, hSQmem, ?_, ?_, ?_⟩
    · rw [hcoc Q hQU' hSQmem]; exact hQne
    · rw [hcoc Q hQU' hSQmem]; exact hQV
    · exact ((hequiv P hPU).1.trans hred).trans (hequiv Q hQU').2
  exact ⟨Part', hA', hcocsub, hfine', hymem, hrecur⟩

/-- **Local observation** (`6_double_successor_memo.tex:412-418`), the analytic core of
`solvableDecomposition`. For each cocenter `y` and each clopen neighbourhood `W ∋ y`, there is
a *smaller* clopen neighbourhood `U ⊆ W` of `y` making the block `F↾A^U_𝒫` (with its
transported sub-partition `𝒫⇂U`) solvable at `y`, all of whose cocenters lie in `U`.

The `U ⊆ W` clause is what lets the caller (`solvableDecomposition`) shrink each chosen
neighbourhood into the complement of the previously chosen ones, achieving disjointness.

*Proof idea (memoir).* Along a clopen neighbourhood basis `(U_n)` at `y`, the sets
`D_n = {g ∈ 𝒞_{α+2} | ∃ P, y_P ∈ U_n, F↾P ≡ g}` are decreasing subsets of the finite reference
set, hence eventually constant `D_M`; `U := U_M ∩ W` then makes every piece-class recurring in
`U` recur in every smaller clopen `V ∋ y`, which is exactly solvability at `y`. Matching each
`F↾P` to the finite reference set uses `FG(<α+2)` via
`exists_pglFinset_decomp_of_centered_doubleSucc`. -/
theorem solvableDecomposition_localObservation
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    (y : Baire) (hy : y ∈ hA.cocenterSet)
    (W : Set Baire) (hWcl : IsClopen W) (hyW : y ∈ W) :
    ∃ U : Set Baire, IsClopen U ∧ y ∈ U ∧ U ⊆ W ∧
      ∃ (Part' : Set (Set ↑(F.restrict (hA.domainOver U)).domain))
        (hA' : (F.restrict (hA.domainOver U)).IsCPartition Part'),
          hA'.cocenterSet ⊆ U ∧ hA'.IsSolvableAt α.limitPart y := by
  -- Sub-lemma A: the `Dₙ`-eventually-constant stable neighbourhood `U ⊆ W`.
  obtain ⟨U, hUcl, hyU, hUW, hrec⟩ :=
    solvableDecomposition_stableNbhd α hα hFG F hFrank hA hfine y hy W hWcl hyW
  -- Sub-lemma B: transport `𝒫⇂U` and package the recurrence as solvability at `y`.
  obtain ⟨Part', hA', hsub, hsolv⟩ :=
    solvableDecomposition_transport α.limitPart F hA hfine y hy U hUcl hyU hrec
  exact ⟨U, hUcl, hyU, hUW, Part', hA', hsub, hsolv⟩

/-- **Theorem `SolvableDecomposition`** (`6_double_successor_memo.tex:403-410`). Let `α < ω₁`,
assume `FG(<α+2)`, and let `Part` be a fine `c`-partition of `F : ScatFun` with
`CB(F) = α+2`. Then there is a countable family `𝒰` of pairwise disjoint clopen subsets of
the codomain such that `Y_𝒫 ⊆ ⋃₀ 𝒰` and, for every `U ∈ 𝒰`, the block `F↾A^U_𝒫` together
with the corestricted partition `𝒫⇂U` is solvable (at some `y`, with all its cocenters in
`U`).

## Provided solution (`6_double_successor_memo.tex:411-424`)

*Local observation* (`:412-418`): for each `y ∈ Y_𝒫`, along a clopen neighbourhood basis
`(U_n)` at `y` the sets `D_n = {g ∈ 𝒞_{α+2} | ∃ P ∈ 𝒫^{≠y}, y_P ∈ U_n, F↾P ≡ g}` are
decreasing, hence (finiteness of `𝒞_{α+2}`) eventually constant, `D_M = D_n` for `n ≥ M`;
`U = U_M` then makes `F↾A^U_𝒫` solvable at `y` with `𝒫⇂U`: any piece class recurring in
`U` recurs in every smaller `U_n ⊆ V`. (Matching each `F↾P` against the finite `𝒞_{α+2}`
uses `FG(<α+2)` via `centered_equiv_mem_Centered_le_doubleSucc`, itself resting on the
proved `ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc`, `PseudoCentered.lean`.)
This whole local observation is now proved (`solvableDecomposition_stableNbhd` +
`solvableDecomposition_transport`), so `solvableDecomposition` is fully proved.

*Greedy disjointification* (`:420-424`): enumerate `Y_𝒫 = (y_n)`; inductively pick, for the
least `y_n` not yet covered, a solvability neighbourhood `U_k ∋ y_n` (by the observation)
disjoint from the previously chosen (clopen, finitely many so far) `U_l`, `l < k`.

## Formalization notes

* The conclusion exhibits the transported partition on `F.restrict (hA.domainOver U)`
  abstractly (`∃ Part' hA' y`) rather than constructing `𝒫⇂U`'s transport in the statement;
  the transport itself is `cPartition_restrict_transport` (`Fine.lean`), and fineness of the
  sub-partition is the memoir's remark `:400` ("any `𝒫⇂U`-lump is a `𝒫`-lump").
* The clause `hA'.cocenterSet ⊆ U` is what lets the capstone corestrict each block to its
  own `U` when applying `solvable_lambdaPlusOne` / `finiteGenerationForSolvable`.
* No rank hypothesis is placed on the blocks: `CB(F↾A^U_𝒫)` can be anything in
  `[λ+1, α+2]`; the capstone dispatches on it. -/
theorem solvableDecomposition
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart) :
    ∃ 𝒰 : Set (Set Baire), 𝒰.Countable ∧ (∀ U ∈ 𝒰, IsClopen U) ∧
      𝒰.PairwiseDisjoint id ∧ hA.cocenterSet ⊆ ⋃₀ 𝒰 ∧
      ∀ U ∈ 𝒰, ∃ (Part' : Set (Set ↑(F.restrict (hA.domainOver U)).domain))
        (hA' : (F.restrict (hA.domainOver U)).IsCPartition Part') (y : Baire),
          hA'.cocenterSet ⊆ U ∧ hA'.IsSolvableAt α.limitPart y := by
  classical
  -- The per-`U` solvability datum we must attach to each chosen neighbourhood.
  set SolvData : Set Baire → Prop := fun U =>
    ∃ (Part' : Set (Set ↑(F.restrict (hA.domainOver U)).domain))
      (hA' : (F.restrict (hA.domainOver U)).IsCPartition Part') (z : Baire),
        hA'.cocenterSet ⊆ U ∧ hA'.IsSolvableAt α.limitPart z with hSolvData
  -- The cocenter set is countable.
  have : Countable ↥Part := hA.countable.to_subtype
  have hcoc_ct : hA.cocenterSet.Countable := Set.countable_range _
  -- Dispatch on whether there are any cocenters at all.
  rcases eq_empty_or_nonempty hA.cocenterSet with hempty | hne
  · exact ⟨∅, Set.countable_empty, by simp, by simp,
      by rw [hempty]; exact Set.empty_subset _, by simp⟩
  -- Enumerate the cocenters, `hA.cocenterSet = range e`.
  obtain ⟨e, he⟩ := hcoc_ct.exists_eq_range hne
  have hein : ∀ n, e n ∈ hA.cocenterSet := fun n => he ▸ Set.mem_range_self n
  -- The local observation, as a total choice function via `choose!`.
  have hLO : ∀ z W, z ∈ hA.cocenterSet → IsClopen W → z ∈ W →
      ∃ U : Set Baire, IsClopen U ∧ z ∈ U ∧ U ⊆ W ∧ SolvData U := by
    intro z W hz hWcl hzW
    obtain ⟨U, hUcl, hzU, hUW, hdata⟩ :=
      solvableDecomposition_localObservation α hα hFG F hFrank hA hfine z hz W hWcl hzW
    refine ⟨U, hUcl, hzU, hUW, ?_⟩
    rw [hSolvData]
    obtain ⟨Part', hA', hsub, hsolv⟩ := hdata
    exact ⟨Part', hA', z, hsub, hsolv⟩
  choose! Uf hUf_cl hUf_mem hUf_sub hUf_data using hLO
  -- Greedy accumulation: `P n` = the union of the neighbourhoods chosen before step `n`.
  set P : ℕ → Set Baire := fun n =>
    Nat.rec ∅ (fun m Pm => Pm ∪ (if e m ∈ Pm then (∅ : Set Baire) else Uf (e m) Pmᶜ)) n
    with hPdef
  set U : ℕ → Set Baire := fun n => if e n ∈ P n then (∅ : Set Baire) else Uf (e n) (P n)ᶜ
    with hUdef
  have hPsucc : ∀ n, P (n + 1) = P n ∪ U n := fun n => rfl
  have hP0 : P 0 = ∅ := rfl
  -- `P n` and `U n` are clopen.
  have hPcl : ∀ n, IsClopen (P n) := by
    intro n
    induction n with
    | zero => rw [hP0]; exact isClopen_empty
    | succ k ih =>
      rw [hPsucc]
      refine ih.union ?_
      simp only [hUdef]
      split_ifs with hc
      · exact isClopen_empty
      · exact hUf_cl (e k) (P k)ᶜ (hein k) ih.compl hc
  have hUcl : ∀ n, IsClopen (U n) := by
    intro n
    simp only [hUdef]
    split_ifs with hc
    · exact isClopen_empty
    · exact hUf_cl (e n) (P n)ᶜ (hein n) (hPcl n).compl hc
  -- `P n = ⋃_{m < n} U m`.
  have hPunion : ∀ n, P n = ⋃ m ∈ Finset.range n, U m := by
    intro n
    induction n with
    | zero => rw [hP0]; simp
    | succ k ih =>
      rw [hPsucc, ih, Finset.range_add_one]
      simp [Set.union_comm]
  -- Each `U n` is contained in the complement of `P n` (empty case is trivial).
  have hUsub : ∀ n, U n ⊆ (P n)ᶜ := by
    intro n
    simp only [hUdef]
    split_ifs with hc
    · exact Set.empty_subset _
    · exact hUf_sub (e n) (P n)ᶜ (hein n) (hPcl n).compl hc
  -- Pairwise disjointness of the `U n`.
  have hUdisj : Pairwise (Function.onFun Disjoint U) := by
    have key : ∀ m n, m < n → Disjoint (U m) (U n) := by
      intro m n hlt
      have hmP : U m ⊆ P n := by
        rw [hPunion n]
        exact Set.subset_iUnion₂_of_subset m (Finset.mem_range.mpr hlt) le_rfl
      exact disjoint_compl_right.mono hmP (hUsub n)
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact key m n h
    · exact (key n m h).symm
  -- Coverage: every cocenter is in some `U n`.
  have hcover : hA.cocenterSet ⊆ ⋃ n, U n := by
    rw [he]
    rintro _ ⟨j, rfl⟩
    by_cases hc : e j ∈ P j
    · -- Already covered by an earlier neighbourhood.
      rw [hPunion j] at hc
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨hmj, rfl⟩, hmem⟩ := hc
      exact Set.mem_iUnion.mpr ⟨m, hmem⟩
    · -- Covered by `U j` itself.
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rw [hUdef]; simp only [hc, if_false]
      exact hUf_mem (e j) (P j)ᶜ (hein j) (hPcl j).compl hc
  -- Assemble `𝒰 = range U \ {∅}`.
  refine ⟨Set.range U \ {∅}, (Set.countable_range U).mono (Set.diff_subset), ?_, ?_, ?_, ?_⟩
  · rintro V ⟨⟨n, rfl⟩, -⟩; exact hUcl n
  · rintro V ⟨⟨m, rfl⟩, -⟩ V' ⟨⟨n, rfl⟩, -⟩ hne'
    exact hUdisj (fun h => hne' (by rw [h]))
  · refine hcover.trans ?_
    rintro z hz
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_sUnion.mpr ⟨U n, ⟨⟨n, rfl⟩, ?_⟩, hzn⟩
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    rw [hmem] at hzn
    exact Set.notMem_empty z hzn
  · rintro V ⟨⟨n, rfl⟩, hVne⟩
    have hc : e n ∉ P n := by
      by_contra hc
      apply hVne
      simp only [Set.mem_singleton_iff, hUdef, hc, if_true]
    have := hUf_data (e n) (P n)ᶜ (hein n) (hPcl n).compl hc
    rw [hSolvData] at this
    have hUeq : U n = Uf (e n) (P n)ᶜ := by rw [hUdef]; simp only [hc, if_false]
    rw [hUeq]; exact this

/-! ## `S(λ)` at successors of limit-or-null ordinals (`6_double_successor_memo.tex:438-497`) -/

/-- Membership half of `solvable_lambdaPlusOne`: a function of `CB`-rank `λ+1` (`λ` limit or
null) is already a finite gluing of `𝒢_{λ+1}`, because `FG(≤λ)` gives `FG(λ+1)`
(`Generators_lambdaPlusOne_finitely_generates` for `λ` limit, `Generators_one_finitely_generates`
for `λ = 0`). Used with `g := F` in the sandwich. -/
lemma solvable_lambdaPlusOne_mem
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam ∨ lam = 0) (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1) :
    F ∈ ScatFun.FinGl (ScatFun.Generators (lam + 1)).toFinFun := by
  rcases hlim with hlim | h0
  · exact ScatFun.Generators_lambdaPlusOne_finitely_generates lam hlim hlam_lt
      (ScatFun.LevelLT.isTwoBQO_of_FG_below hFG) F hFrank
  · subst h0
    rw [zero_add]
    exact ScatFun.Generators_one_finitely_generates F (by rw [hFrank, zero_add])

/-! **Crux of `solvable_lambdaPlusOne`** (`6_double_successor_memo.tex:462-497`): a solvable
function of `CB`-rank `λ+1` reduces into its own corestriction to any clopen `U ⊇ Y_𝒫`. Since
`F⇂U ≤ F` always, this gives `F ≡ F⇂U`. Together with `solvable_lambdaPlusOne_mem` (which shows
`F ∈ FinGl 𝒢_{λ+1}`) it yields the proposition with `g := F`. This is the mathematical content
of the memoir's case analysis. -/

/-
The trivial reduction `F ≤ F⇂U` when *every* value of `F` lies in `U`: the domain
preimage `{z | F z ∈ U}` is all of `F.domain`, so `F⇂U` is `F` up to the domain
identification.
-/
lemma reduces_coRestrict_of_range_subset (F : ScatFun) {U : Set Baire}
    (hU : ∀ z : ↑F.domain, F.func z ∈ U) :
    ScatFun.Reduces F (F.coRestrict U) := by
  convert ScatFun.reduces_coRestrict_of_subtype F F U _ using 1;
  constructor;
  swap;
  exact fun z => ⟨ z, hU z ⟩;
  exact ⟨ by continuity, fun x => x, continuous_id.continuousOn, fun x => rfl ⟩

/-- Restriction never raises `CB`-rank: `CBRank (F.restrict P).func ≤ CBRank F.func`. -/
lemma piece_cbRank_le (F : ScatFun) (P : Set ↑F.domain) :
    CBRank (F.restrict P).func ≤ CBRank F.func :=
  ContinuouslyReduces.rank_monotone (F.restrict P).hScat F.hScat (restrict_le_self F P)

/-
A **centered, locally constant** function is constant, equal to its cocenter. A center `x`
meets every open neighbourhood with a reduction of the whole function into that neighbourhood;
choosing a neighbourhood on which `g` is constant `= g x` forces the entire range to collapse to
`g x = cocenter g hc`. (General topological form, kept for reuse; the `ScatFun`-level
`func_eq_cocenter_of_centered_locallyConstant` below is the specialization to `g.func`.)
-/
lemma ScatFun.eq_cocenter_of_isCentered_isLocallyConstant
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (g : A → B) (hc : IsCentered g) (hlc : IsLocallyConstant g) (a : A) :
    g a = cocenter g hc := by
  obtain ⟨x, hx⟩ := hc;
  have := hx ( g ⁻¹' { g x } ) ( hlc _ ) ( by simp +decide );
  obtain ⟨ σ, τ, hσ, hτ, h ⟩ := this;
  simp +decide only [h a, comp_apply, cocenter];
  grind

/-
A centered, locally-constant scattered function is constant, and its (unique) value is its
cocenter: `g.func w = cocenter g.func hc` for every `w`. The `ScatFun`-level specialization of
`ScatFun.eq_cocenter_of_isCentered_isLocallyConstant`.
-/
lemma func_eq_cocenter_of_centered_locallyConstant (g : ScatFun)
    (hc : IsCentered g.func) (hlc : IsLocallyConstant g.func) (w : ↑g.domain) :
    g.func w = cocenter g.func hc :=
  ScatFun.eq_cocenter_of_isCentered_isLocallyConstant g.func hc hlc w

/-
**Crux, `λ = 0` case** (`6_double_successor_memo.tex:464-468`). At rank `1` every piece is
constant, so `im F = Y_𝒫 ⊆ U`, hence `F⇂U = F`.
-/
lemma solvable_lambdaPlusOne_reduces_coRestrict_zero
    (F : ScatFun) (hFrank : CBRank F.func = (0 : Ordinal.{0}) + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (_hsolv : hA.IsSolvableAt 0 y)
    (U : Set Baire) (_hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U) :
    ScatFun.Reduces F (F.coRestrict U) := by
  -- Apply the lemma that states if the range of F is contained in U, then F reduces to F.coRestrict U.
  -- (The `λ = 0` case needs neither solvability nor clopen-ness of `U`, only that `U` covers `Y_𝒫`.)
  apply reduces_coRestrict_of_range_subset F;
  intro z
  obtain ⟨P, hP⟩ : ∃ P ∈ Part, z ∈ P := by
    exact Set.mem_sUnion.mp ( hA.sUnion_eq ▸ Set.mem_univ z )
  have h_cocenter : F.func z = hA.cocenterOf hP.left := by
    apply Eq.symm;
    have h_cocenter_eq : (F.restrict P).func (ScatFun.restrictEquiv F P |>.symm ⟨z, hP.2⟩) = F.func z := by
      simp +decide only [coe_setOf, mem_setOf_eq, ScatFun.restrictEquiv, Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk];
      exact List.map_inj.mp rfl
    convert func_eq_cocenter_of_centered_locallyConstant ( F.restrict P ) ( hA.centered P hP.1 ) _ _ using 1;
    · convert h_cocenter_eq.symm using 1;
      exact Eq.symm ( func_eq_cocenter_of_centered_locallyConstant _ ( hA.centered P hP.1 ) ( isLocallyConstant_of_cbRank_le_one _ ( by simpa [ hFrank ] using piece_cbRank_le F P ) ) _ );
    · apply isLocallyConstant_of_cbRank_le_one;
      exact le_trans ( piece_cbRank_le F P ) ( by simp +decide [ hFrank ] )
  exact hUcov (by
  exact h_cocenter.symm ▸ Set.mem_range.mpr ⟨ ⟨ P, hP.1 ⟩, rfl ⟩)

/-- Under fineness relative to `λ`, and `CB(F) = λ+1`, every piece has `CB`-rank exactly `λ+1`:
fineness forces rank `> λ` and `piece_cbRank_le` forces rank `≤ λ+1`, and there is no ordinal
strictly between `λ` and `λ+1`. -/
lemma piece_rank_eq_of_fine
    (lam : Ordinal.{0}) (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    {P : Set ↑F.domain} (hP : P ∈ Part) :
    CBRank (F.restrict P).func = lam + 1 := by
  have hgt : lam < CBRank (F.restrict P).func := hfine.2 P hP
  have hle : CBRank (F.restrict P).func ≤ lam + 1 := hFrank ▸ piece_cbRank_le F P
  rw [Ordinal.add_one_eq_succ] at hle ⊢
  exact le_antisymm hle (Order.succ_le_of_lt hgt)

/-- Piece classification (`6_double_successor_memo.tex:472-473`, from `cor:CenteredSucessor`):
with `λ` a nonzero limit and `𝒫` fine, every piece is `≡ k_{λ+1}` (`minFun λ`) or `≡ pgl ℓ_λ`
(`succMaxFun λ`). -/
lemma piece_equiv_minFun_or_succMaxFun
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    {P : Set ↑F.domain} (hP : P ∈ Part) :
    ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt) ∨
      ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt) :=
  centeredSuccessor lam hlam_lt (Or.inr ⟨hlim, hlam_ne⟩) (F.restrict P)
    (piece_rank_eq_of_fine lam F hFrank hA hfine hP) (hA.centered P hP)

/-- A piece whose cocenter lies in the (open) codomain set `U` reduces into `F⇂U`: the piece is
centered with cocenter in `U`, so it reduces to its own corestriction to `U`
(`reduces_coRestrict_cocenter_nbhd`), which in turn reduces into `F⇂U`
(`coRestrict_restrict_reduces`). Reusable across the limit-case branches. -/
lemma piece_reduces_coRestrict_of_cocenter_mem
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {U : Set Baire} (hUo : IsOpen U)
    {P : Set ↑F.domain} (hP : P ∈ Part) (hyU : hA.cocenterOf hP ∈ U) :
    ScatFun.Reduces (F.restrict P) (F.coRestrict U) :=
  (reduces_coRestrict_cocenter_nbhd (F.restrict P) (hA.centered P hP) hUo hyU).trans
    (ScatFun.coRestrict_restrict_reduces F P U)

/- **Overview of the `λ`-limit crux** (`6_double_successor_memo.tex:470-497`). The full case
analysis of the memoir, split below into `_firstCase`/`_secondCase`. `hsolv.1 : hA.IsFine lam`.
By `piece_equiv_minFun_or_succMaxFun` each piece is
`≡ k_{λ+1}` (`minFun λ`) or `≡ pgl ℓ_λ` (`succMaxFun λ`); dispatch on whether all cocenters
equal `y`.

* **First case** (all cocenters `= y`, `:476-480`): `F` is simple (`cocenters_coincide_implies_simple`),
  so `F ≤ pgl ℓ_λ`; the bound `pgl ℓ_λ ≤ F⇂U` comes from a piece `≡ pgl ℓ_λ`
  (`piece_reduces_coRestrict_of_cocenter_mem`) or, when all pieces are `≡ k_{λ+1}`, from `F ≡ k`
  being centered (low rays) or a rank-`λ` ray inside `U` (high ray, via the General Structure
  Theorem and fineness).
* **Second case** (some cocenter `≠ y`, `:481-496`): `Y_𝒫` infinite; split `𝒫 = 𝒫₀ ⊔ 𝒫₁` by
  piece class and analyse `Y₁` (empty / infinite / singleton `{y}`, the last via
  `diagonal_for_lambda_plus_one`), using `reduces_omega_of_forall_piece_le` and
  `intertwine_reductions_omega_centered`.

Supporting facts already available in this file: `piece_equiv_minFun_or_succMaxFun`,
`piece_rank_eq_of_fine`, `piece_reduces_coRestrict_of_cocenter_mem`,
`reduces_coRestrict_of_range_subset`. -/

/-- **First-case top-level constancy.** If every piece of a `c`-partition of `F` has cocenter
`y`, then `F` is constant equal to `y` on its last nonempty CB-level `CBLevel F.func lam`: each
such point lies in a piece whose restriction is centered of rank `lam+1`, hence equals its
cocenter `= y` there (`cbLevel_block_iff`, `block_const_on_top`). -/
lemma firstCase_top_const
    (lam : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire}
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y) :
    ∀ x ∈ CBLevel F.func lam, F.func x = y := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := hA.sUnion_eq.symm.subset (Set.mem_univ x)
  have hP_open : IsOpen P := (hA.isClopen P hP).isOpen
  set z : ↑(F.restrict P).domain := (F.restrictEquiv P).symm ⟨x, hxP⟩ with hzdef
  have hzx : (F.restrictEquiv P z : ↑F.domain) = x := by rw [hzdef]; simp
  have hzlevel : z ∈ CBLevel (F.restrict P).func lam :=
    (cbLevel_block_iff F P hP_open lam z).mpr (by rw [hzx]; exact hx)
  have hP_rank : CBRank (F.restrict P).func = lam + 1 := by
    have hle : CBRank (F.restrict P).func ≤ lam + 1 := hFrank ▸ piece_cbRank_le F P
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hlam' : CBRank (F.restrict P).func ≤ lam := by
        rw [Ordinal.add_one_eq_succ] at hlt
        exact Order.lt_succ_iff.mp hlt
      have hempty : CBLevel (F.restrict P).func lam = ∅ :=
        Set.subset_eq_empty
          (CBLevel_antitone (F.restrict P).func hlam')
          (cbLevel_at_cbRank_empty (F.restrict P).func (F.restrict P).hScat)
      exact absurd hzlevel (by rw [hempty]; exact Set.notMem_empty z)
    · exact heq
  have hcent : IsCentered (F.restrict P).func := hA.centered P hP
  have hconst : (F.restrict P).func z = cocenter (F.restrict P).func hcent :=
    block_const_on_top (F.restrict P) hcent lam
      (by rw [hP_rank, Ordinal.add_one_eq_succ]) z hzlevel
  rw [← hzx]
  show (F.restrict P).func z = y
  rw [hconst]; exact hcoin P hP

/-- **First-case simplicity** (`6_double_successor_memo.tex:476`, Prop 4.11). If every piece of a
`c`-partition of `F` has cocenter `y` (so `Y_𝒫 = {y}`), then `F` is simple: use `α = lam` in the
definition, with `CBLevel lam` nonempty and `CBLevel (lam+1)` empty from `CB(F) = lam+1`, and
constancy on `CBLevel lam` from `firstCase_top_const`. -/
lemma firstCase_simple
    (lam : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire}
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y) :
    SimpleFun F.func := by
  refine ⟨lam, ?_, ?_, y, firstCase_top_const lam F hFrank hA hcoin⟩
  · exact CBLevel_nonempty_below_rank F.func F.hScat lam (by rw [hFrank]; exact lt_add_one lam)
  · convert cbLevel_at_cbRank_empty F.func F.hScat
    rw [hFrank, Ordinal.add_one_eq_succ]

/-- **First-case cocenter identification.** If `F` is centered and every piece has cocenter `y`,
then the cocenter of `F` is `y` (it is the constant value on the top CB-level, which is `y` by
`firstCase_top_const`). -/
lemma firstCase_cocenter_eq
    (lam : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire}
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y)
    (hc : IsCentered F.func) :
    cocenter F.func hc = y := by
  obtain ⟨x, hx⟩ :=
    CBLevel_nonempty_below_rank F.func F.hScat lam (by rw [hFrank]; exact lt_add_one lam)
  have hb : F.func x = cocenter F.func hc :=
    block_const_on_top F hc lam (by rw [hFrank, Ordinal.add_one_eq_succ]) x hx
  rw [← hb]; exact firstCase_top_const lam F hFrank hA hcoin x hx

/-- **First case — the centered branch.** If `F` is centered (which happens when `F ≡ k_{λ+1}` or
`F ≡ pgl ℓ_λ`), its cocenter is `y ∈ U`, so `F ≤ F⇂U` directly by
`reduces_coRestrict_cocenter_nbhd`. -/
lemma firstCase_centered_reduces
    (lam : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hy : y ∈ hA.cocenterSet)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U)
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y)
    (hc : IsCentered F.func) :
    ScatFun.Reduces F (F.coRestrict U) :=
  reduces_coRestrict_cocenter_nbhd F hc hU.isOpen
    (by rw [firstCase_cocenter_eq lam F hFrank hA hcoin hc]; exact hUcov hy)

/-- **First case — the minimum reduces into every corestriction near `y`.** Since `y ∈ Y_𝒫`,
some piece `P` has cocenter `y`; `F↾P` is centered of rank `lam+1` (fineness), hence simple, so
`k_{λ+1} ≤ F↾P` (`minFun_reduces_simple`); and `F↾P ≤ F⇂V` for clopen `V ∋ y`
(`piece_reduces_coRestrict_of_cocenter_mem`). -/
lemma firstCase_minFun_coRestrict
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    {y : Baire} (hy : y ∈ hA.cocenterSet)
    (V : Set Baire) (hVcl : IsClopen V) (hyV : y ∈ V) :
    ScatFun.Reduces (ScatFun.minFun lam hlam_lt) (F.coRestrict V) := by
  obtain ⟨p, hp⟩ := hy
  have hP : p.1 ∈ Part := p.2
  have hp' : hA.cocenterOf hP = y := hp
  have hrank : CBRank (F.restrict p.1).func = lam + 1 :=
    piece_rank_eq_of_fine lam F hFrank hA hfine hP
  have hcent : IsCentered (F.restrict p.1).func := hA.centered p.1 hP
  have hsimple : SimpleFun (F.restrict p.1).func :=
    scatteredCentered_isSimple _ (F.restrict p.1).hScat hcent
  have h1 : ScatFun.Reduces (ScatFun.minFun lam hlam_lt) (F.restrict p.1) :=
    minFun_reduces_simple lam hlam_lt _ hrank hsimple
  have hcocV : hA.cocenterOf hP ∈ V := by rw [hp']; exact hyV
  have h2 : ScatFun.Reduces (F.restrict p.1) (F.coRestrict V) :=
    piece_reduces_coRestrict_of_cocenter_mem F hA hVcl.isOpen hP hcocV
  exact h1.trans h2

/-- **First case — localizing a rank-`λ` ray inside `U`** (`6_double_successor_memo.tex:478-480`).
When some ray of `F` at `y` has rank `λ` (`hhigh`), fineness (`F` is not a lump of itself, so `F`
is `𝒲`-regular at `y`) forces *infinitely many* rank-`λ` rays, which accumulate at `y`; so some
rank-`λ` ray region `R = RaySet y n` with a large index `n` lies inside `U`, avoids `y`, and
satisfies `ℓ_λ ≡ ray_n ≤ F⇂R`. **Scaffolded for aristotle.**

Proof outline: set `S = {j | ℓ_λ ≤ F.rayOn y univ j}`. Since every ray has rank `≤ λ`
(`ScatFun.rayOn_cbRank_lt` + `firstCase_top_const`), `S = {j | λ ≤ CB(ray_j)}` (`≥`:
`ContinuouslyReduces.rank_monotone`; `≤`: `limit_rank_equiv_maxFun`). `S` is nonempty by `hhigh`.
Fineness gives `IsOmegaRegularAt (hA.piece (minFun λ) y) y`
(`isOmegaRegularAt_blockPieces_of_not_lump`, using `IsFine.1`), and `hallmin`+`hcoin` give
`hA.piece (minFun λ) y = F.restrict univ`, so `S` is infinite-or-empty at `w = maxFun λ ∈
omegaRegularSet (λ+1)`; nonempty ⇒ infinite. Take `M` from `exists_tail_raySet_subset y U`, pick
`n ∈ S` with `n ≥ M`; then `R = RaySet Set.univ y n` (`isClopen_raySet`, `⊆ U` by tail, `y ∉ R`),
and `ℓ_λ ≤ F.rayOn y univ n ≡ F.coRestrict R` (`rayOn_eq_corestrict`). -/
lemma firstCase_maxFun_ray
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam)
    (hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U)
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y)
    (hallmin : ∀ P ∈ Part,
      ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt))
    (hhigh : ∃ N : ℕ, lam ≤ CBRank (F.rayOn y Set.univ N).func) :
    ∃ R : Set Baire, IsClopen R ∧ R ⊆ U ∧ y ∉ R ∧
      ScatFun.Reduces (ScatFun.maxFun lam hlam_lt) (F.coRestrict R) := by
  classical
  obtain ⟨N, hN⟩ := hhigh
  have hlt2 : lam + 1 < omega1 := by
    have h := CBRank_lt_omega1 F.hScat; rwa [hFrank] at h
  have hconst : ∀ x ∈ CBLevel F.func lam, F.func x = y := firstCase_top_const lam F hFrank hA hcoin
  have hray_le : ∀ j, CBRank (F.rayOn y Set.univ j).func ≤ lam := fun j =>
    Order.lt_succ_iff.mp (ScatFun.rayOn_cbRank_lt F lam y hconst Set.univ isOpen_univ j)
  set S := {j : ℕ | ScatFun.Reduces (ScatFun.maxFun lam hlam_lt) (F.rayOn y Set.univ j)} with hSdef
  have hNS : N ∈ S := by
    have hrankN : CBRank (F.rayOn y Set.univ N).func = lam := le_antisymm (hray_le N) hN
    exact (limit_rank_equiv_maxFun _ lam hlam_lt hlim hrankN).2
  -- `𝒲`-regularity of `F` at `y`, via the `(minFun λ, y)`-block being all of `Part`.
  have hbp : hA.blockPieces (ScatFun.minFun lam hlam_lt) y = Part := by
    ext P
    constructor
    · rintro ⟨hP, -, -⟩; exact hP
    · intro hP; exact ⟨hP, hallmin P hP, hcoin P hP⟩
  have hpiece_eq :
      hA.piece (ScatFun.minFun lam hlam_lt) y = F.restrict (Set.univ : Set ↑F.domain) := by
    rw [ScatFun.IsCPartition.piece, hbp, hA.sUnion_eq]
  have hreg : IsOmegaRegularAt (hA.piece (ScatFun.minFun lam hlam_lt) y) y :=
    isOmegaRegularAt_blockPieces_of_not_lump hA (fun g y' hg => absurd hg (hsolv.1.1 g y'))
      (by rw [ScatFun.minFun_func]; exact minFun_isCentered lam hlam_lt) hsolv.2.1
      (by rw [minFun_cbRank_eq lam hlam_lt]; exact Order.lt_succ lam)
  have hrank_univ : CBRank (F.restrict (Set.univ : Set ↑F.domain)).func = CBRank F.func := by
    rw [cbRank_restrict_eq]; exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
  have hpiece_rank : CBRank (hA.piece (ScatFun.minFun lam hlam_lt) y).func = lam + 1 := by
    rw [hpiece_eq, hrank_univ, hFrank]
  have hwmem : ScatFun.maxFun lam hlam_lt ∈
      omegaRegularSet (CBRank (hA.piece (ScatFun.minFun lam hlam_lt) y).func)
        (CBRank_lt_omega1 (hA.piece (ScatFun.minFun lam hlam_lt) y).hScat) := by
    rw [omegaRegularSet_congr hpiece_rank
      (CBRank_lt_omega1 (hA.piece (ScatFun.minFun lam hlam_lt) y).hScat) hlt2]
    have hll : (lam + 1).limitPart = lam := ScatFun.limitPart_add_one lam hlim
    simp only [omegaRegularSet, Finset.mem_insert]
    left
    congr 1
    exact hll.symm
  have hset_eq : {j : ℕ | ScatFun.Reduces (ScatFun.maxFun lam hlam_lt)
        ((hA.piece (ScatFun.minFun lam hlam_lt) y).rayOn y Set.univ j)} = S := by
    ext j
    rw [hSdef]; simp only [Set.mem_setOf_eq]
    rw [hpiece_eq]
    exact ⟨fun h => h.trans (ScatFun.rayOn_restrict_equiv F Set.univ y j).1,
      fun h => h.trans (ScatFun.rayOn_restrict_equiv F Set.univ y j).2⟩
  have hSreg := hreg (ScatFun.maxFun lam hlam_lt) hwmem
  rw [hset_eq] at hSreg
  have hSinf : S.Infinite :=
    hSreg.resolve_right (Set.nonempty_iff_ne_empty.mp ⟨N, hNS⟩)
  obtain ⟨M, hM⟩ := exists_tail_raySet_subset y U hU (hUcov hsolv.2.1)
  obtain ⟨n, hnS, hnlt⟩ := hSinf.exists_gt M
  refine ⟨RaySet Set.univ y n, isClopen_raySet y n, hM n hnlt.le, by simp [RaySet], ?_⟩
  have hred : ScatFun.Reduces (ScatFun.maxFun lam hlam_lt) (F.rayOn y Set.univ n) := hnS
  rw [rayOn_eq_corestrict] at hred
  exact hred

/-- **Crux, `λ` limit — first case: all cocenters equal `y`** (`6_double_successor_memo.tex:476-480`).
Since every piece has cocenter `y`, `F` is *simple* (`firstCase_simple`, Prop 4.11), so by the
classification of simple rank-`λ+1` functions (`simpleFunctionsLambdaPlusOne`, Thm 4.12) `F` is
equivalent to `k_{λ+1}`, `k_{λ+1} ⊕ ℓ_λ`, or `pgl ℓ_λ`. In the two *centered* cases (`k_{λ+1}`,
`pgl ℓ_λ`) the cocenter of `F` is `y ∈ U`, so `F ≤ F⇂U` directly (`firstCase_centered_reduces`).
In the middle case `F ≡ k_{λ+1} ⊕ ℓ_λ`, split `U` along a rank-`λ` ray region `R ⊆ U`
(`firstCase_maxFun_ray`): `k_{λ+1} ≤ F⇂(U∖R)` (`firstCase_minFun_coRestrict`) and `ℓ_λ ≤ F⇂R`,
glued by `reduces_glBin_coRestrict_of_disjoint`, giving `F ≤ k_{λ+1} ⊕ ℓ_λ ≤ F⇂U`. -/
lemma solvable_lambdaPlusOne_reduces_coRestrict_limit_firstCase
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U)
    (hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y) :
    ScatFun.Reduces F (F.coRestrict U) := by
  have hy : y ∈ hA.cocenterSet := hsolv.2.1
  have hyU : y ∈ U := hUcov hy
  have hsimple : SimpleFun F.func := firstCase_simple lam F hFrank hA hcoin
  have hFmax : ScatFun.Reduces F (ScatFun.succMaxFun lam hlam_lt) :=
    simple_reduces_succMaxFun lam hlam_lt F hFrank hsimple
  -- If some piece is `≡ pgl ℓ_λ`, then `F ≡ pgl ℓ_λ` is centered; handle directly.
  by_cases hex : ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt)
  · obtain ⟨P, hP, hPeq⟩ := hex
    have hmaxle : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) F :=
      hPeq.2.trans (restrict_le_self F P)
    have hc : IsCentered F.func :=
      isCentered_of_equiv
        (by rw [succMaxFun_func]; exact pglSuccMaxFun_isCentered lam hlam_lt) ⟨hFmax, hmaxle⟩
    exact firstCase_centered_reduces lam F hFrank hA hy U hU hUcov hcoin hc
  · -- Otherwise every piece is `≡ k_{λ+1}` (`piece_equiv_minFun_or_succMaxFun`).
    push_neg at hex
    have hallmin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part),
        ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt) := by
      intro P hP
      rcases piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hsolv.1 hP with
        h | h
      · exact h
      · exact absurd h (hex P hP)
    have hbqo : TwoBQO (ScatFun.LevelLT.reduces lam) :=
      ScatFun.LevelLT.isTwoBQO_of_FG_below (fun β hβ => hFG β (hβ.trans (lt_add_one lam)))
    rcases simpleFunctionsLambdaPlusOne lam hlam_lt (Or.inr ⟨hlim, hlam_ne⟩) hbqo F hFrank hsimple with
      hmin | hmid | hmax
    · -- `F ≡ k_{λ+1}` : centered.
      have hc : IsCentered F.func :=
        isCentered_of_equiv (by rw [ScatFun.minFun_func]; exact minFun_isCentered lam hlam_lt) hmin
      exact firstCase_centered_reduces lam F hFrank hA hy U hU hUcov hcoin hc
    · -- `F ≡ k_{λ+1} ⊕ ℓ_λ`. Split on whether `F` has a rank-`λ` ray at `y`.
      have hconst : ∀ x ∈ CBLevel F.func lam, F.func x = y :=
        firstCase_top_const lam F hFrank hA hcoin
      by_cases hrays : ∀ n, CBRank (F.rayOn y Set.univ n).func < lam
      · -- No rank-`λ` ray: `F ≡ k_{λ+1}`, centered.
        have hFmin : ScatFun.Equiv F (ScatFun.minFun lam hlam_lt) :=
          simple_caseA_equiv_minFun lam hlam_lt (Or.inr ⟨hlim, hlam_ne⟩) F hFrank hsimple y hconst
            hrays
        have hc : IsCentered F.func :=
          isCentered_of_equiv (by rw [ScatFun.minFun_func]; exact minFun_isCentered lam hlam_lt) hFmin
        exact firstCase_centered_reduces lam F hFrank hA hy U hU hUcov hcoin hc
      · -- A rank-`λ` ray exists: localize it inside `U` and glue.
        push_neg at hrays
        obtain ⟨N, hN⟩ := hrays
        obtain ⟨R, hRcl, hRU, hyR, hRmax⟩ :=
          firstCase_maxFun_ray lam hlim hlam_lt F hFrank hA hsolv U hU hUcov hcoin
            hallmin ⟨N, hN⟩
        have hmincov : ScatFun.Reduces (ScatFun.minFun lam hlam_lt) (F.coRestrict (U \ R)) :=
          firstCase_minFun_coRestrict lam hlam_lt F hFrank hA hsolv.1 hy (U \ R)
            (hU.diff hRcl) ⟨hyU, hyR⟩
        have hglue : ScatFun.Reduces (ScatFun.glBin (ScatFun.minFun lam hlam_lt)
              (ScatFun.maxFun lam hlam_lt)) (F.coRestrict U) :=
          ScatFun.reduces_glBin_coRestrict_of_disjoint _ _ (hU.diff hRcl) hRcl
            Set.diff_subset hRU disjoint_sdiff_left hmincov hRmax
        exact hmid.1.trans hglue
    · -- `F ≡ pgl ℓ_λ` : centered.
      have hc : IsCentered F.func :=
        isCentered_of_equiv (by rw [succMaxFun_func]; exact pglSuccMaxFun_isCentered lam hlam_lt)
          hmax
      exact firstCase_centered_reduces lam F hFrank hA hy U hU hUcov hcoin hc

/-
A nontrivial solvable partition has infinitely many cocenters away from its distinguished
point.  This is the solvable (clause-2-only) analogue of
`IsStronglySolvableAt.cocenterSet_diff_singleton_infinite`.
-/
lemma ScatFun.IsCPartition.IsSolvableAt.cocenterSet_diff_singleton_infinite
    {F : ScatFun} {Part : Set (Set ↑F.domain)} {hA : F.IsCPartition Part}
    {lam : Ordinal.{0}} {y : Baire} (hsolv : hA.IsSolvableAt lam y)
    (hne : ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y) :
    (hA.cocenterSet \ {y}).Infinite := by
  by_contra h_contra;
  -- By `exists_clopen_nbhd_disjoint_finite`, obtain a clopen nbhd $U$ of $y$ (contained in $Baire$) disjoint from the finite set `hA.cocenterSet \ {y}`.
  obtain ⟨U, hUcl, hyU, hUdisj⟩ : ∃ U : Set Baire, IsClopen U ∧ y ∈ U ∧ Disjoint U (hA.cocenterSet \ {y}) := by
    obtain ⟨U, hUcl, hyU, hUdisj⟩ : ∃ U : Set Baire, IsClopen U ∧ y ∈ U ∧ ∀ p ∈ (hA.cocenterSet \ {y}), p ∉ U := by
      have h_finite : (hA.cocenterSet \ {y}).Finite := by
        exact Classical.not_not.mp h_contra
      have := @exists_clopen_nbhd_disjoint_finite;
      exact this h_finite ( by aesop ) |> fun ⟨ U, hUcl, hyU, hUdisj ⟩ => ⟨ U, hUcl, hyU, fun p hp hpU => hUdisj.le_bot ⟨ hpU, hp ⟩ ⟩;
    exact ⟨ U, hUcl, hyU, Set.disjoint_left.mpr fun p hp hp' => hUdisj p hp' hp ⟩;
  obtain ⟨ P, hP, hP' ⟩ := hne; have := hsolv.2.2 P hP hP' U hUcl hyU; simp_all +decide [ Set.disjoint_left ] ;
  obtain ⟨ Q, hQ, hQ', hQ'', hQ''' ⟩ := this; specialize hUdisj hQ''; simp_all +decide [ ScatFun.IsCPartition.cocenterSet ] ;
  exact hUdisj Q hQ rfl

/-
Infinitely many distinct cocenters of minimum-type pieces pack an omega-gluing of the
minimum into a corestriction containing those cocenters.
-/
lemma omega_minFun_reduces_coRestrict_of_infinite_cocenters
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (U : Set Baire) (hU : IsOpen U)
    (Y : Set Baire) (hYinf : Y.Infinite) (hYU : Y ⊆ U)
    (hYpieces : ∀ z ∈ Y, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = z ∧ ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt)) :
    ScatFun.Reduces (ScatFun.omega (ScatFun.minFun lam hlam_lt)) (F.coRestrict U) := by
  contrapose! hYinf;
  -- Assume for contradiction that Y is infinite.
  by_contra hYinf';
  -- For each z ∈ Y, choose its piece P. The piece rank is lam+1 from its equivalence to minFun; it is centered and its top CB level is constantly z because z is its cocenter (use block_const_on_top).
  have h_piece_rank : ∀ z ∈ Y, ∃ P : Set ↑F.domain, ∃ hP : P ∈ Part, hA.cocenterOf hP = z ∧ CBRank (F.restrict P).func = lam + 1 ∧ IsCentered (F.restrict P).func ∧ ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = z := by
    intro z hz
    obtain ⟨P, hP, hPcocenter, hPequiv⟩ := hYpieces z hz
    use P, hP, hPcocenter
    have hPrank : CBRank (F.restrict P).func = lam + 1 := by
      have hPrank : CBRank (F.restrict P).func = CBRank (ScatFun.minFun lam hlam_lt).func := by
        exact cbRank_eq_of_equiv hPequiv;
      exact hPrank.trans ( minFun_cbRank_eq _ _ )
    have hPcentered : IsCentered (F.restrict P).func := by
      exact ScatFun.IsCPartition.centered hA P hP
    have hPtop : ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = z := by
      have hPtop : ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = cocenter (F.restrict P).func hPcentered := by
        exact fun x a => block_const_on_top (F.restrict P) hPcentered lam hPrank x a;
      exact fun x hx => hPtop x hx ▸ hPcocenter ▸ rfl
    exact ⟨hPrank, hPcentered, hPtop⟩;
  -- For each z ∈ Y choose its piece P. Then z ∈ IntertwineSet F minFun by minFun_yn_mem_intertwineSet.
  have h_piece_intertwine : ∀ z ∈ Y, z ∈ ScatFun.IntertwineSet F (ScatFun.minFun lam hlam_lt) := by
    intro z hz;
    obtain ⟨ P, hP, hzP, hrank, hc, hconst ⟩ := h_piece_rank z hz;
    convert ScatFun.minFun_yn_mem_intertwineSet F P lam hlam_lt z hrank hconst using 1;
  -- Then z ∈ IntertwineSet (F.coRestrict U) minFun by mem_intertwineSet_coRestrict_of_open.
  have h_piece_intertwine_coRestrict : ∀ z ∈ Y, z ∈ ScatFun.IntertwineSet (F.coRestrict U) (ScatFun.minFun lam hlam_lt) := by
    exact fun z hz => ScatFun.mem_intertwineSet_coRestrict_of_open F ( ScatFun.minFun lam hlam_lt ) U hU ( hYU hz ) ( h_piece_intertwine z hz );
  exact hYinf <| ScatFun.omega_reduces_of_intertwineSet_infinite _ _ <| Set.Infinite.mono h_piece_intertwine_coRestrict hYinf'

/-
Infinitely many distinct cocenters of successor-maximum-type pieces pack an omega-gluing of
that type into a corestriction containing those cocenters.
-/
lemma omega_succMaxFun_reduces_coRestrict_of_infinite_cocenters
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (U : Set Baire) (hU : IsOpen U)
    (Y : Set Baire) (hYinf : Y.Infinite) (hYU : Y ⊆ U)
    (hYpieces : ∀ z ∈ Y, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = z ∧ CBRank (F.restrict P).func = lam + 1 ∧
        ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt)) :
    ScatFun.Reduces (ScatFun.omega (ScatFun.succMaxFun lam hlam_lt)) (F.coRestrict U) := by
  have hY_subset_intertwine : Y ⊆ ScatFun.IntertwineSet (F.coRestrict U) (ScatFun.succMaxFun lam hlam_lt) := by
    intro z hz
    obtain ⟨P, hP, hPcocenter, hPlam, hPequiv⟩ := hYpieces z hz
    have hPconst : ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = z := by
      have hPcentered : IsCentered (F.restrict P).func := by
        exact hA.centered P hP;
      have hPconst : ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = cocenter (F.restrict P).func hPcentered := by
        exact fun x a => block_const_on_top (F.restrict P) hPcentered lam hPlam x a;
      exact fun x hx => hPconst x hx ▸ hPcocenter
    have hPlam1 : CBRank (F.restrict P).func = lam + 1 := by
      exact hPlam
    have hPomega : ScatFun.Reduces (F.restrict P) (F.coRestrict U) := by
      apply piece_reduces_coRestrict_of_cocenter_mem F hA hU hP (by
      exact hPcocenter.symm ▸ hYU hz)
    exact (by
    apply ScatFun.mem_intertwineSet_coRestrict_of_open;
    · exact hU;
    · exact hYU hz;
    · apply ScatFun.succMaxFun_yn_mem_intertwineSet F P lam hlam_lt z hPlam1 hPconst hPequiv);
  exact ScatFun.omega_reduces_of_intertwineSet_infinite _ _ ( hYinf.mono hY_subset_intertwine )

/-- The `Y₁`-infinite branch of the solvable limit case. -/
lemma solvable_limit_secondCase_succ_infinite
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    (U : Set Baire) (hU : IsOpen U) (hUcov : hA.cocenterSet ⊆ U)
    (Y1 : Set Baire) (hY1inf : Y1.Infinite)
    (hY1 : ∀ z, z ∈ Y1 ↔ ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = z ∧
        ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt)) :
    ScatFun.Reduces F (F.coRestrict U) := by
  have hFomega : ScatFun.Reduces F (ScatFun.omega (ScatFun.succMaxFun lam hlam_lt)) := by
    apply hA.reduces_omega_of_forall_piece_le
    intro P hP
    rcases piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine hP with
      hmin | hmax
    · apply hmin.left.trans
      rw [ScatFun.minFun_func, succMaxFun_func]
      exact minFun_le_pglMaxFun lam hlam_lt hlam_ne
    · exact hmax.left
  apply hFomega.trans
  apply omega_succMaxFun_reduces_coRestrict_of_infinite_cocenters
    lam hlam_lt F hA U hU Y1 hY1inf
  · intro z hz
    obtain ⟨P, hP, hPz, _⟩ := (hY1 z).mp hz
    exact hUcov ⟨⟨P, hP⟩, hPz⟩
  · intro z hz
    obtain ⟨P, hP, hPz, hPequiv⟩ := (hY1 z).mp hz
    exact ⟨P, hP, hPz, piece_rank_eq_of_fine lam F hFrank hA hfine hP, hPequiv⟩

/-
The `Y₁`-empty branch of the solvable limit case.
-/
lemma solvable_limit_secondCase_succ_empty
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    (U : Set Baire) (hU : IsOpen U) (hUcov : hA.cocenterSet ⊆ U)
    (hYinf : hA.cocenterSet.Infinite)
    (hempty : ¬ ∃ (P : Set ↑F.domain) (_hP : P ∈ Part),
      ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt)) :
    ScatFun.Reduces F (F.coRestrict U) := by
  have h_kannan : ScatFun.Reduces F (ScatFun.omega (ScatFun.minFun lam hlam_lt)) := by
    apply hA.reduces_omega_of_forall_piece_le;
    intro P hP
    have h_equiv : ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt) := by
      exact Or.resolve_right ( piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine hP ) fun h => hempty ⟨ P, hP, h ⟩
    exact h_equiv.left;
  refine h_kannan.trans ?_;
  apply omega_minFun_reduces_coRestrict_of_infinite_cocenters lam hlam_lt F hA U hU hA.cocenterSet hYinf hUcov;
  intro z hz
  obtain ⟨P, hP, hPz⟩ : ∃ P : Set ↑F.domain, ∃ hP : P ∈ Part, hA.cocenterOf hP = z := by
    exact Subtype.exists'.mpr hz;
  exact ⟨ P, hP, hPz, Or.resolve_right ( piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine hP ) fun h => hempty ⟨ P, hP, h ⟩ ⟩

/-- **A single cocenter block is simple.** For a cocenter `c ∈ Y_𝒫`, the block `F↾A^{c}_𝒫`
(the union of all pieces with cocenter `c`, `hA.domainOver {c}`) is a *simple* function of
CB-rank `λ+1` whose distinguished point is `c`. Proof: transport the sub-partition `𝒫⇂{c}` onto
the block (mirroring `solvableDecomposition_transport` with `U = {c}`), giving an `IsCPartition`
all of whose cocenters are `c`; then `firstCase_simple` / `firstCase_top_const` apply. Rank
`λ+1` is squeezed between the whole `F` (`restrict_le_self`) and one constituent piece
(`piece_rank_eq_of_fine`). -/
lemma block_simple_of_fine
    (lam : Ordinal.{0}) (_hlam_lt : lam < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    {c : Baire} (hc : c ∈ hA.cocenterSet) :
    SimpleFun (F.restrict (hA.domainOver {c})).func ∧
    CBRank (F.restrict (hA.domainOver {c})).func = lam + 1 ∧
    (∀ x ∈ CBLevel (F.restrict (hA.domainOver {c})).func lam,
      (F.restrict (hA.domainOver {c})).func x = c) := by
  classical
  set A : Set ↑F.domain := hA.domainOver {c} with hAdef
  have hAeq : A = ⋃₀ hA.piecesOver {c} := rfl
  set S : Set ↑F.domain → Set ↑(F.restrict A).domain :=
    fun P => {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ P} with hSdef
  set Part' : Set (Set ↑(F.restrict A).domain) := S '' hA.piecesOver {c} with hPart'def
  have hsubA : ∀ P ∈ hA.piecesOver {c}, P ⊆ A := fun P hP => by
    rw [hAeq]; exact Set.subset_sUnion_of_mem hP
  have hequiv : ∀ P ∈ hA.piecesOver {c},
      ScatFun.Equiv ((F.restrict A).restrict (S P)) (F.restrict P) := fun P hP =>
    ScatFun.restrict_restrict_equiv F A P (hsubA P hP)
  have hA' : (F.restrict A).IsCPartition Part' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (hA.countable.mono (fun P hP => hP.choose)).image S
    · rintro _ ⟨P, hP, rfl⟩
      exact (hA.isClopen P hP.choose).preimage
        (continuous_subtype_val.comp (F.restrictEquiv A).continuous)
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      have hPQ : P ≠ Q := fun h => hne (by rw [h])
      have hdisj := hA.pairwiseDisjoint hP.choose hQ.choose hPQ
      simp only [Function.onFun, id] at hdisj ⊢
      rw [Set.disjoint_left] at hdisj ⊢
      intro w hwP hwQ
      exact hdisj hwP hwQ
    · ext w
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      have hwA : (F.restrictEquiv A w : ↑F.domain) ∈ ⋃₀ hA.piecesOver {c} :=
        (F.restrictEquiv A w).2
      obtain ⟨P, hP, hwP⟩ := hwA
      exact ⟨S P, ⟨P, hP, rfl⟩, hwP⟩
    · rintro _ ⟨P, hP, rfl⟩
      exact isCentered_of_equiv (hA.centered P hP.choose) (hequiv P hP)
  have hcoc : ∀ (P : Set ↑F.domain) (hPU : P ∈ hA.piecesOver {c}) (h' : S P ∈ Part'),
      hA'.cocenterOf h' = hA.cocenterOf hPU.choose := fun P hPU h' =>
    ScatFun.cocenter_restrict_restrict_eq F A P (hsubA P hPU) _ _
  have hcoin' : ∀ (P' : Set ↑(F.restrict A).domain) (hP' : P' ∈ Part'),
      hA'.cocenterOf hP' = c := by
    intro P' hP'
    obtain ⟨P, hPU, hSP⟩ := id hP'
    subst hSP
    rw [hcoc P hPU hP']
    exact Set.mem_singleton_iff.mp hPU.choose_spec
  have hGrank : CBRank (F.restrict A).func = lam + 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hFrank]
      exact ContinuouslyReduces.rank_monotone (F.restrict A).hScat F.hScat
        (restrict_le_self F A)
    · obtain ⟨⟨P0, hP0⟩, hP0c⟩ := hc
      have hP0c' : hA.cocenterOf hP0 = c := hP0c
      have hP0U : P0 ∈ hA.piecesOver {c} := ⟨hP0, Set.mem_singleton_iff.mpr hP0c'⟩
      have hrankP0 : CBRank ((F.restrict A).restrict (S P0)).func = lam + 1 := by
        rw [cbRank_eq_of_equiv (hequiv P0 hP0U)]
        exact piece_rank_eq_of_fine lam F hFrank hA hfine hP0
      rw [← hrankP0]
      exact ContinuouslyReduces.rank_monotone ((F.restrict A).restrict (S P0)).hScat
        (F.restrict A).hScat (restrict_le_self (F.restrict A) (S P0))
  exact ⟨firstCase_simple lam (F.restrict A) hGrank hA' hcoin', hGrank,
    firstCase_top_const lam (F.restrict A) hGrank hA' hcoin'⟩

/-- **Crux, `λ` limit — second case, subcase `Y₀ → y`** (`6_double_successor_memo.tex:490`).
`Y₁ = {y}`, `Y₀ = Y_𝒫 \ {y}` is infinite and accumulates only at `y`. Enumerate `Y₀`, group the
pieces by cocenter into blocks `A n` (each simple of rank `λ+1`: `≡ pgl ℓ_λ` at the distinguished
`y = yS 0`, `≡ k_{λ+1}` off `y`), and conclude by `diagonal_for_lambda_plus_one`.

**Fully proved.** -/
lemma solvable_limit_secondCase_diagonal
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) (hfine : hA.IsFine lam)
    {y : Baire} (hy_mem : y ∈ hA.cocenterSet)
    (hdistPiece : ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt))
    (hAway : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt))
    (hY0inf : (hA.cocenterSet \ {y}).Infinite)
    (hconv : ∀ V : Set Baire, IsClopen V → y ∈ V → ((hA.cocenterSet \ {y}) \ V).Finite)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U) :
    ScatFun.Reduces F (F.coRestrict U) := by
  classical
  have hbqo : TwoBQO (ScatFun.LevelLT.reduces lam) :=
    ScatFun.LevelLT.isTwoBQO_of_FG_below (fun β hβ => hFG β (hβ.trans (lt_add_one lam)))
  -- (1) Enumerate `Y₀` (countable + infinite ⟹ a bijection with `ℕ`).
  obtain ⟨e, he_inj, he_range⟩ :
      ∃ e : ℕ → Baire, Function.Injective e ∧ Set.range e = hA.cocenterSet \ {y} := by
    have : Countable {P // P ∈ Part} := hA.countable.to_subtype
    have hcocct : hA.cocenterSet.Countable := Set.countable_range _
    have hct : (hA.cocenterSet \ {y}).Countable := hcocct.mono Set.diff_subset
    obtain ⟨d⟩ := Set.countable_infinite_iff_nonempty_denumerable.mp ⟨hct, hY0inf⟩
    let g : ℕ ≃ ↥(hA.cocenterSet \ {y}) := (@Denumerable.eqv _ d).symm
    refine ⟨fun n => (g n : Baire), fun a b hab => g.injective (Subtype.ext hab), ?_⟩
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨n, rfl⟩
      exact (g n).2
    · intro hz
      exact ⟨g.symm ⟨z, hz⟩, by simp⟩
  -- (2) Cocenter sequence: `yS 0 = y`, `yS (n+1) = e n`.
  set yS : ℕ → Baire := fun n => match n with | 0 => y | (k + 1) => e k with hySdef
  have hyS0 : yS 0 = y := rfl
  have he_ne_y : ∀ n, e n ≠ y := fun n =>
    (he_range ▸ Set.mem_range_self n : e n ∈ hA.cocenterSet \ {y}).2
  have hyS_inj : Function.Injective yS := by
    intro a b hab
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ m => exact absurd hab.symm (he_ne_y m)
    | succ k =>
      cases b with
      | zero => exact absurd hab (he_ne_y k)
      | succ m =>
        have hem : e k = e m := hab
        rw [he_inj hem]
  -- (3) Blocks: `A n = ⋃ {P ∈ Part | cocenter = yS n}` (all pieces with that cocenter).
  set A : ℕ → Set ↑F.domain := fun n => hA.domainOver {yS n} with hAdef
  -- Every `yS n` is a cocenter (`yS 0 = y ∈ Y_𝒫`; `yS (k+1) = e k ∈ Y₀ ⊆ Y_𝒫`).
  have hyS_mem : ∀ n, yS n ∈ hA.cocenterSet := by
    intro n
    cases n with
    | zero => rw [hyS0]; exact hy_mem
    | succ k => exact (he_range ▸ Set.mem_range_self k : e k ∈ hA.cocenterSet \ {y}).1
  -- Each block `A n = A^{yS n}_𝒫` is simple of rank `λ+1`, distinguished point `yS n`
  -- (`block_simple_of_fine`). NB: simple ≠ centered in general.
  have hblock : ∀ n, SimpleFun (F.restrict (A n)).func ∧
      CBRank (F.restrict (A n)).func = lam + 1 ∧
      (∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = yS n) :=
    fun n => block_simple_of_fine lam hlam_lt F hFrank hA hfine (hyS_mem n)
  have hsimple : ∀ n, SimpleFun (F.restrict (A n)).func := fun n => (hblock n).1
  -- Membership in a block: `x ∈ A n ↔ x` lies in a piece with cocenter `yS n`.
  have hAmem : ∀ (n : ℕ) (x : ↑F.domain), x ∈ A n ↔
      ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = yS n ∧ x ∈ P := by
    intro n x
    simp only [hAdef, ScatFun.IsCPartition.domainOver, ScatFun.IsCPartition.piecesOver,
      Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, ⟨hP, hPc⟩, hxP⟩; exact ⟨P, hP, hPc, hxP⟩
    · rintro ⟨P, hP, hPc, hxP⟩; exact ⟨P, ⟨hP, hPc⟩, hxP⟩
  have hdu : F.IsDisjointUnion A := by
    refine ⟨fun i => hA.domainOver_isClopen {yS i}, fun i j hij => ?_, ?_⟩
    · -- Disjoint: pieces with distinct cocenters (`yS i ≠ yS j`) are distinct, hence disjoint.
      rw [Set.disjoint_left]
      intro x hxi hxj
      obtain ⟨P, hP, hPc, hxP⟩ := (hAmem i x).mp hxi
      obtain ⟨Q, hQ, hQc, hxQ⟩ := (hAmem j x).mp hxj
      rcases eq_or_ne P Q with rfl | hPQ
      · exact hij (hyS_inj (hPc.symm.trans hQc))
      · exact Set.disjoint_left.mp (hA.pairwiseDisjoint hP hQ hPQ) hxP hxQ
    · -- Cover: every `x` lies in a piece, whose cocenter is `y = yS 0` or some `e k = yS (k+1)`.
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨P, hP, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
        Set.mem_sUnion.mp (hA.sUnion_eq.symm ▸ Set.mem_univ x)
      have hc : hA.cocenterOf hP ∈ hA.cocenterSet := ⟨⟨P, hP⟩, rfl⟩
      by_cases hcy : hA.cocenterOf hP = y
      · exact Set.mem_iUnion.mpr ⟨0, (hAmem 0 x).mpr ⟨P, hP, hcy, hxP⟩⟩
      · have hr : hA.cocenterOf hP ∈ Set.range e := by rw [he_range]; exact ⟨hc, hcy⟩
        obtain ⟨k, hk⟩ := hr
        exact Set.mem_iUnion.mpr ⟨k + 1, (hAmem (k + 1) x).mpr ⟨P, hP, hk.symm, hxP⟩⟩
  have hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1 := fun n => (hblock n).2.1
  have hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam,
      (F.restrict (A n)).func x = yS n := fun n => (hblock n).2.2
  -- (4) Distinguished block `A 0 ≡ pgl ℓ_λ`.
  have h0 : ScatFun.Equiv (F.restrict (A 0)) (ScatFun.succMaxFun lam hlam_lt) := by
    -- `≤`: block `A 0` is simple of rank `λ+1`, so reduces to the maximum `pgl ℓ_λ`.
    refine ⟨simple_reduces_succMaxFun lam hlam_lt (F.restrict (A 0)) (hrank 0) (hsimple 0), ?_⟩
    -- `≥`: `A 0` contains the `y`-piece `P ≡ pgl ℓ_λ`, and `P ⊆ A 0`.
    obtain ⟨P, hP, hPy, hPeq⟩ := hdistPiece
    have hPmem : P ∈ hA.piecesOver {yS 0} :=
      ⟨hP, Set.mem_singleton_iff.mpr (hPy.trans hyS0.symm)⟩
    have hPsub : P ⊆ A 0 := Set.subset_sUnion_of_mem hPmem
    have hPred : ScatFun.Reduces (F.restrict P) (F.restrict (A 0)) :=
      (ScatFun.restrict_restrict_equiv F (A 0) P hPsub).2.trans
        (restrict_le_self (F.restrict (A 0)) _)
    exact hPeq.2.trans hPred
  -- (5) Off-`y` blocks: simple, not `≥ pgl ℓ_λ`, hence `≤ k_{λ+1} ⊕ ℓ_λ`.
  have hpos : ∀ n, 0 < n → ScatFun.Reduces (F.restrict (A n))
      (ScatFun.glBin (ScatFun.minFun lam hlam_lt) (ScatFun.maxFun lam hlam_lt)) := by
    intro n hn
    -- `n ≥ 1 ⟹ yS n = e (n-1) ∈ Y₀`, so `yS n ≠ y`.
    have hyn_ne : yS n ≠ y := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact he_ne_y k
    -- `pgl ℓ_λ` does not reduce into the block `A n`: else (centered ⟹ into one piece,
    -- `centered_reduces_restrict_of_reduces_restrict_sUnion`) it reduces into a piece with
    -- cocenter `yS n ≠ y`, which is `≡ k_{λ+1}` (`hAway`), giving `pgl ℓ_λ ≤ k_{λ+1}`.
    have hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.restrict (A n)) := by
      intro hred
      have hc : IsCentered (ScatFun.succMaxFun lam hlam_lt).func := by
        rw [succMaxFun_func]; exact pglSuccMaxFun_isCentered lam hlam_lt
      obtain ⟨P, hPmem, hPred⟩ := ScatFun.centered_reduces_restrict_of_reduces_restrict_sUnion
        (F := F) (S := hA.piecesOver {yS n})
        (fun P hP => (hA.isClopen P hP.choose).isOpen) hc hred
      have hPy : hA.cocenterOf hPmem.choose ≠ y := by
        rw [Set.mem_singleton_iff.mp hPmem.choose_spec]; exact hyn_ne
      have hchain : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (ScatFun.minFun lam hlam_lt) :=
        hPred.trans (hAway P hPmem.choose hPy).1
      exact pglMaxFun_not_le_minFunPlusOne_limit lam hlim hlam_ne hlam_lt
        (by rwa [ScatFun.reduces_iff, succMaxFun_func, ScatFun.minFun_func] at hchain)
    -- Simple block, not `≡ pgl ℓ_λ`, so `≤ k_{λ+1} ⊕ ℓ_λ`.
    exact ScatFun.block_reduces_glBin_of_not_succMaxFun lam hlim hlam_lt hbqo (F.restrict (A n))
      (hrank n) (hsimple n) (fun heq => hnotmax heq.2)
  -- (6) `(yS (n+1)) = (e n) → y = yS 0`.
  have hconv' : Filter.Tendsto (fun n => yS (n + 1)) Filter.atTop (nhds (yS 0)) := by
    rw [tendsto_atTop_nhds]
    intro V hyV hVopen
    obtain ⟨m, hm⟩ := nbhd_basis y V hVopen (hyS0 ▸ hyV)
    have hDfin : ((hA.cocenterSet \ {y}) \ nbhd y m).Finite :=
      hconv (nbhd y m) (baire_nbhd_isClopen y m) (fun i _ => rfl)
    have himg : e '' {n : ℕ | e n ∉ nbhd y m} ⊆ (hA.cocenterSet \ {y}) \ nbhd y m := by
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨he_range ▸ Set.mem_range_self n, hn⟩
    have hfin : {n : ℕ | e n ∉ nbhd y m}.Finite :=
      Set.Finite.of_finite_image (hDfin.subset himg) he_inj.injOn
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine ⟨N + 1, fun n hn => hm ?_⟩
    by_contra hcon
    have hnmem : n ∈ {k : ℕ | e k ∉ nbhd y m} := hcon
    exact absurd (hN hnmem) (by omega)
  -- (7) Assemble.
  have hyU : yS 0 ∈ U := hUcov (by rw [hyS0]; exact hy_mem)
  have hpair := ScatFun.diagonal_for_lambda_plus_one F A hdu lam hlam_lt yS hyS_inj hrank hdist
    h0 hpos hconv' U hU hyU
  exact hpair.1.trans hpair.2

/-- The complement of the block `A^U_𝒫` is the block `A^{Uᶜ}_𝒫`: every point lies in exactly
one piece, whose cocenter is in `U` or in `Uᶜ`. -/
lemma ScatFun.IsCPartition.domainOver_compl_eq {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (U : Set Baire) :
    (hA.domainOver U)ᶜ = hA.domainOver Uᶜ := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    obtain ⟨P, hP, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
      Set.mem_sUnion.mp (hA.sUnion_eq.symm ▸ Set.mem_univ x)
    refine Set.mem_sUnion.mpr ⟨P, ⟨hP, ?_⟩, hxP⟩
    intro hcoc
    exact hx (Set.mem_sUnion.mpr ⟨P, ⟨hP, hcoc⟩, hxP⟩)
  · intro x hx hxU
    obtain ⟨P, ⟨hP, hPnU⟩, hxP⟩ := Set.mem_sUnion.mp hx
    obtain ⟨Q, ⟨hQ, hQU⟩, hxQ⟩ := Set.mem_sUnion.mp hxU
    rcases eq_or_ne P Q with rfl | hne
    · exact hPnU hQU
    · exact Set.disjoint_left.mp (hA.pairwiseDisjoint hP hQ hne) hxP hxQ

/-- **`f₀`-bound helper.** If every piece with cocenter in `U` reduces to `g`, then the block
`F↾A^U_𝒫` reduces to `ω g` (`Gluingasupperbound_cor`, via the transported sub-partition — the
same `solvableDecomposition_transport` construction as `block_simple_of_fine`). -/
lemma domainOver_reduces_omega_of_pieces_le
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (U : Set Baire) (g : ScatFun)
    (hpieces : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ∈ U →
      ScatFun.Reduces (F.restrict P) g) :
    ScatFun.Reduces (F.restrict (hA.domainOver U)) (ScatFun.omega g) := by
  classical
  set A : Set ↑F.domain := hA.domainOver U with hAdef
  have hAeq : A = ⋃₀ hA.piecesOver U := rfl
  set S : Set ↑F.domain → Set ↑(F.restrict A).domain :=
    fun P => {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ P} with hSdef
  set Part' : Set (Set ↑(F.restrict A).domain) := S '' hA.piecesOver U with hPart'def
  have hsubA : ∀ P ∈ hA.piecesOver U, P ⊆ A := fun P hP => by
    rw [hAeq]; exact Set.subset_sUnion_of_mem hP
  have hequiv : ∀ P ∈ hA.piecesOver U,
      ScatFun.Equiv ((F.restrict A).restrict (S P)) (F.restrict P) := fun P hP =>
    ScatFun.restrict_restrict_equiv F A P (hsubA P hP)
  have hA' : (F.restrict A).IsCPartition Part' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (hA.countable.mono (fun P hP => hP.choose)).image S
    · rintro _ ⟨P, hP, rfl⟩
      exact (hA.isClopen P hP.choose).preimage
        (continuous_subtype_val.comp (F.restrictEquiv A).continuous)
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      have hPQ : P ≠ Q := fun h => hne (by rw [h])
      have hdisj := hA.pairwiseDisjoint hP.choose hQ.choose hPQ
      simp only [Function.onFun, id] at hdisj ⊢
      rw [Set.disjoint_left] at hdisj ⊢
      intro w hwP hwQ
      exact hdisj hwP hwQ
    · ext w
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      have hwA : (F.restrictEquiv A w : ↑F.domain) ∈ ⋃₀ hA.piecesOver U :=
        (F.restrictEquiv A w).2
      obtain ⟨P, hP, hwP⟩ := hwA
      exact ⟨S P, ⟨P, hP, rfl⟩, hwP⟩
    · rintro _ ⟨P, hP, rfl⟩
      exact isCentered_of_equiv (hA.centered P hP.choose) (hequiv P hP)
  apply hA'.reduces_omega_of_forall_piece_le
  rintro _ ⟨P, hPU, rfl⟩
  exact (hequiv P hPU).1.trans (hpieces P hPU.choose hPU.choose_spec)

/-- **Crux, `λ` limit — second case: some cocenter `≠ y`** (`6_double_successor_memo.tex:481-496`).
Then `Y_𝒫` is infinite (solvability). Split `𝒫 = 𝒫₀ ⊔ 𝒫₁` with
`𝒫₁ = {P | F↾P ≡ pgl ℓ_λ}`, `Y_i = {y_P | P ∈ 𝒫_i}`. Analyse `Y₁`:
* `Y₁ = ∅`: `Y = Y₀` infinite, `F ≤ ω k_{λ+1}` (`Gluingasupperbound_cor`) and
  `ω k_{λ+1} ≤ F⇂U` (`Intertwinereductionsforomegacentered`, `Y₀ ⊆ U`);
* `Y₁` infinite: `ℓ_{λ+1} = ω(pgl ℓ_λ) ≤ F` and `ℓ_{λ+1} ≤ F⇂U` (same two lemmas);
* `Y₁` finite nonempty: forces `Y₁ = {y}` (else solvability would give `pgl ℓ_λ ≤ k_{λ+1}`,
  contradicting Cor 4.10), so `Y₀` is infinite and two subcases:
  - `Y₀ \ V` finite for every clopen `V ∋ y` (i.e. `Y₀ → y`): conclude by
    `diagonal_for_lambda_plus_one` (`Diagonalforlambda+1`);
  - some clopen `V ∋ y` has `Y₀ \ V` infinite: split by cocenter `A₁ = A^{y}_𝒫`,
    `A₀ = A^{yᶜ}_𝒫`, and with `V' = U ∩ V`, `W = U ∖ V`,
    `F ≤ f₁ ⊕ f₀ ≤ pgl ℓ_λ ⊕ ω k_{λ+1} ≤ F⇂V' ⊕ F⇂W ≤ F⇂U`
    (`f₁ = F↾A₁` simple `≤ pgl ℓ_λ ≤ F⇂V'` via the `y`-piece; `f₀ = F↾A₀ ≤ ω k_{λ+1}`
    via `domainOver_reduces_omega_of_pieces_le`, and `ω k_{λ+1} ≤ F⇂W` since `Y₀ ∩ W` is infinite).

**Fully proved.** Subcase `Y₀ → y` is `solvable_limit_secondCase_diagonal`; the split subcase is
inline (using `block_simple_of_fine`, `domainOver_compl_eq`, `domainOver_reduces_omega_of_pieces_le`).
-/
lemma solvable_lambdaPlusOne_reduces_coRestrict_limit_secondCase
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U)
    (hne : ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y) :
    ScatFun.Reduces F (F.coRestrict U) := by
  classical
  -- Fineness / openness / `Y_𝒫` infinite are shared across the three `Y₁` branches.
  have hfine : hA.IsFine lam := hsolv.1
  have hUopen : IsOpen U := hU.isOpen
  have hYinf : hA.cocenterSet.Infinite :=
    (hsolv.cocenterSet_diff_singleton_infinite hne).mono Set.diff_subset
  -- Dispatch on `Y₁ = {y_P | F↾P ≡ pgl ℓ_λ}` (pieces equivalent to `succMaxFun lam`).
  set Y1 : Set Baire :=
    {z : Baire | ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = z ∧
        ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt)} with hY1def
  by_cases hY1inf :
      Y1.Infinite
  · -- `Y₁` infinite ⟹ `F ≡ ℓ_{λ+1} = ω(pgl ℓ_λ)` (`:483-485`). [PROVED branch.]
    exact solvable_limit_secondCase_succ_infinite lam hlim hlam_ne hlam_lt F hFrank hA hfine
      U hUopen hUcov _ hY1inf (fun _ => Iff.rfl)
  · rw [Set.not_infinite] at hY1inf
    by_cases hY1ne :
        Y1.Nonempty
    · -- `Y₁` finite nonempty ⟹ forces `Y₁ = {y}` (else solvability gives `pgl ℓ_λ ≤ k_{λ+1}`,
      -- contradicting Cor 4.10), then two subcases (`:487-496`):
      -- Step 1: force `Y₁ = {y}`.
      -- Core obstruction (`:487`, Cor 4.10 `cor:CenteredSucessor`):
      -- no cocenter in `Y1` can differ from `y`.
      have hcore : ∀ z ∈ Y1, z = y := by
        intro z hz
        by_contra hzy
        -- `z ∈ Y1`: a piece `P_z` with cocenter `z` and `F↾P_z ≡ pgl ℓ_λ`.
        rw [hY1def, Set.mem_setOf_eq] at hz
        obtain ⟨P, hP, hPz, hPequiv⟩ := hz
        have hPy : hA.cocenterOf hP ≠ y := by rw [hPz]; exact hzy
        -- `Y₁` finite ⟹ a clopen `V ∋ y` avoiding every *other* point of `Y₁`.
        set Y1_diff : Set Baire := Y1 \ {y} with hY1diffdef
        have hS : Y1_diff.Finite := hY1inf.subset Set.diff_subset
        obtain ⟨V, hVcl, hyV, hVdisj⟩ :=
          exists_clopen_nbhd_disjoint_finite hS
           (fun h => h.2 rfl)
        -- Solvability at `y` (clause 3): `P_z` reduces into some `Q` with cocenter `≠ y` inside `V`.
        obtain ⟨Q, hQ, hQy, hQV, hred⟩ := hsolv.2.2 P hP hPy V hVcl hyV
        -- `y_Q ∈ V`, `y_Q ≠ y`, `V ∩ (Y₁ \ {y}) = ∅` ⟹ `y_Q ∉ Y₁`.
        have hzQ_notin : hA.cocenterOf hQ ∉ Y1 := fun hmem =>
          Set.disjoint_left.mp hVdisj hQV (Set.mem_diff_singleton.mpr ⟨hmem, hQy⟩)
        -- Dichotomy: `y_Q ∉ Y₁` kills the `pgl ℓ_λ` case, so `F↾Q ≡ k_{λ+1} = minFun λ`.
        have hQmin : ScatFun.Equiv (F.restrict Q) (ScatFun.minFun lam hlam_lt) :=
          (piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine hQ).resolve_right
            (fun hEq => hzQ_notin (by rw [hY1def]; exact ⟨Q, hQ, rfl, hEq⟩))
        -- `pgl ℓ_λ ≡ F↾P_z ≤ F↾Q ≡ k_{λ+1}`  ⟹  `pgl ℓ_λ ≤ k_{λ+1}`.
        have hchain : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (ScatFun.minFun lam hlam_lt) :=
          hPequiv.2.trans (hred.trans hQmin.1)
        -- Contradiction with Cor 4.10 (`pglMaxFun_not_le_minFunPlusOne_limit`).
        exact pglMaxFun_not_le_minFunPlusOne_limit lam hlim hlam_ne hlam_lt
          (by rwa [ScatFun.reduces_iff, succMaxFun_func, ScatFun.minFun_func] at hchain)
      -- `y ∈ Y1`: the nonempty witness must equal `y` by `hcore`.
      have hy_mem : y ∈ Y1 := by
        obtain ⟨z, hz⟩ := hY1ne
        exact hcore z hz ▸ hz
      -- `Y1 = {y}`.
      have hY1eq : Y1 = {y} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hy_mem, hcore⟩
      have hY0inf : (hA.cocenterSet \ {y}).Infinite :=
        hsolv.cocenterSet_diff_singleton_infinite hne
      --   * `Y₀ → y`: conclude by `diagonal_for_lambda_plus_one`;
      --   * some clopen `W ∌ y` catches infinitely many of `Y₀`: with `V = U ∖ W`,
      --     `F ≤ pgl ℓ_λ ⊕ ω k_{λ+1} ≤ F⇂V ⊕ F⇂W ≤ F⇂U`.
      by_cases hconv :
          ∀ V : Set Baire, IsClopen V → y ∈ V → ((hA.cocenterSet \ {y}) \ V).Finite
      · -- Subcase 1: `Y₀ → y` (every clopen nbhd of `y` misses all but finitely many of `Y₀`).
        -- Conclude by `diagonal_for_lambda_plus_one` (via `solvable_limit_secondCase_diagonal`).
        refine solvable_limit_secondCase_diagonal lam hlim hlam_ne hlam_lt hFG F hFrank hA hfine
          hsolv.2.1 ?_ ?_ hY0inf hconv U hU hUcov
        · -- hdistPiece: the `Y₁`-witness has cocenter `y` (by `hcore`) and `≡ succMaxFun`.
          obtain ⟨z, hz⟩ := hY1ne
          have hzy : z = y := hcore z hz
          rw [hY1def, Set.mem_setOf_eq] at hz
          obtain ⟨P, hP, hPz, hPeq⟩ := hz
          exact ⟨P, hP, hPz.trans hzy, hPeq⟩
        · -- hAway: an off-`y` piece can't be `≡ succMaxFun` (else its cocenter ∈ Y₁ = {y}).
          intro P hP hPy
          refine (piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine
            hP).resolve_right (fun hEq => hPy ?_)
          exact hcore _ (by rw [hY1def]; exact ⟨P, hP, rfl, hEq⟩)
      · -- Subcase 2: some clopen `V ∋ y` has `Y₀ \ V` infinite.
        push_neg at hconv
        obtain ⟨V, hVcl, hyV, hVinf⟩ := hconv
        -- `hVinf : (Y₀ \ V).Infinite` (defeq). Split `U = V' ⊔ W`, `V' = U ∩ V ∋ y`, `W = U ∖ V ∌ y`.
        -- Derived facts (as in subcase 1): the `y`-piece `≡ pgl ℓ_λ`, and off-`y` pieces `≡ k_{λ+1}`.
        obtain ⟨Pd, hPd, hPdy, hPdeq⟩ : ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
            hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (ScatFun.succMaxFun lam hlam_lt) := by
          obtain ⟨z, hz⟩ := hY1ne
          have hzy : z = y := hcore z hz
          rw [hY1def, Set.mem_setOf_eq] at hz
          obtain ⟨P, hP, hPz, hPeq⟩ := hz
          exact ⟨P, hP, hPz.trans hzy, hPeq⟩
        have hAway : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
            ScatFun.Equiv (F.restrict P) (ScatFun.minFun lam hlam_lt) := by
          intro P hP hPy
          refine (piece_equiv_minFun_or_succMaxFun lam hlim hlam_ne hlam_lt F hFrank hA hfine
            hP).resolve_right (fun hEq => hPy ?_)
          exact hcore _ (by rw [hY1def]; exact ⟨P, hP, rfl, hEq⟩)
        -- The clopen split of `U`.
        have hyU : y ∈ U := hUcov hsolv.2.1
        set W : Set Baire := U \ V with hWdef
        set V' : Set Baire := U ∩ V with hV'def
        have hWcl : IsClopen W := hU.diff hVcl
        have hV'cl : IsClopen V' := hU.inter hVcl
        have hyV' : y ∈ V' := ⟨hyU, hyV⟩
        have hV'U : V' ⊆ U := Set.inter_subset_left
        have hWU : W ⊆ U := Set.diff_subset
        have hdisjV'W : Disjoint V' W := Set.disjoint_left.mpr fun z hz1 hz2 => hz2.2 hz1.2
        -- `f₁ = F↾A^{y}_𝒫`: simple of rank `λ+1`, so `≤ pgl ℓ_λ`; and `pgl ℓ_λ ≤ F⇂V'` via the
        -- `y`-piece `Pd` (cocenter `y ∈ V'`).
        have hf1 := block_simple_of_fine lam hlam_lt F hFrank hA hfine hsolv.2.1
        have hmax_V' : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.coRestrict V') :=
          hPdeq.2.trans (piece_reduces_coRestrict_of_cocenter_mem F hA hV'cl.isOpen hPd
            (by rw [hPdy]; exact hyV'))
        have hf1_V' : ScatFun.Reduces (F.restrict (hA.domainOver {y})) (F.coRestrict V') :=
          (simple_reduces_succMaxFun lam hlam_lt _ hf1.2.1 hf1.1).trans hmax_V'
        -- `f₀ = F↾A^{yᶜ}_𝒫`: every piece `≡ k_{λ+1}`, so `≤ ω k_{λ+1}`; and `ω k_{λ+1} ≤ F⇂W`
        -- (`Y₀ ∩ W = Y₀ \ V` infinite).
        have hf0_omega : ScatFun.Reduces (F.restrict ((hA.domainOver {y})ᶜ))
            (ScatFun.omega (ScatFun.minFun lam hlam_lt)) := by
          rw [hA.domainOver_compl_eq]
          exact domainOver_reduces_omega_of_pieces_le F hA {y}ᶜ (ScatFun.minFun lam hlam_lt)
            (fun P hP hmem =>
              (hAway P hP (fun h => hmem (Set.mem_singleton_iff.mpr h))).1)
        have homega_W : ScatFun.Reduces (ScatFun.omega (ScatFun.minFun lam hlam_lt))
            (F.coRestrict W) := by
          refine omega_minFun_reduces_coRestrict_of_infinite_cocenters lam hlam_lt F hA W
            hWcl.isOpen ((hA.cocenterSet \ {y}) \ V) hVinf ?_ ?_
          · exact fun z hz => ⟨hUcov hz.1.1, hz.2⟩
          · intro z hz
            obtain ⟨⟨P, hP⟩, hPz⟩ := hz.1.1
            have hPz' : hA.cocenterOf hP = z := hPz
            refine ⟨P, hP, hPz', hAway P hP ?_⟩
            rw [hPz']; exact (Set.mem_diff_singleton.mp hz.1).2
        have hf0_W : ScatFun.Reduces (F.restrict ((hA.domainOver {y})ᶜ)) (F.coRestrict W) :=
          hf0_omega.trans homega_W
        -- Assemble: `F ≤ f₁ ⊕ f₀ ≤ F⇂V' ⊕ F⇂W ≤ F⇂U`.
        refine (reduces_glBin_restrict_compl F (hA.domainOver {y})
          (hA.domainOver_isClopen {y})).trans ?_
        exact ScatFun.reduces_glBin_coRestrict_of_disjoint _ _ hV'cl hWcl hV'U hWU hdisjV'W
          hf1_V' hf0_W

    · -- `Y₁` empty ⟹ `F ≤ ω k_{λ+1} ≤ F⇂U` (`:481-482`). [PROVED branch.]
      rw [Set.not_nonempty_iff_eq_empty] at hY1ne
      refine solvable_limit_secondCase_succ_empty lam hlim hlam_ne hlam_lt F hFrank hA hfine
        U hUopen hUcov hYinf ?_
      rintro ⟨P, hP, hPeq⟩
      have hmem : hA.cocenterOf hP ∈ Y1 := by
        rw [hY1def]; exact ⟨P, hP, rfl, hPeq⟩
      rw [hY1ne] at hmem
      simp at hmem

/-- **Crux, `λ` limit case** (`6_double_successor_memo.tex:470-497`) — dispatch on whether all
cocenters equal `y`, delegating to
`solvable_lambdaPlusOne_reduces_coRestrict_limit_firstCase` /
`solvable_lambdaPlusOne_reduces_coRestrict_limit_secondCase`. **Fully proved** (both dispatch
targets are complete). -/
lemma solvable_lambdaPlusOne_reduces_coRestrict_limit
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0)
    (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y)
    (U : Set Baire) (hU : IsClopen U) (hUcov : hA.cocenterSet ⊆ U) :
    ScatFun.Reduces F (F.coRestrict U) := by
  by_cases hcoin : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y
  · exact solvable_lambdaPlusOne_reduces_coRestrict_limit_firstCase lam hlim hlam_ne hlam_lt
      hFG F hFrank hA hsolv U hU hUcov hcoin
  · push_neg at hcoin
    exact solvable_lambdaPlusOne_reduces_coRestrict_limit_secondCase lam hlim hlam_ne hlam_lt
      hFG F hFrank hA hsolv U hU hUcov hcoin

lemma solvable_lambdaPlusOne_reduces_coRestrict
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam ∨ lam = 0) (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y) :
    ∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
      ScatFun.Reduces F (F.coRestrict U) := by
  intro U hU hUcov
  by_cases h0 : lam = 0
  · subst h0
    exact solvable_lambdaPlusOne_reduces_coRestrict_zero F (by rw [hFrank])
      hA hsolv U hU hUcov
  · exact solvable_lambdaPlusOne_reduces_coRestrict_limit lam (hlim.resolve_right h0) h0
      hlam_lt hFG F hFrank hA hsolv U hU hUcov

/-- **Proposition `solvablelambda+1`** (`6_double_successor_memo.tex:456-460`) — the memoir's
`S(λ)` (`:438-441`) for `λ` limit or null. Let `λ < ω₁` be limit or `0`, assume `FG(≤λ)`
(`FGBelow (λ+1)`), and let `F : ScatFun` with `CB(F) = λ+1` be solvable at `y` with `Part`.
Then there is `g ∈ FinGl 𝒢_{λ+1}` with `F ≤ g` and `g ≤ F⇂U` for every clopen `U ⊇ Y_𝒫`.

## Provided solution (`6_double_successor_memo.tex:462-497`)

*`λ = 0`* (`:464-468`): `F` is locally constant, each piece constant, so `im F = Y_𝒫 ⊆ U`
and `F = F⇂U`; conclude by `𝒞_{≤1}` finite generation (`cLeOne_finitely_generated`,
`CenteredFunctions/FinitenessHelpers.lean`, proved).

*`λ` limit* (`:470-497`): by `centeredSuccessor` (Cor 4.10, `CenteredFunctions/Finiteness.lean`,
proved) every piece is `≡ k_{λ+1}` (`minFun λ`) or `≡ pgl ℓ_λ` (`succMaxFun λ`). Cases:
* all cocenters equal `y` (`:476-477`): `F` is simple (`simpleIffCoincidenceOfCocenters`,
  Prop 4.11) hence `F ≤ pgl ℓ_λ`; the corestriction bound comes from centeredness of a
  `pgl ℓ_λ`-piece, or — all pieces `≡ k_{λ+1}` — from `F` not being a lump of itself (`Part`
  is fine!), giving a high ray of rank `λ` inside `U` and
  `g = k_{λ+1} ⊕ ℓ_λ ≤ F⇂V ⊕ F⇂(ray) ≤ F⇂U`;
* some cocenter `≠ y`, so `Y_𝒫` infinite (`:481-496`): split `𝒫 = 𝒫₀ ⊔ 𝒫₁` by piece class.
  `Y₁` empty ⟹ `F ≤ ω k_{λ+1} ≤ F⇂U`; `Y₁` infinite ⟹ `F ≡ ℓ_{λ+1} = ω(pgl ℓ_λ)`;
  `Y₁` finite nonempty forces `Y₁ = {y}` (else solvability would give
  `pgl ℓ_λ ≤ k_{λ+1}`, contradicting Cor 4.10) and two subcases: cocenters of `𝒫₀`
  accumulate only at `y` — conclude by `diagonal_for_lambda_plus_one`
  (`ScatFun/PreciseStructure/DiagonalForLambdaPlusOne.lean`, proved) — or some clopen `W ∌ y`
  catches infinitely many, and `F ≤ pgl ℓ_λ ⊕ ω k_{λ+1} ≤ F⇂V ⊕ F⇂W ≤ F⇂U`.

All reduction-combination steps are `Gluingasupperbound`(`_cor`)/
`intertwine_reductions_omega_centered`, available and proved. -/
theorem solvable_lambdaPlusOne
    (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam ∨ lam = 0) (hlam_lt : lam < omega1)
    (hFG : ScatFun.FGBelow (lam + 1))
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt lam y) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (lam + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
          ScatFun.Reduces g (F.coRestrict U) :=
  ⟨F, solvable_lambdaPlusOne_mem lam hlim hlam_lt hFG F hFrank,
    ContinuouslyReduces.refl F.func,
    solvable_lambdaPlusOne_reduces_coRestrict lam hlim hlam_lt hFG F hFrank hA hsolv⟩

/-! ## Finite generation for solvable functions (`6_double_successor_memo.tex:503-544`) -/

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- **(memoir §6.4, `:509-511`)** A `ScatFun` `g` is *reducible infinitely often off `y`*
(relative to the `c`-partition `hA` with distinguished cocenter `y`) if some clopen `V ∋ y`
leaves infinitely many pieces, whose cocenter lies *outside* `V`, into which `g` reduces.
This is the predicate carving out `H ⊆ G` in the `H`/`D` split of
`finiteGenerationForSolvable_split`. -/
def ReducibleInfinitelyOftenOffY (hA : F.IsCPartition Part) (y : Baire) (g : ScatFun) : Prop :=
  ∃ V : Set Baire, IsClopen V ∧ y ∈ V ∧
    {z : Baire | z ∈ hA.cocenterSet ∧ z ∉ V ∧
      ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = z ∧ ScatFun.Reduces g (F.restrict P)}.Infinite

/-- **(b) `H` is `≤`-downward closed** (`6_double_successor_memo.tex:511`). If `g' ≤ g` and `g`
is reducible infinitely often off `y`, then so is `g'`: the *same* clopen `V` works, because
`g' ≤ g ≤ F↾P` for every witnessing piece `P`, so the (infinite) witness set only grows. -/
lemma reducibleInfinitelyOftenOffY_downward (hA : F.IsCPartition Part) (y : Baire)
    {g g' : ScatFun} (hle : ScatFun.Reduces g' g)
    (hg : hA.ReducibleInfinitelyOftenOffY y g) :
    hA.ReducibleInfinitelyOftenOffY y g' := by
  obtain ⟨V, hVcl, hyV, hinf⟩ := hg
  refine ⟨V, hVcl, hyV, hinf.mono ?_⟩
  rintro z ⟨hzc, hzV, P, hP, hPz, hgP⟩
  exact ⟨hzc, hzV, P, hP, hPz, hle.trans hgP⟩

end ScatFun.IsCPartition

/- **Overview of `FiniteGenerationForSolvable`** (`6_double_successor_memo.tex:503-506`) — the
memoir's `S(α+1)`, split below into `_split`/`_glue`. Let `α < ω₁`, assume `FG(≤α+1)`
(`FGBelow (α+1+1)`), and let `F : ScatFun` with `CB(F) = α+2` be solvable at `y` with `Part`.
Then there is `g ∈ FinGl 𝒢_{α+2}` with `F ≤ g` and `g ≤ F⇂U` for every clopen `U ⊇ Y_𝒫`.

## Provided solution (`6_double_successor_memo.tex:507-544`)

Choose representatives `G ⊆ 𝒞_{α+2}` for `{F↾P | P ∈ 𝒫^{≠y}}` (`FGconsequences` item 5 again).
Call `g' ∈ G` *reducible infinitely often off `y`* if some clopen `V ∋ y` has
`{y_P | y_P ∉ V, g' ≤ F↾P}` infinite; let `H ⊆ G` be those (note `H` is `≤`-downward closed
in `G`) and `D = G \ H`. Split `𝒫 = 𝒫_H ⊔ 𝒫_M` accordingly. Then:

* `F↾(⋃𝒫_M)` with `𝒫_M` is **strongly solvable** at `y`: clause 1 by pigeonhole on the
  finite `D` (any infinite escape would put some `g' ∈ D` in `H`), clause 2 from solvability
  of `F` plus downward closure of `H` (`:519-525`). The **Diagonal Theorem**
  (`diagonalTheorem`, `Partitions/Diagonal.lean`) then gives `g_M ∈ FinGl 𝒢_{α+2}` with
  `F↾(⋃𝒫_M) ≤ g_M ≤ F⇂V` for every clopen `V ∋ y`.
* Choosing one clopen `V ∋ y` making all the `H`-witness sets infinite simultaneously
  (`H` finite), `F↾(⋃𝒫_H) ≤ ω H ≤ F⇂(U \ V)` by
  `intertwine_reductions_omega_centered` (`:533-538`).
* Assemble: `F ≤ ω H ⊕ g_M ≤ F⇂(U \ V) ⊕ F⇂(V ∩ U) ≤ F⇂U` (`:540-543`), with
  `ω H ⊕ g_M ∈ FinGl 𝒢_{α+2}` by the `genStep` `ω`-image clause.

## Formalization notes

The strongly-solvable restriction step needs the same partition-transport plumbing as
`solvableDecomposition` (`cPartition_restrict_transport`, `Fine.lean`); `𝒫_M`-fineness is
again "any sub-partition lump is a `𝒫`-lump". -/

/-- **`ω g` absorbs binary self-gluing**: `(ω g) ⊕ (ω g) ≤ ω g`. Used in
`finiteGenerationForSolvable_split`'s `λ+1` branch, where `f_M` is folded into `hH = ω H`: once
`F↾A_Mᶜ ≤ ω H` and `f_M = F↾A_M ≤ ω H`, the clopen split gives `F ≤ (ω H) ⊕ (ω H)`, and this
lemma collapses it to `F ≤ ω H`. Proof: `(ω g) ⊕ (ω g) ≡
glList [ω g, ω g] ≤ ω (ω g) ≡ ω g` (`glList_reduces_omega_of_forall` with the two slots reducing
to `ω g` by reflexivity, then `omega_omega_equiv`). -/
lemma ScatFun.glBin_omega_self_reduces (g : ScatFun) :
    ScatFun.Reduces (ScatFun.glBin (ScatFun.omega g) (ScatFun.omega g)) (ScatFun.omega g) := by
  refine (ScatFun.finGl_glBin_equiv_glList _ _).1.trans ?_
  refine (ScatFun.glList_reduces_omega_of_forall (g := ScatFun.omega g) ?_).trans
    (ScatFun.omega_omega_equiv g).1
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact ContinuouslyReduces.refl _

/-- **`FinGl`-generator lift across double successors sharing a limit part.** For `β ≤ α` with
`β.limitPart = α.limitPart`, every element of `FinGl (Generators (β+1+1))` also lies in
`FinGl (Generators (α+1+1))`. Both double successors unfold to `α.limitPart + (natPart + 2)`, so
this is `Generators_mono_of_le` (the offsets satisfy `β.natPart + 2 ≤ α.natPart + 2`) followed by
`FinGl_mono_of_subset`. Lets the double-successor branch of `finiteGenerationForSolvable_split`
lift the `gM` the Diagonal Theorem produces at rank `β+1+1` up to the ambient `α+1+1`. -/
lemma finGl_generators_doubleSucc_mono {α β : Ordinal.{0}}
    (hβα : β ≤ α) (hβlim : β.limitPart = α.limitPart) :
    ScatFun.FinGl (ScatFun.Generators (β + 1 + 1)).toFinFun ⊆
      ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
  have hlim : Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 :=
    Ordinal.limitPart_isLimit_or_zero α
  have add_two : ∀ x : Ordinal.{0}, x + 1 + 1 = x + 2 := fun x => by rw [add_assoc]; norm_num
  have hβeq : β + 1 + 1 = α.limitPart + ((β.natPart + 2 : ℕ) : Ordinal) := by
    conv_lhs => rw [Ordinal.eq_limitPart_add_natPart β]
    rw [hβlim, add_two, add_assoc]; push_cast; ring_nf
  have hαeq : α + 1 + 1 = α.limitPart + ((α.natPart + 2 : ℕ) : Ordinal) := by
    conv_lhs => rw [Ordinal.eq_limitPart_add_natPart α]
    rw [add_two, add_assoc]; push_cast; ring_nf
  have hnat : β.natPart ≤ α.natPart := by
    have hle : α.limitPart + (β.natPart : Ordinal) ≤ α.limitPart + (α.natPart : Ordinal) := by
      calc α.limitPart + (β.natPart : Ordinal)
          = β := by rw [← hβlim]; exact (Ordinal.eq_limitPart_add_natPart β).symm
        _ ≤ α := hβα
        _ = α.limitPart + (α.natPart : Ordinal) := Ordinal.eq_limitPart_add_natPart α
    exact_mod_cast le_of_add_le_add_left hle
  rw [hβeq, hαeq]
  exact ScatFun.FinGl_mono_of_subset (ScatFun.Generators_mono_of_le hlim (by omega))


/-- **The `λ+1` fold** (`6_double_successor_memo.tex`, the `CB(f_M) = λ+1` sub-case of the
`M`-block): if the `𝒫_M`-restriction `F↾A_M` has rank exactly `λ+1`, then `F↾A_M ≤ ω H`, so
`f_M` can be *folded* into the `H`-branch instead of getting its own diagonal generator.

The chain (memoir): `f_M ≤ MaxFun(λ+1) = ω(succMaxFun λ) ≤ ω h ≤ ω H`, where `h ∈ H` is a
representative of rank `α+2`. Such an `h` exists because — with all cocenter-`y` pieces of rank
`λ+1` (`hcase`, itself a consequence of `CB(f_M) = λ+1`) — some cocenter-`≠y` piece attains the
top rank `α+2` (`exists_piece_cocenter_ne_rank_doubleSucc`); that piece cannot be in `𝒫_M` (whose
pieces have rank `λ+1`), so it lies in `𝒫_H` and thus has a representative `h ∈ H` of the same
rank (`hHtop`). The two hypotheses `hcase`/`hHtop` are exactly what the split context provides. -/
lemma reduces_omega_glList_of_rank_limitPart_succ
    (α : Ordinal.{0}) (hα : α < omega1)
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1)
    (A_M : Set ↑F.domain) (H : Finset ScatFun)
    (hm1 : CBRank (F.restrict A_M).func = α.limitPart + 1)
    (hHtop : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      CBRank (F.restrict P).func = α + 1 + 1 → ∃ h ∈ H, (F.restrict P).Equiv h) :
    ScatFun.Reduces (F.restrict A_M) (ScatFun.omega (ScatFun.glList H.toList)) := by
  -- A cocenter-`≠y` piece `P₀` attains the top rank `α+2`; route it to a representative `h ∈ H`.
  obtain ⟨P₀, hP₀, hP₀ne, hP₀rank⟩ :=
    exists_piece_cocenter_ne_rank_doubleSucc α F hFrank hA hcase
  obtain ⟨h, hhH, hP₀h⟩ := hHtop P₀ hP₀ hP₀ne hP₀rank
  have hheq : CBRank h.func = α + 1 + 1 := (cbRank_eq_of_equiv hP₀h).symm.trans hP₀rank
  -- `λ`-side ordinal facts.
  have hlamle : α.limitPart ≤ α := by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  have hlamlt : α.limitPart < omega1 := lt_of_le_of_lt hlamle hα
  have hlam1lt : α.limitPart + 1 < omega1 := by simpa using omega1_add_nat α.limitPart hlamlt 1
  have hlim : Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 :=
    Ordinal.limitPart_isLimit_or_zero α
  have hrankh : Order.succ (Order.succ α.limitPart) ≤ CBRank h.func := by
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, hheq]
    gcongr
  -- The reduction chain.
  have h1 : ScatFun.Reduces (F.restrict A_M) (ScatFun.maxFun (α.limitPart + 1) hlam1lt) :=
    ScatFun.reduces_maxFun_of_rank_le _ _ _ (le_of_eq hm1)
  have h2 : ScatFun.Reduces (ScatFun.maxFun (α.limitPart + 1) hlam1lt)
      (ScatFun.omega (ScatFun.succMaxFun α.limitPart hlamlt)) :=
    ScatFun.maxFun_reduces_omega_succMaxFun α.limitPart hlamlt hlam1lt
  have h3 : ScatFun.Reduces (ScatFun.succMaxFun α.limitPart hlamlt) h :=
    consequencesGeneralStructure_succMaxFun_le α.limitPart hlamlt hlim h hrankh
  have h4 : ScatFun.Reduces (ScatFun.omega (ScatFun.succMaxFun α.limitPart hlamlt))
      (ScatFun.omega (ScatFun.glList H.toList)) :=
    ScatFun.omega_reduces_of_reduces (h3.trans (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hhH)))
  exact h1.trans (h2.trans h4)

/-- **Sub-lemma 1 of `finiteGenerationForSolvable`** — the `H`/`D`/`𝒫_M`-split
(`6_double_successor_memo.tex:509-538`), the genuinely new content. Choosing representatives
`G ⊆ 𝒞_{α+2}` for `{F↾P | P ∈ 𝒫^{≠y}}` (`FGconsequences` item 5,
`exists_pglFinset_decomp_of_centered_doubleSucc`), split `G = H ⊔ D` where `H` is the set of
`g` *reducible infinitely often off `y`* (some clopen `V ∋ y` has `{y_P | y_P ∉ V, g ≤ F↾P}`
infinite; `H` is `≤`-downward closed). Split `𝒫 = 𝒫_H ⊔ 𝒫_M` accordingly, `A_M = ⋃ 𝒫_M`. Then:

* `F↾A_M` with `𝒫_M` is **strongly solvable at `y`** (clause 1 by pigeonhole on the finite `D`,
  clause 2 from solvability of `F` + downward closure of `H`), so the **Diagonal Theorem**
  (`diagonalTheorem`) gives `gM ∈ FinGl 𝒢_{α+2}` with `F↾A_M ≤ gM ≤ F↾A_M⇂W ≤ F⇂W` for every
  clopen `W ∋ y`;
* choosing a single clopen `V ∋ y` making all `H`-witness sets infinite (`H` finite),
  `F↾A_Mᶜ ≤ ω H =: hH ∈ FinGl 𝒢_{α+2}` with `hH ≤ F⇂(U∖V)` for every clopen `U ⊇ Y_𝒫`
  (`Gluingasupperbound` + `intertwine_reductions_omega_centered`).

Under strategy (Z) this lemma returns the final `∃ g ∈ FinGl 𝒢_{α+2}, F ≤ g ∧ ∀ U ⊇ Y_𝒫, g ≤ F⇂U`
conclusion directly: it case-splits on `CB(f_M)` (fold `f_M` into `ω H` when `= λ+1`, else a
diagonal `gM` glued as `hH ⊕ gM`), absorbing what used to be a separate `_glue` assembly.
 -/
lemma finiteGenerationForSolvable_split
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt α.limitPart y) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
          ScatFun.Reduces g (F.coRestrict U) := by
  classical
  -- ==========================================================================
  -- Step 0 (shared core, `6_double_successor_memo.tex:509-517`, `:531`):
  -- representatives `G`, the `H`/`D` split, the piece split `𝒫 = 𝒫_H ⊔ 𝒫_M`,
  -- the clopen `M`-domain `A_M`, and a single clopen `V ∋ y`. All the data the
  -- three sub-goals (d)/(f)/(g) consume, built once with its defining properties.
  -- ==========================================================================
  -- Fineness (bundled in `hsolv`) gives the rank lower bound `λ < CB(F↾P)`.
  have hfineRank : ∀ P ∈ Part, α.limitPart < CBRank (F.restrict P).func := hsolv.1.2
  have hlamle : α.limitPart ≤ α := by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  -- (a) `G ⊆ 𝒞_{α+2}` : representatives for `{F↾P | P ∈ 𝒫^{≠y}}` (the off-`y` pieces),
  --     `hGrep`/`hGreal` the two matching directions
  --     (`diagonalTheorem_secondCase_representatives_D`, memoir's `FGconsequences`).
  obtain ⟨G, hGsub, hGrep, hGreal⟩ :=
    diagonalTheorem_secondCase_representatives_D α hα hFG F hFrank hA (y := y) hfineRank
  -- (b) `H := {g ∈ G | g reducible infinitely often off y}` (`≤`-downward closed,
  --     `reducibleInfinitelyOftenOffY_downward`); `D := G \ H` (not needed here; for (d)).
  set H : Finset ScatFun :=
    G.filter (fun g => hA.ReducibleInfinitelyOftenOffY y g) with hHdef
  have hHsub : H ⊆ ScatFun.Centered (α + 1 + 1) :=
    (Finset.filter_subset _ _).trans hGsub
  -- The induced piece split. `𝒫_H` = off-`y` pieces whose class lies in `H`; `𝒫_M = 𝒫 \ 𝒫_H`.
  set PH : Set (Set ↑F.domain) :=
    {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ≠ y ∧ ∃ h ∈ H, ScatFun.Equiv (F.restrict P) h}
    with hPHdef
  set PM : Set (Set ↑F.domain) := Part \ PH with hPMdef
  have hPHsubPart : PH ⊆ Part := fun P hP => hP.choose
  have hPMsubPart : PM ⊆ Part := Set.diff_subset
  -- `A_M := ⋃ 𝒫_M`, clopen as a sub-union of `c`-partition pieces.
  set A_M : Set ↑F.domain := ⋃₀ PM with hAMdef
  have hA_M : IsClopen A_M := hA.sUnion_subfamily_isClopen hPMsubPart
  -- `A_Mᶜ = ⋃ 𝒫_H` (the two sub-unions partition the domain).
  have hAMcompl : A_Mᶜ = ⋃₀ PH := by
    rw [hAMdef]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sUnion, not_exists, not_and]
    constructor
    · intro hx
      obtain ⟨P, hPmem, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
        Set.mem_sUnion.mp (hA.sUnion_eq.symm ▸ Set.mem_univ x)
      by_cases hPH : P ∈ PH
      · exact ⟨P, hPH, hxP⟩
      · exact absurd hxP (hx P ⟨hPmem, hPH⟩)
    · rintro ⟨P, hPPH, hxP⟩ Q hQPM hxQ
      rcases eq_or_ne P Q with rfl | hne
      · exact hQPM.2 hPPH
      · exact Set.disjoint_left.mp
          (hA.pairwiseDisjoint (hPHsubPart hPPH) (hPMsubPart hQPM) hne) hxP hxQ
  -- (c) A single clopen `V ∋ y` making every `H`-witness set infinite (`H` finite):
  --     take `V := ⋂_{g ∈ H} V_g`, shrinking each per-`g` witness `V_g` only enlarges
  --     its (infinite) witness set `{z ∉ V, g ≤ F↾P}`.
  have hHwit : ∀ g ∈ H, ∃ Vg : Set Baire, IsClopen Vg ∧ y ∈ Vg ∧
      {z : Baire | z ∈ hA.cocenterSet ∧ z ∉ Vg ∧
        ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
          hA.cocenterOf hP = z ∧ ScatFun.Reduces g (F.restrict P)}.Infinite :=
    fun g hg => (Finset.mem_filter.mp hg).2
  choose! Vf hVfcl hVfy hVfinf using hHwit
  set V : Set Baire := ⋂ g ∈ H, Vf g with hVdef
  have hVcl : IsClopen V := isClopen_biInter_finset (fun g hg => hVfcl g hg)
  have hyV : y ∈ V := Set.mem_biInter (fun g hg => hVfy g hg)
  have hVsub : ∀ g ∈ H, V ⊆ Vf g := fun g hg => Set.biInter_subset_of_mem hg
  -- ==========================================================================
  -- (d) (`6_double_successor_memo.tex:519-529`): the induced `𝒫_M`-partition on
  -- `f_M := F.restrict A_M` is **strongly solvable at `y`** (`hSS`). All rank-agnostic —
  -- built once here, up front, so both rank branches below can consume it. The `α+2`-rank
  -- Diagonal Theorem is applied only in the double-successor branch (e); in the `λ+1` branch
  -- `f_M` is instead folded into `hH = ω H` (`glBin_omega_self_reduces`,
  -- `reduces_omega_glList_of_rank_limitPart_succ`).
  -- ==========================================================================
  set f_M := F.restrict A_M with hfMdef
  set PM' : Set (Set ↑f_M.domain) :=
  (fun P : Set ↑F.domain => {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P}) '' PM
  with hPM'def
  have hA_M' : f_M.IsCPartition PM' := by
    rw [hPM'def]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- countable: image of the countable subfamily PM ⊆ Part
      exact (hA.countable.mono hPMsubPart).image _
    · -- clopen: preimage of the clopen ambient piece under the continuous restrictEquiv
      rintro _ ⟨P, hP, rfl⟩
      exact (hA.isClopen P (hPMsubPart hP)).preimage
        (continuous_subtype_val.comp (F.restrictEquiv A_M).continuous)
    · -- pairwise disjoint: inherited from PM ⊆ Part
      rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      have hPQ : P ≠ Q := fun h => hne (by rw [h])
      have hdisj := hA.pairwiseDisjoint (hPMsubPart hP) (hPMsubPart hQ) hPQ
      simp only [Function.onFun, id] at hdisj ⊢
      rw [Set.disjoint_left] at hdisj ⊢
      intro w hwP hwQ
      exact hdisj hwP hwQ
    · -- cover: every w of f_M.domain lands (via restrictEquiv) in A_M = ⋃₀ PM
      ext w
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      have hwA : (F.restrictEquiv A_M w : ↑F.domain) ∈ ⋃₀ PM := (F.restrictEquiv A_M w).2
      obtain ⟨P, hP, hwP⟩ := hwA
      exact ⟨_, ⟨P, hP, rfl⟩, hwP⟩
    · -- centered: each PM'-piece re-realizes its ambient PM-piece (restrict_restrict_equiv)
      rintro _ ⟨P, hP, rfl⟩
      have hsub : P ⊆ A_M := hAMdef ▸ Set.subset_sUnion_of_mem hP
      exact isCentered_of_equiv (hA.centered P (hPMsubPart hP))
        (ScatFun.restrict_restrict_equiv F A_M P hsub)
  -- Transport data for the 𝒫_M-restriction (subfamily PM, block A_M = ⋃₀ PM).
  have hsubP : ∀ P ∈ PM, P ⊆ A_M := fun P hP => hAMdef ▸ Set.subset_sUnion_of_mem hP
  have hequiv : ∀ P ∈ PM,
      ScatFun.Equiv (f_M.restrict {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P})
        (F.restrict P) :=
    fun P hP => ScatFun.restrict_restrict_equiv F A_M P (hsubP P hP)
  have hcoc : ∀ (P : Set ↑F.domain) (hP : P ∈ PM)
      (h' : {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P} ∈ PM'),
      hA_M'.cocenterOf h' = hA.cocenterOf (hPMsubPart hP) :=
    fun P hP h' => ScatFun.cocenter_restrict_restrict_eq F A_M P (hsubP P hP) _ _
  have hfineM : hA_M'.IsFine α.limitPart := by
    -- Shared transport data (subfamily = PM, block = A_M), mirroring
    -- `solvableDecomposition_transport`'s `hequiv`/`hcoc`.
    have hsubP : ∀ P ∈ PM, P ⊆ A_M := fun P hP => hAMdef ▸ Set.subset_sUnion_of_mem hP
    have hequiv : ∀ P ∈ PM,
        ScatFun.Equiv (f_M.restrict {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P})
          (F.restrict P) :=
      fun P hP => ScatFun.restrict_restrict_equiv F A_M P (hsubP P hP)
    have hcoc : ∀ (P : Set ↑F.domain) (hP : P ∈ PM)
        (h' : {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P} ∈ PM'),
        hA_M'.cocenterOf h' = hA.cocenterOf (hPMsubPart hP) :=
      fun P hP h' => ScatFun.cocenter_restrict_restrict_eq F A_M P (hsubP P hP) _ _
    constructor
    · -- No lumps: a `𝒫_M`-lump lifts to a `𝒫`-lump — the sub-block is the full ambient
      --   block (uniform PM/PH membership) or empty (regular automatically).
      rintro g z ⟨hz, hgcent, hirr⟩
      -- `z` is an ambient (`𝒫`) cocenter.
      have hzamb : z ∈ hA.cocenterSet := by
        obtain ⟨⟨P', hP'⟩, hP'coc⟩ := hz
        have hP'coc' : hA_M'.cocenterOf hP' = z := hP'coc
        obtain ⟨P, hP, hSP⟩ := id hP'
        subst hSP
        rw [hcoc P hP hP'] at hP'coc'
        exact ⟨⟨P, hPMsubPart hP⟩, hP'coc'⟩
      -- Ambient `(g,z)`-block is `𝒲`-regular (no `𝒫`-lump, from `hsolv`).
      have hreg : IsOmegaRegularAt (hA.piece g z) z := by
        by_contra hnreg
        exact hsolv.1.1 g z ⟨hzamb, hgcent, hnreg⟩
      -- The `𝒫_M`-block re-realizes the ambient block ∩ `𝒫_M`.
      have hblocks : ⋃₀ hA_M'.blockPieces g z
          = {w : ↑f_M.domain |
              (F.restrictEquiv A_M w : ↑F.domain) ∈ ⋃₀ (hA.blockPieces g z ∩ PM)} := by
        ext w
        constructor
        · rintro ⟨P', hP'block, hwP'⟩
          obtain ⟨hP'mem, hP'eq, hP'coc⟩ := hP'block
          obtain ⟨P, hP, hSP⟩ := id hP'mem
          subst hSP
          rw [hcoc P hP hP'mem] at hP'coc
          exact ⟨P, ⟨⟨hPMsubPart hP, (hequiv P hP).symm.trans hP'eq, hP'coc⟩, hP⟩, hwP'⟩
        · rintro ⟨P, ⟨hPblk, hPPM⟩, hwP⟩
          obtain ⟨hPmem, hPg, hPcoc⟩ := hPblk
          have hSPmem : {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P} ∈ PM' :=
            Set.mem_image_of_mem _ hPPM
          refine ⟨_, ⟨hSPmem, (hequiv P hPPM).trans hPg, ?_⟩, hwP⟩
          rw [hcoc P hPPM hSPmem]
          exact hPcoc
      -- Refute the lump.
      apply hirr
      show IsOmegaRegularAt (f_M.restrict (⋃₀ hA_M'.blockPieces g z)) z
      rw [hblocks]
      refine ScatFun.isOmegaRegularAt_restrict_restrict F A_M
        (⋃₀ (hA.blockPieces g z ∩ PM)) ?_ z ?_
      · rintro x ⟨P, hPmem, hxP⟩
        exact hAMdef ▸ Set.subset_sUnion_of_mem hPmem.2 hxP
      · by_cases hne : (hA.blockPieces g z ∩ PM).Nonempty
        · -- Nonempty ⟹ every block piece ∈ `𝒫_M` ⟹ sub-block = full block.
          have hsubPM : hA.blockPieces g z ∩ PM = hA.blockPieces g z := by
            apply Set.inter_eq_left.mpr
            obtain ⟨P₀, hP₀blk, hP₀PM⟩ := hne
            intro Q hQblk
            refine ⟨hQblk.choose, fun hQPH => hP₀PM.2 ?_⟩
            obtain ⟨hQmem, hQcoc_ne, h, hhH, hQh⟩ := hQPH
            refine ⟨hP₀blk.choose, ?_, h, hhH, ?_⟩
            · have hzc : hA.cocenterOf hQmem = z := hQblk.choose_spec.2
              rw [hP₀blk.choose_spec.2, ← hzc]; exact hQcoc_ne
            · exact (hP₀blk.choose_spec.1.trans hQblk.choose_spec.1.symm).trans hQh
          rw [hsubPM]; exact hreg
        · -- Empty ⟹ empty domain ⟹ regular.
          rw [Set.not_nonempty_iff_eq_empty] at hne
          rw [hne, Set.sUnion_empty]
          exact isOmegaRegularAt_of_isEmpty_domain _
            (Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])) z
    · -- Ranks: each `𝒫_M'`-piece re-realizes its ambient `𝒫_M ⊆ Part` piece.
      rintro _ ⟨P, hP, rfl⟩
      rw [cbRank_eq_of_equiv (hequiv P hP)]
      exact hfineRank P (hPMsubPart hP)
  have hSS : hA_M'.IsStronglySolvableAt α.limitPart y := by
    refine ⟨hfineM, ?_, fun W hW hyW => ⟨?_, ?_⟩⟩
    · -- Goal A:  y ∈ hA_M'.cocenterSet
      -- 1. Grab the ambient piece whose cocenter is y (from solvability's `y ∈ Y_𝒫`).
      obtain ⟨⟨P_y, hP_y⟩, hP_ycoc⟩ := hsolv.2.1
      have hP_ycoc' : hA.cocenterOf hP_y = y := hP_ycoc
      -- 2. It lies in 𝒫_M: a cocenter-y piece cannot be in 𝒫_H (which needs y_P ≠ y).
      have hP_yPM : P_y ∈ PM := by
        refine ⟨hP_y, ?_⟩
        rintro ⟨hmem, hcoc_ne, _⟩
        exact hcoc_ne hP_ycoc'
      -- 3. Its pullback S P_y is the PM'-piece witnessing y.
      have hSmem : {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P_y} ∈ PM' :=
        Set.mem_image_of_mem _ hP_yPM
      exact ⟨⟨_, hSmem⟩, by
        show hA_M'.cocenterOf hSmem = y
        rw [hcoc P_y hP_yPM hSmem]; exact hP_ycoc'⟩
    · -- Goal B:  (hA_M'.cocenterSet \ W).Finite
      rw [← Set.not_infinite]
      intro hinf
      -- hinf : (hA_M'.cocenterSet \ W).Infinite
      -- The ambient escape set: cocenters of 𝒫_M-pieces sitting off W.
      set E : Set Baire :=
          {z | z ∉ W ∧ ∃ (P : Set ↑F.domain) (hP : P ∈ PM), hA.cocenterOf (hPMsubPart hP) = z}
          with hEdef
      have hEinf : E.Infinite := by
        refine hinf.mono ?_
        rintro z ⟨hzc, hzW⟩
        obtain ⟨⟨P', hP'⟩, hP'coc⟩ := hzc
        have hP'coc' : hA_M'.cocenterOf hP' = z := hP'coc
        obtain ⟨P, hP, hSP⟩ := id hP'
        subst hSP
        rw [hcoc P hP hP'] at hP'coc'
        exact ⟨hzW, P, hP, hP'coc'⟩
      -- E infinite, but G is finite, so one g ∈ G has infinitely many cocenters off W.
      set Eg : ScatFun → Set Baire := fun g =>
          {z | z ∉ W ∧ ∃ (P : Set ↑F.domain) (hP : P ∈ PM),
            hA.cocenterOf (hPMsubPart hP) = z ∧ (F.restrict P).Equiv g} with hEgdef
      have hcover : E ⊆ ⋃ g ∈ (G : Set ScatFun), Eg g := by
        rintro z ⟨hzW, P, hP, hPz⟩
        -- y_P ≠ y, since y_P = z ∉ W ∋ y, so hGrep applies.
        have hPy : hA.cocenterOf (hPMsubPart hP) ≠ y := by
          rw [hPz]; rintro rfl; exact hzW hyW
        obtain ⟨g, hgG, hPg⟩ := hGrep P (hPMsubPart hP) hPy
        exact Set.mem_biUnion hgG ⟨hzW, P, hP, hPz, hPg⟩
      -- G finite + E infinite ⟹ some fiber Eg g is infinite.
      obtain ⟨g, hgG, hginf⟩ : ∃ g ∈ (G : Set ScatFun), (Eg g).Infinite := by
        by_contra hall
        refine hEinf (Set.Finite.subset
          (Set.Finite.biUnion G.finite_toSet (fun g hg => ?_)) hcover)
        by_contra hgi
        exact hall ⟨g, hg, hgi⟩
      -- That g reduces infinitely often off y (witness V = W), so g ∈ H.
      have hgROI : hA.ReducibleInfinitelyOftenOffY y g := by
        refine ⟨W, hW, hyW, hginf.mono ?_⟩
        rintro z ⟨hzW, P, hP, hPz, hPg⟩
        exact ⟨⟨⟨P, hPMsubPart hP⟩, hPz⟩, hzW, P, hPMsubPart hP, hPz, hPg.2⟩
      have hgH : g ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hgG, hgROI⟩
      -- A witness piece of the infinite fiber is then in PM and PH at once — contradiction.
      obtain ⟨z₀, hz₀W, P₀, hP₀, hP₀z, hP₀g⟩ := hginf.nonempty
      have hP₀y : hA.cocenterOf (hPMsubPart hP₀) ≠ y := by
        rw [hP₀z]; rintro rfl; exact hz₀W hyW
      exact hP₀.2 ⟨hPMsubPart hP₀, hP₀y, g, hgH, hP₀g⟩
    · -- Goal C:  ∀ (P : Set ↑f_M.domain) (hP : P ∈ PM'), hA_M'.cocenterOf hP ≠ y →
      --            ∃ (Q : Set ↑f_M.domain) (hQ : Q ∈ PM'), hA_M'.cocenterOf hQ ≠ y ∧
      --              hA_M'.cocenterOf hQ ∈ W ∧ ScatFun.Reduces (f_M.restrict P) (f_M.restrict Q)
      intro P' hP' hP'y
      obtain ⟨P₀, hP₀, hSP⟩ := id hP'
      subst hSP
      rw [hcoc P₀ hP₀ hP'] at hP'y          -- hP'y : hA.cocenterOf (hPMsubPart hP₀) ≠ y
      -- Solvability of F gives an ambient recurrer Q₀ (in W, off y).
      obtain ⟨Q₀, hQ₀mem, hQ₀y, hQ₀W, hFred⟩ :=
        hsolv.2.2 P₀ (hPMsubPart hP₀) hP'y W hW hyW
      -- Q₀ ∈ 𝒫_M: else Q₀ ∈ 𝒫_H would force P₀ ∈ 𝒫_H (H is ≤-downward closed), contra P₀ ∈ 𝒫_M.
      have hQ₀PM : Q₀ ∈ PM := by
        refine ⟨hQ₀mem, ?_⟩
        rintro ⟨hQ₀mem', hQ₀y', h, hhH, hQ₀h⟩
        apply hP₀.2
        -- Represent F↾P₀ by some g' ∈ G; then g' ≤ F↾P₀ ≤ F↾Q₀ ≡ h ∈ H.
        obtain ⟨g', hg'G, hP₀g'⟩ := hGrep P₀ (hPMsubPart hP₀) hP'y
        have hg'h : ScatFun.Reduces g' h := hP₀g'.2.trans (hFred.trans hQ₀h.1)
        have hROIh : hA.ReducibleInfinitelyOftenOffY y h := (Finset.mem_filter.mp hhH).2
        have hg'H : g' ∈ H :=
          Finset.mem_filter.mpr ⟨hg'G, ScatFun.IsCPartition.reducibleInfinitelyOftenOffY_downward hA y hg'h hROIh⟩
        exact ⟨hPMsubPart hP₀, hP'y, g', hg'H, hP₀g'⟩
      -- Package the transported witness S Q₀.
      have hSQmem : {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ Q₀} ∈ PM' :=
        Set.mem_image_of_mem _ hQ₀PM
      refine ⟨_, hSQmem, ?_, ?_, ?_⟩
      · rw [hcoc Q₀ hQ₀PM hSQmem]; exact hQ₀y
      · rw [hcoc Q₀ hQ₀PM hSQmem]; exact hQ₀W
      · exact ((hequiv P₀ hP₀).1.trans hFred).trans (hequiv Q₀ hQ₀PM).2
  --rank of f_M is at most α+1+1
  have hfMrank_le : CBRank f_M.func ≤ α + 1 + 1 := by
    have h1 : f_M.Reduces (F.restrict Set.univ) :=
      restrict_reduces_of_subset F (Set.subset_univ A_M)
    have h2 : CBRank f_M.func ≤ CBRank (F.restrict Set.univ).func :=
      ContinuouslyReduces.rank_monotone f_M.hScat (F.restrict Set.univ).hScat h1
    have h3 : CBRank (F.restrict Set.univ).func = CBRank F.func := by
      rw [cbRank_restrict_eq]
      exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
    rw [h3, hFrank] at h2
    exact h2

  -- ==========================================================================
  -- (f) (`6_double_successor_memo.tex:531-538`): `F↾A_Mᶜ ≤ hH := ω H` and
  -- `hH ≤ F⇂(U∖V)` for every clopen `U ⊇ Y_𝒫`. **Proved.**
  -- ==========================================================================
  obtain ⟨hH, hhHmem, hFHred, hhHcov, hFMfold⟩ :
      ∃ hH : ScatFun, hH ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun ∧
        ScatFun.Reduces (F.restrict A_Mᶜ) hH ∧
        (∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
          ScatFun.Reduces hH (F.coRestrict (U \ V))) ∧
        -- `λ+1` fold: when `CB(f_M) = λ+1`, `hH = ω H` also absorbs `f_M`, hence all of `F`.
        (CBRank (F.restrict A_M).func = α.limitPart + 1 → ScatFun.Reduces F hH) := by
    -- Per-`h∈H` corestriction bound `ω h ≤ F⇂(U∖V)`: the (still infinite) `h`-witness set
    -- for `V` lands in `IntertwineSet (F⇂(U∖V)) h`, then `omega_reduces_of_intertwineSet_infinite`.
    have hωh : ∀ h ∈ H, ∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
        ScatFun.Reduces (ScatFun.omega h) (F.coRestrict (U \ V)) := by
      intro h hh U hU hUcov
      have hUVopen : IsOpen (U \ V) := hU.isOpen.sdiff hVcl.isClosed
      apply ScatFun.omega_reduces_of_intertwineSet_infinite
      -- Shrinking `V ⊆ V_h` keeps the witness set infinite.
      have hinfV : {z : Baire | z ∈ hA.cocenterSet ∧ z ∉ V ∧
          ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
            hA.cocenterOf hP = z ∧ ScatFun.Reduces h (F.restrict P)}.Infinite := by
        refine (hVfinf h hh).mono ?_
        rintro z ⟨hzc, hzVf, P, hP, hPz, hle⟩
        exact ⟨hzc, fun hzV => hzVf (hVsub h hh hzV), P, hP, hPz, hle⟩
      refine hinfV.mono ?_
      rintro z ⟨hzc, hzV, P, hP, hPz, hle⟩
      have hzUV : z ∈ U \ V := ⟨hUcov hzc, hzV⟩
      -- `z ∈ IntertwineSet F h`: `h ≤ F↾P` and `F↾P ≤ F⇂W` for every nbhd `W` of `z = y_P`.
      have hzInt : z ∈ ScatFun.IntertwineSet F h := by
        rw [← hPz]
        intro W hW
        obtain ⟨W₀, hW₀sub, hW₀open, hzW₀⟩ := mem_nhds_iff.mp hW
        exact (hle.trans (piece_reduces_coRestrict_of_cocenter_mem F hA hW₀open hP hzW₀)).trans
          (F.coRestrict_reduces_of_subset hW₀sub)
      exact ScatFun.mem_intertwineSet_coRestrict_of_open F h (U \ V) hUVopen hzUV hzInt
    by_cases hHne : H.Nonempty
    · -- `hH := ω(gl H)`, rendered as `ω(glList H.toList)` (membership: `firstCase_omegaD_mem`).
      -- `F↾A_Mᶜ = F↾(⋃𝒫_H) ≤ ω(glList H)`: every `𝒫_H`-piece `≡` some `h ∈ H ≤ glList H`.
      have hFHomega : ScatFun.Reduces (F.restrict A_Mᶜ) (ScatFun.omega (ScatFun.glList H.toList)) := by
        rw [hAMcompl]
        refine reduces_restrict_omega_of_countable_subfamily
          (hA.countable.mono hPHsubPart)
          (fun P hP => hA.isClopen P (hPHsubPart hP))
          (hA.pairwiseDisjoint.subset hPHsubPart) ?_
        rintro P ⟨hPmem, hne, h, hhH, hequivP⟩
        exact hequivP.1.trans (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hhH))
      refine ⟨ScatFun.omega (ScatFun.glList H.toList),
        diagonalTheorem_firstCase_omegaD_mem α hα hHsub hHne, hFHomega, ?_, ?_⟩
      · -- `ω(glList H) ≤ F⇂(U∖V)` via `intertwine_reductions_omega_centered` over `H`.
        intro U hU hUcov
        -- Enumerate `H` as a `Fin H.toList.length` family and combine the per-`h` bounds.
        let Gfam : Fin H.toList.length → ScatFun := fun k => H.toList.getD k.val ScatFun.empty
        have hGmem : ∀ k : Fin H.toList.length, Gfam k ∈ H := by
          intro k
          show H.toList.getD k.val ScatFun.empty ∈ H
          rw [List.getD_eq_getElem _ _ k.isLt]
          exact Finset.mem_toList.mp (List.getElem_mem k.isLt)
        -- `glFin Gfam = glList H.toList`: the two padded families agree (getD default = empty).
        have hfam_eq : ScatFun.glFin Gfam = ScatFun.glList H.toList := by
          unfold ScatFun.glFin ScatFun.glList
          congr 1
          funext k
          by_cases hk : k < H.toList.length
          · rw [dif_pos hk]
          · rw [dif_neg hk, List.getD_eq_default _ _ (not_lt.mp hk)]
        have hcent : ∀ k : Fin H.toList.length, IsCentered (Gfam k).func := fun k =>
          ScatFun.isCentered_of_mem_Centered _ _ (hHsub (hGmem k))
        have hred : ∀ k : Fin H.toList.length,
            ScatFun.Reduces (ScatFun.omega (Gfam k)) (F.coRestrict (U \ V)) :=
          fun k => hωh (Gfam k) (hGmem k) U hU hUcov
        have hgl :=
          ScatFun.intertwine_reductions_omega_centered (F.coRestrict (U \ V)) Gfam hcent hred
        rwa [hfam_eq] at hgl
      · -- `λ+1` fold: `F ≤ ω H` when `CB(f_M) = λ+1` (memoir's `M`-into-`H` absorption).
        intro hm1
        -- All `𝒫_M`-pieces have rank `≤ CB(f_M) = λ+1` (each re-realizes an `f_M`-sub-piece).
        have hPMrank_le : ∀ P ∈ PM, CBRank (F.restrict P).func ≤ α.limitPart + 1 := by
          intro P hP
          rw [← hm1, ← cbRank_eq_of_equiv (hequiv P hP)]
          have h1 := restrict_reduces_of_subset f_M
            (Set.subset_univ {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P})
          have h2 := ContinuouslyReduces.rank_monotone
            (f_M.restrict _).hScat (f_M.restrict Set.univ).hScat h1
          have h3 : CBRank (f_M.restrict Set.univ).func = CBRank f_M.func := by
            rw [cbRank_restrict_eq]
            exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑f_M.domain)) f_M.func
          exact h2.trans_eq h3
        -- `hcase`: cocenter-`y` pieces (which lie in `𝒫_M`) have rank exactly `λ+1`.
        have hcase : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
            CBRank (F.restrict P).func = α.limitPart + 1 := fun P hP hPy =>
          le_antisymm (hPMrank_le P ⟨hP, fun ⟨_, hne, _⟩ => hne hPy⟩)
            (Order.add_one_le_iff.mpr (hfineRank P hP))
        -- `hHtop`: a top-rank cocenter-`≠y` piece lies in `𝒫_H`, giving a representative `h ∈ H`.
        have hHtop : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
            CBRank (F.restrict P).func = α + 1 + 1 → ∃ h ∈ H, (F.restrict P).Equiv h := by
          intro P hP hPne hPrank
          by_cases hPPM : P ∈ PM
          · have hle := hPMrank_le P hPPM
            rw [hPrank] at hle
            exact absurd hle (not_le.mpr (lt_of_le_of_lt (by gcongr)
              (Order.succ_eq_add_one (α + 1) ▸ Order.lt_succ (α + 1))))
          · obtain ⟨_, _, h, hhH, hPh⟩ : P ∈ PH := by
              by_contra hnot; exact hPPM ⟨hP, hnot⟩
            exact ⟨h, hhH, hPh⟩
        -- `f_M ≤ ω H` (the chain), glued with `F↾A_Mᶜ ≤ ω H` and absorbed by `ω H`.
        have hFMomega := reduces_omega_glList_of_rank_limitPart_succ
          α hα F hFrank hA hcase A_M H hm1 hHtop
        exact (ScatFun.reduces_glBin_of_clopen_partition _ _ hA_M.compl hA_M
          (Set.compl_union_self A_M) disjoint_compl_left hFHomega hFMomega).trans
          (ScatFun.glBin_omega_self_reduces _)
    · -- `H = ∅`: then `𝒫_H = ∅`, so `A_Mᶜ = ∅`; take `hH := empty`.
      rw [Finset.not_nonempty_iff_eq_empty] at hHne
      have hAMce : A_Mᶜ = ∅ := by
        rw [hAMcompl]
        refine Set.sUnion_eq_empty.mpr ?_
        rintro P ⟨hPmem, hne, h, hhH, hequiv⟩
        rw [hHne] at hhH
        exact absurd hhH (Finset.notMem_empty h)
      refine ⟨ScatFun.empty,
        ScatFun.empty_mem_FinGl _ (Set.isEmpty_coe_sort.mpr rfl),
        ScatFun.reduces_of_isEmpty_domain
          (Set.isEmpty_coe_sort.mpr (by rw [hAMce]; ext x; simp [ScatFun.restrict])),
        fun U hU hUcov => ScatFun.empty_reduces _, fun hm1 => ?_⟩
      -- Vacuous: `A_Mᶜ = ∅ ⟹ A_M = univ ⟹ CB(f_M) = CB(F) = α+2 ≠ λ+1`, contradicting `hm1`.
      exfalso
      have hAMuniv : A_M = Set.univ := Set.compl_empty_iff.mp hAMce
      have hrank : CBRank (F.restrict A_M).func = α + 1 + 1 := by
        rw [hAMuniv]
        have h3 : CBRank (F.restrict Set.univ).func = CBRank F.func := by
          rw [cbRank_restrict_eq]
          exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
        rw [h3, hFrank]
      rw [hrank] at hm1
      exact absurd hm1.symm (ne_of_lt (lt_of_le_of_lt (by gcongr)
        (Order.succ_eq_add_one (α + 1) ▸ Order.lt_succ (α + 1))))
  -- ==========================================================================
  -- (g) Rank case split: fold `f_M` into `hH = ω H` (`CB(f_M) = λ+1`) or build a diagonal
  -- generator `gM` and glue `hH ⊕ gM` (double-successor rank). [FOR YANN: the diagonal call.]
  -- ==========================================================================
  by_cases hm1 : CBRank (F.restrict A_M).func = α.limitPart + 1
  · -- `λ+1`: `g := hH` already dominates `F` (via `hFMfold`); coverage from `hhHcov`.
    refine ⟨hH, hhHmem, hFMfold hm1, ?_⟩
    intro U hU hUcov
    exact (hhHcov U hU hUcov).trans (F.coRestrict_reduces_of_subset Set.diff_subset)
  · -- Double successor: build `gM` from the Diagonal Theorem, then glue `hH ⊕ gM`.
    obtain ⟨gM, hgMmem, hFMred, hgMcov⟩ :
        ∃ gM : ScatFun, gM ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun ∧
          ScatFun.Reduces (F.restrict A_M) gM ∧
          ∀ W : Set Baire, IsClopen W → y ∈ W → ScatFun.Reduces gM (F.coRestrict W) := by
      -- `CBRank f_M.func` is a double successor (`hm1 : ≠ λ+1`, `hfMrank_le : ≤ α+2`,
      -- `hfM_gt : > λ` available via `hfineRank`); apply `diagonalTheorem` to `hA_M'`/`hSS`
      -- at that rank and lift `FinGl (Generators (β+1+1)) ⊆ FinGl (Generators (α+1+1))`.
            -- Lower bound `λ < CB(f_M)`: the cocenter-`y` piece lies in 𝒫_M and has rank `> λ`.
      have hfM_gt : α.limitPart < CBRank f_M.func := by
        obtain ⟨⟨P_y, hP_y⟩, hP_ycoc⟩ := hsolv.2.1
        have hP_ycoc' : hA.cocenterOf hP_y = y := hP_ycoc
        have hP_yPM : P_y ∈ PM := ⟨hP_y, fun ⟨_, hne, _⟩ => hne hP_ycoc'⟩
        calc α.limitPart
            < CBRank (F.restrict P_y).func := hfineRank P_y hP_y
          _ = CBRank (f_M.restrict {w : ↑f_M.domain |
                (F.restrictEquiv A_M w : ↑F.domain) ∈ P_y}).func :=
              (cbRank_eq_of_equiv (hequiv P_y hP_yPM)).symm
          _ ≤ CBRank f_M.func := by
              set SPy : Set ↑f_M.domain :=
                {w : ↑f_M.domain | (F.restrictEquiv A_M w : ↑F.domain) ∈ P_y} with hSPy
              have h2 := ContinuouslyReduces.rank_monotone (f_M.restrict SPy).hScat
                (f_M.restrict Set.univ).hScat (restrict_reduces_of_subset f_M (Set.subset_univ SPy))
              have h3 : CBRank (f_M.restrict Set.univ).func = CBRank f_M.func := by
                rw [cbRank_restrict_eq]
                exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑f_M.domain)) f_M.func
              exact h2.trans_eq h3
      -- `λ+1 < CB(f_M)`: strict, folding in `hm1 : CB(f_M) ≠ λ+1`.
      have hgrank : α.limitPart + 1 < CBRank f_M.func :=
        lt_of_le_of_ne (Order.add_one_le_iff.mpr hfM_gt) (Ne.symm hm1)
      -- The extraction: `β ≤ α` with `CB(f_M) = β + 1 + 1`.
      obtain ⟨β, hβα, hβsucc, hβαlim⟩ :=
        exists_doubleSucc_of_between α (CBRank f_M.func) hgrank hfMrank_le
      have hβω : β < omega1 := lt_of_le_of_lt hβα hα
      have hFGβ : ScatFun.FGBelow (β + 1 + 1) := hFG.mono (by gcongr)
      -- rewrite hSS at β
      have hSSβ : hA_M'.IsStronglySolvableAt β.limitPart y := by
        rw [hβαlim]; exact hSS
      obtain hDiag := diagonalTheorem β hβω hFGβ f_M hβsucc hA_M' hSSβ
      -- lift back at α and F (instead of f_M)
      obtain ⟨g, hgmem, hgred, hgcov⟩ := hDiag
      exact ⟨g, finGl_generators_doubleSucc_mono hβα hβαlim hgmem, hgred,
        fun W hW hyW => (hgcov W hW hyW).trans (ScatFun.coRestrict_restrict_reduces F A_M W)⟩
    refine ⟨ScatFun.glBin hH gM, ScatFun.finGl_glBin_mem hhHmem hgMmem, ?_, ?_⟩
    · -- `F ≤ hH ⊕ gM`: binary upper bound on the clopen split `A_Mᶜ ⊔ A_M`.
      exact ScatFun.reduces_glBin_of_clopen_partition hH gM hA_M.compl hA_M
        (Set.compl_union_self A_M) disjoint_compl_left hFHred hFMred
    · -- `hH ⊕ gM ≤ F⇂U`: glue `hH ≤ F⇂(U∖V)` and `gM ≤ F⇂(V∩U)` across disjoint clopen pieces.
      intro U hU hUcov
      have hyU : y ∈ U := hUcov hsolv.2.1
      exact ScatFun.reduces_glBin_coRestrict_of_disjoint hH gM
        (hU.diff hVcl) (hVcl.inter hU) Set.diff_subset Set.inter_subset_right
        (disjoint_compl_left.mono (Set.diff_subset_compl U V) Set.inter_subset_left)
        (hhHcov U hU hUcov) (hgMcov (V ∩ U) (hVcl.inter hU) ⟨hyV, hyU⟩)

/-- **Theorem `FiniteGenerationForSolvable`** — now proved directly by
`finiteGenerationForSolvable_split`, which (under strategy (Z)) returns the final `F ≤ g ≤ F⇂U`
conclusion, internalising the rank case split and absorbing the former `_glue` assembly. -/
theorem finiteGenerationForSolvable
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hsolv : hA.IsSolvableAt α.limitPart y) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → hA.cocenterSet ⊆ U →
          ScatFun.Reduces g (F.coRestrict U) :=
  finiteGenerationForSolvable_split α hα hFG F hFrank hA hsolv

end
