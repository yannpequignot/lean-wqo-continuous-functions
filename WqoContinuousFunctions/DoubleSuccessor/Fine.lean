import WqoContinuousFunctions.ScatFun.PreciseStructure.ConsequencesGeneralStructureItem2
import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalForLambdaPlusOne
import WqoContinuousFunctions.ScatFun.PreciseStructure.IntertwineMaxFunLimit
import WqoContinuousFunctions.CenteredFunctions.LocallyCentered.Helpers
import WqoContinuousFunctions.ScatFun.Generators.Basics
import WqoContinuousFunctions.ScatFun.RestrictReindex
import WqoContinuousFunctions.ScatFun.RestrictReduces
import WqoContinuousFunctions.ScatFun.Basics
import WqoContinuousFunctions.ScatFun.Operations
import WqoContinuousFunctions.ScatFun.Generators.Defs
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.FGBelow
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LambdaPlusOne
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `6_double_successor_memo.tex`, §6.1 — Fine partitions in centered functions

This file formalizes Section 1 ("Fine partitions in centered functions") of Chapter 6
("Finite generation at double successors") of the memoir.

The chapter's overall goal is to show `FG(<α) → FG(α)` when `α = λ + n + 2` is a *double*
successor (`λ` limit, `n ∈ ℕ`).  This section introduces `c`-partitions of centered functions
and shows (`existenceFinePartitions`) that, under `FG(<α)`, every function of rank `α` admits
a partition into centered pieces that is as well-behaved as possible ("fine": no lumps, and
every piece has rank `> λ`).

## Main definitions

* `ScatFun.IsCPartition` — a `c`-partition of `F : ScatFun` (memoir "`$c$-partition`"),
  represented as a *set* of clopen pieces `𝒫 : Set (Set ↑F.domain)` (matching the memoir's
  `𝒫 ⊆ Δ⁰₁(A)` literally), rather than an indexed family — see the note below
  `ScatFun.IsCPartition` for why.
* `ScatFun.IsCPartition.cocenterOf` / `.cocenterSet` — the cocenter of a piece / `Y_𝒫`
* `ScatFun.IsCPartition.blockPieces` / `.piece` — `𝒫_{(g,y)}` / `f_{(g,y)}`
* `omegaRegularSet` / `IsOmegaRegularAt` — the reference set `𝒲_α` and `𝒲`-regularity
* `ScatFun.IsCPartition.IsLump` / `.lumpRank` — `𝒫`-lumps and their rank
* `ScatFun.IsCPartition.IsFine` — fine `c`-partitions

## Main results

* `refiningBy1` — Lemma `lemma:RefiningBy1` (dissolving a single lump), **partially proved**:
  Phase 1 (extracting the lump's witness and a common bound, via the fully-proved
  `exists_common_finite_bound`) is proved; Phase 3 is now fully proved
  (`refiningBy1_Ppart_equiv`, `refiningBy1_complement_cbRank_lt`,
  `cPartition_restrict_transport`, hence `refiningBy1_split_complement` and
  `refiningBy1_split_piece`, the last modulo the intended `FG(<α)` application
  `exists_cPartition_of_FGBelow`). The Lindelöf step `exists_countable_clopen_centered_cover`
  (feeding `exists_cPartition_of_FGBelow`; lives in
  `ScatFun/LevelsFinitelyGenerated/FGBelow.lean`, reused from there) is now fully proved.
  Phase 2b (`refiningBy1_exists_regularizing_nbhd`) is now fully proved (using the
  `CB`-rank-preservation hypothesis discharged at the call site by `piece_corestrict_cbRank_eq`
  and its helpers). Phase 4 (`refiningBy1_reassemble`) has all its *partition bookkeeping*
  (the `IsCPartition`, finer, and survival clauses) discharged through the single reusable
  refinement primitive `isCPartition_refine_at_family`; only its two lump-analysis clauses
  (`¬ IsLump g y` and the new-lump rank bound) remain open as inline gaps.
* `gobblingLessThanLambda` — Lemma `lem:gobblingLessThanLambda`, **scaffolded**
* `existenceFinePartitions` — Proposition `ExistenceFinePartitions`, **scaffolded**

Fully proved leaf lemmas: `exists_common_finite_bound`, `isCPartition_refine_at_family`
(the one reusable "refine a `c`-partition at a subfamily of pieces" primitive),
`isCPartition_cPartitionLiminf` (the limit-inferior-of-`c`-partitions primitive, modulo an
explicit coverage/stabilisation hypothesis), `isCPartition_of_indexed_cover`,
`infinite_reduces_stable_under_corestrict`,
`refiningBy1_piece_cbRank_eq`, `refiningBy1_Ppart_equiv`, `refiningBy1_complement_cbRank_lt`,
`cPartition_restrict_transport`, `refiningBy1_split_complement`, `refiningBy1_split_piece`,
`reduces_glBin_restrict_compl`, `reduces_coRestrict_cocenter_nbhd`, `glBin_centered_absorb`,
`gobblingLessThanLambda_reduces`, `gobblingLessThanLambda`,
`exists_clopen_cocenter_avoid` (via its helpers `pgl_const_block_reduces_coRestrict`,
`pgl_const_deep_block_values_in_nbhd`, `pgl_const_base_notMem_closure_block0`), and now
`refiningBy1_exists_regularizing_nbhd` (Phase 2b, via `isClopen_prefixCyl`,
`rayOn_corestrict_reduces`, `rayOn_corestrict_prefixCyl_empty`, `omegaRegularSet_congr`,
`cbRank_restrict_restrict_eq`, `piece_corestrict_inter_cbRank_eq`,
`piece_corestrict_cbRank_eq`). The three
remaining open leaves (`refiningBy1_reassemble`,
`existenceFinePartitions_dissolveAll`, `existenceFinePartitions_gobble`) are recorded with
complete statements and detailed proof-strategy docstrings (mapping each step back to
`6_double_successor_memo.tex`); each is a genuine multi-step construction in its own right,
left for a follow-up pass.

`existenceFinePartitions` also relies on `consequencesGeneralStructure_succMaxFun_le`
(Corollary `ConsequencesGeneralStructureThm`, item 2), a previously-unformalized general
fact that is *not* specific to this chapter — it is proved in full in
`PointedGluing/GeneralStructureConsequences.lean` (raw form) and
`ScatFun/PreciseStructure/ConsequencesGeneralStructureItem2.lean` (`ScatFun` form).
-/

noncomputable section

/-!
## `c`-partitions (`6_double_successor_memo.tex:18-28`)

A `c`-partition of `F : ScatFun` is a countable clopen partition of `F.domain` all of whose
pieces are centered.  As in `SimpleSuccessor/Prop411.lean` (memoir's `f = ⊔ᵢ fᵢ`), the pieces
are *restrictions* `F.restrict P`, which keep `F`'s codomain untouched — this is what makes
the piece cocenters genuine values of `F`.

**Representation choice.** A partition is represented as a *set* `𝒫 : Set (Set ↑F.domain)`
of clopen pieces, matching the memoir's `𝒫 ⊆ Δ⁰₁(A)` literally, rather than as an `ℕ`-indexed
family `A : ℕ → Set ↑F.domain` (the earlier choice in this file). The indexed representation
cannot express a genuinely *finite* `c`-partition: padding the unused indices requires some
value, and the only available one is `∅`, which is never centered (`IsCentered` needs a
witness point), so a finite partition into `k` centered pieces has no faithful `ℕ`-indexed
encoding under a definition requiring *every* block to be centered. (The same obstruction is
flagged, and deferred, in `SimpleSuccessor/Prop411.lean`'s docstring for the same
`f = ⊔ᵢ fᵢ` pattern.) The set-of-pieces representation sidesteps this entirely: a finite
partition is just a finite set, an infinite one a countably infinite set, with no padding and
no case-split between the two — every `P ∈ 𝒫` is guaranteed centered by construction.

The cost: a few existing helper lemmas (`cb_rank_of_clopen_union`, hence
`ScatFun.cbRank_eq_iSup_restrict`) are hardwired to `ℕ`-indexed families. Proofs that need the
`CB`-rank of `⋃₀ 𝒫` (e.g. `refiningBy1`) must first pull an `ℕ`-enumeration out of the
`𝒫.Countable` witness (e.g. via `Set.Countable.exists_eq_range`) before invoking them; this
affects proofs only, not the definitions here. -/

/-- A **`c`-partition** of `F : ScatFun` (memoir "`$c$-partition`",
`6_double_successor_memo.tex:22-23`): a countable set `𝒫` of pairwise-disjoint clopen pieces
of `F.domain`, covering it, such that every piece `F.restrict P` is centered. -/
def ScatFun.IsCPartition (F : ScatFun) (Part : Set (Set ↑F.domain)) : Prop :=
  Part.Countable ∧ (∀ P ∈ Part, IsClopen P) ∧ Part.PairwiseDisjoint id ∧
    ⋃₀ Part = univ ∧ ∀ P ∈ Part, IsCentered (F.restrict P).func

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

lemma countable (hA : F.IsCPartition Part) : Part.Countable := hA.1
lemma isClopen (hA : F.IsCPartition Part) : ∀ P ∈ Part, IsClopen P := hA.2.1
lemma pairwiseDisjoint (hA : F.IsCPartition Part) : Part.PairwiseDisjoint id := hA.2.2.1
lemma sUnion_eq (hA : F.IsCPartition Part) : ⋃₀ Part = univ := hA.2.2.2.1
lemma centered (hA : F.IsCPartition Part) : ∀ P ∈ Part, IsCentered (F.restrict P).func := hA.2.2.2.2

/-- The cocenter `y_P` of a piece `P ∈ 𝒫`. -/
def cocenterOf (hA : F.IsCPartition Part) {P : Set ↑F.domain} (hP : P ∈ Part) : Baire :=
  cocenter (F.restrict P).func (hA.centered P hP)

/-- `Y_𝒫` (memoir, line 26): the (countable) set of cocenters of all pieces. -/
def cocenterSet (hA : F.IsCPartition Part) : Set Baire :=
  Set.range (fun p : {P // P ∈ Part} => hA.cocenterOf p.2)

/-- `𝒫_{(g,y)}` (memoir, line 27): the sub-collection of pieces equivalent to `g` with
cocenter `y`. -/
def blockPieces (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire) : Set (Set ↑F.domain) :=
  {P | ∃ hP : P ∈ Part, ScatFun.Equiv (F.restrict P) g ∧ hA.cocenterOf hP = y}

/-- `f_{(g,y)}` (memoir, line 27): the disjoint union of all pieces equivalent to `g` with
cocenter `y`, as a `ScatFun` (the restriction of `F` to the union of those pieces). -/
def piece (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire) : ScatFun :=
  F.restrict (⋃₀ hA.blockPieces g y)

end ScatFun.IsCPartition

/-!
## `𝒲`-regularity and lumps (`6_double_successor_memo.tex:30-46`)

`𝒲_α` (`\omegaregular{α}` in the memoir) is the *genuinely finite* reference set `{ℓ_λ} ∪
{ωh | h ∈ 𝒞_α}`, writing `α = λ + n` (`λ` the limit part of `α`); here `ωh` is the plain
gluing of the constant sequence `h` (memoir notation, `3_general_struct_memo.tex:238`), and
`𝒞_α` is the memoir's own finite set of centered representatives at rank `α`
(`ScatFun.Centered`, `ScatFun/Generators/Defs.lean`) — **not** the set of *all* centered
functions of `CB`-rank `α` (which is infinite as a literal set of `ScatFun`s, only finite up
to equivalence). Using `Centered α` is what makes `𝒲_α` finite by construction, matching the
memoir's "since `𝒲_β` is finite" (`6_double_successor_memo.tex:61`) literally: only finitely
many equivalence-class "obstructions" `h` need to be tested.
-/

/-- `α.limitPart ≤ α`, unpacked from `α = α.limitPart + α.natPart`. Used to bound the index
of `ℓ_λ` in `omegaRegularSet`. (No reusable global lemma for this exists yet; see the
identical local `have` in `ScatFun/LiftToLex.lean:38`.) -/
private lemma limitPart_le (α : Ordinal.{0}) : α.limitPart ≤ α := by
  conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
  exact le_self_add

/-- The reference set `𝒲_α` (memoir `\omegaregular{α}`, `6_double_successor_memo.tex:32`):
writing `α = λ + n` (`λ` the limit part of `α`), the maximum function `ℓ_λ` together with
`ω h` for every `h` in the memoir's finite set of centered representatives `𝒞_α`
(`ScatFun.Centered α`). A `Finset`, matching the memoir's `𝒲_α` finite by construction. -/
def omegaRegularSet (α : Ordinal.{0}) (hα : α < omega1) : Finset ScatFun :=
  insert (ScatFun.maxFun α.limitPart (lt_of_le_of_lt (limitPart_le α) hα))
    ((ScatFun.Centered α).image (fun h => ScatFun.gl (fun _ => h)))

/-- `F` is **`𝒲`-regular at `y`** (memoir, `6_double_successor_memo.tex:34`): for every `w`
in the reference set `𝒲_{CB(F)}`, the set of ray-indices `j` with `w ≤ ray_j(F, y)` is
either empty or infinite. -/
def IsOmegaRegularAt (F : ScatFun) (y : Baire) : Prop :=
  ∀ w ∈ omegaRegularSet (CBRank F.func) (CBRank_lt_omega1 F.hScat),
    {j : ℕ | ScatFun.Reduces w (F.rayOn y Set.univ j)}.Infinite ∨
      {j : ℕ | ScatFun.Reduces w (F.rayOn y Set.univ j)} = ∅

/-
A `ScatFun` with empty domain is `𝒲`-regular at every base point `y`: each ray
`G.rayOn y univ j` also has empty domain, so for any reference function `w` the set of
qualifying indices is either all of `ℕ` (when `w` too has empty domain) or empty.
-/
lemma isOmegaRegularAt_of_isEmpty_domain (G : ScatFun) (hG : IsEmpty ↑G.domain)
    (y : Baire) : IsOmegaRegularAt G y := by
  intro w hw; by_cases hw' : IsEmpty w.domain <;> simp_all +decide ;
  · exact Or.inl <| Set.infinite_univ.mono fun j _ => ScatFun.reduces_of_isEmpty_domain <| by aesop;
  · refine Or.inr <| Set.eq_empty_of_forall_notMem fun j hj => hw' <| ?_;
    have := hj;
    obtain ⟨ σ, hσ, hσ' ⟩ := this;
    obtain ⟨ x, hx ⟩ := Set.nonempty_iff_ne_empty.mpr hw';
    obtain ⟨ y, hy ⟩ := σ ⟨ x, hx ⟩;
    exact False.elim <| hG.subset hy.1

/-- **Restrict-of-restrict is `Equiv` to restrict-of-intersection.** The "no mathematical
content" bookkeeping of `ScatFun.restrict_restrict_domain_eq`/`_func_eq`
(`ScatFun/RestrictReindex.lean`) packaged as a genuine `ScatFun.Equiv`, via `Homeomorph.setCongr`
pushed through `ContinuouslyReduces.refl` on both sides. Reused both for
`rayOn_restrict_equiv` and for the domain-partition transport of rays
(`rayOn_reduces_gl_of_domain_partition`). -/
theorem ScatFun.restrict_restrict_equiv (F : ScatFun) (D A0 : Set ↑F.domain) (hA0D : A0 ⊆ D) :
    ScatFun.Equiv
      ((F.restrict D).restrict {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0})
      (F.restrict A0) := by
  have hdom := ScatFun.restrict_restrict_domain_eq F D A0 hA0D
  have hfunc := ScatFun.restrict_restrict_func_eq F D A0 hA0D
  set e := Homeomorph.setCongr hdom
  refine ⟨?_, ?_⟩
  · show ContinuouslyReduces _ (F.restrict A0).func
    have h1 := (ContinuouslyReduces.refl (F.restrict A0).func).comp_homeomorph_left e
    rwa [← hfunc] at h1
  · show ContinuouslyReduces (F.restrict A0).func _
    have h2 := (ContinuouslyReduces.refl (F.restrict A0).func).comp_homeomorph_right e
    rwa [← hfunc] at h2

/-- **A ray of a restriction is (up to re-realization) the corresponding restricted ray.**
`(g.restrict C).rayOn y Set.univ j` and `g.rayOn y C j` describe the same underlying points —
`restrict_restrict_equiv` at `D = C`, `A0 = C ∩ {a | g.func a ∈ RaySet univ y j}` (`rayOn`'s own
domain-defining set, already a subset of `C`). Used to move the ray of a `c`-partition piece
`F.restrict P` back and forth against the ray of `F` itself corestricted to `P`. -/
theorem ScatFun.rayOn_restrict_equiv (g : ScatFun) (C : Set ↑g.domain) (y : Baire) (j : ℕ) :
    ScatFun.Equiv ((g.restrict C).rayOn y Set.univ j) (g.rayOn y C j) := by
  rw [rayOn_eq_corestrict, ScatFun.rayOn]
  set A0 : Set ↑g.domain := C ∩ {a : ↑g.domain | g.func a ∈ RaySet Set.univ y j} with hA0def
  have hA0C : A0 ⊆ C := Set.inter_subset_left
  have hpred : {w : ↑(g.restrict C).domain | (g.restrict C).func w ∈ RaySet Set.univ y j}
      = {w : ↑(g.restrict C).domain | (g.restrictEquiv C w : ↑g.domain) ∈ A0} := by
    ext w
    show (g.restrict C).func w ∈ RaySet Set.univ y j ↔ (g.restrictEquiv C w : ↑g.domain) ∈ A0
    have hval : (g.restrict C).func w = g.func (g.restrictEquiv C w : ↑g.domain) := rfl
    rw [hval, hA0def, Set.mem_inter_iff]
    simp
  rw [hpred]
  exact ScatFun.restrict_restrict_equiv g C A0 hA0C

/-- **A ray of `F` decomposes as the disjoint union of the corresponding rays of the pieces of
a domain partition.** Memoir, `6_double_successor_memo.tex:190`: `ray_j(f) = ⊔_{P ∈ 𝒫}
ray_j(f↾P)`. Applies `scatFun_reduces_gl_of_domain_partition` to `F.rayOn y Set.univ j` itself
(seen as `F.restrict S` for `S` the ray's defining clopen codomain-preimage), pulling `A`'s
blocks back along `F.restrictEquiv S`, then identifies each resulting doubly-restricted piece
with `(F.restrict (A i)).rayOn y Set.univ j` via `rayOn_restrict_equiv`
(routed through `restrict_restrict_equiv` at `D = S`, `A0 = A i ∩ S`). -/
theorem ScatFun.rayOn_reduces_gl_of_domain_partition
    (F : ScatFun) (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A) (y : Baire) (j : ℕ) :
    ScatFun.Reduces (F.rayOn y Set.univ j)
      (ScatFun.gl (fun i => (F.restrict (A i)).rayOn y Set.univ j)) := by
  rw [rayOn_eq_corestrict]
  set S : Set ↑F.domain := {a : ↑F.domain | F.func a ∈ RaySet Set.univ y j} with hSdef
  have hScl : IsClopen S :=
    ⟨(isClopen_raySet y j).1.preimage F.hCont, (isClopen_raySet y j).2.preimage F.hCont⟩
  set P : ℕ → Set ↑(F.restrict S).domain :=
    fun i => {w : ↑(F.restrict S).domain | (F.restrictEquiv S w : ↑F.domain) ∈ A i ∩ S}
    with hPdef
  obtain ⟨hAcl, hAdisj, hAcov⟩ := hdu
  have hduP : (F.restrict S).IsDisjointUnion P := by
    refine ⟨fun i => ?_, fun i i' hii' => ?_, ?_⟩
    · exact ((hAcl i).inter hScl).preimage
        (continuous_subtype_val.comp (F.restrictEquiv S).continuous)
    · rw [Set.disjoint_left]
      intro w hw hw'
      exact (Set.disjoint_left.mp (hAdisj i i' hii') hw.1) hw'.1
    · ext w
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hmem : (F.restrictEquiv S w : ↑F.domain) ∈ Set.univ := Set.mem_univ _
      rw [← hAcov] at hmem
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact ⟨i, hi, (F.restrictEquiv S w).2⟩
  have h1 : ScatFun.Reduces (F.restrict S)
      (ScatFun.gl (fun i => (F.restrict S).restrict (P i))) :=
    scatFun_reduces_gl_of_domain_partition (F.restrict S) P hduP
  have h2 : ∀ i, ScatFun.Reduces ((F.restrict S).restrict (P i))
      ((F.restrict (A i)).rayOn y Set.univ j) := fun i =>
    (ScatFun.restrict_restrict_equiv F S (A i ∩ S) Set.inter_subset_right).1.trans
      (ScatFun.rayOn_restrict_equiv F (A i) y j).2
  exact h1.trans (ScatFun.gl_reduces_of_pointwise _ _ h2)

/-
**Cocenters agree for a gobbled superset.** If `P ⊆ D` and `F.restrict D` is equivalent to
`F.restrict P` (both centered), their cocenters coincide: the inclusion `P ↪ D` is a
value-preserving reduction (`τ = id`), so rigidity of the cocenter (`rigidityOfCocenter_tau`)
forces `cocenter (F↾D) = cocenter (F↾P)`.
-/
lemma cocenter_restrict_eq_of_subset_equiv
    (F : ScatFun) (P D : Set ↑F.domain) (hPD : P ⊆ D)
    (hPcent : IsCentered (F.restrict P).func) (hDcent : IsCentered (F.restrict D).func)
    (hequiv : (F.restrict D).Equiv (F.restrict P)) :
    cocenter (F.restrict D).func hDcent = cocenter (F.restrict P).func hPcent := by
  have := @rigidityOfCocenter_tau;
  convert this ( F.restrict P |> ScatFun.hScat ) ( F.restrict D |> ScatFun.hScat ) hPcent hDcent hequiv.symm using 1;
  rotate_left;
  exact fun x => ⟨ x, by
    exact ⟨ x.2.1, hPD x.2.2 ⟩ ⟩
  all_goals generalize_proofs at *;
  exact fun x => x;
  simp +decide only [ScatFun.restrict, coe_setOf, mem_setOf_eq, comp_apply, Subtype.forall, forall_exists_index];
  exact ⟨ fun h => fun _ _ _ => h, fun h => h ( by continuity ) ( by exact continuousOn_id ) fun _ _ _ => rfl ⟩

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- A **`𝒫`-lump** (memoir, `6_double_successor_memo.tex:37`): a pair `(g, y)` with `y ∈
Y_𝒫`, `g` centered, such that `f_{(g,y)}` is not `𝒲`-regular at `y`. -/
def IsLump (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire) : Prop :=
  y ∈ hA.cocenterSet ∧ IsCentered g.func ∧ ¬ IsOmegaRegularAt (hA.piece g y) y

/-- The **rank** of a `𝒫`-lump `(g, y)` is `CB(g)` (memoir, `6_double_successor_memo.tex:38`;
one also has `CB(g) = CB(f_{(g,y)})`, established in the memoir's remark immediately after
the definition and reproved locally where needed). -/
def lumpRank (_hA : F.IsCPartition Part) (g : ScatFun) : Ordinal.{0} :=
  CBRank g.func

end ScatFun.IsCPartition

/-!
## Dissolving lumps (`6_double_successor_memo.tex:30-71`, Lemma `RefiningBy1`)
-/

/-- A `c`-partition `𝒫'` is **finer** than `𝒫` (memoir, `6_double_successor_memo.tex:48`) if
every piece of `𝒫'` is included in some piece of `𝒫`. -/
def IsFinerCPartition {F : ScatFun} (Part' Part : Set (Set ↑F.domain)) : Prop :=
  ∀ P' ∈ Part', ∃ P ∈ Part, P' ⊆ P

/-- **Common bound for a `Finset`'s finite obstruction sets.** If `S : Finset ι` and, for
each `i ∈ S`, we're given a set `J i : Set ℕ`, there is a single `N : ℕ` bounding every
`J i` (`i ∈ S`) that happens to be finite: `J i ⊆ Set.Iio N`.

This makes the memoir's "since `𝒲_β` is finite, there exists `J` such that for all `w`,
either `J_w ⊆ J` or `J_w` is infinite" (`6_double_successor_memo.tex:61`) precise: it is this
elementary `Finset.sup` fact about the *finitely many* `J_w` that are themselves finite, not
literal finiteness of every family the memoir tests. (This is also exactly the fact that was
*not* actually available before `omegaRegularSet` was fixed to use `ScatFun.Centered`, since
`𝒲_β` was not a `Finset` at that point.) -/
lemma exists_common_finite_bound {ι : Type*} (S : Finset ι) (J : ι → Set ℕ) :
    ∃ N : ℕ, ∀ i ∈ S, (J i).Finite → J i ⊆ Set.Iio N := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a S' ha ih =>
    obtain ⟨N', hN'⟩ := ih
    by_cases hJa : (J a).Finite
    · obtain ⟨M, hM⟩ := hJa.bddAbove
      refine ⟨max N' (M + 1), fun i hi hfin j hj => ?_⟩
      simp only [Set.mem_Iio]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · have := hM hj
        omega
      · have := hN' i hi' hfin hj
        simp only [Set.mem_Iio] at this
        omega
    · refine ⟨N', fun i hi hfin => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact absurd hfin hJa
      · exact hN' i hi' hfin

/-!
### Supporting lemmas for `refiningBy1` (Phases 2–3)

The supporting lemmas below correspond to specific steps of the informal proof
(`6_double_successor_memo.tex:57-71`); see each docstring for the exact citation. -/

/-
**Lindelöf extraction for centeredness, via prefix cylinders** (first half of the
"Lindelöf" step of `FGconsequences`). Now lives in
`ScatFun/LevelsFinitelyGenerated/FGBelow.lean` (`exists_countable_clopen_centered_cover`)
alongside its `FGBelow`-threaded corollaries `ScatFun.FGBelow.centeredCylinderWitness` and
`ScatFun.FGBelow.disjointUnionOfCentered`, since it depends only on `ScatFun.cyl`/`IsCentered`
and not on any of this file's `c`-partition machinery, and is reused independently of it.
-/

/-
**Repackaging a `ℕ`-indexed disjoint clopen centered cover as an `IsCPartition`** (second
half of the "Lindelöf" step). Given the output of `exists_countable_clopen_centered_cover`, the
*set* `𝒫 = {P n | (P n).Nonempty}` is a `c`-partition: it is countable (image of a countable
type), all its members are clopen and centered by hypothesis, pairwise disjoint from
`∀ i j, i ≠ j → Disjoint (P i) (P j)` (distinct nonempty blocks have distinct indices), and its
`⋃₀` still equals `univ` since dropping the empty blocks removes nothing from `⋃ n, P n`. This
is the bridge between the `ℕ`-indexed representation used in `ClopenPartitionReduces.lean` and
the set-of-pieces `IsCPartition` (see the representation note at the top of the file).
-/
theorem isCPartition_of_indexed_cover
    (F : ScatFun) (P : ℕ → Set ↑F.domain)
    (hcl : ∀ n, IsClopen (P n)) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcov : ⋃ n, P n = Set.univ)
    (hcent : ∀ n, (P n).Nonempty → IsCentered (F.restrict (P n)).func) :
    ∃ Part : Set (Set ↑F.domain), F.IsCPartition Part := by
  refine ⟨ { S | ∃ n, S = P n ∧ ( P n ).Nonempty }, ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact Set.countable_range ( fun n => P n ) |> Set.Countable.mono fun x hx => by aesop;
  · aesop;
  · intro S hS T hT hST; obtain ⟨ n, rfl, hn ⟩ := hS; obtain ⟨ m, rfl, hm ⟩ := hT; specialize hdisj n m; aesop;
  · simp_all +decide [ Set.ext_iff ];
    exact fun a ha => by obtain ⟨ n, hn ⟩ := hcov a ha; exact ⟨ P n, ⟨ n, fun _ _ => Iff.rfl, ⟨ _, hn ⟩ ⟩, hn ⟩ ;
  · grind

/-- **The missing "Lindelöf" step of `FGconsequences`.** The centered-cylinder-witness fact
gives a genuine countable clopen `c`-partition. Routed through
`exists_countable_clopen_centered_cover` (Lindelöf + laminar cylinder selection) followed by
`isCPartition_of_indexed_cover` (repackaging the resulting indexed cover as a set of pieces);
the genuine mathematical content lives in those two supporting lemmas. This is the gap
`exists_cPartition_of_FGBelow` routes through. -/
theorem exists_cPartition_of_centeredCylinderWitness (F : ScatFun)
    (hcyl : ∀ x : ↑F.domain, ∃ n : ℕ,
      IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain))) :
    ∃ Part : Set (Set ↑F.domain), F.IsCPartition Part := by
  obtain ⟨P, hcl, hdisj, hcov, hcent⟩ := exists_countable_clopen_centered_cover F hcyl
  exact isCPartition_of_indexed_cover F P hcl hdisj hcov hcent

/-- **`FGconsequences`, as actually used**: `FG(<α)` gives every `F` of rank `< α` a
`c`-partition. Memoir citation "`f` admits a `c`-partition `𝒫₀` by `FGconsequences`"
(`6_double_successor_memo.tex:114`, similarly `:184`, `:214`). The centered-cylinder-witness
half is fully proved (`ScatFun.FGBelow.centeredCylinderWitness`, after `ScatFun.FGBelow.mono`
narrows the bound down to `F`'s own rank); only the Lindelöf half
(`exists_cPartition_of_centeredCylinderWitness`) remains open. -/
theorem exists_cPartition_of_FGBelow {α : Ordinal.{0}}
    (hFG : ScatFun.FGBelow α) (F : ScatFun) (hFrank : CBRank F.func < α) :
    ∃ Part : Set (Set ↑F.domain), F.IsCPartition Part :=
  exists_cPartition_of_centeredCylinderWitness F
    ((hFG.mono hFrank.le).centeredCylinderWitness (CBRank_lt_omega1 F.hScat) rfl)

/-
**Reusable CB-rank helper.** The CB-rank of `F` restricted to the union of a *countable*,
*clopen*, *nonempty* family `S` of pieces, all of the same CB-rank `β`, is again `β`. This is
`CBrankofclopenunion` (`cb_rank_of_clopen_union`) packaged for a set-of-pieces family:
enumerate `S` as `range f` (`Set.Countable.exists_eq_range`, needs `S.Nonempty`), transport
`CBRank (F.restrict (⋃₀ S)).func` to `CBRank (fun x : ↥(⋃₀ S) => F.func x.val)` via
`cbRank_restrict_eq`, apply `cb_rank_of_clopen_union` to that function with the open cover
`fun n => {x | (x : Baire) ∈ f n}` (open since each `f n` is clopen; a cover since
`⋃₀ S = ⋃ n, f n`), and identify each summand with `CBRank (F.restrict (f n)).func = β`
(again `cbRank_restrict_eq`, through the subtype homeomorphism). The resulting `⨆` of the
constant `β` over a nonempty index type is `β` (`ciSup_const`).
-/
lemma cbRank_restrict_sUnion_const
    {F : ScatFun} {S : Set (Set ↑F.domain)} (hSc : S.Countable)
    (hScl : ∀ P ∈ S, IsClopen P) (hSne : S.Nonempty) {β : Ordinal.{0}}
    (hconst : ∀ P ∈ S, CBRank (F.restrict P).func = β) :
    CBRank (F.restrict (⋃₀ S)).func = β := by
  obtain ⟨ f, hf ⟩ := hSc.exists_eq_range hSne;
  have h_cb_rank_union : CBRank (fun x : ↥(⋃₀ S) => F.func x.val) = ⨆ n, CBRank (fun x : {x : ↥(⋃₀ S) | (x : ↑F.domain) ∈ f n} => F.func x.val) := by
    convert cb_rank_of_clopen_union _ _ _ _ _ using 1;
    · convert ScatteredFun.comp_homeomorph ( F.restrict ( ⋃₀ S ) ).hScat ( ScatFun.restrictEquiv F ( ⋃₀ S ) ).symm using 1;
    · aesop;
    · intro i; specialize hScl ( f i ) ( hf.symm ▸ Set.mem_range_self i ) ; exact hScl.2.preimage ( continuous_subtype_val ) ;
  have h_cb_rank_union : ∀ n, CBRank (fun x : {x : ↥(⋃₀ S) | (x : ↑F.domain) ∈ f n} => F.func x.val) = β := by
    intro n
    have h_cb_rank_restrict : CBRank (fun x : {x : ↑F.domain | x ∈ f n} => F.func x.val) = β := by
      convert hconst ( f n ) ( hf.symm ▸ Set.mem_range_self n ) using 1;
      convert cbRank_restrict_eq F ( f n ) |> Eq.symm using 1;
    convert h_cb_rank_restrict using 1;
    convert CBRank_comp_homeomorph _ _;
    swap;
    refine ⟨ ?_, ?_, ?_ ⟩;
    refine ⟨ fun x => ⟨ x.val, x.property ⟩, fun x => ⟨ ⟨ x.val, ?_ ⟩, x.property ⟩, ?_, ?_ ⟩ <;> simp +decide;
    exact ⟨ _, hf.symm ▸ Set.mem_range_self _, x.2 ⟩;
    all_goals norm_num [ Function.LeftInverse, Function.RightInverse ]; all_goals fun_prop;
  convert ‹CBRank ( fun x : ↥ ( ⋃₀ S ) => F.func x.val ) = ⨆ n, CBRank ( fun x : { x : ↥ ( ⋃₀ S ) | ( x : ↑F.domain ) ∈ f n } => F.func x.val ) › using 1;
  · convert cbRank_restrict_eq F ( ⋃₀ S ) using 1;
  · aesop

/-
**Block pieces of a lump are nonempty.** If `(g, y)` is a `𝒫`-lump then `f_{(g,y)}` is not
`𝒲`-regular at `y`, so its domain is nonempty, hence `blockPieces g y` is nonempty.
-/
lemma refiningBy1_blockPieces_nonempty
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y) :
    (hA.blockPieces g y).Nonempty := by
  contrapose! hlump; simp_all +decide [ ScatFun.IsCPartition.IsLump ] ;
  intro hy hcentered
  have h_empty_domain : (hA.piece g y).domain = ∅ := by
    simp_all +decide [ ScatFun.IsCPartition.blockPieces, ScatFun.IsCPartition.piece ];
    simp +decide [ ScatFun.restrict ];
  intro w hw; by_cases hw' : w.domain = ∅ <;> simp_all +decide [ ScatFun.Reduces, ContinuouslyReduces ] ;
  · refine Or.inl <| Set.infinite_univ.mono fun j _ => ?_;
    refine ⟨ ?_, ?_, ?_ ⟩;
    exact fun x => False.elim <| hw'.subset x.2;
    · exact continuous_of_const fun x y => by aesop;
    · exact ⟨ fun _ => 0, continuousOn_const ⟩;
  · right; ext j; simp [ScatFun.rayOn, ScatFun.restrict, ScatFun.IsCPartition.piece, ScatFun.IsCPartition.blockPieces] at *; (
    grind +splitImp);

/-- **Phase 2a**: `CB(f_{(g,y)}) = CB(g) = β`. Memoir Remark immediately after the
definition of lump (`6_double_successor_memo.tex:42-45`) — genuinely more than
`CBrankofclopenunion` alone: the remark first shows `f_{(g,y)}` is *not* centered (hence
`blockPieces g y` is infinite), via `Rigidityofthecocenter`/
`Intertwinereductionsforomegacentered`, before the rank identification. Not yet formalized. -/
theorem refiningBy1_piece_cbRank_eq
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y)
    {β : Ordinal.{0}} (hβ : hA.lumpRank g = β) :
    CBRank (hA.piece g y).func = β := by
  have hβg : CBRank g.func = β := hβ
  refine cbRank_restrict_sUnion_const ?_ ?_ (refiningBy1_blockPieces_nonempty hA hlump) ?_
  · exact hA.countable.mono (fun P hP => hP.choose)
  · exact fun P hP => hA.isClopen P hP.choose
  · rintro P ⟨hPmem, hPeq, _⟩
    rw [cbRank_eq_of_equiv hPeq, hβg]

/-
**The genuine content of Phase 2b: infinite obstruction sets survive corestriction.** If
`w`'s obstruction set `{j | w ≤ ray_j(h, y)}` is infinite, then after corestricting `h` to any
clopen neighbourhood `U ∋ y` it is *still* infinite: `y ∈ U` means a whole tail of `y`'s rays
lands inside `U`, so cofinitely many ray-indices are unaffected by the corestriction, and each
surviving `w ≤ ray_j(h, y)` transfers to `w ≤ ray_j(h↾U, y)` unchanged. Memoir,
`6_double_successor_memo.tex:61` ("`h` corestricted to `U` is `𝒲`-regular", infinite half).
This is the half of `refiningBy1_exists_regularizing_nbhd` that is not a direct consequence of
the bound `hN`; the finite half is `hN` applied outside the window.
-/
theorem infinite_reduces_stable_under_corestrict
    (h : ScatFun) (y : Baire) (U : Set Baire) (hU : IsClopen U) (hyU : y ∈ U)
    (w : ScatFun)
    (hinf : {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)}.Infinite) :
    {j : ℕ | ScatFun.Reduces w ((h.restrict (h.func ⁻¹' U)).rayOn y Set.univ j)}.Infinite := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Set.Ici M ⊆ {j : ℕ | Set.range (fun z : ↑(h.rayOn y Set.univ j).domain => (h.rayOn y Set.univ j).func z) ⊆ U} := by
    -- Since `U` is clopen and `y ∈ U`, there exists an `M` such that `nbhd y M ⊆ U`.
    obtain ⟨M, hM⟩ : ∃ M : ℕ, Set.Ici M ⊆ {j : ℕ | ∀ z : ℕ → ℕ, (∀ l < j, z l = y l) → z ∈ U} := by
      have := hU.2.mem_nhds hyU;
      rw [ mem_nhds_iff ] at this;
      obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := this; rcases ( isOpen_pi_iff.mp ht₂ ) y ht₃ with ⟨ s, hs ⟩ ; use s.sup id + 1; intro j hj; simp_all +decide [ Set.subset_def ] ;
      exact fun z hz => ht₁ _ ( hs.choose_spec.2 _ fun i hi => by simpa [ hz i ( lt_of_le_of_lt ( Finset.le_sup ( f := id ) hi ) hj ) ] using hs.choose_spec.1 i hi );
    use M; intro j hj; simp_all +decide [ Set.range_subset_iff, ScatFun.rayOn ] ;
    simp_all +decide [ ScatFun.restrict, RaySet ];
    exact fun a ha hp hq => hM hj _ hp;
  refine Set.Infinite.mono ?_ ( hinf.diff ( Set.finite_Iio M ) ) ; intro j hj ; simp_all +decide [ Set.subset_def ] ;
  obtain ⟨ σ, τ, hσ, hτ, hτ' ⟩ := hj.1;
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  use fun x => ⟨ σ x, by
    simp only [ScatFun.rayOn, ScatFun.restrict, coe_setOf, mem_setOf_eq, univ_inter, comp_apply, forall_exists_index, Subtype.forall, mem_preimage] at *;
    exact ⟨ ⟨ σ x |>.2.1, hM _ hj.2 _ _ ( σ x |>.2.1 ) ( σ x |>.2.2.2 ) rfl ⟩, σ x |>.2.2.2 ⟩ ⟩
  all_goals generalize_proofs at *;
  exact Continuous.subtype_mk ( continuous_subtype_val.comp τ ) _;
  use hσ;
  · grind +locals;
  · intro x; specialize hM j hj.2 ( h.rayOn y univ j |> ScatFun.func <| σ x ) ( h.rayOn y univ j |> ScatFun.func <| σ x ) ; aesop;

/-
The basic clopen prefix cylinder `U = {z | ∀ k ≤ N, z k = y k}` (memoir `N_{y↾(N+1)}`)
is clopen in `Baire`: it is the finite intersection over `k ≤ N` of the clopen coordinate
sets `{z | z k = y k}` (preimages of the clopen singleton `{y k}` under the continuous, and
open, coordinate projections in the product topology of `ℕ → ℕ`).
-/
lemma isClopen_prefixCyl (N : ℕ) (y : Baire) :
    IsClopen {z : Baire | ∀ k, k ≤ N → z k = y k} := by
  have h_clopen : ∀ k ≤ N, IsClopen { z : ℕ → ℕ | z k = y k } := by
    intro k hk
    have h_clopen : IsClopen { z : ℕ → ℕ | z k = y k } := by
      have h_cont : Continuous (fun z : ℕ → ℕ => z k) := by
        exact continuous_apply k
      constructor;
      · exact isClosed_eq h_cont continuous_const;
      · exact h_cont.isOpen_preimage { y k } ( by simp +decide )
    exact h_clopen;
  have h_clopen : IsClopen (⋂ k ∈ Finset.range (N + 1), { z : ℕ → ℕ | z k = y k }) := by
    exact ⟨ isClosed_biInter fun k hk => IsClopen.isClosed ( h_clopen k ( Finset.mem_range_succ_iff.mp hk ) ), isOpen_biInter_finset fun k hk => IsClopen.isOpen ( h_clopen k ( Finset.mem_range_succ_iff.mp hk ) ) ⟩;
  convert h_clopen using 1;
  ext; simp [Finset.mem_range]

/-
A ray of the corestriction `h↾V` reduces to the corresponding ray of `h`: `h↾V` is a
restriction of `h`, so its `j`-th ray at `y` is `h` restricted to a *subset* of `h`'s `j`-th
ray domain, and restriction to a smaller set always reduces to restriction to a larger one
(`restrict_reduces_of_subset`, after `restrict_restrict_domain_eq`).
-/
lemma rayOn_corestrict_reduces (h : ScatFun) (y : Baire) (V : Set Baire) (j : ℕ) :
    ScatFun.Reduces ((h.restrict (h.func ⁻¹' V)).rayOn y Set.univ j)
      (h.rayOn y Set.univ j) := by
  -- Let's denote the rays accordingly.
  set S := {a : ↑h.domain | h.func a ∈ RaySet Set.univ y j}
  set S' := {a : ↑h.domain | h.func a ∈ RaySet Set.univ y j ∧ h.func a ∈ V};
  -- By `restrict_reduces_of_subset`, it suffices to show `S' ⊆ S` (obvious).
  have hSS' : S' ⊆ S := by
    exact fun x hx => hx.1;
  -- By `restrictRestrict_eq`, we have `(h.restrict (h.func ⁻¹' V)).restrict S' = h.restrict S'`.
  have h_restrictRestrict_eq : ((h.restrict (h.func ⁻¹' V)).restrict {a : ↑(h.restrict (h.func ⁻¹' V)).domain | (h.restrict (h.func ⁻¹' V)).func a ∈ RaySet Set.univ y j}).func = (h.restrict S').func ∘ (Homeomorph.setCongr (by
  ext; simp [S'];
  simp +decide only [ScatFun.restrict, coe_setOf, mem_setOf_eq, ScatFun.restrictEquiv, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, comp_apply, mem_preimage];
  tauto)) := by
    exact List.map_inj.mp rfl
  generalize_proofs at *;
  -- By `restrict_reduces_of_subset`, we have `h.restrict S' ≤ h.restrict S`.
  have h_restrict_reduces : ScatFun.Reduces (h.restrict S') (h.restrict S) := by
    exact restrict_reduces_of_subset h hSS';
  simp_all +decide [ ScatFun.rayOn ];
  obtain ⟨ f, hf ⟩ := h_restrict_reduces;
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => f ( Homeomorph.setCongr ‹_› x );
  · exact hf.1.comp ( Homeomorph.continuous _ );
  · obtain ⟨ τ, hτ₁, hτ₂ ⟩ := hf.2;
    refine ⟨ τ, ?_, ?_ ⟩;
    · convert hτ₁ using 1;
      ext; simp [Function.comp];
      constructor <;> rintro ⟨ a, ha, rfl ⟩ <;> use a <;> aesop;
    · intro x; specialize hτ₂ ( Homeomorph.setCongr ‹_› x ) ; aesop;

/-
On the prefix cylinder `U = {z | ∀ k ≤ N, z k = y k}`, every ray index `j ≤ N` of the
corestriction `h↾U` is empty: a point of that ray has value differing from `y` at
coordinate `j`, but membership in `U` forces its value to agree with `y` at every `k ≤ N`,
in particular at `j ≤ N`.
-/
lemma rayOn_corestrict_prefixCyl_empty (h : ScatFun) (y : Baire) (N j : ℕ) (hj : j ≤ N) :
    ((h.restrict (h.func ⁻¹' {z : Baire | ∀ k, k ≤ N → z k = y k})).rayOn
      y Set.univ j).domain = ∅ := by
  simp +decide only [ScatFun.rayOn, ScatFun.restrict, preimage_setOf_eq, mem_setOf_eq, coe_setOf, comp_apply, univ_inter];
  simp +decide only [RaySet, mem_univ, ne_eq, true_and, ScatFun.restrictEquiv, mem_setOf_eq, coe_setOf, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk];
  grind

/-- `omegaRegularSet` depends only on its ordinal argument, not on the `< omega1` proof:
equal ranks give equal reference sets. -/
lemma omegaRegularSet_congr {a b : Ordinal.{0}} (hab : a = b) (ha : a < omega1)
    (hb : b < omega1) : omegaRegularSet a ha = omegaRegularSet b hb := by
  cases hab; rfl

/-- **Phase 2b**: given a bound `N` on the finite obstruction sets of `𝒲_{CB(h)}`
(`exists_common_finite_bound`) and the fact `hpres` that corestricting `h` to any clopen
neighbourhood of `y` preserves `CB`-rank (true for `h = f_{(g,y)}` since each block piece is
centered with cocenter `y`, so `h↾V ≡ h` block-by-block — see `piece_corestrict_cbRank_eq`),
the basic clopen prefix cylinder `U = {z | ∀ k ≤ N, z k = y k}` is a clopen neighbourhood of
`y` such that `h` corestricted to `U` (`h.restrict (h.func ⁻¹' U)`) is `𝒲`-regular at `y`.
Memoir, `6_double_successor_memo.tex:61-62`. Two halves: for `w` with `J_w` infinite the
obstruction set stays infinite on the corestriction (`infinite_reduces_stable_under_corestrict`);
for `w` with `J_w` finite, `hN` bounds `J_w ⊆ Iio N`, and since every corestricted ray
reduces to the corresponding ray of `h` (`rayOn_corestrict_reduces`) while rays of index
`j ≤ N` are empty (`rayOn_corestrict_prefixCyl_empty`), the corestricted obstruction set is
empty. `hpres` matches `omegaRegularSet (CBRank (h↾U).func)` with
`omegaRegularSet (CBRank h.func)`. -/
theorem refiningBy1_exists_regularizing_nbhd
    (h : ScatFun) (y : Baire) (N : ℕ)
    (hpres : ∀ V : Set Baire, IsClopen V → y ∈ V →
      CBRank (h.restrict (h.func ⁻¹' V)).func = CBRank h.func)
    (hN : ∀ w ∈ omegaRegularSet (CBRank h.func) (CBRank_lt_omega1 h.hScat),
      {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)}.Finite →
        {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)} ⊆ Set.Iio N) :
    ∃ U : Set Baire, IsClopen U ∧ y ∈ U ∧
      IsOmegaRegularAt (h.restrict (h.func ⁻¹' U)) y := by
  refine' ⟨{z : Baire | ∀ k, k ≤ N → z k = y k}, isClopen_prefixCyl N y, fun k _ => rfl, _⟩
  set U := {z : Baire | ∀ k, k ≤ N → z k = y k} with hU_def
  intro w hw
  have hrankU : CBRank (h.restrict (h.func ⁻¹' U)).func = CBRank h.func :=
    hpres U (isClopen_prefixCyl N y) (fun k _ => rfl)
  have hwh : w ∈ omegaRegularSet (CBRank h.func) (CBRank_lt_omega1 h.hScat) := by
    rwa [omegaRegularSet_congr hrankU (CBRank_lt_omega1 (h.restrict (h.func ⁻¹' U)).hScat)
      (CBRank_lt_omega1 h.hScat)] at hw
  by_cases hAinf : {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)}.Infinite
  · exact Or.inl (infinite_reduces_stable_under_corestrict h y U (isClopen_prefixCyl N y)
      (fun k _ => rfl) w hAinf)
  · right
    rw [Set.eq_empty_iff_forall_notMem]
    intro j hj
    have hjA : j ∈ {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)} :=
      hj.trans (rayOn_corestrict_reduces h y U j)
    have hjN : j < N := hN w hwh (Set.not_infinite.mp hAinf) hjA
    have hj_empty : ((h.restrict (h.func ⁻¹' U)).rayOn y Set.univ j).domain = ∅ :=
      rayOn_corestrict_prefixCyl_empty h y N j hjN.le
    have hw_empty : w.domain = ∅ := by
      obtain ⟨σ, _⟩ := hj
      have : IsEmpty ↑((h.restrict (h.func ⁻¹' U)).rayOn y Set.univ j).domain :=
        Set.isEmpty_coe_sort.mpr hj_empty
      exact Set.isEmpty_coe_sort.mp (Function.isEmpty σ)
    have hemp : IsEmpty ↑w.domain := Set.isEmpty_coe_sort.mpr hw_empty
    have hw_all : ∀ j', ScatFun.Reduces w (h.rayOn y Set.univ j') := fun j' =>
      ⟨fun x => isEmptyElim x, continuous_of_const (fun a _ => isEmptyElim a),
        fun _ => 0, continuousOn_const, fun a => isEmptyElim a⟩
    exact hAinf (Set.infinite_univ.mono (fun j' _ => hw_all j'))

/-
**Phase 3a**: on the `U`-part `P' = P ∩ F⁻¹(U)` of a lump piece, `F` still restricts to
(something `≡`) `g`. Since `F.restrict P ≡ g` is centered with cocenter `y`, corestricting to
the clopen neighbourhood `U ∋ y` of the cocenter does not change the function up to equivalence
(`centerInvariance_equiv`, Fact 4.2 item 2). Memoir, `6_double_successor_memo.tex:63`
("`f↾P' ≡ g` by centeredness").
-/
theorem refiningBy1_Ppart_equiv
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire}
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y) :
    ScatFun.Equiv (F.restrict (P ∩ F.func ⁻¹' U)) g := by
  unfold ScatFun.IsCPartition.blockPieces at hP; simp +decide at hP;
  obtain ⟨ Q, hQ ⟩ := hP.2;
  apply ScatFun.Equiv.trans;
  rotate_right;
  exact F.restrict P;
  · constructor;
    · grind [restrict_reduces_of_subset];
    · obtain ⟨c, hc⟩ : ∃ c : ↑(F.restrict P).domain, (F.restrict P).func c = y ∧ IsCenterFor (F.restrict P).func c := by
        have hcent : IsCentered (F.restrict P).func := hA.centered P Q
        refine ⟨hcent.choose, ?_, hcent.choose_spec⟩
        simpa [ScatFun.IsCPartition.cocenterOf, cocenter] using hQ
      have h_corestrict : IsCenterFor (F.restrict P).func c ∧ IsOpen {z : ↑(F.restrict P).domain | (F.restrict P).func z ∈ U} ∧ c ∈ {z : ↑(F.restrict P).domain | (F.restrict P).func z ∈ U} := by
        exact ⟨ hc.2, hU.2.preimage ( F.restrict P |>.hCont ), by aesop ⟩;
      obtain ⟨ σ, τ, hσ, hτ, hστ ⟩ := h_corestrict.1 _ h_corestrict.2.1 h_corestrict.2.2;
      refine ⟨ ?_, ?_ ⟩;
      exact fun x => ⟨ σ x, by
        exact ⟨ by exact ( σ x |>.1 |>.2.1 ), by exact ( σ x |>.1 |>.2.2 ), by exact ( σ x |>.2 ) ⟩ ⟩
      generalize_proofs at *;
      refine ⟨ ?_, hσ, ?_, ?_ ⟩;
      · fun_prop;
      · convert hτ using 1;
      · convert hστ using 1;
  · exact hP.1

/-- **The rank-drop at the heart of Phase 3b.** Removing from a lump piece `P` the preimage
of a clopen neighbourhood `U` of its cocenter `y` strictly drops the `CB`-rank below
`β = CB(g) = CB(F↾P)`. Since `F↾P` is centered with cocenter `y` of rank `β = Order.succ α₀`
(`centered_scattered_simple_structure`), it is constant `= y` on its top level `CB_{α₀}`, so by
`cbRank_corestrict_avoid_le` the corestriction avoiding `U` has rank `≤ α₀ < β`. -/
lemma refiningBy1_complement_cbRank_lt
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} {β : Ordinal.{0}} (hgβ : CBRank g.func = β)
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y) :
    CBRank (F.restrict (P ∩ F.func ⁻¹' Uᶜ)).func < β := by
  obtain ⟨Q, hPeq, hcoc⟩ := hP
  have hcent : IsCentered (F.restrict P).func := hA.centered P Q
  have hy : ∀ x, IsCenterFor (F.restrict P).func x → (F.restrict P).func x = y := by
    intro x hx
    have := scatteredHaveCocenter (F.restrict P).func (F.restrict P).hScat x hcent.choose hx
      hcent.choose_spec
    simpa [ScatFun.IsCPartition.cocenterOf, cocenter] using this.trans hcoc
  obtain ⟨α₀, hrank, _, _, hconst⟩ :=
    centered_scattered_simple_structure (F.restrict P).func (F.restrict P).hScat hcent y hy
  have hβeq : β = Order.succ α₀ := by
    rw [← hgβ, ← cbRank_eq_of_equiv hPeq, hrank]
  have h_le : CBRank (F.restrict (P ∩ {a : ↑F.domain | F.func a ∈ Uᶜ})).func ≤ α₀ :=
    ScatFun.cbRank_corestrict_avoid_le F P (hA.isClopen P Q) α₀ y hconst Uᶜ hU.compl
      (fun h => h hyU)
  calc CBRank (F.restrict (P ∩ F.func ⁻¹' Uᶜ)).func ≤ α₀ := h_le
    _ < β := by rw [hβeq]; exact Order.lt_succ α₀

/-
**Transporting a `c`-partition of a clopen sub-restriction back to ambient pieces.** A
`c`-partition `Part0` of `F.restrict A0` (with `A0` clopen) transports to a family `Q` of
clopen subsets of `A0` covering it, each equivalent (as `F.restrict R`) to the corresponding
block `(F.restrict A0).restrict p`. Pure bookkeeping across the `restrict`-of-`restrict`
boundary (`clopen_partition_restrict_transport`, `restrict_restrict_*`).
-/
lemma cPartition_restrict_transport (F : ScatFun) (A0 : Set ↑F.domain) (hA0 : IsClopen A0)
    {Part0 : Set (Set ↑(F.restrict A0).domain)} (hPart0 : (F.restrict A0).IsCPartition Part0) :
    ∃ Q : Set (Set ↑F.domain), Q.Countable ∧ (∀ R ∈ Q, R ⊆ A0) ∧ (∀ R ∈ Q, IsClopen R) ∧
      Q.PairwiseDisjoint id ∧ ⋃₀ Q = A0 ∧
      (∀ R ∈ Q, IsCentered (F.restrict R).func ∧
        CBRank (F.restrict R).func ≤ CBRank (F.restrict A0).func) := by
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
  exact Set.image ( fun p : Set ↑ ( F.restrict A0 ).domain => Subtype.val '' ( F.restrictEquiv A0 '' p ) ) Part0;
  exact hPart0.countable.image _;
  · grind;
  · rintro _ ⟨ p, hp, rfl ⟩;
    have h_clopen : IsClopen (F.restrictEquiv A0 '' p) := by
      have := hPart0.isClopen p hp;
      constructor <;> simp_all +decide [ IsClopen ];
    convert h_clopen using 1;
    constructor <;> intro h <;> constructor <;> simp_all +decide [ IsOpen ];
    · exact hPart0.isClopen p hp |>.1;
    · exact h_clopen.isOpen;
    · convert h_clopen.1 using 1;
      constructor <;> intro h;
      · convert h_clopen.1 using 1;
      · convert hA0.1.isClosedMap_subtype_val _ h using 1;
    · convert hA0.isOpen.isOpenMap_subtype_val _ h_clopen.2 using 1;
  · intro p hp q hq hpq; obtain ⟨ p', hp', rfl ⟩ := hp; obtain ⟨ q', hq', rfl ⟩ := hq; simp_all +decide ;
    have := hPart0.pairwiseDisjoint hp' hq';
    simp_all +decide [ Set.disjoint_left ];
    intro a ha ha' b hb hb' hab hba c hc hc' hbc hca; specialize this ( by aesop ) ; simp_all +decide [ ScatFun.restrictEquiv ] ;
  · ext x;
    constructor;
    · grind;
    · intro hx;
      have := hPart0.sUnion_eq;
      rw [ Set.ext_iff ] at this;
      specialize this ( F.restrictEquiv A0 |>.symm ⟨ x, hx ⟩ ) ; aesop;
  · rintro _ ⟨ p, hp, rfl ⟩;
    refine ⟨ ?_, ?_ ⟩;
    · have h_equiv : ScatFun.Equiv ((F.restrict A0).restrict p) (F.restrict (Subtype.val '' (F.restrictEquiv A0 '' p))) := by
        have h_equiv : ∀ x : ↑(F.restrict A0).domain, x ∈ p ↔ (F.restrictEquiv A0 x : ↑F.domain) ∈ Subtype.val '' (F.restrictEquiv A0 '' p) := by
          aesop;
        have h_equiv : p = {w : ↑(F.restrict A0).domain | (F.restrictEquiv A0 w : ↑F.domain) ∈ Subtype.val '' (F.restrictEquiv A0 '' p)} := by
          exact Set.ext fun x => h_equiv x;
        grind [equiv_restrict_restrict_of_subset];
      exact isCentered_of_equiv ( hPart0.centered p hp ) h_equiv.symm;
    · have h_subset : Subtype.val '' (F.restrictEquiv A0 '' p) ⊆ A0 := by
        grind +revert;
      apply_rules [ ContinuouslyReduces.rank_monotone ];
      · exact (F.restrict _).hScat;
      · exact (F.restrict A0).hScat;
      · exact restrict_reduces_of_subset _ h_subset

/-- **Phase 3b**: the complement `P \ P'` (with `P' = P ∩ F⁻¹(U)`) has `CB`-rank `< β`
(`CenteredasPgluing`: removing a clopen neighbourhood of the cocenter strictly drops the rank),
and so, being of rank `< β ≤ α`, admits by `FG(<α)` (`exists_cPartition_of_FGBelow`) a
`c`-partition all of whose blocks have rank `< β`. Memoir, `6_double_successor_memo.tex:63-64`
("`CB(f↾A_P) < β`, so by `FG(<α)` we get `𝒫_P` ... of `CB`-rank `< β`"). Phrased directly in
terms of subsets of `F.domain` so the blocks can be unioned straight into `Part'`. -/
theorem refiningBy1_split_complement
    {α : Ordinal.{0}} (hFG : ScatFun.FGBelow α)
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} {β : Ordinal.{0}} (hβα : β ≤ α) (hgβ : CBRank g.func = β)
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y) :
    ∃ Q : Set (Set ↑F.domain), Q.Countable ∧ (∀ R ∈ Q, R ⊆ P \ (P ∩ F.func ⁻¹' U)) ∧
      (∀ R ∈ Q, IsClopen R) ∧ Q.PairwiseDisjoint id ∧ ⋃₀ Q = P \ (P ∩ F.func ⁻¹' U) ∧
      (∀ R ∈ Q, IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β) := by
  -- `P \ (P ∩ F⁻¹ U) = P ∩ F⁻¹ Uᶜ =: A0`, clopen, of rank `< β` (rank-drop lemma).
  have hset : P \ (P ∩ F.func ⁻¹' U) = P ∩ F.func ⁻¹' Uᶜ := by
    ext x; simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    tauto
  rw [hset]
  set A0 : Set ↑F.domain := P ∩ F.func ⁻¹' Uᶜ with hA0def
  have hA0cl : IsClopen A0 := (hA.isClopen P hP.choose).inter ((hU.compl).preimage F.hCont)
  have hrank : CBRank (F.restrict A0).func < β :=
    refiningBy1_complement_cbRank_lt hA hgβ hU hyU hP
  -- `FG(<α)` gives a `c`-partition of `F.restrict A0`; transport it to ambient pieces.
  obtain ⟨Part0, hPart0⟩ :=
    exists_cPartition_of_FGBelow hFG (F.restrict A0) (lt_of_lt_of_le hrank hβα)
  obtain ⟨Q, hQc, hQsub, hQcl, hQdisj, hQcov, hQprop⟩ :=
    cPartition_restrict_transport F A0 hA0cl hPart0
  refine ⟨Q, hQc, hQsub, hQcl, hQdisj, hQcov, fun R hR => ?_⟩
  obtain ⟨hcent, hpr⟩ := hQprop R hR
  exact ⟨hcent, lt_of_le_of_lt hpr hrank⟩

/-- **Phase 3**: splitting a lump piece `P` over the regularizing neighbourhood `U`
(Phase 2b) into `P' = P ∩ F⁻¹(U)` and the complement `P \ P'`. On `P'`, `F` still restricts
to (something `≡`) `g`, by centeredness; the complement has `CB`-rank `< β`
(`CenteredasPgluing`) and, by `FG(<α)` (`exists_cPartition_of_FGBelow`), admits a
sub-partition all of whose blocks have rank `< β`. Memoir, `6_double_successor_memo.tex:63-64`.
Phrased directly in terms of subsets of `F.domain` (never re-bundling `F.restrict (P\P')`
into a fresh `ScatFun`), so the resulting pieces can be unioned straight into `Part'`. Now
fully wired: the witness `P' = P ∩ F.func ⁻¹' U` is clopen as the intersection of the clopen
piece `P` with the preimage of the clopen `U` under the continuous `F.func`; the two remaining
obligations are `refiningBy1_Ppart_equiv` (Phase 3a) and `refiningBy1_split_complement`
(Phase 3b). -/
theorem refiningBy1_split_piece
    {α : Ordinal.{0}} (hFG : ScatFun.FGBelow α)
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} {β : Ordinal.{0}} (hβα : β ≤ α) (hgβ : CBRank g.func = β)
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y) :
    ∃ P' : Set ↑F.domain, P' ⊆ P ∧ IsClopen P' ∧ ScatFun.Equiv (F.restrict P') g ∧
      ∃ Q : Set (Set ↑F.domain), Q.Countable ∧ (∀ R ∈ Q, R ⊆ P \ P') ∧
        (∀ R ∈ Q, IsClopen R) ∧ Q.PairwiseDisjoint id ∧ ⋃₀ Q = P \ P' ∧
        (∀ R ∈ Q, IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β) :=
  ⟨P ∩ F.func ⁻¹' U, Set.inter_subset_left,
    (hA.isClopen P hP.choose).inter (hU.preimage F.hCont),
    refiningBy1_Ppart_equiv hA hU hyU hP,
    refiningBy1_split_complement hFG hA hβα hgβ hU hyU hP⟩

/-- **CB-rank of a restrict-of-restrict, packaged for `CBRank` only.** The doubly-restricted
`(F.restrict D).restrict {w | (restrictEquiv D w) ∈ A0}` (for `A0 ⊆ D`) has the same `CB`-rank
as `F.restrict A0`; they differ only by the domain-identifying homeomorphism. This is the
`CBRank`-only slice of `restrict_restrict_transfer` (which additionally threads an irrelevant
`hdist` hypothesis). -/
lemma cbRank_restrict_restrict_eq (F : ScatFun) (D A0 : Set ↑F.domain) (hA0D : A0 ⊆ D) :
    CBRank ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func
      = CBRank (F.restrict A0).func := by
  rw [ScatFun.restrict_restrict_func_eq F D A0 hA0D]
  exact CBRank_comp_homeomorph _ (F.restrict A0).func

/-
The union `(⋃ 𝒫_{(g,y)}) ∩ F⁻¹V` of the `V`-corestricted lump block pieces has `CB`-rank
`β`: each `F↾(P ∩ F⁻¹V)` is `≡ g` (`refiningBy1_Ppart_equiv`), hence of rank `β`, and
`cbRank_restrict_sUnion_const` lifts this to the countable clopen union.
-/
lemma piece_corestrict_inter_cbRank_eq
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y)
    {β : Ordinal.{0}} (hβ : hA.lumpRank g = β)
    {V : Set Baire} (hV : IsClopen V) (hyV : y ∈ V) :
    CBRank (F.restrict ((⋃₀ hA.blockPieces g y) ∩ F.func ⁻¹' V)).func = β := by
  have h_countable : Set.Countable (Set.image (fun P => P ∩ F.func ⁻¹' V) (hA.blockPieces g y)) := by
    refine' Set.Countable.image _ _;
    exact hA.countable.mono fun P hP => hP.choose;
  convert cbRank_restrict_sUnion_const h_countable _ _ _ using 1;
  · congr! 2;
    · simp +decide [ Set.sUnion_eq_biUnion, Set.iUnion_inter ];
    · simp +decide [ Set.sUnion_eq_biUnion ];
      simp +decide [ Set.iUnion_inter ];
    · congr! 2;
      ext; simp [Set.mem_iUnion, Set.mem_inter_iff];
      exact ⟨ fun ⟨ ⟨ t, ht₁, ht₂ ⟩, ht₃ ⟩ => ⟨ t, ht₂, ht₁, ht₃ ⟩, fun ⟨ t, ht₁, ht₂, ht₃ ⟩ => ⟨ ⟨ t, ht₂, ht₁ ⟩, ht₃ ⟩ ⟩;
  · rintro _ ⟨ P, hP, rfl ⟩;
    exact IsClopen.inter ( hA.isClopen P hP.choose ) ( hV.preimage F.hCont );
  · exact Set.Nonempty.image _ ( refiningBy1_blockPieces_nonempty hA hlump );
  · rintro _ ⟨ P, hP, rfl ⟩;
    convert hβ using 1;
    convert cbRank_eq_of_equiv ( refiningBy1_Ppart_equiv hA hV hyV hP ) using 1

/-- **CB-rank preservation under corestriction to a clopen neighbourhood of the cocenter,
for the lump piece `h = f_{(g,y)}`.** Every block piece `P ∈ 𝒫_{(g,y)}` is centered with
cocenter `y`, so corestricting `F↾P` to a clopen neighbourhood `V ∋ y` leaves it `≡ g`
(`refiningBy1_Ppart_equiv`); hence the whole corestriction
`h↾V = F↾((⋃ 𝒫_{(g,y)}) ∩ F⁻¹V)` is a countable clopen union of pieces all of `CB`-rank `β`
(`piece_corestrict_inter_cbRank_eq`), so of rank `β`. The doubly-restricted `h↾V` is
transported to `F↾((⋃ 𝒫_{(g,y)}) ∩ F⁻¹V)` via `cbRank_restrict_restrict_eq`. -/
lemma piece_corestrict_cbRank_eq
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y)
    {β : Ordinal.{0}} (hβ : hA.lumpRank g = β)
    {V : Set Baire} (hV : IsClopen V) (hyV : y ∈ V) :
    CBRank ((hA.piece g y).restrict ((hA.piece g y).func ⁻¹' V)).func = β := by
  have hpiece : hA.piece g y = F.restrict (⋃₀ hA.blockPieces g y) := rfl
  have hset : ((F.restrict (⋃₀ hA.blockPieces g y)).func ⁻¹' V)
      = {w : ↑(F.restrict (⋃₀ hA.blockPieces g y)).domain |
          (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain)
            ∈ ((⋃₀ hA.blockPieces g y) ∩ F.func ⁻¹' V)} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
    exact ⟨fun hw => ⟨(F.restrictEquiv (⋃₀ hA.blockPieces g y) w).2, hw⟩, fun hw => hw.2⟩
  rw [hpiece, hset,
    cbRank_restrict_restrict_eq F (⋃₀ hA.blockPieces g y)
      ((⋃₀ hA.blockPieces g y) ∩ F.func ⁻¹' V) Set.inter_subset_left]
  exact piece_corestrict_inter_cbRank_eq hA hlump hβ hV hyV

/-- **Refine a `c`-partition at a subfamily of pieces — the one reusable refinement
primitive.** Given a `c`-partition `Part` of `F`, a subfamily `B ⊆ Part`, and, for every
`P ∈ B`, a family `new P` of clopen centered pieces partitioning `P` (each `⊆ P`, pairwise
disjoint, covering `P`), the set

  `Part' = (Part \ B) ∪ ⋃_{P ∈ B} new P`

is again a `c`-partition of `F`, finer than `Part`, and containing every surviving piece
`Part \ B`.

This is deliberately the *only* partition-refinement bookkeeping lemma in the chapter: it is
pure set-level bookkeeping (countability / clopenness / disjointness / cover / centeredness of
the reassembled set), with **no** lump or `CB`-rank reasoning. `refiningBy1` instantiates it
with `B = 𝒫_{(g,y)}` and `new P = insert P' 𝒫_P`; the fine-partition existence induction
iterates it. All the genuine mathematical content — *which* pieces to split and *how* — lives
in the caller's choice of `new`, keeping this atom reusable verbatim and avoiding a general
"partition-refinement calculus". -/
theorem isCPartition_refine_at_family
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {B : Set (Set ↑F.domain)} (hB : B ⊆ Part)
    (new : Set ↑F.domain → Set (Set ↑F.domain))
    (hcount : ∀ P ∈ B, (new P).Countable)
    (hsub : ∀ P ∈ B, ∀ R ∈ new P, R ⊆ P)
    (hclopen : ∀ P ∈ B, ∀ R ∈ new P, IsClopen R)
    (hdisj : ∀ P ∈ B, (new P).PairwiseDisjoint id)
    (hcov : ∀ P ∈ B, ⋃₀ new P = P)
    (hcent : ∀ P ∈ B, ∀ R ∈ new P, IsCentered (F.restrict R).func) :
    F.IsCPartition ((Part \ B) ∪ ⋃ P ∈ B, new P) ∧
      IsFinerCPartition ((Part \ B) ∪ ⋃ P ∈ B, new P) Part ∧
      Part \ B ⊆ (Part \ B) ∪ ⋃ P ∈ B, new P := by
  set Part' := (Part \ B) ∪ ⋃ P ∈ B, new P with hPart'_def
  -- Membership dichotomy for a piece of `Part'`.
  have hmem : ∀ X ∈ Part', X ∈ Part \ B ∨ ∃ P ∈ B, X ∈ new P := by
    intro X hX
    rcases hX with hXl | hXr
    · exact Or.inl hXl
    · obtain ⟨P, hPB, hXP⟩ := Set.mem_iUnion₂.mp hXr
      exact Or.inr ⟨P, hPB, hXP⟩
  have hBc : B.Countable := hA.countable.mono hB
  -- Countability.
  have hcountable : Part'.Countable :=
    (hA.countable.mono Set.diff_subset).union (hBc.biUnion hcount)
  -- Clopenness.
  have hclopen' : ∀ P ∈ Part', IsClopen P := by
    intro X hX
    rcases hmem X hX with hXl | ⟨P, hPB, hXP⟩
    · exact hA.isClopen X hXl.1
    · exact hclopen P hPB X hXP
  -- Pairwise disjointness (the only bookkeeping step with case analysis).
  have hdisj' : Part'.PairwiseDisjoint id := by
    rintro X hX Y hY hXY
    show Disjoint X Y
    rcases hmem X hX with hXl | ⟨P, hPB, hXP⟩ <;> rcases hmem Y hY with hYl | ⟨Q, hQB, hYQ⟩
    · exact hA.pairwiseDisjoint hXl.1 hYl.1 hXY
    · -- `X` survives, `Y ⊆ Q` a split piece; `X ≠ Q` since `X ∉ B ∋ Q`.
      have hXQ : X ≠ Q := fun h => hXl.2 (h ▸ hQB)
      exact (hA.pairwiseDisjoint hXl.1 (hB hQB) hXQ).mono_right (hsub Q hQB Y hYQ)
    · have hPY : P ≠ Y := fun h => hYl.2 (h ▸ hPB)
      exact (hA.pairwiseDisjoint (hB hPB) hYl.1 hPY).mono_left (hsub P hPB X hXP)
    · by_cases hPQ : P = Q
      · subst hPQ; exact hdisj P hPB hXP hYQ hXY
      · exact ((hA.pairwiseDisjoint (hB hPB) (hB hQB) hPQ).mono_left
          (hsub P hPB X hXP)).mono_right (hsub Q hQB Y hYQ)
  -- Cover.
  have hcov' : ⋃₀ Part' = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxU : x ∈ (Set.univ : Set ↑F.domain) := Set.mem_univ x
    rw [← hA.sUnion_eq] at hxU
    obtain ⟨P, hPPart, hxP⟩ := hxU
    by_cases hPB : P ∈ B
    · rw [← hcov P hPB] at hxP
      obtain ⟨R, hRnew, hxR⟩ := hxP
      exact ⟨R, Or.inr (Set.mem_iUnion₂.mpr ⟨P, hPB, hRnew⟩), hxR⟩
    · exact ⟨P, Or.inl ⟨hPPart, hPB⟩, hxP⟩
  -- Centeredness.
  have hcent' : ∀ P ∈ Part', IsCentered (F.restrict P).func := by
    intro X hX
    rcases hmem X hX with hXl | ⟨P, hPB, hXP⟩
    · exact hA.centered X hXl.1
    · exact hcent P hPB X hXP
  refine ⟨⟨hcountable, hclopen', hdisj', hcov', hcent'⟩, ?_, Set.subset_union_left⟩
  -- Finer.
  intro X hX
  rcases hmem X hX with hXl | ⟨P, hPB, hXP⟩
  · exact ⟨X, hXl.1, subset_rfl⟩
  · exact ⟨P, hB hPB, hsub P hPB X hXP⟩

/-- **Reducing a centered function to a corestriction near its cocenter.** If `G` is centered
with cocenter `y = cocenter G`, then for every open neighbourhood `Wc ∈ y` we have
`G ≤ G.coRestrict Wc`. -/
lemma reduces_coRestrict_cocenter_nbhd (G : ScatFun) (hc : IsCentered G.func)
    {Wc : Set Baire} (hWc : IsOpen Wc) (hcocWc : cocenter G.func hc ∈ Wc) :
    ScatFun.Reduces G (G.coRestrict Wc) := by
  convert ScatFun.reduces_coRestrict_of_subtype G G Wc _;
  obtain ⟨x, hx⟩ : ∃ x : ↑G.domain, G.func x ∈ Wc ∧ IsCenterFor G.func x := by
    exact ⟨ hc.choose, by simpa [ cocenter ] using hcocWc, hc.choose_spec ⟩;
  have := hx.2 ( { w : ↑G.domain | G.func w ∈ Wc } ) ( hWc.preimage G.hCont ) ?_;
  · convert this using 1;
  · exact hx.1

/-- **A centered scattered function reduces into its corestriction to a clopen neighbourhood of
its cocenter, phrased for `F.restrict A`.** If `F.restrict A` is centered with cocenter `y` and
`U` is a clopen neighbourhood of `y`, then `F.restrict A` reduces to `F.restrict (A ∩ F⁻¹U)`.
This packages `reduces_coRestrict_cocenter_nbhd` (which gives `F.restrict A ≤ (F.restrict A).coRestrict U`)
together with the restrict-of-restrict identification `(F.restrict A).coRestrict U = F.restrict (A ∩ F⁻¹U)`
(via `restrict_restrict_domain_eq`/`restrict_restrict_func_eq`). -/
lemma restrict_reduces_restrict_inter_of_cocenter_mem
    {F : ScatFun} (A : Set ↑F.domain) (hcent : IsCentered (F.restrict A).func)
    {U : Set Baire} (hU : IsOpen U) (hyU : cocenter (F.restrict A).func hcent ∈ U) :
    ScatFun.Reduces (F.restrict A) (F.restrict (A ∩ F.func ⁻¹' U)) := by
  have h1 : ScatFun.Reduces (F.restrict A) ((F.restrict A).coRestrict U) :=
    reduces_coRestrict_cocenter_nbhd (F.restrict A) hcent hU hyU
  have hset : {z : ↑(F.restrict A).domain | (F.restrict A).func z ∈ U}
      = {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ (A ∩ F.func ⁻¹' U)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro hw
      exact ⟨(F.restrictEquiv A w).2, by simpa [ScatFun.restrict, ScatFun.restrictEquiv] using hw⟩
    · intro hw
      simpa [ScatFun.restrict, ScatFun.restrictEquiv] using hw.2
  have h2 : ScatFun.Reduces ((F.restrict A).coRestrict U) (F.restrict (A ∩ F.func ⁻¹' U)) := by
    have hfunc := ScatFun.restrict_restrict_func_eq F A (A ∩ F.func ⁻¹' U) Set.inter_subset_left
    have hgoal : ScatFun.Reduces
        ((F.restrict A).restrict
          {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ (A ∩ F.func ⁻¹' U)})
        (F.restrict (A ∩ F.func ⁻¹' U)) := by
      show ContinuouslyReduces _ (F.restrict (A ∩ F.func ⁻¹' U)).func
      rw [hfunc]
      exact (ContinuouslyReduces.refl (F.restrict (A ∩ F.func ⁻¹' U)).func).comp_homeomorph_left
        (Homeomorph.setCongr (ScatFun.restrict_restrict_domain_eq F A (A ∩ F.func ⁻¹' U)
          Set.inter_subset_left))
    have hco : (F.restrict A).coRestrict U
        = (F.restrict A).restrict
            {w : ↑(F.restrict A).domain | (F.restrictEquiv A w : ↑F.domain) ∈ (A ∩ F.func ⁻¹' U)} := by
      unfold ScatFun.coRestrict; rw [hset]
    rw [hco]; exact hgoal
  exact h1.trans h2

/-- **`Reduces G (G.restrict W)` is exactly the `IsCenterFor`-style continuous reduction to the
subtype `W`.** Bookkeeping bridge between `ScatFun.Reduces` of a self-restriction and the
`ContinuouslyReduces G.func (G.func ∘ Subtype.val)` shape that `IsCenterFor` uses, via the
homeomorphism `G.restrictEquiv W` (`ContinuouslyReduces.comp_homeomorph_right`). -/
lemma reduces_restrict_iff_continuouslyReduces_subtype (G : ScatFun) (W : Set ↑G.domain) :
    ScatFun.Reduces G (G.restrict W)
      ↔ ContinuouslyReduces G.func (G.func ∘ (Subtype.val : ↑W → ↑G.domain)) := by
  have hfunc : (G.restrict W).func
      = (G.func ∘ (Subtype.val : ↑W → ↑G.domain)) ∘ (G.restrictEquiv W) := rfl
  constructor
  · intro h
    have h' : ContinuouslyReduces G.func
        ((G.func ∘ (Subtype.val : ↑W → ↑G.domain)) ∘ (G.restrictEquiv W)) := by
      rw [← hfunc]; exact h
    have hcomp := h'.comp_homeomorph_right (G.restrictEquiv W).symm
    have heq : ((G.func ∘ (Subtype.val : ↑W → ↑G.domain)) ∘ (G.restrictEquiv W))
        ∘ (G.restrictEquiv W).symm = G.func ∘ (Subtype.val : ↑W → ↑G.domain) := by
      funext z; simp [Function.comp]
    rwa [heq] at hcomp
  · intro h
    have hcomp := h.comp_homeomorph_right (G.restrictEquiv W)
    show ContinuouslyReduces G.func (G.restrict W).func
    rw [hfunc]; exact hcomp

/-- **Lifting a center of `F.restrict (A ∩ F⁻¹V)` to a center of `F.restrict A`.** Given that
`F.restrict A` reduces into the corestriction `F.restrict (A ∩ F⁻¹V)` (`hred`), any center `c` of
the corestriction lifts to a center of `F.restrict A` at the same underlying point. Proof by the
sandwich `F↾A ≤ F↾(A∩F⁻¹V) ≤ (F↾(A∩F⁻¹V))|W ≤ (F↾A)|V` for every open `V ∋ x`. -/
lemma isCenterFor_restrict_of_isCenterFor_restrict_inter
    {F : ScatFun} (A : Set ↑F.domain) {V : Set Baire}
    (hred : ScatFun.Reduces (F.restrict A) (F.restrict (A ∩ F.func ⁻¹' V)))
    {c : ↑(F.restrict (A ∩ F.func ⁻¹' V)).domain}
    (hc : IsCenterFor (F.restrict (A ∩ F.func ⁻¹' V)).func c)
    (x : ↑(F.restrict A).domain) (hx : x.val = c.val) :
    IsCenterFor (F.restrict A).func x := by
  intro W hW hxW
  rw [← reduces_restrict_iff_continuouslyReduces_subtype (F.restrict A) W]
  -- Continuous inclusion `ι : ↑H.domain → ↑G.domain`.
  have hιcont : Continuous
      (fun w : ↑(F.restrict (A ∩ F.func ⁻¹' V)).domain =>
        (⟨w.1, w.2.choose, w.2.choose_spec.1⟩ : ↑(F.restrict A).domain)) :=
    continuous_subtype_val.subtype_mk _
  set WH : Set ↑(F.restrict (A ∩ F.func ⁻¹' V)).domain :=
    {w | (⟨w.1, w.2.choose, w.2.choose_spec.1⟩ : ↑(F.restrict A).domain) ∈ W} with hWH_def
  have hWHopen : IsOpen WH := hW.preimage hιcont
  have hcWH : c ∈ WH := by
    show (⟨c.1, c.2.choose, c.2.choose_spec.1⟩ : ↑(F.restrict A).domain) ∈ W
    have hxeq : (⟨c.1, c.2.choose, c.2.choose_spec.1⟩ : ↑(F.restrict A).domain) = x :=
      Subtype.ext hx.symm
    rw [hxeq]; exact hxW
  have h2 : ScatFun.Reduces (F.restrict (A ∩ F.func ⁻¹' V))
      ((F.restrict (A ∩ F.func ⁻¹' V)).restrict WH) :=
    (reduces_restrict_iff_continuouslyReduces_subtype _ WH).mpr (hc WH hWHopen hcWH)
  have h3 : ScatFun.Reduces ((F.restrict (A ∩ F.func ⁻¹' V)).restrict WH)
      ((F.restrict A).restrict W) := by
    refine ⟨fun p => ⟨p.1, ⟨p.2.choose.choose, p.2.choose.choose_spec.1⟩, p.2.choose_spec⟩,
      continuous_subtype_val.subtype_mk _, id, continuousOn_id, ?_⟩
    intro p
    simp [ScatFun.restrict, ScatFun.restrictEquiv]
  exact hred.trans (h2.trans h3)

/--
**Cocenter of the `U`-part of a lump piece.** For a lump piece `P ∈ 𝒫_{(g,y)}`, the
corestriction `F↾(P ∩ F⁻¹U)` to a clopen neighbourhood `U ∋ y` of the cocenter still has
cocenter `y`. Its centeredness is `refiningBy1_Ppart_equiv` combined with `isCentered_of_equiv`;
the cocenter is determined by the fact that `F↾P` is centered with cocenter `y` and
corestricting to a neighbourhood of the cocenter does not move it.
-/
lemma refiningBy1_Ppart_cocenter
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire}
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y)
    (hcent : IsCentered (F.restrict (P ∩ F.func ⁻¹' U)).func) :
    cocenter (F.restrict (P ∩ F.func ⁻¹' U)).func hcent = y := by
      obtain ⟨ hP1, hPeq, hPcoc ⟩ := hP;
      -- By Fact A, every center z of F.restrict P has (F.restrict P).func z = y.
      have hfactA : ∀ z : ↑(F.restrict P).domain, IsCenterFor (F.restrict P).func z → (F.restrict P).func z = y := by
        intros z hz
        have hfactA : cocenter (F.restrict P).func (hA.centered P hP1) = y := by
          exact hPcoc;
        have := scatteredHaveCocenter ( F.restrict P ).func ( F.restrict P ).hScat z ( hA.centered P hP1 ).choose hz ( hA.centered P hP1 ).choose_spec; aesop;
      -- Let c := hcent.choose. Its underlying point lies in P ∩ F.func ⁻¹' U, hence in P; extract a point x : ↑(F.restrict P).domain with x.val = c.val.
      obtain ⟨x, hx⟩ : ∃ x : ↑(F.restrict P).domain, x.val = (hcent.choose : ↑(F.restrict (P ∩ F.func ⁻¹' U)).domain).val := by
        have := hcent.choose.2;
        exact ⟨ ⟨ _, this.1, this.2.1 ⟩, rfl ⟩;
      -- By `isCenterFor_restrict_of_isCenterFor_restrict_inter P hred hcent.choose_spec x (by rfl/simp)` we get `IsCenterFor (F.restrict P).func x`.
      have hcenterP : IsCenterFor (F.restrict P).func x := by
        apply isCenterFor_restrict_of_isCenterFor_restrict_inter P (by
        apply restrict_reduces_restrict_inter_of_cocenter_mem P (hA.centered P hP1) hU.isOpen;
        convert hyU using 1) hcent.choose_spec x hx;
      unfold ScatFun.restrict;
      unfold ScatFun.restrictEquiv; aesop;

/--
**`¬ IsLump g y` after reassembly** (clause 1 of `refiningBy1_reassemble`). The block
pieces of the refined partition `𝒫'` with representative `g` and cocenter `y` are exactly the
`U`-parts `P' = P ∩ F⁻¹U` of the old lump pieces (`Q_P` pieces have rank `< β = CB g` so are
not `≡ g`; surviving pieces are not `≡ g` with cocenter `y` since they would then lie in
`𝒫_{(g,y)}`). Hence `⋃ 𝒫'_{(g,y)} = (⋃ 𝒫_{(g,y)}) ∩ F⁻¹U`, so `f'_{(g,y)} =
(f_{(g,y)})↾U`, which is `𝒲`-regular by `hUreg`; thus `(g,y)` is no longer a lump.
-/
lemma refiningBy1_reassemble_not_lump
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y)
    {β : Ordinal.{0}} (hβ : hA.lumpRank g = β)
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    (hUreg : IsOmegaRegularAt ((hA.piece g y).restrict ((hA.piece g y).func ⁻¹' U)) y)
    {P' : Set ↑F.domain → Set ↑F.domain} {Q : Set ↑F.domain → Set (Set ↑F.domain)}
    (hP'eqU : ∀ P ∈ hA.blockPieces g y, P' P = P ∩ F.func ⁻¹' U)
    (_hP'sub : ∀ P ∈ hA.blockPieces g y, P' P ⊆ P)
    (_hP'cl : ∀ P ∈ hA.blockPieces g y, IsClopen (P' P))
    (hP'equiv : ∀ P ∈ hA.blockPieces g y, (F.restrict (P' P)).Equiv g)
    (_hQsub : ∀ P ∈ hA.blockPieces g y, ∀ R ∈ Q P, R ⊆ P \ P' P)
    (hQprop : ∀ P ∈ hA.blockPieces g y, ∀ R ∈ Q P,
        IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β)
    (hA' : F.IsCPartition ((Part \ hA.blockPieces g y) ∪
        ⋃ P ∈ hA.blockPieces g y, insert (P' P) (Q P))) :
    ¬ hA'.IsLump g y := by
      refine fun h => h.2.2 ?_;
      convert hUreg using 1;
      have h_piece_eq : ⋃₀ hA'.blockPieces g y = (⋃₀ hA.blockPieces g y) ∩ F.func ⁻¹' U := by
        have h_piece_eq : hA'.blockPieces g y = (fun P => P' P) '' hA.blockPieces g y := by
          apply Set.eq_of_subset_of_subset;
          · intro R hR;
            obtain ⟨ hR₁, hR₂, hR₃ ⟩ := hR;
            rcases hR₁ with ( hR₁ | hR₁ );
            · grind +locals;
            · obtain ⟨ P, hP₁, hP₂ ⟩ := Set.mem_iUnion₂.mp hR₁;
              cases hP₂;
              · exact ⟨ P, hP₁, by subst_vars; rfl ⟩;
              · have := hQprop P hP₁ R ‹_›;
                have := cbRank_eq_of_equiv hR₂;
                unfold ScatFun.IsCPartition.lumpRank at hβ; aesop;
          · rintro _ ⟨ P, hP, rfl ⟩;
            refine ⟨ ?_, ?_ ⟩;
            exact Or.inr <| Set.mem_iUnion₂.mpr ⟨ P, hP, Set.mem_insert _ _ ⟩;
            refine ⟨ hP'equiv P hP, ?_ ⟩
            generalize_proofs at *;
            convert refiningBy1_Ppart_cocenter hA hU hyU hP _ using 1
            generalize_proofs at *;
            · rw [ ScatFun.IsCPartition.cocenterOf ];
              grind;
            · grind +locals;
        grind;
      unfold ScatFun.IsCPartition.piece;
      rw [ScatFun.restrict];
      congr! 1;
      · simp +decide [ h_piece_eq, ScatFun.restrict ];
        ext; simp [ScatFun.restrictEquiv];
        exact ⟨ fun ⟨ h₁, h₂, h₃ ⟩ => ⟨ ⟨ h₁, h₂ ⟩, h₃ ⟩, fun ⟨ ⟨ h₁, h₂ ⟩, h₃ ⟩ => ⟨ h₁, h₂, h₃ ⟩ ⟩;
      · unfold ScatFun.restrict; simp +decide ;
        unfold ScatFun.restrictEquiv; simp +decide [ Function.comp_def ] ;
        congr! 1;
        · congr! 1;
        · grind

/--
**New-lump rank bound after reassembly** (clause 2 of `refiningBy1_reassemble`). Any
`𝒫'`-lump `(g', y')` that was not already a `𝒫`-lump must live on the freshly-introduced
pieces. The `Q_P` pieces all have `CB`-rank `< β`; the `P'` pieces carry only the (now
dissolved) representative `(g, y)`. Hence such a new lump has `lumpRank g' < β`.
-/
lemma refiningBy1_reassemble_new_lump_rank
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y)
    {β : Ordinal.{0}} (hβ : hA.lumpRank g = β)
    {U : Set Baire} (hU : IsClopen U) (hyU : y ∈ U)
    (hUreg : IsOmegaRegularAt ((hA.piece g y).restrict ((hA.piece g y).func ⁻¹' U)) y)
    {P' : Set ↑F.domain → Set ↑F.domain} {Q : Set ↑F.domain → Set (Set ↑F.domain)}
    (hP'eqU : ∀ P ∈ hA.blockPieces g y, P' P = P ∩ F.func ⁻¹' U)
    (hP'sub : ∀ P ∈ hA.blockPieces g y, P' P ⊆ P)
    (hP'cl : ∀ P ∈ hA.blockPieces g y, IsClopen (P' P))
    (hP'equiv : ∀ P ∈ hA.blockPieces g y, (F.restrict (P' P)).Equiv g)
    (hQsub : ∀ P ∈ hA.blockPieces g y, ∀ R ∈ Q P, R ⊆ P \ P' P)
    (hQprop : ∀ P ∈ hA.blockPieces g y, ∀ R ∈ Q P,
        IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β)
    (hA' : F.IsCPartition ((Part \ hA.blockPieces g y) ∪
        ⋃ P ∈ hA.blockPieces g y, insert (P' P) (Q P))) :
    ∀ g' y', hA'.IsLump g' y' → hA.IsLump g' y' ∨ hA'.lumpRank g' < β := by
      intro g' y' hlump'
      by_cases hβle : β ≤ hA'.lumpRank g';
      · have h_blockPieces_eq : ∀ R ∈ hA'.blockPieces g' y', R ∈ hA.blockPieces g' y' := by
          intro R hR
          obtain ⟨hRPart, hR_equiv, hR_cocenter⟩ := hR
          have hR_not_in_Q : ∀ P ∈ hA.blockPieces g y, ∀ R ∈ Q P, ¬(F.restrict R).Equiv g' := by
            intros P hP R hR hR_equiv
            have hR_rank : CBRank (F.restrict R).func < β := by
              exact hQprop P hP R hR |>.2
            have hR_rank_g' : CBRank g'.func ≥ β := by
              exact hβle.trans ( by rfl )
            have hR_rank_contra : CBRank (F.restrict R).func = CBRank g'.func := by
              exact cbRank_eq_of_equiv hR_equiv
            exact absurd hR_rank_contra (by
            exact ne_of_lt ( lt_of_lt_of_le hR_rank hR_rank_g' ))
          have hR_not_in_P' : ∀ P ∈ hA.blockPieces g y, R ≠ P' P := by
            intro P hP hR_eq_P'
            have hR_equiv_g : (F.restrict R).Equiv g := by
              exact hR_eq_P'.symm ▸ hP'equiv P hP
            have hR_equiv_g' : (F.restrict R).Equiv g' := by
              exact hR_equiv
            have hR_equiv_g_g' : g.Equiv g' := by
              grind [ScatFun.Equiv.symm, ScatFun.Equiv.trans]
            have hR_cocenter_y : y' = y := by
              have hR_cocenter_y : cocenter (F.restrict R).func (hA'.centered R hRPart) = y := by
                convert refiningBy1_Ppart_cocenter hA hU hyU hP _ using 1;
                grind +qlia;
                grind [ScatFun.IsCPartition.centered];
              convert hR_cocenter_y using 1;
              convert hR_cocenter.symm using 1
            have hR_not_lump : ¬ hA'.IsLump g y := by
              apply refiningBy1_reassemble_not_lump hA hlump hβ hU hyU hUreg hP'eqU hP'sub hP'cl hP'equiv hQsub hQprop hA'
            exact hR_not_lump ⟨by
            exact ⟨⟨R, hRPart⟩, hR_cocenter_y ▸ hR_cocenter⟩, by
              exact hlump.2.1, by
              convert hlump'.2.2 using 1;
              rw [hR_cocenter_y];
              rw [ScatFun.IsCPartition.piece, ScatFun.IsCPartition.piece];
              rw [ show hA'.blockPieces g y = hA'.blockPieces g' y from ?_ ];
              ext R; simp [ScatFun.IsCPartition.blockPieces];
              exact fun _ _ => ⟨ fun h => h.trans hR_equiv_g_g', fun h => h.trans hR_equiv_g_g'.symm ⟩⟩
          have hR_in_Part : R ∈ Part := by
            rcases hRPart with ( ⟨ hRPart₁, hRPart₂ ⟩ | hRPart₁ ) <;> simp_all +decide;
            obtain ⟨ P, hP₁, hP₂ ⟩ := Set.mem_iUnion₂.mp hRPart₁; specialize hR_not_in_Q P hP₁; specialize hR_not_in_P' P hP₁; aesop;
          exact ⟨hR_in_Part, hR_equiv, hR_cocenter⟩;
        refine Or.inl ⟨ ?_, ?_, ?_ ⟩;
        · obtain ⟨ R, hR ⟩ := refiningBy1_blockPieces_nonempty hA' hlump';
          obtain ⟨ hR₁, hR₂, hR₃ ⟩ := h_blockPieces_eq R hR;
          exact ⟨ ⟨ R, hR₁ ⟩, hR₃ ⟩;
        · exact hlump'.2.1;
        · convert hlump'.2.2 using 1;
          unfold ScatFun.IsCPartition.piece;
          rw [ show hA'.blockPieces g' y' = hA.blockPieces g' y' from ?_ ];
          refine Set.Subset.antisymm h_blockPieces_eq ?_;
          intro R hR;
          by_cases hR' : R ∈ hA.blockPieces g y;
          · have h_contra : ScatFun.Equiv g' g ∧ y' = y := by
              have h_contra : ScatFun.Equiv g' g := by
                have h_contra : ScatFun.Equiv (F.restrict R) g' ∧ ScatFun.Equiv (F.restrict R) g := by
                  exact ⟨ hR.choose_spec.1, hR'.choose_spec.1 ⟩;
                exact ScatFun.Equiv.trans h_contra.1.symm h_contra.2;
              have h_contra : hA.cocenterOf hR.1 = y' ∧ hA.cocenterOf hR'.1 = y := by
                exact ⟨ hR.2.2, hR'.2.2 ⟩;
              grind +splitIndPred;
            have h_contra : IsOmegaRegularAt (hA'.piece g' y') y' := by
              have h_contra : IsOmegaRegularAt (hA'.piece g y) y := by
                apply refiningBy1_reassemble_not_lump hA hlump hβ hU hyU hUreg hP'eqU hP'sub hP'cl hP'equiv hQsub hQprop hA' |> fun h => by
                  exact Classical.not_not.1 fun h' => h ⟨ by
                    obtain ⟨ P, hP ⟩ := hlump'.1;
                    exact ⟨ P, by aesop ⟩, by
                    exact hlump.2.1, h' ⟩;
              convert h_contra using 1;
              · have h_contra : ∀ R ∈ hA'.blockPieces g' y', R ∈ hA'.blockPieces g y := by
                  intros R hR
                  simp only [ScatFun.IsCPartition.blockPieces, mem_setOf_eq, ‹g'.Equiv g ∧ y' = y›, exists_and_left, mem_union, mem_diff, not_and, not_exists, mem_iUnion, mem_insert_iff, exists_prop] at hR ⊢;
                  exact ⟨ hR.1.trans ( by tauto ), hR.2 ⟩;
                have h_contra : ∀ R ∈ hA'.blockPieces g y, R ∈ hA'.blockPieces g' y' := by
                  intros R hR;
                  obtain ⟨ hR₁, hR₂, hR₃ ⟩ := hR;
                  exact ⟨ hR₁, by simpa [ ‹g'.Equiv g ∧ y' = y› ] using hR₂.trans ( ScatFun.Equiv.symm ( by tauto ) ), by simpa [ ‹g'.Equiv g ∧ y' = y› ] using hR₃ ⟩;
                exact congr_arg _ ( Set.ext fun x => by aesop );
              · tauto;
            exact False.elim <| hlump'.2.2 h_contra;
          · exact ⟨ hR.1 |> fun h => by aesop, hR.2.1, hR.2.2 ⟩;
      · exact Or.inr ( lt_of_not_ge hβle )

/-- **Phase 4 (reassembly) of `refiningBy1`.** Given the Phase 1–3 data — a regularizing
clopen neighbourhood `U ∋ y` making the lump piece `𝒲`-regular (`hUreg`) and, for every lump
piece `P`, its split into a `≡ g` part `P'` and a rank-`< β` sub-partition of `P \ P'`
(`hsplit`) — assemble the finer `c`-partition
`𝒫' = (𝒫 \ 𝒫_{g,y}) ∪ {P' | P ∈ 𝒫_{g,y}} ∪ ⋃ {𝒫_P | P ∈ 𝒫_{g,y}}` and verify the four
conclusion clauses. Memoir, `6_double_successor_memo.tex:65-70`:

* `IsFinerCPartition 𝒫' 𝒫`: each new piece is a subset of the lump piece it came from
  (`P' ⊆ P`, `R ⊆ P \ P' ⊆ P`), and surviving pieces are unchanged;
* `¬ IsLump g y`: after the split `𝒫'_{g,y} = {P' | P ∈ 𝒫_{g,y}}` and `⋃ 𝒫'_{g,y} =
  F⁻¹(U) ∩ ⋃ 𝒫_{g,y}`, so `f'_{(g,y)}` is `h↾U`, which is `𝒲`-regular by `hUreg`;
* piece survival `𝒫 \ 𝒫_{g,y} ⊆ 𝒫'`: immediate from the first summand;
* new lumps: any `𝒫'`-lump not already a `𝒫`-lump lives on the new pieces, all of `CB`-rank
  `< β` (`hsplit`'s rank bound), so has `lumpRank < β`.

**Structure.** All the *partition bookkeeping* is discharged in one shot by
`isCPartition_refine_at_family` (applied with `B = 𝒫_{(g,y)}` and
`new P = insert P' 𝒫_P`): that gives `F.IsCPartition Part'`, `IsFinerCPartition Part' Part`,
and the survival clause `Part \ 𝒫_{(g,y)} ⊆ Part'` for free. Only the two lump-analysis
clauses are left as inline gaps:

* `¬ IsLump g y`: the `hsplit` interface now records `P' = P ∩ F.func ⁻¹' U` (`hP'eqU`), which
  equates `⋃ 𝒫'_{g,y}` with `(⋃ 𝒫_{g,y}) ∩ F⁻¹U` and hence `f'_{(g,y)}` with `h↾U`, the
  `𝒲`-regular object of `hUreg`. The remaining work is the cocenter bookkeeping identifying
  `𝒫'_{g,y}` exactly with `{P' | P ∈ 𝒫_{g,y}}` (each `F.restrict P'` is `≡ g` with cocenter
  `y`, `refiningBy1_Ppart_equiv`).
* new-lump rank bound: any `Part'`-lump not already a `Part`-lump sits on a freshly-introduced
  piece; the `𝒫_P` pieces have `CB`-rank `< β` (`hQprop`), and the `P'` pieces carry only the
  now-dissolved `(g, y)`. -/
theorem refiningBy1_reassemble
    (α : Ordinal.{0}) (_hα : α < omega1) (_hFG : ScatFun.FGBelow α)
    (F : ScatFun) (_hFrank : CBRank F.func = α)
    (Part : Set (Set ↑F.domain)) (hA : F.IsCPartition Part)
    (g : ScatFun) (y : Baire) (hlump : hA.IsLump g y)
    (β : Ordinal.{0}) (hβ : hA.lumpRank g = β) (_hβα : β ≤ α)
    (U : Set Baire) (hU : IsClopen U) (hyU : y ∈ U)
    (hUreg : IsOmegaRegularAt ((hA.piece g y).restrict ((hA.piece g y).func ⁻¹' U)) y)
    (hsplit : ∀ P ∈ hA.blockPieces g y,
      ∃ P' : Set ↑F.domain, P' = P ∩ F.func ⁻¹' U ∧
        P' ⊆ P ∧ IsClopen P' ∧ ScatFun.Equiv (F.restrict P') g ∧
        ∃ Q : Set (Set ↑F.domain), Q.Countable ∧ (∀ R ∈ Q, R ⊆ P \ P') ∧
          (∀ R ∈ Q, IsClopen R) ∧ Q.PairwiseDisjoint id ∧ ⋃₀ Q = P \ P' ∧
          (∀ R ∈ Q, IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β)) :
    ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'),
      IsFinerCPartition Part' Part ∧
      ¬ hA'.IsLump g y ∧
      Part \ hA.blockPieces g y ⊆ Part' ∧
      (∀ g' y', hA'.IsLump g' y' → hA.IsLump g' y' ∨ hA'.lumpRank g' < β) ∧
      (∀ R ∈ Part', R ∈ Part ∨ CBRank (F.restrict R).func < β ∨
        ((F.restrict R).Equiv g ∧ ∃ hc : IsCentered (F.restrict R).func,
          cocenter (F.restrict R).func hc = y)) := by
  classical
  -- Choose, for each lump piece, its `≡ g` part `P'` and the sub-partition `Q` of `P \ P'`.
  choose! P' hP'eqU hP'sub hP'cl hP'equiv Q hQc hQsub hQcl hQdisj hQcov hQprop using hsplit
  set B := hA.blockPieces g y with hB_def
  -- The refinement replaces each lump piece `P` by `{P'} ∪ Q_P`.
  set new : Set ↑F.domain → Set (Set ↑F.domain) := fun P => insert (P' P) (Q P) with hnew_def
  have hBsub : B ⊆ Part := fun P hP => hP.choose
  -- Discharge the six bookkeeping hypotheses of the reusable refinement atom.
  have hcount_new : ∀ P ∈ B, (new P).Countable := fun P hP => (hQc P hP).insert _
  have hsub_new : ∀ P ∈ B, ∀ R ∈ new P, R ⊆ P := by
    intro P hP R hR
    rcases hR with rfl | hRQ
    · exact hP'sub P hP
    · exact (hQsub P hP R hRQ).trans Set.diff_subset
  have hclopen_new : ∀ P ∈ B, ∀ R ∈ new P, IsClopen R := by
    intro P hP R hR
    rcases hR with rfl | hRQ
    · exact hP'cl P hP
    · exact hQcl P hP R hRQ
  have hdisj_new : ∀ P ∈ B, (new P).PairwiseDisjoint id := by
    intro P hP
    refine Set.PairwiseDisjoint.insert (hQdisj P hP) ?_
    intro R hR _
    show Disjoint (P' P) R
    rw [Set.disjoint_left]
    intro x hx hxR
    exact (hQsub P hP R hR hxR).2 hx
  have hcov_new : ∀ P ∈ B, ⋃₀ new P = P := by
    intro P hP
    rw [hnew_def, Set.sUnion_insert, hQcov P hP]
    exact Set.union_diff_cancel (hP'sub P hP)
  have hcent_new : ∀ P ∈ B, ∀ R ∈ new P, IsCentered (F.restrict R).func := by
    intro P hP R hR
    rcases hR with rfl | hRQ
    · exact isCentered_of_equiv hlump.2.1 (hP'equiv P hP)
    · exact (hQprop P hP R hRQ).1
  obtain ⟨hA', hfiner, hsurv⟩ :=
    isCPartition_refine_at_family hA hBsub new hcount_new hsub_new hclopen_new hdisj_new
      hcov_new hcent_new
  refine ⟨(Part \ B) ∪ ⋃ P ∈ B, new P, hA', hfiner, ?_, hsurv, ?_, ?_⟩
  · -- `¬ IsLump g y`: clause 1, dispatched to `refiningBy1_reassemble_not_lump`.
    exact refiningBy1_reassemble_not_lump hA hlump hβ hU hyU hUreg
      hP'eqU hP'sub hP'cl hP'equiv hQsub hQprop hA'
  · -- New-lump-rank clause: dispatched to `refiningBy1_reassemble_new_lump_rank`.
    exact refiningBy1_reassemble_new_lump_rank hA hlump hβ hU hyU hUreg
      hP'eqU hP'sub hP'cl hP'equiv hQsub hQprop hA'
  · -- New-piece trichotomy: survived / rank `< β` (`Q`-parts) / `≡ g` with cocenter `y` (`P'`-parts).
    rintro R (hRl | hRr)
    · exact Or.inl hRl.1
    · obtain ⟨P, hPB, hRnew⟩ := Set.mem_iUnion₂.mp hRr
      rw [hnew_def] at hRnew
      rcases Set.mem_insert_iff.mp hRnew with rfl | hRQ
      · right; right
        have heq : P' P = P ∩ F.func ⁻¹' U := hP'eqU P hPB
        have hcent : IsCentered (F.restrict (P ∩ F.func ⁻¹' U)).func :=
          isCentered_of_equiv hlump.2.1 (heq ▸ hP'equiv P hPB)
        refine ⟨hP'equiv P hPB, ?_⟩
        rw [heq]
        exact ⟨hcent, refiningBy1_Ppart_cocenter hA hU hyU hPB hcent⟩
      · exact Or.inr (Or.inl (hQprop P hPB R hRQ).2)

/-- **Lemma `RefiningBy1`** (`6_double_successor_memo.tex:51-71`). Let `α < ω₁` and assume
`FG(<α)` (spelled out with the same shape as
`ScatFun.levels_finitely_generated`/`Induction.lean`, since `FG(<α)` is not itself a
reusable named hypothesis in this development). Let `F : ScatFun` with `CBRank F.func = α`
and `𝒫` a `c`-partition of `F`. If `(g, y)` is a `𝒫`-lump of rank `β ≤ α`, there is a finer
`c`-partition `𝒫'` such that:

1. `(g, y)` is no longer a `𝒫'`-lump;
2. every piece of `𝒫` outside the dissolved lump survives literally, `𝒫 \ 𝒫_{(g,y)} ⊆ 𝒫'`;
3. every new `𝒫'`-lump is either a `𝒫`-lump already, or has rank `< β`.

## Provided solution (`6_double_successor_memo.tex:57-71`)

Write `h := f_{(g,y)}`; `CB(h) = CB(g) = β` by `CBrankofclopenunion`
(`ScatFun.cbRank_eq_iSup_restrict`, after pulling an `ℕ`-enumeration out of the countable
sub-collection `𝒫_{(g,y)}`). Since `(g, y)` is a lump, some `w ∈ 𝒲_β` has `J_w = {j | w ≤
ray_j(h,y)}` finite and non-empty. Since `𝒲_β` is a genuine `Finset` (`omegaRegularSet`), and
each `w ∈ 𝒲_β` with `J_w` finite contributes a single bound, taking `J` to be the max of
those finitely many bounds gives a single `J` with `J_w ⊆ J` for every such `w` simultaneously
— a direct `Finset.sup`-style argument, no unpacking of the memoir's "finite" needed (unlike
an earlier draft of `omegaRegularSet`, which used the *set of all* centered functions of rank
`β` and so was not actually finite; fixed by using `ScatFun.Centered β` instead).

Given such a `J`, let `U = N_{y↾(J+1)}` (the clopen neighbourhood of `y` fixing its first
`J+1` coordinates); then `h` corestricted to `U` is `𝒲`-regular. For each lump piece `P ∈
blockPieces g y`, split `P` into `P ∩ F⁻¹(U)` (on which `F` still restricts to `g`, by
centeredness) and the complement, of strictly smaller `CB`-rank
(`CBrankofclopenunion`/`CenteredasPgluing`). Apply `FG(<α)` (via `FGconsequences`) to the
complement piece to get a `c`-partition of rank `< β`. Reassemble: keep every non-lump piece
of `𝒫`, replace each lump piece by its `U`-piece together with the new sub-partition of the
complement.

## Formalization notes / proof phases

* `FG(<α)` is `ScatFun.FGBelow α` (`ScatFun/LevelsFinitelyGenerated/FGBelow.lean`), the same
  shape as the induction hypothesis inside `ScatFun.levels_finitely_generated`
  (`WqoContinuousFunctions/ScatFun/LevelsFinitelyGenerated/Induction.lean`), since no
  reusable `FGconsequences`-style lemma exists yet.
* This is a substantial multi-step construction, broken into phases below and matched by
  named supporting lemmas just above (`exists_cPartition_of_centeredCylinderWitness`,
  `exists_cPartition_of_FGBelow`, `refiningBy1_piece_cbRank_eq`,
  `refiningBy1_exists_regularizing_nbhd`, `refiningBy1_split_piece`). Phases 1–3 are wired
  into the proof below (each still bottoming out in one of those scaffolded
  supporting lemmas, except Phase 1 which is fully proved); only **Phase 4** (reassembly) is
  a genuinely new open goal in this proof itself:
  1. **Done.** Unfold `¬ IsOmegaRegularAt h y` to get `w ∈ 𝒲_{CB(h)}` with `J_w`
     finite and non-empty, then `exists_common_finite_bound` to get a single `N` bounding
     every `w' ∈ 𝒲_{CB(h)}` with `J_{w'}` finite (not just `w` itself).
  2. `CB(h) = CB(g) = β` (`refiningBy1_piece_cbRank_eq`), then `U = N_{y↾(N+1)}` with `h`
     corestricted to `U` `𝒲`-regular (`refiningBy1_exists_regularizing_nbhd`).
  3. For each lump piece `P ∈ blockPieces g y`, split into a `≡ g` part and a rank-`< β`
     complement admitting a sub-partition, via `FG(<α)` (`refiningBy1_split_piece`).
  4. **Routed to `refiningBy1_reassemble`.** Reassemble `Part'` from the non-lump pieces of
     `Part`, the `P'`s, and the `Q`s (choosing one witness per lump piece via Phase 3) and
     check the four conclusion clauses; `refiningBy1`'s own body has no open goals, the sole
     remaining gap being the `refiningBy1_reassemble` construction. -/
theorem refiningBy1
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α)
    (Part : Set (Set ↑F.domain)) (hA : F.IsCPartition Part)
    (g : ScatFun) (y : Baire) (hlump : hA.IsLump g y)
    (β : Ordinal.{0}) (hβ : hA.lumpRank g = β) (hβα : β ≤ α) :
    ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'),
      IsFinerCPartition Part' Part ∧
      ¬ hA'.IsLump g y ∧
      Part \ hA.blockPieces g y ⊆ Part' ∧
      (∀ g' y', hA'.IsLump g' y' → hA.IsLump g' y' ∨ hA'.lumpRank g' < β) ∧
      (∀ R ∈ Part', R ∈ Part ∨ CBRank (F.restrict R).func < β ∨
        ((F.restrict R).Equiv g ∧ ∃ hc : IsCentered (F.restrict R).func,
          cocenter (F.restrict R).func hc = y)) := by
  -- **Phase 1** (done): extract the lump's witness `w` and a common bound `N`.
  set h : ScatFun := hA.piece g y with hh_def
  have hnotreg : ¬ IsOmegaRegularAt h y := hlump.2.2
  have hh_rank_lt : CBRank h.func < omega1 := CBRank_lt_omega1 h.hScat
  obtain ⟨w, hw_mem, hw_fin, hw_ne⟩ :
      ∃ w ∈ omegaRegularSet (CBRank h.func) hh_rank_lt,
        {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)}.Finite ∧
          {j : ℕ | ScatFun.Reduces w (h.rayOn y Set.univ j)}.Nonempty := by
    unfold IsOmegaRegularAt at hnotreg
    push_neg at hnotreg
    obtain ⟨w, hw_mem, hw1, hw2⟩ := hnotreg
    exact ⟨w, hw_mem, hw1, hw2⟩
  -- `N` bounds every `w' ∈ 𝒲_{CB(h)}` whose obstruction set `J_{w'}` is finite, not just `w`.
  obtain ⟨N, hN⟩ := exists_common_finite_bound (omegaRegularSet (CBRank h.func) hh_rank_lt)
    (fun w' => {j : ℕ | ScatFun.Reduces w' (h.rayOn y Set.univ j)})
  -- **Phase 2**: `CB(h) = β`, then a regularizing clopen neighbourhood `U` of `y` from `N`.
  have hh_rank_eq : CBRank h.func = β := refiningBy1_piece_cbRank_eq hA hlump hβ
  have hpres : ∀ V : Set Baire, IsClopen V → y ∈ V →
      CBRank (h.restrict (h.func ⁻¹' V)).func = CBRank h.func := by
    intro V hVcl hyV
    rw [hh_def]
    exact (piece_corestrict_cbRank_eq hA hlump hβ hVcl hyV).trans
      (refiningBy1_piece_cbRank_eq hA hlump hβ).symm
  obtain ⟨U, hU, hyU, hUreg⟩ := refiningBy1_exists_regularizing_nbhd h y N hpres hN
  -- **Phase 3**: every lump piece `P` splits over `U` into a `≡ g` part and a rank-`< β`
  -- complement admitting a sub-partition, via `FG(<α)`.
  -- The split witness is literally `P' = P ∩ F.func ⁻¹' U` (as in `refiningBy1_split_piece`),
  -- recorded explicitly here since `refiningBy1_reassemble` needs that identity for the
  -- `¬ IsLump g y` clause.
  have hsplit : ∀ P ∈ hA.blockPieces g y,
      ∃ P' : Set ↑F.domain, P' = P ∩ F.func ⁻¹' U ∧
        P' ⊆ P ∧ IsClopen P' ∧ ScatFun.Equiv (F.restrict P') g ∧
        ∃ Q : Set (Set ↑F.domain), Q.Countable ∧ (∀ R ∈ Q, R ⊆ P \ P') ∧
          (∀ R ∈ Q, IsClopen R) ∧ Q.PairwiseDisjoint id ∧ ⋃₀ Q = P \ P' ∧
          (∀ R ∈ Q, IsCentered (F.restrict R).func ∧ CBRank (F.restrict R).func < β) :=
    fun P hP => ⟨P ∩ F.func ⁻¹' U, rfl, Set.inter_subset_left,
      (hA.isClopen P hP.choose).inter (hU.preimage F.hCont),
      refiningBy1_Ppart_equiv hA hU hyU hP,
      refiningBy1_split_complement hFG hA hβα hβ hU hyU hP⟩
  -- **Phase 4**: reassemble `Part'` from the non-lump pieces of `Part`, the `P'`s, and the
  -- `Q`s, and check the four conclusion clauses — isolated in `refiningBy1_reassemble`.
  exact refiningBy1_reassemble α hα hFG F hFrank Part hA g y hlump β hβ hβα U hU hyU
    (hh_def ▸ hUreg) hsplit

/-!
## Gobbling up small functions (`6_double_successor_memo.tex:74-93`, Lemma
`gobblingLessThanLambda`)
-/

/-
**Lemma `gobblingLessThanLambda`** (`6_double_successor_memo.tex:79-93`). Let `λ < ω₁`
be limit and `F : ScatFun` be split as `F = F₀ ⊔ F₁` over a clopen `U ⊆ F.domain`
(`F₀ = F.restrict U`, `F₁ = F.restrict Uᶜ`), with `F₀` centered, `pgl ℓ_λ ≤ F₀`, and `F₁ ≤
ℓ_λ`. Then `F` is centered and `F ≡ F₀`.

## Provided solution (`6_double_successor_memo.tex:84-92`)

Let `x` be a center for `F₀` and `V ∋ x` clopen in `F₀.domain`; set `F_V = F.restrict V`.
Since `x` is a center for `F₀`, `F₀ ≤ F_V`, so `pgl ℓ_λ ≤ F_V` via some reduction `(σ, τ)`.
Comparing `F σ(0^ω)` with `F x` (equivalently, using the base point of the witnessing `τ`)
produces a clopen `W ∋ F x` disjoint from a clopen `V' ⊆ im F` with `ℓ_λ ≤ F_V ↾ V'`
(`Gluingasupperbound`/`Gluingaslowerbound`). By centeredness of `F₀`, `F₀ ≤ F_V ↾ W`, and
`F₁ ≤ ℓ_λ ≤ F_V ↾ V'`. Gluing these two reductions (`Gluingasupperbound`/
`Gluingaslowerbound`) gives `F ≤ F₀ ⊔ F₁ ≤ (F_V ↾ W) ⊔ (F_V ↾ V') ≤ F_V ≤ F₀`, and the reverse
reduction `F₀ ≤ F` is immediate from `F₀ = F.restrict U`. Centeredness of `F` then transfers
from `F₀` along `F ≡ F₀` (`Centerinvariance`, item 2).

## Formalization notes

The proof is self-contained (independent of the `c`-partition/lump machinery above) but
requires the base-point comparison and gluing/pointed-gluing upper- and lower-bound API
(`clopen_partition_to_gluing_reduces`, its lower-bound counterpart, and
`centerInvariance_equiv`). The assembly is now complete: `gobblingLessThanLambda` and its core
`gobblingLessThanLambda_reduces` are proved, bottoming out in the single open leaf
`exists_clopen_cocenter_avoid` (the one-tower-block cocenter-avoidance step).

The gluing core is isolated in `gobblingLessThanLambda_reduces` (the hard direction
`F ≤ F.restrict U`); the wrapper `gobblingLessThanLambda` adds the immediate reverse reduction
and transfers centeredness across the equivalence (`isCentered_of_equiv`).

**Domain split as `glBin`.** A clopen `U ⊆ F.domain` splits `F` over the clopen
partition `{U, Uᶜ}`: `F ≤ (F.restrict U) ⊕ (F.restrict Uᶜ)`.  Routine: paste the two
inclusion reductions on the clopen 2-piece domain partition (the converse of
`reduces_glBin_split`).
-/
lemma reduces_glBin_restrict_compl (F : ScatFun) (U : Set ↑F.domain) (hU : IsClopen U) :
    ScatFun.Reduces F (ScatFun.glBin (F.restrict U) (F.restrict Uᶜ)) := by
  -- Define the partition A where A n = if n = 0 then U else if n = 1 then Uᶜ else ∅.
  set A : ℕ → Set ↑F.domain := fun n => if n = 0 then U else if n = 1 then Uᶜ else ∅;
  -- Apply the lemma that states the gluing of the restrictions is equivalent to the gluing of the original function.
  have h_gl_eq : ScatFun.Reduces F (ScatFun.gl (fun i => F.restrict (A i))) := by
    apply scatFun_reduces_gl_of_domain_partition;
    refine ⟨ ?_, ?_, ?_ ⟩;
    · intro n; rcases n with ( _ | _ | n ) <;> simp +decide [ *, IsClopen ] ;
      · exact ⟨ hU.1, hU.2 ⟩;
      · exact ⟨ hU.isOpen.isClosed_compl, hU.isClosed.isOpen_compl ⟩;
      · aesop;
    · grind;
    · ext x; simp [A];
      exact ⟨ if x ∈ U then 0 else 1, by aesop ⟩;
  have h_gl_eq : ScatFun.Reduces (ScatFun.gl (fun i => F.restrict (A i))) (ScatFun.glList [F.restrict U, F.restrict Uᶜ]) := by
    apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ A ] ;
    · exact restrict_reduces_of_subset F fun ⦃a⦄ a_1 => a_1;
    · exact restrict_reduces_of_subset F fun ⦃a⦄ a_1 => a_1;
    · convert ScatFun.reduces_of_isEmpty_domain _;
      simp +decide [ ScatFun.restrict ];
  convert ‹F.Reduces ( ScatFun.gl fun i => F.restrict ( A i ) ) ›.trans h_gl_eq using 1

/-
**Reducing a centered function to a corestriction near its cocenter.** If `G` is centered
with cocenter `y = cocenter G`, then for every open neighbourhood `Wc ∋ y` we have
`G ≤ G.coRestrict Wc`.  The preimage `{w | G w ∈ Wc}` is an open neighbourhood of any center
(centers map to the cocenter, which lies in `Wc`), so the center property gives the reduction
(`reduces_coRestrict_of_subtype`).
-/
/-
**Block-`d` reduction of a constant tower into a corestriction.** Given the reduction data
`(σ, τ)` witnessing `pgl (fun _ => a) ≤ G` and a block-`d` embedding `σd` of `a` into the tower
whose `G`-values all land in `V`, `a` reduces into `G.coRestrict V`. The translator is
`stripZerosOne d ∘ τ`, since `pgl.func (σd z) = prependZerosOne d (a.func z) = τ (G.func (σ (σd z)))`
and `stripZerosOne d ∘ prependZerosOne d = id`.
-/
lemma pgl_const_block_reduces_coRestrict
    (a G : ScatFun) (d : ℕ)
    (σ : ↑(ScatFun.pgl (fun _ => a)).domain → ↑G.domain) (hσ : Continuous σ)
    (τ : Baire → Baire) (hτ : ContinuousOn τ (Set.range fun x => G.func (σ x)))
    (heq : ∀ x, (ScatFun.pgl (fun _ => a)).func x = τ (G.func (σ x)))
    (σd : ↑a.domain → ↑(ScatFun.pgl (fun _ => a)).domain) (hσd : Continuous σd)
    (hσdv : ∀ z, (ScatFun.pgl (fun _ => a)).func (σd z) = prependZerosOne d (a.func z))
    (V : Set Baire) (hVval : ∀ z, G.func (σ (σd z)) ∈ V) :
    ScatFun.Reduces a (G.coRestrict V) := by
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  use fun z => ⟨ σ ( σd z ), by
    exact ⟨ by
      exact σ ( σd z ) |>.2, hVval z ⟩ ⟩
  all_goals generalize_proofs at *;
  rotate_left;
  use fun x => stripZerosOne d ( τ x );
  · refine' ContinuousOn.comp ( _ : ContinuousOn ( fun x => stripZerosOne d x ) _ ) _ _;
    exact Set.univ;
    · exact Continuous.continuousOn ( continuous_stripZerosOne d );
    · refine hτ.mono ?_;
      rintro _ ⟨ z, rfl ⟩ ; exact ⟨ σd z, rfl ⟩ ;
    · exact fun x hx => Set.mem_univ _;
  · intro z
    simp only [ScatFun.coRestrict];
    grind [restrict_func_eq, stripZerosOne_prependZerosOne];
  · fun_prop

/-
**Deep blocks of a constant tower cluster at the base value.** If `V` is an open
neighbourhood of the base value `G.func (σ 0^ω)`, then some deep block `d` of the tower embeds
`a` with all its `G`-values inside `V`: the block-`d` cylinder `(0)^d(1)·` is contained in any
basic subspace-cylinder neighbourhood of the base `0^ω`, on which the continuous map
`G.func ∘ σ` stays inside `V`.
-/
lemma pgl_const_deep_block_values_in_nbhd
    (a G : ScatFun)
    (σ : ↑(ScatFun.pgl (fun _ => a)).domain → ↑G.domain) (hσ : Continuous σ)
    (hb : zeroStream ∈ (ScatFun.pgl (fun _ => a)).domain)
    (V : Set Baire) (hV : IsOpen V) (hVy : G.func (σ ⟨zeroStream, hb⟩) ∈ V) :
    ∃ (d : ℕ) (σd : ↑a.domain → ↑(ScatFun.pgl (fun _ => a)).domain),
      Continuous σd ∧
      (∀ z, (ScatFun.pgl (fun _ => a)).func (σd z) = prependZerosOne d (a.func z)) ∧
      (∀ z, G.func (σ (σd z)) ∈ V) := by
  have h_cylinder : ∃ m : ℕ, ∀ x : ↑(ScatFun.pgl (fun _ => a)).domain, (∀ i < m, x.val i = zeroStream i) → G.func (σ x) ∈ V := by
    have h_cylinder : IsOpen {x : ↑(ScatFun.pgl (fun _ => a)).domain | G.func (σ x) ∈ V} := by
      exact hV.preimage ( G.hCont.comp hσ );
    obtain ⟨ m, hm ⟩ := baire_subspace_cylinder_mem_nhds ⟨ zeroStream, hb ⟩ { x : ↑ ( ScatFun.pgl fun x => a ).domain | G.func ( σ x ) ∈ V } h_cylinder hVy;
    exact ⟨ m, fun x hx => hm fun i hi => hx i <| Finset.mem_range.mp hi ⟩;
  obtain ⟨ m, hm ⟩ := h_cylinder;
  refine ⟨ m, ?_, ?_, ?_, ?_ ⟩;
  use fun z => ⟨ prependZerosOne m z.val, by
    simp +decide only [ScatFun.pgl];
    unfold PointedGluingSet; simp +decide ;
    exact Or.inr ⟨ m, z, z.2, rfl ⟩ ⟩
  all_goals generalize_proofs at *;
  · refine Continuous.subtype_mk ?_ ?_;
    refine continuous_pi fun i => ?_;
    by_cases hi : i < m <;> simp +decide [ hi, prependZerosOne ];
    · exact continuous_const;
    · split_ifs <;> [ exact continuous_const; exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val ];
  · exact fun z => ScatFun.pgl_func_block (fun x => a) m z
  · intro z; specialize hm ⟨ prependZerosOne m z.val, by solve_by_elim ⟩ ; simp_all +decide [ prependZerosOne ] ;
    exact hm fun i hi => rfl

/-
**The base value is separated from the block-`0` value range.** With `(σ, τ)` witnessing
`pgl (fun _ => a) ≤ G` and `σ0` the block-`0` embedding, the base value `G.func (σ 0^ω)` is not
in the closure of the block-`0` `G`-values. Indeed `(τ ·) 0` is continuous on the value range,
equals `1` on every block-`0` value (`prependZerosOne 0 v` has `0`-th coordinate `1`), yet
equals `0` at the base value (whose `τ`-image is `0^ω`, since `pgl` fixes `0^ω`).
-/
lemma pgl_const_base_notMem_closure_block0
    (a G : ScatFun)
    (σ : ↑(ScatFun.pgl (fun _ => a)).domain → ↑G.domain)
    (τ : Baire → Baire) (hτ : ContinuousOn τ (Set.range fun x => G.func (σ x)))
    (heq : ∀ x, (ScatFun.pgl (fun _ => a)).func x = τ (G.func (σ x)))
    (hb : zeroStream ∈ (ScatFun.pgl (fun _ => a)).domain)
    (σ0 : ↑a.domain → ↑(ScatFun.pgl (fun _ => a)).domain)
    (hσ0v : ∀ z, (ScatFun.pgl (fun _ => a)).func (σ0 z) = prependZerosOne 0 (a.func z)) :
    G.func (σ ⟨zeroStream, hb⟩) ∉ closure (Set.range fun z => G.func (σ (σ0 z))) := by
  intro h;
  rw [ mem_closure_iff_seq_limit ] at h;
  obtain ⟨ x, hx₁, hx₂ ⟩ := h;
  -- Since $τ$ is continuous on the range of $G.func (σ ·)$, and $x_n$ converges to $G.func (σ ⟨zeroStream, hb⟩)$, we have $τ(x_n)$ converges to $τ(G.func (σ ⟨zeroStream, hb⟩))$.
  have hτ_conv : Filter.Tendsto (fun n => τ (x n)) Filter.atTop (nhds (τ (G.func (σ ⟨zeroStream, hb⟩)))) := by
    apply Filter.Tendsto.comp;
    apply_rules [ ContinuousOn.continuousAt ];
    · exact ⟨ _, rfl ⟩;
    · rw [ tendsto_nhdsWithin_iff ];
      exact ⟨ hx₂, Filter.Eventually.of_forall fun n => by obtain ⟨ z, hz ⟩ := hx₁ n; exact ⟨ σ0 z, hz ⟩ ⟩;
  -- Since $τ(x_n)$ converges to $τ(G.func (σ ⟨zeroStream, hb⟩))$, and $τ(x_n)$ is always $1$, we have $τ(G.func (σ ⟨zeroStream, hb⟩)) = 1$.
  have hτ_one : τ (G.func (σ ⟨zeroStream, hb⟩)) 0 = 1 := by
    have hτ_one : ∀ n, τ (x n) 0 = 1 := by
      intro n; specialize hx₁ n; obtain ⟨ z, hz ⟩ := hx₁; specialize heq ( σ0 z ) ; simp_all ;
      exact heq ▸ by simp +decide [ prependZerosOne ] ;
    exact tendsto_nhds_unique ( tendsto_pi_nhds.mp hτ_conv 0 ) ( tendsto_const_nhds.congr fun n => hτ_one n ▸ rfl );
  have := heq ⟨ zeroStream, hb ⟩;
  exact absurd hτ_one ( by rw [ ← this ] ; exact by rw [ ScatFun.pgl_func_zeroStream ] ; exact by simp +decide )

/-- **One tower block avoids a cocenter neighbourhood.** If the `ω`-tower `pgl (fun _ => a)`
reduces into a centered `G`, then some clopen neighbourhood `Wc` of `G`'s cocenter `y` is
avoided by a copy of `a`: `a` reduces into `G.coRestrict Wcᶜ`.  A single block of the tower
maps into `G` with values bounded away from `y` (blocks sit in cylinders disjoint from the
tower's base, whose image is `yb`), so a clopen `Wc ∋ y` disjoint from that block's value-range
works. Two cases on whether the cocenter `y` equals the base value `yb = G.func (σ 0^ω)`: if
`y ≠ yb`, a deep block clusters at `yb` inside a clopen `V ∋ yb` avoiding `y`
(`pgl_const_deep_block_values_in_nbhd`); if `y = yb`, block `0` stays off a clopen `V` avoiding
the base value (`pgl_const_base_notMem_closure_block0`). In both cases `Wc := Vᶜ` and
`pgl_const_block_reduces_coRestrict` gives `a ≤ G.coRestrict V = G.coRestrict Wcᶜ`. -/
lemma exists_clopen_cocenter_avoid (a G : ScatFun) (hc : IsCentered G.func)
    (hge : ScatFun.Reduces (ScatFun.pgl (fun _ => a)) G) :
    ∃ Wc : Set Baire, IsClopen Wc ∧ cocenter G.func hc ∈ Wc ∧
      ScatFun.Reduces a (G.coRestrict Wcᶜ) := by
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := hge
  have hb : zeroStream ∈ (ScatFun.pgl (fun _ => a)).domain :=
    zeroStream_mem_pointedGluingSet _
  obtain ⟨σ0, τ0, hσ0c, hτ0, hτ0eq, -, hσ0v⟩ := pgl_block_reduction_explicit (fun _ => a) 0
  set yb : Baire := G.func (σ ⟨zeroStream, hb⟩) with hyb
  set y : Baire := cocenter G.func hc with hy
  by_cases hyy : y = yb
  · -- `y = yb`: block `0` avoids a clopen neighbourhood of the base value.
    have hnc : yb ∉ closure (Set.range fun z => G.func (σ (σ0 z))) :=
      pgl_const_base_notMem_closure_block0 a G σ τ hτ heq hb σ0 hσ0v
    obtain ⟨Wc, hWccl, hyWc, hWcsub⟩ := baire_exists_clopen_subset_of_open y
      (closure (Set.range fun z => G.func (σ (σ0 z))))ᶜ
      (isClosed_closure.isOpen_compl) (hyy ▸ hnc)
    refine ⟨Wc, hWccl, hyWc, ?_⟩
    have hVval : ∀ z, G.func (σ (σ0 z)) ∈ (Wcᶜ : Set Baire) := by
      intro z
      have hz : G.func (σ (σ0 z)) ∈ closure (Set.range fun z => G.func (σ (σ0 z))) :=
        subset_closure (Set.mem_range_self z)
      intro hzWc
      exact (hWcsub hzWc) hz
    exact pgl_const_block_reduces_coRestrict a G 0 σ hσ τ hτ heq σ0 hσ0c hσ0v Wcᶜ hVval
  · -- `y ≠ yb`: a deep block clusters inside a clopen neighbourhood of `yb` avoiding `y`.
    obtain ⟨V, hVcl, hybV, hVsub⟩ := baire_exists_clopen_subset_of_open yb {s : Baire | s ≠ y}
      isOpen_ne (fun h => hyy h.symm)
    obtain ⟨d, σd, hσdc, hσdv, hVval⟩ :=
      pgl_const_deep_block_values_in_nbhd a G σ hσ hb V hVcl.isOpen hybV
    refine' ⟨Vᶜ, hVcl.compl, fun (hyVc : y ∈ V) => (hVsub hyVc) rfl, _⟩
    have : ScatFun.Reduces a (G.coRestrict V) :=
      pgl_const_block_reduces_coRestrict a G d σ hσ τ hτ heq σd hσdc hσdv V hVval
    simpa [compl_compl] using this

/-- **The absorption (gobbling) core.** If `F₀ = F.restrict U` is centered and contains an
`ω`-tower of `ℓ_λ`'s (`succMaxFun lam ≤ F₀`), then it absorbs any extra block `F₁ ≤ ℓ_λ`:
`F₀ ⊕ F₁ ≤ F₀`.  Codomain form of the memoir's argument
(`6_double_successor_memo.tex:84-92`): choose a clopen neighbourhood `Wc` of `F₀`'s cocenter
avoided by one tower copy of `ℓ_λ` (`exists_clopen_cocenter_avoid`); then `F₀ ≤ F₀↾Wc`
(`reduces_coRestrict_cocenter_nbhd`, centeredness) and `F₁ ≤ ℓ_λ ≤ F₀↾Wcᶜ`, so
`F₀ ⊕ F₁ ≤ (F₀↾Wc) ⊕ (F₀↾Wcᶜ) ≤ F₀` (`glBin_reduces_of_reduces`,
`glBin_coRestrict_compl_reduces`). -/
lemma glBin_centered_absorb
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (F : ScatFun) (U : Set ↑F.domain)
    (hF0cent : IsCentered (F.restrict U).func)
    (hF0ge : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.restrict U))
    (hF1le : ScatFun.Reduces (F.restrict Uᶜ) (ScatFun.maxFun lam hlam_lt)) :
    ScatFun.Reduces (ScatFun.glBin (F.restrict U) (F.restrict Uᶜ)) (F.restrict U) := by
  obtain ⟨Wc, hWccl, hcWc, hii⟩ :=
    exists_clopen_cocenter_avoid (ScatFun.maxFun lam hlam_lt) (F.restrict U) hF0cent hF0ge
  have hi : ScatFun.Reduces (F.restrict U) ((F.restrict U).coRestrict Wc) :=
    reduces_coRestrict_cocenter_nbhd (F.restrict U) hF0cent hWccl.isOpen hcWc
  have hF1 : ScatFun.Reduces (F.restrict Uᶜ) ((F.restrict U).coRestrict Wcᶜ) := hF1le.trans hii
  exact (ScatFun.glBin_reduces_of_reduces hi hF1).trans
    (ScatFun.glBin_coRestrict_compl_reduces (F.restrict U) Wc hWccl)

lemma gobblingLessThanLambda_reduces
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (_hlim : Order.IsSuccLimit lam)
    (F : ScatFun) (U : Set ↑F.domain) (hU : IsClopen U)
    (hF0cent : IsCentered (F.restrict U).func)
    (hF0ge : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.restrict U))
    (hF1le : ScatFun.Reduces (F.restrict Uᶜ) (ScatFun.maxFun lam hlam_lt)) :
    ScatFun.Reduces F (F.restrict U) :=
  (reduces_glBin_restrict_compl F U hU).trans
    (glBin_centered_absorb lam hlam_lt F U hF0cent hF0ge hF1le)

theorem gobblingLessThanLambda
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (hlim : Order.IsSuccLimit lam)
    (F : ScatFun) (U : Set ↑F.domain) (hU : IsClopen U)
    (hF0cent : IsCentered (F.restrict U).func)
    (hF0ge : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.restrict U))
    (hF1le : ScatFun.Reduces (F.restrict Uᶜ) (ScatFun.maxFun lam hlam_lt)) :
    IsCentered F.func ∧ ScatFun.Equiv F (F.restrict U) := by
  have hfwd : ScatFun.Reduces F (F.restrict U) :=
    gobblingLessThanLambda_reduces lam hlam_lt hlim F U hU hF0cent hF0ge hF1le
  have hrev : ScatFun.Reduces (F.restrict U) F :=
    ⟨fun x => ⟨x.val, x.property.choose⟩, by fun_prop, id, continuousOn_id, fun x => rfl⟩
  exact ⟨isCentered_of_equiv hF0cent ⟨hfwd, hrev⟩, hfwd, hrev⟩

/-!
## Fine `c`-partitions (`6_double_successor_memo.tex:95-124`)
-/

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- A `c`-partition `𝒫` of `F` is **fine relative to `λ`** (memoir Definition,
`6_double_successor_memo.tex:97-99`) if it has no lumps and every piece has `CB`-rank
`> λ`. -/
def IsFine (hA : F.IsCPartition Part) (lam : Ordinal.{0}) : Prop :=
  (∀ g y, ¬ hA.IsLump g y) ∧ ∀ P ∈ Part, lam < CBRank (F.restrict P).func

end ScatFun.IsCPartition

/-- **Limit inferior of a sequence of `c`-partitions** (memoir `⋃_k ⋂_{k ≤ j} 𝒫'_j`,
`6_double_successor_memo.tex:118`). A piece belongs to the liminf iff it is *eventually
always present*: `P ∈ 𝒫_j` for all sufficiently large `j`. -/
def cPartitionLiminf {F : ScatFun} (Parts : ℕ → Set (Set ↑F.domain)) : Set (Set ↑F.domain) :=
  {P | ∃ k : ℕ, ∀ j : ℕ, k ≤ j → P ∈ Parts j}

/-- **The liminf primitive.** The limit inferior of a sequence of `c`-partitions is again a
`c`-partition, *provided it still covers* `F.domain` (`hcov`). Everything except the covering
is pure bookkeeping: an eventually-present piece is a piece of some `𝒫_j`, hence clopen and
centered; two distinct liminf-pieces are both present in a common late `𝒫_j`, hence disjoint;
and the liminf is contained in `⋃_j 𝒫_j`, hence countable.

The covering hypothesis is the single genuinely hard content of the memoir's liminf
construction: for each point `x`, the (decreasing, clopen) sequence of pieces containing `x`
must *stabilise*, so that its eventual value is a liminf-piece covering `x`. In the intended
application (`existenceFinePartitions_dissolveAll`) stabilisation follows from
well-foundedness of `CB`-rank together with `refiningBy1`'s piece-survival clause. Kept as an
explicit hypothesis here so the primitive is reusable and its bookkeeping is not entangled
with the stabilisation argument. -/
theorem isCPartition_cPartitionLiminf {F : ScatFun} (Parts : ℕ → Set (Set ↑F.domain))
    (hpart : ∀ j, F.IsCPartition (Parts j))
    (hcov : ∀ x : ↑F.domain, ∃ P ∈ cPartitionLiminf Parts, x ∈ P) :
    F.IsCPartition (cPartitionLiminf Parts) := by
  -- Each liminf-piece is a piece of some `Parts k`.
  have hmem : ∀ P ∈ cPartitionLiminf Parts, ∃ k, P ∈ Parts k := by
    rintro P ⟨k, hk⟩; exact ⟨k, hk k le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Countable: contained in `⋃_j 𝒫 j`.
    refine (Set.countable_iUnion (fun j => (hpart j).countable)).mono ?_
    rintro P hP
    obtain ⟨k, hk⟩ := hmem P hP
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · -- Clopen.
    intro P hP
    obtain ⟨k, hk⟩ := hmem P hP
    exact (hpart k).isClopen P hk
  · -- Pairwise disjoint: present together in `𝒫 (max k k')`.
    rintro P ⟨k, hk⟩ P' ⟨k', hk'⟩ hPP'
    exact (hpart (max k k')).pairwiseDisjoint (hk _ (le_max_left k k'))
      (hk' _ (le_max_right k k')) hPP'
  · -- Cover: exactly `hcov`.
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨P, hP, hxP⟩ := hcov x
    exact ⟨P, hP, hxP⟩
  · -- Centered.
    intro P hP
    obtain ⟨k, hk⟩ := hmem P hP
    exact (hpart k).centered P hk

/-- **Lump ranks are bounded by `CB(F)`.** For any `𝒫`-lump `(g, y)`, its rank `CB(g)`
equals `CB(f_{(g,y)})` (`refiningBy1_piece_cbRank_eq`), and `f_{(g,y)} = F.restrict (⋃₀ 𝒫_{(g,y)})`
is a restriction of `F` to an open set, so its `CB`-rank is `≤ CB(F)`
(`CBRank_open_restrict_le`). -/
lemma lumpRank_le_cbRank {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {g : ScatFun} {y : Baire} (hlump : hA.IsLump g y) :
    hA.lumpRank g ≤ CBRank F.func := by
  have h1 : CBRank (hA.piece g y).func = hA.lumpRank g :=
    refiningBy1_piece_cbRank_eq hA hlump rfl
  rw [← h1]
  show CBRank (F.restrict (⋃₀ hA.blockPieces g y)).func ≤ CBRank F.func
  rw [cbRank_restrict_eq]
  refine CBRank_open_restrict_le F.func F.hScat _ ?_
  refine isOpen_sUnion (fun P hP => (hA.isClopen P hP.choose).isOpen)

/-- **Lump status is invariant under `Equiv` of the representative.** Since `blockPieces g y`
only depends on `g` up to `ScatFun.Equiv`, so does `piece g y`, `IsCentered g`, and hence
`IsLump g y`. -/
lemma IsLump_congr_equiv {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {g g' : ScatFun} {y : Baire} (h : g.Equiv g') :
    hA.IsLump g y ↔ hA.IsLump g' y := by
  have hblock : hA.blockPieces g y = hA.blockPieces g' y := by
    ext P
    exact ⟨fun ⟨hP, he, hc⟩ => ⟨hP, he.trans h, hc⟩, fun ⟨hP, he, hc⟩ => ⟨hP, he.trans h.symm, hc⟩⟩
  have hpiece : hA.piece g y = hA.piece g' y := by
    unfold ScatFun.IsCPartition.piece; rw [hblock]
  unfold ScatFun.IsCPartition.IsLump
  rw [hpiece]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, isCentered_of_equiv h2 h.symm, h3⟩,
         fun ⟨h1, h2, h3⟩ => ⟨h1, isCentered_of_equiv h2 h, h3⟩⟩

/-- `lumpRank` only depends on the representative up to `ScatFun.Equiv`. -/
lemma lumpRank_congr_equiv {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {g g' : ScatFun} (h : g.Equiv g') :
    hA.lumpRank g = hA.lumpRank g' :=
  cbRank_eq_of_equiv h

/-- **One dissolving step.** If `(g,y) = gy` is a rank-`γ` lump of the current `c`-partition
`QQ`, replace `QQ` by a `refiningBy1` refinement dissolving it; otherwise keep `QQ`. Packaged
as an operation on the subtype of `c`-partitions of `F`. -/
noncomputable def dissolveStep
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α) (γ : Ordinal.{0}) (hγα : γ ≤ α)
    (gy : ScatFun × Baire)
    (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    {Q : Set (Set ↑F.domain) // F.IsCPartition Q} :=
  if h : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ then
    ⟨(refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose,
     (refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose_spec.choose⟩
  else QQ

section DissolveSeq
variable (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α) (γ : Ordinal.{0}) (hγα : γ ≤ α)

/-- Every `dissolveStep`-lump was already a lump before the step, or has rank `< γ`
(`refiningBy1` clause 5). -/
lemma dissolveStep_isLump_mono (gy : ScatFun × Baire)
    (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    ∀ g' y', (dissolveStep α hα hFG F hFrank γ hγα gy QQ).2.IsLump g' y' →
      QQ.2.IsLump g' y' ∨ (dissolveStep α hα hFG F hFrank γ hγα gy QQ).2.lumpRank g' < γ := by
  by_cases h : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ
  · intro g' y' hl
    rw [dissolveStep, dif_pos h] at hl ⊢
    exact (refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose_spec.choose_spec.2.2.2.1
      g' y' hl
  · intro g' y' hl; rw [dissolveStep, dif_neg h] at hl; exact Or.inl hl

/-- **New-piece trichotomy for a step.** Any piece of the post-step partition either survived
from before the step, has rank `< γ`, or is `≡ gy.1` with cocenter `gy.2` (`refiningBy1`'s
new-piece clause; in the non-firing branch every piece survived trivially). -/
lemma dissolveStep_newpiece (gy : ScatFun × Baire)
    (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    ∀ R ∈ (dissolveStep α hα hFG F hFrank γ hγα gy QQ).1,
      R ∈ QQ.1 ∨ CBRank (F.restrict R).func < γ ∨
        ((F.restrict R).Equiv gy.1 ∧ ∃ hc : IsCentered (F.restrict R).func,
          cocenter (F.restrict R).func hc = gy.2) := by
  by_cases h : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ
  · intro R hR
    rw [dissolveStep, dif_pos h] at hR
    exact (refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose_spec.choose_spec.2.2.2.2
      R hR
  · intro R hR; rw [dissolveStep, dif_neg h] at hR; exact Or.inl hR

/-- If the step fires (`gy` is a rank-`γ` lump), then afterwards `gy` is no longer a lump
(`refiningBy1` clause 1). -/
lemma dissolveStep_dissolved (gy : ScatFun × Baire)
    (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (h : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ) :
    ¬ (dissolveStep α hα hFG F hFrank γ hγα gy QQ).2.IsLump gy.1 gy.2 := by
  rw [dissolveStep, dif_pos h]
  exact (refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose_spec.choose_spec.2.1

/-- **The dissolving sequence** (recursion): `Parts 0 = QQ0`, and
`Parts (k+1) = dissolveStep (enum k) (Parts k)`. -/
noncomputable def dissolveSeqAux
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    ℕ → {Q : Set (Set ↑F.domain) // F.IsCPartition Q}
  | 0 => QQ0
  | (k+1) => dissolveStep α hα hFG F hFrank γ hγα (enum k)
      (dissolveSeqAux enum QQ0 k)

/-- **Invariant: all lumps stay of rank `≤ γ`.** By induction using
`dissolveStep_isLump_mono` and the base bound on `QQ0`. -/
lemma dissolveSeqAux_isLump_le
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (h0 : ∀ g y, QQ0.2.IsLump g y → QQ0.2.lumpRank g ≤ γ) :
    ∀ k g y, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.IsLump g y →
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.lumpRank g ≤ γ := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro g y hl
    rcases dissolveStep_isLump_mono α hα hFG F hFrank γ hγα (enum k)
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k) g y hl with h1 | h2
    · exact ih g y h1
    · exact h2.le

/-- **Invariant: rank-`γ` lumps trace back to `QQ0`.** A rank-`γ` lump of `Parts k` was already
a `QQ0`-lump (it cannot have been created by a step, since new lumps have rank `< γ`). -/
lemma dissolveSeqAux_isLump_orig
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    ∀ k g y, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.IsLump g y →
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.lumpRank g = γ →
      QQ0.2.IsLump g y := by
  intro k
  induction k with
  | zero => intro g y hl _; exact hl
  | succ k ih =>
    intro g y hl hrank
    rcases dissolveStep_isLump_mono α hα hFG F hFrank γ hγα (enum k)
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k) g y hl with h1 | h2
    · exact ih g y h1 hrank
    · exact absurd hrank (by rw [hrank] at h2; exact absurd h2 (lt_irrefl γ))

/-- **Non-lump-ness of a rank-`γ` lump is preserved by a step.** From `dissolveStep_isLump_mono`
(a fresh lump would have rank `< γ`). -/
lemma dissolveSeqAux_nonlump_step
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    {g : ScatFun} {y : Baire} (hrank : ∀ k, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.lumpRank g = γ)
    {k : ℕ} (hk : ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.IsLump g y) :
    ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 (k+1)).2.IsLump g y := by
  intro hl
  rcases dissolveStep_isLump_mono α hα hFG F hFrank γ hγα (enum k)
    (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k) g y hl with h1 | h2
  · exact hk h1
  · exact absurd (hrank (k+1)) (ne_of_lt h2)

/-- Once a rank-`γ` lump `(g,y)` is gone at some stage `N`, it stays gone. -/
lemma nonlump_persist
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    {g : ScatFun} {y : Baire}
    (hrank : ∀ k, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.lumpRank g = γ)
    {N : ℕ} (hK : ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 N).2.IsLump g y) :
    ∀ j : ℕ, N ≤ j → ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.IsLump g y := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hK
  | succ m hm ih => exact dissolveSeqAux_nonlump_step α hα hFG F hFrank γ hγα enum QQ0 hrank ih

/-- **Every rank-`γ` `QQ0`-lump is eventually dissolved.** Its enumeration index `k` (from
`henum`) either already witnesses `(g,y)` as a non-lump of `Parts k`, or the step at `k` fires
and dissolves it (`dissolveStep_dissolved`); either way it stays a non-lump forever
(`nonlump_persist`). Uses `IsLump_congr_equiv` to pass between `g` and the enumerated
representative `(enum k).1 ≡ g`. -/
lemma dissolveSeqAux_dissolved
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (henum : ∀ g y, QQ0.2.IsLump g y → QQ0.2.lumpRank g = γ →
      ∃ k : ℕ, (enum k).2 = y ∧ (enum k).1.Equiv g)
    {g : ScatFun} {y : Baire} (hg : QQ0.2.IsLump g y) (hgr : QQ0.2.lumpRank g = γ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.IsLump g y := by
  obtain ⟨k, hky, hkg⟩ := henum g y hg hgr
  set gk := (enum k).1 with hgk
  have hrank : ∀ j, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.lumpRank g = γ :=
    fun j => hgr
  have hrankgk : ∀ j, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.lumpRank gk = γ := by
    intro j; rw [lumpRank_congr_equiv _ hkg]; exact hrank j
  set Q := dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 with hQ
  by_cases hcase : (Q k).2.IsLump g y
  · have hlumpgk : (Q k).2.IsLump gk y := (IsLump_congr_equiv (Q k).2 hkg).mpr hcase
    have hguard : (Q k).2.IsLump (enum k).1 (enum k).2 ∧ (Q k).2.lumpRank (enum k).1 = γ := by
      rw [hky]; exact ⟨hlumpgk, hrankgk k⟩
    have hdis : ¬ (Q (k+1)).2.IsLump (enum k).1 (enum k).2 :=
      dissolveStep_dissolved α hα hFG F hFrank γ hγα (enum k) (Q k) hguard
    rw [hky] at hdis
    have hnl : ¬ (Q (k+1)).2.IsLump g y :=
      fun h => hdis ((IsLump_congr_equiv (Q (k+1)).2 hkg).mpr h)
    exact ⟨k+1, nonlump_persist α hα hFG F hFrank γ hγα enum QQ0 hrank hnl⟩
  · exact ⟨k, nonlump_persist α hα hFG F hFrank γ hγα enum QQ0 hrank hcase⟩

/-- A `dissolveStep` never removes a piece outside the dissolved block (`refiningBy1`'s
survival clause; identity in the non-firing branch). -/
lemma dissolveStep_survival (gy : ScatFun × Baire)
    (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    QQ.1 \ QQ.2.blockPieces gy.1 gy.2 ⊆ (dissolveStep α hα hFG F hFrank γ hγα gy QQ).1 := by
  by_cases h : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ
  · rw [dissolveStep, dif_pos h]
    exact (refiningBy1 α hα hFG F hFrank QQ.1 QQ.2 gy.1 gy.2 h.1 γ h.2 hγα).choose_spec.choose_spec.2.2.1
  · rw [dissolveStep, dif_neg h]; exact Set.diff_subset

/-- Every piece of a `(g,y)`-block has `CB`-rank equal to the lump rank of `g`. -/
lemma blockPiece_rank {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {g : ScatFun} {y : Baire} {P : Set ↑F.domain} (hP : P ∈ hA.blockPieces g y) :
    CBRank (F.restrict P).func = hA.lumpRank g := by
  obtain ⟨hmem, heq, hcoc⟩ := hP
  rw [cbRank_eq_of_equiv heq]; rfl

/-- **Low-rank pieces persist.** A piece of rank `< γ` is never split (splitting needs rank
`γ`), so it survives every later stage. -/
lemma lowrank_persists
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    {P : Set ↑F.domain} {k : ℕ}
    (hPk : P ∈ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1)
    (hrank : CBRank (F.restrict P).func < γ) :
    ∀ j : ℕ, k ≤ j → P ∈ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).1 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hPk
  | succ m hm ih =>
    by_cases hg : (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2.IsLump (enum m).1 (enum m).2 ∧
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2.lumpRank (enum m).1 = γ
    · show P ∈ (dissolveStep α hα hFG F hFrank γ hγα (enum m)
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m)).1
      apply dissolveStep_survival α hα hFG F hFrank γ hγα
      refine ⟨ih, fun hPblock => ?_⟩
      have hr := blockPiece_rank F (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2 hPblock
      rw [hg.2] at hr
      exact absurd hr (ne_of_lt hrank)
    · show P ∈ (dissolveStep α hα hFG F hFrank γ hγα (enum m)
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m)).1
      rw [dissolveStep, dif_neg hg]; exact ih

/-- **Pieces of an eventually-non-lump class persist.** A piece `≡ g'` with cocenter `y'`
where `(g',y')` is a non-lump at every later stage is never split, so it survives. -/
lemma stable_piece_persists
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    {P : Set ↑F.domain} {g' : ScatFun} {y' : Baire} {k : ℕ}
    (hPk : P ∈ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1)
    (heq : (F.restrict P).Equiv g')
    (hcoc : ∃ hc : IsCentered (F.restrict P).func, cocenter (F.restrict P).func hc = y')
    (hnl : ∀ j : ℕ, k ≤ j → ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.IsLump g' y') :
    ∀ j : ℕ, k ≤ j → P ∈ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).1 := by
  obtain ⟨hc, hcy⟩ := hcoc
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hPk
  | succ m hm ih =>
    by_cases hg : (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2.IsLump (enum m).1 (enum m).2 ∧
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2.lumpRank (enum m).1 = γ
    · show P ∈ (dissolveStep α hα hFG F hFrank γ hγα (enum m)
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m)).1
      apply dissolveStep_survival α hα hFG F hFrank γ hγα
      refine ⟨ih, fun hPblock => ?_⟩
      obtain ⟨hmem, hPeqm, hPcocm⟩ := hPblock
      have hgg : (enum m).1.Equiv g' := hPeqm.symm.trans heq
      have hym : (enum m).2 = y' := by rw [← hPcocm]; exact hcy
      have hlump : (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m).2.IsLump g' y' := by
        rw [← hym]; exact (IsLump_congr_equiv _ hgg).mp hg.1
      exact hnl m hm hlump
    · show P ∈ (dissolveStep α hα hFG F hFrank γ hγα (enum m)
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 m)).1
      rw [dissolveStep, dif_neg hg]; exact ih

/-- **Coverage / stabilisation.** Every point of `F.domain` lies in some piece of the limit
inferior of the dissolving sequence. This holds because each point's (decreasing, clopen)
sequence of pieces changes at most once: a piece is only split when the rank-`γ` lump it
belongs to is dissolved, after which the point lands in a piece that is either of rank `< γ`
(never split, since splitting needs rank `γ`) or `≡ g` with the same cocenter (never split
again, since that lump is now dissolved forever, `nonlump_persist`). -/
lemma dissolveSeq_cover
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q}) :
    ∀ x : ↑F.domain, ∃ P ∈ cPartitionLiminf
      (fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1), x ∈ P := by
  intro x
  set Parts : ℕ → Set (Set ↑F.domain) :=
    fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1 with hParts
  have hex : ∀ k, ∃ P, P ∈ Parts k ∧ x ∈ P := by
    intro k
    have hu : x ∈ ⋃₀ Parts k := by
      rw [(dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.sUnion_eq]; trivial
    exact hu
  choose piece hpmem hpx using hex
  have huniq : ∀ k Q, Q ∈ Parts k → x ∈ Q → Q = piece k := by
    intro k Q hQmem hxQ
    by_contra hne
    exact Set.disjoint_left.mp
      ((dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.pairwiseDisjoint hQmem (hpmem k) hne)
      hxQ (hpx k)
  by_cases hchg : ∃ k, piece (k+1) ≠ piece k
  · obtain ⟨k, hk⟩ := hchg
    have hnotmem : piece (k+1) ∉ Parts k := by
      intro hmem; exact hk (huniq k (piece (k+1)) hmem (hpx (k+1)))
    have hguard : (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.IsLump (enum k).1 (enum k).2 ∧
        (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2.lumpRank (enum k).1 = γ := by
      by_contra hg
      apply hnotmem
      show piece (k+1) ∈ Parts k
      have hpe : Parts (k+1) = Parts k := by
        show (dissolveStep α hα hFG F hFrank γ hγα (enum k)
          (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k)).1 = _
        rw [dissolveStep, dif_neg hg]
      rw [← hpe]; exact hpmem (k+1)
    have htri := dissolveStep_newpiece α hα hFG F hFrank γ hγα (enum k)
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k) (piece (k+1)) (hpmem (k+1))
    rcases htri with hmem | hlow | hclass
    · exact absurd hmem hnotmem
    · exact ⟨piece (k+1), ⟨k+1, fun j hj => lowrank_persists α hα hFG F hFrank γ hγα enum QQ0
        (hpmem (k+1)) hlow j hj⟩, hpx (k+1)⟩
    · have hrank : ∀ j, (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.lumpRank (enum k).1 = γ :=
        fun j => hguard.2
      have hdis : ¬ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 (k+1)).2.IsLump (enum k).1 (enum k).2 :=
        dissolveStep_dissolved α hα hFG F hFrank γ hγα (enum k)
          (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k) hguard
      have hnl := nonlump_persist α hα hFG F hFrank γ hγα enum QQ0 hrank hdis
      exact ⟨piece (k+1), ⟨k+1, fun j hj => stable_piece_persists α hα hFG F hFrank γ hγα enum QQ0
        (hpmem (k+1)) hclass.1 hclass.2 hnl j hj⟩, hpx (k+1)⟩
  · push_neg at hchg
    have hconst : ∀ k, piece k = piece 0 := by
      intro k; induction k with
      | zero => rfl
      | succ m ih => rw [hchg m, ih]
    exact ⟨piece 0, ⟨0, fun j _ => by rw [← hconst j]; exact hpmem j⟩, hpx 0⟩

/-- **Block-union stabilisation for high-rank classes.** For any `(g,y)` with
`γ ≤ CB(g)`, the union of the `(g,y)`-block eventually equals its liminf value. The block
only changes when the `(g,y)`-lump itself is dissolved (a single step, after which it is a
non-lump forever); dissolving any other lump neither removes a `(g,y)`-block piece (different
block) nor creates one (new pieces are either rank `< γ ≤ CB(g)` so `≢ g`, or `≡` the other,
different representative). Hence the union is eventually constant, and by coverage
(`dissolveSeq_cover`) its eventual value is the liminf-block union. -/
lemma dissolveStep_blockUnion_stable {g : ScatFun} {y : Baire} (hgrank : γ ≤ CBRank g.func)
    (gy : ScatFun × Baire) (QQ : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (hnf : ¬(QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ ∧ gy.1.Equiv g ∧ gy.2 = y)) :
    ⋃₀ (dissolveStep α hα hFG F hFrank γ hγα gy QQ).2.blockPieces g y
      = ⋃₀ QQ.2.blockPieces g y := by
  by_cases hguard : QQ.2.IsLump gy.1 gy.2 ∧ QQ.2.lumpRank gy.1 = γ
  · have hclass : ¬(gy.1.Equiv g ∧ gy.2 = y) := fun h => hnf ⟨hguard.1, hguard.2, h.1, h.2⟩
    apply Set.Subset.antisymm
    · rintro z ⟨Q, hQblock, hzQ⟩
      obtain ⟨hQmem, hQeq, hQcoc⟩ := hQblock
      rcases dissolveStep_newpiece α hα hFG F hFrank γ hγα gy QQ Q hQmem with hin | hlow | hcl
      · exact ⟨Q, ⟨hin, hQeq, hQcoc⟩, hzQ⟩
      · exact absurd (cbRank_eq_of_equiv hQeq ▸ hlow) (not_lt.mpr hgrank)
      · exfalso
        obtain ⟨hcl1, hc, hccoc⟩ := hcl
        exact hclass ⟨hcl1.symm.trans hQeq, by rw [← hccoc]; exact hQcoc⟩
    · rintro z ⟨Q, hQblock, hzQ⟩
      obtain ⟨hQmem, hQeq, hQcoc⟩ := hQblock
      have hQnotblock : Q ∉ QQ.2.blockPieces gy.1 gy.2 := by
        rintro ⟨hm, heqgy, hcocgy⟩
        exact hclass ⟨heqgy.symm.trans hQeq, by rw [← hcocgy]; exact hQcoc⟩
      exact ⟨Q, ⟨dissolveStep_survival α hα hFG F hFrank γ hγα gy QQ ⟨hQmem, hQnotblock⟩,
        hQeq, hQcoc⟩, hzQ⟩
  · rw [dissolveStep, dif_neg hguard]

lemma blockUnion_eventually_eq
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (hL : F.IsCPartition (cPartitionLiminf
      (fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1)))
    (g : ScatFun) (y : Baire) (hgrank : γ ≤ CBRank g.func) :
    ∃ K : ℕ, ∀ j : ℕ, K ≤ j →
      ⋃₀ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.blockPieces g y
        = ⋃₀ hL.blockPieces g y := by
  set Parts : ℕ → {Q : Set (Set ↑F.domain) // F.IsCPartition Q} :=
    fun k => dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k with hPd
  set S : ℕ → Set ↑F.domain := fun j => ⋃₀ (Parts j).2.blockPieces g y with hSd
  have hchange_fire : ∀ j : ℕ, S (j+1) ≠ S j →
      (Parts j).2.IsLump (enum j).1 (enum j).2 ∧ (Parts j).2.lumpRank (enum j).1 = γ ∧
        (enum j).1.Equiv g ∧ (enum j).2 = y := by
    intro j hjne
    by_contra hnf
    exact hjne (dissolveStep_blockUnion_stable α hα hFG F hFrank γ hγα hgrank (enum j) (Parts j) hnf)
  have hfire_lump : ∀ j : ℕ, S (j+1) ≠ S j → (Parts j).2.IsLump g y := by
    intro j hjne
    obtain ⟨hgd, hrk, heqg, heqy⟩ := hchange_fire j hjne
    rw [← heqy]; exact (IsLump_congr_equiv (Parts j).2 heqg).mp hgd
  have hfire_dissolve : ∀ j : ℕ, S (j+1) ≠ S j → ∀ j' : ℕ, j+1 ≤ j' → ¬ (Parts j').2.IsLump g y := by
    intro j hjne
    obtain ⟨hgd, hrk, heqg, heqy⟩ := hchange_fire j hjne
    have hdis : ¬ (Parts (j+1)).2.IsLump (enum j).1 (enum j).2 :=
      dissolveStep_dissolved α hα hFG F hFrank γ hγα (enum j) (Parts j) ⟨hgd, hrk⟩
    have hnl0 : ¬ (Parts (j+1)).2.IsLump g y := by
      intro h
      exact hdis (heqy ▸ (IsLump_congr_equiv (Parts (j+1)).2 heqg).mpr h)
    have hCB : (Parts j).2.lumpRank g = γ := (lumpRank_congr_equiv (Parts j).2 heqg).symm.trans hrk
    exact nonlump_persist α hα hFG F hFrank γ hγα enum QQ0 (fun k => hCB) hnl0
  obtain ⟨K, hKconst⟩ : ∃ K : ℕ, ∀ j : ℕ, K ≤ j → S j = S K := by
    by_cases hex : ∃ j : ℕ, S (j+1) ≠ S j
    · obtain ⟨j0, hj0⟩ := hex
      refine ⟨j0+1, ?_⟩
      have hnochange : ∀ j : ℕ, j0+1 ≤ j → S (j+1) = S j := by
        intro j hj
        by_contra hjne
        exact hfire_dissolve j0 hj0 j hj (hfire_lump j hjne)
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ m hm ih => rw [hnochange m hm, ih]
    · push_neg at hex
      have hall : ∀ j : ℕ, S j = S 0 := by
        intro j; induction j with
        | zero => rfl
        | succ m ih => rw [hex m, ih]
      exact ⟨0, fun j _ => hall j⟩
  refine ⟨K, fun j hj => ?_⟩
  have hjeq : S j = S K := hKconst j hj
  show S j = ⋃₀ hL.blockPieces g y
  rw [hjeq]
  apply Set.Subset.antisymm
  · rintro z ⟨Q, hQblock, hzQ⟩
    obtain ⟨hQmem, hQeq, hQcoc⟩ := hQblock
    obtain ⟨P, hPlim, hzP⟩ := dissolveSeq_cover α hα hFG F hFrank γ hγα enum QQ0 z
    obtain ⟨k, hk⟩ := hPlim
    have hiK : K ≤ max k K := le_max_right _ _
    have hik : k ≤ max k K := le_max_left _ _
    have hzSi : z ∈ S (max k K) := by rw [hKconst _ hiK]; exact ⟨Q, ⟨hQmem, hQeq, hQcoc⟩, hzQ⟩
    obtain ⟨Q', hQ'block, hzQ'⟩ := hzSi
    obtain ⟨hQ'mem, hQ'eq, hQ'coc⟩ := hQ'block
    have hPi : P ∈ (Parts (max k K)).1 := hk _ hik
    have hQ'P : Q' = P := by
      by_contra hne
      exact Set.disjoint_left.mp ((Parts (max k K)).2.pairwiseDisjoint hQ'mem hPi hne) hzQ' hzP
    subst hQ'P
    exact ⟨Q', ⟨⟨k, hk⟩, hQ'eq, hQ'coc⟩, hzQ'⟩
  · rintro z ⟨P, hPblock, hzP⟩
    obtain ⟨hPlim, hPeq, hPcoc⟩ := hPblock
    obtain ⟨k, hk⟩ := hPlim
    have hiK : K ≤ max k K := le_max_right _ _
    have hik : k ≤ max k K := le_max_left _ _
    have hPi : P ∈ (Parts (max k K)).1 := hk _ hik
    have hz : z ∈ S (max k K) := ⟨P, ⟨hPi, hPeq, hPcoc⟩, hzP⟩
    rwa [hKconst _ hiK] at hz

/-- **The limit inferior has only lumps of rank `< γ`.** If `(g,y)` were a liminf-lump of rank
`≥ γ`, then (block stabilisation `blockUnion_eventually_eq`) for large `j` the liminf
`(g,y)`-block union equals the `Parts j`-block union, so `(g,y)` is a `Parts j`-lump for
large `j`, hence (by `dissolveSeqAux_isLump_le`/`dissolveSeqAux_isLump_orig`) a rank-`γ`
`QQ0`-lump, which is eventually dissolved (`dissolveSeqAux_dissolved`) — a contradiction. -/
lemma dissolveSeq_lump
    (enum : ℕ → ScatFun × Baire) (QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q})
    (henum : ∀ g y, QQ0.2.IsLump g y → QQ0.2.lumpRank g = γ →
      ∃ k : ℕ, (enum k).2 = y ∧ (enum k).1.Equiv g)
    (h0 : ∀ g y, QQ0.2.IsLump g y → QQ0.2.lumpRank g ≤ γ)
    (hL : F.IsCPartition (cPartitionLiminf
      (fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1))) :
    ∀ g y, hL.IsLump g y → hL.lumpRank g < γ := by
  intro g y hgy
  by_contra hge
  push_neg at hge
  have hgrank : γ ≤ CBRank g.func := hge
  obtain ⟨K, hK⟩ := blockUnion_eventually_eq α hα hFG F hFrank γ hγα enum QQ0 hL g y hgrank
  have hpiece : ∀ j, K ≤ j →
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.piece g y = hL.piece g y := by
    intro j hj
    show F.restrict (⋃₀ (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.blockPieces g y)
      = F.restrict (⋃₀ hL.blockPieces g y)
    rw [hK j hj]
  have htrans : ∀ j, K ≤ j →
      (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 j).2.IsLump g y := by
    intro j hj
    refine ⟨?_, hgy.2.1, ?_⟩
    · obtain ⟨P, hP⟩ := refiningBy1_blockPieces_nonempty hL hgy
      obtain ⟨hPmem, hPeq, hPcoc⟩ := hP
      set c := F.restrictEquiv P (hL.centered P hPmem).choose with hc
      have hz : (c.1 : ↑F.domain) ∈ ⋃₀ hL.blockPieces g y := ⟨P, ⟨hPmem, hPeq, hPcoc⟩, c.2⟩
      rw [← hK j hj] at hz
      obtain ⟨Q, hQblock, hzQ⟩ := hz
      obtain ⟨hQmem, hQeq, hQcoc⟩ := hQblock
      exact ⟨⟨Q, hQmem⟩, hQcoc⟩
    · rw [hpiece j hj]; exact hgy.2.2
  have hrankeq : (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 K).2.lumpRank g = γ := by
    have hle := dissolveSeqAux_isLump_le α hα hFG F hFrank γ hγα enum QQ0 h0 K g y (htrans K le_rfl)
    exact le_antisymm hle hgrank
  have hQQ0 : QQ0.2.IsLump g y :=
    dissolveSeqAux_isLump_orig α hα hFG F hFrank γ hγα enum QQ0 K g y (htrans K le_rfl) hrankeq
  obtain ⟨N, hN⟩ := dissolveSeqAux_dissolved α hα hFG F hFrank γ hγα enum QQ0 henum hQQ0 hrankeq
  exact hN (max K N) (le_max_right _ _) (htrans (max K N) (le_max_left _ _))

end DissolveSeq

/-- **The dissolving sequence.** The heart of `dissolveOneLevel`: there is a sequence of
`c`-partitions `Parts` of `F` whose limit inferior covers `F.domain` (so is a `c`-partition)
and all of whose lumps have rank `< γ`. Built by dissolving the countably many rank-`γ`
lumps one at a time via `refiningBy1` and taking the limit inferior; the coverage clause is
the stabilisation of each point's (eventually constant) sequence of pieces, and the lump
clause combines `refiningBy1`'s clauses 1 (dissolved lump gone) and 5 (new lumps rank `< γ`)
with `hbound`. The lump conclusion is stated for an arbitrary `c`-partition proof `hL` of the
liminf (proof-irrelevant), so `dissolveOneLevel` can consume it directly. -/
theorem dissolveSeq_exists
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α)
    (γ : Ordinal.{0}) (hγα : γ ≤ α)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hbound : ∀ g y, hA.IsLump g y → hA.lumpRank g ≤ γ) :
    ∃ Parts : ℕ → Set (Set ↑F.domain), (∀ k, F.IsCPartition (Parts k)) ∧
      (∀ x : ↑F.domain, ∃ P ∈ cPartitionLiminf Parts, x ∈ P) ∧
      (∀ (hL : F.IsCPartition (cPartitionLiminf Parts)) g y,
        hL.IsLump g y → hL.lumpRank g < γ) := by
  classical
  -- Build an enumeration `enum` of the rank-`γ` lumps (via their block pieces `B ⊆ Part`).
  set yOf : Set ↑F.domain → Baire := fun P =>
    if h : IsCentered (F.restrict P).func then cocenter (F.restrict P).func h else default
    with hyOf
  set B : Set (Set ↑F.domain) :=
    {P | ∃ g y, hA.IsLump g y ∧ hA.lumpRank g = γ ∧ P ∈ hA.blockPieces g y} with hB
  have hBsub : B ⊆ Part := by rintro P ⟨g, y, _, _, hPb⟩; exact hPb.choose
  have hBc : B.Countable := hA.countable.mono hBsub
  obtain ⟨enum, henum⟩ :
      ∃ enum : ℕ → ScatFun × Baire, ∀ g y, hA.IsLump g y → hA.lumpRank g = γ →
        ∃ k : ℕ, (enum k).2 = y ∧ (enum k).1.Equiv g := by
    rcases B.eq_empty_or_nonempty with hBe | hBn
    · refine ⟨fun _ => (F, default), fun g y hg hgr => ?_⟩
      obtain ⟨P, hP⟩ := refiningBy1_blockPieces_nonempty hA hg
      exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe P ⟨g, y, hg, hgr, hP⟩) not_false
    · obtain ⟨e, he⟩ := hBc.exists_eq_range hBn
      refine ⟨fun k => (F.restrict (e k), yOf (e k)), fun g y hg hgr => ?_⟩
      obtain ⟨P, hP⟩ := refiningBy1_blockPieces_nonempty hA hg
      have hPB : P ∈ B := ⟨g, y, hg, hgr, hP⟩
      rw [he] at hPB
      obtain ⟨k, hk⟩ := hPB
      obtain ⟨hPmem, hPeq, hPcoc⟩ := hP
      refine ⟨k, ?_, ?_⟩
      · dsimp only; rw [hk, hyOf]
        have hcent : IsCentered (F.restrict P).func := hA.centered P hPmem
        simp only [dif_pos hcent]
        have : hA.cocenterOf hPmem = y := hPcoc
        rwa [ScatFun.IsCPartition.cocenterOf] at this
      · dsimp only; rw [hk]; exact hPeq
  set QQ0 : {Q : Set (Set ↑F.domain) // F.IsCPartition Q} := ⟨Part, hA⟩ with hQQ0
  refine ⟨fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).1,
    fun k => (dissolveSeqAux α hα hFG F hFrank γ hγα enum QQ0 k).2,
    dissolveSeq_cover α hα hFG F hFrank γ hγα enum QQ0,
    fun hL => dissolveSeq_lump α hα hFG F hFrank γ hγα enum QQ0 henum hbound hL⟩

/-- **Dissolving one rank level.** From a `c`-partition all of whose lumps have rank `≤ γ`
(with `γ ≤ α = CB(F)`), produce a `c`-partition all of whose lumps have rank `< γ`. This is
the inner step of `ExistenceFinePartitions`: enumerate the countably many rank-`γ` lumps and
dissolve them one at a time via `refiningBy1`, taking the limit inferior of the resulting
sequence (`cPartitionLiminf` / `isCPartition_cPartitionLiminf`). `refiningBy1` clause 3
(new lumps have rank `< γ`) and clause 1 (the dissolved lump is gone) give the conclusion. -/
theorem dissolveOneLevel
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α)
    (γ : Ordinal.{0}) (hγα : γ ≤ α)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hbound : ∀ g y, hA.IsLump g y → hA.lumpRank g ≤ γ) :
    ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'),
      ∀ g y, hA'.IsLump g y → hA'.lumpRank g < γ := by
  obtain ⟨Parts, hP, hcov, hlump⟩ := dissolveSeq_exists α hα hFG F hFrank γ hγα hA hbound
  exact ⟨cPartitionLiminf Parts, isCPartition_cPartitionLiminf Parts hP hcov,
    hlump (isCPartition_cPartitionLiminf Parts hP hcov)⟩

/-- **The finite descent over rank levels.** Iterating `dissolveOneLevel` `m` times drives an
all-lumps-`≤ λ+m` `c`-partition down to an all-lumps-`< λ` one. Each step turns
`≤ λ+(k+1)` into `< λ+(k+1) = ≤ λ+k` (successor), and the base case `m = 0` dissolves the
top level `γ = λ`. -/
theorem dissolveDown
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow α)
    (F : ScatFun) (hFrank : CBRank F.func = α) (lam : Ordinal.{0}) :
    ∀ (m : ℕ), lam + (m : Ordinal.{0}) ≤ α →
      ∀ {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part),
        (∀ g y, hA.IsLump g y → hA.lumpRank g ≤ lam + (m : Ordinal.{0})) →
        ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'),
          ∀ g y, hA'.IsLump g y → hA'.lumpRank g < lam := by
  intro m
  induction m with
  | zero =>
    intro hle Part hA hbound
    simp only [Nat.cast_zero, add_zero] at hle hbound
    exact dissolveOneLevel α hα hFG F hFrank lam hle hA hbound
  | succ k ih =>
    intro hle Part hA hbound
    have hcast : lam + ((k + 1 : ℕ) : Ordinal.{0}) = lam + (k : Ordinal.{0}) + 1 := by
      rw [Nat.cast_succ, ← add_assoc]
    rw [hcast] at hle hbound
    obtain ⟨Part', hA', hlt⟩ :=
      dissolveOneLevel α hα hFG F hFrank (lam + (k : Ordinal.{0}) + 1) hle hA hbound
    have hle' : lam + (k : Ordinal.{0}) ≤ α := le_trans le_self_add hle
    refine ih hle' hA' (fun g y hg => ?_)
    have := hlt g y hg
    rwa [Ordinal.add_one_eq_succ, Order.lt_succ_iff] at this

/-- **The lump-dissolving induction of `ExistenceFinePartitions`**
(`6_double_successor_memo.tex:113-118`). From *any* `c`-partition of `F`, produce a `c`-partition
all of whose lumps have rank `< λ`. This is the `(𝒫_i)_{i ≤ n+2}` outer induction: each step
lowers the maximal lump rank by one (from `λ+n+2-i` to `λ+n+2-(i+1)`) by enumerating the
countably many lumps at the top rank and dissolving them one at a time via `refiningBy1`, then
taking the "limit inferior" `⋃_k ⋂_{k ≤ j} 𝒫'_j` of the resulting sequence; `refiningBy1`'s
piece-survival clause `𝒫 \ 𝒫_{g,y} ⊆ 𝒫'` is what makes the limit inferior well-behaved. After
`n+2` steps every remaining lump has rank `< λ`.

The liminf itself is now available as `cPartitionLiminf` / `isCPartition_cPartitionLiminf`,
which reduces "the liminf is a `c`-partition" to a single **coverage/stabilisation** obligation
(each point's decreasing sequence of pieces stabilises). What remains open here is: (i) building
the `refiningBy1` sequence for a fixed rank via `Nat`-recursion + `Classical.choice`,
(ii) discharging that coverage obligation from well-foundedness of `CB`-rank + the survival
clause, and (iii) the outer *finite* induction over the `n+2` rank levels `λ+1, …, λ+n+2`. -/
theorem existenceFinePartitions_dissolveAll
    (lam : Ordinal.{0}) (_hlam_lt : lam < omega1) (_hlim : Order.IsSuccLimit lam) (n : ℕ)
    (hα_lt : lam + (n : Ordinal.{0}) + 2 < omega1)
    (hFG : ScatFun.FGBelow (lam + (n : Ordinal.{0}) + 2))
    (F : ScatFun) (hFrank : CBRank F.func = lam + (n : Ordinal.{0}) + 2)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) :
    ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'),
      ∀ g y, hA'.IsLump g y → hA'.lumpRank g < lam := by
  -- All lumps have rank `≤ CB(F) = λ+n+2`; descend `n+2` levels via `dissolveDown`.
  have hcast : lam + ((n + 2 : ℕ) : Ordinal.{0}) = lam + (n : Ordinal.{0}) + 2 := by
    push_cast; rw [← add_assoc]
  refine dissolveDown (lam + (n : Ordinal.{0}) + 2) hα_lt hFG F hFrank lam (n + 2)
    (by rw [hcast]) hA (fun g y hg => ?_)
  rw [hcast]
  exact (lumpRank_le_cbRank hA hg).trans hFrank.le

/-- **Join-primeness of `𝒲`-reference functions over a binary clopen ray split.**
If `w ∈ 𝒲_α` reduces to the `j`-th ray of `F ↾ (V ∪ U)` at `y` (with `V, U` disjoint clopen),
then `w` reduces to the `j`-th ray of `F ↾ V` *or* of `F ↾ U`. This is the forward half
extracted from the former `isOmegaRegularAt_union_of_lowRank`: split the ray over the 2-block
domain partition `{V ∩ RS, U ∩ RS}` and apply the intertwining-for-`ω`-centered piece lemmas
(`intertwine_reductions_maxFun_limit_piece` / `_omega_centered_piece`), which say the ω-centered
`w` reduces into one of the two blocks. The degenerate `w = ℓ_0` (`α.limitPart = 0`) has empty
domain (`MaxDom 0 = ∅`) and is dispatched up front. -/
lemma omegaRef_rayOn_binary_joinPrime
    (F : ScatFun) (V U : Set ↑F.domain) (y : Baire)
    (hUcl : IsClopen U) (hVcl : IsClopen V) (hdisj : Disjoint V U)
    (α : Ordinal.{0}) (hα_lt : α < omega1)
    (w : ScatFun) (hwα : w ∈ omegaRegularSet α hα_lt)
    (j : ℕ)
    (hj : ScatFun.Reduces w ((F.restrict (V ∪ U)).rayOn y Set.univ j)) :
    ScatFun.Reduces w ((F.restrict V).rayOn y Set.univ j)
      ∨ ScatFun.Reduces w ((F.restrict U).rayOn y Set.univ j) := by
  classical
  by_cases hwempty : IsEmpty ↑w.domain
  · exact Or.inl (ScatFun.reduces_of_isEmpty_domain hwempty)
  set RS : Set ↑F.domain := {a : ↑F.domain | F.func a ∈ RaySet Set.univ y j} with hRS
  set Dvu : Set ↑F.domain := (V ∪ U) ∩ RS with hDvu
  set Dv : Set ↑F.domain := V ∩ RS with hDvdef
  set Du : Set ↑F.domain := U ∩ RS with hDudef
  have hRScl : IsClopen RS :=
    ⟨(isClopen_raySet y j).1.preimage F.hCont, (isClopen_raySet y j).2.preimage F.hCont⟩
  -- Move `hj` to the `F`-level ray `F.rayOn y (V∪U) j = F.restrict Dvu`.
  have hrayEq : F.rayOn y (V ∪ U) j = F.restrict Dvu := by rw [hDvu, hRS]; rfl
  have hjD : ScatFun.Reduces w (F.restrict Dvu) := by
    rw [← hrayEq]; exact hj.trans (ScatFun.rayOn_restrict_equiv F (V ∪ U) y j).1
  -- The 2-block domain partition of `F.restrict Dvu`.
  set φ : ↑(F.restrict Dvu).domain → ↑F.domain :=
    fun w' => (F.restrictEquiv Dvu w' : ↑F.domain) with hφ
  have hφcont : Continuous φ :=
    continuous_subtype_val.comp (F.restrictEquiv Dvu).continuous
  set B : ℕ → Set ↑(F.restrict Dvu).domain :=
    fun i => if i = 0 then φ ⁻¹' Dv else if i = 1 then φ ⁻¹' Du else ∅ with hBdef
  have hDvDvu : Dv ⊆ Dvu := fun a ha => ⟨Or.inl ha.1, ha.2⟩
  have hDuDvu : Du ⊆ Dvu := fun a ha => ⟨Or.inr ha.1, ha.2⟩
  have hVUdisj : Disjoint Dv Du := by
    rw [hDvdef, hDudef]
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hdisj
  have hBmem : ∀ k a, a ∈ B k → (k = 0 ∧ φ a ∈ Dv) ∨ (k = 1 ∧ φ a ∈ Du) := by
    intro k a hak
    rcases eq_or_ne k 0 with rfl | h0
    · exact Or.inl ⟨rfl, by simpa only [hBdef, if_pos rfl, Set.mem_preimage] using hak⟩
    · rcases eq_or_ne k 1 with rfl | h1
      · exact Or.inr ⟨rfl, by
          simpa only [hBdef, if_neg h0, if_pos rfl, Set.mem_preimage] using hak⟩
      · simp only [hBdef, if_neg h0, if_neg h1, Set.mem_empty_iff_false] at hak
  have hduB : (F.restrict Dvu).IsDisjointUnion B := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rcases eq_or_ne i 0 with rfl | h0
      · simpa only [hBdef, if_pos rfl, hDvdef] using (hVcl.inter hRScl).preimage hφcont
      · rcases eq_or_ne i 1 with rfl | h1
        · simpa only [hBdef, if_neg h0, if_pos rfl, hDudef] using
            (hUcl.inter hRScl).preimage hφcont
        · simp only [hBdef, if_neg h0, if_neg h1]; exact isClopen_empty
    · intro i i' hii'
      refine Set.disjoint_left.mpr fun a hai hai' => ?_
      rcases hBmem i a hai with ⟨rfl, hDv⟩ | ⟨rfl, hDu⟩ <;>
        rcases hBmem i' a hai' with ⟨rfl, hDv'⟩ | ⟨rfl, hDu'⟩
      · exact hii' rfl
      · exact (Set.disjoint_left.mp hVUdisj hDv) hDu'
      · exact (Set.disjoint_left.mp hVUdisj hDv') hDu
      · exact hii' rfl
    · ext w'
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hmemDvu : φ w' ∈ (V ∪ U) ∩ RS := hDvu ▸ (F.restrictEquiv Dvu w').2
      rcases hmemDvu.1 with hV | hU
      · refine ⟨0, ?_⟩
        simp only [hBdef, if_pos rfl, Set.mem_preimage, hDvdef, Set.mem_inter_iff]
        exact ⟨hV, hmemDvu.2⟩
      · refine ⟨1, ?_⟩
        simp only [hBdef, if_neg one_ne_zero, hDudef]
        exact ⟨hU, hmemDvu.2⟩
  have hAn : ∀ i, 1 < i → B i = ∅ := by
    intro i hi
    simp only [hBdef, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega)]
  -- Block identifications.
  have hB0equiv : ScatFun.Equiv ((F.restrict Dvu).restrict (B 0)) (F.restrict Dv) := by
    have h := ScatFun.restrict_restrict_equiv F Dvu Dv hDvDvu
    simp only [hBdef, if_pos rfl]; exact h
  have hB1equiv : ScatFun.Equiv ((F.restrict Dvu).restrict (B 1)) (F.restrict Du) := by
    have h := ScatFun.restrict_restrict_equiv F Dvu Du hDuDvu
    simp only [hBdef, if_neg one_ne_zero]; exact h
  have hDvRay : ScatFun.Reduces (F.restrict Dv) ((F.restrict V).rayOn y Set.univ j) := by
    rw [hDvdef, hRS]; exact (ScatFun.rayOn_restrict_equiv F V y j).2
  have hDuRay : ScatFun.Reduces (F.restrict Du) ((F.restrict U).rayOn y Set.univ j) := by
    rw [hDudef, hRS]; exact (ScatFun.rayOn_restrict_equiv F U y j).2
  have hpiece : ∃ i ≤ 1, ScatFun.Reduces w ((F.restrict Dvu).restrict (B i)) := by
    have hwα' := hwα
    rw [omegaRegularSet, Finset.mem_insert] at hwα'
    rcases hwα' with rfl | himg
    · by_cases hβ0 : α.limitPart = 0
      · exact absurd (Set.isEmpty_coe_sort.mpr
          (show MaxDom α.limitPart = ∅ by rw [hβ0]; exact MaxDom_zero)) hwempty
      · have hβlim : Order.IsSuccLimit α.limitPart :=
          α.limitPart_isLimit_or_zero.resolve_right hβ0
        exact ScatFun.intertwine_reductions_maxFun_limit_piece (F.restrict Dvu) α.limitPart _
          hβlim hβ0 B hduB hAn hjD
    · obtain ⟨h, hhmem, rfl⟩ := Finset.mem_image.mp himg
      exact ScatFun.intertwine_reductions_omega_centered_piece (F.restrict Dvu) h B hduB hAn
        (ScatFun.isCentered_of_mem_Centered α h hhmem) hjD
  obtain ⟨i, hi1, hired⟩ := hpiece
  interval_cases i
  · exact Or.inl ((hired.trans hB0equiv.1).trans hDvRay)
  · exact Or.inr ((hired.trans hB1equiv.1).trans hDuRay)

/-
The union of the pieces of a `(g,y)`-block is clopen: it is a union of (clopen) partition
pieces, and its complement is the union of the remaining (open) pieces.
-/
lemma blockPieces_sUnion_isClopen {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire) :
    IsClopen (⋃₀ hA.blockPieces g y) := by
      constructor;
      · have h_closed : IsClosed (⋃₀ Part) := by
          rw [ hA.sUnion_eq ] ; exact isClosed_univ;
        have h_closed : ⋃₀ hA.blockPieces g y = (⋃₀ Part) \ ⋃₀ (Part \ hA.blockPieces g y) := by
          ext x
          simp only [mem_sUnion, mem_diff, not_exists, not_and, and_imp];
          constructor;
          · rintro ⟨ t, ht, hx ⟩;
            exact ⟨ ⟨ t, ht.1, hx ⟩, fun u hu htu hxu => hA.pairwiseDisjoint hu ht.1 ( by aesop ) |> fun h => h.le_bot ⟨ hxu, hx ⟩ ⟩;
          · grind;
        convert IsClosed.sdiff ‹IsClosed (⋃₀ Part)› ( isOpen_sUnion fun P hP => ?_ ) using 1;
        exact hA.isClopen P hP.1 |>.isOpen;
      · exact isOpen_sUnion fun P hP => ( hA.isClopen P ( hP.1 ) ).isOpen

/-- The CB-rank of the union of a nonempty `(g,y)`-block equals `CB g` (all pieces of the block
are `Equiv g`, so all have rank `CB g`; `cbRank_restrict_sUnion_const`). -/
lemma cbRank_blockPieces_sUnion {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire)
    (hne : (hA.blockPieces g y).Nonempty) :
    CBRank (F.restrict (⋃₀ hA.blockPieces g y)).func = CBRank g.func := by
  refine cbRank_restrict_sUnion_const ?_ ?_ hne ?_
  · exact hA.countable.mono (fun P hP => hP.choose)
  · exact fun P hP => hA.isClopen P hP.choose
  · rintro P ⟨hPmem, hPeq, -⟩
    exact cbRank_eq_of_equiv hPeq

/-
A `𝒫`-block `(g,y)` with centered `g`, `y ∈ Y_𝒫`, and `CB g > λ` is `𝒲`-regular at `y`,
provided every `𝒫`-lump has rank `< λ`: such a block cannot be a lump (its rank `CB g` exceeds
`λ`), and failing to be a lump — with the first two clauses of `IsLump` satisfied — forces
`𝒲`-regularity.
-/
lemma isOmegaRegularAt_blockPieces_of_not_lump {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}}
    (hlumps : ∀ (g : ScatFun) (y : Baire), hA.IsLump g y → hA.lumpRank g < lam)
    {g : ScatFun} {y : Baire} (hgcent : IsCentered g.func)
    (hycc : y ∈ hA.cocenterSet) (hgbig : lam < CBRank g.func) :
    IsOmegaRegularAt (F.restrict (⋃₀ hA.blockPieces g y)) y := by
      by_contra h;
      exact absurd ( hlumps g y ⟨ hycc, hgcent, h ⟩ ) ( by simpa using hgbig.not_gt )

/-
The union of a `(g,y)`-block (with `CB g > λ`) is disjoint from the union of the small
(rank `< λ`) pieces: no block piece (rank `= CB g > λ`) can coincide with a small piece, so
pairwise disjointness of the partition applies.
-/
lemma blockPieces_disjoint_lowRank {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}}
    {g : ScatFun} {y : Baire} (hgbig : lam < CBRank g.func)
    (U : Set ↑F.domain)
    (hU : U = ⋃₀ {Q | Q ∈ Part ∧ CBRank (F.restrict Q).func < lam}) :
    Disjoint (⋃₀ hA.blockPieces g y) U := by
      rw [ Set.disjoint_left, hU ];
      rintro x ⟨ P, ⟨ hPmem, hPeq, hycc ⟩, hx ⟩ ⟨ Q, hQmem, hx' ⟩;
      have := hA.pairwiseDisjoint hPmem hQmem.1;
      exact Set.disjoint_left.mp ( this ( by rintro rfl; exact hQmem.2.not_ge <| by simpa [ cbRank_eq_of_equiv hPeq ] using hgbig.le ) ) hx hx'

/-- A `𝒫'`-lump `(g,y)` has `CB g > λ` when every piece of `𝒫'` has rank `> λ`: the block
`𝒫'_{(g,y)}` is nonempty and every piece of it is `Equiv g`, so `CB g` equals the rank of a
`𝒫'`-piece, which exceeds `λ`. -/
lemma lump_cbRank_gt {F : ScatFun} {Part' : Set (Set ↑F.domain)}
    (hA' : F.IsCPartition Part') {lam : Ordinal.{0}}
    (hrankgt : ∀ X ∈ Part', lam < CBRank (F.restrict X).func)
    {g : ScatFun} {y : Baire} (hlump : hA'.IsLump g y) :
    lam < CBRank g.func := by
  obtain ⟨X, hX⟩ := refiningBy1_blockPieces_nonempty hA' hlump
  obtain ⟨hXmem, hXeq, -⟩ := hX
  rw [← cbRank_eq_of_equiv hXeq]
  exact hrankgt X hXmem

/-
**Cocenter transfer for the gobbled partition.** In the gobbling construction, the
cocenter set of `𝒫' = insert D (Part \ B)` is contained in that of `𝒫`: pieces of `Part \ B`
keep their cocenter, and `D = P ∪ U` (`≡ F↾P`) has the same cocenter as `P ∈ Part`. Hence any
cocenter of `𝒫'` (in particular `y` for a `𝒫'`-lump) is a cocenter of `𝒫`.
-/
lemma gobble_cocenterSet_mem {F : ScatFun} {Part Part' : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (hA' : F.IsCPartition Part')
    (P D : Set ↑F.domain) (hPPart : P ∈ Part) (hPsubD : P ⊆ D)
    (hDcent : IsCentered (F.restrict D).func)
    (hDequivP : (F.restrict D).Equiv (F.restrict P))
    (hPart'sub : Part' ⊆ insert D Part)
    {y : Baire} (hy : y ∈ hA'.cocenterSet) :
    y ∈ hA.cocenterSet := by
      cases' hy with X hX;
      cases' hPart'sub X.2 with hX hX;
      · have h_cocenter_eq : cocenter (F.restrict D).func hDcent = cocenter (F.restrict P).func (hA.centered P hPPart) := by
          apply cocenter_restrict_eq_of_subset_equiv F P D hPsubD (hA.centered P hPPart) hDcent hDequivP;
        use ⟨P, hPPart⟩;
        unfold ScatFun.IsCPartition.cocenterOf at *; aesop;
      · use ⟨ X, hX ⟩ ; aesop;

/-
**The `hA`-block of a `𝒫'`-lump is nonempty.** With `CB g > λ`, small pieces cannot lie in
the block, so the nonempty `𝒫'`-block `{D} ∪ (blocks in Part\B)` corresponds to a nonempty
`hA`-block `{P} ∪ (same blocks)`.
-/
lemma gobble_blockPieces_hA_nonempty {F : ScatFun} {Part Part' : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}}
    (P U D : Set ↑F.domain) (S B : Set (Set ↑F.domain))
    (hS : S = {Q | Q ∈ Part ∧ CBRank (F.restrict Q).func < lam})
    (_hU : U = ⋃₀ S) (_hD : D = P ∪ U) (hB : B = insert P S)
    (hPart' : Part' = insert D (Part \ B))
    (hPPart : P ∈ Part) (hPsubD : P ⊆ D)
    (hDcent : IsCentered (F.restrict D).func)
    (hDequivP : (F.restrict D).Equiv (F.restrict P))
    (hA' : F.IsCPartition Part')
    {g : ScatFun} {y : Baire} (_hgbig : lam < CBRank g.func)
    (hlump : hA'.IsLump g y) :
    (hA.blockPieces g y).Nonempty := by
      -- Obtain `X ∈ hA'.blockPieces g y` from nonemptiness of the `𝒫'`-block.
      obtain ⟨X, hXPart, hXeq, hXcoc⟩ := refiningBy1_blockPieces_nonempty hA' hlump
      by_cases hXeqD : X = D
      · refine ⟨P, hPPart, ?_, ?_⟩
        · exact ScatFun.Equiv.trans hDequivP.symm (by simpa [hXeqD] using hXeq)
        · have h_cocenter_eq :
              cocenter (F.restrict D).func hDcent
                = cocenter (F.restrict P).func (hA.centered P hPPart) :=
            cocenter_restrict_eq_of_subset_equiv F P D hPsubD (hA.centered P hPPart) hDcent hDequivP
          grind +locals
      · have hXPart' : X ∈ Part \ B := by grind
        refine ⟨X, ?_, hXeq, ?_⟩ <;> simp_all +decide [ScatFun.IsCPartition.cocenterOf]

/-
**The `𝒫'`-block union equals the `hA`-block union, or that plus `U`.** In the gobbling
construction, `𝒫' = insert D (Part \ B)` with `D = P ∪ U`, `B = {P} ∪ S`. With `CB g > λ`,
no small piece (`∈ S`, rank `< λ`) realises `g`; and `D` realises `(g,y)` iff `P` does
(`F↾D ≡ F↾P`, same cocenter). Hence the `𝒫'`-block equals the `hA`-block (`= V`) if `P` is not
in the `hA`-block, or `V` with `P` swapped for `D = P ∪ U` (so `V ∪ U`) if it is.
-/
set_option maxHeartbeats 800000 in
lemma gobble_blockPieces_sUnion_eq {F : ScatFun} {Part Part' : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}}
    (P U D : Set ↑F.domain) (S B : Set (Set ↑F.domain))
    (hS : S = {Q | Q ∈ Part ∧ CBRank (F.restrict Q).func < lam})
    (hU : U = ⋃₀ S) (hD : D = P ∪ U) (hB : B = insert P S)
    (hPart' : Part' = insert D (Part \ B))
    (hPPart : P ∈ Part) (_hPsubD : P ⊆ D)
    (hDcent : IsCentered (F.restrict D).func)
    (hDequivP : (F.restrict D).Equiv (F.restrict P))
    (hA' : F.IsCPartition Part')
    {g : ScatFun} {y : Baire} (hgbig : lam < CBRank g.func) :
    (P ∈ hA.blockPieces g y →
        ⋃₀ hA'.blockPieces g y = (⋃₀ hA.blockPieces g y) ∪ U)
      ∧ (P ∉ hA.blockPieces g y →
        ⋃₀ hA'.blockPieces g y = ⋃₀ hA.blockPieces g y) := by
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · have h_blockPieces_eq : hA'.blockPieces g y = insert D (hA.blockPieces g y \ {P}) := by
      ext Q; simp;
      constructor <;> intro hQ <;> simp_all +decide [ ScatFun.IsCPartition.blockPieces ];
      · rcases hQ.2.1 with ( rfl | ⟨ hQ₁, hQ₂, hQ₃ ⟩ ) <;> simp_all +decide [ ScatFun.IsCPartition.cocenterOf ];
      · rcases hQ with ( rfl | ⟨ ⟨ hQ₁, hQ₂ ⟩, hQ₃ ⟩ ) <;> simp_all +decide [ ScatFun.IsCPartition.cocenterOf ];
        · have := cocenter_restrict_eq_of_subset_equiv F P ( P ∪ ⋃₀ { Q | Q ∈ Part ∧ CBRank ( F.restrict Q ).func < lam } ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ ScatFun.Equiv ];
          exact ⟨ hDequivP.1.trans hP.1.1, hP.1.2.trans hDequivP.2 ⟩;
          · exact hA.centered P hPPart;
          · grobner;
        · grind [cbRank_eq_of_equiv];
    have hPU : P ∪ ⋃₀ (hA.blockPieces g y \ {P}) = ⋃₀ hA.blockPieces g y := by
      rw [← Set.sUnion_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem hP]
    rw [h_blockPieces_eq, Set.sUnion_insert, hD, Set.union_right_comm, hPU]
  · have h_subset : hA'.blockPieces g y ⊆ Part \ B := by
      intro X hX;
      by_cases hX' : X = D;
      · contrapose! hP; simp_all +decide [ ScatFun.IsCPartition.blockPieces ] ;
        have hPcent : IsCentered (F.restrict P).func := by
          exact hA.centered P hPPart
        have hPcoc : cocenter (F.restrict P).func hPcent = cocenter (F.restrict D).func hDcent := by
          convert cocenter_restrict_eq_of_subset_equiv F P D ( by aesop ) hPcent hDcent ( by aesop ) |> Eq.symm using 1
        exact ⟨hDequivP.symm.trans hX.left, by
          grind +locals⟩;
      · grind +locals;
    have h_eq : hA'.blockPieces g y = hA.blockPieces g y := by
      ext X; simp at *; (
      constructor <;> intro hX <;> simp_all +decide [ ScatFun.IsCPartition.blockPieces ] ;
      · rcases hX with ⟨ hX₁, hX₂, hX₃ ⟩ ; specialize h_subset ⟨ hX₁, hX₂, hX₃ ⟩ ; simp_all +decide ;
        convert hX₃ using 1;
      · use Or.inr ⟨ hX.2.1, by
          rintro rfl; exact hP hX.1 hX.2.2;, by
          exact fun _ => le_of_lt ( by simpa [ cbRank_eq_of_equiv hX.1 ] using hgbig ) ; ⟩
        generalize_proofs at *;
        convert hX.2.choose_spec using 1);
    rw [h_eq]

/-- **Lemma A: a single centered function is `𝒲`-regular at its cocenter.** For centered `C`
with cocenter `y = cocenter C.func`, the ray-index obstruction set `{j | w ≤ ray_j(C, y)}` is
empty or infinite for every reference `w ∈ 𝒲_{CB C}`. This is the *remark right after the
definition of a lump* in the memoir (`6_double_successor_memo.tex:42-44`), and the analytic
heart of the "no lumps" clause of `ExistenceFinePartitions`.

**Proof (memoir remark).** Suppose `{j | w ≤ ray_j(C,y)}` is nonempty; show it is infinite.
Fix any `m`. By *rigidity of the cocenter* (`rays_glRegular` in `CenteredAsPgluing/Helpers`,
the memoir's `Rigidityofthecocenter`), for each ray index there is `M ≥ m` with
`ray_j(C,y) ≤ glWindow (Ray(C,y,·)) m M = gl_{i=m}^{M} ray_i(C,y)`. So from `w ≤ ray_j(C,y)`
we get `w ≤ gl_{i=m}^{M} ray_i(C,y)`. Now `w` is `ω h` (`h ∈ Centered`) or `ℓ_λ`, both
join-prime over a finite gluing: by `intertwine_reductions_omega_centered_piece` /
`intertwine_reductions_maxFun_limit_piece` (applied to the gl-block `IsDisjointUnion` of the
window), `w ≤ ray_i(C,y)` for some `m ≤ i ≤ M`. As `m` was arbitrary this yields witnesses
`≥ m` for every `m`, so the index set is infinite.

**Not** the false "all `U`-rays `< λ`": this is a fact about a *single* centered part. An
infinite union of centered parts (a `𝒫`-block) need *not* be regular — that is exactly what a
lump is (`refiningBy1_piece_cbRank_eq` docstring; memoir: `𝒫_{(g,y)}` infinite for a lump).
Ingredients: `rays_glRegular`, `glWindow`, `intertwine_reductions_{omega_centered,maxFun_limit}_piece`.
-/
lemma isOmegaRegularAt_of_centered (C : ScatFun) (hcent : IsCentered C.func) :
    IsOmegaRegularAt C (cocenter C.func hcent) := by
  classical
  set y : Baire := cocenter C.func hcent with hy
  intro w hw
  by_cases hwe : IsEmpty ↑w.domain
  · -- `w` empty ⟹ reduces to every ray ⟹ obstruction set is `univ`, infinite.
    left
    have : {j : ℕ | ScatFun.Reduces w (C.rayOn y Set.univ j)} = Set.univ := by
      ext j; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ScatFun.reduces_of_isEmpty_domain hwe
    rw [this]; exact Set.infinite_univ
  by_cases hEmp : {j : ℕ | ScatFun.Reduces w (C.rayOn y Set.univ j)} = ∅
  · exact Or.inr hEmp
  left
  -- Nonempty: pick `j0` with `w ≤ ray_{j0}`; show the set is unbounded, hence infinite.
  obtain ⟨j0, hj0⟩ := Set.nonempty_iff_ne_empty.mpr hEmp
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro m
  -- Rigidity: `ray_{j0} ≤ glWindow (rays) (m+1) M` for some `M ≥ m+1`.
  obtain ⟨M, _hmM, hwin⟩ := rays_glRegular C hcent (m + 1) j0
  set H : ℕ → ScatFun :=
    fun k => if m + 1 ≤ k ∧ k ≤ M then C.rayOn y Set.univ k else ScatFun.empty with hH
  have hwG : ScatFun.Reduces w (ScatFun.gl H) :=
    (hj0 : ScatFun.Reduces w (C.rayOn y Set.univ j0)).trans hwin
  have hdu : (ScatFun.gl H).IsDisjointUnion (glBlockSet H) := gl_isDisjointUnion_blockSet H
  have hAn : ∀ i, M < i → glBlockSet H i = ∅ := by
    intro i hi
    apply glBlockSet_eq_empty
    have hHi : H i = ScatFun.empty := by rw [hH]; simp only; rw [if_neg (by omega)]
    rw [hHi]; exact Set.isEmpty_coe_sort.mpr rfl
  -- Join-primeness of `w = ℓ_λ / ω h` over the finite window gluing.
  obtain ⟨i, _hiM, hred⟩ :
      ∃ i ≤ M, ScatFun.Reduces w ((ScatFun.gl H).restrict (glBlockSet H i)) := by
    rw [omegaRegularSet, Finset.mem_insert] at hw
    rcases hw with rfl | himg
    · by_cases hβ0 : (CBRank C.func).limitPart = 0
      · exact absurd (Set.isEmpty_coe_sort.mpr
          (show MaxDom (CBRank C.func).limitPart = ∅ by rw [hβ0]; exact MaxDom_zero)) hwe
      · have hβlim : Order.IsSuccLimit (CBRank C.func).limitPart :=
          (CBRank C.func).limitPart_isLimit_or_zero.resolve_right hβ0
        exact ScatFun.intertwine_reductions_maxFun_limit_piece (ScatFun.gl H)
          (CBRank C.func).limitPart _ hβlim hβ0 (glBlockSet H) hdu hAn hwG
    · obtain ⟨h, hhmem, rfl⟩ := Finset.mem_image.mp himg
      exact ScatFun.intertwine_reductions_omega_centered_piece (ScatFun.gl H) h (glBlockSet H)
        hdu hAn (ScatFun.isCentered_of_mem_Centered _ h hhmem) hwG
  -- `w ≤ block_i ≤ H i`; `H i` is nonempty (`w` nonempty) so `m+1 ≤ i ≤ M` and `H i = ray_i`.
  have hwHi : ScatFun.Reduces w (H i) := hred.trans (gl_restrict_blockSet_reduces H i)
  have hine : ¬ IsEmpty ↑(H i).domain := by
    intro hHe; obtain ⟨σ, -⟩ := hwHi; exact hwe ⟨fun a => hHe.false (σ a)⟩
  have hi_win : m + 1 ≤ i ∧ i ≤ M := by
    by_contra hc; apply hine; rw [hH]; simp only; rw [if_neg hc]
    exact Set.isEmpty_coe_sort.mpr rfl
  have hHiR : H i = C.rayOn y Set.univ i := by rw [hH]; simp only; rw [if_pos hi_win]
  rw [hHiR] at hwHi
  exact ⟨i, hwHi, by omega⟩

/-- **Adjoining one centered part preserves `𝒲`-regularity at the shared cocenter.**
Let `F ↾ V` be `𝒲`-regular at `y`, and let `D = P ∪ U` be *one* centered clopen part with
`cocenter(F ↾ D) = y`, where `P ⊆ V` and `U` is disjoint clopen from `V` (all three of rank
`= CB(F ↾ V)`). Then `F ↾ (V ∪ U)` is `𝒲`-regular at `y`.

This replaces the earlier (false-premise) `isOmegaRegularAt_union_of_lowRank`. The `𝒫'`-block
`(g,y)` is the disjoint union `(V \ P) ⊔ D`; for each reference `w` and ray index `j`,
join-primeness (`omegaRef_rayOn_binary_joinPrime`) gives
`{j | w ≤ ray_j(F↾(V∪U))} = R_{V\P} ∪ R_D`. `R_D` is empty-or-infinite because `D` is a
*single* centered part with cocenter `y` (`isOmegaRegularAt_of_centered`). If `R_D` is
infinite the union is; if `R_D = ∅` then `R_P ⊆ R_D = ∅` (as `P ⊆ D`), so the set collapses to
`{j | w ≤ ray_j(F↾V)}`, empty-or-infinite by `hVreg`. Crucially the split is over `{V\P, D}`
(with `D` centered), *not* `{V, U}` (`U` need not be centered, and can have a rank-`λ` ray). -/
lemma isOmegaRegularAt_swap_centered
    (lam : Ordinal.{0}) (_hlim : Order.IsSuccLimit lam)
    (F : ScatFun) (V P U D : Set ↑F.domain) (y : Baire)
    (hDdef : D = P ∪ U)
    (hPV : P ⊆ V) (hVcl : IsClopen V) (hUcl : IsClopen U) (hPcl : IsClopen P)
    (hVUdisj : Disjoint V U)
    (hDcent : IsCentered (F.restrict D).func)
    (hDcoc : cocenter (F.restrict D).func hDcent = y)
    (_hVbig : lam < CBRank (F.restrict V).func)
    (hDrank : CBRank (F.restrict D).func = CBRank (F.restrict V).func)
    (hVUrank : CBRank (F.restrict (V ∪ U)).func = CBRank (F.restrict V).func)
    (hVreg : IsOmegaRegularAt (F.restrict V) y) :
    IsOmegaRegularAt (F.restrict (V ∪ U)) y := by
  classical
  set α : Ordinal.{0} := CBRank (F.restrict V).func with hαdef
  have hα_lt : α < omega1 := CBRank_lt_omega1 (F.restrict V).hScat
  have hVmP_cl : IsClopen (V \ P) := hVcl.diff hPcl
  have hDcl : IsClopen D := by rw [hDdef]; exact hPcl.union hUcl
  have hVmP_P_disj : Disjoint (V \ P) P := Set.disjoint_left.mpr (fun a ha haP => ha.2 haP)
  have hVmP_D_disj : Disjoint (V \ P) D := by
    rw [hDdef]; exact hVmP_P_disj.union_right (hVUdisj.mono_left Set.diff_subset)
  have hcover : (V \ P) ∪ D = V ∪ U := by
    rw [hDdef, ← Set.union_assoc, Set.diff_union_of_subset hPV]
  have hVeq : (V \ P) ∪ P = V := Set.diff_union_of_subset hPV
  have hDsub : D ⊆ V ∪ U := hcover ▸ Set.subset_union_right
  have hDreg : IsOmegaRegularAt (F.restrict D) y := by
    have h := isOmegaRegularAt_of_centered (F.restrict D) hDcent
    rwa [hDcoc] at h
  have hmono : ∀ (W : Set ↑F.domain), W ⊆ V ∪ U → ∀ (j : ℕ),
      ScatFun.Reduces ((F.restrict W).rayOn y Set.univ j)
        ((F.restrict (V ∪ U)).rayOn y Set.univ j) := by
    intro W hWsub j
    exact ((ScatFun.rayOn_restrict_equiv F W y j).1.trans
      (ScatFun.rayOn_reduces_mono F y hWsub j)).trans
      (ScatFun.rayOn_restrict_equiv F (V ∪ U) y j).2
  intro w hw
  have hwα : w ∈ omegaRegularSet α hα_lt := by
    have hcong := omegaRegularSet_congr (a := CBRank (F.restrict (V ∪ U)).func) (b := α)
      hVUrank (CBRank_lt_omega1 (F.restrict (V ∪ U)).hScat) hα_lt
    rwa [hcong] at hw
  have hwV : w ∈ omegaRegularSet (CBRank (F.restrict V).func)
      (CBRank_lt_omega1 (F.restrict V).hScat) := by
    rw [← omegaRegularSet_congr hαdef hα_lt (CBRank_lt_omega1 (F.restrict V).hScat)]
    exact hwα
  have hwD : w ∈ omegaRegularSet (CBRank (F.restrict D).func)
      (CBRank_lt_omega1 (F.restrict D).hScat) := by
    rw [omegaRegularSet_congr hDrank (CBRank_lt_omega1 (F.restrict D).hScat) hα_lt]
    exact hwα
  set RD : Set ℕ := {j : ℕ | ScatFun.Reduces w ((F.restrict D).rayOn y Set.univ j)}
    with hRDdef
  set T : Set ℕ := {j : ℕ | ScatFun.Reduces w ((F.restrict (V ∪ U)).rayOn y Set.univ j)}
    with hTdef
  rcases hDreg w hwD with hRDinf | hRDempty
  · left
    refine hRDinf.mono ?_
    intro j hj
    have hjD : ScatFun.Reduces w ((F.restrict D).rayOn y Set.univ j) := hj
    exact hjD.trans (hmono D hDsub j)
  · have hset : T = {j : ℕ | ScatFun.Reduces w ((F.restrict V).rayOn y Set.univ j)} := by
      apply Set.eq_of_subset_of_subset
      · intro j hj
        have hjVU : ScatFun.Reduces w ((F.restrict (V ∪ U)).rayOn y Set.univ j) := hj
        have hjr := omegaRef_rayOn_binary_joinPrime F (V \ P) D y hDcl hVmP_cl hVmP_D_disj
          α hα_lt w hwα j (by rw [hcover]; exact hjVU)
        rcases hjr with hL | hR
        · show ScatFun.Reduces w ((F.restrict V).rayOn y Set.univ j)
          exact hL.trans (((ScatFun.rayOn_restrict_equiv F (V \ P) y j).1.trans
            (ScatFun.rayOn_reduces_mono F y Set.diff_subset j)).trans
            (ScatFun.rayOn_restrict_equiv F V y j).2)
        · exact absurd hR (Set.eq_empty_iff_forall_notMem.mp hRDempty j)
      · intro j hj
        have hjV : ScatFun.Reduces w ((F.restrict V).rayOn y Set.univ j) := hj
        have hjr := omegaRef_rayOn_binary_joinPrime F (V \ P) P y hPcl hVmP_cl hVmP_P_disj
          α hα_lt w hwα j (by rw [hVeq]; exact hjV)
        rcases hjr with hL | hR
        · show ScatFun.Reduces w ((F.restrict (V ∪ U)).rayOn y Set.univ j)
          exact hL.trans (hmono (V \ P) ((Set.diff_subset).trans Set.subset_union_left) j)
        · exfalso
          have hjP2 : ScatFun.Reduces w ((F.restrict D).rayOn y Set.univ j) :=
            hR.trans (((ScatFun.rayOn_restrict_equiv F P y j).1.trans
              (ScatFun.rayOn_reduces_mono F y (hDdef ▸ Set.subset_union_left) j)).trans
              (ScatFun.rayOn_restrict_equiv F D y j).2)
          exact Set.eq_empty_iff_forall_notMem.mp hRDempty j hjP2
    rw [hset]
    exact hVreg w hwV

/-- **The gobbling step of `ExistenceFinePartitions`** (`6_double_successor_memo.tex:119-123`).
From a `c`-partition all of whose lumps have rank `< λ`, produce a *fine* one. Since `CB(F) =
λ+n+2 ≥ λ+2`, `consequencesGeneralStructure_succMaxFun_le` gives `pgl ℓ_λ ≤ F`, hence
(`centerInvariance_cover`, Fact 4.2 item 3) `pgl ℓ_λ ≤ F.restrict P` for some piece `P`. Let
`R = ⋃₀ {Q ∈ 𝒫 | F.restrict Q ≤ ℓ_λ}`; then `gobblingLessThanLambda` (applied to `U = P ∪ R`)
shows `F.restrict (P ∪ R)` is centered and `≡ F.restrict P`. Replacing `P` and every piece of
`R` by their union `P ∪ R` yields a `c`-partition with no lumps and every piece of `CB`-rank
`> λ`, i.e. `IsFine`. Open: the replacement construction (depends on `gobblingLessThanLambda`). -/
theorem existenceFinePartitions_gobble
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (hlim : Order.IsSuccLimit lam) (n : ℕ)
    (_hα_lt : lam + (n : Ordinal.{0}) + 2 < omega1)
    (_hFG : ScatFun.FGBelow (lam + (n : Ordinal.{0}) + 2))
    (F : ScatFun) (hFrank : CBRank F.func = lam + (n : Ordinal.{0}) + 2)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hlumps : ∀ g y, hA.IsLump g y → hA.lumpRank g < lam) :
    ∃ (Part' : Set (Set ↑F.domain)) (hA' : F.IsCPartition Part'), hA'.IsFine lam := by
  -- `S` = the "small" pieces (rank `< λ`), `U = ⋃₀ S` (`R` in the memoir), `B = {P} ∪ S`
  -- the family of pieces we will merge into the single big piece `D = P ∪ U`.
  set S : Set (Set ↑F.domain) := {Q ∈ Part | CBRank (F.restrict Q).func < lam} with hS
  set U : Set ↑F.domain := ⋃₀ S with hU
  have hlim' : Order.IsSuccLimit lam ∨ lam = 0 := Or.inl hlim
  have hScount : S.Countable := hA.countable.mono (fun Q hQ => hQ.1)
  have hSsub : S ⊆ Part := fun Q hQ => hQ.1
  -- **Every piece is centered, hence *simple*, hence of *successor* CB-rank.** This is what
  -- makes `rank < λ ⟺ rank ≤ λ` and, dually, forces the surviving pieces to have rank `> λ`
  -- (never `= λ`, since `λ` is a limit).
  have cbRank_piece_succ : ∀ X ∈ Part, ∃ β, CBRank (F.restrict X).func = Order.succ β := by
    intro X hX
    obtain ⟨β, hne, hempty, -⟩ :=
      scatteredCentered_isSimple (F.restrict X).func (F.restrict X).hScat (hA.centered X hX)
    exact ⟨β, cbRank_eq_succ_of_simple_witness (F.restrict X).func (F.restrict X).hScat β hne hempty⟩
  -- **`CB(F ↾ U) ≤ λ`** (the memoir's "at most `λ`"). `U` is a countable disjoint clopen union
  -- of pieces each of rank `< λ`; the union's rank is the supremum of the block ranks, `≤ λ`.
  -- (Only `≤ λ` holds: with ranks cofinal in the limit `λ` the supremum can equal `λ`.)
  have h_FULtLam : CBRank (F.restrict U).func ≤ lam := by
    by_cases hSne : S.Nonempty
    · obtain ⟨f, hf⟩ := hScount.exists_eq_range hSne
      have hfmem : ∀ i, f i ∈ S := fun i => hf ▸ Set.mem_range_self i
      have hUeq : U = ⋃ i, disjointed f i := by
        rw [hU, iUnion_disjointed, hf, Set.sUnion_range]
      rw [hUeq]
      apply ScatFun.cbRank_restrict_iUnion_le F (disjointed f)
      · -- each `disjointed f i` is clopen (piece minus finitely many pieces).
        intro i
        rw [disjointed_eq_inter_compl]
        have hcl : IsClopen (⋂ jj ∈ Finset.range i, (f jj)ᶜ) :=
          isClopen_biInter_finset (fun k _ => (hA.isClopen (f k) (hSsub (hfmem k))).compl)
        refine (hA.isClopen (f i) (hSsub (hfmem i))).inter ?_
        convert hcl using 2 with jj
        simp [Finset.mem_range]
      · exact fun i j hij => disjoint_disjointed f hij
      · -- rank ≤ λ: `disjointed f i ⊆ f i`, and `f i ∈ S` has rank `< λ`.
        intro i
        have hsub : disjointed f i ⊆ f i := disjointed_subset f i
        have hmono : CBRank (F.restrict (disjointed f i)).func ≤ CBRank (F.restrict (f i)).func :=
          ContinuouslyReduces.rank_monotone (F.restrict (disjointed f i)).hScat
            (F.restrict (f i)).hScat (restrict_reduces_of_subset F hsub)
        exact hmono.trans (le_of_lt (hfmem i).2)
    · -- `S` empty ⇒ `U = ∅` ⇒ rank `0 ≤ λ`.
      have hUe : U = (∅ : Set ↑F.domain) := by
        rw [hU, Set.not_nonempty_iff_eq_empty.mp hSne, Set.sUnion_empty]
      have hem : IsEmpty ↑(F.restrict U).domain := by
        rw [hUe]; exact Set.isEmpty_coe_sort.mpr (by ext y; simp [ScatFun.restrict])
      have hz := ContinuouslyReduces.rank_monotone (F.restrict U).hScat ScatFun.empty.hScat
        (ScatFun.reduces_of_isEmpty_domain hem)
      rw [ScatFun.empty_cbRank] at hz
      exact hz.trans (zero_le lam)
  -- **A base piece exists** (domain nonempty since `CB(F) ≠ 0`).
  have hz0 : CBRank F.func ≠ 0 := by
    rw [hFrank]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : Ordinal) < 2) le_add_self)
  have hdomne : Nonempty ↑F.domain := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hz0 (le_antisymm (by
      have := ContinuouslyReduces.rank_monotone F.hScat ScatFun.empty.hScat
        (ScatFun.reduces_of_isEmpty_domain h)
      rwa [ScatFun.empty_cbRank] at this) (zero_le _))
  obtain ⟨x0⟩ := hdomne
  obtain ⟨P₀, hP₀mem, -⟩ : x0 ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; trivial
  -- **Some piece `P` has rank `≥ λ+2`** (the memoir's `pgl ℓ_λ ≤ F ↾ P`): otherwise every piece
  -- has rank `≤ λ+1`, so `CB(F) = ⨆ (piece ranks) ≤ λ+1 < λ+n+2`, contradiction.
  have h_FPgeLam2 : ∃ P ∈ Part, lam + 2 ≤ CBRank (F.restrict P).func := by
    -- Enumerate `Part` as an `ℕ`-indexed disjoint union (`disjointed` of a range enumeration);
    -- inlined here because `exists_partition_enumeration` lives in `PseudoCentered`, which
    -- imports this file (so we cannot import it back).
    obtain ⟨A, hdu, hAmem⟩ :
        ∃ A : ℕ → Set ↑F.domain, F.IsDisjointUnion A ∧ ∀ i, A i ∈ Part ∨ A i = ∅ := by
      obtain ⟨g, hg⟩ := hA.countable.exists_eq_range ⟨P₀, hP₀mem⟩
      have hgmem : ∀ i, g i ∈ Part := fun i => hg ▸ Set.mem_range_self i
      refine ⟨disjointed g, ⟨fun i => ?_, fun i i' hii' => disjoint_disjointed g hii', ?_⟩, ?_⟩
      · rw [disjointed_eq_inter_compl]
        have hcl : IsClopen (⋂ jj ∈ Finset.range i, (g jj)ᶜ) :=
          isClopen_biInter_finset (fun k _ => (hA.isClopen (g k) (hgmem k)).compl)
        refine (hA.isClopen (g i) (hgmem i)).inter ?_
        convert hcl using 2 with jj
        simp [Finset.mem_range]
      · rw [iUnion_disjointed]
        ext y
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        obtain ⟨Q, hQ, hyQ⟩ : y ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; trivial
        rw [hg] at hQ
        obtain ⟨i, rfl⟩ := hQ
        exact ⟨i, hyQ⟩
      · intro i
        by_cases hex : ∃ k, k < i ∧ g k = g i
        · right
          rw [disjointed_eq_inter_compl]
          obtain ⟨k, hki, hgk⟩ := hex
          refine' Set.eq_empty_iff_forall_notMem.mpr (fun y ⟨hy1, hy2⟩ => _)
          exact (Set.mem_iInter₂.mp hy2 k hki) (hgk ▸ hy1)
        · left
          have heq : disjointed g i = g i := by
            rw [disjointed_eq_inter_compl]
            push_neg at hex
            refine' Set.inter_eq_left.mpr (fun y hy => Set.mem_iInter₂.mpr (fun k hki hygk => _))
            exact (Set.disjoint_left.mp (hA.pairwiseDisjoint (hgmem k) (hgmem i) (hex k hki)) hygk) hy
          rw [heq]; exact hgmem i
    have hsup : ⨆ i, CBRank (F.restrict (A i)).func = lam + ↑n + 2 := by
      rw [← hFrank, cbRank_eq_iSup_restrict F A hdu]
    by_contra hcon
    push_neg at hcon
    have hle : ∀ i, CBRank (F.restrict (A i)).func ≤ lam + 1 := by
      intro i
      rcases hAmem i with hAi | hAi
      · have hlt := hcon (A i) hAi
        have heq : lam + 2 = Order.succ (lam + 1) := by
          rw [← Ordinal.add_one_eq_succ, add_assoc, one_add_one_eq_two]
        rw [heq, Order.lt_succ_iff] at hlt
        exact hlt
      · rw [hAi]
        have hem : IsEmpty ↑(F.restrict (∅ : Set ↑F.domain)).domain :=
          Set.isEmpty_coe_sort.mpr (by ext y; simp [ScatFun.restrict])
        have hz := ContinuouslyReduces.rank_monotone (F.restrict ∅).hScat ScatFun.empty.hScat
          (ScatFun.reduces_of_isEmpty_domain hem)
        rw [ScatFun.empty_cbRank] at hz
        exact le_trans hz (zero_le _)
    have hsuple : ⨆ i, CBRank (F.restrict (A i)).func ≤ lam + 1 := ciSup_le hle
    rw [hsup] at hsuple
    have hcontra : lam + 1 < lam + ↑n + 2 := by
      rw [add_assoc]
      exact (add_lt_add_iff_left lam).mpr
        (lt_of_lt_of_le (by norm_num : (1 : Ordinal) < 2) le_add_self)
    exact absurd hsuple (not_le.mpr hcontra)
  obtain ⟨P, hPPart, hPrank⟩ := h_FPgeLam2
  -- `P` is not small (rank `≥ λ+2 > λ`), and `P` is disjoint from `U`.
  have hPnS : P ∉ S := fun hPS => absurd hPS.2 (not_lt.mpr
    (le_trans le_self_add hPrank))
  have hPUdisj : Disjoint P U := by
    rw [hU, Set.disjoint_sUnion_right]
    intro Q hQ
    exact hA.pairwiseDisjoint hPPart hQ.1 (fun h => hPnS (by rw [h]; exact hQ))
  -- **The gobbling.** Apply `gobblingLessThanLambda` to `G = F ↾ D` with `D = P ∪ U`, splitting
  -- `G` into `G ↾ P` (centered, `≥ pgl ℓ_λ`) and `G ↾ U` (`≤ ℓ_λ`). Restrict-of-restrict
  -- (`restrict_restrict_func_eq`) identifies `G ↾ P` with `F ↾ P` and `G ↾ Pᶜ` with `F ↾ U`.
  set D : Set ↑F.domain := P ∪ U with hD
  have hPsubD : P ⊆ D := by rw [hD]; exact Set.subset_union_left
  have hUsubD : U ⊆ D := by rw [hD]; exact Set.subset_union_right
  have hfuncP := ScatFun.restrict_restrict_func_eq F D P hPsubD
  have hfuncU := ScatFun.restrict_restrict_func_eq F D U hUsubD
  -- `Pinᶜ = Uin` as subsets of `G.domain` (since `D = P ⊔ U`).
  have hPinc : {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}ᶜ
      = {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ U} := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    have hmemD : (F.restrictEquiv D w : ↑F.domain) ∈ P ∪ U := by
      rw [← hD]; exact (F.restrictEquiv D w).2
    constructor
    · intro hw; exact hmemD.resolve_left hw
    · intro hw hwP; exact (Set.disjoint_left.mp hPUdisj hwP hw)
  -- Clopen of the copy of `P` inside `G.domain`.
  have hPincl : IsClopen {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P} :=
    IsClopen.preimage (hA.isClopen P hPPart)
      (continuous_subtype_val.comp (F.restrictEquiv D).continuous)
  have hF0cent : IsCentered ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}).func := by
    rw [hfuncP]; exact (IsCentered_comp_homeomorph _ _).mpr (hA.centered P hPPart)
  -- `pgl ℓ_λ ≤ F ↾ P` from `CB(F ↾ P) ≥ λ+2`.
  have hPrank' : Order.succ (Order.succ lam) ≤ CBRank (F.restrict P).func := by
    have heq : Order.succ (Order.succ lam) = lam + 2 := by
      rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc, one_add_one_eq_two]
    rw [heq]; exact hPrank
  have hsucc_le : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) (F.restrict P) :=
    consequencesGeneralStructure_succMaxFun_le lam hlam_lt hlim' (F.restrict P) hPrank'
  have hF0ge : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}) := by
    show ContinuouslyReduces _ _
    rw [hfuncP]; exact hsucc_le.comp_homeomorph_right _
  have hUmax : ScatFun.Reduces (F.restrict U) (ScatFun.maxFun lam hlam_lt) :=
    ScatFun.reduces_maxFun_of_rank_le (F.restrict U) lam hlam_lt h_FULtLam
  have hF1le : ScatFun.Reduces ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}ᶜ)
      (ScatFun.maxFun lam hlam_lt) := by
    show ContinuouslyReduces _ _
    rw [hPinc, hfuncU]; exact hUmax.comp_homeomorph_left _
  have hgob := gobblingLessThanLambda lam hlam_lt hlim (F.restrict D)
    {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}
    hPincl hF0cent hF0ge hF1le
  have hDcent : IsCentered (F.restrict D).func := hgob.1
  -- `G ↾ Pin ≡ F ↾ P`, hence `G = F ↾ D ≡ F ↾ P`.
  have hPinEquivP : ScatFun.Equiv ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ P}) (F.restrict P) := by
    refine ⟨?_, ?_⟩
    · show ContinuouslyReduces _ _
      rw [hfuncP]; exact (ContinuouslyReduces.refl (F.restrict P).func).comp_homeomorph_left _
    · show ContinuouslyReduces _ _
      rw [hfuncP]; exact (ContinuouslyReduces.refl (F.restrict P).func).comp_homeomorph_right _
  have hDequivP : ScatFun.Equiv (F.restrict D) (F.restrict P) := hgob.2.trans hPinEquivP
  -- **The merged partition.** Replace `P` and all small pieces `S` by the single piece `D = P∪U`.
  set B : Set (Set ↑F.domain) := insert P S with hB
  have hBsub : B ⊆ Part := by
    rw [hB]; exact Set.insert_subset hPPart hSsub
  set Part' : Set (Set ↑F.domain) := insert D (Part \ B) with hPart'
  -- `U` is clopen (it is `univ` minus the union of the remaining — open — pieces).
  have hUcl : IsClopen U := by
    refine ⟨?_, isOpen_sUnion (fun Q hQ => (hA.isClopen Q hQ.1).isOpen)⟩
    rw [← isOpen_compl_iff]
    have hUc : Uᶜ = ⋃₀ (Part \ S) := by
      apply Set.eq_of_subset_of_subset
      · intro y hy
        obtain ⟨Q, hQP, hyQ⟩ : y ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; trivial
        exact ⟨Q, ⟨hQP, fun hQS => hy ⟨Q, hQS, hyQ⟩⟩, hyQ⟩
      · rintro y ⟨Q, ⟨hQP, hQS⟩, hyQ⟩ hyU
        obtain ⟨Q', hQ'S, hyQ'⟩ := hyU
        exact hQS ((hA.pairwiseDisjoint.elim hQP hQ'S.1
          (Set.not_disjoint_iff.mpr ⟨y, hyQ, hyQ'⟩)) ▸ hQ'S)
    rw [hUc]
    exact isOpen_sUnion (fun Q hQ => (hA.isClopen Q hQ.1).isOpen)
  -- `D` disjoint from every surviving piece.
  have hDdisj : ∀ Y ∈ Part \ B, Disjoint D Y := by
    intro Y hY
    have hYP : Y ∈ Part := hY.1
    have hYneP : Y ≠ P := fun h => hY.2 (h ▸ Set.mem_insert P S)
    have hYnS : Y ∉ S := fun h => hY.2 (Set.mem_insert_of_mem P h)
    rw [hD]
    refine Disjoint.union_left (hA.pairwiseDisjoint hPPart hYP (Ne.symm hYneP)) ?_
    rw [hU, Set.disjoint_sUnion_left]
    intro Q hQ
    exact hA.pairwiseDisjoint hQ.1 hYP (fun h => hYnS (h ▸ hQ))
  -- Assemble `F.IsCPartition Part'`.
  have hcount' : Part'.Countable := (hA.countable.mono Set.diff_subset).insert D
  have hclopen' : ∀ X ∈ Part', IsClopen X := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hXmem
    · rw [hD]; exact (hA.isClopen P hPPart).union hUcl
    · exact hA.isClopen X hXmem.1
  have hdisj' : Part'.PairwiseDisjoint id := by
    rintro X hX Y hY hXY
    simp only [hPart', Set.mem_insert_iff] at hX hY
    show Disjoint X Y
    rcases hX with rfl | hXmem <;> rcases hY with rfl | hYmem
    · exact absurd rfl hXY
    · exact hDdisj Y hYmem
    · exact (hDdisj X hXmem).symm
    · exact hA.pairwiseDisjoint hXmem.1 hYmem.1 hXY
  have hcov' : ⋃₀ Part' = Set.univ := by
    have hBP : ⋃₀ B = D := by rw [hB, Set.sUnion_insert, ← hU, ← hD]
    have hsplit : ⋃₀ Part = ⋃₀ B ∪ ⋃₀ (Part \ B) := by
      rw [← Set.sUnion_union, Set.union_diff_cancel hBsub]
    rw [hPart', Set.sUnion_insert, ← hBP, ← hsplit, hA.sUnion_eq]
  have hcent' : ∀ X ∈ Part', IsCentered (F.restrict X).func := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hXmem
    · exact hDcent
    · exact hA.centered X hXmem.1
  -- **Every piece of `Part'` has rank `> λ`.** (Proved first so the no-lumps argument can use it.)
  have hrankgt : ∀ X ∈ Part', lam < CBRank (F.restrict X).func := by
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hXmem
    · -- `D ≡ F ↾ P`, so `CB(F ↾ D) = CB(F ↾ P) ≥ λ+2 > λ`.
      rw [cbRank_eq_of_equiv hDequivP]
      exact lt_of_lt_of_le (lt_add_of_pos_right lam (by norm_num : (0 : Ordinal) < 2)) hPrank
    · -- surviving piece: rank `≥ λ` (not small) and `≠ λ` (successor), so `> λ`.
      have hXP : X ∈ Part := hXmem.1
      have hXnS : X ∉ S := fun h => hXmem.2 (Set.mem_insert_of_mem P h)
      have hge : lam ≤ CBRank (F.restrict X).func := by
        by_contra hlt; push_neg at hlt; exact hXnS ⟨hXP, hlt⟩
      rcases lt_or_eq_of_le hge with h | h
      · exact h
      · obtain ⟨β, hβ⟩ := cbRank_piece_succ X hXP
        exact absurd ((hβ ▸ h).symm) (hlim.succ_ne β)
  have hA' : F.IsCPartition Part' := ⟨hcount', hclopen', hdisj', hcov', hcent'⟩
  refine ⟨Part', hA', ?_, hrankgt⟩
  -- **No lumps.** A `Part'`-lump `(g, y)` records that its piece `hA'.piece g y` fails to be
  -- `𝒲`-regular at `y`; it therefore suffices to prove that piece *is* `𝒲`-regular at `y`.
  --
  -- Proof strategy (reduces to two standalone analytic facts about `ω`-gluings / centered
  -- pieces, developed and then removed above; see git history for the full skeleton):
  -- if the block is empty the piece has empty domain (regular); otherwise its rank is `> λ`
  -- (`hrankgt`), so `(g,y)` is not an `hA`-lump (by `hlumps`), giving regularity of the
  -- corresponding `hA`-piece `F.restrict (⋃₀ hA.blockPieces g y)`; the `Part'`-piece differs
  -- only by replacing `P` with the gobbled superset `D = P ∪ U` (equivalent, same cocenter by
  -- `cocenter_restrict_eq_of_subset_equiv`), and `𝒲`-regularity is preserved under swapping a
  -- piece for such a centered superset.
  intro g y hlump
  apply hlump.2.2
  -- `V` = the union of the `hA`-block for `(g,y)`.
  set V : Set ↑F.domain := ⋃₀ hA.blockPieces g y with hVdef
  have hgcent : IsCentered g.func := hlump.2.1
  have hgbig : lam < CBRank g.func := lump_cbRank_gt hA' hrankgt hlump
  have hne : (hA.blockPieces g y).Nonempty :=
    gobble_blockPieces_hA_nonempty hA P U D S B hS hU hD hB hPart' hPPart hPsubD hDcent
      hDequivP hA' hgbig hlump
  have hycc : y ∈ hA.cocenterSet :=
    gobble_cocenterSet_mem hA hA' P D hPPart hPsubD hDcent hDequivP
      (by rw [hPart']; exact Set.insert_subset_insert Set.diff_subset) hlump.1
  have hVreg : IsOmegaRegularAt (F.restrict V) y :=
    isOmegaRegularAt_blockPieces_of_not_lump hA hlumps hgcent hycc hgbig
  have hVrank : CBRank (F.restrict V).func = CBRank g.func :=
    cbRank_blockPieces_sUnion hA g y hne
  have hVcl : IsClopen V := blockPieces_sUnion_isClopen hA g y
  have hVUdisj : Disjoint V U := blockPieces_disjoint_lowRank hA hgbig U hU
  -- **The `hA'`-block union is `V` (if `P ∉` block) or `V ∪ U` (if `P ∈` block, `P` merged
  -- into `D = P ∪ U`).**
  have hbp := gobble_blockPieces_sUnion_eq hA P U D S B hS hU hD hB hPart' hPPart hPsubD
    hDcent hDequivP hA' hgbig (g := g) (y := y)
  by_cases hPblock : P ∈ hA.blockPieces g y
  · -- **`P ∈` block ⟹ piece `= F ↾ (V ∪ U)`; adjoin the centered `D = P ∪ U`.**
    obtain ⟨hPmemP, hPeqg, hPcocy⟩ := hPblock
    have hpiece_eq : hA'.piece g y = F.restrict (V ∪ U) := by
      rw [ScatFun.IsCPartition.piece, hbp.1 ⟨hPmemP, hPeqg, hPcocy⟩, hVdef]
    rw [hpiece_eq]
    have hPV : P ⊆ V := hVdef ▸ Set.subset_sUnion_of_mem ⟨hPmemP, hPeqg, hPcocy⟩
    have hDcoc : cocenter (F.restrict D).func hDcent = y := by
      rw [cocenter_restrict_eq_of_subset_equiv F P D hPsubD (hA.centered P hPmemP) hDcent hDequivP]
      exact hPcocy
    have hDrank : CBRank (F.restrict D).func = CBRank (F.restrict V).func := by
      rw [cbRank_eq_of_equiv hDequivP, cbRank_eq_of_equiv hPeqg, hVrank]
    have hVUrank : CBRank (F.restrict (V ∪ U)).func = CBRank (F.restrict V).func := by
      refine le_antisymm ?_ (ContinuouslyReduces.rank_monotone (F.restrict V).hScat
        (F.restrict (V ∪ U)).hScat (restrict_reduces_of_subset F Set.subset_union_left))
      exact ScatFun.cbRank_restrict_union_le F V U hVcl hUcl hVUdisj (CBRank (F.restrict V).func)
        le_rfl (h_FULtLam.trans (le_of_lt (hVrank ▸ hgbig)))
    have hVbig : lam < CBRank (F.restrict V).func := hVrank ▸ hgbig
    exact isOmegaRegularAt_swap_centered lam hlim F V P U D y hD hPV hVcl hUcl
      (hA.isClopen P hPmemP) hVUdisj hDcent hDcoc hVbig hDrank hVUrank hVreg
  · -- **`P ∉` block ⟹ piece `= F ↾ V`, already `𝒲`-regular.**
    have hpiece_eq : hA'.piece g y = F.restrict V := by
      rw [ScatFun.IsCPartition.piece, hbp.2 hPblock, hVdef]
    rw [hpiece_eq]; exact hVreg

/-- **Proposition `ExistenceFinePartitions`** (`6_double_successor_memo.tex:108-124`). Let
`α = λ+n+2` with `λ < ω₁` limit and `n : ℕ`, and assume `FG(<α)`. Then every `F : ScatFun`
with `CBRank F.func = α` admits a `c`-partition that is fine relative to `λ`.

## Provided solution (`6_double_successor_memo.tex:112-124`)

Build a sequence `(𝒫_i)_{i ≤ n+2}` of `c`-partitions of `F`, with every `𝒫_i`-lump of rank
`≤ λ+n+2-i`, starting from an arbitrary `c`-partition `𝒫_0` (`FGconsequences`). At each step,
enumerate the (countably many) rank-`(λ+n+2-i)` lumps of `𝒫_i` and dissolve them one at a
time via `refiningBy1`, taking the "limit inferior" of the resulting sequence of partitions
to get `𝒫_{i+1}`; `refiningBy1`'s piece-survival clause `𝒫 \ 𝒫_{(g,y)} ⊆ 𝒫'` is exactly what
makes this limit inferior well-behaved. After `n+2` steps, every lump of `𝒫_{n+2}` has rank
`< λ`.

Finally, since `CB(F) ≥ λ+2`, `consequencesGeneralStructure_succMaxFun_le` gives
`pgl ℓ_λ ≤ F`, hence (`Centerinvariance`, item 3, `centerInvariance_cover`) `pgl ℓ_λ ≤
F.restrict P` for some `P ∈ 𝒫_{n+2}`. Let `R = ⋃₀ {Q ∈ 𝒫_{n+2} | F.restrict Q ≤ ℓ_λ}`; then
`gobblingLessThanLambda` (applied to `U = P ∪ R`) shows `F.restrict (P ∪ R)` is centered and
`≡ F.restrict P`. Replacing `P` and every piece of `R` by their union yields the desired fine
partition.

## Formalization notes

* The "limit inferior of a sequence of partitions" is not yet formalized as reusable
  machinery; assembling it is the main missing piece of this induction.
* `FG(<α)` is threaded exactly as in `refiningBy1`.
* This proposition depends on both `refiningBy1` and `gobblingLessThanLambda`, each of which
  still bottoms out in open leaves; the three results together are recorded as the supporting
  lemmas for this chapter's main induction (`ScatFun.levels_finitely_generated`'s remaining
  successor-of-successor gap, `LevelsFinitelyGenerated/Induction.lean`). -/
theorem existenceFinePartitions
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (hlim : Order.IsSuccLimit lam) (n : ℕ)
    (hα_lt : lam + (n : Ordinal.{0}) + 2 < omega1)
    (hFG : ScatFun.FGBelow (lam + (n : Ordinal.{0}) + 2))
    (F : ScatFun) (hFrank : CBRank F.func = lam + (n : Ordinal.{0}) + 2) :
    ∃ (Part : Set (Set ↑F.domain)) (hA : F.IsCPartition Part), hA.IsFine lam := by
  -- `𝒫₀` from `FGconsequences`: `F`'s own rank is `λ+n+2`, so `FG(<λ+n+2)` gives it centered
  -- cylinder witnesses (exactly as in `exists_cPartition_of_FGBelow`), hence a `c`-partition
  -- exists.
  obtain ⟨P0, hP0⟩ := exists_cPartition_of_centeredCylinderWitness F
    ((hFG.mono hFrank.le).centeredCylinderWitness (CBRank_lt_omega1 F.hScat) rfl)
  -- Dissolve every lump of rank `≥ λ`, then gobble the small (`≤ ℓ_λ`) pieces.
  obtain ⟨P1, hP1, hlumps⟩ :=
    existenceFinePartitions_dissolveAll lam hlam_lt hlim n hα_lt hFG F hFrank hP0
  exact existenceFinePartitions_gobble lam hlam_lt hlim n hα_lt hFG F hFrank hP1 hlumps

/-- **`ExistenceFinePartitions`, `λ = 0` (finite `α`) variant.**  For `α = n+2` finite
(`lam = 0`), assuming `FG(<n+2)`, every `F : ScatFun` with `CBRank F.func = n+2` admits a
`c`-partition fine relative to `0` (every piece has positive rank and there are no lumps).

The memoir states `ExistenceFinePartitions` for `α = λ+n+2` with `λ` *limit*; this is the
companion `λ = 0` case flagged in `DoubleSuccessor.lean`'s dependency checklist, needed by the
capstone `Generators_doubleSuccessor_finitely_generates` for finite ranks.  Gobbling is
vacuous here (there are no rank-`< λ = 0` pieces to absorb). -/
theorem existenceFinePartitions_zero (n : ℕ)
    (hα_lt : (n : Ordinal.{0}) + 2 < omega1)
    (hFG : ScatFun.FGBelow ((n : Ordinal.{0}) + 2))
    (F : ScatFun) (hFrank : CBRank F.func = (n : Ordinal.{0}) + 2) :
    ∃ (Part : Set (Set ↑F.domain)) (hA : F.IsCPartition Part), hA.IsFine 0 := by
  -- Initial `c`-partition `𝒫₀` from `FGconsequences`.
  obtain ⟨P0, hP0⟩ := exists_cPartition_of_centeredCylinderWitness F
    ((hFG.mono hFrank.le).centeredCylinderWitness (CBRank_lt_omega1 F.hScat) rfl)
  -- Dissolve all lumps down to rank `< 0` (i.e. no lumps at all); `dissolveDown` does not
  -- require `lam` to be a limit, so it applies verbatim with `lam = 0`.
  obtain ⟨Part, hA, hlumps⟩ := dissolveDown ((n : Ordinal.{0}) + 2) hα_lt hFG F hFrank 0 (n + 2)
    (le_of_eq (by push_cast; rw [zero_add])) hP0
    (fun g y hg => by
      rw [zero_add]; push_cast
      exact (lumpRank_le_cbRank hP0 hg).trans hFrank.le)
  refine ⟨Part, hA, fun g y hg => ?_, fun P hP => ?_⟩
  · -- No lumps: a lump would have `lumpRank < 0`, impossible.
    exact absurd (hlumps g y hg) not_lt_bot
  · -- Every piece is centered scattered simple, hence of successor CB-rank `> 0`.
    obtain ⟨β, hne, hempty, -⟩ :=
      scatteredCentered_isSimple (F.restrict P).func (F.restrict P).hScat (hA.centered P hP)
    rw [cbRank_eq_succ_of_simple_witness (F.restrict P).func (F.restrict P).hScat β hne hempty]
    exact Ordinal.succ_pos β

/-- **`ExistenceFinePartitions`, uniform form.**  For every `α < ω₁` (limit part or not),
assuming `FG(<α+2)`, every `F : ScatFun` with `CBRank F.func = α+2` admits a `c`-partition
fine relative to `α.limitPart`.  Dispatches on whether `α.limitPart` is a nonzero limit
(`existenceFinePartitions`) or `0` (`existenceFinePartitions_zero`). -/
theorem existenceFinePartitions_all (α : Ordinal.{0}) (hα_lt : α + 1 + 1 < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1) :
    ∃ (Part : Set (Set ↑F.domain)) (hA : F.IsCPartition Part), hA.IsFine α.limitPart := by
  have key : ∀ x : Ordinal.{0}, x + 1 + 1 = x + 2 := fun x => by rw [add_assoc]; norm_num
  have hrank2 : α + 1 + 1 = α.limitPart + (α.natPart : Ordinal.{0}) + 2 := by
    rw [key α]; conv_lhs => rw [Ordinal.eq_limitPart_add_natPart α]
  have hlam_le : α.limitPart ≤ α := by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  have hlam_lt : α.limitPart < omega1 :=
    lt_of_le_of_lt hlam_le (lt_of_le_of_lt (le_trans (le_self_add (a := α) (b := 1))
      (le_self_add (a := α + 1) (b := 1))) hα_lt)
  rcases Ordinal.limitPart_isLimit_or_zero α with hlim | hz
  · have hlt2 : α.limitPart + (α.natPart : Ordinal.{0}) + 2 < omega1 := hrank2 ▸ hα_lt
    have hFG2 : ScatFun.FGBelow (α.limitPart + (α.natPart : Ordinal.{0}) + 2) := hrank2 ▸ hFG
    have hFrank2 : CBRank F.func = α.limitPart + (α.natPart : Ordinal.{0}) + 2 := hrank2 ▸ hFrank
    exact existenceFinePartitions α.limitPart hlam_lt hlim α.natPart hlt2 hFG2 F hFrank2
  · have hz2 : α + 1 + 1 = (α.natPart : Ordinal.{0}) + 2 := by rw [hrank2, hz, zero_add]
    have hlt2 : (α.natPart : Ordinal.{0}) + 2 < omega1 := hz2 ▸ hα_lt
    have hFG2 : ScatFun.FGBelow ((α.natPart : Ordinal.{0}) + 2) := hz2 ▸ hFG
    have hFrank2 : CBRank F.func = (α.natPart : Ordinal.{0}) + 2 := hz2 ▸ hFrank
    obtain ⟨Part, hA, hfine⟩ := existenceFinePartitions_zero α.natPart hlt2 hFG2 F hFrank2
    exact ⟨Part, hA, hz ▸ hfine⟩

end
