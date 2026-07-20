import WqoContinuousFunctions.ScatFun.FiniteGluing
import WqoContinuousFunctions.ScatFun.Generators.Defs
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LevelLTTwoBQO
import WqoContinuousFunctions.CenteredFunctions.LocallyCentered.Theorem
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.Shared

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# `FG(<α)` — a name for the finite-generation-below-`α` hypothesis, and its consequences

`FG(<α)` (memoir notation) is not itself a reusable named hypothesis anywhere in this
development: every consumer re-spells it inline, matching the shape of the induction
hypothesis `ih` inside `ScatFun.levels_finitely_generated`
(`ScatFun/LevelsFinitelyGenerated/Induction.lean`). This file gives it a name, so later
files (starting with the double-successor chapter, `DoubleSuccessor/Fine.lean`)
don't have to keep re-spelling the triple quantifier.

Deliberately **not** used inside `Induction.lean` itself, which must not be imported by
lower files (see that file's own module doc) — `ScatFun.FGBelow` is declared `abbrev`
precisely so it stays transparent and unifies against `ih`'s literal type with no
`unfold`/`show` needed, regardless of whether `Induction.lean` spells it out or not.

The memoir also states general consequences of `FG(<α)` as Proposition `FGconsequences`
(`5_precise_struct_memo.tex:519-540`, 5 items). Every consumer of `FGBelow` is likely to need
at least one of these, so already-established ones are collected here too, re-derived from
existing lemmas rather than reproved. So far, item 4 (local centeredness), in
three forms of increasing strength:
* `ScatFun.FGBelow.isLocallyCentered` — plain `IsLocallyCentered`.
* `ScatFun.FGBelow.centeredCylinderWitness` — a genuine centered *prefix cylinder* around
  every point, not just some centered neighbourhood; needed because `IsLocallyCentered` alone
  is too weak to build a genuine disjoint union of centered pieces (centeredness is not
  restriction-closed; see the note above `locally_implies_disjointUnion_nat` in
  `CenteredFunctions/SimpleSuccessor/Shared.lean`).
* `ScatFun.FGBelow.disjointUnionOfCentered` — the actual disjoint union of centered pieces
  (`ScatFun.IsDisjointUnion`), via the standalone Lindelöf step
  `exists_countable_clopen_centered_cover` (also in this file: it depends only on
  `ScatFun.cyl`/`IsCentered`, not on `FGBelow`, and is reused by `Fine.lean` independently of
  it). This is the fact `Fine.lean` cites informally as "`f` admits a `c`-partition by
  `FGconsequences`"; the Lindelöf step itself is now fully proved, via the laminar
  cylinder-selection argument `laminar_cover_disjoint_selection` (see its docstring).
Items 1–3 and 5 are not yet re-exported here (either not needed yet, or — item 3, full BQO
rather than 2-BQO — not actually available anywhere in this development yet); add them here
if/when a later file needs them, rather than routing through this file speculatively.
-/

/-- **`FG(<α)`**: every `ScatFun` of `CB`-rank `β < α` is a finite gluing of
`Generators β`. `abbrev`, not `def`, so it stays definitionally transparent (see the
module doc above). -/
abbrev ScatFun.FGBelow (α : Ordinal.{0}) : Prop :=
  ∀ β < α, ∀ G : ScatFun, CBRank G.func = β → G ∈ ScatFun.FinGl (ScatFun.Generators β).toFinFun

/-- **`FGconsequences`, item 4** (`5_precise_struct_memo.tex:527`): `FG(<α)` implies every
function of `CB`-rank `α` is locally centered. Composed from two already-proved pieces:
`FG(<α)` gives 2-BQO of `LevelLT α` (`ScatFun.LevelLT.isTwoBQO_of_FG_below`), and 2-BQO of
`LevelLT α` gives local centeredness at `α` (Theorem 4.8 `LocalCenterednessFromBQO`,
`localCenterednessFromTwoBQO_scatFun`). This is the fact `Fine.lean` cites informally as
"`f` admits a `c`-partition by `FGconsequences`" (local centeredness + a Lindelöf-style
countable-subcover argument, not itself formalized yet, turns local centeredness into a
genuine `c`-partition). -/
theorem ScatFun.FGBelow.isLocallyCentered {α : Ordinal.{0}} (hα : α < omega1)
    (hFG : ScatFun.FGBelow α) {F : ScatFun} (hFrank : CBRank F.func = α) :
    IsLocallyCentered F.func :=
  localCenterednessFromTwoBQO_scatFun α hα (ScatFun.LevelLT.isTwoBQO_of_FG_below hFG) F hFrank

/-- **`FGconsequences`, item 4, cylinder-witness form.** `FG(<α)` gives every function of
`CB`-rank `α` a genuine *prefix cylinder* around each point of its domain on which it is
centered (`scatFun_centered_cylinder_witness`), not merely some unspecified centered
neighbourhood (`isLocallyCentered` above). This is the form `exists_countable_clopen_centered_cover`
below actually needs: `IsLocallyCentered` alone cannot be turned into a genuine disjoint union
of centered pieces, since centeredness is not preserved under restriction to an arbitrary
clopen subset (see the note above `locally_implies_disjointUnion_nat`,
`CenteredFunctions/SimpleSuccessor/Shared.lean`), whereas prefix cylinders are laminar (nested
or disjoint), which is what makes a genuine disjoint selection of them possible. Same
derivation as `isLocallyCentered`, feeding the stronger cylinder-witness theorem instead. -/
theorem ScatFun.FGBelow.centeredCylinderWitness {α : Ordinal.{0}} (hα : α < omega1)
    (hFG : ScatFun.FGBelow α) {F : ScatFun} (hFrank : CBRank F.func = α) :
    ∀ x : ↑F.domain, ∃ n : ℕ,
      IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain)) :=
  scatFun_centered_cylinder_witness α hα (ScatFun.LevelLT.isTwoBQO_of_FG_below hFG) F hFrank

/-- Centeredness of the flat composition `F.func ∘ Subtype.val` on a subset `A` transfers
to centeredness of the packaged restriction `(F.restrict A).func`, since the latter is the
former precomposed with the realization homeomorphism `F.restrictEquiv A`. -/
theorem ScatFun.isCentered_restrict_of_comp (F : ScatFun) (A : Set ↑F.domain)
    (h : IsCentered (F.func ∘ (Subtype.val : ↥A → ↑F.domain))) :
    IsCentered (F.restrict A).func :=
  isCentered_of_homeomorph (F.func ∘ (Subtype.val : ↥A → ↑F.domain)) (F.restrict A).func
    (F.restrictEquiv A) (fun _ => rfl) h

/-
**Prefix cylinders are laminar.** If a depth-`m` cylinder around `x` and a deeper
(depth-`n`, `m ≤ n`) cylinder around `y` intersect, then the deeper one is contained in the
shallower one. Any common point agrees with `x` on the first `m` coordinates and with `y` on
the first `n ≥ m`, so `x` and `y` agree on the first `m`, hence every point of the depth-`n`
cylinder agrees with `x` on the first `m`.
-/
theorem ScatFun.cyl_laminar (G : ScatFun) (x y : ↑G.domain) {m n : ℕ} (hmn : m ≤ n)
    (hne : (G.cyl x m ∩ G.cyl y n).Nonempty) : G.cyl y n ⊆ G.cyl x m := by
  obtain ⟨ z, hz ⟩ := hne;
  intro a ha; simp_all +decide [ ScatFun.cyl, nbhd' ] ;
  grind

/-
**Disjoint selection from a countable laminar cover.** Given a countable family `C` of
sets equipped with a `depth` function `d` such that whenever two members intersect the one of
smaller depth contains the other (`hlam`), and the family covers everything (`hcov`), one can
select a subfamily `P` — each `P n` either the original `C n` or empty — that is pairwise
disjoint and still covers everything. Keep, for each set, the shallowest (largest) member
intersecting it (well-defined by laminarity), taking the least index among duplicates.

Proof sketch. Say `k` is *maximal* (`isMax k`) if every member intersecting `C k` is contained
in `C k`. Define `keep k := isMax k ∧ ∀ j < k, ¬ isMax j ∨ Disjoint (C j) (C k)` and
`P k := if keep k then C k else ∅`.
* *Disjoint.* Two kept `i ≠ j` that intersect are both maximal and intersecting, hence
  `C i = C j`; the `keep` clause at the larger index then fails. Contradiction.
* *Maximality of the shallowest at a point.* For `x`, pick `k₀` minimizing `d` over
  `{k | x ∈ C k}` (a nonempty set of naturals). Any `j` with `C j ∩ C k₀ ≠ ∅`: if `d j ≤ d k₀`
  then `C k₀ ⊆ C j` by `hlam`, so `x ∈ C j`, forcing `d j = d k₀` by minimality and then
  `C j ⊆ C k₀`; if `d k₀ < d j` then `C j ⊆ C k₀` directly by `hlam`. So `isMax k₀`.
* *Cover.* All maximals containing `x` share the same set `C k₀` (pairwise intersecting at
  `x`, so equal); the least such index `l` satisfies `keep l`, and `x ∈ C l = P l`.
-/
theorem laminar_cover_disjoint_selection {X : Type*} (C : ℕ → Set X) (d : ℕ → ℕ)
    (hlam : ∀ i j, d i ≤ d j → (C i ∩ C j).Nonempty → C j ⊆ C i)
    (hcov : ⋃ i, C i = Set.univ) :
    ∃ P : ℕ → Set X,
      (∀ n, P n = C n ∨ P n = ∅) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ n, P n = Set.univ) := by
  by_contra! h_contra;
  -- Define `isMax k := ∀ j, (C k ∩ C j).Nonempty → C j ⊆ C k`, `keep k := isMax k ∧ ∀ j < k, ¬ isMax j ∨ Disjoint (C j) (C k)`, and `P k := if keep k then C k else ∅`.
  set isMax : ℕ → Prop := fun k => ∀ j, (C k ∩ C j).Nonempty → C j ⊆ C k
  set keep : ℕ → Prop := fun k => isMax k ∧ ∀ j < k, ¬ isMax j ∨ Disjoint (C j) (C k)
  set P : ℕ → Set X := fun k => if keep k then C k else ∅;
  refine h_contra P ?_ ?_ ?_;
  · grind;
  · grind +splitImp;
  · simp_all +decide [ Set.ext_iff ];
    intro x
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, x ∈ C k₀ ∧ ∀ k, x ∈ C k → d k₀ ≤ d k := by
      have h_min : ∃ m ∈ Set.image d {k | x ∈ C k}, ∀ n ∈ Set.image d {k | x ∈ C k}, m ≤ n := by
        exact ⟨ Nat.find <| Set.image_nonempty.2 <| hcov x, Nat.find_spec <| Set.image_nonempty.2 <| hcov x, fun n hn => Nat.find_min' _ hn ⟩;
      obtain ⟨ m, ⟨ k₀, hk₀, rfl ⟩, hm ⟩ := h_min; exact ⟨ k₀, hk₀, fun k hk => hm _ ⟨ k, hk, rfl ⟩ ⟩ ;
    -- Show that `k₀` is maximal.
    have hk₀_max : isMax k₀ := by
      intro j hj;
      obtain ⟨ y, hy ⟩ := hj;
      by_cases h : d k₀ ≤ d j <;> simp_all +decide [ Set.Nonempty ];
      · exact hlam _ _ h _ hy.1 hy.2;
      · linarith [ hk₀.2 j ( by
          exact hlam _ _ h.le _ hy.2 hy.1 |> fun h => h hk₀.1 ) ];
    -- Let `l` be the least index such that `isMax l` and `x ∈ C l`.
    obtain ⟨l, hl⟩ : ∃ l, isMax l ∧ x ∈ C l ∧ ∀ j < l, ¬ isMax j ∨ ¬ x ∈ C j := by
      exact ⟨ Nat.find ( ⟨ k₀, hk₀_max, hk₀.1 ⟩ : ∃ k, isMax k ∧ x ∈ C k ), Nat.find_spec ( ⟨ k₀, hk₀_max, hk₀.1 ⟩ : ∃ k, isMax k ∧ x ∈ C k ) |>.1, Nat.find_spec ( ⟨ k₀, hk₀_max, hk₀.1 ⟩ : ∃ k, isMax k ∧ x ∈ C k ) |>.2, fun j hj => by contrapose! hj; aesop ⟩;
    grind [disjoint_or_nonempty_inter]

/-
**Countable `ℕ`-indexed centered cylinder subcover.** From the pointwise centered-cylinder
witnesses, use second-countability (Lindelöf) of the domain to extract a countable subfamily,
indexed by `ℕ`, of centered prefix cylinders that still covers the (nonempty) domain.
-/
theorem exists_nat_indexed_cyl_subcover (F : ScatFun) [Nonempty ↑F.domain]
    (hcyl : ∀ x : ↑F.domain, ∃ n : ℕ,
      IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain))) :
    ∃ (idx : ℕ → ↑F.domain) (m : ℕ → ℕ),
      (⋃ k, F.cyl (idx k) (m k)) = Set.univ ∧
      (∀ k, IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl (idx k) (m k)) → ↑F.domain))) := by
  choose n hn using hcyl;
  -- Since `F.domain` is second-countable (Baire is second-countable, hence Lindelöf),
  -- we can apply the definition of Lindelöf to the open cover `{F.cyl x (n x) | x : F.domain}`.
  obtain ⟨T, hT_countable, hT_cover⟩ : ∃ T : Set ↑F.domain, T.Countable ∧ ⋃ x ∈ T, F.cyl x (n x) = Set.univ := by
    convert TopologicalSpace.isOpen_iUnion_countable _ _;
    all_goals try infer_instance;
    · exact Set.ext fun x => ⟨ fun hx => Set.mem_iUnion.2 ⟨ x, ScatFun.mem_cyl _ _ _ ⟩, fun hx => Set.mem_univ x ⟩;
    · exact fun x => F.cyl_isOpen x _;
  have := hT_countable.exists_eq_range;
  by_cases hT_nonempty : T.Nonempty;
  · obtain ⟨ f, rfl ⟩ := this hT_nonempty; exact ⟨ f, fun k => n ( f k ), by simpa using hT_cover, fun k => hn _ ⟩ ;
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hT_nonempty ]

/-- **Lindelöf extraction for centeredness, via prefix cylinders** (first half of the
"Lindelöf" step of `FGconsequences`, `5_precise_struct_memo.tex:527`). Cover the
(second-countable, hence Lindelöf) domain by the centered prefix cylinders
`scatFun_centered_cylinder_witness` provides (one `F.cyl x n` per point `x`), extract a
countable subcover.

**Why this needs cylinders, not `IsLocallyCentered`.** The naive approach — cover by
arbitrary centered clopen neighbourhoods (`IsLocallyCentered`), extract a countable subcover,
then *disjointify* it (`disjointed`), as `locally_reduces_to_maxfun_implies_reduces`
(`PointedGluing/ClopenPartitionReduces.lean:15`) does for "reduces to `MaxFun`" — does **not**
work here: that technique relies on the target property being restriction-closed (any clopen
*subset* of a witness neighbourhood still has the property), which holds for
`ContinuouslyReduces` but explicitly fails for `IsCentered` (a clopen subset of a centered
neighbourhood need not contain a center point at all). See the note above
`locally_implies_disjointUnion_nat` (`CenteredFunctions/SimpleSuccessor/Shared.lean:894`).

Prefix cylinders fix this because they are *laminar*: any two are nested or disjoint, never
partially overlapping. A genuine disjoint **selection** from a countable cylinder subcover
(e.g. keeping, for each point, the shallowest listed cylinder covering it — well-defined by
laminarity) reuses the original cylinders verbatim rather than cutting pieces out of them, so
centeredness transfers with no restriction step at all. This selection lemma is now formalized
as the standalone `laminar_cover_disjoint_selection` ("countable laminar cover ⇒ disjoint
sub-selection covering everything"), and the countable extraction as
`exists_nat_indexed_cyl_subcover` (Lindelöf). The
target `ℕ`-indexed (not set-of-pieces) shape matches what
`DoubleSuccessor/Fine.lean`'s `isCPartition_of_indexed_cover` expects; the
unguarded, `IsDisjointUnion`-bundled form is `ScatFun.FGBelow.disjointUnionOfCentered` below. -/
theorem exists_countable_clopen_centered_cover
    (F : ScatFun)
    (hcyl : ∀ x : ↑F.domain, ∃ n : ℕ,
      IsCentered (F.func ∘ (Subtype.val : ↥(F.cyl x n) → ↑F.domain))) :
    ∃ P : ℕ → Set ↑F.domain,
      (∀ n, IsClopen (P n)) ∧ (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (⋃ n, P n = Set.univ) ∧
        (∀ n, (P n).Nonempty → IsCentered (F.restrict (P n)).func) := by
  rcases isEmpty_or_nonempty ↑F.domain with hemp | hne
  · refine ⟨fun _ => ∅, fun _ => isClopen_empty, fun i j _ => by simp,
      ?_, fun n h => (hemp.false h.some).elim⟩
    rw [Set.eq_univ_iff_forall]; intro x; exact (hemp.false x).elim
  · obtain ⟨idx, m, hcov, hcent⟩ := exists_nat_indexed_cyl_subcover F hcyl
    obtain ⟨P, hPor, hPdisj, hPcov⟩ :=
      laminar_cover_disjoint_selection (fun k => F.cyl (idx k) (m k)) m
        (fun i j hij hnex => F.cyl_laminar (idx i) (idx j) hij hnex) hcov
    refine ⟨P, fun n => ?_, hPdisj, hPcov, fun n hnne => ?_⟩
    · rcases hPor n with h | h
      · rw [h]; exact baire_nbhd'_isClopen _ _ _
      · rw [h]; exact isClopen_empty
    · rcases hPor n with h | h
      · rw [h]; exact F.isCentered_restrict_of_comp _ (hcent n)
      · rw [h] at hnne; exact absurd hnne (by simp)

/-- **`FGconsequences`, item 4, disjoint-union form.** `FG(<α)` gives every function of
`CB`-rank `α` a genuine `ScatFun.IsDisjointUnion` decomposition into pieces that are centered
whenever nonempty. A thin repackaging of `exists_countable_clopen_centered_cover` (fed
`centeredCylinderWitness` above) — `ScatFun.IsDisjointUnion`'s three clauses are exactly its
first three conclusions — so it inherits the same open gap (the laminar cylinder-selection
argument) verbatim.

**Why the `Nonempty` guard is unavoidable.** `ScatFun.IsDisjointUnion` does not require blocks
nonempty, and `IsCentered` is vacuously false on an empty domain; any `F` needing only
finitely many centered pieces forces the `ℕ`-indexed family to pad with `∅` for the unused
indices. This is exactly why `DoubleSuccessor/Fine.lean`'s "Representation
choice" note (above `ScatFun.IsCPartition`) uses a *set* of pieces rather than an `ℕ`-indexed
family for the genuine `c`-partition — the guarded form here is the ℕ-indexed analogue,
usable precisely where the caller doesn't need a literal set of pieces. -/
theorem ScatFun.FGBelow.disjointUnionOfCentered {α : Ordinal.{0}} (hα : α < omega1)
    (hFG : ScatFun.FGBelow α) {F : ScatFun} (hFrank : CBRank F.func = α) :
    ∃ A : ℕ → Set ↑F.domain, F.IsDisjointUnion A ∧
      ∀ i, (A i).Nonempty → IsCentered (F.restrict (A i)).func := by
  obtain ⟨P, hcl, hdisj, hcov, hcent⟩ :=
    exists_countable_clopen_centered_cover F (hFG.centeredCylinderWitness hα hFrank)
  exact ⟨P, ⟨hcl, hdisj, hcov⟩, hcent⟩

/-- **Monotonicity of `FG(<α)`.** If `FG(<α)` holds and `β ≤ α`, then `FG(<β)` holds too:
`FGBelow` only quantifies over ranks below its bound, so shrinking the bound only drops
constraints. Lets a caller with `hFG : FGBelow α` and some `F` of rank `< α` (e.g. a piece
strictly smaller than the ambient level) get `FGBelow (CBRank F.func)` and apply
`isLocallyCentered` to `F` itself, e.g. in `exists_cPartition_of_FGBelow`
(`DoubleSuccessor/Fine.lean`). -/
theorem ScatFun.FGBelow.mono {α β : Ordinal.{0}} (hβα : β ≤ α) (h : ScatFun.FGBelow α) :
    ScatFun.FGBelow β :=
  fun γ hγβ G hG => h γ (hγβ.trans_le hβα) G hG