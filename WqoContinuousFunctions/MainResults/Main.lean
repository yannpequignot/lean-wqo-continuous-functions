import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.WellQuasiOrder
import WqoContinuousFunctions.ContinuousReducibility.Defs
import WqoContinuousFunctions.ContinuousReducibility.Universality
import WqoContinuousFunctions.ScatFun.FiniteGluing
import ZeroDimensionalSpaces.Basics
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.ContinuousReducibility.Scattered.NonScattered
import WqoContinuousFunctions.MainResults.ScatFunBQO
import WqoContinuousFunctions.MainResults.ScatFunRepresentation
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Formalization of main theorems

This file contains all the main theorems
with proofs by importing the relevant lemmas from the repo.

## Main theorem statements

* `MainTheorem1` — Continuous reducibility is a WQO on continuous functions from an
  analytic zero-dimensional space to a separable metrizable space.
* `MainTheorem2` — Continuous reducibility is a WQO on continuous functions from a
  separable metrizable zero-dimensional space to a countable metrizable space.
* `MainTheorem3` — Continuous reducibility is a WQO on scattered continuous functions
  from a zero-dimensional separable metrizable space to a metrizable space.
* `first_reduction_theorem` — A continuous function `f : X → Y` from a zero-dimensional
  separable metrizable space to a metrizable space, with either `X` Polish or `Y` countable,
  is one of three kinds: scattered, equivalent to `id_CantorRat` (the `ℚ`-model), or
  equivalent to `id_CantorSpace` (the `2^ℕ`-model).
-/


section WQO

/-!
## Well-Quasi-Orders

An *antichain* is a set of pairwise incomparable elements. A quasi-order is a
*well-quasi-order (WQO)* if it has no infinite antichains and no infinite strictly
descending chains. Equivalently (by Ramsey-like arguments), `(Q, ≤)` is WQO iff
for every infinite sequence `f: ℕ → Q` there exist `m < n` with `f(m) ≤ f(n)`.

Mathlib provides `WellQuasiOrdered` with the sequential characterization.

While proofs rely on `WellQuasiOrdered` and its strengthening `TwoBQO`,
for simplicity we rely on the sequential characterization in the statements
of the main theorems.

-/

-- `WellQuasiOrdered` is already in Mathlib for `r:α → α → Prop`:
-- `WellQuasiOrdered r ↔ ∀ f : ℕ → α, ∃ m n, m < n ∧ r (f m) (f n)`


end WQO


section FirstReductionTheorem

/-!
## Theorem 2.12 (`FirststepforBQOthm`) — First Reduction Theorem

This result is *informative* and *off the critical path* for the WQO program (Main
Theorem 3 does not depend on it): it explains how the general classification reduces to the
scattered case.

**Statement faithfulness.** The memoir (2_prelim_memo.tex, `FirststepforBQOthm`) states the
trichotomy `f ≡ id_ℚ`, `f ≡ id_𝒩`, or `f` scattered, for `f : X → Y` continuous with `X`
zero-dimensional separable metrizable and `Y` metrizable, under the standing hypothesis of
Main Theorem 1/2 (so either `X` is *analytic*, or `Y` is *countable*).  We make two faithful
adaptations that keep the proof entirely within results already formalized in this repo:

* We use the concrete canonical models `CantorRat` (≅ `ℚ`: countable metrizable perfect) and
  `CantorSpace = ℕ → Fin 2` (≅ `2^ℕ`) in place of `ℚ` and `ℕ → ℕ`.  In the non-scattered
  *uncountable* case the memoir invokes the Perfect Function Property (`uncountablerange`) to
  embed the full Baire space; here we instead embed the Cantor space, which is exactly what
  `nonscattered_embeds_idCantor` provides and which suffices for an *equivalence* once the
  Polish zero-dimensional domain is itself embedded into `CantorSpace`.  This avoids the
  Perfect Function Property entirely (it is not formalized).
* Accordingly the standing hypothesis becomes `PolishSpace X ∨ Countable Y` (Polish being the
  formalized stand-in for the memoir's analytic domains, cf. `MainTheorem1`).
-/

/-- **First Reduction Theorem (Theorem 2.12).** A continuous function `f : X → Y` from a
zero-dimensional separable metrizable space to a metrizable space, with either `X` Polish or
`Y` countable, is one of three kinds: scattered, equivalent to `id_CantorRat` (the `ℚ`-model),
or equivalent to `id_CantorSpace` (the `2^ℕ`-model).

Proof outline (see the module note and 2_prelim_memo.tex, `FirststepforBQOthm`):
* If `f` is scattered we are done.
* Otherwise `id_CantorRat ≤ f` by `nonscattered_embeds_idCantorRat`.
  - If `Y` is countable, then `f ≤ id_Y ≤ id_CantorRat` (`reduces_to_codomain_id`,
    `countable_metrizable_embeds_cantorRat`, `id_le_id_of_embedding`), giving `f ≡ id_CantorRat`.
  - Otherwise `X` is Polish, so `id_CantorSpace ≤ f` (`nonscattered_embeds_idCantor`) and
    `f ≤ id_CantorSpace` (the domain embeds into `CantorSpace` via
    `ZerodimMetrizableSep_hom_CantorSubspace`, exactly as in `MainTheorem1`), giving
    `f ≡ id_CantorSpace`. -/
theorem first_reduction_theorem
    {X Y : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [ZeroDimensionalSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : Continuous f)
    (hXY : PolishSpace X ∨ Countable Y) :
    ScatteredFun f ∨
    ContinuouslyEquiv f (@id CantorRat) ∨
    ContinuouslyEquiv f (@id CantorSpace) := by
  by_cases hsc : ScatteredFun f
  · exact Or.inl hsc
  · -- `f` is non-scattered.  First, `X` (hence `Y`) is nonempty: on an empty domain every
    -- function is vacuously scattered.
    have hXne : Nonempty X := by
      rcases isEmpty_or_nonempty X with hX | hX
      · exact absurd (fun S hS => (hX.false hS.some).elim) hsc
      · exact hX
    have : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
    -- `id_CantorRat ≤ f`: the non-scattered locus carries a `CantorRat`-embedding `σ` with
    -- `f ∘ σ` still an embedding.
    obtain ⟨σ, hσ, hfσ⟩ := nonscattered_embeds_idCantorRat hf hsc
    have h_idCR_le_f : ContinuouslyReduces (@id CantorRat) f :=
      id_reduces_of_embedding_pair hσ.continuous hfσ
    rcases hXY with hPolish | hYcount
    · -- `Y` may be uncountable, but `X` is Polish: conclude `f ≡ id_CantorSpace`.
      have := hPolish
      -- `id_CantorSpace ≤ f` via the Cantor-scheme embedding into the (complete) domain.
      obtain ⟨σ', hσ', hfσ'⟩ := nonscattered_embeds_idCantor hf hsc
      have h_idC_le_f : ContinuouslyReduces (@id CantorSpace) f :=
        id_reduces_of_embedding_pair hσ'.continuous hfσ'
      -- `f ≤ id_CantorSpace`: the domain embeds into `CantorSpace` (as in `MainTheorem1`).
      obtain ⟨A, ⟨φ⟩⟩ := ZerodimMetrizableSep_hom_CantorSubspace (X := X)
      have hemb : Topology.IsEmbedding (Subtype.val ∘ φ : X → CantorSpace) :=
        Topology.IsEmbedding.subtypeVal.comp φ.isEmbedding
      have h_f_le_idC : ContinuouslyReduces f (@id CantorSpace) :=
        reduces_to_id_of_domain_embedding hf hemb
      exact Or.inr (Or.inr ⟨h_f_le_idC, h_idC_le_f⟩)
    · -- `Y` is countable: conclude `f ≡ id_CantorRat`.
      have := hYcount
      -- `f ≤ id_Y ≤ id_CantorRat`, the second step since `Y` embeds into `CantorRat`.
      obtain ⟨ι, hι⟩ := countable_metrizable_embeds_cantorRat (X := Y)
      have h_f_le_idCR : ContinuouslyReduces f (@id CantorRat) :=
        (reduces_to_codomain_id hf).trans (id_le_id_of_embedding hι)
      exact Or.inr (Or.inl ⟨h_f_le_idCR, h_idCR_le_f⟩)

end FirstReductionTheorem


section MainTheorems

/-!
## Main Theorems

We state the three main theorems from the introduction.

### Notation

* A space is *Polish* if it is separable and completely metrizable. In Mathlib:
  `PolishSpace`.
* A space is *zero-dimensional* if it is Hausdorff and has a basis of clopen sets.
  This notion was absent from MathLib so we define it in this project as
  `ZeroDimensionalSpace` in `ZeroDimensionalSpaces.Basics`.
  -/

/-- **Main Theorem 3.** Continuous reducibility is a well-quasi-order on scattered
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space.
In fact we formalized the proof that it is 2-BQO:
The lemma main3_to_ScatFun reduces the general case to ScatFun
and ScatFun.Reduces.TwoBQO shows that ScatFun is 2-BQO.
In the memoir, we show it is BQO with the same proof.

It is proved before Main Theorems 1 and 2 because their proofs invoke it on the
(scattered) subsequence produced by the scattered/non-scattered dichotomy.
 -/
theorem MainTheorem3
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, ZeroDimensionalSpace (X n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n))
    (hsc : ∀ n, ScatteredFun (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces_range_based (f m) (f n) := by
  -- The conclusion uses the memoir's image-based reduction.  This is both faithful to the
  -- paper and convenient: an empty-codomain function image-reduces to *anything*, so the
  -- degenerate case is dispatched immediately, while the substantive case goes through the
  -- total-`τ` `ContinuouslyReduces` (built from the `ScatFun` WQO) and is translated back via
  -- `ContinuouslyReduces.to_range_based`.
  by_cases hEmpty : ∃ m, IsEmpty (Y m)
  · -- Some codomain is empty: `f m` image-reduces to `f (m+1)` for free.
    obtain ⟨m, hm⟩ := hEmpty
    have := hm
    exact ⟨m, m + 1, Nat.lt_succ_self m,
      ContinuouslyReduces_range_based.of_isEmpty_codomain⟩
  · -- All codomains nonempty: reduce each `f n` to a `ScatFun` and apply the `ScatFun` WQO.
    push_neg at hEmpty
    have hH : ∀ n, ∃ G : ScatFun, ContinuouslyEquiv (f n) G.func := fun n =>
      have := hEmpty n
      main3_to_ScatFun (hf n) (hsc n)
    choose H hequiv using hH
    obtain ⟨m, n, hmn, hred⟩ := ScatFun.Reduces.isWQO H
    -- Transfer: f m ≤ (H m).func ≤ (H n).func ≤ f n, then pass to the image-based variant.
    exact ⟨m, n, hmn, ((hequiv m).1.trans (hred.trans (hequiv n).2)).to_range_based⟩

/-- **Main Theorem 1.** Continuous reducibility is a well-quasi-order on continuous
functions from an analytic zero-dimensional space to a separable metrizable space.

Formally: for any sequence `fₙ : Xₙ → Yₙ` of continuous functions where each `Xₙ`
is Polish and zero-dimensional and each `Yₙ` is separable and metrizable, there
exist `m < n` such that `fₘ` continuously reduces to `fₙ` (in the memoir's image-based
variant `ContinuouslyReduces_range_based`).

The proof is the scattered/non-scattered dichotomy: if some `f n` (`n ≥ 1`) is
non-scattered it is a *top* (`f 0 ≤ id_Cantor ≤ f n`); otherwise `f (k+1)` is scattered
for all `k`, and `MainTheorem3` applies to that subsequence. -/
theorem MainTheorem1
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, PolishSpace (X n)] [∀ n, ZeroDimensionalSpace (X n)]
    [∀ n, SeparableSpace (Y n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces_range_based (f m) (f n) := by
  by_cases hns : ∃ n, 0 < n ∧ ¬ ScatteredFun (f n)
  · -- A non-scattered `f n` (`n ≥ 1`) is a top: `f 0 ≤ id_Cantor ≤ f n`.
    obtain ⟨n, hn, hnsn⟩ := hns
    refine ⟨0, n, hn, ?_⟩
    rcases isEmpty_or_nonempty (Y 0) with hY0 | hY0
    · -- Empty codomain: `f 0` image-reduces to anything.
      have := hY0
      exact ContinuouslyReduces_range_based.of_isEmpty_codomain
    · have := hY0
      -- `id_Cantor ≤ f n` from the embedding pair `(σ, f n ∘ σ)`.
      obtain ⟨σ, hσ, hfσ⟩ := nonscattered_embeds_idCantor (hf n) hnsn
      have h_below : ContinuouslyReduces (@id CantorSpace) (f n) :=
        id_reduces_of_embedding_pair hσ.continuous hfσ
      -- `f 0 ≤ id_Cantor`: the Polish, zero-dimensional domain `X 0` embeds in the Cantor space
      -- (`ZerodimMetrizableSep_hom_CantorSubspace`).  This is where Main Theorem 1's hypotheses on
      -- the *domain* are used; the memoir's analyticity is only needed for the more general
      -- (non-Polish) analytic domains, which do not embed in the Cantor space directly.
      obtain ⟨A, ⟨φ⟩⟩ := ZerodimMetrizableSep_hom_CantorSubspace (X := X 0)
      have hemb : Topology.IsEmbedding (Subtype.val ∘ φ : X 0 → CantorSpace) :=
        Topology.IsEmbedding.subtypeVal.comp φ.isEmbedding
      have h_univ : ContinuouslyReduces (f 0) (@id CantorSpace) :=
        reduces_to_id_of_domain_embedding (hf 0) hemb
      exact (h_univ.trans h_below).to_range_based
  · -- Otherwise `f (k+1)` is scattered for every `k`; apply Main Theorem 3 to that subsequence.
    push_neg at hns
    have hsc : ∀ k, ScatteredFun (f (k + 1)) := fun k => hns (k + 1) k.succ_pos
    obtain ⟨k, l, hkl, hred⟩ :=
      MainTheorem3 (fun k => X (k + 1)) (fun k => Y (k + 1)) (fun k => f (k + 1))
        (fun k => hf (k + 1)) hsc
    exact ⟨k + 1, l + 1, by omega, hred⟩

/-- **Main Theorem 2.** Continuous reducibility is a well-quasi-order on continuous
functions from a separable metrizable zero-dimensional space to a countable metrizable
space (stated in the memoir's image-based variant `ContinuouslyReduces_range_based`).

Same dichotomy as `MainTheorem1`, with `ℚ` in place of the Cantor space: a non-scattered
`f n` is a top (`f 0 ≤ id_ℚ ≤ f n`), otherwise `MainTheorem3` handles the scattered tail. -/
theorem MainTheorem2
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, ZeroDimensionalSpace (X n)]
    [∀ n, MetrizableSpace (Y n)] [∀ n, Countable (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces_range_based (f m) (f n) := by
  by_cases hns : ∃ n, 0 < n ∧ ¬ ScatteredFun (f n)
  · -- A non-scattered `f n` (`n ≥ 1`) is a top: `f 0 ≤ id_ℚ ≤ f n`.
    obtain ⟨n, hn, hnsn⟩ := hns
    refine ⟨0, n, hn, ?_⟩
    rcases isEmpty_or_nonempty (Y 0) with hY0 | hY0
    · -- Empty codomain: `f 0` image-reduces to anything.
      have := hY0
      exact ContinuouslyReduces_range_based.of_isEmpty_codomain
    · have := hY0
      have : Nonempty CantorRat := ⟨⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩⟩
      -- `id_CantorRat ≤ f n` from the embedding pair `(σ, f n ∘ σ)`.  Using `CantorRat` (not `ℚ`)
      -- keeps this Sierpiński-free (`nonscattered_embeds_idCantorRat` goes via the Cantor scheme).
      obtain ⟨σ, hσ, hfσ⟩ := nonscattered_embeds_idCantorRat (hf n) hnsn
      have h_below : ContinuouslyReduces (@id CantorRat) (f n) :=
        id_reduces_of_embedding_pair hσ.continuous hfσ
      -- `f 0 ≤ id_CantorRat`: `f 0 ≤ id_{Y 0}` (codomain identity) and the countable metrizable
      -- `Y 0` embeds in `CantorRat` (`countable_metrizable_embeds_cantorRat` — the one gap).
      obtain ⟨ι, hι⟩ := countable_metrizable_embeds_cantorRat (X := Y 0)
      have h_univ : ContinuouslyReduces (f 0) (@id CantorRat) :=
        (reduces_to_codomain_id (hf 0)).trans (id_le_id_of_embedding hι)
      exact (h_univ.trans h_below).to_range_based
  · -- Otherwise `f (k+1)` is scattered for every `k`; apply Main Theorem 3 to that subsequence.
    push_neg at hns
    have hsc : ∀ k, ScatteredFun (f (k + 1)) := fun k => hns (k + 1) k.succ_pos
    obtain ⟨k, l, hkl, hred⟩ :=
      MainTheorem3 (fun k => X (k + 1)) (fun k => Y (k + 1)) (fun k => f (k + 1))
        (fun k => hf (k + 1)) hsc
    exact ⟨k + 1, l + 1, by omega, hred⟩

end MainTheorems


section ZeroDimContFunBQO

/-!
## The whole admissible class is 2-BQO

`first_reduction_theorem` classifies every continuous `f : X → Y` satisfying the standing
hypotheses (`X` zero-dimensional separable metrizable, `Y` metrizable, and
`PolishSpace X ∨ Countable Y`) as scattered, `≡ id_CantorRat`, or `≡ id_CantorSpace`.
Bundling such functions into one type `ZeroDimContFun`, this upgrades Main Theorem 3 from the
scattered class (`ScatFun`) to the *entire* admissible class: the (image-based) continuous
reducibility quasi-order `ContinuouslyReduces_range_based` is 2-BQO on `ZeroDimContFun`.
The proof reads straight off the trichotomy:

* the scattered class is 2-BQO because each member is `≡` a `ScatFun` (`main3_to_ScatFun`, or
  `ScatFun.empty` for the empty function) and `ScatFun.Reduces` is 2-BQO
  (`ScatFun.Reduces.isTwoBQO`), pulled back by `TwoBQO.comap`/`.mono`;
* the two identity classes are each a single `≡`-class, hence 2-BQO by
  `TwoBQO.of_finite_coloring` (colour by "`≡ id_CantorRat`?");
* `TwoBQO.union` glues the two parts along the trichotomy cover.
-/

/-- A continuous function `func : X → Y` satisfying the standing hypotheses of the First
Reduction Theorem: `X` is a zero-dimensional separable metrizable space, `Y` is a metrizable
space, and either `X` is Polish or `Y` is countable.

We take the order to be the memoir's image-based `ContinuouslyReduces_range_based`.  This is the
clean choice because it includes the **empty function** (empty domain, e.g. when `Y = ∅`): under
the image-based order the empty function is an honest *minimum* — indeed a minimum of *arbitrary*
functions between *arbitrary* topological spaces, continuous or not, since the empty map `∅ → Y`
image-reduces to every `g` (`ContinuouslyReduces_range_based.of_isEmpty_dom`).  Concretely the
empty function is `≡ᵣ ScatFun.empty`, so it sits inside the scattered class with no special
casing of the codomain (the total-`τ` order `ContinuouslyReduces` would instead need
`Nonempty Y`, because `ScatFun.func`'s codomain `Baire` must be reached). -/
structure ZeroDimContFun where
  X : Type
  Y : Type
  [topX : TopologicalSpace X]
  [sepX : SeparableSpace X]
  [metX : MetrizableSpace X]
  [zdX : ZeroDimensionalSpace X]
  [topY : TopologicalSpace Y]
  [metY : MetrizableSpace Y]
  func : X → Y
  cont : Continuous func
  hXY : PolishSpace X ∨ Countable Y

attribute [instance] ZeroDimContFun.topX ZeroDimContFun.sepX ZeroDimContFun.metX
  ZeroDimContFun.zdX ZeroDimContFun.topY ZeroDimContFun.metY

/-- Image-based continuous reducibility between two admissible functions (the memoir's
quasi-order, which makes the empty function a genuine minimum). -/
def ZeroDimContFun.Reduces (F G : ZeroDimContFun) : Prop :=
  ContinuouslyReduces_range_based F.func G.func

instance : IsPreorder ZeroDimContFun ZeroDimContFun.Reduces where
  refl F := ContinuouslyReduces_range_based.refl F.func
  trans _ _ _ hFG hGH := ContinuouslyReduces_range_based.trans hFG hGH

/-- **Image-based continuous reducibility is 2-BQO on the whole admissible class**
(`ZeroDimContFun`).  Every admissible function is scattered, `≡ id_CantorRat`, or
`≡ id_CantorSpace` (`first_reduction_theorem`); the scattered ones are 2-BQO via `ScatFun`
(`main3_to_ScatFun`, with the empty function represented by `ScatFun.empty`) and the two
identity classes are single `≡`-classes, so `TwoBQO.union` and `TwoBQO.of_finite_coloring`
give the result. -/
theorem ZeroDimContFun.Reduces.isTwoBQO : TwoBQO ZeroDimContFun.Reduces := by
  classical
  -- `ScatFun` is 2-BQO for the image-based order too: it contains the strong order, which is
  -- 2-BQO (`ScatFun.Reduces.isTwoBQO`), and 2-BQO is upward closed (`TwoBQO.mono`).
  have hScat : TwoBQO (fun F G : ScatFun =>
      ContinuouslyReduces_range_based F.func G.func) :=
    ScatFun.Reduces.isTwoBQO.mono (fun _ _ h => ContinuouslyReduces.to_range_based h)
  refine TwoBQO.union ZeroDimContFun.Reduces
    (fun F => ScatteredFun F.func)
    (fun F => ContinuouslyEquiv F.func (@id CantorRat) ∨
              ContinuouslyEquiv F.func (@id CantorSpace))
    (fun F => first_reduction_theorem F.cont F.hXY) ?_ ?_
  · -- Scattered part: represent each member by a `ScatFun` (image-based equivalence), the empty
    -- function by `ScatFun.empty`; then pull back `hScat` by `TwoBQO.comap`/`.mono`.
    have hrep : ∀ F : {F : ZeroDimContFun // ScatteredFun F.func},
        ∃ H : ScatFun, ContinuouslyReduces_range_based F.val.func H.func ∧
                       ContinuouslyReduces_range_based H.func F.val.func := by
      intro F
      rcases isEmpty_or_nonempty F.val.X with hX | hX
      · -- Empty domain: `≡ᵣ ScatFun.empty`, both directions vacuous (`of_isEmpty_dom`).
        have := hX
        have : IsEmpty ↥(ScatFun.empty.domain) := ⟨fun x => Set.notMem_empty x.1 x.2⟩
        exact ⟨ScatFun.empty, ContinuouslyReduces_range_based.of_isEmpty_dom,
          ContinuouslyReduces_range_based.of_isEmpty_dom⟩
      · -- Nonempty domain ⟹ nonempty codomain ⟹ `main3_to_ScatFun` (strong, hence image-based).
        have := hX
        have : Nonempty F.val.Y := ⟨F.val.func (Classical.arbitrary F.val.X)⟩
        obtain ⟨H, hHeq⟩ := main3_to_ScatFun F.val.cont F.property
        exact ⟨H, hHeq.1.to_range_based, hHeq.2.to_range_based⟩
    choose w hw1 hw2 using hrep
    refine (hScat.comap w).mono ?_
    intro a b hab
    exact (hw1 a).trans (hab.trans (hw2 b))
  · -- Identity part: two single `≡`-classes.  Chain in the strong order, convert once.
    refine TwoBQO.of_finite_coloring _
      (fun F => decide (ContinuouslyEquiv F.val.func (@id CantorRat))) ?_
    intro a b hcol
    simp only [decide_eq_decide] at hcol
    by_cases ha : ContinuouslyEquiv a.val.func (@id CantorRat)
    · exact (ha.1.trans (hcol.mp ha).2).to_range_based
    · exact ((a.property.resolve_left ha).1.trans
        (b.property.resolve_left (fun h => ha (hcol.mpr h))).2).to_range_based

end ZeroDimContFunBQO
