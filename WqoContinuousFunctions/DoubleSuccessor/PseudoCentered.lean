import WqoContinuousFunctions.DoubleSuccessor.Fine
import WqoContinuousFunctions.CenteredFunctions.CenteredAsPgluing
import WqoContinuousFunctions.ScatFun.Generators.Basics

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `6_double_successor_memo.tex`, §6.2 — Pseudo-centered functions

This file starts formalizing Section 2 ("Pseudo-centered functions") of Chapter 6
("Finite generation at double successors") of the memoir, continuing from `Fine.lean`
(§6.1, fine `c`-partitions, `ScatFun.IsCPartition`/`.IsFine`).

A function `f` (together with a fine `c`-partition `𝒫`) is **pseudo-centered at `y`** if `𝒫`
has a single cocenter `y` and all of its pieces restrict `f` to equivalent functions — the
simplest possible combinatorial shape a fine `c`-partition can have (memoir,
`6_double_successor_memo.tex:134-136`: "a disjoint union of the same centered function with
only one cocenter"). The section's main result, the **Vertical Theorem**, shows that such an
`f` is sandwiched, near `y`, between an `ω`-tower of a finite set of "obstruction" generators
and a single centered function `g` of the same `CB`-rank as `f`.

## Main definitions

* `ScatFun.IsCPartition.IsPseudoCenteredAt` — `f` (with fine `c`-partition `𝒫`) pseudo-centered
  at `y` (memoir Definition, `6_double_successor_memo.tex:139-141`).

## Main results

* `ScatFun.IsCPartition.IsPseudoCenteredAt.exists_rep` — every pseudo-centered partition has a
  single centered representative `ĝ` with `f↾P ≡ ĝ` for every piece `P` (memoir,
  `6_double_successor_memo.tex:162`). **Fully proved.**
* `coRestrict_bound_of_common_cocenter` — if `g` is equivalent to every piece of a `c`-partition
  with cocenter `y`, then `g ≤ F⇂V` for every clopen `V ∋ y` (memoir, `:166`). **Fully proved.**
* `ScatFun.finGl_reduces_omega_glList` — every `FinGl S` member reduces into `ω(glList S.toList)`,
  the "gl-target" analogue of `finitegenerationAndPgluing_upper` needed by the hard case's Phase D
  below. **Fully proved.**
* `verticalTheorem` — the **Vertical Theorem** (`6_double_successor_memo.tex:150-160`). Its body
  is **fully assembled**, dispatching on whether `F`'s rays lie in `FinGl G`:
  * `verticalTheorem_setup` (Phase A, `:161-166`) — existence of the sandwiching `g`/`G`.
    **Fully proved**, including its structure lemma
    `exists_pglFinset_decomp_of_centered_doubleSucc` ("finite generation propagates one level up",
    Thm 4.9 at rank `α+2`). Conclusion relaxed to `G ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}`.
  * `verticalTheorem_easyCase` (Phase B, `:168-171`) — the no-obstruction branch, `F ≤ g`.
    **Fully proved**.
  * `verticalTheorem_hardCase_rayOn_reduces_omegaG` / `..._rayOn_reduces_g` (Phase D, `:190-191`)
    — every ray reduces into `ω(glList G)`, hence into `g`. **Fully proved**.
  * `verticalTheorem_hardCase_glList_le_g` (clause 3, `:190-191`, `\gl H ≤ g`). **Fully proved**,
    via the ray-`≤ ω G` bound plus `gl_const_omega_equiv`/`omega_glList_reduces_pglFinset`.
  * `verticalTheorem_hardCase_C` (Phase C, `:180-187`, `\gl H ≤ f⇂W` for clopen `y ∉ W ⊆ U`).
    **Fully proved**, via C1 (`pseudoCentered_obstruction_infinite_or_empty`, obstruction sets
    infinite), an injective large-index choice (`exists_strictMono_forall_mem`), the tail
    threshold `exists_tail_raySet_subset`, and C3 (`glList_reduces_coRestrict_biUnion_rays`,
    block-matching into disjoint rays — a cleaner substitute for the memoir's
    `Intertwinereductionsforomegacentered`).
  * `verticalTheorem_hardCase_split` (Phases E+F) — the last genuinely
    double-successor-specific step (the diagonal domain split). **Fully proved**: item E
    (`hardCase_split_claim`, the per-`j` generator case-split, using `diagBracketSet` for
    `f^{[j]}` and the `exists_partition_enumeration` `ℕ`-enumeration of `Part`) and item F (the
    diagonal assembly in its body, `clopen_regroup`) are both discharged. See each docstring for
    the proof strategy. `verticalTheorem`'s hard-case branch defines the obstruction `Finset H`
    and assembles these plus clause 3, Phase C, and `coRestrict_bound_of_common_cocenter`.

**`verticalTheorem` is fully proved in this file**, as is its `Fine.lean` dependency (the
fine-partition existence machinery); nothing in `PseudoCentered.lean` itself is left open.
-/

noncomputable section

/-! ## Pseudo-centered functions (`6_double_successor_memo.tex:128-141`) -/

namespace ScatFun.IsCPartition

variable {F : ScatFun} {Part : Set (Set ↑F.domain)}

/-- `f` together with a fine `c`-partition `𝒫` (fine relative to `lam`) is **pseudo-centered
at `y`** (memoir Definition, `6_double_successor_memo.tex:139-141`): `𝒫`'s set of cocenters
`Y_𝒫` is the singleton `{y}`, and every two pieces of `𝒫` restrict `F` to equivalent
functions.

As with `IsFine` (`Fine.lean`), `lam` is carried explicitly rather than derived from `F`'s
`CB`-rank, since the definition itself doesn't need it decomposed; call sites (e.g.
`verticalTheorem` below, for `F` of rank `α+2`) instantiate it at `lam = α.limitPart`. -/
def IsPseudoCenteredAt (hA : F.IsCPartition Part) (lam : Ordinal.{0}) (y : Baire) : Prop :=
  hA.IsFine lam ∧ hA.cocenterSet = {y} ∧
    ∀ P ∈ Part, ∀ P' ∈ Part, ScatFun.Equiv (F.restrict P) (F.restrict P')

/-- **The canonical representative `f̂`** (memoir, `6_double_successor_memo.tex:162`: "Fix a
fine `c`-partition `𝒫` such that `Y_𝒫 = {y}` and some centered `f̂` with `f↾P ≡ f̂` for all
`P ∈ 𝒫`"). Since `Y_𝒫 = {y}` is nonempty, `𝒫` itself is nonempty; any of its pieces serves as
the witness `f̂`, by the pairwise-equivalence clause of pseudo-centeredness. -/
theorem IsPseudoCenteredAt.exists_rep {hA : F.IsCPartition Part} {lam : Ordinal.{0}}
    {y : Baire} (hpc : hA.IsPseudoCenteredAt lam y) :
    ∃ ĝ : ScatFun, IsCentered ĝ.func ∧ ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) ĝ := by
  have hy : y ∈ hA.cocenterSet := by simp [hpc.2.1]
  obtain ⟨p, -⟩ := hy
  exact ⟨F.restrict p.1, hA.centered p.1 p.2, fun P hP => hpc.2.2 P hP p.1 p.2⟩

end ScatFun.IsCPartition

/-- **A single common cocenter forces a corestriction bound.** If `y` is the cocenter of some
piece of a `c`-partition `𝒫` and `g` is equivalent to every piece, then `g ≤ F⇂V` for every
clopen `V ∋ y` (memoir, `6_double_successor_memo.tex:166`: "for all clopen `V ∋ y`,
`\pgl G ≤ f⇂V`, because for any `P ∈ 𝒫` we have `\pgl G ≤ f↾P ≤ f↾P⇂V`"). Chains
`reduces_coRestrict_cocenter_nbhd` (centeredness gives `f↾P ≤ f↾P⇂V`) with
`coRestrict_restrict_reduces` (`f↾P⇂V ≤ F⇂V`), both from `Fine.lean`. Stated for a bare
`y ∈ hA.cocenterSet` (not full pseudo-centeredness) so it is reusable wherever *some* piece has
cocenter `y`, not just in the single-cocenter case. -/
theorem coRestrict_bound_of_common_cocenter
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hy : y ∈ hA.cocenterSet)
    {g : ScatFun} (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g) :
    ∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V) := by
  obtain ⟨p, hp⟩ := hy
  intro V hVcl hyV
  have hcent : IsCentered (F.restrict p.1).func := hA.centered p.1 p.2
  have hcocenter : cocenter (F.restrict p.1).func hcent = y := by
    simpa [ScatFun.IsCPartition.cocenterOf] using hp
  have hcocV : cocenter (F.restrict p.1).func hcent ∈ V := by rw [hcocenter]; exact hyV
  have h1 : ScatFun.Reduces g (F.restrict p.1) := (hgP p.1 p.2).symm.1
  have h2 : ScatFun.Reduces (F.restrict p.1) ((F.restrict p.1).coRestrict V) :=
    reduces_coRestrict_cocenter_nbhd (F.restrict p.1) hcent hVcl.isOpen hcocV
  have h3 : ScatFun.Reduces ((F.restrict p.1).coRestrict V) (F.coRestrict V) :=
    ScatFun.coRestrict_restrict_reduces F p.1 V
  exact h1.trans (h2.trans h3)

/-- **`FinGl S` members reduce into `ω(glList S.toList)`.** This is the "gl-target" analogue of
`ScatFun.finitegenerationAndPgluing_upper` (`ScatFun/FiniteGluing.lean:316`) flagged as missing
in the Vertical Theorem's Phase D docstring below: a family of pieces each individually bounded
in `FinGl G` combines into a bound by the single fixed `ω G`.

Since `omega (glList S.toList) = gl (fun _ => glList S.toList)` already glues together
*infinitely many* full copies of `glList S.toList` (one per `ℕ`-index), no reindexing is needed:
every block of `Gl S.toFinFun t` (`t` the finite multiplicity witness for `a ∈ FinGl S.toFinFun`)
is either `empty` (which reduces into anything, `empty_reduces`) or some `S.toFinFun i`, which
reduces into `glList S.toList` via the block-`i` embedding `reduces_block_gl`; `gl_reduces_of_pointwise`
then bounds the whole gluing blockwise, since the target family is constant. -/
theorem ScatFun.finGl_reduces_omega_glList {S : Finset ScatFun} {a : ScatFun}
    (ha : a ∈ ScatFun.FinGl S.toFinFun) :
    ScatFun.Reduces a (ScatFun.omega (ScatFun.glList S.toList)) := by
  obtain ⟨t, -, hat⟩ := ha
  refine hat.trans ?_
  show ScatFun.Reduces (ScatFun.gl (ScatFun.copiesSeq S.toFinFun t))
    (ScatFun.gl (fun _ => ScatFun.glList S.toList))
  apply ScatFun.gl_reduces_of_pointwise
  intro k
  by_cases hk : k < (ScatFun.copiesList S.toFinFun t).length
  · obtain ⟨i, hi⟩ := ScatFun.copiesSeq_eq_B S.toFinFun t k hk
    show ScatFun.Reduces (ScatFun.copiesSeq S.toFinFun t k) (ScatFun.glList S.toList)
    rw [hi]
    have hget : S.toFinFun i = S.toList.getD i.val ScatFun.empty := by
      unfold Finset.toFinFun
      simp [List.getD_eq_getElem?_getD]
    show ScatFun.Reduces (S.toFinFun i) (ScatFun.gl (fun k => S.toList.getD k ScatFun.empty))
    rw [hget]
    exact ScatFun.reduces_block_gl (fun k => S.toList.getD k ScatFun.empty) i.val
  · have hempty : ScatFun.copiesSeq S.toFinFun t k = ScatFun.empty :=
      List.getD_eq_default _ _ (not_lt.mp hk)
    show ScatFun.Reduces (ScatFun.copiesSeq S.toFinFun t k) (ScatFun.glList S.toList)
    rw [hempty]
    exact ScatFun.empty_reduces _

/-- **A countable gluing of `ω c`'s collapses to `ω c`.** Needed to combine countably many
pieces, each individually bounded by `ω G` (via `finGl_reduces_omega_glList`), into a *single*
`ω G` bound (Phase D of the Vertical Theorem's hard case): `gl (fun _ => omega c)` is literally
the nested double gluing `gl (fun i => gl (fun _ => c))`, which `gl_gl_flatten_equiv`
(`ScatFun/LevelsFinitelyGenerated/GlList.lean`) identifies (via the `ℕ ≃ ℕ × ℕ` pairing) with the
flattened `gl (fun m => c) = omega c`. -/
theorem ScatFun.gl_const_omega_equiv (c : ScatFun) :
    ScatFun.Equiv (ScatFun.gl (fun _ : ℕ => ScatFun.omega c)) (ScatFun.omega c) := by
  have h := ScatFun.gl_gl_flatten_equiv (fun _ _ : ℕ => c)
  simpa [ScatFun.omega] using h

/-! ### Sound helper lemmas about `pglFinset`

Three general facts about pointed gluings of finite sets (extracted by aristotle
while investigating Phase A; self-contained and reusable). -/

/-- Every element of `G` reduces into `pglFinset G` (it is a block of the first copy). -/
lemma ScatFun.mem_reduces_pglFinset {G : Finset ScatFun} {c : ScatFun} (hc : c ∈ G) :
    ScatFun.Reduces c (ScatFun.pglFinset G) := by
  obtain ⟨l, hl⟩ : ∃ l : List ScatFun, l = G.toList ∧ c ∈ l := by
    aesop;
  unfold ScatFun.pglFinset;
  unfold ScatFun.pgl;
  unfold PointedGluingFun ScatFun.pglBlock; simp +decide ;
  have := ScatFun.mem_reduces_glList ( Finset.mem_toList.mpr hc );
  exact this.trans ( block_reduces_pgl ( fun _ => ScatFun.glList G.toList ) 0 )

/-- `ω c` reduces into `pglFinset G` whenever `c ∈ G`: the `ω`-copies of `c` are routed into the
`ω`-copies (one per outer slot) of `pglFinset G`. -/
lemma ScatFun.omega_reduces_pglFinset {G : Finset ScatFun} {c : ScatFun} (hc : c ∈ G) :
    ScatFun.Reduces (ScatFun.omega c) (ScatFun.pglFinset G) := by
  have h1 : ScatFun.Reduces c (ScatFun.glList G.toList) :=
    ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hc)
  have h2 : ScatFun.Reduces (ScatFun.omega c) (ScatFun.omega (ScatFun.glList G.toList)) :=
    ScatFun.omega_reduces_of_reduces h1
  have h3 : ScatFun.Reduces (ScatFun.omega (ScatFun.glList G.toList)) (ScatFun.pglFinset G) := by
    obtain ⟨σ, τ, hσ, heq, hτ, -, -⟩ :=
      ScatFun.gl_reduces_pgl_direct (fun _ => ScatFun.glList G.toList)
        (fun _ => ScatFun.glList G.toList) id Function.injective_id (fun _ => Or.inl rfl)
    exact ⟨σ, hσ, τ, hτ, heq⟩
  exact h2.trans h3

/-- Reindexing: the pointed gluing of the periodic repetition of a nonempty finite family `b` is
equivalent to the `pglFinset` of its image (both cycle through the same finite set). -/
lemma ScatFun.pgl_repSeq_equiv_pglFinset_image {k : ℕ} (b : Fin k → ScatFun) (hk : 0 < k) :
    ScatFun.Equiv (ScatFun.pgl (ScatFun.repSeq b))
      (ScatFun.pglFinset (Finset.image b Finset.univ)) := by
  refine ⟨ ?_, ?_ ⟩;
  · -- By definition of `repSeq`, every element in `repSeq b` is in the image of `b`.
    have h_repSeq_image : ∀ i, ∃ j, ScatFun.repSeq b i = b j := by
      exact fun i => ⟨ ⟨ i % k, Nat.mod_lt _ hk ⟩, by unfold ScatFun.repSeq; aesop ⟩;
    choose f hf using h_repSeq_image;
    -- By definition of `pglFinset`, every element in `pglFinset (image b)` is in the image of `b`.
    have h_pglFinset_image : ∀ i, ScatFun.Reduces (b (f i)) (ScatFun.pglFinset (Finset.image b Finset.univ)) := by
      exact fun i => ScatFun.mem_reduces_pglFinset ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) );
    have h_pgl_reduces_pgl : ∀ (s t : ℕ → ScatFun), (∀ i j₀, ∃ j ≥ j₀, ScatFun.Reduces (s i) (t j)) → ScatFun.Reduces (ScatFun.pgl s) (ScatFun.pgl t) := by
      exact fun s t a => pgl_reduces_pgl s t a
    convert h_pgl_reduces_pgl _ _ _ using 1;
    intro i j₀; use j₀; simp [hf];
    grind [mem_reduces_glList, Finset.mem_toList];
  · -- By definition of `repSeq`, every element in the image of `b` appears cofinally in `repSeq b`.
    have h_cofinal : ∀ x ∈ Finset.image b Finset.univ, ∀ j₀ : ℕ, ∃ j ≥ j₀, ScatFun.Reduces x (ScatFun.repSeq b j) := by
      intro x hx j₀
      obtain ⟨i, hi⟩ : ∃ i : Fin k, x = b i := by
        aesop;
      refine ⟨ j₀ * k + i, ?_, ?_ ⟩ <;> simp +decide [ hi, ScatFun.repSeq ];
      · nlinarith [ Fin.is_lt i ];
      · simp +decide [ Nat.mod_eq_of_lt, hk ];
        constructor;
        exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ScatFun, (∀ i, g i ∈ Finset.image b Finset.univ) ∧ ScatFun.Equiv (ScatFun.pglFinset (Finset.image b Finset.univ)) (ScatFun.pgl g) := by
      obtain ⟨g, hg⟩ : ∃ g : Fin (Finset.card (Finset.image b Finset.univ)) → ScatFun, (∀ i, g i ∈ Finset.image b Finset.univ) ∧ ScatFun.Equiv (ScatFun.pglFinset (Finset.image b Finset.univ)) (ScatFun.pgl (ScatFun.repSeq g)) := by
        have := ScatFun.pglFinset_equiv_pgl_repSeq ( Finset.image b Finset.univ );
        refine ⟨ ?_, ?_, ?_ ⟩;
        exact fun i => ( Finset.image b Finset.univ ).toList.get ⟨ i, by simp ⟩;
        · exact fun i => Finset.mem_toList.mp ( by simp );
        · congr! 2;
      use fun i => g ⟨i % Finset.card (Finset.image b Finset.univ), Nat.mod_lt _ (Finset.card_pos.mpr ⟨b ⟨0, hk⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)⟩;
      convert hg using 1;
      · grind;
      · congr! 2;
        ext i; simp [ScatFun.repSeq];
        grind +locals;
    have h_cofinal_g : ∀ i, ∀ j₀ : ℕ, ∃ j ≥ j₀, ScatFun.Reduces (g i) (ScatFun.repSeq b j) := by
      exact fun i j₀ => h_cofinal _ ( hg.1 i ) j₀;
    have h_cofinal_g : ScatFun.Reduces (ScatFun.pgl g) (ScatFun.pgl (ScatFun.repSeq b)) :=
      pgl_reduces_pgl g (ScatFun.repSeq b) h_cofinal_g
    exact hg.2.1.trans h_cofinal_g

/-- **`0^ω` is a center of `pgl F`, for `F` regular — witness exposed.**
`CenteredFunctions/Helpers.lean`'s `pgl_isCentered_of_regular` proves exactly this but
immediately packages it into the existential `IsCentered`, erasing which witness was used;
since `cocenter` needs a *specific* known center to pin down its value (via
`scatteredHaveCocenter`, comparing it against the arbitrary witness `Classical.choice` produces
for the existential), the explicit witness is needed here. Duplicated (rather than extracted
into `Helpers.lean`, a hub imported from many `grind`-sensitive call sites — see the "avoid
widely-imported files" project note) verbatim from that lemma's proof. -/
theorem ScatFun.pgl_isCenterFor_zeroStream_of_regular (F : ℕ → ScatFun)
    (hf_reg : Preorder.IsRegularSeq ScatFun.Reduces F) :
    IsCenterFor (ScatFun.pgl F).func ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ := by
  apply pgl_isCenterFor_of_local
  intro i V hV hzV
  obtain ⟨n, hn⟩ :=
    nbhd_basis' (ScatFun.pgl F).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hV hzV
  obtain ⟨j, hjn, hred⟩ := hf_reg.exists_ge i n
  obtain ⟨σ₀, hσ₀cont, τ₀, hτ₀cont, hστ₀⟩ := hred
  set σ : (F i).domain → ↥(ScatFun.pgl F).domain :=
    fun z => ⟨prependZerosOne j (σ₀ z).val,
      prependZerosOne_mem_pointedGluingSet _ j _ (σ₀ z).prop⟩ with hσ
  have hfs : ∀ z, (ScatFun.pgl F).func (σ z) = prependZerosOne j ((F j).func (σ₀ z)) :=
    fun z => ScatFun.pgl_func_block F j (σ₀ z)
  refine ⟨σ, fun y => τ₀ (stripZerosOne j y), ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk
      ((continuous_prependZerosOne j).comp (continuous_subtype_val.comp hσ₀cont)) _
  · intro z
    show (F i).func z = τ₀ (stripZerosOne j ((ScatFun.pgl F).func (σ z)))
    rw [hfs z, stripZerosOne_prependZerosOne]
    exact hστ₀ z
  · apply hτ₀cont.comp (continuous_stripZerosOne j).continuousOn
    rintro _ ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    show ((F j).func ∘ σ₀) z = stripZerosOne j ((ScatFun.pgl F).func (σ z))
    rw [hfs z, stripZerosOne_prependZerosOne]
    rfl
  · intro z
    refine hn ?_
    intro k hk
    exact prependZerosOne_head_eq_zero j _ k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjn)
  · have hCcl : IsClosed {y : Baire | y j = 1} :=
      isClosed_singleton.preimage (continuous_apply j)
    have hsub : Set.range (fun z => (ScatFun.pgl F).func (σ z)) ⊆ {y : Baire | y j = 1} := by
      rintro _ ⟨z, rfl⟩
      simp only [Set.mem_setOf_eq, hfs z]
      exact prependZerosOne_at_i j _
    intro h
    have : zeroStream ∈ {y : Baire | y j = 1} := hCcl.closure_subset_iff.mpr hsub h
    simp [zeroStream] at this

/-- **The cocenter of a regular `pgl` is `0^ω`.** Given the explicit center witness
`pgl_isCenterFor_zeroStream_of_regular`, `scatteredHaveCocenter` identifies its image
(`zeroStream`, since `pgl F`'s base-point block is untouched, `ScatFun.pgl_func_zeroStream`)
with the value of `cocenter (pgl F).func hcent` for *any* other proof `hcent` of centeredness
(since all centers agree). -/
theorem ScatFun.cocenter_pgl_eq_zeroStream_of_regular (F : ℕ → ScatFun)
    (hf_reg : Preorder.IsRegularSeq ScatFun.Reduces F)
    (hcent : IsCentered (ScatFun.pgl F).func) :
    cocenter (ScatFun.pgl F).func hcent = zeroStream := by
  have hzero := ScatFun.pgl_isCenterFor_zeroStream_of_regular F hf_reg
  have heq := scatteredHaveCocenter (ScatFun.pgl F).func (ScatFun.pgl F).hScat
    hcent.choose ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ hcent.choose_spec hzero
  show (ScatFun.pgl F).func hcent.choose = zeroStream
  rw [heq]
  exact ScatFun.pgl_func_zeroStream F _

/-- **A `rayOn` is `ContinuouslyReduces`-equivalent (both ways) to the raw `RayFun` predicate.**
`P.rayOn y Set.univ n` is, by definition, `P.restrict (Set.univ ∩ {a | P.func a ∈ RaySet Set.univ
y n})`; since `Set.univ ∩ S = S`, its defining set literally equals `RayFun`'s domain predicate
`{a | (∀ k < n, P.func a k = y k) ∧ P.func a n ≠ y n}` (`RaySet`'s own definition), so
`Homeomorph.setCongr` identifies the two subtypes and, composed with `P.restrictEquiv`, gives the
homeomorphism pushed through `ContinuouslyReduces.refl (RayFun P.func y n)` on both sides — the
same idiom as `restrict_restrict_equiv` above, one level down (no restrict on the raw side). This
bridges `ScatFun.rayOn` to the raw-predicate form used by `rigidityOfCocenter_finiteGluing`. -/
theorem ScatFun.rayOn_continuouslyReduces_rayFun (P : ScatFun) (y : Baire) (n : ℕ) :
    ContinuouslyReduces (P.rayOn y Set.univ n).func (RayFun P.func y n) ∧
    ContinuouslyReduces (RayFun P.func y n) (P.rayOn y Set.univ n).func := by
  have hAeq : (Set.univ : Set ↑P.domain) ∩ {a : ↑P.domain | P.func a ∈ RaySet Set.univ y n}
      = {a : ↑P.domain | (∀ k, k < n → P.func a k = y k) ∧ P.func a n ≠ y n} := by
    ext a; simp [RaySet]
  set e := (P.restrictEquiv
      (Set.univ ∩ {a : ↑P.domain | P.func a ∈ RaySet Set.univ y n})).trans
    (Homeomorph.setCongr hAeq) with hedef
  have hfunc : (P.rayOn y Set.univ n).func = (RayFun P.func y n) ∘ e := by
    funext x
    show P.func (Subtype.val ((P.restrictEquiv _) x)) = P.func (Subtype.val (e x))
    have hval : (Subtype.val ((P.restrictEquiv _) x) : ↑P.domain) = Subtype.val (e x) := by
      show (Subtype.val ((P.restrictEquiv _) x) : ↑P.domain)
        = Subtype.val (Homeomorph.setCongr hAeq ((P.restrictEquiv _) x))
      rfl
    rw [hval]
  refine ⟨?_, ?_⟩
  · have h1 := (ContinuouslyReduces.refl (RayFun P.func y n)).comp_homeomorph_left e
    rwa [← hfunc] at h1
  · have h2 := (ContinuouslyReduces.refl (RayFun P.func y n)).comp_homeomorph_right e
    rwa [← hfunc] at h2

/-- **A finite-union-of-rays raw predicate is `ContinuouslyReduces`-equivalent (both ways) to
the corresponding `ScatFun` corestriction.** The same `Homeomorph.setCongr` idiom as
`rayOn_continuouslyReduces_rayFun`, generalized from a single ray index `n` to a finite union
`i ∈ Jf`: `rigidityOfCocenter_finiteGluing`'s target predicate `∃ i, m ≤ i ∧ i ≤ M ∧ ...` is
exactly this shape with `Jf = Finset.Icc m M`. -/
theorem ScatFun.corestrict_finUnionRays_continuouslyReduces
    (Q : ScatFun) (y : Baire) (Jf : Finset ℕ) :
    ContinuouslyReduces
      (fun (x : {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧ Q.func a i ≠ y i}) =>
        Q.func x.val)
      (Q.restrict {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Jf, RaySet Set.univ y i}).func ∧
    ContinuouslyReduces
      (Q.restrict {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Jf, RaySet Set.univ y i}).func
      (fun (x : {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧ Q.func a i ≠ y i}) =>
        Q.func x.val) := by
  have hAeq : {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Jf, RaySet Set.univ y i}
      = {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧ Q.func a i ≠ y i} := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_iUnion, RaySet, exists_prop]; tauto
  set e := (Q.restrictEquiv
      {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Jf, RaySet Set.univ y i}).trans
    (Homeomorph.setCongr hAeq) with hedef
  have hfunc : (Q.restrict {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Jf, RaySet Set.univ y i}).func
      = (fun (x : {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧ Q.func a i ≠ y i}) =>
          Q.func x.val) ∘ e := by
    funext x
    show Q.func (Subtype.val ((Q.restrictEquiv _) x)) = Q.func (Subtype.val (e x))
    have hval : (Subtype.val ((Q.restrictEquiv _) x) : ↑Q.domain) = Subtype.val (e x) := by
      show (Subtype.val ((Q.restrictEquiv _) x) : ↑Q.domain)
        = Subtype.val (Homeomorph.setCongr hAeq ((Q.restrictEquiv _) x))
      rfl
    rw [hval]
  refine ⟨?_, ?_⟩
  · have h1 := (ContinuouslyReduces.refl
        (fun (x : {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧
          Q.func a i ≠ y i}) => Q.func x.val)).comp_homeomorph_right e
    rwa [← hfunc] at h1
  · have h2 := (ContinuouslyReduces.refl
        (fun (x : {a : ↑Q.domain | ∃ i ∈ Jf, (∀ k, k < i → Q.func a k = y k) ∧
          Q.func a i ≠ y i}) => Q.func x.val)).comp_homeomorph_left e
    rwa [← hfunc] at h2

/-- **Phase D, item 1 (piece-ray ↦ `FinGl G`).** Every ray of a centered `P` equivalent to
`pglFinset G`, taken at `P`'s own cocenter, reduces into `FinGl G.toFinFun`.

Instantiates `rigidityOfCocenter_finiteGluing` (Prop. 4.4 Item 3, `CenteredFunctions/Theorems.lean`)
between `P` and `Q := pglFinset G` at `m = 0`: this gives, for every `n`, an `M` and a raw
`ContinuouslyReduces` from `P`'s `n`-th ray (as a predicate-subtype using `cocenter P.func hPcent`)
into the finite gluing of `Q`'s rays `0..M` (using `cocenter Q.func hQcent`). Since
`Q = pgl (fun _ => glList G.toList)` is a *constant* regular sequence,
`cocenter_pgl_eq_zeroStream_of_regular` identifies `cocenter Q.func hQcent` with `zeroStream`, so
each of these finitely many rays (`RayFun_pgl_zeroStream_reduces_block`) reduces into the single
block `glList G.toList`, which is trivially `∈ FinGl G.toFinFun`
(`ScatFun.finGl_of_equiv_glList`/`glList` reflexivity on `G.toList` itself); a finite plain gluing
of `FinGl G.toFinFun` members is again in `FinGl G.toFinFun`
(`ScatFun.finGl_gl_ite_of_forall_finGl`, `Sandwich_lemma.lean`). Repackaging the raw
`ContinuouslyReduces` conclusion at the `ScatFun.rayOn` level uses the same
`restrict_restrict_equiv`-style identification as `rayOn_restrict_equiv` above. -/
theorem ScatFun.rayOn_cocenter_reduces_finGl_of_equiv_pglFinset
    (P : ScatFun) (hPcent : IsCentered P.func) (G : Finset ScatFun)
    (hequiv : ScatFun.Equiv P (ScatFun.pglFinset G)) (n : ℕ) :
    ∃ h ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces (P.rayOn (cocenter P.func hPcent) Set.univ n) h := by
  set c : ScatFun := ScatFun.glList G.toList with hcdef
  set Q : ScatFun := ScatFun.pglFinset G with hQdef
  have hreg : Preorder.IsRegularSeq ScatFun.Reduces (fun _ : ℕ => c) := scatFun_const_isRegularSeq c
  have hQcent : IsCentered Q.func := pgl_isCentered_of_regular (fun _ => c) hreg
  have hQcoc : cocenter Q.func hQcent = zeroStream :=
    ScatFun.cocenter_pgl_eq_zeroStream_of_regular (fun _ => c) hreg hQcent
  obtain ⟨M, -, hred⟩ := rigidityOfCocenter_finiteGluing P Q hPcent hQcent hequiv 0 n
  -- Repackage the `0 ≤ i ∧ i ≤ M` target predicate as `i ∈ Finset.Icc 0 M`.
  have hpredeq : {a : ↑Q.domain | ∃ i, 0 ≤ i ∧ i ≤ M ∧
        (∀ k, k < i → Q.func a k = cocenter Q.func hQcent k) ∧
        Q.func a i ≠ cocenter Q.func hQcent i}
      = {a : ↑Q.domain | ∃ i ∈ Finset.Icc 0 M,
        (∀ k, k < i → Q.func a k = cocenter Q.func hQcent k) ∧
        Q.func a i ≠ cocenter Q.func hQcent i} := by
    ext a; simp [Finset.mem_Icc]
  have hred2 : ContinuouslyReduces (RayFun P.func (cocenter P.func hPcent) n)
      (fun (x : {a : ↑Q.domain | ∃ i ∈ Finset.Icc 0 M,
        (∀ k, k < i → Q.func a k = cocenter Q.func hQcent k) ∧
        Q.func a i ≠ cocenter Q.func hQcent i}) => Q.func x.val) :=
    hred.comp_homeomorph_right (Homeomorph.setCongr hpredeq.symm)
  have hbridge := ScatFun.corestrict_finUnionRays_continuouslyReduces Q
    (cocenter Q.func hQcent) (Finset.Icc 0 M)
  have hred3 : ContinuouslyReduces (RayFun P.func (cocenter P.func hPcent) n)
      (Q.restrict {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Finset.Icc 0 M,
        RaySet Set.univ (cocenter Q.func hQcent) i}).func :=
    hred2.trans hbridge.1
  -- Bound the corestriction to the finite ray union by a finite `gl` of copies of `c`.
  set U : Set ↑Q.domain := {a : ↑Q.domain | Q.func a ∈ ⋃ i ∈ Finset.Icc 0 M,
    RaySet Set.univ (cocenter Q.func hQcent) i} with hUdef
  have hUeq : U = ⋃ i ∈ Finset.Icc 0 M,
      {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} := by
    rw [hUdef]; ext a; simp
  have hUcl : IsClopen U := by
    rw [hUeq]
    exact isClopen_biUnion_finset
      (fun i _ => (isClopen_raySet (cocenter Q.func hQcent) i).preimage Q.hCont)
  set D : ℕ → Set ↑(Q.restrict U).domain :=
    fun i => {w : ↑(Q.restrict U).domain | (Q.restrictEquiv U w : ↑Q.domain) ∈
      {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} ∩ U} with hDdef
  have hduD : (Q.restrict U).IsDisjointUnion D := by
    refine ⟨fun i => ?_, fun i i' hii' => ?_, ?_⟩
    · exact (((isClopen_raySet (cocenter Q.func hQcent) i)).preimage Q.hCont).inter hUcl
        |>.preimage (continuous_subtype_val.comp (Q.restrictEquiv U).continuous)
    · rw [Set.disjoint_left]
      intro w hw hw'
      simp only [hDdef, Set.mem_setOf_eq, Set.mem_inter_iff, RaySet, Set.mem_univ,
        true_and] at hw hw'
      rcases lt_or_gt_of_ne hii' with hlt | hlt
      · exact hw.1.2 (hw'.1.1 i hlt)
      · exact hw'.1.2 (hw.1.1 i' hlt)
    · ext w
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hmem : (Q.restrictEquiv U w : ↑Q.domain) ∈ U := (Q.restrictEquiv U w).2
      have hmem2 : (Q.restrictEquiv U w : ↑Q.domain) ∈
          ⋃ i ∈ Finset.Icc 0 M, {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} :=
        hUeq ▸ hmem
      simp only [Set.mem_iUnion] at hmem2
      obtain ⟨i, -, hi⟩ := hmem2
      refine ⟨i, ?_⟩
      simp only [hDdef, Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨hi, hmem⟩
  have hstep1 : ScatFun.Reduces (Q.restrict U)
      (ScatFun.gl (fun i => (Q.restrict U).restrict (D i))) :=
    scatFun_reduces_gl_of_domain_partition (Q.restrict U) D hduD
  have hstep2 : ∀ i, ScatFun.Reduces ((Q.restrict U).restrict (D i))
      (if i ∈ Finset.Icc 0 M then c else ScatFun.empty) := by
    intro i
    by_cases hi : i ∈ Finset.Icc 0 M
    · rw [if_pos hi]
      have hsub : {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} ∩ U ⊆ U :=
        Set.inter_subset_right
      have e1 : ScatFun.Reduces ((Q.restrict U).restrict (D i))
          (Q.restrict ({a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} ∩ U)) :=
        (ScatFun.restrict_restrict_equiv Q U
          ({a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} ∩ U) hsub).1
      have hIcap : {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} ∩ U
          = {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} := by
        refine Set.inter_eq_left.mpr (fun a ha => ?_)
        rw [hUeq]
        exact Set.mem_biUnion hi ha
      rw [hIcap] at e1
      have e2 : ScatFun.Reduces
          (Q.restrict {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i}) c := by
        have hrayeq : Q.rayOn (cocenter Q.func hQcent) Set.univ i
            = Q.restrict {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} := by
          rw [ScatFun.rayOn, Set.univ_inter]
        rw [← hrayeq]
        exact (ScatFun.rayOn_continuouslyReduces_rayFun Q (cocenter Q.func hQcent) i).1.trans
          (hQcoc ▸ RayFun_pgl_zeroStream_reduces_block (fun _ => c) i)
      exact e1.trans e2
    · rw [if_neg hi]
      have : IsEmpty ↑((Q.restrict U).restrict (D i)).domain := by
        rw [Set.isEmpty_coe_sort, Set.eq_empty_iff_forall_notMem]
        rintro x ⟨h, hx⟩
        simp only [hDdef, Set.mem_setOf_eq, Set.mem_inter_iff, RaySet, Set.mem_univ,
          true_and] at hx
        obtain ⟨⟨hx1, hx2⟩, hxU⟩ := hx
        have hxU2 : (Q.restrictEquiv U ⟨x, h⟩ : ↑Q.domain) ∈
            ⋃ i ∈ Finset.Icc 0 M,
              {a : ↑Q.domain | Q.func a ∈ RaySet Set.univ (cocenter Q.func hQcent) i} :=
          hUeq ▸ hxU
        simp only [Set.mem_iUnion] at hxU2
        obtain ⟨i', hi', hxi'⟩ := hxU2
        simp only [Set.mem_setOf_eq, RaySet, Set.mem_univ, true_and] at hxi'
        rcases eq_or_ne i i' with rfl | hne
        · exact hi hi'
        · rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact hx2 (hxi'.1 i hlt)
          · exact hxi'.2 (hx1 i' hlt)
      exact ScatFun.reduces_of_isEmpty_domain this
  have hstep3 : ScatFun.Reduces (Q.restrict U)
      (ScatFun.gl (fun i => if i ∈ Finset.Icc 0 M then c else ScatFun.empty)) :=
    hstep1.trans (ScatFun.gl_reduces_of_pointwise _ _ hstep2)
  have hmemc : c ∈ ScatFun.FinGl G.toFinFun :=
    ScatFun.finGl_of_equiv_glList (L := G.toList) (fun w hw => Finset.mem_toList.mp hw)
      (ScatFun.Equiv.refl c)
  have hmemh : (ScatFun.gl (fun i => if i ∈ Finset.Icc 0 M then c else ScatFun.empty))
      ∈ ScatFun.FinGl G.toFinFun :=
    ScatFun.finGl_gl_ite_of_forall_finGl (Finset.Icc 0 M) (fun _ => c) (fun i _ => hmemc)
  refine ⟨ScatFun.gl (fun i => if i ∈ Finset.Icc 0 M then c else ScatFun.empty), hmemh, ?_⟩
  have hrayP := (ScatFun.rayOn_continuouslyReduces_rayFun P (cocenter P.func hPcent) n).1
  exact hrayP.trans (hred3.trans hstep3)

/-!
## The Vertical Theorem (`6_double_successor_memo.tex:150-251`)
-/

/-- **`𝒞_{α+2} = centStep 𝒞_{α+1}`.** The double-successor unfolding of `Centered`: writing
`α = λ + m` (`λ = α.limitPart` limit-or-zero, `m = α.natPart`), `Centered (α+2) =
CentBlock (centBase1 λ) (m+1) = centStep (CentBlock (centBase1 λ) m) = centStep (Centered (α+1))`.
Pure `Centered_lam_add_succ` + ordinal-arithmetic bookkeeping. -/
theorem ScatFun.Centered_succ_succ_eq (α : Ordinal.{0}) :
    ScatFun.Centered (α + 1 + 1) = ScatFun.centStep (ScatFun.Centered (α + 1)) := by
  set lam := α.limitPart with hlamdef
  set m := α.natPart with hmdef
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hα : α = lam + ↑m := Ordinal.eq_limitPart_add_natPart α
  have h1 : α + 1 + 1 = lam + ↑(m + 1) + 1 := by
    rw [hα, Nat.cast_add, Nat.cast_one, add_assoc lam (↑m) 1]
  have h2 : α + 1 = lam + ↑m + 1 := by rw [hα]
  rw [h1, h2, Centered_lam_add_succ hlim (m + 1), Centered_lam_add_succ hlim m]
  rfl

/-- **`\pgl G ∈ 𝒞_{α+2}`** whenever `G` is a nonempty subset of `𝒞_{α+1} ∪ ω{𝒞_{α+1}}`. Direct
from `Centered_succ_succ_eq` and the definition of `centStep` (`C ∪ (𝒫⁺(C ∪ ω C)).image pglFinset`):
`G ∈ 𝒫⁺(𝒞_{α+1} ∪ ω{𝒞_{α+1}})` exactly says `G` is nonempty and `G ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}`. -/
theorem ScatFun.pglFinset_mem_Centered_succ_succ (α : Ordinal.{0}) (G : Finset ScatFun)
    (hGne : G.Nonempty)
    (hGsub : G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1))) :
    ScatFun.pglFinset G ∈ ScatFun.Centered (α + 1 + 1) := by
  rw [Centered_succ_succ_eq, centStep]
  refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨G, ?_, rfl⟩)
  rw [nonemptySubsets, Finset.mem_erase]
  exact ⟨hGne.ne_empty, Finset.mem_powerset.mpr hGsub⟩

/-
**Intermediate form of `exists_pglFinset_decomp_of_centered_doubleSucc`.** Same statement,
but with the generators only required to lie in the full generator level `𝒢_{α+1}`
(`ScatFun.Generators (α+1)`) rather than in the smaller `𝒞_{α+1} ∪ ω{𝒞_{α+1}}`. This is the
direct output of `finitenessOfCenteredFunctions_generators` (Theorem 4.9) at rank `α+2 =
λ+(m+1)+1` (`λ = α.limitPart`, `m = α.natPart`): the `minFun` alternative is ruled out by
`CB`-rank, and the `pgl (repSeq (𝒢_{α+1}.toFinFun ∘ ι))` alternative is repackaged as
`pglFinset G` via `pgl_repSeq_equiv_pglFinset_image`.
-/
theorem ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc_generators
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (f : ScatFun) (hfrank : CBRank f.func = α + 1 + 1) (hfcent : IsCentered f.func) :
    ∃ G : Finset ScatFun, G.Nonempty ∧
      G ⊆ ScatFun.Generators (α + 1) ∧
      ScatFun.Equiv f (ScatFun.pglFinset G) := by
  -- Let `lam` be the limit part of `α` and `m` be the natural number part.
  set lam := α.limitPart
  set m := α.natPart
  have hlam : lam < omega1 := by
    exact lt_of_le_of_lt le_self_add ( Ordinal.eq_limitPart_add_natPart α ▸ hα )
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 :=
    Ordinal.limitPart_isLimit_or_zero α
  have hα_eq : α = lam + m := Ordinal.eq_limitPart_add_natPart α
  obtain ⟨k, ι, hk, hpgl⟩ := finitenessOfCenteredFunctions_generators hlam hlim (m + 1) (by
  convert hFG using 1;
  simp +arith +decide only [Nat.cast_add, Nat.cast_one, Ordinal.add_one_eq_succ, Order.succ_eq_succ_iff];
  rw [ hα_eq, Ordinal.add_succ ]) f (by
  constructor <;> norm_num [ hfrank ];
  · exact hα_eq.symm ▸ le_add_of_le_of_nonneg ( le_add_of_nonneg_right <| by norm_num ) ( by norm_num ) |> le_trans <| le_add_of_nonneg_right <| by norm_num;
  · exact hα_eq ▸ lt_of_lt_of_le ( by simp +decide ) ( le_refl _ )) hfcent;
  · obtain ⟨τ, hτ⟩ := hpgl;
    have h_contradiction : CBRank (minFun lam hlam).func = Order.succ lam :=
      minFun_cbRank_eq lam hlam
    have h_contradiction : CBRank f.func = CBRank (minFun lam hlam).func := by
      apply cbRank_eq_of_equiv;
      exact ⟨ k, ⟨ ι, hk, τ, hτ.1, hτ.2 ⟩ ⟩;
    simp_all +singlePass [ Ordinal.add_one_eq_succ ];
    exact absurd hfrank ( ne_of_gt ( Ordinal.succ_pos _ ) );
  · rename_i h;
    obtain ⟨ k, ι, hk, h ⟩ := h;
    refine ⟨ Finset.image ( ( Generators ( lam + ↑ ( m + 1 ) ) ).toFinFun ∘ ι ) Finset.univ, ?_, ?_, ?_ ⟩;
    · exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, hk ⟩ ) ⟩;
    · rw [ show α + 1 = lam + ( m + 1 ) by rw [ hα_eq ] ; simp +decide [ add_assoc ] ];
      exact Finset.image_subset_iff.mpr fun i _ => Finset.mem_toList.mp ( List.get_mem _ _ );
    · exact h.trans ( ScatFun.pgl_repSeq_equiv_pglFinset_image _ hk )

/--
**CB-rank upper bound for a finite gluing.** If every member of the list `l` has CB-rank
`≤ b`, then `glList l` has CB-rank `≤ b`. Via `gl_cbRank_eq`: `CBRank (glList l).func =
⨆ k, CBRank (l.getD k empty).func`, and each block is either a member of `l` (`≤ b`) or `empty`
(rank `0 ≤ b`).
-/
theorem ScatFun.cbRank_glList_le (l : List ScatFun) (b : Ordinal.{0})
    (hl : ∀ x ∈ l, CBRank x.func ≤ b) : CBRank (ScatFun.glList l).func ≤ b := by
  rw [ ScatFun.glList, ScatFun.gl_cbRank_eq ];
  refine ciSup_le fun k => ?_;
  by_cases hk : k < l.length <;> simp_all +decide;
  rw [ List.getD_eq_default ] <;> norm_num [ ScatFun.empty_cbRank ];
  linarith

/--
**CB-rank upper bound for centered generators.** Every element of `Centered β` has CB-rank
`≤ β` (for `β < ω₁`). Proved by induction on `β.natPart`: the base data `centBase1 λ`
(`minFun λ`, `succMaxFun λ`) has rank `λ+1`, and each `centStep` builds a `pglFinset` whose rank
is `succ (rank of glList)`, one level higher; `ω` preserves CB-rank (`gl_cbRank_eq`).
-/
theorem ScatFun.cbRank_mem_Centered_le (β : Ordinal.{0}) (_hβ : β < omega1)
    (x : ScatFun) (hx : x ∈ ScatFun.Centered β) : CBRank x.func ≤ β := by
  obtain ⟨lam, hlam⟩ : ∃ lam : Ordinal.{0}, β = lam + (β.natPart : Ordinal.{0}) ∧ Order.IsSuccLimit lam ∨ β = lam + (β.natPart : Ordinal.{0}) ∧ lam = 0 := by
    use β.limitPart;
    exact Or.imp ( fun h => ⟨ Ordinal.eq_limitPart_add_natPart β , h ⟩ )
      ( fun h => ⟨ Ordinal.eq_limitPart_add_natPart β , h ⟩ ) ( Ordinal.limitPart_isLimit_or_zero β );
  -- Apply the induction hypothesis on the natPart of β.
  have h_ind : ∀ k : ℕ, ∀ y ∈ ScatFun.CentBlock (ScatFun.centBase1 lam) k, CBRank y.func ≤ lam + (k + 1) := by
    intro k;
    induction' k with k ih;
    · simp +decide [ CentBlock, centBase1 ];
      split_ifs <;> simp +decide [ * ];
      · convert minFun_cbRank_eq 0 ‹_› |> le_of_eq;
        norm_num;
      · constructor;
        · convert minFun_cbRank_eq lam ‹_› |> le_of_eq using 1;
        · rw [ cbRank_pgl_regular ];
          · simp +decide;
            exact le_of_eq ( maxFun_cbRank_eq lam ‹_› );
          · exact scatFun_const_isRegularSeq _;
    · intro y hy
      rw [ScatFun.CentBlock] at hy;
      rcases Finset.mem_union.mp hy with ( hy | hy );
      · exact le_trans ( ih y hy ) ( by norm_cast; simp +arith +decide );
      · obtain ⟨G, hGne, hGsub, rfl⟩ : ∃ G : Finset ScatFun, G.Nonempty ∧ G ⊆ ScatFun.CentBlock (ScatFun.centBase1 lam) k ∪ ScatFun.omegaImage (ScatFun.CentBlock (ScatFun.centBase1 lam) k) ∧ y = ScatFun.pglFinset G := by
          unfold nonemptySubsets at hy; simp +decide at hy;
          exact ⟨ hy.choose, Finset.nonempty_of_ne_empty hy.choose_spec.1.1, hy.choose_spec.1.2, hy.choose_spec.2.symm ⟩;
        have hG_rank : ∀ g ∈ G, CBRank g.func ≤ lam + (k + 1) := by
          intro g hg; specialize hGsub hg; simp +decide [ omegaImage ] at hGsub;
          rcases hGsub with ( hGsub | ⟨ a, ha, rfl ⟩ );
          · exact ih g hGsub;
          · have hG_rank : CBRank (ScatFun.omega a).func = CBRank a.func := by
              rw [ ScatFun.omega, ScatFun.gl_cbRank_eq ];
              exact ciSup_const;
            exact hG_rank.symm ▸ ih a ha;
        have hG_rank : CBRank (ScatFun.glList G.toList).func ≤ lam + (k + 1) := by
          grind [cbRank_glList_le, Finset.mem_toList];
        have hG_rank : CBRank (ScatFun.pgl (fun _ : ℕ => ScatFun.glList G.toList)).func = Order.succ (CBRank (ScatFun.glList G.toList).func) := by
          exact cbRank_pgl_const (glList G.toList);
        convert hG_rank.le.trans ( Order.succ_le_succ ‹_› ) using 1;
        simp +decide [ Ordinal.add_succ ];
  by_cases h : β.natPart = 0;
  · unfold Centered at hx; aesop;
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, β.natPart = k + 1 := by
      exact Nat.exists_eq_succ_of_ne_zero h;
    convert h_ind k x _;
    · cases hlam <;> simp_all +singlePass;
    · unfold ScatFun.Centered at hx; simp +decide [ hk ] at hx;
      grind [centBase1_of_limit, Ordinal.eq_limitPart_add_natPart, Ordinal.limitPart_isLimit_or_zero, ordinal_limit_nat_decomposition_unique]

/-- **"Finite generation propagates one level up" for centered functions at a double successor**
(the genuine content of Theorem 4.9 / `finitenessOfCenteredFunctions` instantiated at rank
`α+2`, memoir `FGconsequences`, `6_double_successor_memo.tex:165`). A centered `f` of `CB`-rank
`α+2`, under `FG(<α+2)` (`ScatFun.FGBelow (α+1+1)`), is equivalent to `pglFinset G` for a
nonempty `G` of *centered-or-`ω`-regular* generators one level down, i.e. `G ⊆ 𝒞_{α+1} ∪
ω{𝒞_{α+1}}`.

**Fully proved.** The route: `exists_pglFinset_decomp_of_centered_doubleSucc_generators`
(itself via `finitenessOfCenteredFunctions_generators`, Thm 4.9, with the `minFun` alternative
ruled out by `CB`-rank) yields `f ≡ pglFinset G0` for a nonempty `G0 ⊆ Generators(α+1)`;
`pglFinset_generators_equiv_mem_Centered` transports `pglFinset G0` to a member `h` of
`Centered(α+2)`, and `Centered_succ_succ_eq` unfolds `Centered(α+2) = centStep (Centered(α+1))`
to extract the refined `G' ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}` (the `h ∈ Centered(α+1)` branch is a rank
contradiction via `cbRank_mem_Centered_le`). The conclusion is stated with `∪ ω{𝒞_{α+1}}`
(relaxed from the memoir's literal `𝒞_{α+1}`, with the author's agreement) since `pgl(ω k)`
for `k ∈ 𝒞_{α+1}` is a genuine centered rank-`α+2` function whose only decomposition uses the
`ω`-regular block `ω k ∈ ω{𝒞_{α+1}} ∖ 𝒞_{α+1}`. -/
theorem ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (f : ScatFun) (hfrank : CBRank f.func = α + 1 + 1) (hfcent : IsCentered f.func) :
    ∃ G : Finset ScatFun, G.Nonempty ∧
      G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)) ∧
      ScatFun.Equiv f (ScatFun.pglFinset G) := by
  classical
  -- Step 1: decompose `f` into a `pglFinset` of `Generators (α+1)`.
  obtain ⟨G0, hG0ne, hG0sub, hfG0⟩ :=
    ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc_generators α hα hFG f hfrank hfcent
  -- Step 2: transport `pglFinset G0` to a member `h` of `Centered (α+2)`.
  set lam := α.limitPart with hlamdef
  set m := α.natPart with hmdef
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hlamlt : lam < omega1 :=
    lt_of_le_of_lt le_self_add (Ordinal.eq_limitPart_add_natPart α ▸ hα)
  have hα_eq : α = lam + ↑m := Ordinal.eq_limitPart_add_natPart α
  have hαsucc : α + 1 = lam + ↑(m + 1) := by
    rw [hα_eq, Nat.cast_add, Nat.cast_one, add_assoc]
  have hFG' : ScatFun.FGBelow (lam + ↑(m + 1) + 1) := by rw [← hαsucc]; exact hFG
  have hG0sub' : G0 ⊆ ScatFun.Generators (lam + ↑(m + 1)) := by rw [← hαsucc]; exact hG0sub
  obtain ⟨h, hhmem, hheq⟩ :=
    ScatFun.pglFinset_generators_equiv_mem_Centered hlamlt hlim (m + 1) hFG' G0 hG0ne hG0sub'
  -- `h ∈ Centered (α+2)` and `f ≡ h`.
  have hhmem' : h ∈ ScatFun.Centered (α + 1 + 1) := by
    have : lam + ↑(m + 1) + 1 = α + 1 + 1 := by rw [← hαsucc]
    rwa [this] at hhmem
  have hfh : ScatFun.Equiv f h := hfG0.trans hheq
  -- Step 3: `Centered (α+2) = centStep (Centered (α+1))`; dispatch.
  rw [ScatFun.Centered_succ_succ_eq, ScatFun.centStep, Finset.mem_union] at hhmem'
  rcases hhmem' with hcent | himg
  · -- `h ∈ Centered (α+1)`: rank contradiction.
    exfalso
    have hrank_le : CBRank h.func ≤ α + 1 :=
      ScatFun.cbRank_mem_Centered_le (α + 1) (by simpa using omega1_add_nat α hα 1) h hcent
    have hrank_eq : CBRank h.func = α + 1 + 1 := by
      rw [← cbRank_eq_of_equiv hfh]; exact hfrank
    rw [hrank_eq] at hrank_le
    exact (lt_irrefl _ (lt_of_lt_of_le (Order.lt_succ (α + 1)) hrank_le))
  · -- `h = pglFinset G'`: extract `G'`.
    rw [Finset.mem_image] at himg
    obtain ⟨G', hG'mem, hG'eq⟩ := himg
    rw [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset] at hG'mem
    refine ⟨G', Finset.nonempty_iff_ne_empty.mpr hG'mem.1, hG'mem.2, ?_⟩
    rw [hG'eq]; exact hfh

/-- **Phase A (setup)** (`6_double_successor_memo.tex:161-166`). Fix a fine `c`-partition `𝒫`
with `Y_𝒫 = {y}`. Then there is `g ∈ 𝒞_{α+2}` and a nonempty `G ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}` with
`g ≡ \pgl G` and `f↾P ≡ g` for every `P ∈ 𝒫`.

The body is now fully assembled around the single open structure lemma
`exists_pglFinset_decomp_of_centered_doubleSucc`: from `exists_rep` get a centered representative
`f̂` with `f↾P ≡ f̂` for all `P`; its `CB`-rank is `α+2` because every piece has rank `CB(f̂)`
(pairwise-equivalence `hpc.2.2`) and `cbRank_restrict_sUnion_const` glues that back to
`CB(F.restrict univ) = CB(F) = α+2` (`⋃₀ Part = univ`); the structure lemma then gives `G` with
`f̂ ≡ pglFinset G`, and `g := pglFinset G` lands *literally* in `𝒞_{α+2}` by
`pglFinset_mem_Centered_succ_succ`. -/
theorem verticalTheorem_setup
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y) :
    ∃ (g : ScatFun) (G : Finset ScatFun),
      g ∈ ScatFun.Centered (α + 1 + 1) ∧ G.Nonempty ∧
        G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)) ∧
        ScatFun.Equiv g (ScatFun.pglFinset G) ∧ ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g := by
  obtain ⟨fhat, hfhat_cent, hfhat_equiv⟩ := hpc.exists_rep
  -- A distinguished piece `P₀ ∈ Part` (from `y ∈ Y_𝒫 = {y}`).
  have hy : y ∈ hA.cocenterSet := by rw [hpc.2.1]; rfl
  obtain ⟨p₀, -⟩ := hy
  -- Every piece has `CB`-rank `α+2`, hence so does `f̂`.
  have hpieces_rank : ∀ P ∈ Part, CBRank (F.restrict P).func = CBRank (F.restrict p₀.1).func :=
    fun P hP => cbRank_eq_of_equiv (hpc.2.2 P hP p₀.1 p₀.2)
  have hsUnion : CBRank (F.restrict (⋃₀ Part)).func = CBRank (F.restrict p₀.1).func :=
    cbRank_restrict_sUnion_const hA.countable hA.isClopen ⟨p₀.1, p₀.2⟩ hpieces_rank
  have hrank_univ : CBRank (F.restrict (Set.univ : Set ↑F.domain)).func = CBRank F.func := by
    rw [cbRank_restrict_eq]
    exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
  have hp₀_rank : CBRank (F.restrict p₀.1).func = α + 1 + 1 := by
    rw [← hsUnion, hA.sUnion_eq, hrank_univ, hFrank]
  have hfhat_rank : CBRank fhat.func = α + 1 + 1 := by
    rw [← cbRank_eq_of_equiv (hfhat_equiv p₀.1 p₀.2), hp₀_rank]
  obtain ⟨G, hGne, hGsub, hfhat_pgl⟩ :=
    ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc α hα hFG fhat hfhat_rank hfhat_cent
  exact ⟨ScatFun.pglFinset G, G,
    ScatFun.pglFinset_mem_Centered_succ_succ α G hGne hGsub, hGne, hGsub,
    ScatFun.Equiv.refl _, fun P hP => (hfhat_equiv P hP).trans hfhat_pgl⟩

/-- **Phase B (easy case)** (`6_double_successor_memo.tex:168-171`): if every ray of `F` at `y`
reduces into a finite gluing of `G`, then `F` reduces into `g`. This is the degenerate branch
of the Vertical Theorem needing no `𝒲`-obstruction `H` at all (`H = ∅` in `verticalTheorem`'s
assembly below). **Fully proved**, chaining three already-proved facts: every function reduces
into the pointed gluing of its own rays at any point (`centeredAsPgluing_forward`, memoir
`Pgluingasupperbound` — general, no centeredness of `F` needed, unlike its use for the
`𝒫`-pieces elsewhere in the proof), pointwise-bounded pointed gluings compose
(`ScatFun.finitegenerationAndPgluing_upper`), and `\pgl (repSeq G) ≡ \pgl G`
(`ScatFun.pglFinset_equiv_pgl_repSeq`). -/
theorem verticalTheorem_easyCase
    (F : ScatFun) (y : Baire) {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (heasy : ∀ j : ℕ, ∃ h ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.rayOn y Set.univ j) h) :
    ScatFun.Reduces F g := by
  have h1 : ScatFun.Reduces F (ScatFun.pgl (fun j => F.rayOn y Set.univ j)) :=
    centeredAsPgluing_forward F y
  have h2 : ScatFun.Reduces (ScatFun.pgl (fun j => F.rayOn y Set.univ j))
      (ScatFun.pgl (ScatFun.repSeq G.toFinFun)) :=
    ScatFun.finitegenerationAndPgluing_upper G.toFinFun (fun j => F.rayOn y Set.univ j) heasy
  have h3 : ScatFun.Reduces (ScatFun.pgl (ScatFun.repSeq G.toFinFun)) (ScatFun.pglFinset G) :=
    (ScatFun.pglFinset_equiv_pgl_repSeq G).2
  exact h1.trans (h2.trans (h3.trans hgequiv.2))

/-- **Phase D, assembled.** Every ray of `F` at the common cocenter `y` of a pseudo-centered
`c`-partition reduces into `g` (memoir, `6_double_successor_memo.tex:190-191`, generalized to
hold unconditionally, not just for `H`'s members — this is *not* the easy-case hypothesis
`heasy`, which needs a single *fixed-multiplicity* `FinGl G` bound, genuinely stronger).

`Set.Countable.exists_eq_range` only gives a surjective (possibly repeating) `f : ℕ → Set
↑F.domain` onto `Part`; `disjointed f` (`Mathlib.Order.Disjointed`) turns this into a genuine
pairwise-disjoint `IsDisjointUnion`, and since `Part`'s own pieces are already pairwise disjoint
from each other, `disjointed f i` is provably either `∅` (a repeat) or the full `f i` (`hAor`).
Chains `rayOn_reduces_gl_of_domain_partition` (D2, ray of `F` = disjoint union of piece-rays),
`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset` (D1, piece-ray ↦ `FinGl G`),
`finGl_reduces_omega_glList` (`FinGl G` member ↦ `ω(glList G.toList)`), and
`gl_const_omega_equiv` (collapsing the resulting countable `gl` of `ω G`'s back to a single
`ω G`), finishing via `gl_reduces_pgl_direct` (`ω G ≤ pglFinset G`) and `hgequiv.symm`. -/
theorem verticalTheorem_hardCase_rayOn_reduces_omegaG
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hy : y ∈ hA.cocenterSet) (hcocset : hA.cocenterSet = {y})
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g) (j : ℕ) :
    ScatFun.Reduces (F.rayOn y Set.univ j) (ScatFun.omega (ScatFun.glList G.toList)) := by
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := hy
  obtain ⟨f, hf⟩ := hA.countable.exists_eq_range ⟨P₀, hP₀⟩
  have hfmem : ∀ i, f i ∈ Part := fun i => hf ▸ Set.mem_range_self i
  set A : ℕ → Set ↑F.domain := disjointed f with hAdef
  have hAsub : ∀ i, A i ⊆ f i := fun i => disjointed_subset f i
  have hAor : ∀ i, A i = ∅ ∨ A i = f i := by
    intro i
    rw [hAdef, disjointed_eq_inter_compl]
    by_cases hex : ∃ k, k < i ∧ f k = f i
    · left
      obtain ⟨k, hki, hfk⟩ := hex
      refine' Set.eq_empty_iff_forall_notMem.mpr (fun x ⟨hx1, hx2⟩ => _)
      exact (Set.mem_iInter₂.mp hx2 k hki) (hfk ▸ hx1 : x ∈ f k)
    · right
      push_neg at hex
      refine' Set.inter_eq_left.mpr (fun x hx => Set.mem_iInter₂.mpr (fun k hki hxfk => _))
      exact (Set.disjoint_left.mp (hA.pairwiseDisjoint (hfmem k) (hfmem i) (hex k hki)) hxfk) hx
  have hdu : F.IsDisjointUnion A := by
    refine ⟨fun i => ?_, fun i i' hii' => disjoint_disjointed f hii', ?_⟩
    · rw [hAdef, disjointed_eq_inter_compl]
      have hIioeq : {j : ℕ | j < i} = ↑(Finset.range i) := by ext k; simp
      have hcl : IsClopen (⋂ j ∈ Finset.range i, (f j)ᶜ) :=
        isClopen_biInter_finset (fun k _ => (hA.isClopen (f k) (hfmem k)).compl)
      refine (hA.isClopen (f i) (hfmem i)).inter ?_
      convert hcl using 2 with j
      simp [Finset.mem_range]
    · rw [hAdef, iUnion_disjointed]
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hxmem : x ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; trivial
      obtain ⟨P, hP, hxP⟩ := hxmem
      rw [hf] at hP
      obtain ⟨i, rfl⟩ := hP
      exact ⟨i, hxP⟩
  have hstep2 : ∀ i, ScatFun.Reduces (F.restrict (A i)) g := by
    intro i
    rcases hAor i with h0 | heq
    · rw [h0]
      have : IsEmpty ↑(F.restrict (∅ : Set ↑F.domain)).domain :=
        Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])
      exact ScatFun.reduces_of_isEmpty_domain this
    · rw [heq]; exact (hgP (f i) (hfmem i)).1
  have hstep1 : ScatFun.Reduces (F.rayOn y Set.univ j)
      (ScatFun.gl (fun i => (F.restrict (A i)).rayOn y Set.univ j)) :=
    ScatFun.rayOn_reduces_gl_of_domain_partition F A hdu y j
  have hstep3 : ∀ i, ScatFun.Reduces ((F.restrict (A i)).rayOn y Set.univ j)
      (ScatFun.omega (ScatFun.glList G.toList)) := by
    intro i
    rcases hAor i with h0 | heq
    · have hdom0 : (F.restrict (A i)).domain = ∅ := by rw [h0]; ext x; simp [ScatFun.restrict]
      have hempty0 : IsEmpty ↑(F.restrict (A i)).domain := Set.isEmpty_coe_sort.mpr hdom0
      have hemptyray : IsEmpty ↑((F.restrict (A i)).rayOn y Set.univ j).domain := by
        rw [Set.isEmpty_coe_sort, rayOn_eq_corestrict, Set.eq_empty_iff_forall_notMem]
        rintro z ⟨h, -⟩
        exact hempty0.elim ⟨z, h⟩
      exact ScatFun.reduces_of_isEmpty_domain hemptyray
    · rw [heq]
      have hPcent : IsCentered (F.restrict (f i)).func := hA.centered (f i) (hfmem i)
      have hycoc : cocenter (F.restrict (f i)).func hPcent = y := by
        have hmem : hA.cocenterOf (hfmem i) ∈ hA.cocenterSet := ⟨⟨f i, hfmem i⟩, rfl⟩
        rw [hcocset, Set.mem_singleton_iff] at hmem
        rw [← hmem]; rfl
      obtain ⟨h, hhmem, hhred⟩ := hycoc ▸
        ScatFun.rayOn_cocenter_reduces_finGl_of_equiv_pglFinset (F.restrict (f i)) hPcent G
          ((hgP (f i) (hfmem i)).trans hgequiv) j
      exact hhred.trans (ScatFun.finGl_reduces_omega_glList hhmem)
  have hstep4 : ScatFun.Reduces (F.rayOn y Set.univ j)
      (ScatFun.gl (fun _ : ℕ => ScatFun.omega (ScatFun.glList G.toList))) :=
    hstep1.trans (ScatFun.gl_reduces_of_pointwise _ _ hstep3)
  have hcollapse : ScatFun.Reduces
      (ScatFun.gl (fun _ : ℕ => ScatFun.omega (ScatFun.glList G.toList)))
      (ScatFun.omega (ScatFun.glList G.toList)) :=
    (ScatFun.gl_const_omega_equiv (ScatFun.glList G.toList)).1
  exact hstep4.trans hcollapse

/-- **`ω(glList G) ≤ pglFinset G`.** The plain-gluing tower of `glList G` embeds, block-by-block
into distinct copies, of the pointed gluing `pglFinset G = pgl(fun _ => glList G.toList)`
(`gl_reduces_pgl_direct` with `e = id`). -/
theorem ScatFun.omega_glList_reduces_pglFinset (G : Finset ScatFun) :
    ScatFun.Reduces (ScatFun.omega (ScatFun.glList G.toList)) (ScatFun.pglFinset G) := by
  obtain ⟨σ, τ, hσ, heqfun, hτ, -, -⟩ :=
    ScatFun.gl_reduces_pgl_direct (fun _ => ScatFun.glList G.toList)
      (fun _ => ScatFun.glList G.toList) id Function.injective_id (fun _ => Or.inl rfl)
  exact ⟨σ, hσ, τ, hτ, heqfun⟩

/-- **Phase D** (`6_double_successor_memo.tex:190-191`), `g`-form. Every ray of `F` at `y` reduces
into `g`, chaining `verticalTheorem_hardCase_rayOn_reduces_omegaG` (ray `≤ ω G`) with
`omega_glList_reduces_pglFinset` (`ω G ≤ \pgl G`) and `hgequiv.2` (`\pgl G ≡ g`). **Fully proved.** -/
theorem verticalTheorem_hardCase_rayOn_reduces_g
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hy : y ∈ hA.cocenterSet) (hcocset : hA.cocenterSet = {y})
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g) (j : ℕ) :
    ScatFun.Reduces (F.rayOn y Set.univ j) g :=
  (verticalTheorem_hardCase_rayOn_reduces_omegaG hA y hy hcocset hgequiv hgP j).trans
    ((ScatFun.omega_glList_reduces_pglFinset G).trans hgequiv.2)

/-- **`𝒲_{α+1} ⊆ 𝒲_{α+2}`.** The `𝒲`-reference set is monotone across a natural successor:
`omegaRegularSet (α+1)` and `omegaRegularSet (α+2)` share the same limit part `α.limitPart`
(hence the same `ℓ_λ = maxFun`), and `Centered (α+1) ⊆ Centered (α+2)`
(`Centered_add_nat_subset_succ`) makes the `ω`-image half monotone. Needed in Phase C to feed
`H`-members (living in `𝒲_{α+1}`) into the `𝒲`-regularity of the rank-`α+2` piece
`f_{(f̂,y)}`. -/
lemma omegaRegularSet_add_one_subset (α : Ordinal.{0})
    (h1 : α + 1 < omega1) (h2 : α + 1 + 1 < omega1) :
    omegaRegularSet (α + 1) h1 ⊆ omegaRegularSet (α + 1 + 1) h2 := by
  set lam := α.limitPart with hlamdef
  set m := α.natPart with hmdef
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hα : α = lam + ↑m := Ordinal.eq_limitPart_add_natPart α
  have e1 : α + 1 = lam + ↑(m + 1) := by rw [hα, Nat.cast_add, Nat.cast_one, add_assoc]
  have hlp1 : (α + 1).limitPart = lam := by
    rw [e1]; exact Ordinal.limitPart_add_natCast lam (m + 1) hlim
  have hlp2 : (α + 1 + 1).limitPart = lam := by
    rw [show α + 1 + 1 = lam + ↑(m + 1) + 1 by rw [e1], add_assoc, ← Nat.cast_succ]
    exact Ordinal.limitPart_add_natCast lam (m + 1 + 1) hlim
  have hCsub : ScatFun.Centered (α + 1) ⊆ ScatFun.Centered (α + 1 + 1) := by
    rw [e1]; exact ScatFun.Centered_add_nat_subset_succ hlim (m + 1)
  intro x hx
  rw [omegaRegularSet, Finset.mem_insert] at hx
  rw [omegaRegularSet, Finset.mem_insert]
  rcases hx with hxmax | hximg
  · left
    rw [hxmax]
    have hmax : ∀ (p1 : (α + 1).limitPart < omega1) (p2 : (α + 1 + 1).limitPart < omega1),
        ScatFun.maxFun (α + 1).limitPart p1 = ScatFun.maxFun (α + 1 + 1).limitPart p2 := by
      rw [hlp1, hlp2]; intro p1 p2; rfl
    exact hmax _ _
  · right
    rw [Finset.mem_image] at hximg ⊢
    obtain ⟨h, hhC, rfl⟩ := hximg
    exact ⟨h, hCsub hhC, rfl⟩

/-- **C1: obstruction sets of `𝒲_{α+1}`-members are infinite or empty.** For a pseudo-centered
`F` of rank `α+2`, every `w ∈ 𝒲_{α+1}` has ray-index obstruction set `{j | w ≤ ray_j(F)}` empty
or infinite. This is exactly the `𝒲`-regularity of the piece `f_{(f̂,y)}` at rank `α+2`
(`hpc.1.1 : ¬ IsLump f̂ y`, i.e. `IsOmegaRegularAt`), transported to `F`: in the pseudo-centered
case `blockPieces f̂ y = Part`, so `piece f̂ y = F.restrict univ ≡ F` (rays and rank match), and
`𝒲_{α+1} ⊆ 𝒲_{α+2} = 𝒲_{CB(piece)}` (`omegaRegularSet_add_one_subset`). Used in Phase C: an
`H`-member has *nonempty* obstruction set (by definition of `H`), hence infinite, which is what
lets the ray index be pushed into the tail so `RaySet_j ⊆ U`. -/
lemma pseudoCentered_obstruction_infinite_or_empty
    {α : Ordinal.{0}} (hα : α < omega1)
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    (w : ScatFun)
    (hw : w ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1)) :
    {j : ℕ | ScatFun.Reduces w (F.rayOn y Set.univ j)}.Infinite ∨
      {j : ℕ | ScatFun.Reduces w (F.rayOn y Set.univ j)} = ∅ := by
  have hα1 : α + 1 < omega1 := by simpa using omega1_add_nat α hα 1
  have hα2 : α + 1 + 1 < omega1 := by simpa using omega1_add_nat (α + 1) hα1 1
  obtain ⟨fhat, hfhat_cent, hfhat_equiv⟩ := hpc.exists_rep
  have hy : y ∈ hA.cocenterSet := by rw [hpc.2.1]; rfl
  -- Every piece has cocenter `y`, so `blockPieces f̂ y = Part`.
  have hcocy : ∀ P (hP : P ∈ Part), hA.cocenterOf hP = y := by
    intro P hP
    have hmem : hA.cocenterOf hP ∈ hA.cocenterSet := ⟨⟨P, hP⟩, rfl⟩
    rw [hpc.2.1, Set.mem_singleton_iff] at hmem; exact hmem
  have hbp : hA.blockPieces fhat y = Part := by
    ext P
    constructor
    · rintro ⟨hP, -, -⟩; exact hP
    · intro hP; exact ⟨hP, hfhat_equiv P hP, hcocy P hP⟩
  have hpiece_eq : hA.piece fhat y = F.restrict (Set.univ : Set ↑F.domain) := by
    rw [ScatFun.IsCPartition.piece, hbp, hA.sUnion_eq]
  have hrank_univ : CBRank (F.restrict (Set.univ : Set ↑F.domain)).func = CBRank F.func := by
    rw [cbRank_restrict_eq]
    exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
  have hpiece_rank : CBRank (hA.piece fhat y).func = α + 1 + 1 := by
    rw [hpiece_eq, hrank_univ, hFrank]
  -- `¬ IsLump f̂ y` gives `𝒲`-regularity of the piece.
  have hreg : IsOmegaRegularAt (hA.piece fhat y) y := by
    by_contra hc
    exact hpc.1.1 fhat y ⟨hy, hfhat_cent, hc⟩
  -- Feed `w` into the piece's `𝒲`-regularity: `𝒲_{α+1} ⊆ 𝒲_{α+2} = 𝒲_{CB(piece)}`.
  have hwmem2 : w ∈ omegaRegularSet (α + 1 + 1) hα2 :=
    omegaRegularSet_add_one_subset α hα1 hα2 hw
  have hwmem_piece : w ∈ omegaRegularSet (CBRank (hA.piece fhat y).func)
      (CBRank_lt_omega1 (hA.piece fhat y).hScat) := by
    rw [omegaRegularSet_congr hpiece_rank (CBRank_lt_omega1 (hA.piece fhat y).hScat) hα2]
    exact hwmem2
  have hreg_w := hreg w hwmem_piece
  -- Transport the obstruction set from the piece back to `F`.
  have hset_eq : {j : ℕ | ScatFun.Reduces w ((hA.piece fhat y).rayOn y Set.univ j)}
      = {j : ℕ | ScatFun.Reduces w (F.rayOn y Set.univ j)} := by
    ext j
    simp only [Set.mem_setOf_eq]
    rw [hpiece_eq]
    exact ⟨fun h => h.trans (ScatFun.rayOn_restrict_equiv F Set.univ y j).1,
      fun h => h.trans (ScatFun.rayOn_restrict_equiv F Set.univ y j).2⟩
  rwa [hset_eq] at hreg_w

/-- **Injective choice of arbitrarily large representatives.** Given a family `O : ℕ → Set ℕ` of
infinite index sets and a threshold `N`, there is a strictly increasing `idx : ℕ → ℕ` with
`idx n ∈ O n` and `idx n ≥ N` for every `n`. Built by the obvious greedy recursion: pick each
`idx n` above both `N` and the previous value, always possible since each `O n` is infinite hence
unbounded (`Set.Infinite.exists_gt`). `StrictMono` gives the injectivity Phase C needs (distinct
ray indices ⟹ disjoint rays). -/
lemma exists_strictMono_forall_mem {O : ℕ → Set ℕ} (hO : ∀ n, (O n).Infinite) (N : ℕ) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ n, N ≤ idx n ∧ idx n ∈ O n := by
  have hnext : ∀ (n b : ℕ), ∃ m, b < m ∧ N ≤ m ∧ m ∈ O n := by
    intro n b
    obtain ⟨m, hm, hlt⟩ := (hO n).exists_gt (max b N)
    exact ⟨m, lt_of_le_of_lt (le_max_left _ _) hlt,
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hlt), hm⟩
  choose next hnext1 hnext2 hnext3 using hnext
  set idx : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) n with hidx
  refine ⟨idx, strictMono_nat_of_lt_succ (fun n => hnext1 (n + 1) (idx n)), fun n => ?_⟩
  cases n with
  | zero => exact ⟨hnext2 0 0, hnext3 0 0⟩
  | succ k => exact ⟨hnext2 (k + 1) (idx k), hnext3 (k + 1) (idx k)⟩

/-- **A clopen neighbourhood of `y` swallows all sufficiently late rays.** For clopen `U ∋ y`
there is `M` with `RaySet univ y j ⊆ U` for every `j ≥ M`: `U` contains a basic prefix cylinder
`{z | ∀ l < M, z l = y l}` (clopen-nbhd basis), and any point of the `j`-th ray (`j ≥ M`) agrees
with `y` on `[0, j) ⊇ [0, M)`, so lands in that cylinder. The nbhd extraction is the same idiom
as `infinite_reduces_stable_under_corestrict` (`Fine.lean`). Phase C uses this to force the
chosen ray indices into the tail so that `W = ⋃ RaySet ⊆ U`. -/
lemma exists_tail_raySet_subset (y : Baire) (U : Set Baire) (hU : IsClopen U) (hyU : y ∈ U) :
    ∃ M : ℕ, ∀ j, M ≤ j → RaySet Set.univ y j ⊆ U := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Set.Ici M ⊆ {j : ℕ | ∀ z : ℕ → ℕ, (∀ l < j, z l = y l) → z ∈ U} := by
    have hmem := hU.2.mem_nhds hyU
    rw [mem_nhds_iff] at hmem
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hmem
    rcases (isOpen_pi_iff.mp ht₂) y ht₃ with ⟨s, hs⟩
    use s.sup id + 1
    intro j hj
    simp_all +decide [Set.subset_def]
    exact fun z hz => ht₁ _ (hs.choose_spec.2 _ fun i hi => by
      simpa [hz i (lt_of_le_of_lt (Finset.le_sup (f := id) hi) hj)] using hs.choose_spec.1 i hi)
  refine ⟨M, fun j hj z hz => hM (Set.mem_Ici.mpr hj) z ?_⟩
  exact hz.2.1

/-- **C3: block-matching of `\gl L` into a disjoint union of rays.** If each block `L n` reduces
into `ray_{idx n}(F)` for a *strictly increasing* `idx` (so the ray indices are distinct), then
`\gl L` reduces into `F` corestricted to `W = ⋃_{n < |L|} RaySet_{idx n}`. Since distinct ray
indices give *disjoint* rays (`firstDiff_eq_of_mem`), the block `L n` is routed into its own
disjoint clopen slice of `F⇂W`; `gl_coRestrict_disjoint_open_reduces` assembles the slices.
This is the clean substitute for the memoir's `Intertwinereductionsforomegacentered` packing
step — the injective index choice does the disjointifying, so no intertwine-set argument is
needed. -/
lemma glList_reduces_coRestrict_biUnion_rays
    (F : ScatFun) (y : Baire) (L : List ScatFun) (idx : ℕ → ℕ) (hidx : StrictMono idx)
    (hred : ∀ n, n < L.length →
      ScatFun.Reduces (L.getD n ScatFun.empty) (F.rayOn y Set.univ (idx n))) :
    ScatFun.Reduces (ScatFun.glList L)
      (F.coRestrict (⋃ n ∈ Finset.range L.length, RaySet Set.univ y (idx n))) := by
  set k := L.length with hk
  set W := ⋃ n ∈ Finset.range k, RaySet Set.univ y (idx n) with hWdef
  set V : ℕ → Set Baire := fun n => if n < k then RaySet Set.univ y (idx n) else ∅ with hVdef
  have hVopen : ∀ n, IsOpen (V n) := by
    intro n
    simp only [hVdef]
    by_cases hn : n < k
    · simp only [if_pos hn]; exact (isClopen_raySet y (idx n)).2
    · simp only [if_neg hn]; exact isOpen_empty
  have hVdisj : Pairwise (Disjoint on V) := by
    intro i j hij
    simp only [Function.onFun, hVdef]
    by_cases hi : i < k
    · by_cases hj : j < k
      · simp only [if_pos hi, if_pos hj, Set.disjoint_left]
        intro z hzi hzj
        have h1 := firstDiff_eq_of_mem y z (idx i) hzi
        have h2 := firstDiff_eq_of_mem y z (idx j) hzj
        exact hij (hidx.injective (h1.symm.trans h2))
      · simp only [if_neg hj, Set.disjoint_empty]
    · simp only [if_neg hi, Set.empty_disjoint]
  have hstep1 : ScatFun.Reduces (ScatFun.glList L)
      (ScatFun.gl (fun n => (F.coRestrict W).coRestrict (V n))) := by
    show ScatFun.Reduces (ScatFun.gl (fun n => L.getD n ScatFun.empty)) _
    refine ScatFun.gl_reduces_of_pointwise _ _ (fun n => ?_)
    by_cases hn : n < k
    · have hVn : V n = RaySet Set.univ y (idx n) := by simp only [hVdef, if_pos hn]
      have hb : ScatFun.Reduces (L.getD n ScatFun.empty)
          (F.restrict {z : ↑F.domain | F.func z ∈ V n}) := by
        have hr := hred n hn
        rw [rayOn_eq_corestrict] at hr
        rwa [← hVn] at hr
      have hsub : {z : ↑F.domain | F.func z ∈ V n} ⊆ {z : ↑F.domain | F.func z ∈ W} := by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        rw [hVn] at hz
        exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr hn, hz⟩
      have he := ScatFun.restrict_restrict_equiv F {z | F.func z ∈ W} {z | F.func z ∈ V n} hsub
      exact hb.trans he.2
    · have hval : L.getD n ScatFun.empty = ScatFun.empty :=
        List.getD_eq_default L ScatFun.empty (not_lt.mp hn)
      rw [hval]
      exact ScatFun.empty_reduces _
  exact hstep1.trans (ScatFun.gl_coRestrict_disjoint_open_reduces (F.coRestrict W) V hVopen hVdisj)

/-!
### Hard-case phase lemmas (Phases C, E, F)

The genuinely double-successor-specific steps of the Vertical Theorem's hard case, extracted as
standalone statement-lemmas (mirroring the Phase D extraction
`verticalTheorem_hardCase_rayOn_reduces_g` above) so the main theorem's body assembles them.
Phase C (`verticalTheorem_hardCase_C`) is **fully proved** (see the C1/C3 helpers just above), as
is Phase E+F (`verticalTheorem_hardCase_split`); all hard-case phase lemmas are now proved.
`H` is the memoir's
obstruction set `{h ∈ 𝒲_{α+1} | h ≰ FinGl G ∧ ∃ j, h ≤ ray_j(f)}` and `w = \gl H` is
`glList H.toList`.
-/

/-- **Phase C** (`6_double_successor_memo.tex:180-187`): `w ≤ f⇂W` for a clopen `W` with
`y ∉ W ⊆ U`. **Fully proved.** Every `h ∈ H` has infinite ray-index obstruction set (nonempty by
`hHray`, hence infinite by `pseudoCentered_obstruction_infinite_or_empty` — the `𝒲`-regularity of
the rank-`α+2` piece, since `hpc.1 : IsFine` forbids lumps). This lets us pick, via
`exists_strictMono_forall_mem`, a *strictly increasing* index `idx n` for each list position `n`
with `H.toList[n] ≤ ray_{idx n}(f)` and `idx n ≥ M`, where `M` is the tail threshold past which
`RaySet_j ⊆ U` (`exists_tail_raySet_subset`). Then `W = ⋃_{n < |H|} RaySet_{idx n} ⊆ U` is clopen
with `y ∉ W`, and `glList_reduces_coRestrict_biUnion_rays` (C3) gives `\gl H ≤ f⇂W` by routing the
distinct blocks into the disjoint rays — replacing the memoir's
`Intertwinereductionsforomegacentered` packing step with an injective index choice. -/
theorem verticalTheorem_hardCase_C
    {α : Ordinal.{0}} (hα : α < omega1)
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    (H : Finset ScatFun)
    (hHsub : H ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1))
    (hHray : ∀ h ∈ H, ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (U : Set Baire) (hU : IsClopen U) (hyU : y ∈ U) :
    ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
      ScatFun.Reduces (ScatFun.glList H.toList) (F.coRestrict W) := by
  classical
  -- Tail threshold: `RaySet_j ⊆ U` for `j ≥ M`.
  obtain ⟨M, htail⟩ := exists_tail_raySet_subset y U hU hyU
  -- Obstruction sets of all list positions are infinite.
  set O : ℕ → Set ℕ :=
    fun n => {j : ℕ | ScatFun.Reduces (H.toList.getD n ScatFun.empty) (F.rayOn y Set.univ j)}
    with hOdef
  have hOinf : ∀ n, (O n).Infinite := by
    intro n
    by_cases hn : n < H.toList.length
    · have hmemH : H.toList.getD n ScatFun.empty ∈ H := by
        rw [List.getD_eq_getElem _ _ hn]; exact Finset.mem_toList.mp (List.getElem_mem hn)
      rcases pseudoCentered_obstruction_infinite_or_empty hα hFrank hA y hpc
          (H.toList.getD n ScatFun.empty) (hHsub hmemH) with hinf | hempty
      · exact hinf
      · exfalso
        obtain ⟨j, hj⟩ := hHray _ hmemH
        rw [Set.eq_empty_iff_forall_notMem] at hempty
        exact hempty j hj
    · have hval : O n = Set.univ := by
        rw [hOdef]; ext j
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [List.getD_eq_default _ _ (not_lt.mp hn)]
        exact ScatFun.empty_reduces _
      rw [hval]; exact Set.infinite_univ
  -- Strictly increasing index choice with `idx n ∈ O n` and `idx n ≥ M`.
  obtain ⟨idx, hidx, hidxspec⟩ := exists_strictMono_forall_mem hOinf M
  set W : Set Baire := ⋃ n ∈ Finset.range H.toList.length, RaySet Set.univ y (idx n) with hWdef
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact Set.iUnion₂_subset (fun n _ => htail (idx n) (hidxspec n).1)
  · exact isClopen_biUnion_finset (fun n _ => isClopen_raySet y (idx n))
  · intro hymem
    rw [hWdef, Set.mem_iUnion₂] at hymem
    obtain ⟨n, _, hy⟩ := hymem
    exact hy.2.2 rfl
  · exact glList_reduces_coRestrict_biUnion_rays F y H.toList idx hidx
      (fun n _ => (hidxspec n).2)

/-- **A `c`-partition can be enumerated as a disjoint clopen `ℕ`-family.** From any piece
`P₀ ∈ Part` (a nonempty witness), `Set.Countable.exists_eq_range` + `disjointed` produce
`A : ℕ → Set ↑F.domain` that is a genuine `IsDisjointUnion` of `F` with each `A i` either a
piece of `Part` or `∅` (a repeat killed by `disjointed`). The same idiom already used inline in
`verticalTheorem_hardCase_rayOn_reduces_omegaG`; extracted here for reuse by the Phase E+F
diagonal split. -/
lemma exists_partition_enumeration {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (P₀ : Set ↑F.domain) (hP₀ : P₀ ∈ Part) :
    ∃ A : ℕ → Set ↑F.domain, F.IsDisjointUnion A ∧ (∀ i, A i ∈ Part ∨ A i = ∅) ∧ A 0 ∈ Part := by
  obtain ⟨f, hf⟩ := hA.countable.exists_eq_range ⟨P₀, hP₀⟩
  have hfmem : ∀ i, f i ∈ Part := fun i => hf ▸ Set.mem_range_self i
  refine ⟨disjointed f, ?_, ?_, by rw [disjointed_zero]; exact hfmem 0⟩
  · refine ⟨fun i => ?_, fun i i' hii' => disjoint_disjointed f hii', ?_⟩
    · rw [disjointed_eq_inter_compl]
      have hcl : IsClopen (⋂ jj ∈ Finset.range i, (f jj)ᶜ) :=
        isClopen_biInter_finset (fun k _ => (hA.isClopen (f k) (hfmem k)).compl)
      refine (hA.isClopen (f i) (hfmem i)).inter ?_
      convert hcl using 2 with jj
      simp [Finset.mem_range]
    · rw [iUnion_disjointed]
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hxmem : x ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; trivial
      obtain ⟨P, hP, hxP⟩ := hxmem
      rw [hf] at hP
      obtain ⟨i, rfl⟩ := hP
      exact ⟨i, hxP⟩
  · intro i
    by_cases hex : ∃ k, k < i ∧ f k = f i
    · right
      rw [disjointed_eq_inter_compl]
      obtain ⟨k, hki, hfk⟩ := hex
      refine' Set.eq_empty_iff_forall_notMem.mpr (fun x ⟨hx1, hx2⟩ => _)
      exact (Set.mem_iInter₂.mp hx2 k hki) (hfk ▸ hx1 : x ∈ f k)
    · left
      have heq : disjointed f i = f i := by
        rw [disjointed_eq_inter_compl]
        push_neg at hex
        refine' Set.inter_eq_left.mpr (fun x hx => Set.mem_iInter₂.mpr (fun k hki hxfk => _))
        exact (Set.disjoint_left.mp (hA.pairwiseDisjoint (hfmem k) (hfmem i) (hex k hki)) hxfk) hx
      rw [heq]; exact hfmem i

/-- `f^{[j]}`'s domain set (memoir `6_double_successor_memo.tex:194`,
`f^{[j]} = ⊔_{i>j} ray_j(f_i)`): points lying in some late block `A i` (`i > j`) whose `F`-value
is in the `j`-th ray at `y`, so that `f^{[j]} = F.restrict (diagBracketSet A y j)`. -/
def diagBracketSet {F : ScatFun} (A : ℕ → Set ↑F.domain) (y : Baire) (j : ℕ) : Set ↑F.domain :=
  (⋃ i, ⋃ (_ : j < i), A i) ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y j}

/--
A set `S` is clopen provided its intersection with every block `A i` of a disjoint union is
clopen. The blocks are clopen and cover `F.domain`, so openness/closedness can be checked
block-by-block: `S = ⋃ i, S ∩ A i` is open, and `Sᶜ = ⋃ i, (A i \ S)` is open too.
-/
lemma ScatFun.isClopen_of_inter_blocks {F : ScatFun} {A : ℕ → Set ↑F.domain}
    (hdu : F.IsDisjointUnion A) {S : Set ↑F.domain} (h : ∀ i, IsClopen (S ∩ A i)) :
    IsClopen S := by
  constructor;
  · have h_union : Sᶜ = ⋃ i, (A i \ S) := by
      have := hdu.2; simp_all +decide [ Set.ext_iff ] ;
    rw [ ← isOpen_compl_iff, h_union ];
    refine isOpen_iUnion ?_;
    intro i
    have h_closed : IsClosed (S ∩ A i) := by
      exact h i |>.1;
    convert hdu.1 i |> fun h => h.isOpen.inter ( h_closed.isOpen_compl ) using 1 ; ext ; aesop;
  · have h_union : S = ⋃ i, S ∩ A i := by
      ext x; exact ⟨fun hx => by
        rcases hdu.2.2 ▸ Set.mem_univ x with ⟨ i, hi ⟩ ; aesop;, fun hx => by
        aesop⟩
    generalize_proofs at *; (
    exact h_union ▸ isOpen_iUnion fun i => ( h i ).isOpen)

/--
The diagonal set `A⁰ = ⋃_j A0 j` (from the per-`j` bracket splits, each `A0 j ⊆
diagBracketSet A y j`) is clopen. On each block `A i` it coincides with the *finite* union
`⋃_{j<i} (A0 j ∩ A i)`: for `j ≥ i` we have `A0 j ⊆ diagBracketSet A y j ⊆ ⋃_{k>j} A k`, which is
disjoint from `A i` since `i ≤ j < k`. A finite union of clopen sets is clopen, so
`isClopen_of_inter_blocks` applies.
-/
lemma diag_iUnion_isClopen {F : ScatFun} {A : ℕ → Set ↑F.domain} (hdu : F.IsDisjointUnion A)
    (y : Baire) (A0 : ℕ → Set ↑F.domain) (hcl : ∀ j, IsClopen (A0 j))
    (hsub : ∀ j, A0 j ⊆ diagBracketSet A y j) :
    IsClopen (⋃ j, A0 j) := by
  refine ScatFun.isClopen_of_inter_blocks hdu ?_;
  intro i
  have h_union_clopen : IsClopen (⋃ j ∈ Finset.range i, (A0 j ∩ A i)) :=
    isClopen_biUnion_finset (fun j _ => IsClopen.inter (hcl j) (hdu.1 i))
  have h_eq : (⋃ j, A0 j) ∩ A i = ⋃ j ∈ Finset.range i, (A0 j ∩ A i) := by
    ext x
    simp only [diagBracketSet, subset_inter_iff, Finset.mem_range, mem_inter_iff, mem_iUnion, exists_and_left, exists_prop] at *;
    constructor <;> intro h;
    · obtain ⟨ ⟨ j, hj ⟩, hi ⟩ := h; specialize hsub j; simp_all +decide [ Set.subset_def ] ;
      obtain ⟨ k, hk₁, hk₂ ⟩ := hsub.1 _ _ hj; have := hdu.2.1 i k; simp_all +decide [ Set.disjoint_left ] ;
      grind;
    · exact ⟨ ⟨ _, h.choose_spec.1 ⟩, h.choose_spec.2.2 ⟩
  rw [h_eq]
  exact h_union_clopen

/--
**`ω`-idempotency of a plain gluing of `ω`-idempotent blocks.** If every element `w` of the
list `L` satisfies `ω w ≤ w`, then `ω (glList L) ≤ glList L`. `ω (glList L) = gl (const glList L)`
flattens (`gl_gl_flatten_equiv`) into `gl_k (ω (block k))`, and each `ω (block k) ≤ block k`
(by hypothesis for `k < |L|`, and `ω empty ≤ empty` past the end).
-/
lemma ScatFun.omega_glList_reduces_glList_of_omega_le {L : List ScatFun}
    (h : ∀ w ∈ L, ScatFun.Reduces (ScatFun.omega w) w) :
    ScatFun.Reduces (ScatFun.omega (ScatFun.glList L)) (ScatFun.glList L) := by
  -- Apply gl_gl_flatten_reduces with H i k := f k.
  set f : ℕ → ScatFun := fun k => L.getD k ScatFun.empty
  have h1 : ScatFun.Reduces (ScatFun.gl (fun _ => ScatFun.gl f)) (ScatFun.gl (fun m => f (Nat.unpair m).2)) := by
    convert ScatFun.gl_gl_flatten_reduces ( fun i k => f k ) using 1;
  -- Apply gl_reindex with e m := Nat.pair (Nat.unpair m).2 (Nat.unpair m).1.
  set e : ℕ → ℕ := fun m => Nat.pair (Nat.unpair m).2 (Nat.unpair m).1
  have h2 : ScatFun.Reduces (ScatFun.gl (fun m => f (Nat.unpair m).2)) (ScatFun.gl (fun m => f (Nat.unpair m).1)) := by
    convert ScatFun.gl_reindex ( fun m => f ( Nat.unpair m |>.1 ) ) e _ using 1;
    · aesop;
    · intro m n hmn
      simp only [Nat.pair_eq_pair, e] at hmn
      exact (by
      rw [ ← Nat.pair_unpair m, ← Nat.pair_unpair n, hmn.2, hmn.1 ]);
  -- Apply gl_flat_reduces_gl_gl with H i k := f i.
  have h3 : ScatFun.Reduces (ScatFun.gl (fun m => f (Nat.unpair m).1)) (ScatFun.gl (fun i => ScatFun.gl (fun k => f i))) := by
    convert ScatFun.gl_flat_reduces_gl_gl ( fun i k => f i ) using 1;
  -- Apply gl_reduces_of_pointwise with H i k := f i.
  have h4 : ScatFun.Reduces (ScatFun.gl (fun i => ScatFun.gl (fun k => f i))) (ScatFun.gl f) := by
    apply ScatFun.gl_reduces_of_pointwise;
    intro i
    by_cases hi : i < L.length;
    · convert h ( L.getD i ScatFun.empty ) _ using 1;
      grind;
    · simp +zetaDelta at *;
      rw [ List.getElem?_eq_none ] <;> norm_num [ hi ];
      exact gl_reduces_single (fun _ => empty) (e i) fun j => congrFun rfl;
  exact h1.trans ( h2.trans ( h3.trans h4 ) )

/--
Every element of `𝒲_α = omegaRegularSet α` is `ω`-idempotent: `ω w ≤ w`. Elements are either
`ℓ_λ = maxFun α.limitPart` (`omega_maxFun_reduces_self`) or `ω h` for `h ∈ 𝒞_α`
(`omega_omega_equiv`).
-/
lemma ScatFun.omega_le_self_of_mem_omegaRegularSet (α : Ordinal.{0}) (hα : α < omega1)
    {w : ScatFun} (hw : w ∈ omegaRegularSet α hα) :
    ScatFun.Reduces (ScatFun.omega w) w := by
  unfold omegaRegularSet at hw; simp_all +decide ;
  obtain rfl | ⟨ a, ha, rfl ⟩ := hw;
  · exact omega_maxFun_reduces_self _ _;
  · convert ScatFun.omega_omega_equiv a |> And.left using 1

/--
**`A⁰` reduction.** Given pairwise-disjoint clopen sets `A0 j`, each contained in the `j`-th
bracket `diagBracketSet A y j` (hence in the disjoint ray `{F.func ∈ RaySet univ y j}`), with
`F.restrict (A0 j) ≤ glList H` for every `j`, and `ω (glList H) ≤ glList H`, the diagonal union
`F.restrict (⋃ j, A0 j) ≤ glList H`. The `A0 j` form a disjoint-union partition of the diagonal,
so `F.restrict (⋃ j A0 j) ≤ gl_j (F.restrict (A0 j)) ≤ ω (glList H) ≤ glList H`.
-/
lemma diag_A0_reduces_glList {F : ScatFun} {A : ℕ → Set ↑F.domain} (_hdu : F.IsDisjointUnion A)
    (y : Baire) (H : Finset ScatFun) (A0 : ℕ → Set ↑F.domain) (hcl : ∀ j, IsClopen (A0 j))
    (hsub : ∀ j, A0 j ⊆ diagBracketSet A y j)
    (hred : ∀ j, ScatFun.Reduces (F.restrict (A0 j)) (ScatFun.glList H.toList))
    (homega : ScatFun.Reduces (ScatFun.omega (ScatFun.glList H.toList)) (ScatFun.glList H.toList)) :
    ScatFun.Reduces (F.restrict (⋃ j, A0 j)) (ScatFun.glList H.toList) := by
  have h_domain_partition : ∃ P : ℕ → Set ↑(F.restrict (⋃ j, A0 j)).domain, (F.restrict (⋃ j, A0 j)).IsDisjointUnion P ∧ ∀ i, P i = {w : ↑(F.restrict (⋃ j, A0 j)).domain | (F.restrictEquiv (⋃ j, A0 j) w : ↑F.domain) ∈ A0 i} := by
    refine' ⟨ _, _, fun i => rfl ⟩;
    refine ⟨ ?_, ?_, ?_ ⟩;
    · intro i;
      convert IsClopen.preimage ( hcl i ) ( show Continuous fun w : ↑ ( F.restrict ( ⋃ j, A0 j ) ).domain => ( F.restrictEquiv ( ⋃ j, A0 j ) w : ↑F.domain ) from ?_ ) using 1;
      exact continuous_subtype_val.comp ( F.restrictEquiv ( ⋃ j, A0 j ) |>.continuous );
    · intro i j hij; rw [ Set.disjoint_left ] ; intro w hw hw'; simp_all +decide ;
      have := hsub i hw; have := hsub j hw'; simp_all +decide [ diagBracketSet ] ;
      cases lt_or_gt_of_ne hij <;> simp_all +decide [ RaySet ];
    · ext w; simp [diagBracketSet] at *; (
      obtain ⟨ i, hi ⟩ := w.2;
      obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp hi; use j; aesop;);
  obtain ⟨P, hP⟩ := h_domain_partition;
  have h_gl_reduces : ScatFun.Reduces (ScatFun.gl (fun i => (F.restrict (⋃ j, A0 j)).restrict (P i))) (ScatFun.omega (ScatFun.glList H.toList)) := by
    have h_gl_reduces : ∀ i, ScatFun.Reduces ((F.restrict (⋃ j, A0 j)).restrict (P i)) (ScatFun.glList H.toList) := by
      intro i
      have h_equiv : ScatFun.Equiv ((F.restrict (⋃ j, A0 j)).restrict (P i)) (F.restrict (A0 i)) := by
        convert ScatFun.restrict_restrict_equiv F ( ⋃ j, A0 j ) ( A0 i ) _ using 1;
        · rw [ hP.2 i ];
        · exact Set.subset_iUnion _ _;
      exact h_equiv.1.trans ( hred i );
    convert ScatFun.gl_reduces_of_pointwise _ _ _ using 1;
    assumption;
  have h_gl_reduces : ScatFun.Reduces (F.restrict (⋃ j, A0 j)) (ScatFun.gl (fun i => (F.restrict (⋃ j, A0 j)).restrict (P i))) := by
    apply scatFun_reduces_gl_of_domain_partition;
    exact hP.1;
  exact h_gl_reduces.trans ( by assumption ) |> fun h => h.trans homega

/--
**Finite disjoint clopen union reducing into `FinGl G`.** If `S = ⋃ k, Q k` is a finite
(`Fin n`-indexed) union of pairwise-disjoint clopen sets `Q k`, and each `F.restrict (Q k)`
reduces into a member of `FinGl G.toFinFun`, then `F.restrict S` reduces into a member of
`FinGl G.toFinFun` (glue the finitely many pieces; `FinGl` is closed under finite gluing).
-/
lemma ScatFun.reduces_finGl_of_finite_union {F : ScatFun} {n : ℕ} (Q : Fin n → Set ↑F.domain)
    (hcl : ∀ k, IsClopen (Q k)) (hdisj : Pairwise (Disjoint on Q))
    (G : Finset ScatFun)
    (hpiece : ∀ k, ∃ m ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict (Q k)) m) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict (⋃ k, Q k)) hh := by
  obtain ⟨m, hm⟩ : ∃ m : Fin n → ScatFun, (∀ k, m k ∈ FinGl G.toFinFun) ∧ (∀ k, (F.restrict (Q k)).Reduces (m k)) := by
    exact ⟨ fun k => Classical.choose ( hpiece k ), fun k => Classical.choose_spec ( hpiece k ) |>.1, fun k => Classical.choose_spec ( hpiece k ) |>.2 ⟩;
  -- By scatFun_reduces_gl_of_domain_partition, Reduces (F.restrict U) (gl (fun j => (F.restrict U).restrict (P j))).
  have h_reduces_gl : ScatFun.Reduces (F.restrict (⋃ k, Q k)) (ScatFun.gl (fun j => (F.restrict (⋃ k, Q k)).restrict (if h : j < n then {w : ↑(F.restrict (⋃ k, Q k)).domain | (F.restrictEquiv (⋃ k, Q k) w).val ∈ Q ⟨j, h⟩} else ∅))) := by
    apply scatFun_reduces_gl_of_domain_partition;
    constructor;
    · intro i; by_cases hi : i < n <;> simp +decide [ *, IsClopen ] ;
      exact ⟨ IsClosed.preimage ( continuous_subtype_val.comp ( F.restrictEquiv ( ⋃ k, Q k ) |>.continuous ) ) ( hcl _ |>.1 ), IsOpen.preimage ( continuous_subtype_val.comp ( F.restrictEquiv ( ⋃ k, Q k ) |>.continuous ) ) ( hcl _ |>.2 ) ⟩;
    · constructor;
      · intro i j hij; by_cases hi : i < n <;> by_cases hj : j < n <;> simp +decide [ hi, hj ] ;
        exact Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp ( hdisj ( show ⟨ i, hi ⟩ ≠ ⟨ j, hj ⟩ from by simpa [ Fin.ext_iff ] using hij ) ) hx hx';
      · ext w; simp [ScatFun.restrictEquiv];
        rcases w with ⟨ w, hw ⟩;
        rcases hw with ⟨ hw₁, hw₂ ⟩;
        rcases Set.mem_iUnion.mp hw₂ with ⟨ k, hk ⟩ ; use k ; aesop;
  refine' ⟨ _, finGl_gl_ite_of_forall_finGl ( Finset.range n ) ( fun j => if h : j < n then m ⟨ j, h ⟩ else ScatFun.empty ) _, h_reduces_gl.trans _ ⟩;
  · aesop;
  · apply ScatFun.gl_reduces_of_pointwise;
    intro i; split_ifs <;> simp_all +decide ;
    · have h_restrict_equiv : ScatFun.Equiv ((F.restrict (⋃ k, Q k)).restrict {w : ↑(F.restrict (⋃ k, Q k)).domain | (F.restrictEquiv (⋃ k, Q k) w).val ∈ Q ⟨i, by assumption⟩}) (F.restrict (Q ⟨i, by assumption⟩)) := by
        apply ScatFun.restrict_restrict_equiv;
        exact Set.subset_iUnion ( fun k => Q k ) _;
      exact h_restrict_equiv.1.trans ( hm.2 _ );
    · linarith;
    · convert ScatFun.reduces_of_isEmpty_domain _;
      simp +decide [ ScatFun.restrict ]

/-- Restricting the ray operation commutes with the underlying set: `ray_i(F↾C) ≡ F↾(C ∩
{F.func ∈ RaySet y i})`. Direct from `rayOn_restrict_equiv` and the definitional unfolding of
`ScatFun.rayOn` (`F.rayOn y C i = F.restrict (C ∩ {a | F.func a ∈ RaySet univ y i})`). -/
lemma ScatFun.rayOn_restrict_set_equiv (F : ScatFun) (C : Set ↑F.domain) (y : Baire) (i : ℕ) :
    ScatFun.Equiv ((F.restrict C).rayOn y Set.univ i)
      (F.restrict (C ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i})) := by
  have h := ScatFun.rayOn_restrict_equiv F C y i
  rwa [ScatFun.rayOn] at h

/--
A piece `P ∈ Part` intersected with the `i`-th ray reduces into `FinGl G`: `F↾(P ∩ {F.func ∈
RaySet y i}) ≤ FinGl G`. Since `P` is a piece, `F.restrict P` is centered with cocenter `y`, so by
`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset` its `i`-th ray reduces into `FinGl G`; transport
along `rayOn_restrict_set_equiv`.
-/
lemma piece_rayOn_set_reduces_finGl {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (y : Baire) (hcocset : hA.cocenterSet = {y})
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (P : Set ↑F.domain) (hP : P ∈ Part) (i : ℕ) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces (F.restrict (P ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i})) hh := by
  have := ScatFun.rayOn_cocenter_reduces_finGl_of_equiv_pglFinset ( F.restrict P ) ( hA.centered P hP ) G ( ( hgP P hP ).trans hgequiv ) i;
  obtain ⟨ hh, hhmem, hhh ⟩ := this;
  obtain ⟨hPcent, hycoc⟩ : IsCentered (F.restrict P).func ∧ cocenter (F.restrict P).func (hA.centered P hP) = y := by
    have hmem : hA.cocenterOf hP ∈ hA.cocenterSet := ⟨⟨P, hP⟩, rfl⟩
    rw [hcocset, Set.mem_singleton_iff] at hmem
    exact ⟨hA.centered P hP, hmem⟩;
  obtain ⟨h₁, h₂⟩ := ScatFun.rayOn_restrict_set_equiv F P y i;
  exact ⟨ hh, hhmem, h₂.trans ( by simpa only [ hycoc ] using hhh ) ⟩

/--
The finite family `Q` cutting out `ray_i(f↾A¹)`'s domain is pairwise disjoint: distinct early
blocks `A k` (`k ≤ i`) are disjoint (`hdu`), and `A1 i` lies in blocks `> i` (from
`A1 i ⊆ diagBracketSet A y i`), so is disjoint from every early block.
-/
lemma diag_A1_Q_pairwise {F : ScatFun} (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (y : Baire) (A1 : ℕ → Set ↑F.domain) (hsub1 : ∀ j, A1 j ⊆ diagBracketSet A y j) (i : ℕ) :
    Pairwise (Disjoint on (fun k : Fin (i + 2) =>
      if k.val ∈ Finset.range (i + 1) then A k.val ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i}
      else A1 i)) := by
  intro k l hkl; simp_all +decide [ Set.disjoint_left ] ;
  intro a ha ha' ha''; split_ifs at ha' ha'' <;> simp_all +decide [ Fin.ext_iff ] ;
  · exact Set.disjoint_left.mp ( hdu.2.1 _ _ hkl ) ha'.1 ha'';
  · obtain ⟨ m, hm ⟩ := Set.mem_iUnion₂.mp ( hsub1 i ha'' |>.1 );
    exact Set.disjoint_left.mp ( hdu.2.1 _ _ <| by linarith [ hm.1, Fin.is_lt k, Fin.is_lt l ] ) ha'.1 hm.2;
  · have := hsub1 i ha';
    obtain ⟨ m, hm₁, hm₂ ⟩ := Set.mem_iUnion₂.mp this.1;
    exact Set.disjoint_left.mp ( hdu.2.1 _ _ ( by linarith ) ) hm₂ ha''.1;
  · exact hkl ( by linarith [ Fin.is_lt k, Fin.is_lt l ] )

/--
The finite family `Q` cutting out `ray_i(f↾A¹)`'s domain has union exactly
`(⋃_j A0 j)ᶜ ∩ {F.func ∈ RaySet y i}`. Points in a late block (`> i`) lying in ray `i` fall in
`diagBracketSet A y i = A0 i ∪ A1 i`, and being outside `⋃ A0` land in `A1 i`; points in an early
block (`≤ i`) are automatically outside every `A0 j`.
-/
lemma diag_A1_Q_iUnion_eq {F : ScatFun} (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (y : Baire) (A0 A1 : ℕ → Set ↑F.domain)
    (hsub0 : ∀ j, A0 j ⊆ diagBracketSet A y j)
    (hsub1 : ∀ j, A1 j ⊆ diagBracketSet A y j)
    (hcov : ∀ j, A0 j ∪ A1 j = diagBracketSet A y j)
    (hdisjA : ∀ j, Disjoint (A0 j) (A1 j)) (i : ℕ) :
    (⋃ k : Fin (i + 2), if k.val ∈ Finset.range (i + 1) then
        A k.val ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i} else A1 i)
      = (⋃ j, A0 j)ᶜ ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i} := by
  apply Set.ext;
  intro x; constructor <;> intro hx;
  · simp_all +decide [ Set.ext_iff, mem_iUnion ];
    obtain ⟨ k, hk ⟩ := hx; split_ifs at hk <;> simp_all +decide [ Set.disjoint_left ] ;
    · intro j hj; specialize hsub0 j; specialize hsub1 j; specialize hcov j; simp_all +decide [ diagBracketSet ] ;
      have := hsub0.2 hj; simp_all +decide [ RaySet ] ;
      have := hdu.2.1; simp_all +decide [ Set.disjoint_left ] ;
      grind +splitImp;
    · constructor;
      · intro j hj; specialize hcov j x.1 x.2; simp_all +decide [ diagBracketSet ] ;
        have := hsub1 i; simp_all +decide [ RaySet ] ;
        grind +splitImp;
      · exact hsub1 i hk |>.2;
  · by_cases h : ∃ k ≤ i, x ∈ A k <;> simp_all +decide [ Set.ext_iff ];
    · obtain ⟨ k, hk₁, hk₂ ⟩ := h; use ⟨ k, by linarith ⟩ ; aesop;
    · obtain ⟨k, hk⟩ : ∃ k, x ∈ A k := by
        simpa using hdu.2.2.symm.subset ( Set.mem_univ x );
      use ⟨ i + 1, by linarith ⟩ ; simp_all +decide [ diagBracketSet ] ;
      grind +qlia

/--
**The `A¹`-ray bound** (memoir `6_double_successor_memo.tex:243-249`). With `A¹ = (⋃_j A0 j)ᶜ`
the complement of the diagonal, every ray `ray_i(f↾A¹)` reduces into `FinGl G`. Its domain
`A¹ ∩ {F.func ∈ RaySet y i}` splits as the *finite* disjoint clopen union of `A1 i` (the `A¹`-part
of the `i`-th bracket, `≤ FinGl G` by hypothesis `hA1red`) together with `A_k ∩ {F.func ∈ RaySet y
i}` for the finitely many early blocks `k ≤ i` (each a piece-ray `ray_i(f_k)`, `≤ FinGl G` by
`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset`). `reduces_finGl_of_finite_union` glues them.
-/
lemma diag_A1_rayOn_reduces_finGl {F : ScatFun}
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hcocset : hA.cocenterSet = {y})
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (hAmem : ∀ i, A i ∈ Part ∨ A i = ∅)
    (A0 A1 : ℕ → Set ↑F.domain)
    (hsub0 : ∀ j, A0 j ⊆ diagBracketSet A y j)
    (hsub1 : ∀ j, A1 j ⊆ diagBracketSet A y j)
    (hcov : ∀ j, A0 j ∪ A1 j = diagBracketSet A y j)
    (hdisjA : ∀ j, Disjoint (A0 j) (A1 j))
    (hcl1 : ∀ j, IsClopen (A1 j))
    (hA1red : ∀ j, ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict (A1 j)) hh)
    (i : ℕ) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces ((F.restrict (⋃ j, A0 j)ᶜ).rayOn y Set.univ i) hh := by
  classical
  set Q : Fin (i + 2) → Set ↑F.domain :=
    fun k => if k.val ∈ Finset.range (i + 1) then A k.val ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i}
      else A1 i with hQdef
  have hrcl : IsClopen {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i} :=
    (isClopen_raySet y i).preimage F.hCont
  have hcl : ∀ k, IsClopen (Q k) := by
    intro k; rw [hQdef]; dsimp only; split_ifs
    · exact (hdu.1 _).inter hrcl
    · exact hcl1 i
  have hdisj : Pairwise (Disjoint on Q) := diag_A1_Q_pairwise A hdu y A1 hsub1 i
  have hunion : (⋃ k, Q k) = (⋃ j, A0 j)ᶜ ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y i} :=
    diag_A1_Q_iUnion_eq A hdu y A0 A1 hsub0 hsub1 hcov hdisjA i
  have hpiece : ∀ k, ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict (Q k)) hh := by
    intro k; rw [hQdef]; dsimp only; split_ifs with hk
    · rcases hAmem k.val with hP | h0
      · exact piece_rayOn_set_reduces_finGl hA y hcocset hgequiv hgP _ hP i
      · refine ⟨ScatFun.empty, ScatFun.empty_mem_FinGl _ ⟨fun x => x.2⟩,
          ScatFun.reduces_of_isEmpty_domain ?_⟩
        rw [Set.isEmpty_coe_sort, Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx, hmem⟩
        rw [h0] at hmem
        exact hmem.1
    · exact hA1red i
  obtain ⟨hh, hhmem, hhred⟩ := ScatFun.reduces_finGl_of_finite_union Q hcl hdisj G hpiece
  refine ⟨hh, hhmem, ?_⟩
  have h_equiv := ScatFun.rayOn_restrict_set_equiv F (⋃ j, A0 j)ᶜ y i
  rw [hunion] at hhred
  exact h_equiv.1.trans hhred

/--
The `j`-th bracket set `diagBracketSet A y j` is clopen: `⋃_{i>j} A i` is the complement of
the finite clopen union `⋃_{i≤j} A i` (as `A` is a disjoint clopen cover), and it is intersected
with the clopen ray-preimage `{F.func ∈ RaySet y j}`.
-/
lemma diagBracketSet_isClopen {F : ScatFun} {A : ℕ → Set ↑F.domain} (hdu : F.IsDisjointUnion A)
    (y : Baire) (j : ℕ) : IsClopen (diagBracketSet A y j) := by
  apply_rules [ IsClopen.inter, isClopen_raySet, isClopen_biUnion_finset ];
  · have h_compl : ⋃ i, ⋃ (_ : j < i), A i = (⋃ i ∈ Finset.range (j+1), A i)ᶜ := by
      ext x; simp;
      constructor;
      · rintro ⟨ i, hi, hx ⟩ k hk;
        exact fun hx' => hdu.2.1 i k ( by linarith ) |> fun h => h.le_bot ⟨ hx, hx' ⟩;
      · obtain ⟨ i, hi ⟩ := hdu.2.2.symm.subset ( Set.mem_univ x );
        grind;
    convert isClopen_biUnion_finset ( fun i _ => hdu.1 i ) |> IsClopen.compl using 1;
  · exact ⟨ isClosed_univ.preimage F.hCont, isOpen_univ.preimage F.hCont ⟩;
  · constructor;
    · have h_clopen : ∀ k < j, IsClosed (fun x : ↑F.domain => F.func x k = y k) := by
        intro k hk; exact isClosed_eq ( continuous_apply k |> Continuous.comp <| F.hCont ) continuous_const;
      convert isClosed_iInter fun k => isClosed_iInter fun hk => h_clopen k hk using 1;
      aesop;
    · have h_clopen : ∀ k < j, IsOpen {x : ↑F.domain | F.func x k = y k} := by
        intro k hk
        have h_cont : Continuous (fun x : ↑F.domain => F.func x k) := by
          exact continuous_apply k |> Continuous.comp <| F.hCont;
        exact h_cont.isOpen_preimage { y k } ( by simp +decide );
      convert isOpen_biInter_finset fun k hk => h_clopen k ( Finset.mem_range.mp hk ) using 1;
      ext; simp [Finset.mem_range];
      rfl;
  · constructor;
    · have h_cont : Continuous (fun x : ↑F.domain => F.func x j) := by
        exact continuous_apply j |> Continuous.comp <| F.hCont;
      exact isClosed_compl_iff.mpr ( h_cont.isOpen_preimage { y j } ( by simp +decide ) );
    · exact isOpen_compl_iff.mpr ( isClosed_eq ( show Continuous fun x => F.func x j from by exact continuous_apply j |> Continuous.comp <| F.hCont ) continuous_const )

/--
**`glList` is monotone under a pointwise map reduction.** If `w ≤ f w` for every `w ∈ L`,
then `glList L ≤ glList (L.map f)`.
-/
lemma ScatFun.glList_reduces_glList_map (L : List ScatFun) (f : ScatFun → ScatFun)
    (h : ∀ w ∈ L, ScatFun.Reduces w (f w)) :
    ScatFun.Reduces (ScatFun.glList L) (ScatFun.glList (L.map f)) := by
  convert ScatFun.gl_reduces_of_pointwise _ _ _ using 1;
  grind [List.getElem?_eq_none, List.getElem_mem, empty_reduces]

/--
The interleaved flattening `[c,d₀,c,d₁,…]` is a permutation of `replicate |D| c ++ D`.
-/
lemma flatten_pair_perm (c : ScatFun) (D : List ScatFun) :
    ((D.map (fun d => [c, d])).flatten).Perm (List.replicate D.length c ++ D) := by
  induction' ‹List ScatFun› using List.reverseRecOn with d D ih <;> simp +decide [ *, List.replicate ];
  grind

/-- **Factoring a common left block out of a list of binary gluings.** If `c` is `ω`-idempotent
(`ω c ≤ c`), then `glList (D.map (fun d => c ⊕ d)) ≤ c ⊕ glList D`: the finitely many copies of `c`
collapse into the single left slot (via `ω c ≤ c`), and the `d`-blocks assemble into `glList D`. -/
lemma ScatFun.glList_map_glBin_left_factor (c : ScatFun)
    (hc : ScatFun.Reduces (ScatFun.omega c) c) (D : List ScatFun) :
    ScatFun.Reduces (ScatFun.glList (D.map (fun d => ScatFun.glBin c d)))
      (ScatFun.glBin c (ScatFun.glList D)) := by
  have hstep1 : ScatFun.Reduces (ScatFun.glList (D.map (fun d => ScatFun.glBin c d)))
      (ScatFun.glList (D.map (fun d => ScatFun.glList [c, d]))) := by
    show ScatFun.Reduces (ScatFun.gl (fun k => (D.map (fun d => ScatFun.glBin c d)).getD k ScatFun.empty))
      (ScatFun.gl (fun k => (D.map (fun d => ScatFun.glList [c, d])).getD k ScatFun.empty))
    refine ScatFun.gl_reduces_of_pointwise _ _ (fun k => ?_)
    by_cases hk : k < D.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hk),
        List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_map]
      exact (ScatFun.finGl_glBin_equiv_glList c D[k]).1
    · rw [List.getD_eq_default _ _ (by simpa using not_lt.mp hk),
        List.getD_eq_default _ _ (by simpa using not_lt.mp hk)]
      exact ContinuouslyReduces.refl _
  have hstep2 : ScatFun.Equiv (ScatFun.glList (D.map (fun d => ScatFun.glList [c, d])))
      (ScatFun.glList ((D.map (fun d => [c, d])).flatten)) := by
    have h := ScatFun.glList_map_glList_flatten (D.map (fun d => [c, d]))
    simpa only [List.map_map, Function.comp] using h
  have hstep3 := (ScatFun.glList_perm_equiv (flatten_pair_perm c D)).1
  have hstep4 := (ScatFun.glList_append_equiv (List.replicate D.length c) D).1
  have hrep : ScatFun.Reduces (ScatFun.glList (List.replicate D.length c)) c :=
    (ScatFun.glList_reduces_omega_of_forall (fun w hw => by
      rw [(List.mem_replicate.mp hw).2]; exact ContinuouslyReduces.refl _)).trans hc
  have hstep5 : ScatFun.Reduces (ScatFun.glBin (ScatFun.glList (List.replicate D.length c)) (ScatFun.glList D))
      (ScatFun.glBin c (ScatFun.glList D)) :=
    ScatFun.glBin_reduces_of_reduces hrep (ContinuouslyReduces.refl _)
  exact hstep1.trans (hstep2.1.trans (hstep3.trans (hstep4.trans hstep5)))

/-- **Combine step for the Claim.** If `B` reduces into `glList L` and every block `w ∈ L` reduces
into `glList Hset ⊕ (m w)` with `m w ∈ FinGl G` (and `glList Hset` is `ω`-idempotent), then `B`
reduces into `glList Hset ⊕ hh` for a single `hh ∈ FinGl G`. The finitely many `glList Hset`
copies collapse (via `ω`-idempotency, `glList_map_glBin_left_factor`) and the `m w` gather into a
finite gluing `hh := glList (L.map m) ∈ FinGl G` (`finGl_glList_of_forall_finGl`). -/
lemma hardCase_bracket_combine {G Hset : Finset ScatFun} (L : List ScatFun)
    (hHomega : ScatFun.Reduces (ScatFun.omega (ScatFun.glList Hset.toList)) (ScatFun.glList Hset.toList))
    (hLred : ∀ w ∈ L, ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList Hset.toList) hh))
    (B : ScatFun) (hBeq : ScatFun.Reduces B (ScatFun.glList L)) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces B (ScatFun.glBin (ScatFun.glList Hset.toList) hh) := by
  classical
  set m : ScatFun → ScatFun :=
    fun w => if h : ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList Hset.toList) hh) then h.choose else ScatFun.empty
    with hmdef
  have hm_mem : ∀ w ∈ L, m w ∈ ScatFun.FinGl G.toFinFun := by
    intro w hw; rw [hmdef]; dsimp only; rw [dif_pos (hLred w hw)]; exact (hLred w hw).choose_spec.1
  have hm_red : ∀ w ∈ L, ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList Hset.toList) (m w)) := by
    intro w hw; rw [hmdef]; dsimp only; rw [dif_pos (hLred w hw)]; exact (hLred w hw).choose_spec.2
  refine ⟨ScatFun.glList ((L.map m)), ScatFun.finGl_glList_of_forall_finGl (fun w hw => ?_), ?_⟩
  · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw; exact hm_mem w' hw'
  · have h1 : ScatFun.Reduces (ScatFun.glList L)
        (ScatFun.glList (L.map (fun w => ScatFun.glBin (ScatFun.glList Hset.toList) (m w)))) :=
      ScatFun.glList_reduces_glList_map L _ hm_red
    have h2 : ScatFun.Reduces
        (ScatFun.glList ((L.map m).map (fun d => ScatFun.glBin (ScatFun.glList Hset.toList) d)))
        (ScatFun.glBin (ScatFun.glList Hset.toList) (ScatFun.glList (L.map m))) :=
      ScatFun.glList_map_glBin_left_factor (ScatFun.glList Hset.toList) hHomega (L.map m)
    have heq : (L.map m).map (fun d => ScatFun.glBin (ScatFun.glList Hset.toList) d)
        = L.map (fun w => ScatFun.glBin (ScatFun.glList Hset.toList) (m w)) := by
      rw [List.map_map]; rfl
    rw [heq] at h2
    exact hBeq.trans (h1.trans h2)

/-- The bracket `f^{[j]} = F.restrict (diagBracketSet A y j)` reduces into the `j`-th ray
`F.rayOn y univ j`, since `diagBracketSet A y j ⊆ {x | F.func x ∈ RaySet univ y j}`
(restriction to a subset of the ray's clopen codomain-preimage). -/
lemma bracket_reduces_rayOn {F : ScatFun} (A : ℕ → Set ↑F.domain) (y : Baire) (j : ℕ) :
    ScatFun.Reduces (F.restrict (diagBracketSet A y j)) (F.rayOn y Set.univ j) := by
  rw [rayOn_eq_corestrict]
  exact restrict_reduces_of_subset F (by rw [diagBracketSet]; exact Set.inter_subset_right)

/-- The left factor of a binary gluing reduces into the gluing. -/
lemma ScatFun.reduces_glBin_left (a b : ScatFun) : ScatFun.Reduces a (ScatFun.glBin a b) :=
  (ScatFun.mem_reduces_glList (show a ∈ [a, b] by simp)).trans
    (ScatFun.finGl_glBin_equiv_glList a b).2

/-- The right factor of a binary gluing reduces into the gluing. -/
lemma ScatFun.reduces_glBin_right (a b : ScatFun) : ScatFun.Reduces b (ScatFun.glBin a b) :=
  (ScatFun.mem_reduces_glList (show b ∈ [a, b] by simp)).trans
    (ScatFun.finGl_glBin_equiv_glList a b).2

/-- Monotonicity of the centered levels across one limit-or-zero block:
`𝒞_{λ+k+1} ⊆ 𝒞_{λ+m+1}` for `k ≤ m`. -/
lemma ScatFun.Centered_succ_mono {lam : Ordinal.{0}} (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    {k m : ℕ} (h : k ≤ m) :
    ScatFun.Centered (lam + (k : Ordinal) + 1) ⊆ ScatFun.Centered (lam + (m : Ordinal) + 1) := by
  rw [ScatFun.Centered_lam_add_succ hlim, ScatFun.Centered_lam_add_succ hlim]
  exact ScatFun.CentBlock_mono _ h

/-- Reshuffle of nested binary gluings: `a ⊕ (b ⊕ c)` reduces into `b ⊕ (a ⊕ c)`. -/
lemma ScatFun.reduces_glBin_left_comm (a b c : ScatFun) :
    ScatFun.Reduces (ScatFun.glBin a (ScatFun.glBin b c))
      (ScatFun.glBin b (ScatFun.glBin a c)) := by
  have e1 : ScatFun.Equiv (ScatFun.glBin a (ScatFun.glBin b c)) (ScatFun.glList [a, b, c]) :=
    (ScatFun.glBin_congr (ScatFun.glList_single_equiv a)
      (ScatFun.finGl_glBin_equiv_glList b c)).trans (ScatFun.glList_append_equiv [a] [b, c]).symm
  have e2 : ScatFun.Equiv (ScatFun.glBin b (ScatFun.glBin a c)) (ScatFun.glList [b, a, c]) :=
    (ScatFun.glBin_congr (ScatFun.glList_single_equiv b)
      (ScatFun.finGl_glBin_equiv_glList a c)).trans (ScatFun.glList_append_equiv [b] [a, c]).symm
  have e3 : ScatFun.Equiv (ScatFun.glList [a, b, c]) (ScatFun.glList [b, a, c]) :=
    ScatFun.glList_perm_equiv (List.Perm.swap b a [c])
  exact ((e1.trans e3).trans e2.symm).1

/-- If every block of a list reduces into `FinGl G`, then so does the whole gluing. -/
lemma ScatFun.glList_reduces_finGl_of_forall {G : Finset ScatFun} (L : List ScatFun)
    (h : ∀ x ∈ L, ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces x hh) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (ScatFun.glList L) hh := by
  classical
  set m : ScatFun → ScatFun :=
    fun x => if hx : ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces x hh then hx.choose
      else ScatFun.empty with hmdef
  have hm_mem : ∀ x ∈ L, m x ∈ ScatFun.FinGl G.toFinFun := by
    intro x hx; rw [hmdef]; dsimp only; rw [dif_pos (h x hx)]; exact (h x hx).choose_spec.1
  have hm_red : ∀ x ∈ L, ScatFun.Reduces x (m x) := by
    intro x hx; rw [hmdef]; dsimp only; rw [dif_pos (h x hx)]; exact (h x hx).choose_spec.2
  refine ⟨ScatFun.glList (L.map m), ScatFun.finGl_glList_of_forall_finGl (fun w hw => ?_), ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw; exact hm_mem x hx
  · exact ScatFun.glList_reduces_glList_map L m hm_red

/-- **A centered function reducing into an `ω`-tower reduces into a single copy.** If `w` is
centered and `w ≤ ω c = gl (fun _ => c)`, then `w ≤ c`.

Proof: let `x` be a center of `w` and `(σ, τ)` a reduction `w.func ≤ (ω c).func`. The image
`σ x` lies in one clopen block `Bᵢ₀` of the disjoint-block gluing `ω c`. By center invariance
(`centerInvariance_reduce`), `w ≤ (ω c)↾Bᵢ₀`, and the restriction of `ω c` to a single block
`Bᵢ₀` is (continuously equivalent to) `c` itself. -/
lemma ScatFun.reduces_of_centered_reduces_omega (w c : ScatFun) (hw : IsCentered w.func)
    (hle : ScatFun.Reduces w (ScatFun.omega c)) : ScatFun.Reduces w c := by
  obtain ⟨x, hx⟩ := hw
  set D := (ScatFun.omega c).domain with hD
  have hcover : (⋃ i, {a : ↑D | (a : ℕ → ℕ) 0 = i}) = (Set.univ : Set ↑D) := by
    ext a; simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨(a : ℕ → ℕ) 0, rfl⟩
  have hopen : ∀ i, IsOpen {a : ↑D | (a : ℕ → ℕ) 0 = i} := by
    intro i
    have hcont : Continuous (fun a : ↑D => (a : ℕ → ℕ) 0) :=
      (continuous_apply 0).comp continuous_subtype_val
    have hset : {a : ↑D | (a : ℕ → ℕ) 0 = i} = (fun a : ↑D => (a : ℕ → ℕ) 0) ⁻¹' {i} := by
      ext a; simp
    rw [hset]; exact (isOpen_discrete _).preimage hcont
  obtain ⟨i, hi⟩ := centerInvariance_cover hx hle hcover hopen
  refine hi.trans ?_
  have hmem : ∀ a : ↑{a : ↑D | (a : ℕ → ℕ) 0 = i}, unprepend (a.val : ℕ → ℕ) ∈ c.domain := by
    intro a
    obtain ⟨k, hk, hk2⟩ := GluingSet_inverse_short (fun _ => c.domain) a.val
    exact hk2
  refine ⟨fun a => ⟨unprepend (a.val : ℕ → ℕ), hmem a⟩, ?_, prepend i, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact (continuous_apply (k+1)).comp (continuous_subtype_val.comp continuous_subtype_val)
  · apply Continuous.continuousOn
    apply continuous_pi
    intro k
    by_cases hk : k = 0
    · subst hk; simp only [prepend]; exact continuous_const
    · simp only [prepend, if_neg hk]; exact continuous_apply _
  · intro a
    show (ScatFun.omega c).func a.val = prepend i (c.func ⟨unprepend (a.val : ℕ → ℕ), hmem a⟩)
    have ha0 : (a.val : ℕ → ℕ) 0 = i := a.property
    have hval : (a.val : ℕ → ℕ) = prepend i (unprepend (a.val : ℕ → ℕ)) := by
      conv_lhs => rw [← prepend_unprepend (a.val : ℕ → ℕ)]
      rw [ha0]
    have hpre := omega_func_prepend c i ⟨unprepend (a.val : ℕ → ℕ), hmem a⟩
    rw [← hpre]
    congr 1
    apply Subtype.ext
    exact hval

/-- **Case 1 of the per-generator bound — the centered clause.** A *centered* generator
`w ∈ 𝒞_{α+1}` with `w ≤ f^{[j]}` reduces into a member of `FinGl G`.

Proof (memoir `6_double_successor_memo.tex:216-221`): `w ≤ f^{[j]} ≤ ray_j(f)`
(`bracket_reduces_rayOn`) and `ray_j(f) ≤ ω(\gl G)`
(`verticalTheorem_hardCase_rayOn_reduces_omegaG`), so `w ≤ ω(\gl G)`. A centered `w` reducing
into an `ω`-tower of `\gl G` reduces (`ScatFun.reduces_of_centered_reduces_omega`) into the
single block `\gl G = glList G.toList`, which lies in `FinGl G`. -/
lemma hardCase_centered_reduces_finGl
    {α : Ordinal.{0}} (_hα : α < omega1)
    {F : ScatFun}
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (A : ℕ → Set ↑F.domain) (j : ℕ)
    (w : ScatFun) (hwc : w ∈ ScatFun.Centered (α + 1))
    (hwle : ScatFun.Reduces w (F.restrict (diagBracketSet A y j))) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces w hh := by
  have hwc' : IsCentered w.func := ScatFun.isCentered_of_mem_Centered (α + 1) w hwc
  have hwle_omega : ScatFun.Reduces w (ScatFun.omega (ScatFun.glList G.toList)) :=
    (hwle.trans (bracket_reduces_rayOn A y j)).trans
      (verticalTheorem_hardCase_rayOn_reduces_omegaG hA y (by simp [hpc.2.1]) hpc.2.1
        hgequiv hgP j)
  refine ⟨ScatFun.glList G.toList,
    ScatFun.finGl_of_equiv_glList (fun x hx => Finset.mem_toList.mp hx) (ScatFun.Equiv.refl _),
    ScatFun.reduces_of_centered_reduces_omega w _ hwc' hwle_omega⟩

/-
**Case 2 of the per-generator bound — the `ω`-clause (generalised).** For a finite set
`D ⊆ 𝒞_{α+1}` of centered representatives, if `ω(\gl D) ≤ f^{[j]}` then `ω(\gl D)` reduces into
`\gl H ⊕ hh` for some `hh ∈ FinGl G`.

Proof (memoir `6_double_successor_memo.tex:222-226`): `ω(\gl D) ≡ \gl_{h∈D} (ω h)`
(`omega_glList_equiv_glList_omega`). Each `ω h` (`h ∈ 𝒞_{α+1}`) lies in `𝒲_{α+1}`
(`omegaRegularSet (α+1)`, whose definition is `insert ℓ_λ` of the `ω`-image of `𝒞_{α+1}`) and
satisfies `ω h ≤ ω(\gl D) ≤ f^{[j]} ≤ ray_j(f)`. By `hHmem`, either `ω h ∈ FinGl G`
(then `ω h ≤ \gl H ⊕ (ω h)`), or `ω h ∈ H` (then `ω h ≤ \gl H` by `mem_reduces_glList`).
Gather the finitely many `\gl H ⊕ hh_h` copies via `glList_map_glBin_left_factor` /
`hardCase_bracket_combine`-style collapse into a single `\gl H ⊕ hh`.
-/
lemma hardCase_omega_glList_reduces_glBin
    {α : Ordinal.{0}} (hα : α < omega1) (_hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (_hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (_hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (_hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (_hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (_hdu : F.IsDisjointUnion A)
    (_hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ)
    (D : Finset ScatFun) (hD : D ⊆ ScatFun.Centered (α + 1))
    (hwle : ScatFun.Reduces (ScatFun.omega (ScatFun.glList D.toList))
      (F.restrict (diagBracketSet A y j))) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces (ScatFun.omega (ScatFun.glList D.toList))
        (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
  apply hardCase_bracket_combine (L := D.toList.map ScatFun.omega) (hHomega := by
    apply ScatFun.omega_glList_reduces_glList_of_omega_le;
    exact fun w hw => ScatFun.omega_le_self_of_mem_omegaRegularSet _ ( by simpa using omega1_add_nat α hα 1 ) ( hHmem w |>.1 ( Finset.mem_toList.mp hw ) |>.1 )) (hLred := by
    intro w hw
    obtain ⟨h, hh⟩ : ∃ h ∈ D, w = ScatFun.omega h := by
      rw [ List.mem_map ] at hw; obtain ⟨ h, hh, rfl ⟩ := hw; exact ⟨ h, by simpa using hh, rfl ⟩ ;
    by_cases hwG : w ∈ ScatFun.FinGl G.toFinFun;
    · exact ⟨ w, hwG, ScatFun.reduces_glBin_right _ _ ⟩;
    · have hwH : w ∈ H := by
        simp_all +decide [ omegaRegularSet ];
        refine' ⟨ Or.inr ⟨ h, hD hh.1, rfl ⟩, _ ⟩;
        have hwle : ScatFun.Reduces (ScatFun.omega h) (F.restrict (diagBracketSet A y j)) := by
          exact ScatFun.omega_reduces_of_reduces (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hh.1)) |> fun h => h.trans hwle;
        exact ⟨ j, hwle.trans ( bracket_reduces_rayOn A y j ) ⟩;
      have hwH : ScatFun.Reduces w (ScatFun.glList H.toList) := by
        exact ScatFun.mem_reduces_glList ( Finset.mem_toList.mpr hwH );
      use ScatFun.glList G.toList;
      exact ⟨ by
        apply ScatFun.finGl_of_equiv_glList;
        exact fun x hx => Finset.mem_toList.mp hx;
        exact ScatFun.Equiv.refl _, hwH.trans ( ScatFun.reduces_glBin_left _ _ ) ⟩) (B := ScatFun.omega (ScatFun.glList D.toList)) (hBeq := by
    exact ScatFun.omega_glList_equiv_glList_omega _ |>.1)

/-- **FG decomposition of the bracket into generators** (memoir `6_double_successor_memo.tex:211-213`).
Since `CB(f^{[j]}) < α+2` — each ray `ray_j(f_i)` has `CB ≤ α+1` — `FG(≤α+1)` (`hFG`) writes the
bracket `f^{[j]} = F.restrict (diagBracketSet A y j)` as a finite gluing of `Generators (α+1)`, so
there is a *list* `L` of generators with `f^{[j]} ≤ glList L` and each block `w ∈ L` a generator
`≤ f^{[j]}` (via `mem_reduces_glList` over the `Equiv`). We record the blocks at the `genStep`
level `genStep (𝒞_{α+1}) (𝒢_α)` — the clause split the per-generator lemma needs
(`Generators_add_succ_eq`: `𝒢_{α+1} = 𝒢_α ∪ genStep (𝒞_{α+1}) (𝒢_α)`).

**Proved.** Proof: obtain `CB(f^{[j]}) ≤ α+1` (rays bound each column); apply
`hFG` to get `f^{[j]} ∈ FinGl (Generators (α+1))`, then `exists_glList_of_finGl`
(`Sandwich_lemma.lean`) for the list `L ⊆ Generators (α+1)` with `f^{[j]} ≡ glList L`. The one
genuine gap is routing pure-`𝒢_α` blocks (the memoir's `CB(f^{[j]}) < λ` alternative, absorbed by
the general structure theorem `general_structure_theorem`) into the `genStep`-membership shape — or,
if `𝒢_α ⊆` the centered clause `𝒞_{α+1}` of `genStep` (cumulativity), uniformly with no
`λ`-dichotomy. Decide which when discharging this. -/
lemma hardCase_bracket_fg_decomp
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (_hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hGsub : G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)))
    (_hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (_hdu : F.IsDisjointUnion A)
    (_hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ)
    (hlamle : α.limitPart ≤ CBRank (F.restrict (diagBracketSet A y j)).func) :
    ∃ L : List ScatFun,
      (∀ w ∈ L, w ∈ ScatFun.Generators (α + 1)) ∧
      (∀ w ∈ L, ScatFun.Reduces w (F.restrict (diagBracketSet A y j))) ∧
      ScatFun.Reduces (F.restrict (diagBracketSet A y j)) (ScatFun.glList L) := by
  classical
  have hα1 : α + 1 < omega1 := by simpa using omega1_add_nat α hα 1
  -- Each generator of `G` has CB-rank ≤ α+1 (from `hGsub`).
  have hGrank : ∀ c ∈ G, CBRank c.func ≤ α + 1 := by
    intro c hc
    rcases Finset.mem_union.mp (hGsub hc) with hcC | hcO
    · exact ScatFun.cbRank_mem_Centered_le (α + 1) hα1 c hcC
    · rw [ScatFun.omegaImage, Finset.mem_image] at hcO
      obtain ⟨c', hc'C, rfl⟩ := hcO
      have hrk : CBRank (ScatFun.omega c').func = CBRank c'.func := by
        rw [ScatFun.omega, ScatFun.gl_cbRank_eq]; exact ciSup_const
      rw [hrk]
      exact ScatFun.cbRank_mem_Centered_le (α + 1) hα1 c' hc'C
  have hglGrank : CBRank (ScatFun.glList G.toList).func ≤ α + 1 :=
    ScatFun.cbRank_glList_le G.toList (α + 1)
      (fun c hc => hGrank c (Finset.mem_toList.mp hc))
  have homegaGrank : CBRank (ScatFun.omega (ScatFun.glList G.toList)).func ≤ α + 1 := by
    rw [ScatFun.omega, ScatFun.gl_cbRank_eq]
    exact ciSup_le (fun _ => hglGrank)
  -- Upper CB-rank bound for the bracket, via `bracket ≤ ω(gl G)`.
  have hub : CBRank (F.restrict (diagBracketSet A y j)).func ≤ α + 1 := by
    have hred : ScatFun.Reduces (F.restrict (diagBracketSet A y j))
        (ScatFun.omega (ScatFun.glList G.toList)) :=
      (bracket_reduces_rayOn A y j).trans
        (verticalTheorem_hardCase_rayOn_reduces_omegaG hA y (by simp [hpc.2.1]) hpc.2.1
          hgequiv hgP j)
    exact le_trans (ContinuouslyReduces.rank_monotone
      (F.restrict (diagBracketSet A y j)).hScat
      (ScatFun.omega (ScatFun.glList G.toList)).hScat hred) homegaGrank
  -- Finite generation of the bracket, from `FG(≤α+1)` on the level interval `[λ, α+1]`.
  have hlim := Ordinal.limitPart_isLimit_or_zero α
  have hαsucc : α.limitPart + ((α.natPart + 1 : ℕ) : Ordinal) = α + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Ordinal.eq_limitPart_add_natPart α]
  have hmem : F.restrict (diagBracketSet A y j)
      ∈ ScatFun.FinGl (ScatFun.Generators (α + 1)).toFinFun := by
    have hlevel := ScatFun.LevelInter_finitelyGenerated hlim (α.natPart + 1)
      (fun k hk F' hF' => hFG (α.limitPart + (k : Ordinal)) (by
        have hle : α.limitPart + (k : Ordinal) ≤ α.limitPart + ((α.natPart + 1 : ℕ) : Ordinal) :=
          (add_le_add_iff_left α.limitPart).2
            (show (k : Ordinal) ≤ ((α.natPart + 1 : ℕ) : Ordinal) by exact_mod_cast hk)
        rw [hαsucc] at hle
        exact lt_of_le_of_lt hle (Order.lt_succ _)) F' hF')
    rw [hαsucc] at hlevel
    exact hlevel ⟨hlamle, hub⟩
  obtain ⟨L, hLmem, hEq⟩ := ScatFun.exists_glList_of_finGl hmem
  exact ⟨L, hLmem, fun w hw => (ScatFun.mem_reduces_glList hw).trans hEq.2, hEq.1⟩

/-- **Per-generator bound across all generator levels** (memoir `6_double_successor_memo.tex:215-232`).
Every generator `w ∈ 𝒢_{λ+n}` (with `λ+n ≤ α+1`, `λ = α.limitPart`) that reduces into the bracket
`f^{[j]}` reduces into `\gl H ⊕ hh` for some `hh ∈ FinGl G`. Proved by induction on `n`: the base
level `𝒢_λ` is either empty (`λ = 0`) or `{ℓ_λ}` (`λ` limit) with `ℓ_λ ∈ 𝒲_{α+1}` handled by the
obstruction membership `hHmem`; the successor level unfolds via `Generators_add_succ_eq` into the
previous level (induction hypothesis) plus one `genStep`, whose three clauses are discharged by
`hardCase_centered_reduces_finGl` (centered), `hardCase_omega_glList_reduces_glBin` (`ω`), and
`wedgeGenerator_bounding` + the previous two (wedge), all transported up to `𝒞_{α+1}` via
`ScatFun.Centered_succ_mono`. -/
lemma hardCase_gen_level_reduces_glBin
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ) :
    ∀ n : ℕ, α.limitPart + (n : Ordinal) ≤ α + 1 →
      ∀ w ∈ ScatFun.Generators (α.limitPart + (n : Ordinal)),
        ScatFun.Reduces w (F.restrict (diagBracketSet A y j)) →
        ∃ hh ∈ ScatFun.FinGl G.toFinFun,
          ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
  classical
  set lam := α.limitPart with hlamdef
  have hlam : lam < omega1 :=
    lt_of_le_of_lt (by rw [Ordinal.eq_limitPart_add_natPart α]; exact le_self_add) hα
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hαsucc : lam + (α.natPart : Ordinal) + 1 = α + 1 := by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
  have hobstruct : ∀ w : ScatFun,
      w ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) →
      ScatFun.Reduces w (F.restrict (diagBracketSet A y j)) →
      ∃ hh ∈ ScatFun.FinGl G.toFinFun,
        ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
    intro w hwreg hwle
    by_cases hwG : w ∈ ScatFun.FinGl G.toFinFun
    · exact ⟨w, hwG, ScatFun.reduces_glBin_right _ _⟩
    · have hwH : w ∈ H :=
        (hHmem w).2 ⟨hwreg, hwG, j, hwle.trans (bracket_reduces_rayOn A y j)⟩
      exact ⟨ScatFun.glList G.toList,
        ScatFun.finGl_of_equiv_glList (fun x hx => Finset.mem_toList.mp hx) (ScatFun.Equiv.refl _),
        (ScatFun.mem_reduces_glList (Finset.mem_toList.mpr hwH)).trans
          (ScatFun.reduces_glBin_left _ _)⟩
  intro n
  induction n with
  | zero =>
    intro _hn w hw hwle
    rw [Nat.cast_zero, add_zero] at hw
    rcases hlim with hl | hl
    · rw [ScatFun.Generators_lam_limit hlam hl, Finset.mem_singleton] at hw
      subst hw
      refine hobstruct _ ?_ hwle
      have hlp : (α + 1).limitPart = lam := by
        rw [← hαsucc,
          show lam + (α.natPart : Ordinal) + 1 = lam + ((α.natPart + 1 : ℕ) : Ordinal) by
            rw [Nat.cast_add, Nat.cast_one, add_assoc]]
        exact Ordinal.limitPart_add_natCast _ _ (Or.inl hl)
      rw [omegaRegularSet]
      exact Finset.mem_insert.mpr (Or.inl (by congr 1; exact hlp.symm))
    · rw [hl, ScatFun.Generators_zero] at hw
      exact absurd hw (Finset.notMem_empty w)
  | succ n ih =>
    intro hn w hw hwle
    have hcast : lam + ((n + 1 : ℕ) : Ordinal) = lam + (n : Ordinal) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    rw [hcast] at hw hn
    have hnle : n ≤ α.natPart := by
      by_contra hlt
      push_neg at hlt
      have hab : (α.natPart : Ordinal) < (n : Ordinal) := by exact_mod_cast hlt
      have h1 : lam + (α.natPart : Ordinal) < lam + (n : Ordinal) := (add_lt_add_iff_left lam).2 hab
      have key : lam + (α.natPart : Ordinal) + 1 ≤ lam + (n : Ordinal) := Order.add_one_le_iff.mpr h1
      have h2 : α + 1 ≤ lam + (n : Ordinal) := by rw [← hαsucc]; exact key
      exact absurd (lt_of_le_of_lt h2 (lt_of_lt_of_le (Order.lt_succ _) hn)) (lt_irrefl _)
    have hn' : lam + (n : Ordinal) ≤ α + 1 := le_trans (le_of_lt (Order.lt_succ _)) hn
    have hmono : ScatFun.Centered (lam + (n : Ordinal) + 1) ⊆ ScatFun.Centered (α + 1) := by
      have h := ScatFun.Centered_succ_mono hlim hnle
      rwa [hαsucc] at h
    rw [ScatFun.Generators_add_succ_eq hlim n] at hw
    rcases Finset.mem_union.mp hw with hwold | hwstep
    · exact ih hn' w hwold hwle
    · by_cases hwC : w ∈ ScatFun.Centered (lam + (n : Ordinal) + 1)
      · obtain ⟨hh, hhmem, hred⟩ :=
          hardCase_centered_reduces_finGl hα hA y hpc hgequiv hgP A j w (hmono hwC) hwle
        exact ⟨hh, hhmem, hred.trans (ScatFun.reduces_glBin_right _ _)⟩
      · by_cases hwW : ∃ S ∈ ScatFun.nonemptySubsets
              (ScatFun.nonemptySubsets (ScatFun.Generators (lam + (n : Ordinal)))),
            ∃ D : Finset ScatFun, D ⊆ ScatFun.Centered (lam + (n : Ordinal) + 1) ∧
              ScatFun.wedgeFinset (S.toList.map Finset.toList) D.toList = w
        · obtain ⟨S, hS, D, hD, rfl⟩ := hwW
          have hFGn : ScatFun.FGBelow (lam + (n : Ordinal) + 1) := fun β hβ =>
            hFG β (lt_of_lt_of_le hβ (le_trans hn (le_of_lt (Order.lt_succ (α + 1)))))
          obtain ⟨L, hLsub, hLred, homegaD, hglBin⟩ :=
            ScatFun.wedgeGenerator_bounding hlam hlim n hFGn S hS D hD
          obtain ⟨hh1, hh1mem, hh1red⟩ :
              ∃ hh1 ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (ScatFun.glList L) hh1 :=
            ScatFun.glList_reduces_finGl_of_forall L (fun x hx =>
              hardCase_centered_reduces_finGl hα hA y hpc hgequiv hgP A j x
                (hmono (hLsub x hx)) ((hLred x hx).trans hwle))
          obtain ⟨hh2, hh2mem, hh2red⟩ :=
            hardCase_omega_glList_reduces_glBin hα hFG hFrank hA y hpc hgequiv hgP hHmem A hdu hAmem
              j D (fun x hx => hmono (hD hx)) (homegaD.trans hwle)
          exact ⟨ScatFun.glBin hh1 hh2, ScatFun.finGl_glBin_mem hh1mem hh2mem,
            hglBin.trans ((ScatFun.glBin_reduces_of_reduces hh1red hh2red).trans
              (ScatFun.reduces_glBin_left_comm hh1 (ScatFun.glList H.toList) hh2))⟩
        · obtain ⟨c, hc, rfl⟩ :
              ∃ c ∈ ScatFun.Centered (lam + (n : Ordinal) + 1), ScatFun.omega c = w := by
            simp only [ScatFun.genStep, ScatFun.omegaImage, Finset.mem_union, Finset.mem_image,
              Finset.mem_biUnion, Finset.mem_powerset] at hwstep
            rcases hwstep with (hCn | hOm) | hWedge
            · exact absurd hCn hwC
            · exact hOm
            · exact absurd (by
                obtain ⟨S, hS, D, hD, hDw⟩ := hWedge
                exact ⟨S, hS, D, hD, hDw⟩) hwW
          have heq : ScatFun.Equiv (ScatFun.omega c)
              (ScatFun.omega (ScatFun.glList ({c} : Finset ScatFun).toList)) := by
            rw [Finset.toList_singleton]
            exact ScatFun.omega_equiv_congr (ScatFun.glList_single_equiv c)
          obtain ⟨hh, hhmem, hred⟩ :=
            hardCase_omega_glList_reduces_glBin hα hFG hFrank hA y hpc hgequiv hgP hHmem A hdu hAmem
              j ({c}) (Finset.singleton_subset_iff.mpr (hmono hc)) (heq.2.trans hwle)
          exact ⟨hh, hhmem, heq.1.trans hred⟩

/-- **Per-generator three-case bound** (memoir `6_double_successor_memo.tex:215-232`). A generator
`w ∈ 𝒢_{α+1}` with `w ≤ f^{[j]}` reduces into `\gl H ⊕ hh` for some `hh ∈ FinGl G`. Immediate
from `hardCase_gen_level_reduces_glBin` at level `n = α.natPart + 1` (since
`λ + (α.natPart + 1) = α + 1`). -/
lemma hardCase_generator_reduces_glBin
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ)
    (w : ScatFun)
    (hwgen : w ∈ ScatFun.Generators (α + 1))
    (hwle : ScatFun.Reduces w (F.restrict (diagBracketSet A y j))) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces w (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
  have hαeq : α.limitPart + ((α.natPart + 1 : ℕ) : Ordinal) = α + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Ordinal.eq_limitPart_add_natPart α]
  exact hardCase_gen_level_reduces_glBin hα hFG hFrank hA y hpc hgequiv hgP hHmem A hdu hAmem j
    (α.natPart + 1) (le_of_eq hαeq) w (hαeq ▸ hwgen) hwle

/- **Core of the Claim.** The `j`-th bracket reduces into `glList H ⊕ hh` for some `hh ∈ FinGl G`
(memoir `6_double_successor_memo.tex:203-233`). This is the genuinely double-successor-specific
generator case-split, assembled by a dichotomy on `CB(f^{[j]})` versus `λ = α.limitPart`: the
high-rank branch uses the FG decomposition `hardCase_bracket_fg_decomp` + the per-generator
bound `hardCase_generator_reduces_glBin` + `hardCase_bracket_combine`; the low-rank branch is
`hardCase_bracket_lowrank_reduces_glBin`. -/
/-- **Low-rank branch of the Claim** (memoir `6_double_successor_memo.tex:206-208`,
"`CB(f^{[j]}) < λ`"): when the bracket has CB-rank strictly below the limit part `λ`, the
general structure theorem collapses it below `\gl G ∈ FinGl G`, giving directly `f^{[j]} ≤ \gl G`
(hence `≤ \gl H ⊕ \gl G`).

**Proof.** `λ` is a nonzero limit (else `CB(f^{[j]}) < λ = 0` is impossible). The sandwiching
`g ≡ \pgl G` has `CB(g) = α+2` (every piece has that rank, `f↾P ≡ g`), so
`\pgl G = pgl(const \gl G)` has rank `succ(CB(\gl G)) = α+2` (`cbRank_pgl_const`), whence
`CB(\gl G) = α+1 > λ`. Therefore `f^{[j]} ≤ ℓ_λ = maxFun λ` by `reduces_maxFun_of_rank_le`
(its rank is `≤ λ`), and `ℓ_λ ≤ \gl G` by `maxFun_reduces_of_lam_lt_rank` (the General Structure
Theorem at the limit `λ`, since `λ < CB(\gl G)`). Finally `\gl G ∈ FinGl G`. -/
lemma hardCase_bracket_lowrank_reduces_glBin
    {α : Ordinal.{0}} (hα : α < omega1)
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (A : ℕ → Set ↑F.domain) (j : ℕ)
    (hlow : CBRank (F.restrict (diagBracketSet A y j)).func < α.limitPart) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces (F.restrict (diagBracketSet A y j))
        (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
  classical
  set lam := α.limitPart with hlamdef
  have hlam : lam < omega1 :=
    lt_of_le_of_lt (by rw [Ordinal.eq_limitPart_add_natPart α]; exact le_self_add) hα
  -- `lam` is a genuine (nonzero) limit: otherwise `hlow` would place the bracket's rank below 0.
  have hlim : Order.IsSuccLimit lam := by
    rcases Ordinal.limitPart_isLimit_or_zero α with h | h
    · rw [hlamdef]; exact h
    · rw [← hlamdef] at h
      exact absurd (h ▸ hlow) (by simp)
  -- **Rank of `g`.** Every piece has rank `α+2` (pairwise equivalence + partition), and
  -- `f↾P ≡ g`, so `CB(g) = α+2`.  (Same computation as `verticalTheorem_setup`.)
  have hy : y ∈ hA.cocenterSet := by rw [hpc.2.1]; rfl
  obtain ⟨p₀, -⟩ := hy
  have hpieces_rank : ∀ P ∈ Part, CBRank (F.restrict P).func = CBRank (F.restrict p₀.1).func :=
    fun P hP => cbRank_eq_of_equiv (hpc.2.2 P hP p₀.1 p₀.2)
  have hsUnion : CBRank (F.restrict (⋃₀ Part)).func = CBRank (F.restrict p₀.1).func :=
    cbRank_restrict_sUnion_const hA.countable hA.isClopen ⟨p₀.1, p₀.2⟩ hpieces_rank
  have hrank_univ : CBRank (F.restrict (Set.univ : Set ↑F.domain)).func = CBRank F.func := by
    rw [cbRank_restrict_eq]
    exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
  have hp₀_rank : CBRank (F.restrict p₀.1).func = α + 1 + 1 := by
    rw [← hsUnion, hA.sUnion_eq, hrank_univ, hFrank]
  have hgrank : CBRank g.func = α + 1 + 1 := by
    rw [← cbRank_eq_of_equiv (hgP p₀.1 p₀.2), hp₀_rank]
  -- **Rank of `gl G`.** `pglFinset G = pgl(const gl G)` has rank `succ (CB(gl G))`, and
  -- `g ≡ pglFinset G`, so `CB(gl G) = α+1 > lam`.
  have hpgl : CBRank (ScatFun.pglFinset G).func
      = Order.succ (CBRank (ScatFun.glList G.toList).func) :=
    ScatFun.cbRank_pgl_const _
  have hsucc : Order.succ (CBRank (ScatFun.glList G.toList).func) = Order.succ (α + 1) := by
    rw [← hpgl, ← cbRank_eq_of_equiv hgequiv, hgrank, Ordinal.add_one_eq_succ]
  have hglrank : CBRank (ScatFun.glList G.toList).func = α + 1 := Order.succ_injective hsucc
  have hlam_le : lam ≤ α :=
    le_self_add.trans_eq (Ordinal.eq_limitPart_add_natPart α).symm
  have hlam_lt_glrank : lam < CBRank (ScatFun.glList G.toList).func := by
    rw [hglrank, Ordinal.add_one_eq_succ]
    exact lt_of_le_of_lt hlam_le (Order.lt_succ α)
  -- **The collapse.** `bracket ≤ maxFun lam ≤ gl G` (general structure at the limit `lam`).
  have h1 : ScatFun.Reduces (F.restrict (diagBracketSet A y j)) (ScatFun.maxFun lam hlam) :=
    ScatFun.reduces_maxFun_of_rank_le _ lam hlam (le_of_lt hlow)
  have h2 : ScatFun.Reduces (ScatFun.maxFun lam hlam) (ScatFun.glList G.toList) :=
    ScatFun.maxFun_reduces_of_lam_lt_rank hlam hlim _ hlam_lt_glrank
  exact ⟨ScatFun.glList G.toList,
    ScatFun.finGl_of_equiv_glList (fun x hx => Finset.mem_toList.mp hx) (ScatFun.Equiv.refl _),
    (h1.trans h2).trans (ScatFun.reduces_glBin_right _ _)⟩

lemma hardCase_bracket_reduces_glBin
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hGsub : G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)))
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ) :
    ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces (F.restrict (diagBracketSet A y j))
        (ScatFun.glBin (ScatFun.glList H.toList) hh) := by
  classical
  by_cases hlamle : α.limitPart ≤ CBRank (F.restrict (diagBracketSet A y j)).func
  · -- High-rank branch: finite generation into `𝒢_{α+1}`, then the per-generator bound.
    have hHomega : ScatFun.Reduces (ScatFun.omega (ScatFun.glList H.toList))
        (ScatFun.glList H.toList) :=
      ScatFun.omega_glList_reduces_glList_of_omega_le (fun w hw =>
        ScatFun.omega_le_self_of_mem_omegaRegularSet (α + 1)
          (by simpa using omega1_add_nat α hα 1)
          ((hHmem w).mp (Finset.mem_toList.mp hw)).1)
    obtain ⟨L, hLgen, hLred, hfjL⟩ :=
      hardCase_bracket_fg_decomp hα hFG hFrank hA y hpc hgequiv hgP hGsub hHmem A hdu hAmem j hlamle
    exact hardCase_bracket_combine L hHomega
      (fun w hw => hardCase_generator_reduces_glBin hα hFG hFrank hA y hpc hgequiv hgP hHmem
        A hdu hAmem j w (hLgen w hw) (hLred w hw)) _ hfjL
  · -- Low-rank branch: general structure theorem collapse.
    exact hardCase_bracket_lowrank_reduces_glBin hα hFrank hA y hpc hgequiv hgP
      A j (lt_of_not_ge hlamle)

/-- **The Claim** (`6_double_successor_memo.tex:200-233`), per `j` — the genuinely
double-successor-specific step. For each `j`, the bracket `f^{[j]} = F.restrict (diagBracketSet
A y j)` admits a clopen partition `(A⁰_j, A¹_j)` of its domain with `f^{[j]}↾A⁰_j ≤ \gl H` and
`f^{[j]}↾A¹_j ≤ FinGl G`.

**Proved.** Strategy: it suffices to show `f^{[j]} ≤ \gl H ⊕ h` for some `h ∈ FinGl G`;
`reduces_glBin_split` (`DiagonalForLambdaPlusOne.lean`) then yields the clopen partition. Now
`CB(f^{[j]}) < α+2` (each ray has `CB ≤ α+1`), so either `CB(f^{[j]}) < λ` — then `f^{[j]} ≤ G` by
the general structure theorem — or, by `FG(≤α+1)` (`hFG`), `f^{[j]}` is a finite gluing of
generators `g_i ∈ 𝒢_{α+1}`. It then suffices to bound each generator `g ≤ f^{[j]}`, splitting on
`genStep`'s three clauses (the `generator_omega_equiv` idiom, `Generators/Basics.lean`):
1. **`g ∈ 𝒞_{α+1}` centered**: `f^{[j]} = ⊔_{i>j} ray_j(f_i) ≤ \gl_{i>j} ray_j(f_i)` and each
   `ray_j(f_i) ≤ FinGl G` (`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset`, this file, since
   each `f_i = F.restrict (A i)` is a piece `≡ g` with cocenter `y`), so `g ≤ G` by
   `centerInvariance_reduce` (`Theorems.lean`).
2. **`g ∈ 𝒲_{α+1}`**: `g ≤ f^{[j]} ≤ ray_j(f)`, so by `hHmem` either `g ≤ FinGl G`, or `g ∈ H`
   and hence `g ≤ \gl H` (`mem_reduces_glList`).
3. **`g` a wedge generator**: `wedgeGenerator_bounding` (`Generators/Basics.lean`) gives
   `F₀, F₁ ⊆ 𝒞_{α+1}` with `g ≤ (\gl F₀) ⊕ ω F₁`; `\gl F₀ ≤ G` by case 1 and `ω F₁ ≤ FinGl G` or
   `ω F₁ ≤ \gl H` by case 2, so `g ≤ \gl H ⊕ h`.
Per-generator bounds combine into `\gl H ⊕ (FinGl G)` since `FinGl G` is closed under finite
gluing (`finGl_gl_ite_of_forall_finGl`). -/
lemma hardCase_split_claim
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G H : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hGsub : G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)))
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j))
    (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (hAmem : ∀ i, A i ∈ Part ∨ A i = ∅) (j : ℕ) :
    ∃ A0j A1j : Set ↑F.domain,
      A0j ⊆ diagBracketSet A y j ∧ A1j ⊆ diagBracketSet A y j ∧
      IsClopen A0j ∧ IsClopen A1j ∧ Disjoint A0j A1j ∧
      A0j ∪ A1j = diagBracketSet A y j ∧
      ScatFun.Reduces (F.restrict A0j) (ScatFun.glList H.toList) ∧
      ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict A1j) hh := by
  obtain ⟨hh, hhmem, hred⟩ :=
    hardCase_bracket_reduces_glBin hα hFG hFrank hA y hpc hgequiv hgP hGsub hHmem A hdu hAmem j
  obtain ⟨Sa, Sb, hSa, hSb, hcla, hclb, hdisjS, hcovS, hreda, hredb⟩ :=
    ScatFun.reduces_glBin_split F (ScatFun.glList H.toList) hh (diagBracketSet A y j)
      (diagBracketSet_isClopen hdu y j) hred
  exact ⟨Sa, Sb, hSa, hSb, hcla, hclb, hdisjS, hcovS, hreda, hh, hhmem, hredb⟩

/-- **Phases E + F** (`6_double_successor_memo.tex:193-251`): the diagonal domain split. There
is a clopen partition `F.domain = A⁰ ⊔ A¹` with `F↾A⁰ ≤ \gl H` and `F↾A¹ ≤ g`.

**Proved**: the per-`j` `hardCase_split_claim` (all of the memoir's generator case-split) is
invoked here, then the pure **diagonal assembly** (memoir `:236-251`):
`A⁰ = ⋃_j A⁰_j`, `A¹ = A ∖ A⁰`. Openness of `A¹` uses that `A_i ∩ dom(f^{[j]}) = ∅` for `j ≥ i`,
so `A_i ∩ A⁰ = A_i ∩ ⋃_{j<i} A⁰_j` is clopen (`clopen_regroup`, `GlList.lean:552`, is the right
primitive — *not* `isClopen_iUnion_sub_partition`, whose one-sub-piece-per-block shape does not
fit). Then `f↾A⁰ ≤ \gl_j f↾A⁰_j ≤ ω(\gl H) ≡ \gl H` (the `A⁰_j` are pairwise disjoint since they
lie in the disjoint `RaySet_j`), and for every `j`, `ray_j(f↾A¹) = f↾A¹_j ⊔ ⊔_{i≤j} ray_j(f_i) ≤
FinGl G`, so `f↾A¹ ≤ \pgl G ≡ g` by `centeredAsPgluing_forward`. -/
theorem verticalTheorem_hardCase_split
    {α : Ordinal.{0}} (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    {F : ScatFun} (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y)
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (hGsub : G ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)))
    (H : Finset ScatFun)
    (hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      h ∉ ScatFun.FinGl G.toFinFun ∧ ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j)) :
    ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧ A0 ∪ A1 = Set.univ ∧ Disjoint A0 A1 ∧
      ScatFun.Reduces (F.restrict A0) (ScatFun.glList H.toList) ∧
      ScatFun.Reduces (F.restrict A1) g ∧
      ScatFun.Reduces g (F.restrict A1) ∧
      (∀ (h : IsCentered (F.restrict A1).func), cocenter (F.restrict A1).func h = y) := by
  classical
  -- Nonempty piece witness (from `Y_𝒫 = {y}`), and the disjoint `ℕ`-enumeration of `Part`.
  have hy : y ∈ hA.cocenterSet := by rw [hpc.2.1]; rfl
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := hy
  obtain ⟨A, hdu, hAmem, hA0mem⟩ := exists_partition_enumeration hA P₀ hP₀
  -- Per-`j` Claim: clopen split of each bracket `f^{[j]}`.
  have hclaim : ∀ j, ∃ A0j A1j : Set ↑F.domain,
      A0j ⊆ diagBracketSet A y j ∧ A1j ⊆ diagBracketSet A y j ∧
      IsClopen A0j ∧ IsClopen A1j ∧ Disjoint A0j A1j ∧
      A0j ∪ A1j = diagBracketSet A y j ∧
      ScatFun.Reduces (F.restrict A0j) (ScatFun.glList H.toList) ∧
      ∃ hh ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.restrict A1j) hh :=
    fun j => hardCase_split_claim hα hFG hFrank hA y hpc hgequiv hgP hGsub hHmem A hdu hAmem j
  -- Diagonal assembly (`A⁰ = ⋃_j A⁰_j`, `A¹ = A ∖ A⁰`); memoir `:236-251`.
  choose A0 A1 hs0 hs1 hc0 hc1 hd hcov hr0 hr1 using hclaim
  have hU : IsClopen (⋃ j, A0 j) := diag_iUnion_isClopen hdu y A0 hc0 hs0
  -- Each ray of `F↾A¹` at `y` reduces into `FinGl G` (memoir `:250`); this proves `F↾A¹ ≤ g`.
  have hA1ray : ∀ k : ℕ, ∃ hh ∈ ScatFun.FinGl G.toFinFun,
      ScatFun.Reduces ((F.restrict (⋃ j, A0 j)ᶜ).rayOn y Set.univ k) hh :=
    fun k => diag_A1_rayOn_reduces_finGl hA y hpc.2.1 hgequiv hgP A hdu hAmem A0 A1
      hs0 hs1 hcov hd hc1 hr1 k
  -- `F↾A⁰ ≤ gl H`.
  have hA0red : ScatFun.Reduces (F.restrict (⋃ j, A0 j)) (ScatFun.glList H.toList) := by
    have homega : ScatFun.Reduces (ScatFun.omega (ScatFun.glList H.toList))
        (ScatFun.glList H.toList) :=
      ScatFun.omega_glList_reduces_glList_of_omega_le (fun w hw =>
        ScatFun.omega_le_self_of_mem_omegaRegularSet (α + 1)
          (by simpa using omega1_add_nat α hα 1)
          ((hHmem w).mp (Finset.mem_toList.mp hw)).1)
    exact diag_A0_reduces_glList hdu y H A0 hc0 hs0 hr0 homega
  -- `F↾A¹ ≤ g`.
  have hA1g : ScatFun.Reduces (F.restrict (⋃ j, A0 j)ᶜ) g :=
    verticalTheorem_easyCase (F.restrict (⋃ j, A0 j)ᶜ) y hgequiv hA1ray
  -- `g ≤ F↾A¹`: the index-`0` piece `A 0` is excluded from every bracket (`i > j`), so
  -- `A 0 ⊆ A¹ = (⋃ⱼ A⁰ⱼ)ᶜ`, and `F↾(A 0) ≡ g` (a `𝒫`-piece), giving `g ≤ F↾(A 0) ≤ F↾A¹`.
  have hA0sub : A 0 ⊆ (⋃ j, A0 j)ᶜ := by
    intro x hx0
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro j hxj
    obtain ⟨hxU, -⟩ := hs0 j hxj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨hij, hxi⟩ := Set.mem_iUnion.mp hi
    exact (Set.disjoint_left.mp (hdu.2.1 0 i (by omega)) hx0) hxi
  have hgA1 : ScatFun.Reduces g (F.restrict (⋃ j, A0 j)ᶜ) :=
    ((hgP (A 0) hA0mem).symm.1).trans (restrict_reduces_of_subset F hA0sub)
  -- `cocenter(F↾A¹) = y`: the whole piece `A 0 ⊆ A¹` (cocenter `y`) fixes it, since `F↾A¹ ≡ F↾(A 0)`.
  have hcoc : ∀ (h : IsCentered (F.restrict (⋃ j, A0 j)ᶜ).func),
      cocenter (F.restrict (⋃ j, A0 j)ᶜ).func h = y := by
    intro h
    have hA0cent : IsCentered (F.restrict (A 0)).func := hA.centered (A 0) hA0mem
    have hEquiv : ScatFun.Equiv (F.restrict (⋃ j, A0 j)ᶜ) (F.restrict (A 0)) :=
      (show ScatFun.Equiv (F.restrict (⋃ j, A0 j)ᶜ) g from ⟨hA1g, hgA1⟩).trans
        (hgP (A 0) hA0mem).symm
    rw [cocenter_restrict_eq_of_subset_equiv F (A 0) (⋃ j, A0 j)ᶜ hA0sub hA0cent h hEquiv]
    have hmem : hA.cocenterOf hA0mem ∈ hA.cocenterSet := ⟨⟨A 0, hA0mem⟩, rfl⟩
    rw [hpc.2.1] at hmem
    exact hmem
  exact ⟨⋃ j, A0 j, (⋃ j, A0 j)ᶜ, hU, hU.compl, Set.union_compl_self _,
    disjoint_compl_right, hA0red, hA1g, hgA1, hcoc⟩

/-- **Clause 3** (`6_double_successor_memo.tex:190-191`, `w ≤ g`): the obstruction gluing
reduces into `g`. **Fully proved.** Each `h ∈ H` has `h ≤ ray_j(f)` for some `j`, and `ray_j(f) ≤
ω(glList G)` by `verticalTheorem_hardCase_rayOn_reduces_omegaG` (Phase D), so `h ≤ ω(glList G)` for
every `h ∈ H`. The finite gluing `\gl H` is then absorbed: `glList H ≤ ω(ω(glList G))` (a gluing of
functions each `≤ ω(glList G)`, `glList_reduces_omega_of_forall`), and `ω(ω(glList G)) ≡ ω(glList G)`
(`gl_const_omega_equiv`), then `ω(glList G) ≤ \pgl G ≡ g` (`omega_glList_reduces_pglFinset`,
`hgequiv.2`). This is the memoir's `w ≤ ω G ≤ \pgl G` chain. -/
theorem verticalTheorem_hardCase_glList_le_g
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hy : y ∈ hA.cocenterSet) (hcocset : hA.cocenterSet = {y})
    {g : ScatFun} {G : Finset ScatFun}
    (hgequiv : ScatFun.Equiv g (ScatFun.pglFinset G))
    (hgP : ∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g)
    (H : Finset ScatFun)
    (hHray : ∀ h ∈ H, ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j)) :
    ScatFun.Reduces (ScatFun.glList H.toList) g := by
  have hhω : ∀ h ∈ H.toList, ScatFun.Reduces h (ScatFun.omega (ScatFun.glList G.toList)) := by
    intro h hh
    obtain ⟨j, hj⟩ := hHray h (Finset.mem_toList.mp hh)
    exact hj.trans
      (verticalTheorem_hardCase_rayOn_reduces_omegaG hA y hy hcocset hgequiv hgP j)
  have h1 : ScatFun.Reduces (ScatFun.glList H.toList)
      (ScatFun.omega (ScatFun.omega (ScatFun.glList G.toList))) :=
    ScatFun.glList_reduces_omega_of_forall hhω
  have h2 : ScatFun.Reduces (ScatFun.omega (ScatFun.omega (ScatFun.glList G.toList)))
      (ScatFun.omega (ScatFun.glList G.toList)) :=
    (ScatFun.gl_const_omega_equiv (ScatFun.glList G.toList)).1
  exact h1.trans (h2.trans ((ScatFun.omega_glList_reduces_pglFinset G).trans hgequiv.2))

/-- **The Vertical Theorem** (`6_double_successor_memo.tex:150-160`). Let `α < ω₁` and assume
`FG(≤α+1)`, i.e. `FG(<α+2)` (`ScatFun.FGBelow (α+1+1)`). Let `F : ScatFun` with
`CB(F) = α+2` be pseudo-centered at `y`, witnessed by a fine `c`-partition `Part` (fine
relative to `α.limitPart`). Then there exist `g ∈ 𝒞_{α+2}` (`ScatFun.Centered (α+1+1)`) and a
finite `H ⊆ 𝒲_{α+1}` (`omegaRegularSet (α+1) _`) such that for every clopen neighbourhood `U`
of `y` there is a clopen `W ⊆ U` and a clopen domain-partition `F.domain = A⁰ ⊔ A¹` with:

1. `y ∉ W` and `F↾A⁰ ≤ gl H ≤ F⇂W`;
2. for every clopen `V ∋ y`, `F↾A¹ ≤ g ≤ F⇂V`;
3. `gl H ≤ g` (so, informally — not part of the formal statement below, since it is only an
   immediate corollary of 1–2 — `F ≤ g ⊔ g`, memoir's closing remark).

## Proof skeleton (`6_double_successor_memo.tex:161-251`), matching `LambdaPlusOne.lean`'s
## dispatcher style

Following `ScatFun.Generators_lambdaPlusOne_finitely_generates`'s pattern (one `by_cases`/
`rcases` dispatching into standalone case-theorems, rather than one monolithic proof), the body
below: (1) invokes `verticalTheorem_setup` (Phase A) once for the shared data `g`/`G`; (2)
derives the `g ≤ F⇂V` bound uniformly via `coRestrict_bound_of_common_cocenter`, valid
regardless of which branch is taken; (3) splits on whether `F`'s rays at `y` already lie in
`FinGl G` — the **easy case**, dispatched to `verticalTheorem_easyCase` (Phase B, fully proved)
with `H = ∅`; (4) the remaining **hard case** (`𝒫` infinite with a genuine `𝒲`-obstruction,
`6_double_successor_memo.tex:174-233`): its branch defines the obstruction
`Finset H` and assembles the extracted phase lemmas `verticalTheorem_hardCase_C` (Phase C,
**proved**), `verticalTheorem_hardCase_glList_le_g` (clause 3, **proved**), and
`verticalTheorem_hardCase_split` (Phases E+F, **proved**), documented at
their declarations and below.

### The hard case (fully proved)

Let `H = { h ∈ 𝒲_{α+1} | h ≰ FinGl G ∧ ∃ j, h ≤ ray_j(f) }` and `w = \gl H`
(`ScatFun.glList H.toList`). The hard case is broken into the top-level lemmas below (mirroring
`refiningBy1`'s phase breakdown in `Fine.lean`). Phases C, D, E, F and clause 3 are all proved;
item (E) is `hardCase_split_claim` and item (F) is the diagonal assembly inside
`verticalTheorem_hardCase_split`, both now discharged:

* **(C) `w ≤ f⇂W`** for a suitable clopen `W` with `y ∉ W ⊆ U`, any clopen `U ∋ y`
  (`:180-187`): **now proved** as `verticalTheorem_hardCase_C`. Every `h ∈ H` has infinite
  ray-index set (nonempty by `∃ j` in `H`'s definition, hence infinite since `(f,y)` is not a
  lump — `pseudoCentered_obstruction_infinite_or_empty`, C1 above). The implementation departs
  slightly from the memoir's `exists_common_finite_bound` route: instead of a common finite `J`,
  it picks a *strictly increasing* ray index `idx n` per list position (`exists_strictMono_forall_mem`)
  above the tail threshold `M` where `RaySet_j ⊆ U` (`exists_tail_raySet_subset`, the clopen-nbhd
  construction shared with `refiningBy1_exists_regularizing_nbhd`). Then `W = ⋃_{n} RaySet_{idx n}`,
  and `glList H ≤ f⇂W` follows by routing the *distinct* blocks into the *disjoint* rays
  (`glList_reduces_coRestrict_biUnion_rays`, C3 above) — the injective index choice removes the
  need for the memoir's `Intertwinereductionsforomegacentered` packing step.
* **(D) `w ≤ g`** (`:190-191`): every ray of `f` reduces into `\omega G`. This step needs *two*
  translation lemmas that do not yet exist at the `ScatFun.rayOn`/`FinGl` level used throughout
  this file (checked directly — searched the whole repo for a `rayOn`/`FinGl`-level corollary
  of rigidity and found none):
  1. **piece-ray ↦ `FinGl G`**: `rigidityOfCocenter_finiteGluing`/`_reducibleByPieces`
     (`CenteredFunctions/Theorems.lean`, Prop. 4.4, fully proved) are stated at the *raw*
     `ContinuouslyReduces`/predicate-subtype level (`{a : domain | ∀ k<n, ...}`), not in terms
     of `ScatFun.rayOn`/`ScatFun.Reduces`/`FinGl` — genuine new plumbing is needed to instantiate
     them at `G = pglFinset G`/`pgl (repSeq G.toFinFun)` and repackage the conclusion, in the
     style already carried out (for other fixed targets) by
     `CenteredFunctions/SimpleSuccessorOfLimit.lean`'s `centered_two_rayOn_finImage` and
     `CenteredFunctions/SimpleSuccessor/LimitCase.lean`'s `pgl_rayOn_zeroStream_cbRank_lt` — use
     those as the template. `RayFun_pgl_zeroStream_reduces_block`
     (`SimpleSuccessor/LamOne.lean:142`) gives the needed "ray of `pgl s` at `zeroStream`
     reduces into the single block `s n`" fact for the constant sequence
     `repSeq G.toFinFun`, landing in `FinGl G.toFinFun` trivially
     (`ScatFun.finGl_of_equiv_glList`/`glList_single_equiv`,
     `ScatFun/LevelsFinitelyGenerated/GlList.lean`).
  2. **disjoint union of `FinGl G`-bounded pieces ↦ `\omega G`**: `scatFun_reduces_gl_of_domain_partition`
     (`CenteredFunctions/SimpleSuccessor/Shared.lean`) only gives `f ≤ gl(pieces)`, which still
     needs combining with a bound on each piece. **Now closed**: `ScatFun.finGl_reduces_omega_glList`
     (just above `verticalTheorem_setup` in this file, fully proved) shows every
     `a ∈ FinGl S.toFinFun` reduces into `omega (glList S.toList)` directly — turned out to need
     *no* reindexing at all, since `omega (glList S.toList) = gl (fun _ => glList S.toList)`
     already has the same constant target block at every index, so `gl_reduces_of_pointwise`
     applies with the identity embedding (each block of `Gl S.toFinFun t` is either `empty` or a
     single `S.toFinFun i`, and `reduces_block_gl` embeds it into `glList S.toList` directly).
     Composing `scatFun_reduces_gl_of_domain_partition` (piecewise: `f rayOn ≤ gl(piece rays)`)
     with `gl_reduces_of_pointwise` (using item 1's per-piece `FinGl G` bound) and
     `finGl_reduces_omega_glList` (bounding each resulting block by `omega (glList G.toList)`)
     gives `ray_j(f) ≤ omega G`. Both translation lemmas are now in place, so Phase D is proved.
  Once both hold: `h ∈ H` reduces into `\omega G` by definition of `H`, hence so does `w`; and
  `\omega G ≤ \pgl G ≡ g` (`ScatFun.gl_reduces_pgl_direct`, `ScatFun/Operations/GlReduces.lean`,
  confirmed present and usable with `e = id`).
* **(E) The Claim** (`:203-233`, the hardest, genuinely double-successor-specific step):
  fixing an `ℕ`-enumeration `(A_i)` of `Part` (`Set.Countable.exists_eq_range`, the same idiom
  as `cbRank_restrict_sUnion_const`/`Fine.lean`), `f_i = F.restrict (A i)`, and
  `f^{[j]} = F.restrict ((⋃_{i > j} A i) ∩ {x | F.func x ∈ RaySet univ y j})` (expressible
  directly via `F.restrict`, no nested nested nested restricts needed — a genuinely new
  definition, not reused from elsewhere), for every `j` there is a clopen partition
  `(A⁰_j, A¹_j)` of `dom(f^{[j]})` with `f^{[j]}↾A⁰_j ≤ w` and `f^{[j]}↾A¹_j ≤ FinGl G`. Proved
  by unfolding `f^{[j]}` (via `FG(≤α+1)`) as a finite gluing of `Generators (α+1)` and
  case-splitting each generator on `genStep`'s three defining clauses (the `simp
  [genStep, omegaImage, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
  Finset.mem_powerset]` + `rcases _ with (hCn | hOmega) | hWedge` idiom of
  `generator_omega_equiv`, `ScatFun/Generators/Basics.lean`): centered generators reduce into
  `G` (`centerInvariance_reduce`/`centerInvariance_equiv`, `Theorems.lean`, combined with the
  rigidity facts above); `𝒲`-regular generators either reduce into `FinGl G` or, by definition
  of `H`, into `w`; **wedge generators** split via `wedgeGenerator_bounding`
  (`ScatFun/Generators/Basics.lean`, fully proved) into a centered part (into `G`, as above)
  and an `ω`-tower part (into `w` or `FinGl G` as for the `𝒲`-regular case).
* **(F) Assembly** (`:236-251`): `A⁰ = ⋃_j A⁰_j`, `A¹ = A \ A⁰`. The general clopen-openness
  tool `isClopen_iUnion_sub_partition` (`GeneralTopology/ClopenPartitions.lean`) does not literally
  apply (its `D i ⊆ A i` shape assumes one sub-piece per block, whereas `A⁰_j` here cuts across
  infinitely many `𝒫`-pieces); a genuinely new diagonal argument is needed. `clopen_regroup`
  (`ScatFun/LevelsFinitelyGenerated/GlList.lean:552`, confirmed present and fully proved: given a
  countable clopen partition `Q` and any `t : ℕ → ℕ`, the pullback `⋃_{t k = n} Q k` is clopen)
  is the right primitive for this — *not* `exists_simple_block_decomposition`
  (`LambdaPlusOne.lean:1533`), which solves a different problem (distinguishing infinitely many
  points within a single rank-`λ+1` block) despite using `clopen_regroup` internally. Then
  `f↾A⁰ ≤ \gl_j f↾A⁰_j ≤ \omega w ≡ w` (`scatFun_reduces_gl_of_domain_partition` again) and,
  for every `j`, `ray_j(f↾A¹) ≤ FinGl G`, so `f↾A¹ ≤ \pgl G ≡ g` by `centeredAsPgluing_forward`
  applied to `f↾A¹` (the same tool as Phase B's `h1`/`h2`/`h3` chain).

`FG(≤α+1)` is spelled `ScatFun.FGBelow (α+1+1)`, matching `6_double_successor_memo.tex:151`'s
own convention `FG(≤α+1) = FG(<α+2)` and the existing `ScatFun.FGBelow` naming
(`FGBelow.lean`). -/

theorem verticalTheorem
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (y : Baire) (hpc : hA.IsPseudoCenteredAt α.limitPart y) :
    ∃ g : ScatFun, g ∈ ScatFun.Centered (α + 1 + 1) ∧
      (∀ P ∈ Part, ScatFun.Equiv (F.restrict P) g) ∧
      ∃ H : Finset ScatFun, H ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
        ∀ U : Set Baire, IsClopen U → y ∈ U →
          ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧
            ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧
              A0 ∪ A1 = Set.univ ∧ Disjoint A0 A1 ∧
              (y ∉ W ∧
                ScatFun.Reduces (F.restrict A0) (ScatFun.glList H.toList) ∧
                ScatFun.Reduces (ScatFun.glList H.toList) (F.coRestrict W)) ∧
              (∀ V : Set Baire, IsClopen V → y ∈ V →
                ScatFun.Reduces (F.restrict A1) g ∧ ScatFun.Reduces g (F.coRestrict V)) ∧
              ScatFun.Reduces (ScatFun.glList H.toList) g ∧
              ScatFun.Reduces g (F.restrict A1) ∧
              (∀ (h : IsCentered (F.restrict A1).func),
                cocenter (F.restrict A1).func h = y) := by
  obtain ⟨g, G, hgC, hGne, hGsub, hgequiv, hgP⟩ :=
    verticalTheorem_setup α hα hFG F hFrank hA y hpc
  have hy : y ∈ hA.cocenterSet := by simp [hpc.2.1]
  have hcorestrict : ∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V) :=
    coRestrict_bound_of_common_cocenter hA hy hgP
  -- `g ≤ F↾univ`, used for the easy-case `A¹ = univ`.
  have hgUniv : ScatFun.Reduces g (F.restrict Set.univ) := by
    obtain ⟨⟨P₀, hP₀⟩, -⟩ := hy
    exact ((hgP P₀ hP₀).symm.1).trans (restrict_reduces_of_subset F (Set.subset_univ P₀))
  by_cases heasy : ∀ j : ℕ, ∃ h ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (F.rayOn y Set.univ j) h
  · -- **Easy case**: `F ≤ g` outright (Phase B), no `𝒲`-obstruction needed, so `H = ∅`.
    refine ⟨g, hgC, hgP, ∅, Finset.empty_subset _, fun U hUcl hyU => ?_⟩
    have hFg : ScatFun.Reduces F g := verticalTheorem_easyCase F y hgequiv heasy
    have hA1_reduces_F : ScatFun.Reduces (F.restrict (Set.univ : Set ↑F.domain)) F :=
      ⟨fun x => ⟨x.val, x.property.choose⟩, by fun_prop, id, continuousOn_id, fun x => rfl⟩
    have hA0_isEmpty : IsEmpty ↑(F.restrict (∅ : Set ↑F.domain)).domain :=
      Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])
    have hglListNil_domain : (ScatFun.glList ((∅ : Finset ScatFun).toList)).domain = ∅ := by
      simp [ScatFun.glList, ScatFun.gl_domain, GluingSet, ScatFun.empty]
    have hglListNil_isEmpty :
        IsEmpty ↑(ScatFun.glList ((∅ : Finset ScatFun).toList)).domain :=
      Set.isEmpty_coe_sort.mpr hglListNil_domain
    refine ⟨∅, Set.empty_subset _, isClopen_empty, ∅, Set.univ, isClopen_empty, isClopen_univ,
      by simp, by simp,
      ⟨by simp, ScatFun.reduces_of_isEmpty_domain hA0_isEmpty,
        ScatFun.reduces_of_isEmpty_domain hglListNil_isEmpty⟩,
      fun V hVcl hyV => ⟨hA1_reduces_F.trans hFg, hcorestrict V hVcl hyV⟩,
      ScatFun.reduces_of_isEmpty_domain hglListNil_isEmpty, hgUniv,
      fun h => by
        obtain ⟨⟨P₀, hP₀⟩, -⟩ := hy
        have hP0cent : IsCentered (F.restrict P₀).func := hA.centered P₀ hP₀
        have hEquiv : ScatFun.Equiv (F.restrict Set.univ) (F.restrict P₀) :=
          ⟨(hA1_reduces_F.trans hFg).trans (hgP P₀ hP₀).symm.1,
            restrict_reduces_of_subset F (Set.subset_univ P₀)⟩
        rw [cocenter_restrict_eq_of_subset_equiv F P₀ Set.univ (Set.subset_univ P₀) hP0cent h hEquiv]
        have hmem : hA.cocenterOf hP₀ ∈ hA.cocenterSet := ⟨⟨P₀, hP₀⟩, rfl⟩
        rw [hpc.2.1] at hmem
        exact hmem⟩
  · -- **Hard case**: genuine `𝒲`-obstruction. `H = {h ∈ 𝒲_{α+1} | h ≰ FinGl G ∧ ∃ j, h ≤ ray_j}`;
    -- assemble Phases C (`W`), E+F (`A0`/`A1` split), and clause 3 (`\gl H ≤ g`), with the
    -- `g ≤ f⇂V` bound coming uniformly from `hcorestrict`.
    classical
    have hα1 : α + 1 < omega1 := by simpa using omega1_add_nat α hα 1
    set H : Finset ScatFun :=
      (omegaRegularSet (α + 1) hα1).filter
        (fun h => h ∉ ScatFun.FinGl G.toFinFun ∧
          ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j)) with hHdef
    have hHsub : H ⊆ omegaRegularSet (α + 1) hα1 := Finset.filter_subset _ _
    have hHmem : ∀ h, h ∈ H ↔ h ∈ omegaRegularSet (α + 1) hα1 ∧ h ∉ ScatFun.FinGl G.toFinFun ∧
        ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j) :=
      fun h => by rw [hHdef]; exact Finset.mem_filter
    have hHchar : ∀ h ∈ H, h ∉ ScatFun.FinGl G.toFinFun ∧
        ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j) :=
      fun h hh => ((hHmem h).mp hh).2
    have hHray : ∀ h ∈ H, ∃ j : ℕ, ScatFun.Reduces h (F.rayOn y Set.univ j) :=
      fun h hh => (hHchar h hh).2
    -- Clause 3, U-independent.
    have hwg : ScatFun.Reduces (ScatFun.glList H.toList) g :=
      verticalTheorem_hardCase_glList_le_g hA y hy hpc.2.1 hgequiv hgP H hHray
    -- The diagonal domain split, U-independent.
    obtain ⟨A0, A1, hA0cl, hA1cl, hcover, hdisj, hA0red, hA1red, hgA1, hcoc⟩ :=
      verticalTheorem_hardCase_split hα hFG hFrank hA y hpc hgequiv hgP hGsub H hHmem
    refine ⟨g, hgC, hgP, H, hHsub, fun U hUcl hyU => ?_⟩
    obtain ⟨W, hWU, hWcl, hyW, hWred⟩ :=
      verticalTheorem_hardCase_C hα hFrank hA y hpc H hHsub hHray U hUcl hyU
    exact ⟨W, hWU, hWcl, A0, A1, hA0cl, hA1cl, hcover, hdisj,
      ⟨hyW, hA0red, hWred⟩,
      fun V hVcl hyV => ⟨hA1red, hcorestrict V hVcl hyV⟩, hwg, hgA1, hcoc⟩

end
