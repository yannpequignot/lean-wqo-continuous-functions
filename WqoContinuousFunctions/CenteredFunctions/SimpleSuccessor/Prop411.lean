import WqoContinuousFunctions.CenteredFunctions.Finiteness
import WqoContinuousFunctions.CenteredFunctions.LocallyCentered.Theorem
import WqoContinuousFunctions.ScatFun.Basics
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

/-!
# §4.3 — Simple at a successor of a limit: general infrastructure & Proposition 4.11

Extracted from `SimpleSuccessorOfLimit.lean`.  General CB/disjoint-union infrastructure,
Proposition 4.11 (`Simpleiffcoincidenceofcocenters`), and the `gl`-equivalence criterion
`equiv_gl_of_codomain_clopen_partition`.
-/

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section


/-!
## Proposition 4.11 (`Simpleiffcoincidenceofcocenters`)

Let `f` be in `𝒞`, written `f = ⊔ᵢ fᵢ` for a sequence `(fᵢ)ᵢ` of centered functions, and
set `I = {n | CB(fₙ) = supᵢ CB(fᵢ)}`.

1. `CB(f)` is successor `⟺ I ≠ ∅`.
2. The CB-degree of `f` is the cardinality of the set of cocenters `{y_n | n ∈ I}`.

In particular, `f` is simple `⟺ I ≠ ∅` and the cocenters `(y_n)_{n ∈ I}` all coincide
(with the distinguished point of `f`).

Item 2, which quantifies the *degree*, is not transcribed below: the CB-degree is not yet
a primitive in the development (only its `= 1` specialisation, `SimpleFun`, is).  The two
scaffolded statements are item 1 and the simple-iff specialisation, which are the parts
consumed by Theorem 4.12.
-/

/-
**Helper.** A centered scattered function has successor CB-rank.
A centered scattered function is simple (`scatteredCentered_isSimple` /
`centered_scattered_simple_structure`), and simple functions have CB-rank a successor
ordinal.  The cocenter of `G.func` (well-defined by `scatteredHaveCocenter`) provides the
distinguished value `y` required by `centered_scattered_simple_structure`.
-/
lemma centered_scatFun_rank_succ (G : ScatFun) (hc : IsCentered G.func) :
    ∃ α : Ordinal.{0}, CBRank G.func = Order.succ α := by
  obtain ⟨α, hα⟩ : ∃ α, CBRank G.func = Order.succ α ∧ ∃ y, ∀ x, IsCenterFor G.func x → G.func x = y := by
    exact ⟨ Classical.choose ( centered_scattered_simple_structure G.func G.hScat hc ( G.func hc.choose ) fun x hx => scatteredHaveCocenter G.func G.hScat x hc.choose hx hc.choose_spec ), Classical.choose_spec ( centered_scattered_simple_structure G.func G.hScat hc ( G.func hc.choose ) fun x hx => scatteredHaveCocenter G.func G.hScat x hc.choose hx hc.choose_spec ) |>.1, _, fun x hx => scatteredHaveCocenter G.func G.hScat x hc.choose hx hc.choose_spec ⟩;
  exact ⟨ α, hα.1 ⟩


/-
**Helper.** `CBLevel` is unchanged by post-composing the function with an injective map
on the codomain: the isolated-locus condition `f y = f x` is equivalent to `h (f y) = h (f x)`
when `h` is injective.
-/
lemma cbLevel_comp_injective_left {X : Type} {Y Z : Type*} [TopologicalSpace X]
    (h : Y → Z) (hh : Function.Injective h) (f : X → Y) (β : Ordinal.{0}) :
    CBLevel (fun x => h (f x)) β = CBLevel f β := by
  contrapose! hh;
  simp_all +decide [ CBLevel ];
  contrapose! hh;
  congr! 2;
  ext; simp +decide [ isolatedLocus, hh.eq_iff ] ;


/-!
## Proposition 4.11 — disjoint-union framing (infinite case)

The memoir's `f = ⊔ᵢ fᵢ` is **not** the index-tagging gluing `ScatFun.gl` (which prepends
the block index to the codomain value).  It is a single `F : ScatFun` together with a
countable **clopen partition `(Aᵢ)` of its domain**; the blocks are the *restrictions*
`F.restrict (Aᵢ)`, which keep `F`'s codomain untouched.  Only with this framing are the
block cocenters genuine values of `F`, so the cocenter-coincidence characterisation of
simplicity holds.  (It is *false* for `ScatFun.gl`, whose CB-degree is `|I|` regardless of
the cocenters — this was the modelling mistake corrected here.)

We treat the **infinite (`ℕ`-indexed)** case; the finite (`Fin n`) case is deferred.  Note a
finite partition cannot simply be padded to `ℕ` with empty blocks, since the empty function
is not centered, so the two index shapes need separate treatment.
-/

/- The disjoint-union infrastructure (`ScatFun.IsDisjointUnion`, `ScatFun.topRankIndex`,
`cbRank_restrict_eq`, `cbRank_eq_iSup_restrict`) lives in `ScatFun/Basics.lean`. -/

/-
**Proposition 4.11, item 1.**  With `f = ⊔ᵢ fᵢ` a disjoint union of centered functions
(`F.IsDisjointUnion A`, each block centered) and `I = F.topRankIndex A`, the CB-rank of `f`
is a successor iff `I` is non-empty.

## Provided solution

By `cbRank_eq_iSup_restrict`, `CB(f) = supᵢ CB(fᵢ)`.

(⟹) If `CB(f) = β+1` then `β < supᵢ CB(fᵢ)`, so some block has `β < CB(fₙ) ≤ sup`, forcing
`CB(fₙ) = β+1 = sup`, i.e. `n ∈ I`.

(⟸) If `n ∈ I` then `CB(fₙ) = sup = CB(f)`; `fₙ` is centered hence of successor rank
(`centered_scatFun_rank_succ`), so `CB(f)` is a successor too.
-/
theorem CBrank_succ_iff_index_nonempty (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A)
    (hcent : ∀ i, IsCentered (F.restrict (A i)).func) :
    (∃ β : Ordinal.{0}, CBRank F.func = β + 1) ↔ (F.topRankIndex A).Nonempty := by
  constructor <;> intro h
  · obtain ⟨β, hβ⟩ := h
    rw [cbRank_eq_iSup_restrict F A hdu] at hβ
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup
      (show β < ⨆ i, CBRank (F.restrict (A i)).func from hβ.symm ▸ Order.lt_succ β)
    exact ⟨i, le_antisymm (le_ciSup (Ordinal.bddAbove_of_small _) i) (by simpa [hβ] using hi)⟩
  · obtain ⟨n, hn⟩ := h
    obtain ⟨β, hβ⟩ := centered_scatFun_rank_succ (F.restrict (A n)) (hcent n)
    refine ⟨β, ?_⟩
    have hn' : CBRank (F.restrict (A n)).func = ⨆ i, CBRank (F.restrict (A i)).func := hn
    rw [cbRank_eq_iSup_restrict F A hdu, ← hn', hβ, Ordinal.add_one_eq_succ]


/-- **Block/global CB-level bridge.**  For a clopen (here only open is needed) block
`A ⊆ F.domain`, a point `z` of the block domain lies in `CBLevel (F.restrict A).func β` iff
its realization `F.restrictEquiv A z` (as a point of `F.domain`) lies in `CBLevel F.func β`. -/
lemma cbLevel_block_iff (F : ScatFun) (A : Set ↑F.domain) (hA : IsOpen A) (β : Ordinal.{0})
    (z : ↑(F.restrict A).domain) :
    z ∈ CBLevel (F.restrict A).func β ↔
      ((F.restrictEquiv A z : ↑F.domain)) ∈ CBLevel F.func β := by
  show z ∈ CBLevel ((F.func ∘ (Subtype.val : A → ↑F.domain)) ∘ (F.restrictEquiv A)) β ↔ _
  rw [CBLevel_homeomorph, Set.mem_preimage]
  exact CBLevel_open_restrict F.func A hA β (F.restrictEquiv A z)


/-- A centered scattered function is constant (equal to its cocenter) on its last nonempty
CB-level `CBLevel α`, where `CBRank = succ α`. -/
lemma block_const_on_top (G : ScatFun) (hc : IsCentered G.func) (α : Ordinal.{0})
    (hrank : CBRank G.func = Order.succ α) :
    ∀ x ∈ CBLevel G.func α, G.func x = cocenter G.func hc := by
  have hy : ∀ x, IsCenterFor G.func x → G.func x = cocenter G.func hc := fun x hx =>
    scatteredHaveCocenter G.func G.hScat x hc.choose hx hc.choose_spec
  obtain ⟨α', hrank', -, -, hconst⟩ :=
    centered_scattered_simple_structure G.func G.hScat hc (cocenter G.func hc) hy
  have hαα : α' = α := Order.succ_injective (hrank'.symm.trans hrank)
  subst hαα
  exact hconst


/-- If `CBLevel f α` is nonempty and `CBLevel f (succ α)` is empty, then `CBRank f = succ α`. -/
lemma cbRank_eq_succ_of_simple_witness {X : Type} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (α : Ordinal.{0})
    (hne : (CBLevel f α).Nonempty) (hempty : CBLevel f (Order.succ α) = ∅) :
    CBRank f = Order.succ α := by
  refine le_antisymm (CBRank_le_of_CBLevel_empty f _ hempty) (Order.succ_le_of_lt ?_)
  by_contra h
  push_neg at h
  exact hne.ne_empty
    (Set.subset_eq_empty (CBLevel_antitone f h) (CBLevel_eq_empty_at_rank f hf))


/-- Membership in `topRankIndex` is exactly having block CB-rank `succ β`, when `CBRank F = succ β`. -/
lemma mem_topRankIndex_iff (F : ScatFun) (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (n : ℕ) (β : Ordinal.{0}) (hR : CBRank F.func = Order.succ β) :
    n ∈ F.topRankIndex A ↔ CBRank (F.restrict (A n)).func = Order.succ β := by
  unfold ScatFun.topRankIndex
  rw [Set.mem_setOf_eq, ← cbRank_eq_iSup_restrict F A hdu, hR]


/-
**Proposition 4.11, "in particular" (⟹ direction).**

If `f = ⊔ᵢ fᵢ` (disjoint union of centered blocks) is **simple**, then `I = F.topRankIndex A`
is non-empty and the block cocenters `(yₙ)_{n ∈ I}` all coincide with `f`'s *distinguished
point* `y` — the value `f` takes on its last non-empty CB-level `CBₐ(f)`.

## Provided solution

By item 1, `I ≠ ∅`.  Simplicity gives `α` with `CB(f) = α+1`, `CBₐ(f)` non-empty, and `f ≡ y`
constant on `CBₐ(f)`.  For `n ∈ I`, `CB(fₙ) = α+1`, so `CBₐ(fₙ) ≠ ∅`; as `Aₙ` is clopen,
`CBₐ(fₙ)` embeds into `CBₐ(f)` (`CBLevel_open_restrict`), where `f` — hence the block `fₙ` —
is constantly `y`.  The cocenter of `fₙ` is exactly that constant value
(`scatteredHaveCocenter` applied at a center of `fₙ` lying in `CBₐ(fₙ)`), so `yₙ = y`.

Note: the `α, y` returned are precisely the `SimpleFun` witnesses for `f`, exposed so callers
(e.g. Theorem 4.12) can use the distinguished point `ȳ`.
-/
theorem simple_implies_cocenters_eq_distinguished (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A)
    (hcent : ∀ i, IsCentered (F.restrict (A i)).func)
    (hsimple : SimpleFun F.func) :
    ∃ (α : Ordinal.{0}) (y : Baire),
      (CBLevel F.func α).Nonempty ∧
      CBLevel F.func (Order.succ α) = ∅ ∧
      (∀ x ∈ CBLevel F.func α, F.func x = y) ∧
      (∀ m ∈ F.topRankIndex A, cocenter (F.restrict (A m)).func (hcent m) = y) := by
  obtain ⟨α, hne, hempty, y, hconst⟩ := hsimple
  refine ⟨α, y, hne, hempty, hconst, ?_⟩
  intro m hm
  have hRrank : CBRank F.func = Order.succ α :=
    cbRank_eq_succ_of_simple_witness F.func F.hScat α hne hempty
  have hblockrank : CBRank (F.restrict (A m)).func = Order.succ α :=
    (mem_topRankIndex_iff F A hdu m α hRrank).mp hm
  obtain ⟨z, hz⟩ : (CBLevel (F.restrict (A m)).func α).Nonempty :=
    CBLevel_nonempty_below_rank _ (F.restrict (A m)).hScat α (hblockrank ▸ Order.lt_succ α)
  have hx : ((F.restrictEquiv (A m) z : ↑F.domain)) ∈ CBLevel F.func α :=
    (cbLevel_block_iff F (A m) (hdu.1 m).isOpen α z).mp hz
  have hco : (F.restrict (A m)).func z = cocenter (F.restrict (A m)).func (hcent m) :=
    block_const_on_top (F.restrict (A m)) (hcent m) α hblockrank z hz
  have hval : (F.restrict (A m)).func z = F.func (F.restrictEquiv (A m) z : ↑F.domain) := rfl
  rw [← hco, hval]
  exact hconst _ hx


/-
**Proposition 4.11, "in particular" (⟸ direction).**

Conversely, if `I = F.topRankIndex A` is non-empty and the block cocenters `(yₙ)_{n ∈ I}` all
coincide, then `f = ⊔ᵢ fᵢ` is **simple**.

## Provided solution

By item 1 (using `I ≠ ∅`), `CB(f) = α+1` is a successor.  The top level splits over the
partition, `CBₐ(f) = ⊔_{n ∈ I} CBₐ(fₙ)` (blocks with `CB(fₙ) < α+1` contribute nothing to
`CBₐ`), and on each `CBₐ(fₙ)` the block — hence `f` — is constantly the cocenter `yₙ`
(`scatteredHaveCocenter`).  Since the `yₙ` coincide, `f` is constant on `CBₐ(f)`; together
with `CBLevel f (α+1) = ∅` this is exactly simplicity of `f`.
-/
theorem cocenters_coincide_implies_simple (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A)
    (hcent : ∀ i, IsCentered (F.restrict (A i)).func)
    (hI : (F.topRankIndex A).Nonempty)
    (hcoin : ∀ m ∈ F.topRankIndex A, ∀ n ∈ F.topRankIndex A,
      cocenter (F.restrict (A m)).func (hcent m)
        = cocenter (F.restrict (A n)).func (hcent n)) :
    SimpleFun F.func := by
  obtain ⟨β, hβ⟩ := (CBrank_succ_iff_index_nonempty F A hdu hcent).mpr hI
  rw [Ordinal.add_one_eq_succ] at hβ
  obtain ⟨m₀, hm₀⟩ := hI
  refine ⟨β, ?_, ?_, cocenter (F.restrict (A m₀)).func (hcent m₀), ?_⟩
  · exact CBLevel_nonempty_below_rank F.func F.hScat β (hβ ▸ Order.lt_succ β)
  · rw [← hβ]; exact cbLevel_at_cbRank_empty F.func F.hScat
  · intro x hx
    obtain ⟨n, hn⟩ : ∃ n, x ∈ A n := by
      have hxu : x ∈ ⋃ i, A i := hdu.2.2 ▸ Set.mem_univ x
      exact Set.mem_iUnion.mp hxu
    have hzmem : x.val ∈ (F.restrict (A n)).domain := ⟨x.property, hn⟩
    set z : ↑(F.restrict (A n)).domain := ⟨x.val, hzmem⟩ with hzdef
    have hreq : (F.restrictEquiv (A n) z : ↑F.domain) = x := by
      apply Subtype.ext; rfl
    have hzlevel : z ∈ CBLevel (F.restrict (A n)).func β :=
      (cbLevel_block_iff F (A n) (hdu.1 n).isOpen β z).mpr (hreq ▸ hx)
    have hblockle : CBRank (F.restrict (A n)).func ≤ Order.succ β := by
      rw [← hβ, cbRank_eq_iSup_restrict F A hdu]
      exact le_ciSup (Ordinal.bddAbove_of_small _) n
    have hblockgt : β < CBRank (F.restrict (A n)).func := by
      by_contra h; push_neg at h
      have hnonempty : (CBLevel (F.restrict (A n)).func β).Nonempty := ⟨z, hzlevel⟩
      exact hnonempty.ne_empty
        (Set.subset_eq_empty (CBLevel_antitone _ h)
          (CBLevel_eq_empty_at_rank _ (F.restrict (A n)).hScat))
    have hblockrank : CBRank (F.restrict (A n)).func = Order.succ β :=
      le_antisymm hblockle (Order.succ_le_of_lt hblockgt)
    have hnI : n ∈ F.topRankIndex A := (mem_topRankIndex_iff F A hdu n β hβ).mpr hblockrank
    have hco : (F.restrict (A n)).func z = cocenter (F.restrict (A n)).func (hcent n) :=
      block_const_on_top (F.restrict (A n)) (hcent n) β hblockrank z hzlevel
    have hval : (F.restrict (A n)).func z = F.func (F.restrictEquiv (A n) z : ↑F.domain) := rfl
    rw [hval, hreq] at hco
    rw [hco]
    exact hcoin n hnI m₀ hm₀


/-- **`UsefulcriterionforequivFinGl`** (Corollary, `2_prelim_memo.tex`), `ScatFun` form.

If the codomain pieces `(B i)` form a clopen partition of the Baire space and, for every
`i`, the corestriction `F ↾ (B i)` is continuously equivalent to `(G i).func`, then
`F ≡ gl_i (G i)`.

This certifies a `gl` equivalence by exhibiting *both* a clopen partition of the domain (for
the upper bound) and a clopen partition of the codomain (for the lower bound).  Theorem 4.12
consumes it in the binary case `B = ![¬W, W]` to get `g ≡ g|_{¬W} ⊕ g|_{W}` for clopen
`W ⊆ im g`.

It is stated here in this leaf file rather than next to `ScatFun.gl`: adding declarations to
the widely-imported `ScatFun/Operations.lean` perturbs downstream `grind` proofs (see
`LocallyCentered/Helpers.lean`).  Once proved it can be relocated with care.

## Provided solution

* **`F ≤ gl G`** (`Gluingasupperbound`): the codomain partition `(B i)` pulls back to the
  *domain* clopen partition `(F.func ⁻¹' B i)`; on each block `F ↾ (B i) ≤ (G i).func`, so
  `clopen_partition_to_gluing_reduces` gives `F ≤ gl G`.
* **`gl G ≤ F`** (`Gluingaslowerbound`): the `(B i)` are pairwise-disjoint relatively clopen
  in `im F`; on each block `(G i).func ≤ F ↾ (B i)`, giving `gl G ≤ F`. -/

/-
Upper bound for `equiv_gl_of_codomain_clopen_partition`: `F` reduces to `gl G`.
-/
lemma reduces_F_gl_of_codomain
    (F : ScatFun) (G : ℕ → ScatFun) (B : ℕ → Set (ℕ → ℕ))
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB_cover : ⋃ i, B i = Set.univ)
    (hequiv : ∀ i, ContinuouslyEquiv (CoRestrict' F.domain F.func (B i)) (G i).func) :
    ScatFun.Reduces F (ScatFun.gl G) := by
  -- Let's define the partition P i := {x : F.domain | F.func x ∈ B i}.
  set P : ℕ → Set F.domain := fun i => {x | F.func x ∈ B i} with hP_def
  have hP_clopen : ∀ i, IsClopen (P i) := by
    intro i; specialize hB_clopen i; exact ⟨ IsClosed.preimage ( F.hCont ) hB_clopen.1, IsOpen.preimage ( F.hCont ) hB_clopen.2 ⟩ ;
  have hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
    exact fun i j hij => Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp ( hB_disj i j hij ) hx hx'
  have hP_cover : ⋃ i, P i = F.domain := by
    simp_all +decide [ Set.ext_iff ];
    exact fun x => ⟨ fun ⟨ i, hi, hi' ⟩ => hi, fun hx => by obtain ⟨ i, hi ⟩ := hB_cover ( F.func ⟨ x, hx ⟩ ) ; exact ⟨ i, hx, hi ⟩ ⟩
  generalize_proofs at *;
  -- By `hequiv i`, we obtain per-block `σ_i : P i → (G i).domain` and `τ_i` with `F.func x = τ_i ((G i).func (σ_i ⟨x,_⟩))` for `x ∈ P i`, and `τ_i` continuous on range.
  obtain ⟨σ_i, τ_i, hσ_i, hτ_i⟩ : ∃ (σ_i : ∀ i, P i → (G i).domain) (τ_i : ∀ i, (ℕ → ℕ) → (ℕ → ℕ)), (∀ i, Continuous (σ_i i)) ∧ (∀ i, ContinuousOn (τ_i i) (range ((G i).func ∘ σ_i i))) ∧ (∀ i, ∀ x : P i, F.func x = τ_i i ((G i).func (σ_i i x))) := by
    have hσ_i : ∀ i, ∃ (σ_i : P i → (G i).domain) (τ_i : (ℕ → ℕ) → (ℕ → ℕ)), Continuous σ_i ∧ ContinuousOn τ_i (range ((G i).func ∘ σ_i)) ∧ ∀ x : P i, F.func x = τ_i ((G i).func (σ_i x)) := by
      intro i
      obtain ⟨σ_i, τ_i, hσ_i, hτ_i⟩ := hequiv i |>.1
      generalize_proofs at *; (
      use fun x => σ_i ⟨x, by
        exact ⟨ x.1.2, x.2 ⟩⟩, hσ_i
      generalize_proofs at *; (
      refine ⟨ ?_, ?_, ?_ ⟩
      all_goals generalize_proofs at *;
      · exact τ_i.comp <| Continuous.subtype_mk ( continuous_subtype_val.comp <| continuous_subtype_val ) _;
      · refine' hτ_i.1.mono _;
        exact Set.range_subset_iff.mpr fun x => ⟨ _, rfl ⟩;
      · intro x; specialize hτ_i; have := hτ_i.2 ⟨ x, by solve_by_elim ⟩ ; simp_all +decide [ CoRestrict' ] ;))
    generalize_proofs at *; (
    exact ⟨ fun i => Classical.choose ( hσ_i i ), fun i => Classical.choose_spec ( hσ_i i ) |> Classical.choose, fun i => Classical.choose_spec ( hσ_i i ) |> Classical.choose_spec |> And.left, fun i => Classical.choose_spec ( hσ_i i ) |> Classical.choose_spec |> And.right |> And.left, fun i x => Classical.choose_spec ( hσ_i i ) |> Classical.choose_spec |> And.right |> And.right |> fun h => h x ⟩)
  generalize_proofs at *;
  -- Build `σ_raw : F.domain → Baire` by continuous_pasting_on_clopen on the partition `P`, with block map `x ↦ prepend i (σ_i x).val` (continuous by `continuous_prepend ∘ σ_i`); get `σ_raw` continuous with `σ_raw x = prepend i (σ_i ⟨x,hi⟩).val` on `P i`, and `σ_raw x ∈ GluingSet (fun i => (G i).domain)` (mem_gluingSet_prepend).
  obtain ⟨σ_raw, hσ_raw⟩ : ∃ σ_raw : F.domain → ℕ → ℕ, Continuous σ_raw ∧ (∀ i, ∀ x : P i, σ_raw x = prepend i (σ_i i x).val) ∧ (∀ x, σ_raw x ∈ GluingSet (fun i => (G i).domain)) := by
    have := continuous_pasting_on_clopen ( P ) ( Set.univ ) ( fun i => hP_clopen i ) ( fun i j hij => hP_disj i j hij ) ( by
      grind ) ( fun i => fun x : P i => prepend i ( σ_i i x ).val ) ( fun i => continuous_prepend i |> Continuous.comp <| continuous_subtype_val.comp <| hσ_i i ) ( fun i j hij => by
      intro k hk; have := hP_disj j k; simp_all +decide [ Set.disjoint_left ] ;
      grind +ring )
    generalize_proofs at *;
    obtain ⟨ σ_raw, hσ_raw₁, hσ_raw₂ ⟩ := this; use fun x => σ_raw ⟨ x, trivial ⟩ ; simp_all +decide [ GluingSet ] ;
    refine ⟨ hσ_raw₁.comp ?_, ?_, ?_ ⟩
    all_goals generalize_proofs at *;
    · exact continuous_id.subtype_mk _;
    · exact fun i a b hi => hσ_raw₂ a b i hi;
    · intro a ha; specialize hP_cover; replace hP_cover := Set.ext_iff.mp hP_cover a; simp_all +decide [ Set.mem_iUnion ] ;
      obtain ⟨ i, hi ⟩ := hP_cover; use i; specialize hσ_raw₂ a ha i hi; aesop;
  generalize_proofs at *;
  refine ⟨ fun x => ⟨ σ_raw x, hσ_raw.2.2 x ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ ScatFun.gl ];
  · exact Continuous.subtype_mk hσ_raw.1 _;
  · refine ⟨ fun z => τ_i ( z 0 ) ( unprepend z ), ?_, ?_ ⟩ <;> simp_all +decide [ GluingFunVal ];
    · convert gluing_backward_tau_cont _ _ _ _ _ _ _ _ using 1;
      use fun i => P i;
      exact hP_cover;
      use fun i x => σ_i i ⟨ ⟨ x.val, by
        exact x.2.choose_spec.2.symm ▸ x.2.choose.2 ⟩, by
        grind ⟩
      all_goals generalize_proofs at *;
      · convert hτ_i.1 using 1;
        congr! 2;
        ext; simp [ScatFun.glBlock];
        exact ⟨ fun ⟨ a, ha, ha' ⟩ => ⟨ a, ha.1, ha.2, ha' ⟩, fun ⟨ a, ha, ha', ha'' ⟩ => ⟨ a, ⟨ ha, ha' ⟩, ha'' ⟩ ⟩;
      · exact hσ_raw.1;
      · grind;
    · intro a ha; specialize hτ_i; have := hτ_i.2 ( σ_raw ⟨ a, ha ⟩ 0 ) a ha; simp_all +decide [ prepend, ScatFun.glBlock ] ;
      convert this _ using 1;
      grind +suggestions;
      obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hB_cover.symm ▸ Set.mem_univ ( F.func ⟨ a, ha ⟩ ) ) ; specialize hσ_raw ; have := hσ_raw.2.1 i ⟨ ⟨ a, ha ⟩, hi ⟩ ; simp_all +decide [ prepend ] ;
      grobner


/-- **Codomain-corestriction blocks of `F`.**  For a clopen codomain piece `B i`, the block
`Fb F B i` is the restriction of `F` to the domain piece `{y | F.func y ∈ B i}`.  Its underlying
function is definitionally `CoRestrict' F.domain F.func (B i)`. -/
def Fb (F : ScatFun) (B : ℕ → Set (ℕ → ℕ)) (i : ℕ) : ScatFun :=
  F.restrict {y : ↑F.domain | F.func y ∈ B i}


lemma Fb_func_eq (F : ScatFun) (B : ℕ → Set (ℕ → ℕ)) (i : ℕ) :
    (Fb F B i).func = CoRestrict' F.domain F.func (B i) := rfl


/-
**`Gluingaslowerbound`, corestriction form.**  The plain gluing of the codomain-corestriction
blocks of `F` reduces to `F`.

`σ` re-realizes a block-`i` point `(i)⌐a` of the gluing as the point `a ∈ F.domain` (forgetting
the prepended block index); `τ` re-prepends the block index, recovered from which clopen piece
`B i` the value `F.func a` lands in (well-defined and continuous because `(B i)` is a clopen
partition).
-/
lemma gl_corestrict_reduces (F : ScatFun) (B : ℕ → Set (ℕ → ℕ))
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB_cover : ⋃ i, B i = Set.univ) :
    ScatFun.Reduces (ScatFun.gl (Fb F B)) F := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ unprepend x.val, by
    obtain ⟨ i, hi, ha ⟩ := GluingSet_inverse_short ( fun i => ( Fb F B i ).domain ) x ; simp_all +decide [ Fb ] ;
    exact ha.1 ⟩
  all_goals generalize_proofs at *;
  exact Continuous.subtype_mk ( continuous_unprepend.comp continuous_subtype_val ) _;
  exact fun z => prepend ( Classical.choose ( Set.mem_iUnion.mp ( hB_cover ▸ Set.mem_univ z ) ) ) z;
  refine ⟨ ?_, ?_ ⟩
  all_goals generalize_proofs at *;
  · apply_rules [ continuousOn_piecewise_clopen ];
    rotate_right;
    use fun i z => prepend i z;
    · exact fun z hz => by rcases hz with ⟨ x, rfl ⟩ ; exact Set.mem_iUnion.mp ( hB_cover ▸ Set.mem_univ _ ) ;
    · intro z hz i hi j hj; specialize hB_disj i j; by_cases hij : i = j <;> simp_all +decide [ Set.disjoint_left ] ;
    · exact fun i => Continuous.continuousOn ( continuous_prepend i );
    · exact fun z hz => Set.mem_iUnion.mp ( hB_cover ▸ Set.mem_univ z );
    · intro z hz i hi; have := Classical.choose_spec ( Set.mem_iUnion.mp ( hB_cover ▸ Set.mem_univ z ) ) ; simp_all +decide ;
      exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( hB_disj _ _ <| by aesop ) this hi;
  · intro x
    obtain ⟨i, hi, ha⟩ := GluingSet_inverse_short (fun i => (Fb F B i).domain) x
    have hx : x.val = prepend i (unprepend x.val) := by
      rw [ ← hi, prepend_unprepend ]
    have hval : F.func ⟨unprepend x.val, by
      exact ha.1⟩ ∈ B i := by
      exact ha.choose_spec
    generalize_proofs at *;
    convert GluingFunVal_prepend ( fun i => ( Fb F B i ).domain ) ( fun _ => Set.univ ) ( ScatFun.glBlock ( Fb F B ) ) i ⟨ unprepend x.val, ha ⟩ _ using 1;
    convert rfl;
    · exact hx.symm;
    · simp +decide [ ScatFun.glBlock ];
      congr! 1
      generalize_proofs at *;
      exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( hB_disj _ _ h ) ( Classical.choose_spec ‹∃ x_1, F.func ⟨ unprepend x, ha.1 ⟩ ∈ B x_1› ) hval;
    · grind +splitIndPred


/-- Lower bound for `equiv_gl_of_codomain_clopen_partition`: `gl G` reduces to `F`. -/
lemma reduces_gl_F_of_codomain
    (F : ScatFun) (G : ℕ → ScatFun) (B : ℕ → Set (ℕ → ℕ))
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB_cover : ⋃ i, B i = Set.univ)
    (hequiv : ∀ i, ContinuouslyEquiv (CoRestrict' F.domain F.func (B i)) (G i).func) :
    ScatFun.Reduces (ScatFun.gl G) F := by
  have hGFb : ∀ i, ScatFun.Reduces (G i) (Fb F B i) := fun i => (hequiv i).2
  exact (ScatFun.gl_reduces_of_pointwise G (Fb F B) hGFb).trans
    (gl_corestrict_reduces F B hB_clopen hB_disj hB_cover)


theorem equiv_gl_of_codomain_clopen_partition
    (F : ScatFun) (G : ℕ → ScatFun) (B : ℕ → Set (ℕ → ℕ))
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB_cover : ⋃ i, B i = Set.univ)
    (hequiv : ∀ i, ContinuouslyEquiv (CoRestrict' F.domain F.func (B i)) (G i).func) :
    ScatFun.Equiv F (ScatFun.gl G) :=
  ⟨reduces_F_gl_of_codomain F G B hB_clopen hB_disj hB_cover hequiv,
   reduces_gl_F_of_codomain F G B hB_clopen hB_disj hB_cover hequiv⟩

end
