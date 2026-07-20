import WqoContinuousFunctions.DoubleSuccessor.Diagonal.Basic
import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.Representatives
import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.Vertical

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Diagonal theorem, second case — block data (`6_double_successor_memo.tex`)

Builds, for each block `A_g` of the second-case decomposition, the *induced* `c`-partition on
the restriction `F↾A_g` and verifies it is pseudo-centered / `ω`-regular at the transported
cocenter, culminating in `secondCase_singleBlockData` and `secondCase_blockData`. These are the
per-block inputs to the diagonal construction of Chapter 6 (double-successor case).

**The induced `c`-partition of a block.** Transporting the ambient pieces `P ∈ blockPieces g y`
(all contained in the block `A_g = ⋃₀ blockPieces g y`) down through the restrict homeomorphism
`F.restrictEquiv A_g` yields a `c`-partition of `hA.piece g y = F.restrict A_g`. Pure bookkeeping
across the restrict-of-restrict boundary (mirrors `cPartition_restrict_transport`), using
`blockPieces_sUnion_isClopen` and `ScatFun.restrict_restrict_equiv`.
-/
theorem block_induced_isCPartition
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (g : ScatFun) (y : Baire) :
    (hA.piece g y).IsCPartition
      ((fun P => {w : ↑(hA.piece g y).domain |
          (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ P}) ''
        (hA.blockPieces g y)) := by
  -- Let's denote the block as `A := ⋃₀ hA.blockPieces g y`, so `hA.piece g y = F.restrict A` (definitionally).
  set A := ⋃₀ hA.blockPieces g y with hA_def;
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact Set.Countable.image ( Set.Countable.mono ( fun P hP => hP.choose ) hA.countable ) _;
  · rintro _ ⟨ P, hP, rfl ⟩;
    convert hA.isClopen P hP.1 |> IsClopen.preimage <| show Continuous ( fun w : ( F.restrict A ).domain => ( F.restrictEquiv A w : F.domain ) ) from ?_ using 1;
    exact Continuous.comp ( continuous_subtype_val ) ( F.restrictEquiv A |> Homeomorph.continuous );
  · intro P hP Q hQ hPQ; simp_all +decide ;
    obtain ⟨ P, hP, rfl ⟩ := hP; obtain ⟨ Q, hQ, rfl ⟩ := hQ; simp_all +decide [ Set.disjoint_left ] ;
    intro a ha hPa hQa; have := hA.pairwiseDisjoint ( hP.choose ) ( hQ.choose ) ; simp_all +decide [ Set.disjoint_left ] ;
    exact this ( by aesop_cat ) _ _ hPa hQa;
  · ext w
    simp only [coe_setOf, mem_setOf_eq, sUnion_image, mem_iUnion, exists_prop, mem_univ, iff_true];
    grind;
  · rintro _ ⟨ P, hP, rfl ⟩;
    convert isCentered_of_equiv _ ( ScatFun.restrict_restrict_equiv F A P ?_ ) using 1;
    · exact hA.centered P hP.choose;
    · exact Set.subset_sUnion_of_mem hP

/-
**Cocenter is preserved by re-realization of the domain.** The doubly-restricted function
`(F.restrict D).restrict {w | (F.restrictEquiv D w) ∈ A0}` (for `A0 ⊆ D`) has the same `func` as
`F.restrict A0` up to a domain homeomorphism (`restrict_restrict_func_eq`), so its cocenter equals
that of `F.restrict A0`.
-/
theorem ScatFun.cocenter_restrict_restrict_eq (F : ScatFun) (D A0 : Set ↑F.domain)
    (hA0D : A0 ⊆ D)
    (h1 : IsCentered ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func)
    (h2 : IsCentered (F.restrict A0).func) :
    cocenter ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func h1
      = cocenter (F.restrict A0).func h2 := by
  have h_func_eq : ((F.restrict D).restrict {w | (F.restrictEquiv D w : ↑F.domain) ∈ A0}).func = (F.restrict A0).func ∘ (Homeomorph.setCongr (ScatFun.restrict_restrict_domain_eq F D A0 hA0D)) :=
    ScatFun.restrict_restrict_func_eq F D A0 hA0D
  have h_center_eq : IsCenterFor (F.restrict A0).func (Homeomorph.setCongr (ScatFun.restrict_restrict_domain_eq F D A0 hA0D) h1.choose) := by
    grind [IsCenterFor.comp_homeomorph];
  convert scatteredHaveCocenter ( F.restrict A0 ).func ( F.restrict A0 ).hScat _ _ h_center_eq h2.choose_spec using 1

/-
**A nonempty block is `𝒲`-regular at `y`.** Since the ambient partition is fine (no lumps),
the block `(g, y)` — which has centered `g`, cocenter `y`, and rank `> lam` — cannot be a lump, so
`hA.piece g y = F.restrict (⋃₀ blockPieces g y)` is `𝒲`-regular at `y`
(`isOmegaRegularAt_blockPieces_of_not_lump`).
-/
theorem block_isOmegaRegularAt {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}} (hfine : hA.IsFine lam)
    {g : ScatFun} {y : Baire} (hne : (hA.blockPieces g y).Nonempty) :
    IsOmegaRegularAt (hA.piece g y) y := by
  obtain ⟨ P, hP ⟩ := hne;
  convert isOmegaRegularAt_blockPieces_of_not_lump hA _ _ _ _;
  exact lam;
  · exact fun g y hg => False.elim <| hfine.1 g y hg;
  · have := hA.centered P hP.choose;
    convert isCentered_of_equiv this _;
    exact hP.choose_spec.1.symm;
  · exact Set.mem_range.mpr ⟨ ⟨ P, hP.choose ⟩, hP.choose_spec.2 ⟩;
  · exact hfine.2 P hP.choose |> fun h => h.trans_le ( cbRank_eq_of_equiv hP.choose_spec.1 ▸ le_rfl )

/-
**`𝒲`-regularity transfers to the restriction to the whole domain.** Since `E.restrict univ`
re-realizes `E` (a domain homeomorphism preserving `func`), it is `𝒲`-regular at `y` whenever `E`
is.
-/
theorem isOmegaRegularAt_restrict_univ (E : ScatFun) (y : Baire)
    (h : IsOmegaRegularAt E y) : IsOmegaRegularAt (E.restrict Set.univ) y := by
  intro w hw
  generalize_proofs at *;
  have h_rank_eq : CBRank (E.restrict Set.univ).func = CBRank E.func := by
    rw [cbRank_restrict_eq];
    convert CBRank_comp_homeomorph ( Homeomorph.Set.univ ↑E.domain ) E.func using 1
  generalize_proofs at *; (
  have h_ray_eq : ∀ j : ℕ, ScatFun.Reduces w ((E.restrict Set.univ).rayOn y Set.univ j) ↔ ScatFun.Reduces w (E.rayOn y Set.univ j) := by
    intro j
    have h_ray_eq : ScatFun.Equiv ((E.restrict Set.univ).rayOn y Set.univ j) (E.rayOn y Set.univ j) := by
      convert ScatFun.rayOn_restrict_equiv E Set.univ y j using 1
    generalize_proofs at *; (
    exact ⟨ fun h => h.trans h_ray_eq.1, fun h => h.trans h_ray_eq.2 ⟩)
  generalize_proofs at *; (
  convert h w _ using 1 <;> aesop ( simp_config := { singlePass := true } ) ;))

/-
**The induced block partition has cocenter set `{y}`.** Every induced block `S P` is `Equiv` to
`F.restrict P` (`restrict_restrict_equiv`), whose cocenter is `y` (as `P ∈ blockPieces g y`); with
the block nonempty this pins the cocenter set to `{y}`. Uses `cocenter_restrict_restrict_eq`.
-/
theorem block_induced_cocenterSet {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) (g : ScatFun) (y : Baire)
    (hne : (hA.blockPieces g y).Nonempty) :
    (block_induced_isCPartition hA g y).cocenterSet = {y} := by
  ext z
  simp only [ScatFun.IsCPartition.cocenterSet, coe_setOf, mem_setOf_eq, mem_range, Subtype.exists, mem_image, mem_singleton_iff];
  constructor;
  · rintro ⟨ a, ⟨ P, hP, rfl ⟩, rfl ⟩;
    convert ScatFun.cocenter_restrict_restrict_eq F ( ⋃₀ hA.blockPieces g y ) P _ _ _ using 1;
    convert hP.choose_spec.2.symm using 1;
    exact Set.subset_sUnion_of_mem hP;
  · rintro rfl;
    obtain ⟨P, hP⟩ : ∃ P ∈ hA.blockPieces g z, True := by
      exact ⟨ _, hne.choose_spec, trivial ⟩;
    refine' ⟨ _, ⟨ P, hP.1, rfl ⟩, _ ⟩;
    convert ScatFun.cocenter_restrict_restrict_eq F (⋃₀ hA.blockPieces g z) P (Set.subset_sUnion_of_mem hP.1) _ _ using 1;
    convert hP.1.choose_spec.2.symm

/-
**The induced block partition has no lumps.** For any `(g', y')`, if the induced sub-block is
nonempty then it re-realizes the whole block `hA.piece g y` (all induced blocks are `Equiv`, so the
sub-block union is everything), which is `𝒲`-regular by `block_isOmegaRegularAt`; and if empty it is
trivially regular. Either way `(g', y')` is not a lump.
-/
theorem block_induced_noLumps {F : ScatFun} {Part : Set (Set ↑F.domain)}
    (hA : F.IsCPartition Part) {lam : Ordinal.{0}} (hfine : hA.IsFine lam)
    (g : ScatFun) (y : Baire) (hne : (hA.blockPieces g y).Nonempty) :
    ∀ g' y', ¬ (block_induced_isCPartition hA g y).IsLump g' y' := by
  intro g' y';
  by_cases hy : y' = y <;> simp_all +decide [ ScatFun.IsCPartition.IsLump ];
  · intro hy hcent
    by_cases hempty : (block_induced_isCPartition hA g y).blockPieces g' y = ∅;
    · convert isOmegaRegularAt_of_isEmpty_domain _ _ y;
      simp +decide only [ScatFun.IsCPartition.piece, hempty, sUnion_empty, isEmpty_coe_sort];
      simp +decide [ ScatFun.restrict ];
    · obtain ⟨ S₀, hS₀ ⟩ := Set.nonempty_iff_ne_empty.mpr hempty;
      have h_equiv : ScatFun.Equiv g' g := by
        obtain ⟨ P₀, hP₀ ⟩ := hS₀.1
        have h_equiv : ScatFun.Equiv ((hA.piece g y).restrict S₀) g' := by
          exact hS₀.2.1
        have h_equiv' : ScatFun.Equiv ((hA.piece g y).restrict (S₀)) (F.restrict P₀) := by
          rw [ ← hP₀.2 ];
          apply ScatFun.restrict_restrict_equiv;
          exact Set.subset_sUnion_of_mem hP₀.1
        have h_equiv'' : ScatFun.Equiv (F.restrict P₀) g := by
          exact hP₀.1.choose_spec.1
        have h_equiv''' : ScatFun.Equiv g' g := by
          exact h_equiv.symm.trans ( h_equiv'.trans h_equiv'' )
        exact h_equiv''';
      have h_union : ⋃₀ (block_induced_isCPartition hA g y).blockPieces g' y = Set.univ := by
        refine Set.eq_univ_of_forall fun x => ?_;
        obtain ⟨ P, hP, hP' ⟩ := (block_induced_isCPartition hA g y).sUnion_eq ▸ Set.mem_univ x;
        obtain ⟨ Q, hQ, rfl ⟩ := hP;
        refine ⟨ ?_, ?_, ?_ ⟩;
        exact { w : ↑ ( hA.piece g y ).domain | ( F.restrictEquiv ( ⋃₀ hA.blockPieces g y ) w : ↑F.domain ) ∈ Q };
        · refine ⟨ ?_, ?_, ?_ ⟩;
          grind;
          · convert ScatFun.restrict_restrict_equiv F ( ⋃₀ hA.blockPieces g y ) Q ( Set.subset_sUnion_of_mem hQ ) |> ScatFun.Equiv.trans <| hQ.choose_spec.1 |> ScatFun.Equiv.trans <| h_equiv.symm using 1;
          · convert hQ.choose_spec.2 using 1;
            convert ScatFun.cocenter_restrict_restrict_eq F ( ⋃₀ hA.blockPieces g y ) Q ( Set.subset_sUnion_of_mem hQ ) _ _ using 1;
        · exact hP';
      convert isOmegaRegularAt_restrict_univ ( hA.piece g y ) y ( block_isOmegaRegularAt hA hfine hne ) using 1;
      exact h_union ▸ rfl;
  · have := block_induced_cocenterSet hA g y hne; simp_all +decide [ ScatFun.IsCPartition.cocenterSet ] ;

/-
**A block restriction is pseudo-centered** (memoir `6_double_successor_memo.tex:306`, "for all
`g ∈ M` the function `f↾A_g` is pseudo-centered"). Here `A_g = ⋃₀ (hA.blockPieces g y)` is the
union of the pieces of `𝒫` that are `Equiv` to `g` and have cocenter `y`, and `hA.piece g y` is
`F.restrict A_g`. Provided the block is nonempty (`hne`) and the ambient partition is fine
(`hfine`), the induced `c`-partition of `F↾A_g` — its pieces the images of the `blockPieces` under
the `restrictEquiv` — has cocenter set `{y}` and pairwise-equivalent blocks (all `≡ g`), i.e. is
pseudo-centered at `y` (relative to the same `lam`). This is the linchpin that lets the Vertical
Theorem apply to each block in the Diagonal Theorem's second case.
-/
theorem block_induced_isPseudoCenteredAt
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {lam : Ordinal.{0}} (hfine : hA.IsFine lam) (g : ScatFun) (y : Baire)
    (hne : (hA.blockPieces g y).Nonempty) :
    (block_induced_isCPartition hA g y).IsPseudoCenteredAt lam y := by
  refine ⟨ ⟨ ?_, ?_ ⟩, ?_, ?_ ⟩;
  · exact block_induced_noLumps hA hfine g y hne;
  · rintro _ ⟨ P, hP, rfl ⟩;
    convert hfine.2 P hP.choose using 1;
    convert cbRank_eq_of_equiv ( ScatFun.restrict_restrict_equiv F ( ⋃₀ hA.blockPieces g y ) P ( Set.subset_sUnion_of_mem hP ) ) using 1;
  · exact block_induced_cocenterSet hA g y hne;
  · simp +zetaDelta at *;
    intro P hP Q hQ;
    convert ScatFun.Equiv.trans ( ScatFun.restrict_restrict_equiv F ( ⋃₀ hA.blockPieces g y ) P ( Set.subset_sUnion_of_mem hP ) ) ( ScatFun.Equiv.trans ( hP.choose_spec.1 ) ( hQ.choose_spec.1.symm ) ) |> ScatFun.Equiv.trans <| ScatFun.Equiv.symm ( ScatFun.restrict_restrict_equiv F ( ⋃₀ hA.blockPieces g y ) Q ( Set.subset_sUnion_of_mem hQ ) ) using 1

theorem block_isPseudoCenteredAt
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {lam : Ordinal.{0}} (hfine : hA.IsFine lam) (g : ScatFun) (y : Baire)
    (hne : (hA.blockPieces g y).Nonempty) :
    ∃ (Part_B : Set (Set ↑(hA.piece g y).domain)) (hB : (hA.piece g y).IsCPartition Part_B),
      hB.IsPseudoCenteredAt lam y :=
  ⟨_, block_induced_isCPartition hA g y, block_induced_isPseudoCenteredAt hA hfine g y hne⟩

/-
**Pushforward of a clopen subset of a restricted domain.** If `D ⊆ ↑F.domain` is clopen and
`S` is a clopen subset of `(F.restrict D).domain`, then `S` is the pullback (under the
`restrictEquiv` inclusion) of a clopen `A ⊆ D ⊆ ↑F.domain`. Concretely `A` is the image of `S`
under `w ↦ (F.restrictEquiv D w : ↑F.domain)`, which is a clopen embedding onto `D`. This is the
tool that transports a clopen split of a block's domain back to `F.domain`.
-/
lemma ScatFun.exists_pushforward_clopen (F : ScatFun) (D : Set ↑F.domain)
    (S : Set ↑(F.restrict D).domain) (hDcl : IsClopen D) (hScl : IsClopen S) :
    ∃ A : Set ↑F.domain, IsClopen A ∧ A ⊆ D ∧
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A} = S := by
  set e := F.restrictEquiv D with he
  have heS : IsClopen (e '' S) :=
    ⟨e.isClosedMap _ hScl.1, e.isOpenMap _ hScl.2⟩
  refine ⟨(fun w => (e w : ↑F.domain)) '' S, ?_, ?_, ?_⟩
  · have himg : (fun w => (e w : ↑F.domain)) '' S = Subtype.val '' (e '' S) := by
      rw [Set.image_image]
    rw [himg]
    exact ⟨hDcl.1.isClosedMap_subtype_val _ heS.1, hDcl.2.isOpenMap_subtype_val _ heS.2⟩
  · exact Set.image_subset_iff.mpr fun x _ => (e x).2
  · ext w
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w', hw', hval⟩
      rwa [e.injective (Subtype.ext hval)] at hw'
    · intro hw; exact ⟨w, hw, rfl⟩

/-- **Pushforward of a clopen binary split of a restricted domain.** A clopen partition
`A0' ⊔ A1' = univ` of `(F.restrict D).domain` (with `D ⊆ ↑F.domain` clopen) transports to a clopen
partition `A0 ⊔ A1 = D` of `D ⊆ ↑F.domain`, with the pieces `Equiv`-matching under
`restrict_restrict_equiv`. -/
lemma ScatFun.exists_pushforward_split (F : ScatFun) (D : Set ↑F.domain)
    (A0' A1' : Set ↑(F.restrict D).domain)
    (hDcl : IsClopen D) (h0 : IsClopen A0') (h1 : IsClopen A1')
    (hcov : A0' ∪ A1' = Set.univ) (hdj : Disjoint A0' A1') :
    ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧ Disjoint A0 A1 ∧
      A0 ∪ A1 = D ∧
      ScatFun.Equiv ((F.restrict D).restrict A0') (F.restrict A0) ∧
      ScatFun.Equiv ((F.restrict D).restrict A1') (F.restrict A1) ∧
      A1 ⊆ D ∧ {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A1} = A1' := by
  obtain ⟨A0, hA0cl, hA0sub, hA0eq⟩ := F.exists_pushforward_clopen D A0' hDcl h0
  obtain ⟨A1, hA1cl, hA1sub, hA1eq⟩ := F.exists_pushforward_clopen D A1' hDcl h1
  -- For `x ∈ D`, there is a domain point `w` of `F.restrict D` with `(restrictEquiv D w : ↑F.domain) = x`.
  have hsurj : ∀ x ∈ D, ∃ w : ↑(F.restrict D).domain, (F.restrictEquiv D w : ↑F.domain) = x := by
    intro x hx
    refine ⟨(F.restrictEquiv D).symm ⟨x, hx⟩, ?_⟩
    simp
  -- membership transfer: `x = restrictEquiv D w → (x ∈ A0 ↔ w ∈ A0')`, and same for `A1`.
  have hmem0 : ∀ w : ↑(F.restrict D).domain,
      ((F.restrictEquiv D w : ↑F.domain) ∈ A0 ↔ w ∈ A0') := fun w => by
    have := hA0eq; rw [Set.ext_iff] at this; simpa using this w
  have hmem1 : ∀ w : ↑(F.restrict D).domain,
      ((F.restrictEquiv D w : ↑F.domain) ∈ A1 ↔ w ∈ A1') := fun w => by
    have := hA1eq; rw [Set.ext_iff] at this; simpa using this w
  refine ⟨A0, A1, hA0cl, hA1cl, ?_, ?_, ?_, ?_, hA1sub, hA1eq⟩
  · rw [Set.disjoint_left]
    intro x hx0 hx1
    obtain ⟨w, rfl⟩ := hsurj x (hA0sub hx0)
    exact (Set.disjoint_left.mp hdj ((hmem0 w).mp hx0) ((hmem1 w).mp hx1))
  · apply Set.Subset.antisymm (Set.union_subset hA0sub hA1sub)
    intro x hx
    obtain ⟨w, rfl⟩ := hsurj x hx
    have : w ∈ A0' ∪ A1' := by rw [hcov]; exact Set.mem_univ w
    rcases this with hw | hw
    · exact Or.inl ((hmem0 w).mpr hw)
    · exact Or.inr ((hmem1 w).mpr hw)
  · rw [← hA0eq]; exact ScatFun.restrict_restrict_equiv F D A0 hA0sub
  · rw [← hA1eq]; exact ScatFun.restrict_restrict_equiv F D A1 hA1sub

/-- **Second case — Vertical-Theorem data for a single representative block**
(`6_double_successor_memo.tex:305-311`, the per-`g` slice of `secondCase_blockData`). For a
representative `g ∈ 𝒞_{α+2}` whose block `A_g = ⋃₀ 𝒫_{(g,y)}` is nonempty, produce all of the
Vertical-Theorem data attached to that one block, phrased over `F.domain`:

* the `pgl`-decomposition `Mg ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}` with `g ≡ pgl (Mg)`;
* the `𝒲`-finset `Hf ⊆ 𝒲_{α+1}`;
* a clopen split `A_g = A0 ⊔ A1` (as subsets of `F.domain`, so `A0 ∪ A1 = ⋃₀ 𝒫_{(g,y)}`) with
  `F↾A0 ≤ gl Hf`, `F↾A1 ≤ g`, `gl Hf ≤ g`;
* the corestriction bounds `g ≤ F⇂V` (`V ∋ y`) and, per clopen `U ∋ y`, a clopen `W ⊆ U` with
  `y ∉ W` and `gl Hf ≤ F⇂W`.

**Proof strategy (variable-rank Vertical Theorem, *no new theory*).** Contrary to the earlier
scaffold, the block does **not** need a from-scratch rank-`≤ α+2` Vertical Theorem: the existing
`verticalTheorem'` (`:848`) already covers it, re-instantiated at a *smaller base
ordinal* `β` sharing `α`'s limit part.

Let `ρ := CB(g)` be the block rank (all pieces of `A_g` are `≡ g`, so `CB(F↾A_g) = ρ` by
`cbRank_restrict_sUnion_const`). Because `λ+1 < ρ ≤ α+2 = λ+(m+2)` (`m = α.natPart`; lower bound is
the new hypothesis `hgrank`, upper is `F↾P ≤ F`), `ρ = λ + k` with `2 ≤ k ≤ m+2`, so `ρ` is a
genuine **double successor** `β+1+1` for `β := λ + (k-2)`, with `β.limitPart = λ` and `β ≤ α < ω₁`.
Then:

1. **Vertical Theorem at `β`.** `F↾A_g` is pseudo-centered at `λ = β.limitPart`
   (`block_isPseudoCenteredAt`, using `hfine`), of rank `β+1+1`, and `FGBelow (β+1+1)` follows from
   `FGBelow (α+1+1)` by `ScatFun.FGBelow.mono` (since `β+1+1 = ρ ≤ α+1+1`). So
   `verticalTheorem'_withRep β … ` applies verbatim, yielding the split/reductions/`𝒲`-finset `H`
   for the *induced* partition, **plus** the piece-equivalences identifying its representative `g'`.
2. **Level upgrade `β → α`** (pure monotonicity, no new theory): `Mg ⊆ 𝒞_{β+1} ∪ ω𝒞_{β+1} ⊆
   𝒞_{α+1} ∪ ω𝒞_{α+1}` and `H ⊆ 𝒲_{β+1} ⊆ 𝒲_{α+1}` via `Centered_add_nat_subset_succ` /
   `Generators_mono_of_le` (same `λ`, larger natural part).
3. **Representative identification `g' ≡ g`** — now routine: the block's induced pieces are
   `≡ g` (block membership) and `≡ g'` (the exposed conjunct of `verticalTheorem'_withRep`), so
   `g' ≡ g` by symmetry+transitivity. The `pgl`-decomposition `g ≡ pgl (Mg)` comes directly from
   `exists_pglFinset_decomp_of_centered_doubleSucc` **applied to `g` at base `β`** (rank `= β+1+1`).
4. **Transport** `A0'/A1' ⊆ (F↾A_g).domain ↦ A0/A1 ⊆ F.domain` via `ScatFun.restrict_restrict_equiv`
   (turning `A0'∪A1' = univ` into `A0∪A1 = ⋃₀ 𝒫_{(g,y)}`), and `(F↾A_g)⇂V ≤ F⇂V` (a
   sub-corestriction reduces into the corestriction).

Leaves ①(limitPart squeeze), ②(generator-level upgrade β→α), ③(rep-id `g'≡g`) and ④(domain
transport) are all **proved**, as is the `verticalTheorem'_withRep` packaging body. The
mathematically substantive step (1) is fully wired to the existing theorem.

**New hypothesis `hgrank`.** `λ+1 < CB(g)` is required to make `ρ` a *double* successor (it excludes
`ρ = λ+1`, a successor of the limit `λ`, which `verticalTheorem'` cannot treat). It is supplied for
free at the sole call site (`secondCase_blockData`), where `g` ranges over the representatives
`M` of `diagonalTheorem_secondCase_representatives_M`, each realized by a piece of rank `> λ+1`. -/
theorem secondCase_singleBlockData
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hfine : hA.IsFine α.limitPart)
    (g : ScatFun)
    (hgrank : α.limitPart + 1 < CBRank g.func)
    (hne : (hA.blockPieces g y).Nonempty) :
    ∃ (Mg Hf : Finset ScatFun) (A0 A1 : Set ↑F.domain),
      Mg ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)) ∧
      ScatFun.Equiv g (ScatFun.pglFinset Mg) ∧
      Hf ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) ∧
      IsClopen A0 ∧ IsClopen A1 ∧ Disjoint A0 A1 ∧
      A0 ∪ A1 = ⋃₀ hA.blockPieces g y ∧
      ScatFun.Reduces (F.restrict A0) (ScatFun.glList Hf.toList) ∧
      ScatFun.Reduces (F.restrict A1) g ∧
      ScatFun.Reduces g (F.restrict A1) ∧
      (∀ (h : IsCentered (F.restrict A1).func), cocenter (F.restrict A1).func h = y) ∧
      ScatFun.Reduces (ScatFun.glList Hf.toList) g ∧
      (∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V)) ∧
      (∀ U : Set Baire, IsClopen U → y ∈ U →
        ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
          ScatFun.Reduces (ScatFun.glList Hf.toList) (F.coRestrict W)) := by
  classical
  set lam := α.limitPart with hlam
  set m := α.natPart with hm
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  -- ── (a) A witnessing piece pins the block rank ρ := CB(g). ──────────────────────
  obtain ⟨P₀, hP₀mem, hP₀eq, hP₀coc⟩ := hne
  have hblock_ne : (hA.blockPieces g y).Nonempty := ⟨P₀, hP₀mem, hP₀eq, hP₀coc⟩
  have hgcent : IsCentered g.func :=
    isCentered_of_equiv (hA.centered P₀ hP₀mem) hP₀eq.symm
  -- upper bound  ρ ≤ α+2   (the piece reduces into `F`, `hFrank`)
  have hub : CBRank g.func ≤ α + 1 + 1 := by
    rw [← cbRank_eq_of_equiv hP₀eq, ← hFrank]
    have h1 : (F.restrict P₀).Reduces (F.restrict Set.univ) :=
      restrict_reduces_of_subset F (Set.subset_univ P₀)
    refine (ContinuouslyReduces.rank_monotone (F.restrict P₀).hScat
      (F.restrict Set.univ).hScat h1).trans (le_of_eq ?_)
    rw [cbRank_restrict_eq]; exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
  -- ── (b) Extract β with β+1+1 = ρ, β.limitPart = λ, β ≤ α. ────────────────────────
  have add_two : ∀ x : Ordinal.{0}, x + 1 + 1 = x + 2 := fun x => by rw [add_assoc]; norm_num
  have hαsucc : α + 1 + 1 = lam + ((m : Ordinal) + 2) := by
    rw [hlam, hm]; conv_lhs => rw [Ordinal.eq_limitPart_add_natPart α]
    rw [add_two, add_assoc]
  -- `ρ`'s limit part is `λ`: since `λ ≤ ρ ≤ λ+(m+2)`, the difference `ρ - λ` is finite
  -- (`< ω`), so `ρ = λ + ↑n` and `limitPart_add_natCast` closes it — no separate monotone helper.
  have hρlim : (CBRank g.func).limitPart = lam := by
    have hle : lam ≤ CBRank g.func := le_of_lt (lt_of_le_of_lt le_self_add hgrank)
    have hsub_le : CBRank g.func - lam ≤ ((m + 2 : ℕ) : Ordinal) := by
      rw [Ordinal.sub_le]
      refine hub.trans (le_of_eq ?_)
      rw [hαsucc]; norm_cast
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CBRank g.func - lam = (n : Ordinal) :=
      Ordinal.lt_omega0.mp (lt_of_le_of_lt hsub_le (Ordinal.nat_lt_omega0 (m + 2)))
    have hρeq : CBRank g.func = lam + (n : Ordinal) := by
      rw [← hn, Ordinal.add_sub_cancel_of_le hle]
    rw [hρeq]; exact Ordinal.limitPart_add_natCast lam n hlim
  have hρk : CBRank g.func = lam + (((CBRank g.func).natPart : ℕ) : Ordinal) := by
    conv_lhs => rw [Ordinal.eq_limitPart_add_natPart (CBRank g.func)]
    rw [hρlim]
  set r := (CBRank g.func).natPart with hr
  have hr2 : 2 ≤ r := by
    have hlt : lam + 1 < lam + (r : Ordinal) := hρk ▸ hgrank
    have h1 : (1 : Ordinal) < (r : Ordinal) := lt_of_add_lt_add_left hlt
    exact_mod_cast h1
  have hrm : r ≤ m + 2 := by
    have hle : lam + (r : Ordinal) ≤ lam + ((m : Ordinal) + 2) := by rw [← hρk, ← hαsucc]; exact hub
    have h1 : (r : Ordinal) ≤ (m : Ordinal) + 2 := le_of_add_le_add_left hle
    exact_mod_cast h1
  obtain ⟨j, hj⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  set β : Ordinal.{0} := lam + (j : Ordinal) with hβ
  have hβsucc : β + 1 + 1 = CBRank g.func := by
    rw [hβ, hρk, hj, add_two, add_assoc]; push_cast; ring_nf
  have hβlim : β.limitPart = lam := by rw [hβ]; exact Ordinal.limitPart_add_natCast lam _ hlim
  have hβα : β ≤ α := by
    rw [hβ]; conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    gcongr; exact_mod_cast (by omega : j ≤ m)
  have hβω : β < omega1 := lt_of_le_of_lt hβα hα
  have hFGβ : ScatFun.FGBelow (β + 1 + 1) := hFG.mono (by rw [hβsucc]; exact hub)
  -- ── (c) The block is pseudo-centered at λ = β.limitPart, of rank β+1+1. ──────────
  set PartB : Set (Set ↑(hA.piece g y).domain) :=
    (fun P => {w : ↑(hA.piece g y).domain |
      (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ P}) '' (hA.blockPieces g y)
    with hPartBdef
  have hB : (hA.piece g y).IsCPartition PartB := block_induced_isCPartition hA g y
  have hpcB : hB.IsPseudoCenteredAt lam y := block_induced_isPseudoCenteredAt hA hfine g y hblock_ne
  have hErank : CBRank (hA.piece g y).func = β + 1 + 1 := by
    rw [hβsucc]
    show CBRank (F.restrict (⋃₀ hA.blockPieces g y)).func = CBRank g.func
    refine cbRank_restrict_sUnion_const
      (hA.countable.mono (fun P hP => hP.choose))
      (fun P hP => hA.isClopen P hP.choose)
      hblock_ne
      (fun P hP => ?_)
    rw [cbRank_eq_of_equiv hP.choose_spec.1]
  have hpcB' : hB.IsPseudoCenteredAt β.limitPart y := by rw [hβlim]; exact hpcB
  -- ── (d) Apply the representative-exposing Vertical Theorem at base β. ────────────
  obtain ⟨g', hg'C, H, hHsub, A0', A1', hA0'cl, hA1'cl, hcover', hdisj',
          hA0'red, hA1'red, hHg', hcoreg', hW', hg'rep, hg'A1, hcoc'⟩ :=
    verticalTheorem'_withRep β hβω hFGβ (hA.piece g y) hErank hB y hpcB'
  -- ── (e) Independent pgl-decomposition of the *given* g (no g′ needed). ───────────
  obtain ⟨Mg, hMgne, hMgsub, hgMg⟩ :=
    ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc β hβω hFGβ g hβsucc.symm hgcent
  -- ── (f) Level upgrade β → α for the two generator finsets (same limit part λ, larger natural
  -- part; `Centered_add_nat_subset_succ` chained, then `Finset.image_subset_image` for the ω-image
  -- and proof-irrelevant `maxFun` for the `𝒲`-insert). ─────────────────────────────
  have hCmono : ∀ {a b : ℕ}, a ≤ b →
      ScatFun.Centered (lam + (a : Ordinal)) ⊆ ScatFun.Centered (lam + (b : Ordinal)) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih =>
      refine ih.trans ?_
      rw [show lam + ((n + 1 : ℕ) : Ordinal) = lam + (n : Ordinal) + 1 by push_cast; rw [add_assoc]]
      exact ScatFun.Centered_add_nat_subset_succ hlim n
  have hβ1 : β + 1 = lam + ((j + 1 : ℕ) : Ordinal) := by rw [hβ]; push_cast; rw [add_assoc]
  have hα1 : α + 1 = lam + ((m + 1 : ℕ) : Ordinal) := by
    conv_lhs => rw [Ordinal.eq_limitPart_add_natPart α]
    push_cast; rw [add_assoc]
  have hCsub1 : ScatFun.Centered (β + 1) ⊆ ScatFun.Centered (α + 1) := by
    rw [hβ1, hα1]; exact hCmono (by omega)
  have hlpβ : (β + 1).limitPart = lam := by rw [hβ1]; exact Ordinal.limitPart_add_natCast lam _ hlim
  have hlpα : (α + 1).limitPart = lam := by rw [hα1]; exact Ordinal.limitPart_add_natCast lam _ hlim
  have hMgup : Mg ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1)) :=
    hMgsub.trans (Finset.union_subset_union hCsub1 (Finset.image_subset_image hCsub1))
  have hHup : H ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1) := by
    refine hHsub.trans (fun x hx => ?_)
    rw [omegaRegularSet, Finset.mem_insert] at hx
    rw [omegaRegularSet, Finset.mem_insert]
    rcases hx with hxmax | hximg
    · refine Or.inl ?_
      rw [hxmax]
      have hmax : ∀ (p1 : (β + 1).limitPart < omega1) (p2 : (α + 1).limitPart < omega1),
          ScatFun.maxFun (β + 1).limitPart p1 = ScatFun.maxFun (α + 1).limitPart p2 := by
        rw [hlpβ, hlpα]; intro p1 p2; rfl
      exact hmax _ _
    · refine Or.inr ?_
      rw [Finset.mem_image] at hximg ⊢
      obtain ⟨h, hhC, rfl⟩ := hximg
      exact ⟨h, hCsub1 hhC, rfl⟩
  -- ── (g) Representative identification g′ ≡ g. ────────────────────────────────────
  -- The induced pieces of the block are `≡ (F.restrict P) ≡ g` (block membership) and, by the
  -- exposed conjunct `hg'rep`, also `≡ g'`; hence `g' ≡ g`.  Routine, unblocked by
  -- `verticalTheorem'_withRep`.
  have hP₀block : P₀ ∈ hA.blockPieces g y := ⟨hP₀mem, hP₀eq, hP₀coc⟩
  have hPind_mem :
      {w : ↑(hA.piece g y).domain |
          (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ P₀} ∈ PartB :=
    ⟨P₀, hP₀block, rfl⟩
  have hg'g : ScatFun.Equiv g' g :=
    (hg'rep _ hPind_mem).symm.trans
      ((ScatFun.restrict_restrict_equiv F (⋃₀ hA.blockPieces g y) P₀
          (Set.subset_sUnion_of_mem hP₀block)).trans hP₀eq)
  -- ── (h) Transport the split A0'/A1' ⊆ (block).domain back to F.domain, and package. ─
  -- LEAF ④: the pure restrict-of-restrict transport (mirrors `block_induced_isCPartition`),
  -- combined with (g) to rephrase every reduction against `g` instead of `g'`, and with the
  -- sub-corestriction bound `(F.restrict A_g)⇂V ≤ F⇂V`.  All A0/A1-dependent clauses are
  -- produced together here so the final `refine` is a pure repackaging.
  obtain ⟨A0, A1, hA0cl, hA1cl, hdisj, hcover, hA0red, hA1red, hgA1new, hcocA1, hHg, hcoreg, hW⟩ :
      ∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧ Disjoint A0 A1 ∧
        A0 ∪ A1 = ⋃₀ hA.blockPieces g y ∧
        ScatFun.Reduces (F.restrict A0) (ScatFun.glList H.toList) ∧
        ScatFun.Reduces (F.restrict A1) g ∧
        ScatFun.Reduces g (F.restrict A1) ∧
        (∀ (h : IsCentered (F.restrict A1).func), cocenter (F.restrict A1).func h = y) ∧
        ScatFun.Reduces (ScatFun.glList H.toList) g ∧
        (∀ V : Set Baire, IsClopen V → y ∈ V → ScatFun.Reduces g (F.coRestrict V)) ∧
        (∀ U : Set Baire, IsClopen U → y ∈ U →
          ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
            ScatFun.Reduces (ScatFun.glList H.toList) (F.coRestrict W)) := by
    obtain ⟨A0, A1, hA0cl, hA1cl, hdisj, hcover, hEqA0, hEqA1, hA1subD, hA1eqSet⟩ :=
      F.exists_pushforward_split (⋃₀ hA.blockPieces g y) A0' A1'
        (blockPieces_sUnion_isClopen hA g y) hA0'cl hA1'cl hcover' hdisj'
    -- **Cocenter transport** `cocenter(F↾A1) = cocenter(block↾A1') = y` (`cocenter_restrict_restrict_eq`,
    -- using the pullback set-equality `A1' = {w | (restrictEquiv D w).val ∈ A1}`).
    have hcocA1 : ∀ (h : IsCentered (F.restrict A1).func), cocenter (F.restrict A1).func h = y := by
      intro h
      have hcoc'2 : ∀ (h' : IsCentered ((F.restrict (⋃₀ hA.blockPieces g y)).restrict
          {w | (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ A1}).func),
          cocenter ((F.restrict (⋃₀ hA.blockPieces g y)).restrict
            {w | (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ A1}).func h' = y := by
        rw [hA1eqSet]; exact hcoc'
      have hc1 : IsCentered ((F.restrict (⋃₀ hA.blockPieces g y)).restrict
          {w | (F.restrictEquiv (⋃₀ hA.blockPieces g y) w : ↑F.domain) ∈ A1}).func := by
        rw [hA1eqSet]; exact isCentered_of_equiv h hEqA1
      rw [← ScatFun.cocenter_restrict_restrict_eq F (⋃₀ hA.blockPieces g y) A1 hA1subD hc1 h]
      exact hcoc'2 hc1
    refine ⟨A0, A1, hA0cl, hA1cl, hdisj, hcover,
      (hEqA0.symm.1).trans hA0'red,
      ((hEqA1.symm.1).trans hA1'red).trans hg'g.1,
      (hg'g.2.trans hg'A1).trans hEqA1.1,
      hcocA1,
      hHg'.trans hg'g.1,
      fun V hVcl hyV =>
        (hg'g.symm.1.trans (hcoreg' V hVcl hyV)).trans
          (ScatFun.coRestrict_restrict_reduces F (⋃₀ hA.blockPieces g y) V),
      fun U hUcl hyU => ?_⟩
    obtain ⟨W, hWU, hWcl, hyW, hWred⟩ := hW' U hUcl hyU
    exact ⟨W, hWU, hWcl, hyW,
      hWred.trans (ScatFun.coRestrict_restrict_reduces F (⋃₀ hA.blockPieces g y) W)⟩
  exact ⟨Mg, H, A0, A1, hMgup, hgMg, hHup, hA0cl, hA1cl, hdisj, hcover,
    hA0red, hA1red, hgA1new, hcocA1, hHg, hcoreg, hW⟩

/-- **Second case — per-block Vertical-Theorem data** (`6_double_successor_memo.tex:305-311`).
Enumerate the finite representatives `M ⊆ 𝒞_{α+2}` of `𝒫'_M` (pieces of cocenter `y` and rank
`> λ+1`) as `gM : Fin n → ScatFun`. For each `i`, the block `A_{gᵢ} = ⋃₀ 𝒫_{(gᵢ,y)}` is
pseudo-centered (`block_isPseudoCenteredAt`), so the Vertical Theorem (`verticalTheorem'`,
transported to `F.domain`) yields:

* the pgl-decomposition `Mg i ⊆ 𝒞_{α+1} ∪ ω{𝒞_{α+1}}` with `gᵢ ≡ pgl (Mg i)`
  (`exists_pglFinset_decomp_of_centered_doubleSucc`);
* the `𝒲`-finset `Hf i ⊆ 𝒲_{α+1}`;
* the clopen split `A_{gᵢ} = A⁰ᵢ ⊔ A¹ᵢ` with `F↾A⁰ᵢ ≤ gl Hᵢ`, `F↾A¹ᵢ ≤ gᵢ`, `gl Hᵢ ≤ gᵢ`;
* the corestriction bounds `gᵢ ≤ F⇂V` (`V ∋ y`) and, per clopen `U ∋ y`, a clopen `Wᵢ ⊆ U`
  with `y ∉ Wᵢ` and `gl Hᵢ ≤ F⇂Wᵢ`.

`hMcov` records that every `𝒫'_M` piece is `Equiv` to some `gᵢ`. This is the foundation that
`diagonalTheorem_secondCase_construction` consumes; its proof (per-block application of
`verticalTheorem'` to `block_isPseudoCenteredAt`, plus the restrict-of-restrict transport of the
splits/reductions back to `F.domain`) is now complete. -/
theorem secondCase_blockData
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y) :
    ∃ (n : ℕ) (gM : Fin n → ScatFun) (Mg : Fin n → Finset ScatFun)
      (Hf : Fin n → Finset ScatFun) (A0 A1 : Fin n → Set ↑F.domain),
      (∀ i, gM i ∈ ScatFun.Centered (α + 1 + 1)) ∧
      (∀ i, Mg i ⊆ ScatFun.Centered (α + 1) ∪ ScatFun.omegaImage (ScatFun.Centered (α + 1))) ∧
      (∀ i, ScatFun.Equiv (gM i) (ScatFun.pglFinset (Mg i))) ∧
      (∀ i, Hf i ⊆ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1)) ∧
      (∀ i, IsClopen (A0 i)) ∧ (∀ i, IsClopen (A1 i)) ∧
      (∀ i, Disjoint (A0 i) (A1 i)) ∧
      (∀ i, A0 i ∪ A1 i = ⋃₀ hA.blockPieces (gM i) y) ∧
      (∀ i, ScatFun.Reduces (F.restrict (A0 i)) (ScatFun.glList (Hf i).toList)) ∧
      (∀ i, ScatFun.Reduces (F.restrict (A1 i)) (gM i)) ∧
      (∀ i, ScatFun.Reduces (gM i) (F.restrict (A1 i))) ∧
      (∀ i, ∀ (h : IsCentered (F.restrict (A1 i)).func),
        cocenter (F.restrict (A1 i)).func h = y) ∧
      (∀ i, ScatFun.Reduces (ScatFun.glList (Hf i).toList) (gM i)) ∧
      (∀ (i : Fin n) (V : Set Baire), IsClopen V → y ∈ V →
        ScatFun.Reduces (gM i) (F.coRestrict V)) ∧
      (∀ (i : Fin n) (U : Set Baire), IsClopen U → y ∈ U →
        ∃ W : Set Baire, W ⊆ U ∧ IsClopen W ∧ y ∉ W ∧
          ScatFun.Reduces (ScatFun.glList (Hf i).toList) (F.coRestrict W)) ∧
      (∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
        α.limitPart + 1 < CBRank (F.restrict P).func →
          ∃ i, ScatFun.Equiv (F.restrict P) (gM i)) ∧
      -- **Realized (onto) direction**: every representative `gM i` is `≡` to some cocenter-`y`
      -- piece.  The `rep→piece` companion of the cover clause, consumed by the Disjointification
      -- vertical clause (`secondCase_wedge_vertical_clause`, which needs a per-column anchor).
      (∀ i, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (gM i)) := by
  classical
  -- Finite representatives `M ⊆ 𝒞_{α+2}` of `𝒫'_M` (cocenter `y`, rank `> λ+1`).
  obtain ⟨M, hMsub, hMcov, hMrep⟩ :=
    diagonalTheorem_secondCase_representatives_M α hα hFG F hFrank hA (y := y)
  -- Enumerate `M` as a `Fin M.card`-indexed family `gM`.
  set e : Fin M.card ≃ {x // x ∈ M} := M.equivFin.symm with he_def
  set gM : Fin M.card → ScatFun := fun i => ↑(e i) with hgM_def
  have hgM_mem : ∀ i, gM i ∈ M := fun i => (e i).2
  -- Each block `A_{gᵢ}` is nonempty: the representative-cover clause `hMrep` supplies a piece.
  have hne : ∀ i, (hA.blockPieces (gM i) y).Nonempty := by
    intro i
    obtain ⟨P, hP, hPy, _, hPeq⟩ := hMrep (gM i) (hgM_mem i)
    exact ⟨P, hP, hPeq, hPy⟩
  -- Each representative has rank `> λ+1` (its realizing piece does, `hMrep`), the double-successor
  -- hypothesis `secondCase_singleBlockData` needs to run the Vertical Theorem at variable rank.
  have hgrank : ∀ i, α.limitPart + 1 < CBRank (gM i).func := by
    intro i
    obtain ⟨P, hP, hPy, hPrank, hPeq⟩ := hMrep (gM i) (hgM_mem i)
    rwa [cbRank_eq_of_equiv hPeq] at hPrank
  -- Per-block Vertical-Theorem data, chosen uniformly in `i`.
  choose! Mg Hf A0 A1 hdata using
    (fun i : Fin M.card => secondCase_singleBlockData α hα hFG F hFrank hA hss.1 (gM i)
      (hgrank i) (hne i))
  refine ⟨M.card, gM, Mg, Hf, A0, A1,
    fun i => hMsub (hgM_mem i),
    fun i => (hdata i).1,
    fun i => (hdata i).2.1,
    fun i => (hdata i).2.2.1,
    fun i => (hdata i).2.2.2.1,
    fun i => (hdata i).2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun i => (hdata i).2.2.2.2.2.2.2.2.2.2.2.2.2,
    ?_,
    -- Realized (onto) clause: `hMrep` supplies a cocenter-`y` piece for each representative `gM i`.
    fun i => by
      obtain ⟨P, hP, hPy, _, hPeq⟩ := hMrep (gM i) (hgM_mem i)
      exact ⟨P, hP, hPy, hPeq⟩⟩
  -- Cover clause: a rank-`> λ+1` piece of cocenter `y` matches some representative `gM i`.
  intro P hP hPy hPrank
  obtain ⟨g, hgM, hgeq⟩ := hMcov P hP hPy hPrank
  refine ⟨e.symm ⟨g, hgM⟩, ?_⟩
  have hg_eq : gM (e.symm ⟨g, hgM⟩) = g := by simp [hgM_def]
  rw [hg_eq]; exact hgeq


end
