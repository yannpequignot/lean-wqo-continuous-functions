import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.Shared

/-!
# §4.3 — Theorem 4.12, λ = 1 base case (Case B diagonal)

Extracted from `SimpleSuccessorOfLimit.lean`.  The `λ=1` diagonal mirrors the limit case
with the restriction-closed block class "the ray has finite image".
-/

open scoped Topology ScatFun
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section


/-! ### `λ = 1` base case (helper lemmas)

The `λ = 1` Case-B diagonal mirrors the non-zero-limit case, but the ray class
"`CBRank < λ`" (empty at `λ = 1`) is replaced by the restriction-closed class
"the ray has *finite image*".  A centered block of rank `2` is `≡ k₂` (= `pgl` of
copies of the single point `k₁ = minFun 0`), whose rays each `≡ k₁` and so have finite
image; and a pointed gluing of finite-image functions reduces to `k₂` by finite
generation (`finitegenerationAndPgluing_upper` with `B = ![k₁]`, then
`pgl_const_minFun_zero_equiv_minFun_one`). -/

/-
A reduction cannot enlarge the image: if `F ≤ G` and `G` has finite image then so
does `F` (`F.func x = τ (G.func (σ x))` so `range F.func ⊆ τ '' range G.func`).
-/
lemma reduces_finite_range (F G : ScatFun) (hFG : ScatFun.Reduces F G)
    (hfin : (Set.range G.func).Finite) : (Set.range F.func).Finite := by
  obtain ⟨ σ, hσ, τ, hτ, h_eq ⟩ := hFG;
  exact Set.Finite.subset ( hfin.image _ ) ( Set.range_subset_iff.mpr fun x => by aesop )


/-
The copies-sequence of `N` copies of the single generator `k₁ = minFun 0` agrees with
the copies-sequence of `genLeOne` with multiplicities `![N, 0]` (the `ℓ₁` block unused).
Both `copiesList`s equal `List.replicate N (minFun 0)`.
-/
lemma lamOne_copiesSeq_eq (N : ℕ) :
    ScatFun.copiesSeq ![ScatFun.minFun 0 zero_lt_omega1] ![N]
      = ScatFun.copiesSeq genLeOne ![N, 0] := by
  rfl


/-- `Gl ![k₁] ![N] = Gl genLeOne ![N, 0]`, since their copies-sequences agree. -/
lemma lamOne_Gl_single_eq (N : ℕ) :
    ScatFun.Gl ![ScatFun.minFun 0 zero_lt_omega1] ![N] = ScatFun.Gl genLeOne ![N, 0] := by
  unfold ScatFun.Gl
  rw [lamOne_copiesSeq_eq]


/-- **Finite image ⟹ single-generator finite gluing.**  A scattered continuous function
with finite image is `≡` a finite gluing of copies of the single point `k₁ = minFun 0`,
i.e. lies in `FinGl ![k₁]`.  (Same construction as `finite_image_mem_finGl`, but the
multiplicity of `ℓ₁` is `0`, so `Gl genLeOne ![N,0] = Gl ![k₁] ![N]`.) -/
lemma lamOne_finImage_mem_finGl_single (F : ScatFun) (hfin : (Set.range F.func).Finite) :
    F ∈ ScatFun.FinGl ![ScatFun.minFun 0 zero_lt_omega1] := by
  classical
  have : Finite ↑(Set.range F.func) := hfin
  set N := Nat.card ↑(Set.range F.func) with hN
  let e : ↑(Set.range F.func) ≃ Fin N := Finite.equivFin _
  let idxF : ↑F.domain → Fin N := fun x => e ⟨F.func x, Set.mem_range_self x⟩
  let valF : Fin N → Baire := fun k => (e.symm k).val
  have hsec : ∀ x, valF (idxF x) = F.func x := by
    intro x; simp only [valF, idxF, Equiv.symm_apply_apply]
  have hvalinj : Function.Injective valF := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hidx : Continuous idxF :=
    continuous_of_discreteTopology.comp (F.hCont.subtype_mk _)
  have hsurj : Function.Surjective idxF := by
    intro k
    obtain ⟨v, hv⟩ := (e.symm k).2
    refine ⟨v, ?_⟩
    show e ⟨F.func v, Set.mem_range_self v⟩ = k
    rw [show (⟨F.func v, Set.mem_range_self v⟩ : ↑(Set.range F.func)) = e.symm k from
      Subtype.ext hv, e.apply_symm_apply]
  let rep : Fin N → ↑F.domain := fun k => (hsurj k).choose
  have hrep : ∀ k, F.func (rep k) = valF k := by
    intro k
    have h1 : idxF (rep k) = k := (hsurj k).choose_spec
    rw [← hsec (rep k), h1]
  refine ⟨![N], ?_, ?_⟩ <;> rw [lamOne_Gl_single_eq N]
  · exact glCopies_reduces_of_enum F N valF hvalinj rep hrep
  · exact reduces_glCopies_of_enum F N idxF hidx valF hsec


/-
**Finite-image collapse.**  If every ray of `h` at `y` has finite image, then `h`
reduces to `k₂ = minFun 1`.  (`h ≤ pgl (rays)` by `reduces_pgl_rays`; each ray lies in
`FinGl ![k₁]`, so `pgl (rays) ≤ pgl (repSeq ![k₁]) = pgl (const k₁) ≡ minFun 1` by
`finitegenerationAndPgluing_upper` and `pgl_const_minFun_zero_equiv_minFun_one`.)
-/
lemma lamOne_finImage_rays_reduces_minFun_one (h : ScatFun) (y : Baire)
    (hfin : ∀ j, (Set.range (h.rayOn y Set.univ j).func).Finite) :
    ScatFun.Reduces h (ScatFun.minFun 1 one_lt_omega1) := by
  revert hfin;
  intro hfin
  have h_pgl : ScatFun.Reduces h (ScatFun.pgl (fun i => (h.rayOn y Set.univ i))) := by
    convert ScatFun.reduces_pgl_rays h y using 1;
  refine h_pgl.trans ?_;
  have h_upper : ScatFun.Reduces (ScatFun.pgl (fun i => h.rayOn y Set.univ i)) (ScatFun.pgl (ScatFun.repSeq ![ScatFun.minFun 0 zero_lt_omega1])) := by
    apply ScatFun.finitegenerationAndPgluing_upper;
    exact fun i => ⟨ _, lamOne_finImage_mem_finGl_single _ ( hfin i ), ContinuouslyReduces.refl _ ⟩;
  have h_eq : ScatFun.repSeq ![ScatFun.minFun 0 zero_lt_omega1] = fun _ => ScatFun.minFun 0 zero_lt_omega1 := by
    ext; simp [ScatFun.repSeq];
  exact h_upper.trans ( by rw [ h_eq ] ; exact pgl_const_minFun_zero_equiv_minFun_one.1 )


/-
**Case A at `λ = 1`.**  If all rays of a simple rank-`2` function `g` (with
distinguished point `y`) have finite image, then `g ≡ k₂ = minFun 1`.
-/
lemma lamOne_caseA_equiv_minFun (g : ScatFun)
    (hg_rank : CBRank g.func = 1 + 1) (hg_simple : SimpleFun g.func)
    (y : Baire) (_hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (hfin : ∀ n, (Set.range (g.rayOn y Set.univ n).func).Finite) :
    ScatFun.Equiv g (ScatFun.minFun 1 one_lt_omega1) := by
  exact ⟨ lamOne_finImage_rays_reduces_minFun_one g y hfin, minFun_reduces_simple 1 one_lt_omega1 g hg_rank hg_simple ⟩


/-
The image of a single ray `g.rayOn y univ n` is `range g.func ∩ RaySet univ y n`; so the
image of the corestriction of `g` to a *finite* union of ray-sets is the corresponding finite
union of ray images, hence finite whenever each ray has finite image.
-/
lemma corestrict_finUnion_raysets_finImage (g : ScatFun) (y : Baire) (Jf : Finset ℕ)
    (hfin : ∀ n, (Set.range (g.rayOn y Set.univ n).func).Finite) :
    (Set.range (g.restrict
      {z : ↑g.domain | g.func z ∈ ⋃ n ∈ Jf, RaySet Set.univ y n}).func).Finite := by
  convert Set.Finite.biUnion Jf.finite_toSet fun n hn => hfin n using 1;
  ext; simp [ScatFun.restrict, ScatFun.rayOn];
  grind


/-- The `n`-th ray (in `RayFun` form) of `pgl s` at `zeroStream` continuously reduces to the
block `s n`.  This is exactly the `h_ray_reduces` step in the proof of `cbRank_rayFun_pgl`. -/
lemma RayFun_pgl_zeroStream_reduces_block (s : ℕ → ScatFun) (n : ℕ) :
    ContinuouslyReduces (RayFun (ScatFun.pgl s).func zeroStream n) (s n).func := by
  refine ⟨ ?_, ?_ ⟩;
  exact fun x => ⟨ stripZerosOne n x.val.val, by
    have := x.2.1; have := x.2.2; simp_all +decide [ ScatFun.pgl, PointedGluingFun ] ;
    split_ifs at this <;> simp_all +decide [ ScatFun.pglBlock ];
    have h_firstNonzero : firstNonzero x.val.val = n := by
      exact le_antisymm ( le_of_not_gt fun h => this <| by
        exact if_pos h ) ( le_of_not_gt fun h => by
        simp_all +decide [ prependZerosOne, zeroStream ];
        grind +splitImp )
    generalize_proofs at *; (
    grind) ⟩
  generalize_proofs at *; (
  refine ⟨ ?_, ?_ ⟩
  all_goals generalize_proofs at *;
  · exact Continuous.subtype_mk ( continuous_stripZerosOne n |> Continuous.comp <| continuous_subtype_val.comp continuous_subtype_val ) _;
  · refine ⟨ fun x => prependZerosOne n x, ?_, ?_ ⟩ <;> simp +decide [ RayFun ];
    · exact Continuous.continuousOn ( continuous_prependZerosOne n );
    · intro a ha hp hq
      have h_block : ∃ w : (s n).domain, a = prependZerosOne n w.val := by
        obtain ⟨ i, hi ⟩ := ha
        generalize_proofs at *; (
        simp_all +decide [ ScatFun.pgl_func_zeroStream ]);
        obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ‹_›
        generalize_proofs at *; (
        obtain ⟨ w, hw, rfl ⟩ := hi
        generalize_proofs at *; (
        have h_block : i = n := by
          have h_block : (ScatFun.pgl s).func ⟨prependZerosOne i w, by
            assumption⟩ = prependZerosOne i ((s i).func ⟨w, hw⟩) := by
            exact ScatFun.pgl_func_block s i ⟨ w, hw ⟩
          generalize_proofs at *; (
          by_cases hi : i < n <;> simp_all +decide [ prependZerosOne ];
          · specialize hp i hi ; simp_all +decide [ zeroStream ];
          · cases lt_or_eq_of_le hi <;> simp_all +decide [ zeroStream ])
        generalize_proofs at *; (
        exact ⟨ ⟨ w, by aesop ⟩, by aesop ⟩)))
      generalize_proofs at *; (
      obtain ⟨ w, rfl ⟩ := h_block; simp +decide [ ScatFun.pgl_func_block ] ;
      grind +suggestions))


/-
**Rays of a pointed gluing of finite-image blocks have finite image.**  The `i`-th ray
of `pgl s` at `zeroStream` reduces to the block `s i` (`cbRank_rayFun_pgl`'s explicit
reduction via `prependZerosOne`), so `reduces_finite_range` transports finiteness.
-/
lemma pgl_rayOn_zeroStream_finImage (s : ℕ → ScatFun)
    (hsfin : ∀ i, (Set.range (s i).func).Finite) (i : ℕ) :
    (Set.range ((ScatFun.pgl s).rayOn zeroStream Set.univ i).func).Finite := by
  obtain ⟨ σ, hσ, τ, hτ, h_eq ⟩ := RayFun_pgl_zeroStream_reduces_block s i;
  refine Set.Finite.subset ( Set.Finite.image ( fun x : Baire => τ x ) ( hsfin i ) ) ?_;
  intro x hx;
  simp_all +decide [ ScatFun.rayOn, ScatFun.restrict, RayFun ];
  rcases hx with ⟨ a, ha, hx, rfl ⟩ ; specialize h_eq a ha ; simp_all +decide [ RaySet ] ;
  exact ⟨ _, σ ⟨ ⟨ a, ha ⟩, by aesop ⟩ |>.2, rfl ⟩


/-
**Rays of a centered rank-`2` non-maximal block have finite image.**  Mirrors
`centered_lamPlusOne_rayOn_lt`: such a block is `≡ k₂ = pgl (const k₁)`; by
`rigidityOfCocenter_reducibleByPieces` each ray reduces to a finite gluing of rays of
`pgl (const k₁)` at `zeroStream`, each `≡ k₁` (`cbRank_rayFun_pgl`'s explicit reductions),
hence finite image; `reduces_finite_range` transports finiteness back.
-/
lemma centered_two_rayOn_finImage (F : ScatFun)
    (hF_rank : CBRank F.func = 1 + 1) (hF_cent : IsCentered F.func)
    (y : Baire) (hy : ∀ a ∈ CBLevel F.func 1, F.func a = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) F) :
    ∀ n, (Set.range (F.rayOn y Set.univ n).func).Finite := by
  -- Let `P := ScatFun.pgl (fun _ => ScatFun.minFun 0 zero_lt_omega1)`.
  set P : ScatFun := ScatFun.pgl (fun _ => ScatFun.minFun 0 zero_lt_omega1) with hP_def;
  obtain ⟨I, hI⟩ : ∃ I : ℕ → Finset ℕ, ∀ n, ContinuouslyReduces (RayFun F.func y n) (P.func ∘ (Subtype.val : ↥{a : ↑P.domain | P.func a ∈ ⋃ i ∈ I n, RaySet Set.univ zeroStream i} → ↑P.domain)) := by
    have h_equiv : ScatFun.Equiv F P := by
      have h_equiv : ScatFun.Equiv F (ScatFun.minFun 1 one_lt_omega1) := by
        have h_equiv : ScatFun.Equiv F (ScatFun.minFun 1 one_lt_omega1) ∨ ScatFun.Equiv F (ScatFun.succMaxFun 1 one_lt_omega1) := by
          apply centeredSuccessor 1 one_lt_omega1 (Or.inl rfl) F hF_rank hF_cent;
        cases h_equiv <;> simp_all +decide [ ScatFun.Equiv ]
      generalize_proofs at *;
      have h_equiv_P : ScatFun.Equiv (ScatFun.minFun 1 one_lt_omega1) P := by
        convert pgl_const_minFun_zero_equiv_minFun_one.symm using 1;
      exact ⟨ h_equiv.1.trans h_equiv_P.1, h_equiv_P.2.trans h_equiv.2 ⟩
    generalize_proofs at *;
    have h_cocenter : cocenter F.func hF_cent = y ∧ cocenter P.func (by
    apply pgl_isCentered_of_regular;
    exact scatFun_const_isRegularSeq _) = zeroStream := by
      exact ⟨ cocenter_eq_distinguished F hF_cent 1 hF_rank y hy, cocenter_pgl_eq_zeroStream _ ( scatFun_const_isRegularSeq _ ) ( fun _ _ => rfl ) _ ⟩
    generalize_proofs at *;
    obtain ⟨I, hI⟩ := rigidityOfCocenter_reducibleByPieces F P hF_cent ‹_› ⟨h_equiv.1, h_equiv.2⟩
    generalize_proofs at *;
    use I
    intro n
    generalize_proofs at *;
    exact (by
    convert hI.2 n using 1;
    all_goals congr! 1;
    all_goals norm_num [ RayFun, RaySet, h_cocenter ];
    · exact Set.ext fun x => ⟨ fun ⟨ i, hi₁, hi₂, hi₃ ⟩ => ⟨ i, hi₂, hi₁, hi₃ ⟩, fun ⟨ i, hi₂, hi₁, hi₃ ⟩ => ⟨ i, hi₁, hi₂, hi₃ ⟩ ⟩;
    · grind;
    · congr! 1;
      congr! 1;
      ext; simp [h_cocenter];
    · congr! 1;
      congr! 1;
      ext; simp [RaySet, h_cocenter];
      exact ⟨ fun ⟨ i, hi₁, hi₂, hi₃ ⟩ => ⟨ i, hi₂, hi₁, hi₃ ⟩, fun ⟨ i, hi₂, hi₁, hi₃ ⟩ => ⟨ i, hi₁, hi₂, hi₃ ⟩ ⟩)
  generalize_proofs at *;
  intro n
  have h_range_finite : (Set.range (P.func ∘ (Subtype.val : ↥{a : ↑P.domain | P.func a ∈ ⋃ i ∈ I n, RaySet Set.univ zeroStream i} → ↑P.domain))).Finite := by
    convert corestrict_finUnion_raysets_finImage P zeroStream ( I n ) _ using 1;
    · ext; simp [ScatFun.restrict];
    · convert pgl_rayOn_zeroStream_finImage ( fun _ => ScatFun.minFun 0 zero_lt_omega1 ) ( fun _ => ?_ ) using 1;
      simp +decide only [ScatFun.minFun_func, MinFun, MinDom, Subtype.range_coe_subtype, Ordinal.limitRecOn_zero, setOf_mem_eq];
      simp +decide [ PointedGluingSet ]
  generalize_proofs at *;
  have h_range_finite : (Set.range (RayFun F.func y n)).Finite := by
    obtain ⟨ g, hg ⟩ := hI n;
    obtain ⟨ τ, hτ₁, hτ₂ ⟩ := hg.2
    generalize_proofs at *;
    have h_range_finite : (Set.range (τ ∘ (P.func ∘ Subtype.val) ∘ g)).Finite := by
      exact Set.Finite.subset ( h_range_finite.image τ ) ( Set.range_subset_iff.mpr fun x => Set.mem_image_of_mem _ <| Set.mem_range_self _ )
    generalize_proofs at *;
    convert h_range_finite using 1
    generalize_proofs at *;
    exact Set.ext fun x => ⟨ fun hx => by obtain ⟨ y, rfl ⟩ := hx; exact ⟨ y, hτ₂ y ▸ rfl ⟩, fun hx => by obtain ⟨ y, rfl ⟩ := hx; exact ⟨ y, hτ₂ y ▸ rfl ⟩ ⟩
  generalize_proofs at *;
  convert h_range_finite using 1;
  ext; simp [ScatFun.rayOn, RayFun];
  simp +decide only [RaySet, ne_eq, mem_setOf_eq, ScatFun.restrict, coe_setOf, comp_apply, mem_univ, true_and];
  constructor <;> rintro ⟨ a, ha ⟩ <;> use a <;> aesop ( simp_config := { singlePass := true } ) ;


/-
The identity `id_ℕ` is **not** centered: a center `x` would, via the clopen singleton
`{x}`, force `id` to reduce to a constant, contradicting injectivity of `id`.
-/
lemma not_isCentered_id : ¬ IsCentered (@id ℕ) := by
  rintro ⟨ x, hx ⟩;
  obtain ⟨ σ, hσ, τ, hτ, h_eq ⟩ := hx { x } ( isOpen_discrete _ ) rfl;
  -- Since every element of the singleton set {x} is equal to x, we have (σ k).val = x for all k.
  have h_sigma_val : ∀ k, (σ k).val = x := by
    exact fun k => ( σ k ) |>.2;
  norm_num [ h_sigma_val ] at h_eq;
  linarith [ h_eq 0, h_eq 1 ]


/-
**Local membership in the finite-image-ray class (`λ = 1`).**  Mirrors
`caseB_local_in_class`.
-/
lemma lamOne_caseB_block_rayOn_finImage (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) g)
    (C : Set ↑g.domain) (hC : IsOpen C)
    (hcent : IsCentered (g.func ∘ (Subtype.val : ↥C → ↑g.domain))) :
    ∀ j, (Set.range (g.rayOn y C j).func).Finite := by
  intros j
  set H := g.restrict C with hH_def
  have hH_cent : IsCentered H.func := by
    convert hcent using 1;
    convert Iff.rfl using 1;
    constructor <;> intro h;
    · convert IsCentered_comp_homeomorph ( g := g.func ∘ Subtype.val ) ( g.restrictEquiv C ) using 1;
      constructor <;> intro h <;> simp_all +decide [ Function.comp_def ]; all_goals convert h using 1;
    · exact hcent
  have hH_rank : CBRank H.func = 1 + 1 ∨ CBRank H.func = 1 := by
    have hH_rank : CBRank H.func ≤ CBRank g.func := by
      have hH_rank : ScatFun.Reduces H g := by
        exact restrict_le_self g C;
      exact hH_rank.rank_monotone H.hScat g.hScat;
    obtain ⟨β, hβ⟩ := centered_scatFun_rank_succ H hH_cent;
    cases' lt_or_eq_of_le ( show β ≤ 1 from by
                              contrapose! hH_rank;
                              rw [ hβ, hg_rank ];
                              exact lt_of_le_of_lt ( by norm_num ) ( Order.succ_lt_succ hH_rank ) ) with hβ₁ hβ₁ <;> simp_all +decide [ Order.succ_le_iff ];
  cases' hH_rank with hH_rank hH_rank;
  · have hH_notmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) H := by
      contrapose! hnotmax;
      exact hnotmax.trans ( restrict_le_self g C );
    convert centered_two_rayOn_finImage H hH_rank hH_cent y _ hH_notmax j using 1;
    · ext;
      simp +decide only [ScatFun.rayOn, ScatFun.restrict, coe_setOf, mem_setOf_eq, EquivLike.range_comp, mem_range, comp_apply, Subtype.exists, mem_inter_iff, exists_prop, univ_inter];
      exact ⟨ fun ⟨ a, ha, ha', ha'' ⟩ => ⟨ a, ⟨ ha, ha'.1 ⟩, ha'.2, ha'' ⟩, fun ⟨ a, ⟨ ha, ha' ⟩, ha'', ha''' ⟩ => ⟨ a, ha, ⟨ ha', ha'' ⟩, ha''' ⟩ ⟩;
    · intros a ha; exact (by
      apply hconst;
      convert cbLevel_block_iff g C hC 1 a |>.1 ha using 1);
  · have hH_locallyConstant : IsLocallyConstant H.func := by
      exact isLocallyConstant_of_cbRank_le_one H ( by rw [ hH_rank ] );
    by_cases hH_inf : (Set.range H.func).Infinite;
    · have hH_equiv_id : ContinuouslyEquiv H.func (@id ℕ) := by
        apply_rules [ locally_constant_infinite_image ];
      exact False.elim <| not_isCentered_id <| isCentered_of_equiv hH_cent hH_equiv_id.symm;
    · have hH_finite : (Set.range (H.restrict {w : ↑H.domain | H.func w ∈ RaySet Set.univ y j}).func).Finite := by
        exact Set.Finite.subset ( Set.not_infinite.mp hH_inf ) ( Set.range_subset_iff.mpr fun x => Set.mem_range_self _ );
      convert hH_finite using 1;
      convert Set.ext fun x => ?_ using 1;
      simp +decide only [ScatFun.rayOn, ScatFun.restrict, coe_setOf, mem_setOf_eq, EquivLike.range_comp, mem_range, comp_apply, Subtype.exists, mem_inter_iff, exists_prop];
      exact ⟨ fun ⟨ a, ha, ha', hx ⟩ => ⟨ a, ⟨ ha, ha'.1 ⟩, ha'.2, hx ⟩, fun ⟨ a, ⟨ ha, ha' ⟩, ha'', hx ⟩ => ⟨ a, ha, ⟨ ha', ha'' ⟩, hx ⟩ ⟩


/-
**2-BQO at level `2` (`= 1 + 1`).**  `𝒞_{<2} = 𝒞_{≤1}`: the `rank = 1` part is 2-BQO
because it embeds into `FinGl genLeOne` (finite generation `cLeOne_finitely_generated`,
which is 2-BQO by `FinGl.isTwoBQO`); the `rank < 1` part is the given `hbqo`.  Replaces
`twoBQO_levelLT_succ` (which needs `lam` a limit) for `lam = 1`.
-/
lemma lamOne_twoBQO_levelLT_two
    (_hbqo : TwoBQO (ScatFun.LevelLT.reduces (1 : Ordinal.{0}))) :
    TwoBQO (ScatFun.LevelLT.reduces (1 + 1 : Ordinal.{0})) := by
  intro f;
  -- By definition of $f$, we know that for any $m < n$, $f m n hmn$ is in the set of functions with CB-rank less than 2.
  have h_cb_rank : ∀ m n hmn, CBRank (f m n hmn).val.func < 2 := by
    exact fun m n hmn => lt_of_lt_of_le ( f m n hmn |>.2 ) ( by norm_num );
  -- By definition of $f$, we know that for any $m < n$, $f m n hmn$ is in the set of functions with CB-rank at most 1.
  have h_cb_rank_le_one : ∀ m n hmn, CBRank (f m n hmn).val.func ≤ 1 := by
    intros m n hmn
    have h_cb_rank_lt_two : CBRank (f m n hmn).val.func < 2 := h_cb_rank m n hmn
    have h_cb_rank_le_one : CBRank (f m n hmn).val.func ≤ 1 := by
      contrapose! h_cb_rank_lt_two;
      convert Order.succ_le_of_lt h_cb_rank_lt_two using 1;
      norm_num
    exact h_cb_rank_le_one;
  have h_cb_rank_le_one : ∀ m n hmn, (f m n hmn).val ∈ ScatFun.FinGl genLeOne := by
    intros m n hmn
    apply cLeOne_finitely_generated
    exact ⟨zero_le _, h_cb_rank_le_one m n hmn⟩;
  obtain ⟨ m, n, l, hmn, hnl, h ⟩ := ScatFun.FinGl.isTwoBQO genLeOne ( fun m n hmn => ⟨ ( f m n hmn ).val, h_cb_rank_le_one m n hmn ⟩ );
  exact ⟨ m, n, l, hmn, hnl, h ⟩


lemma lamOne_caseB_local_in_class
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (1 : Ordinal.{0})))
    (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) g) :
    IsLocallyInClass g.func
      (fun (C : Set ↑g.domain) (_ : ↥C → Baire) =>
        ∀ j, (Set.range (g.rayOn y C j).func).Finite) := by
  intro x;
  have := scatFun_centered_cylinder_witness ( 1 + 1 ) ( by
    convert omega1_add_nat 1 one_lt_omega1 1 using 1;
    norm_cast ) ( lamOne_twoBQO_levelLT_two hbqo ) g hg_rank x
  generalize_proofs at *; (
  obtain ⟨ n, hn ⟩ := this
  generalize_proofs at *; (
  refine ⟨ g.cyl x n, ?_, ?_, ?_ ⟩;
  · exact baire_nbhd'_isClopen g.domain x n;
  · exact g.mem_cyl x n;
  · apply_rules [ lamOne_caseB_block_rayOn_finImage ];
    exact g.cyl_isOpen x n))


/-
**Case-B block decomposition (`λ = 1`).**  Mirrors `caseB_decomposition` with the
finite-image-ray class.
-/
lemma lamOne_caseB_decomposition
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (1 : Ordinal.{0})))
    (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) g) :
    ∃ A : ℕ → Set ↑g.domain, g.IsDisjointUnion A ∧
      ∀ i j, (Set.range (g.rayOn y (A i) j).func).Finite := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set ↑g.domain, g.IsDisjointUnion A ∧ ∀ i, ∀ j, (Set.range (g.rayOn y (A i) j).func).Finite := by
    have hloc := lamOne_caseB_local_in_class hbqo g hg_rank y hconst hnotmax
    obtain ⟨A, hA⟩ := locally_implies_disjointUnion_nat g.func (by
    by_contra h_empty_domain;
    simp_all +decide [ CBRank ];
    have h_empty_domain : ∀ α, CBLevel g.func α = ∅ := by
      grind +splitIndPred;
    simp_all +decide [ CBLevel ]) (fun C x => ∀ j, (Set.range (g.rayOn y C j).func).Finite) hloc (by
    intros C D hCD hD hC j
    have h_rayOn_subset : ScatFun.Reduces (g.restrict (D ∩ {a | g.func a ∈ RaySet Set.univ y j})) (g.restrict (C ∩ {a | g.func a ∈ RaySet Set.univ y j})) := by
      apply restrict_reduces_of_subset g (Set.inter_subset_inter_left _ hCD);
    convert reduces_finite_range _ _ h_rayOn_subset ( hC j ) using 1);
    exact ⟨ A, ⟨ hA.1, hA.2.1, hA.2.2.1 ⟩, hA.2.2.2 ⟩;
  use A


/-
**Diagonal lower piece `C₁ ≤ k₂` (`λ = 1`).**  Mirrors `caseB_C1_reduces_minFun`:
the `j`-th ray of `g│_{C₁}` is the finite union over `i ≤ j` of finite-image pieces, hence
has finite image; conclude with `lamOne_finImage_rays_reduces_minFun_one`.
-/
lemma lamOne_caseB_C1_reduces_minFun (g : ScatFun) (y : Baire)
    (A : ℕ → Set ↑g.domain) (_hdu : g.IsDisjointUnion A)
    (hfin : ∀ i j, (Set.range (g.rayOn y (A i) j).func).Finite) :
    ScatFun.Reduces
      (g.restrict (⋃ i, A i ∩
        {z : ↑g.domain | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}))
      (ScatFun.minFun 1 one_lt_omega1) := by
  apply lamOne_finImage_rays_reduces_minFun_one;
  intro j
  have h_range : (range ((g.restrict (⋃ i, A i ∩ {z | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet univ y j)ᶜ})).rayOn y Set.univ j).func) ⊆ ⋃ i ∈ Finset.range (j + 1), (Set.range (g.rayOn y (A i) j).func) := by
    intro x hx;
    simp_all +decide [ ScatFun.rayOn, ScatFun.restrict ];
    obtain ⟨ a, ⟨ ha₁, i, hi₁, hi₂ ⟩, hi₃, hi₄ ⟩ := hx; use i; simp_all +decide [ ScatFun.restrictEquiv ] ;
    grind +suggestions;
  exact Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet ( Finset.range ( j + 1 ) ) ) fun i hi => hfin i j ) h_range


/-- **Diagonal upper bound `g ≤ k₂ ⊕ ℓ₁` (`λ = 1`).**  Mirrors `simple_caseB_g_reduces_Gl`,
using `lamOne_caseB_decomposition`, `caseB_C0_reduces_maxFun` (general in `lam`) and
`lamOne_caseB_C1_reduces_minFun`. -/
lemma lamOne_g_reduces_Gl
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (1 : Ordinal.{0})))
    (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1) (_hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 one_lt_omega1) g) :
    ScatFun.Reduces g
      (ScatFun.minFun 1 one_lt_omega1 ⊕ ScatFun.maxFun 1 one_lt_omega1) := by
  obtain ⟨A, hdu, hray⟩ := lamOne_caseB_decomposition hbqo g hg_rank y hconst hnotmax;
  obtain ⟨C0, C1, hC0, hC1, hC⟩ : ∃ C0 C1 : Set ↑g.domain, IsClopen C0 ∧ IsClopen C1 ∧ C0 ∪ C1 = Set.univ ∧ Disjoint C0 C1 ∧
    ScatFun.Reduces (g.restrict C0) (ScatFun.maxFun 1 one_lt_omega1) ∧
    ScatFun.Reduces (g.restrict C1) (ScatFun.minFun 1 one_lt_omega1) := by
      refine' ⟨ _, _, _, _, _, _, caseB_C0_reduces_maxFun 1 one_lt_omega1 g y hconst A hdu, lamOne_caseB_C1_reduces_minFun g y A hdu hray ⟩;
      · refine ⟨ ?_, ?_ ⟩;
        · refine isClosed_of_closure_subset ?_;
          intro x hx;
          rw [ mem_closure_iff ] at hx;
          contrapose! hx;
          refine ⟨ { z : ↑g.domain | ∃ i, z ∈ A i ∧ ∀ j < i, g.func z ∉ RaySet univ y j }, ?_, ?_, ?_ ⟩;
          · simp +decide [ Set.setOf_exists ];
            refine isOpen_iUnion fun i => ?_;
            simp +decide only [setOf_and, setOf_forall];
            refine IsOpen.inter ?_ ?_;
            · exact hdu.1 i |>.2;
            · refine isOpen_iff_forall_mem_open.mpr ?_;
              intro x hx;
              refine ⟨ ⋂ j < i, { z : ↑g.domain | g.func z ∉ RaySet univ y j }, ?_, ?_, ?_ ⟩;
              · exact Set.Subset.rfl;
              · rw [ show ( ⋂ j : ℕ, ⋂ ( _ : j < i ), { z : ↑g.domain | g.func z ∉ RaySet univ y j } ) = ⋂ j ∈ Finset.range i, { z : ↑g.domain | g.func z ∉ RaySet univ y j } by ext; simp +decide [ Finset.mem_range ] ];
                exact isOpen_biInter_finset fun j hj => IsOpen.preimage g.hCont <| isOpen_compl_iff.mpr <| isClopen_raySet y j |>.1;
              · exact hx;
          · simp_all +decide ;
            obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ x ) ; exact ⟨ i, hi, hx i hi ⟩ ;
          · simp_all +decide [ Set.ext_iff ];
            intro a ha i hi hi' j hj hj';
            cases eq_or_ne i j <;> simp_all +decide;
            exact False.elim <| hdu.2.1 i j ‹_› |> fun h => h.le_bot ⟨ hi, hj ⟩;
        · refine isOpen_iUnion fun i => ?_;
          refine IsOpen.inter ( hdu.1 i |>.2 ) ?_;
          refine' IsOpen.preimage g.hCont _;
          exact isOpen_biUnion fun j hj => isClopen_raySet y j |>.2;
      · have hC0_open : IsOpen (⋃ i, A i ∩ {z | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}) := by
          refine isOpen_iUnion fun i => ?_;
          refine IsOpen.inter ( hdu.1 i |>.2 ) ?_;
          refine IsOpen.preimage g.hCont ?_;
          refine' isOpen_compl_iff.mpr _;
          exact isClosed_biUnion_finset fun j _ => isClopen_raySet y j |>.1;
        have hC0_closed : IsClosed (⋃ i, A i ∩ {z | g.func z ∈ (⋃ j ∈ Finset.range i, RaySet Set.univ y j)ᶜ}) := by
          have hC0_compl_open : IsOpen (⋃ i, A i ∩ {z | g.func z ∈ ⋃ j ∈ Finset.range i, RaySet Set.univ y j}) := by
            refine isOpen_iUnion fun i => ?_;
            refine' IsOpen.inter ( hdu.1 i |>.2 ) _;
            exact g.hCont.isOpen_preimage _ ( isClopen_biUnion_finset ( fun j hj => isClopen_raySet y j ) |> IsClopen.isOpen )
          convert hC0_compl_open.isClosed_compl using 1;
          ext; simp [Set.mem_compl_iff, Set.mem_iUnion];
          constructor;
          · rintro ⟨ i, hi, hi' ⟩ j hj k hk; have := hdu.2.1 i j; simp_all +decide [ Set.disjoint_left ] ;
            grind;
          · intro hx;
            obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ _ );
            exact ⟨ i, hi, hx i hi ⟩;
        constructor <;> assumption;
      · ext x; simp ;
        obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hdu.2.2.symm ▸ Set.mem_univ x ) ; exact if hi' : ∃ j < i, g.func x ∈ RaySet univ y j then Or.inl ⟨ i, hi, hi' ⟩ else Or.inr ⟨ i, hi, fun j hj => by aesop ⟩ ;
      · simp +contextual [ Set.disjoint_left ];
        intro a ha x hx y hy hxy z hz; have := hdu.2.1 x z; simp_all +decide [ Set.disjoint_left ] ;
        grind +revert;
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Set ↑g.domain, g.IsDisjointUnion P ∧ P 0 = C1 ∧ P 1 = C0 ∧ ∀ i ≥ 2, P i = ∅ := by
    refine ⟨ fun i => if i = 0 then C1 else if i = 1 then C0 else ∅, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ ScatFun.IsDisjointUnion ];
    · refine ⟨ ?_, ?_, ?_ ⟩;
      · intro i; split_ifs <;> simp_all +decide [ IsClopen ] ;
      · grind +locals;
      · simp_all +decide [ Set.ext_iff ];
        exact fun a ha => by rcases hC.1 a ha with h | h <;> [ exact ⟨ 1, by simpa using h ⟩ ; exact ⟨ 0, by simpa using h ⟩ ] ;
    · grind;
  refine ( scatFun_reduces_gl_of_domain_partition g P hP.1 ).trans ?_;
  refine ScatFun.gl_reduces_of_pointwise ?_ ?_ ?_;
  intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ *, ScatFun.copiesSeq ] ;
  · exact hC.2.2.2;
  · exact hC.2.2.1;
  · use fun x => x.2.choose_spec.elim;
    simp +decide only [ScatFun.empty, Subtype.forall];
    exact ⟨ continuous_of_const fun x y => by tauto, fun _ => 0, continuousOn_const, fun x hx => by tauto ⟩


/-
**A ray of infinite image is `≡ ℓ₁ = maxFun 1`.**  A ray of a simple rank-`2` function
has CB-rank `≤ 1`, hence is locally constant; with infinite image it is `≡ id_ℕ ≡ ℓ₁`
(`locally_constant_infinite_image`, `maxFun_one_equiv_id`).
-/
lemma lamOne_ray_infImage_equiv_maxFun (g : ScatFun) (y : Baire)
    (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (N : ℕ) (hinf : (Set.range (g.rayOn y Set.univ N).func).Infinite) :
    ScatFun.Equiv (g.rayOn y Set.univ N) (ScatFun.maxFun 1 one_lt_omega1) := by
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨h₁, h₂⟩ : IsLocallyConstant (ScatFun.rayOn g y Set.univ N).func ∧ ¬(Set.range (ScatFun.rayOn g y Set.univ N).func).Finite := by
    refine ⟨ ?_, hinf ⟩;
    apply isLocallyConstant_of_cbRank_le_one;
    have := ScatFun.rayOn_cbRank_lt g 1 y hconst Set.univ isOpen_univ N;
    exact Order.le_of_lt_succ this;
  apply h_contra;
  obtain ⟨h₁, h₂⟩ : ContinuouslyEquiv (g.rayOn y Set.univ N).func (id : ℕ → ℕ) ∧ ¬(Set.range (g.rayOn y Set.univ N).func).Finite := by
    apply And.intro;
    · apply_rules [ locally_constant_infinite_image ];
    · exact h₂;
  have h₃ : ContinuouslyEquiv (ScatFun.maxFun 1 one_lt_omega1).func (id : ℕ → ℕ) := by
    convert maxFun_one_equiv_id using 1;
  exact ⟨ h₁.1.trans h₃.2, h₃.1.trans h₁.2 ⟩


/-- **Case-B lower bound `k₂ ⊕ ℓ₁ ≤ g` (`λ = 1`).**  Mirrors `simple_caseB_Gl_reduces_g`,
using a ray `W = RaySet univ y N` that is `≡ ℓ₁` (instead of the limit step
`limit_rank_equiv_maxFun`); `k₂ ≤ g│_{Wᶜ}` by minimality (the centre survives in `Wᶜ`). -/
lemma lamOne_Gl_reduces_g (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1)
    (hg_simple : SimpleFun g.func)
    (y : Baire) (hconst : ∀ x ∈ CBLevel g.func 1, g.func x = y)
    (N : ℕ) (hrayN : ScatFun.Equiv (g.rayOn y Set.univ N) (ScatFun.maxFun 1 one_lt_omega1)) :
    ScatFun.Reduces
      (ScatFun.minFun 1 one_lt_omega1 ⊕ ScatFun.maxFun 1 one_lt_omega1) g := by
  set W : Set Baire := RaySet Set.univ y N
  set B : ℕ → Set Baire := fun i => if i = 0 then Wᶜ else if i = 1 then W else (∅ : Set Baire);
  have h_equiv : ScatFun.Equiv g (ScatFun.gl (fun i => Fb g B i)) := by
    apply equiv_gl_of_codomain_clopen_partition g (fun i => Fb g B i) B (by
    simp +zetaDelta only [Ordinal.add_one_eq_succ, Ordinal.succ_one, Subtype.forall] at *;
    intro i; split_ifs <;> [ exact IsClopen.compl ( isClopen_raySet y N ) ; exact isClopen_raySet y N; exact isClopen_empty ] ;) (by
    grind +qlia) (by
    ext x; simp [B, W];
    exact ⟨ if x ∈ RaySet univ y N then 1 else 0, by aesop ⟩) (by
    intro i; exact (by
    exact Fb_func_eq g B i ▸ ContinuouslyEquiv.refl _););
  have h_red : ∀ i, ScatFun.Reduces (ScatFun.copiesSeq ![ScatFun.minFun 1 one_lt_omega1, ScatFun.maxFun 1 one_lt_omega1] ![1, 1] i) (Fb g B i) := by
    intro i
    rcases i with ( _ | _ | i ) <;> simp_all +decide [ ScatFun.copiesSeq ];
    · obtain ⟨ x₀, hx₀ ⟩ := simple_lam_data 1 g (by simpa using hg_rank) hg_simple |>.1;
      convert minFun_is_minimum 1 one_lt_omega1 ( Fb g B 0 |> ScatFun.domain ) ( Fb g B 0 |> ScatFun.func ) ( Fb g B 0 |> ScatFun.hCont ) ( Fb g B 0 |> ScatFun.hScat ) _ using 1;
      use ⟨x₀, by
        simp +zetaDelta only at *;
        simp +decide only [Fb, ↓reduceIte, RaySet, mem_univ, ne_eq, true_and, mem_compl_iff, mem_setOf_eq, not_and, Decidable.not_not];
        simp +decide [ ScatFun.restrict, hconst _ x₀.2 hx₀ ]⟩
      generalize_proofs at *;
      convert cbLevel_block_iff g { z : g.domain | g.func z ∈ Wᶜ } _ 1 ⟨ x₀, by assumption ⟩ |>.2 hx₀ using 1;
      exact IsOpen.preimage ( g.hCont ) ( isClopen_raySet y N |> IsClopen.compl |> IsClopen.isOpen );
    · convert hrayN.2 using 1;
      exact rayOn_eq_corestrict g y N ▸ rfl;
    · convert ScatFun.empty_reduces _ using 1;
  have h_red_gl : ScatFun.Reduces (ScatFun.gl (ScatFun.copiesSeq ![ScatFun.minFun 1 one_lt_omega1, ScatFun.maxFun 1 one_lt_omega1] ![1, 1])) (ScatFun.gl (fun i => Fb g B i)) := by
    grind +suggestions;
  exact h_red_gl.trans h_equiv.2

end
