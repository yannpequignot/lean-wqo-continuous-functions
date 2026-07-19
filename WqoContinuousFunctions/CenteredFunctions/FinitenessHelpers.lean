import WqoContinuousFunctions.CenteredFunctions.CenteredAsPgluing
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Helper lemmas for Theorem 4.9 (Finitenessofcenteredfunctions)

CB-rank / `pgl` / `minFun` / finite-gluing helper lemmas supporting
`finitenessOfCenteredFunctions`.  Extracted from `CenteredFunctions/Theorems.lean`.

The CB-rank / `pgl` / `minFun` lemmas below (`cbRank_rayFun_pgl`, `cbRank_pgl_regular`,
`pgl_reduces_pgl`, `ordinal_limit_add_nat`, `minFun_cbRank_via_pgl`, `iSup_succ_cofinalSeq`,
`minFun_cbRank_eq`, `minFun_limit_equiv_pgl`, `reduces_minFun_cofinal`) are defined once, in
`CenteredFunctions/Theorems.lean`'s `ConseqMinFunAux` namespace, and re-exported here under
their bare names so downstream callers (and the helpers below) keep using them unqualified.
-/

export ConseqMinFunAux (cbRank_rayFun_pgl cbRank_pgl_regular pgl_reduces_pgl
  ordinal_limit_add_nat minFun_cbRank_via_pgl iSup_succ_cofinalSeq minFun_cbRank_eq
  minFun_limit_equiv_pgl reduces_minFun_cofinal)


/-- Two continuously-equivalent `ScatFun`s have the same CB-rank. -/
lemma cbRank_eq_of_equiv {F G : ScatFun} (h : ScatFun.Equiv F G) :
    CBRank F.func = CBRank G.func :=
  le_antisymm
    (ContinuouslyReduces.rank_monotone F.hScat G.hScat h.1)
    (ContinuouslyReduces.rank_monotone G.hScat F.hScat h.2)


/-
A monotone (more generally, regular) sequence has the same pointed gluing,
up to equivalence, as any of its tails.
-/
lemma pgl_tail_equiv (s : ℕ → ScatFun) (hs : IsMonotoneSeq s) (j : ℕ) :
    ScatFun.Equiv (ScatFun.pgl (fun i => s (i + j))) (ScatFun.pgl s) := by
  constructor;
  · apply pgl_reduces_pgl;
    exact fun i j₀ => ⟨ i + j + j₀, by linarith, hs _ _ <| by linarith ⟩;
  · apply pgl_reduces_pgl;
    exact fun i j₀ => ⟨ j₀ + i, by linarith, hs _ _ <| by linarith ⟩


/-
Explicit block reduction into a pointed gluing, exposing the underlying point
`(0)^d(1)·` and the value `prependZerosOne d ((s d).func z)`.
-/
lemma pgl_block_reduction_explicit (s : ℕ → ScatFun) (d : ℕ) :
    ∃ (σ : ↑(s d).domain → ↑(ScatFun.pgl s).domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun z => (ScatFun.pgl s).func (σ z)) ∧
      (∀ z, (s d).func z = τ ((ScatFun.pgl s).func (σ z))) ∧
      (∀ z, ((σ z : ↑(ScatFun.pgl s).domain) : Baire) = prependZerosOne d (z : Baire)) ∧
      (∀ z, (ScatFun.pgl s).func (σ z) = prependZerosOne d ((s d).func z)) := by
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
  generalize_proofs at *;
  exact fun z => ⟨ prependZerosOne d z.val, prependZerosOne_mem_pointedGluingSet _ d z.val z.prop ⟩;
  exact fun x => stripZerosOne d x;
  · exact Continuous.subtype_mk ( continuous_prependZerosOne d |> Continuous.comp <| continuous_subtype_val ) _;
  · exact Continuous.continuousOn ( continuous_stripZerosOne d );
  · intro z
    generalize_proofs at *;
    have := ScatFun.pgl_func_block s d z; have := stripZerosOne_prependZerosOne d ( ( s d ).func z ) ; aesop;
  · exact ⟨ fun z => rfl, fun z => ScatFun.pgl_func_block s d z ⟩

/-
Each block of a pointed gluing reduces into the gluing (block-`i` embedding).
-/
lemma block_reduces_pgl (s : ℕ → ScatFun) (i : ℕ) :
    ScatFun.Reduces (s i) (ScatFun.pgl s) := by
  obtain ⟨σ, τ, hσc, hτc, heq, -, -⟩ := pgl_block_reduction_explicit s i
  exact ⟨σ, hσc, τ, hτc, heq⟩


/-
A generator block with positive multiplicity reduces into the finite gluing.
-/
lemma block_reduces_Gl {m : ℕ} (B : Fin m → ScatFun) (mult : Fin m → ℕ)
    (f : Fin m) (h : 0 < mult f) :
    ScatFun.Reduces (B f) (ScatFun.Gl B mult) := by
  -- Since the multiplicity is positive, the block B f appears in the copiesList.
  have h_block_in_list : B f ∈ List.flatMap (fun i => List.replicate (mult i) (B i)) (List.finRange m) := by
    rw [ List.mem_flatMap ] ; use f ; aesop;
  -- Since B f is in the copiesList, there exists some p such that copiesSeq B mult p = B f.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p < List.length (List.flatMap (fun i => List.replicate (mult i) (B i)) (List.finRange m)) ∧ (ScatFun.copiesSeq B mult p) = B f := by
    obtain ⟨ p, hp ⟩ := List.mem_iff_get.mp h_block_in_list; use p; simp_all +decide [ ScatFun.copiesSeq ] ;
    refine ⟨ ?_, ?_ ⟩;
    · convert p.2 using 1 ; simp +decide [ List.length_flatMap ];
    · rw [ ← hp, ScatFun.copiesList ];
      grind;
  -- Since the block B f appears in the copiesList, we can reduce it to the block at position p in the gluing.
  have h_block_reduces : ScatFun.Reduces (ScatFun.copiesSeq B mult p) (ScatFun.gl (ScatFun.copiesSeq B mult)) := by
    refine ⟨ ?_, ?_, ?_ ⟩;
    exact fun x => ⟨ prepend p x.val, mem_gluingSet_prepend x.prop ⟩;
    · exact Continuous.subtype_mk ( continuous_prepend p |> Continuous.comp <| continuous_subtype_val ) _;
    · refine ⟨ fun x => unprepend x, ?_, ?_ ⟩;
      · exact Continuous.continuousOn ( continuous_unprepend );
      · intro x; simp +decide [ ScatFun.gl, GluingFunVal_prepend ] ;
        exact Eq.symm ( unprepend_prepend _ _ );
  aesop

/-
A finite gluing whose multiplicities are supported on the image of an injective
reindexing `ι` lies in the `FinGl` class of the sub-family `B ∘ ι`.
-/
lemma Gl_subfamily_mem {m : ℕ} (B : Fin m → ScatFun) (mult : Fin m → ℕ)
    {k : ℕ} (ι : Fin k → Fin m) (hι : Function.Injective ι)
    (hsupp : ∀ f, mult f ≠ 0 → f ∈ Set.range ι) :
    ScatFun.Gl B mult ∈ ScatFun.FinGl (B ∘ ι) := by
  -- Let `t' := mult ∘ ι`. By definition of `FinGl`, it suffices to show `Reduces (Gl (B ∘ ι) t') (Gl B mult)` and `Reduces (Gl B mult) (Gl (B ∘ ι) t')`.
  use fun i => mult (ι i);
  have h_equiv : List.Perm (List.flatMap (fun i => List.replicate (mult (ι i)) (B (ι i))) (List.finRange k)) (List.flatMap (fun i => List.replicate (mult i) (B i)) (List.finRange m)) := by
    rw [ List.perm_iff_count ];
    intro a; by_cases ha : a ∈ Set.range ( fun i : Fin k => B ( ι i ) ) <;> simp_all +decide [ List.count_flatMap ] ;
    · have h_count_eq : ∑ i : Fin m, (if B i = a then mult i else 0) = ∑ i : Fin k, (if B (ι i) = a then mult (ι i) else 0) := by
        rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ι Finset.univ ) ) ];
        · rw [ Finset.sum_image <| by tauto ];
        · grind;
      grind +suggestions;
    · rw [ List.sum_eq_zero, List.sum_eq_zero ] <;> simp_all +decide [ Function.comp, List.count_replicate ];
      exact fun f hf => Classical.not_not.1 fun h => by obtain ⟨ y, rfl ⟩ := hsupp f h; exact ha y hf;
  have h_equiv : ∃ (e : ℕ → ℕ) (e' : ℕ → ℕ), Function.Injective e ∧ Function.Injective e' ∧
    (∀ i, ScatFun.Reduces (List.getD (List.flatMap (fun i => List.replicate (mult (ι i)) (B (ι i))) (List.finRange k)) i ScatFun.empty) (List.getD (List.flatMap (fun i => List.replicate (mult i) (B i)) (List.finRange m)) (e i) ScatFun.empty)) ∧
    (∀ i, ScatFun.Reduces (List.getD (List.flatMap (fun i => List.replicate (mult i) (B i)) (List.finRange m)) i ScatFun.empty) (List.getD (List.flatMap (fun i => List.replicate (mult (ι i)) (B (ι i))) (List.finRange k)) (e' i) ScatFun.empty)) := by
      have h_equiv : ∀ (l1 l2 : List ScatFun), List.Perm l1 l2 → ∃ (e e' : ℕ → ℕ), Function.Injective e ∧ Function.Injective e' ∧
        (∀ i, List.getD l1 i ScatFun.empty = List.getD l2 (e i) ScatFun.empty) ∧
        (∀ i, List.getD l2 i ScatFun.empty = List.getD l1 (e' i) ScatFun.empty) := by
          intros l1 l2 h_perm
          induction' h_perm with l1 l2 h_perm ih;
          · exact ⟨ fun i => i, fun i => i, fun i j hij => by simpa using hij, fun i j hij => by simpa using hij, fun i => rfl, fun i => rfl ⟩;
          · obtain ⟨ e, e', he, he', he'', he''' ⟩ := ‹_›;
            use fun i => if i = 0 then 0 else e (i - 1) + 1, fun i => if i = 0 then 0 else e' (i - 1) + 1;
            refine ⟨ ?_, ?_, ?_, ?_ ⟩;
            · intro i j hij;
              grind;
            · intro i j hij; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp +decide at hij ⊢;
              exact he' hij;
            · grind;
            · grind;
          · refine ⟨ fun i => if i = 0 then 1 else if i = 1 then 0 else i, fun i => if i = 0 then 1 else if i = 1 then 0 else i, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ Function.Injective ];
            · grind;
            · lia;
            · rintro ( _ | _ | i ) <;> simp +decide;
            · rintro ( _ | _ | i ) <;> simp +decide;
          · rename_i h₁ h₂ h₃ h₄;
            obtain ⟨ e, e', he, he', he'', he''' ⟩ := h₃
            obtain ⟨ f, f', hf, hf', hf'', hf''' ⟩ := h₄
            use fun i => f (e i), fun i => e' (f' i);
            exact ⟨ hf.comp he, he'.comp hf', fun i => by rw [ he'', hf'' ], fun i => by rw [ hf''', he''' ] ⟩;
      specialize h_equiv _ _ ‹_›;
      obtain ⟨ e, e', he, he', he'', he''' ⟩ := h_equiv;
      refine ⟨ e, e', he, he', ?_, ?_ ⟩;
      · intro i; specialize he'' i; rw [ he'' ] ;
        constructor;
        exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
      · intro i; specialize he''' i; rw [ he''' ] ;
        constructor;
        exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
  obtain ⟨ e, e', he, he', h₁, h₂ ⟩ := h_equiv;
  exact ⟨ ScatFun.gl_reduces_of_blockEmbed _ _ e he h₁, ScatFun.gl_reduces_of_blockEmbed _ _ e' he' h₂ ⟩

/-
If every block `s i` is empty, the pointed gluing `pgl s` is the one-point
function `k_1 = minFun 0`.
-/
lemma pgl_allEmpty_equiv_minFun_zero (s : ℕ → ScatFun)
    (hempty : ∀ i, IsEmpty ↥(s i).domain) (h : (0 : Ordinal.{0}) < omega1) :
    ScatFun.Equiv (ScatFun.pgl s) (ScatFun.minFun 0 h) := by
  constructor;
  · refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    exact fun x => ⟨ zeroStream, by
      convert zeroStream_mem_pointedGluingSet _;
      convert MinDom_zero ⟩
    all_goals generalize_proofs at *;
    exact continuous_const;
    exact fun _ => zeroStream;
    · exact continuousOn_const;
    · intro x; exact (by
      convert ScatFun.pgl_func_zeroStream s _;
      · have := x.2;
        cases this <;> aesop;
      · exact zeroStream_mem_pointedGluingSet _);
  · apply minFun_is_minimum 0 h (ScatFun.pgl s).domain (ScatFun.pgl s).func (ScatFun.pgl s).hCont (ScatFun.pgl s).hScat; simp [CBLevel_zero];
    exact ⟨ ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩, Set.mem_univ _ ⟩

/-
**Finite-generation packaging for the pointed-gluing case.**
If a monotone tail sequence `t` consists of finite gluings `t i ≡ Gl B (mult i)`
with at least one positive multiplicity, then `pgl t` is equivalent to the pointed
gluing of a non-empty sub-family `B ∘ ι`.
-/
lemma pgl_finGl_to_subfamily {m : ℕ} (B : Fin m → ScatFun) (t : ℕ → ScatFun)
    (ht_mono : IsMonotoneSeq t) (mult : ℕ → (Fin m → ℕ))
    (ht_eq : ∀ i, ScatFun.Equiv (t i) (ScatFun.Gl B (mult i)))
    (hne : ∃ i f, 0 < mult i f) :
    ∃ (k : ℕ) (ι : Fin k → Fin m), 0 < k ∧
      ScatFun.Equiv (ScatFun.pgl t) (ScatFun.pgl (ScatFun.repSeq (B ∘ ι))) := by
  revert hne;
  intro hne
  set S : Finset (Fin m) := Finset.univ.filter (fun f => ∃ i, 0 < mult i f)
  obtain ⟨k, hk⟩ : ∃ k, S.card = k ∧ 0 < k := by
    exact ⟨ _, rfl, Finset.card_pos.mpr ⟨ hne.choose_spec.choose, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hne.choose, hne.choose_spec.choose_spec ⟩ ⟩ ⟩;
  refine ⟨ k, fun x => S.orderEmbOfFin hk.1 x, hk.2, ?_ ⟩;
  refine ⟨ ?_, ?_ ⟩;
  · apply ScatFun.finitegenerationAndPgluing_upper;
    intro i
    use ScatFun.Gl B (mult i);
    refine ⟨ ?_, ht_eq i |>.1 ⟩;
    apply Gl_subfamily_mem;
    · exact fun x y hxy => by simpa [ Fin.ext_iff ] using hxy;
    · intro f hf; have := Finset.mem_coe.mp ( Finset.mem_coe.mpr ( show f ∈ S from Finset.mem_filter.mpr ⟨ Finset.mem_univ _, i, Nat.pos_of_ne_zero hf ⟩ ) ) ; aesop;
  · apply ScatFun.finitegenerationAndPgluing_lower;
    intro x i
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < mult i₀ (S.orderEmbOfFin hk.1 x) := by
      exact Finset.mem_filter.mp ( S.orderEmbOfFin_mem hk.1 x ) |>.2;
    have h_block_reduces_Gl : ScatFun.Reduces (B (S.orderEmbOfFin hk.1 x)) (ScatFun.Gl B (mult i₀)) :=
      block_reduces_Gl B (mult i₀) (S.orderEmbOfFin hk.1 x) hi₀
    have h_Gl_reduces_t : ScatFun.Reduces (ScatFun.Gl B (mult i₀)) (t i₀) := by
      exact ht_eq i₀ |>.2;
    exact ⟨ Max.max i i₀, le_max_left _ _, h_block_reduces_Gl.trans ( h_Gl_reduces_t.trans ( ht_mono _ _ ( le_max_right _ _ ) ) ) ⟩

/-
The finite gluing with all-zero multiplicities is empty.
-/
lemma Gl_zero_isEmpty {m : ℕ} (B : Fin m → ScatFun) :
    IsEmpty ↥(ScatFun.Gl B (0 : Fin m → ℕ)).domain := by
  unfold ScatFun.Gl;
  unfold ScatFun.copiesSeq ScatFun.gl; simp +decide [ ScatFun.copiesList ] ;
  ext x; simp [GluingSet];
  exact fun n y hy => False.elim <| hy

/-- **A plain gluing whose only inhabited block is `0` reduces to that block.**
If every block of `F` past index `0` is empty, then any point of `gl F` lives in
block `0`; mapping it by `unprepend` lands in `(F 0).domain`, and `τ = prepend 0`
recovers the glued value.  This is the single-block special case where the plain
gluing collapses to its base block (the empty tail contributes nothing). -/
lemma gl_single_le (F : ℕ → ScatFun)
    (hemp : ∀ k, k ≠ 0 → IsEmpty ↥(F k).domain) :
    ScatFun.Reduces (ScatFun.gl F) (F 0) := by
  -- Every point of `gl F` has first coordinate `0` and `unprepend`-tail in `(F 0).domain`.
  have hidx : ∀ x : ↥(ScatFun.gl F).domain,
      x.val 0 = 0 ∧ unprepend x.val ∈ (F 0).domain := by
    intro x
    obtain ⟨i, hi0, hmem⟩ := GluingSet_inverse_short (fun i => (F i).domain) x
    rcases eq_or_ne i 0 with hi | hi
    · subst hi; exact ⟨hi0, hmem⟩
    · have hE := hemp i hi
      rw [Set.isEmpty_coe_sort] at hE
      rw [hE] at hmem
      exact absurd hmem (Set.notMem_empty _)
  refine ⟨fun x => ⟨unprepend x.val, (hidx x).2⟩, ?_, prepend 0, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_unprepend.comp continuous_subtype_val) _
  · exact (continuous_prepend 0).continuousOn
  · intro x
    obtain ⟨hx0, hmem0⟩ := hidx x
    have hxval : x.val = prepend 0 (unprepend x.val) := by
      rw [← hx0]; exact (prepend_unprepend x.val).symm
    calc (ScatFun.gl F).func x
        = (ScatFun.gl F).func ⟨prepend 0 (unprepend x.val), mem_gluingSet_prepend hmem0⟩ :=
          congrArg _ (Subtype.ext hxval)
      _ = prepend 0 ((F 0).func ⟨unprepend x.val, hmem0⟩) :=
          GluingFunVal_prepend (fun i => (F i).domain) (fun _ => Set.univ)
            (ScatFun.glBlock F) 0 ⟨unprepend x.val, hmem0⟩ (mem_gluingSet_prepend hmem0)

/-- **A single generator lies in its own one-element `FinGl`.**  Taking one copy
(`t = ![1]`) gives `Gl ![h] ![1] ≡ h`: the `→` reduction is `block_reduces_Gl`
(block `0` into the gluing), the `←` reduction is `gl_single_le` (the gluing's
only inhabited block is `h`). -/
lemma single_mem_finGl (h : ScatFun) : h ∈ ScatFun.FinGl ![h] := by
  -- `copiesList ![h] ![1] = [h]`, so block `0` is `h` and blocks `≥ 1` are empty.
  have hcl : ScatFun.copiesList ![h] ![1] = [h] := by
    simp +decide [ScatFun.copiesList, List.finRange]
  have hF0 : ScatFun.copiesSeq ![h] ![1] 0 = h := by
    simp [ScatFun.copiesSeq, hcl]
  have hemp : ∀ k, k ≠ 0 → IsEmpty ↥(ScatFun.copiesSeq ![h] ![1] k).domain := by
    intro k hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcs : ScatFun.copiesSeq ![h] ![1] k = ScatFun.empty := by
      simp only [ScatFun.copiesSeq, hcl]
      rw [List.getD_eq_default]
      simpa using hk1
    rw [hcs]
    exact ⟨fun x => Set.notMem_empty x.1 x.2⟩
  refine ⟨![1], ?_, ?_⟩
  · -- `Reduces (Gl ![h] ![1]) h`
    have hred := gl_single_le (ScatFun.copiesSeq ![h] ![1]) hemp
    rw [hF0] at hred
    exact hred
  · -- `Reduces h (Gl ![h] ![1])`
    have hred := block_reduces_Gl ![h] ![1] 0 (by norm_num)
    simpa using hred

/-- `FinGl B` is closed under continuous equivalence: a function equivalent to a
member of `FinGl B` is itself in `FinGl B`. -/
lemma finGl_closed_equiv {m : ℕ} (B : Fin m → ScatFun) {f f' : ScatFun}
    (hf : f ∈ ScatFun.FinGl B) (h : ScatFun.Equiv f f') : f' ∈ ScatFun.FinGl B := by
  obtain ⟨t, h1, h2⟩ := hf
  exact ⟨t, h1.trans h.1, h.2.trans h2⟩

/-! ## Base case of finite generation: `𝒞_{≤1}` (`LocallyConstantFunctions`, Prop 2.24)

The class of scattered continuous functions of CB-rank `≤ 1` is finitely generated
by the two generators `k₁ = minFun 0` (a single point `{0^ω}`) and
`ℓ₁ = maxFun 1` (`≡ id_ℕ`).  This is the base of the finite-generation induction
(`levels_finitely_generated`) and is what discharges the `lam = 1` case of
Corollary 4.10 (applied with `lam = 0`, `n = 1`).

The analytic inputs are isolated as named lemmas (the rank↔locally-constant bridge
`isLocallyConstant_of_cbRank_le_one`, the finite-image gluing equivalence
`finite_image_mem_finGl`, the generator membership `generator_mem_finGl`, and
`ℓ₁ ≡ id_ℕ`, `maxFun_one_equiv_id`), and the structural assembly
(`cLeOne_finitely_generated`, `infinite_image_mem_finGl`) is proved from them. -/

/-- `1 < ω₁` (since `ω = ℵ₀.ord ≤ ℵ₁.ord = ω₁`). -/
lemma one_lt_omega1 : (1 : Ordinal.{0}) < omega1 := by
  have h : Ordinal.omega0 ≤ omega1 := by
    have := Cardinal.ord_le_ord.mpr (Cardinal.aleph0_le_aleph 1)
    rwa [Cardinal.ord_aleph0] at this
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 h

/-- `0 < ω₁`. -/
lemma zero_lt_omega1 : (0 : Ordinal.{0}) < omega1 :=
  lt_trans zero_lt_one one_lt_omega1

/-- The two generators of `𝒞_{≤1}`: `k₁ = minFun 0` (a single point) and
`ℓ₁ = maxFun 1` (`≡ id_ℕ`). -/
noncomputable def genLeOne : Fin 2 → ScatFun :=
  ![ScatFun.minFun 0 zero_lt_omega1, ScatFun.maxFun 1 one_lt_omega1]

/-- **Gap 1 — rank ↔ locally constant.**  A scattered continuous function of CB-rank
`≤ 1` is locally constant.  `CBLevel f 1 = univ \ isolatedLocus f univ`; rank `≤ 1`
plus scatteredness forces `CBLevel f 1 = ∅` (via `CBLevel_eq_empty_at_rank` +
`CBLevel_antitone`), i.e. `isolatedLocus f univ = univ`, which says every point has an
open neighbourhood on which `f` is constant — exactly local constancy. -/
lemma isLocallyConstant_of_cbRank_le_one (F : ScatFun) (h : CBRank F.func ≤ 1) :
    IsLocallyConstant F.func := by
  -- `CBLevel f 1 = ∅`: it sits below `CBLevel f (CBRank f) = ∅` (antitone, `CBRank ≤ 1`).
  have hempty : CBLevel F.func 1 = ∅ :=
    Set.subset_empty_iff.mp
      (CBLevel_eq_empty_at_rank F.func F.hScat ▸ CBLevel_antitone F.func h)
  -- `CBLevel f 1 = univ \ isolatedLocus f univ`.
  have hone : CBLevel F.func 1 = univ \ isolatedLocus F.func univ := by
    rw [show (1 : Ordinal) = Order.succ 0 from by rw [← Ordinal.add_one_eq_succ, zero_add],
      CBLevel_succ', CBLevel_zero]
  rw [hone, Set.diff_eq_empty] at hempty
  have hiso : isolatedLocus F.func univ = univ := Set.eq_univ_of_univ_subset hempty
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  have hx : x ∈ isolatedLocus F.func univ := by rw [hiso]; trivial
  obtain ⟨_, U, hU, hxU, hconst⟩ := hx
  exact ⟨U, hU, hxU, fun y hy => hconst y ⟨hy, Set.mem_univ y⟩⟩

/-- The copies-list of the one-hot multiplicity `1` at `i` (and `0` elsewhere) is the
singleton `[B i]`: only block `i` contributes, with one copy.  (`finRange m` is
nodup, so the single `replicate 1 (B i)` is surrounded by empty `replicate 0`s.) -/
lemma copiesList_indicator {m : ℕ} (B : Fin m → ScatFun) (i : Fin m) :
    ScatFun.copiesList B (fun j => if j = i then 1 else 0) = [B i] := by
  have key : ∀ (l : List (Fin m)), l.Nodup →
      (l.flatMap (fun j => List.replicate (if j = i then 1 else 0) (B j)))
        = (if i ∈ l then [B i] else []) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, ih (List.Nodup.of_cons hl)]
      rcases eq_or_ne a i with rfl | ha
      · have hi : a ∉ l := (List.nodup_cons.mp hl).1
        simp [hi]
      · simp [List.mem_cons, ha, Ne.symm ha]
  simp only [ScatFun.copiesList]
  rw [key (List.finRange m) (List.nodup_finRange m)]
  simp [List.mem_finRange]

/-- Each generator of a finite family lies in its own `FinGl` class (one copy of it).
Generalises `single_mem_finGl` from a one-element family: take the one-hot
multiplicity `1` at `i`, for which `Gl B · = gl` of a single nonempty block `B i`. -/
lemma generator_mem_finGl {m : ℕ} (B : Fin m → ScatFun) (i : Fin m) :
    B i ∈ ScatFun.FinGl B := by
  have hcl : ScatFun.copiesList B (fun j => if j = i then 1 else 0) = [B i] :=
    copiesList_indicator B i
  have hF0 : ScatFun.copiesSeq B (fun j => if j = i then 1 else 0) 0 = B i := by
    simp [ScatFun.copiesSeq, hcl]
  have hemp : ∀ k, k ≠ 0 →
      IsEmpty ↥(ScatFun.copiesSeq B (fun j => if j = i then 1 else 0) k).domain := by
    intro k hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcs : ScatFun.copiesSeq B (fun j => if j = i then 1 else 0) k = ScatFun.empty := by
      simp only [ScatFun.copiesSeq, hcl]
      rw [List.getD_eq_default]; simpa using hk1
    rw [hcs]; exact ⟨fun x => Set.notMem_empty x.1 x.2⟩
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · have hred := gl_single_le (ScatFun.copiesSeq B (fun j => if j = i then 1 else 0)) hemp
    rw [hF0] at hred
    exact hred
  · exact block_reduces_Gl B (fun j => if j = i then 1 else 0) i (by simp)

/-- `ℓ₁ = MaxFun 1` is continuously equivalent to `id_ℕ`: it is locally constant
(rank `1`, via the bridge) with infinite image (`MaxDom 1 = GluingSet (fun _ =>
PointedGluingSet (fun _ => ∅))` contains the infinitely many distinct points
`prepend i 0^ω`), so `locally_constant_infinite_image` applies. -/
lemma maxFun_one_equiv_id : ContinuouslyEquiv (MaxFun 1) (@id ℕ) := by
  have hlc : IsLocallyConstant (MaxFun 1) :=
    isLocallyConstant_of_cbRank_le_one (ScatFun.maxFun 1 one_lt_omega1)
      (le_of_eq (maxFun_cbRank_eq 1 one_lt_omega1))
  have hinf : (Set.range (MaxFun 1)).Infinite := by
    have hrange : Set.range (MaxFun 1) = MaxDom 1 := Subtype.range_val
    rw [hrange, show (1 : Ordinal) = Order.succ 0 from by rw [← Ordinal.add_one_eq_succ, zero_add],
      MaxDom_succ]
    apply Set.infinite_of_injective_forall_mem (f := fun i : ℕ => prepend i zeroStream)
    · intro i j hij
      have := congrFun hij 0
      simpa [prepend] using this
    · intro i
      exact mem_gluingSet_prepend (zeroStream_mem_pointedGluingSet _)
  exact locally_constant_infinite_image hlc hinf

/-
`k₁ = minFun 0` has domain the singleton `{0^ω}`.
-/
lemma minFun_zero_domain :
    (ScatFun.minFun 0 zero_lt_omega1).domain = {zeroStream} := by
  have h_minFun_zero : (ScatFun.minFun 0 zero_lt_omega1).domain = PointedGluingSet (fun _ => ∅) := by
    convert MinDom_zero;
  simp_all +decide [ PointedGluingSet ]

/-
The block sequence of the `N`-fold gluing `Gl genLeOne ![N,0]` consists of `N`
copies of `k₁ = minFun 0`, padded by the empty function.
-/
lemma copiesSeq_genLeOne_eq (N i : ℕ) :
    ScatFun.copiesSeq genLeOne ![N, 0] i
      = if i < N then ScatFun.minFun 0 zero_lt_omega1 else ScatFun.empty := by
  unfold ScatFun.copiesSeq;
  unfold ScatFun.copiesList genLeOne;
  simp +decide only [List.flatMap, List.finRange, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one, List.ofFn_zero, List.map_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, List.replicate_zero, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.getD_eq_getElem?_getD];
  grind

/-
For `i < N`, the point `(i)⌢0^ω` belongs to the domain of `Gl genLeOne ![N,0]`.
-/
lemma prepend_zeroStream_mem_Gl (N i : ℕ) (hi : i < N) :
    prepend i zeroStream ∈ (ScatFun.Gl genLeOne ![N, 0]).domain := by
  apply mem_gluingSet_prepend; simp [genLeOne];
  convert minFun_zero_domain.symm.subset _;
  · convert copiesSeq_genLeOne_eq N i using 1;
    rw [ if_pos hi ];
  · exact Set.mem_singleton _

/-
The gluing `Gl genLeOne ![N,0]` fixes the point `(i)⌢0^ω` (`i < N`).
-/
lemma Gl_genLeOne_func_prepend (N i : ℕ) (hi : i < N)
    (h : prepend i zeroStream ∈ (ScatFun.Gl genLeOne ![N, 0]).domain) :
    (ScatFun.Gl genLeOne ![N, 0]).func ⟨prepend i zeroStream, h⟩ = prepend i zeroStream := by
  have h_minFun : (ScatFun.minFun 0 zero_lt_omega1).func = Subtype.val := rfl
  convert GluingFunVal_prepend ( fun j => ( ScatFun.copiesSeq genLeOne ![N, 0] j ).domain ) ( fun j => Set.univ ) ( fun j a => ⟨ ( ScatFun.copiesSeq genLeOne ![N, 0] j ).func a, Set.mem_univ _ ⟩ ) i ⟨ zeroStream, _ ⟩ _ using 1;
  convert rfl;
  convert congr_fun h_minFun ⟨ zeroStream, _ ⟩;
  · exact copiesSeq_genLeOne_eq N i ▸ if_pos hi;
  · exact minFun_zero_domain.symm.subset rfl;
  · convert Set.mem_singleton zeroStream;
    convert minFun_zero_domain;
    exact copiesSeq_genLeOne_eq N i ▸ if_pos hi

/-
Every point `x` of `Gl genLeOne ![N,0]` has first coordinate `< N`, equals
`(x₀)⌢0^ω`, and is fixed by the gluing function.
-/
lemma Gl_genLeOne_func_eq (N : ℕ) (x : ↥(ScatFun.Gl genLeOne ![N, 0]).domain) :
    x.val 0 < N ∧ x.val = prepend (x.val 0) zeroStream ∧
      (ScatFun.Gl genLeOne ![N, 0]).func x = prepend (x.val 0) zeroStream := by
  obtain ⟨i, hi⟩ : ∃ i, x.val 0 = i ∧ (unprepend x.val) ∈ (ScatFun.copiesSeq genLeOne ![N, 0] i).domain := by
    convert GluingSet_inverse_short ( fun j => ( ScatFun.copiesSeq genLeOne ![ N, 0 ] j |> ScatFun.domain ) ) x using 1;
  by_cases hiN : i < N <;> simp_all +decide [ ScatFun.copiesSeq ];
  · have h_unprepend : unprepend x.val = zeroStream := by
      simp_all +decide [ ScatFun.copiesList ];
      simp_all +decide [ List.finRange, List.flatMap ];
      exact minFun_zero_domain.subset hi.2;
    grind +suggestions;
  · have h_empty_domain : (ScatFun.empty : ScatFun).domain = ∅ := rfl
    cases i <;> simp_all +decide [ ScatFun.copiesList ];
    cases ‹ℕ› <;> simp_all +decide [ List.finRange ]

/-
**Forward reduction for the finite-image case.**  Given an index function
`idxF` (the locally-constant labelling of the fibres of `F` by `Fin N`) with a
section `valF`, `F` reduces to the `N`-fold gluing of the one-point generator.
-/
lemma reduces_glCopies_of_enum (F : ScatFun) (N : ℕ)
    (idxF : ↥F.domain → Fin N) (hidx : Continuous idxF)
    (valF : Fin N → Baire) (hsec : ∀ x, valF (idxF x) = F.func x) :
    ScatFun.Reduces F (ScatFun.Gl genLeOne ![N, 0]) := by
  -- Define the continuous map σ : F.domain → (ScatFun.Gl genLeOne ![N, 0]).domain by σ x = ⟨prepend (idxF x) zeroStream, prepend_zeroStream_mem_Gl N (idxF x).val (idxF x).isLt⟩.
  set σ : F.domain → (ScatFun.Gl genLeOne ![N, 0]).domain := fun x => ⟨prepend (idxF x).val zeroStream, prepend_zeroStream_mem_Gl N (idxF x).val (idxF x).isLt⟩;
  refine ⟨ σ, ?_, ?_ ⟩;
  · refine Continuous.subtype_mk ?_ ?_;
    convert ( continuous_of_discreteTopology ( f := fun x : Fin N => prepend x.val zeroStream ) ) |> Continuous.comp <| hidx using 1;
  · refine ⟨ fun y => if h : y 0 < N then valF ⟨ y 0, h ⟩ else zeroStream, ?_, ?_ ⟩;
    · refine Continuous.continuousOn ?_;
      convert continuous_of_discreteTopology.comp ( continuous_apply 0 ) using 1;
      rotate_right;
      exact fun n => if h : n < N then valF ⟨ n, h ⟩ else zeroStream;
      · exact funext fun x => by simp +decide [ Function.comp ] ;
      · infer_instance;
    · intro x; specialize hsec x; simp_all +decide;
      rw [ ← hsec, Gl_genLeOne_func_prepend ];
      · unfold prepend; aesop;
      · exact Fin.is_lt _

/-
**Backward reduction for the finite-image case.**  Given an injective value
function `valF` and representatives `rep` of each fibre, the `N`-fold gluing of
the one-point generator reduces to `F`.
-/
lemma glCopies_reduces_of_enum (F : ScatFun) (N : ℕ)
    (valF : Fin N → Baire) (hvalinj : Function.Injective valF)
    (rep : Fin N → ↥F.domain) (hrep : ∀ k, F.func (rep k) = valF k) :
    ScatFun.Reduces (ScatFun.Gl genLeOne ![N, 0]) F := by
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => rep ⟨ x.val 0, by linarith [ Gl_genLeOne_func_eq N x ] ⟩;
  · refine continuous_of_discreteTopology.comp ?_;
    -- The function `x => ⟨x.val 0, by linarith [Gl_genLeOne_func_eq N x]⟩` is locally constant because it depends only on the first coordinate of `x`.
    have h_locally_const : IsLocallyConstant (fun x : ↥(ScatFun.Gl genLeOne ![N, 0]).domain => x.val 0) := by
      intro x;
      refine ⟨ ?_, ?_, ?_ ⟩;
      exact { w : Baire | w 0 ∈ x };
      · exact isOpen_iff_mem_nhds.mpr fun w hw => by exact Filter.mem_of_superset ( IsOpen.mem_nhds ( isOpen_discrete { w 0 } |> IsOpen.preimage ( continuous_apply 0 ) ) ( by aesop ) ) fun y hy => by aesop;
      · rfl;
    convert h_locally_const.continuous using 1;
    rw [ continuous_iff_continuousAt ];
    simp +decide only [ContinuousAt, nhds_discrete, Filter.tendsto_pure, Fin.mk.injEq, Subtype.forall];
    rw [ continuous_iff_continuousAt ];
    simp +decide [ ContinuousAt ];
  · refine ⟨ fun w => if h : ∃ k : Fin N, valF k = w then prepend ( h.choose : ℕ ) zeroStream else zeroStream, ?_, ?_ ⟩;
    · refine' Set.Finite.continuousOn _ _;
      exact Set.Finite.subset ( Set.toFinite ( Set.range valF ) ) ( Set.range_subset_iff.mpr fun x => by aesop );
    · intro x;
      convert Gl_genLeOne_func_eq N x |>.2.2 using 1;
      simp +decide only [hrep, exists_apply_eq_apply, ↓reduceDIte];
      grind +suggestions

/-- **Gap 2 — finite image → gluing.**  A (continuous) scattered function with finite
image is `≡` to a finite gluing of copies of the point `k₁`, hence lies in
`FinGl ![k₁, ℓ₁]`.

Local constancy is not needed as a separate hypothesis here: a continuous map into
the finite (hence discrete) subspace `range F.func` is automatically locally
constant. -/
lemma finite_image_mem_finGl (F : ScatFun)
    (hfin : (Set.range F.func).Finite) :
    F ∈ ScatFun.FinGl genLeOne := by
  classical
  have : Finite ↥(Set.range F.func) := hfin
  set N := Nat.card ↥(Set.range F.func) with hN
  let e : ↥(Set.range F.func) ≃ Fin N := Finite.equivFin _
  let idxF : ↥F.domain → Fin N := fun x => e ⟨F.func x, Set.mem_range_self x⟩
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
    rw [show (⟨F.func v, Set.mem_range_self v⟩ : ↥(Set.range F.func)) = e.symm k from
      Subtype.ext hv, e.apply_symm_apply]
  let rep : Fin N → ↥F.domain := fun k => (hsurj k).choose
  have hrep : ∀ k, F.func (rep k) = valF k := by
    intro k
    have h1 : idxF (rep k) = k := (hsurj k).choose_spec
    rw [← hsec (rep k), h1]
  exact ⟨![N, 0],
    glCopies_reduces_of_enum F N valF hvalinj rep hrep,
    reduces_glCopies_of_enum F N idxF hidx valF hsec⟩

/-- **Infinite-image branch (proved).**  A locally constant function with infinite
image is `≡ id_ℕ ≡ ℓ₁`, hence lies in `FinGl ![k₁, ℓ₁]`.  Assembled from
`locally_constant_infinite_image`, `maxFun_one_equiv_id`, `generator_mem_finGl`
(`ℓ₁ ∈ FinGl`) and `finGl_closed_equiv`. -/
lemma infinite_image_mem_finGl (F : ScatFun) (hlc : IsLocallyConstant F.func)
    (hinf : (Set.range F.func).Infinite) :
    F ∈ ScatFun.FinGl genLeOne := by
  have hFid : ContinuouslyEquiv F.func (@id ℕ) := locally_constant_infinite_image hlc hinf
  have hFmax : ContinuouslyEquiv F.func (MaxFun 1) := hFid.trans maxFun_one_equiv_id.symm
  -- `ℓ₁ = genLeOne 1 ∈ FinGl genLeOne`, and `F ≡ ℓ₁`, so `F ∈ FinGl genLeOne`.
  exact finGl_closed_equiv genLeOne (generator_mem_finGl genLeOne 1) ⟨hFmax.2, hFmax.1⟩

/-- **Base case of finite generation (`LocallyConstantFunctions`).**  Every scattered
continuous function of CB-rank in `[0, 1]` lies in `FinGl ![k₁, ℓ₁]`.  Case split on
whether the image is finite (`finite_image_mem_finGl`) or infinite
(`infinite_image_mem_finGl`); local constancy comes from
`isLocallyConstant_of_cbRank_le_one`. -/
theorem cLeOne_finitely_generated :
    ScatFun.LevelInter 0 1 ⊆ ScatFun.FinGl genLeOne := by
  intro F hF
  have hlc : IsLocallyConstant F.func := isLocallyConstant_of_cbRank_le_one F hF.2
  rcases Set.finite_or_infinite (Set.range F.func) with hfin | hinf
  · exact finite_image_mem_finGl F hfin
  · exact infinite_image_mem_finGl F hlc hinf

end