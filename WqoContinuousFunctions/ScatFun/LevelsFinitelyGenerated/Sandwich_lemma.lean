import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LevelsFinitelyGenerated
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.GlList

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# The sandwich lemma for finite gluing membership

`finGl_sandwich`, split out of `LambdaPlusOne.lean` since it is reused (with its supporting
`FinGl`/`glList` gluing lemmas) by both `LambdaPlusOne.lean` (`λ+1` case, `λ` a non-zero limit)
and `Two.lean` (`λ = 1` case).
-/

namespace ScatFun

/-- **A finitely-supported plain gluing is equivalent to the `glList` of its support.**  The
gluing `gl (fun n => if n ∈ I then g n else empty)` is continuously equivalent to
`glList (I.toList.map g)`.  (Same reindexing argument as in `finGl_gl_ite_of_forall_mem`.) -/
lemma gl_ite_equiv_glList_map (I : Finset ℕ) (g : ℕ → ScatFun) :
    Equiv (gl (fun n => if n ∈ I then g n else empty)) (glList (I.toList.map g)) := by
  refine ⟨?_, ?_⟩
  · convert gl_reindex _ _ _;
    rotate_left;
    use fun n => if h : n ∈ I then List.idxOf n I.toList else I.card + n;
    · intro n m hnm; by_cases hn : n ∈ I <;> by_cases hm : m ∈ I <;> simp_all +decide [ List.idxOf_inj ] ;
      · grind [List.idxOf_eq_length_iff, Finset.length_toList, Finset.mem_toList,
          List.idxOf_lt_length_iff];
      · linarith [ List.idxOf_lt_length_iff.mpr ( show m ∈ I.toList from by simpa using hm ), show List.length I.toList = I.card from by simp +decide ];
    · split_ifs <;> simp_all +decide ;
  · obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, Function.Injective e ∧ ∀ k, (fun n => if n ∈ I then g n else empty) (e k) = (I.toList.map g).getD k empty := by
      obtain ⟨eC, heC⟩ : ∃ eC : ℕ → ℕ, Function.Injective eC ∧ ∀ k, eC k ∉ I := by
        have h_compl : Set.Infinite {n : ℕ | n ∉ I} := by
          exact Set.infinite_of_finite_compl ( I.finite_toSet.subset fun x hx => by simpa using hx );
        exact ⟨ fun k => Nat.nth ( fun n => n ∉ I ) k, Nat.nth_injective h_compl, fun k => Nat.nth_mem_of_infinite h_compl _ ⟩;
      use fun k => if h : k < I.card then I.toList.get ⟨k, by simpa using h⟩ else eC (k - I.card);
      refine ⟨ ?_, ?_ ⟩;
      · intro k l hkl;
        by_cases hk : k < I.card <;> by_cases hl : l < I.card <;> simp_all +decide [ heC.1.eq_iff ];
        · have := List.nodup_iff_injective_get.mp ( Finset.nodup_toList I ) hkl; aesop;
        · exact False.elim <| heC.2 _ <| hkl ▸ Finset.mem_toList.mp ( List.getElem_mem _ );
        · exact False.elim <| heC.2 _ <| hkl.symm ▸ Finset.mem_toList.mp ( List.getElem_mem _ );
        · omega;
      · intro k; by_cases hk : k < I.card <;> simp +decide [ hk, heC.2 ] ;
        exact fun h => False.elim <| h <| Finset.mem_toList.mp <| by simp;
    convert gl_reindex _ _ he.1 using 1;
    unfold glList; aesop;

/-- **A finite-support plain gluing of `FinGl S` members lies in `FinGl S`.**  The `FinGl`-valued
analogue of `finGl_gl_ite_of_forall_mem`. -/
lemma finGl_gl_ite_of_forall_finGl {S : Finset ScatFun} (I : Finset ℕ) (g : ℕ → ScatFun)
    (hg : ∀ i ∈ I, g i ∈ FinGl S.toFinFun) :
    gl (fun n => if n ∈ I then g n else empty) ∈ FinGl S.toFinFun := by
  have hlist : glList (I.toList.map g) ∈ FinGl S.toFinFun := by
    refine finGl_glList_of_forall_finGl (fun w hw => ?_)
    rcases List.mem_map.mp hw with ⟨i, hi, rfl⟩
    exact hg i (Finset.mem_toList.mp hi)
  obtain ⟨L, hL, hEq⟩ := exists_glList_of_finGl hlist
  exact finGl_of_equiv_glList hL ((gl_ite_equiv_glList_map I g).trans hEq)

/-- **Finite fibre-family assembly (the "sandwich lemma").**  If `(D n)` is an `F`-domain partition
supported on the finite set `I`, `(U i)` are pairwise-disjoint clopen codomain sets, and for each
`i ∈ I` a function `g i` sandwiched `F.restrict (D i) ≤ g i ≤ F.coRestrict (U i)` with
`g i ∈ FinGl S.toFinFun`, then `F ∈ FinGl S.toFinFun`.

Note: `hgen` asks for `g i ∈ FinGl S.toFinFun` rather than the literal `g i ∈ S` (as an earlier
draft of this lemma had it) — the natural `g i`'s at the call sites (e.g. `succMaxFun`, the wedge
generator) are only *equivalent* to, not literally equal to, some element of `S`, so literal
membership is unsatisfiable in practice. `FinGl`-membership is what both callers actually have on
hand (`succMaxFun_one_mem_finGl_two`, `wedge_maxFun_minFun_one_mem_finGl_two` in `Two.lean`;
`succMaxFun_mem_Generators_add_one`, `wedge_maxFun_minFun_mem_Generators_add_one` in
`LambdaPlusOne.lean`). -/
lemma finGl_sandwich {S : Finset ScatFun} (F : ScatFun) (I : Finset ℕ)
    (D : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion D) (hDempty : ∀ n, n ∉ I → D n = ∅)
    (U : ℕ → Set Baire) (hUcl : ∀ i, IsClopen (U i)) (hUdisj : Pairwise (Disjoint on U))
    (g : ℕ → ScatFun)
    (hup : ∀ i ∈ I, Reduces (F.restrict (D i)) (g i))
    (hlow : ∀ i ∈ I, Reduces (g i) (F.coRestrict (U i)))
    (hgen : ∀ i ∈ I, g i ∈ FinGl S.toFinFun) :
    F ∈ FinGl S.toFinFun := by
  set G : ℕ → ScatFun := fun n => if n ∈ I then g n else empty with hG
  -- `F` is equivalent to the finitely-supported plain gluing `gl G`.
  have hfwd : Reduces F (gl G) := by
    refine (scatFun_reduces_gl_of_domain_partition F D hdu).trans
      (gl_reduces_of_pointwise _ _ (fun n => ?_))
    by_cases hn : n ∈ I
    · simpa only [hG, if_pos hn] using hup n hn
    · have hempty : IsEmpty ↑(F.restrict (D n)).domain := by
        rw [Set.isEmpty_coe_sort]
        simp [ScatFun.restrict, hDempty n hn]
      exact reduces_of_isEmpty_domain hempty
  have hbwd : Reduces (gl G) F := by
    refine (gl_reduces_of_pointwise _ _ (fun n => ?_)).trans
      (gl_coRestrict_disjoint_open_reduces F U (fun k => (hUcl k).isOpen) hUdisj)
    by_cases hn : n ∈ I
    · simpa only [hG, if_pos hn] using hlow n hn
    · simpa only [hG, if_neg hn] using empty_reduces (F.coRestrict (U n))
  have hmem : gl G ∈ FinGl S.toFinFun := finGl_gl_ite_of_forall_finGl I g hgen
  obtain ⟨L, hL, hEq⟩ := exists_glList_of_finGl hmem
  have hFG : Equiv F (gl G) := ⟨hfwd, hbwd⟩
  exact finGl_of_equiv_glList hL (hFG.trans hEq)

end ScatFun
