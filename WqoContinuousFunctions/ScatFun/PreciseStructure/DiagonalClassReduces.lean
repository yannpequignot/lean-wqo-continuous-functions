import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalForLambdaPlusOne
import WqoContinuousFunctions.ScatFun.RestrictReindex
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.LimitCase
import ZeroDimensionalSpaces.IsolatingSequences

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Wiring `diagonal_for_lambda_plus_one` onto a reindexed accumulation class

Lam-agnostic wrapper around `diagonal_for_lambda_plus_one`, factored out of
`case_N1_finite_nonempty_subcase_b_two` (`Two.lean`) so that both it (`lam = 1`) and the general
`lam` case (`LambdaPlusOne.lean`'s `case_N1_finite_nonempty_subcase_b`) can share it.

## Context

At `case_N1_finite_nonempty_subcase_b`, `F`'s simple blocks `(F.restrict (A n))` are partitioned,
via a finite index set `I` of "distinguished" blocks (those `≡ succMaxFun`), into classes `P' i`
(`i ∈ I`) that are either exact singletons `{i}` or infinite. For an infinite class with
representative `i` and remaining points `S = P' i \ {i}` (with `(y n)_{n ∈ S}` converging to
`y i`, in the "cofinite in every clopen neighbourhood" sense), this lemma builds the reindexing,
transfers `CBRank`/`CBLevel` facts across the restrict-of-restrict boundary
(`ScatFun.restrict_restrict_transfer`), and invokes `diagonal_for_lambda_plus_one` to conclude
that the whole class (`F.restrict (A i ∪ ⋃ n ∈ S, A n)`) is squeezed against the wedge generator
`⋁(maxFun lam ∣ minFun lam)`.
-/

open ScatFun

/-- **Diagonal wiring for one accumulation class.** See the module docstring for context. Given
an infinite "accumulation class" `{i} ∪ S` (`i` the distinguished representative, `S` the
non-distinguished points converging to `y i`), the class as a whole reduces to the wedge
generator, and the wedge generator reduces down into any clopen neighbourhood `U` of `y i`. -/
lemma diagonal_class_reduces_wedge (lam : Ordinal.{0}) (hlam : lam < omega1)
    (F : ScatFun) (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (hrank : ∀ n, CBRank (F.restrict (A n)).func = lam + 1)
    (hdist : ∀ n, ∀ x ∈ CBLevel (F.restrict (A n)).func lam, (F.restrict (A n)).func x = y n)
    (i : ℕ) (h0 : Equiv (F.restrict (A i)) (succMaxFun lam hlam))
    (S : Set ℕ) (hiS : i ∉ S) (hSinf : S.Infinite)
    (hSclass : ∀ n ∈ S, Reduces (F.restrict (A n)) (minFun lam hlam ⊕ maxFun lam hlam))
    (hSconv : ∀ V : Set Baire, IsClopen V → y i ∈ V → {n | n ∈ S ∧ y n ∉ V}.Finite)
    (U : Set Baire) (hUcl : IsClopen U) (hUmem : y i ∈ U) :
    Reduces (F.restrict (A i ∪ ⋃ n ∈ S, A n))
        (wedge (fun _ : Fin 1 => maxFun lam hlam) (minFun lam hlam)) ∧
    Reduces (wedge (fun _ : Fin 1 => maxFun lam hlam) (minFun lam hlam)) (F.coRestrict U) := by
  obtain ⟨nSeq, hnSeq0, hnSeq_inj, hnSeq_memS, hnSeq_range, hnSeq_conv⟩ :=
    exists_reindexing_of_cofinite_convergent y i S hiS hSinf hSconv
  set D : Set ↑F.domain := ⋃ m, A (nSeq m) with hDdef
  have hD_eq : D = A i ∪ ⋃ n ∈ S, A n := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hx
      rcases m with _ | k
      · rw [hnSeq0] at hxm
        exact Or.inl hxm
      · exact Or.inr (Set.mem_biUnion (hnSeq_memS k) hxm)
    · rintro x (hx | hx)
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        rw [hnSeq0]
        exact hx
      · obtain ⟨n, hnS, hxn⟩ := Set.mem_iUnion₂.mp hx
        have hn' : n ∈ Set.range (fun m => nSeq (m + 1)) := by rw [hnSeq_range]; exact hnS
        obtain ⟨m, hm⟩ := hn'
        dsimp only at hm
        refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
        rw [hm]
        exact hxn
  have hdu' : (F.restrict D).IsDisjointUnion
      (fun m => {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)}) :=
    ScatFun.restrict_iUnion_comp_isDisjointUnion F A hdu nSeq hnSeq_inj
  have htrans : ∀ m, (CBRank ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)}).func
      = CBRank (F.restrict (A (nSeq m))).func) ∧
    (∀ x ∈ CBLevel ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)}).func lam,
      ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)}).func x
        = y (nSeq m)) :=
    fun m => ScatFun.restrict_restrict_transfer F D (A (nSeq m))
      (Set.subset_iUnion (fun m' => A (nSeq m')) m) lam (y (nSeq m)) (hdist (nSeq m))
  have hAiD : A i ⊆ D := by
    rw [hDdef, ← hnSeq0]
    exact Set.subset_iUnion (fun m' => A (nSeq m')) 0
  have h0'' : Equiv ((F.restrict D).restrict
      {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq 0)})
      (succMaxFun lam hlam) := by
    rw [hnSeq0]
    exact (equiv_restrict_restrict_of_subset F D (A i) hAiD).trans h0
  have hpos'' : ∀ m, 0 < m → Reduces
      ((F.restrict D).restrict
        {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)})
      (minFun lam hlam ⊕ maxFun lam hlam) := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hmem : nSeq (k + 1) ∈ S := hnSeq_memS k
    have hsub : A (nSeq (k + 1)) ⊆ D := Set.subset_iUnion (fun m' => A (nSeq m')) (k + 1)
    exact (equiv_restrict_restrict_of_subset F D (A (nSeq (k + 1))) hsub).1.trans
      (hSclass (nSeq (k + 1)) hmem)
  have hconv'' : Filter.Tendsto (fun n => (y ∘ nSeq) (n + 1)) Filter.atTop
      (nhds ((y ∘ nSeq) 0)) := by
    show Filter.Tendsto (fun n => y (nSeq (n + 1))) Filter.atTop (nhds (y (nSeq 0)))
    rw [hnSeq0]
    exact hnSeq_conv
  have hUmem' : (y ∘ nSeq) 0 ∈ U := by
    show y (nSeq 0) ∈ U
    rw [hnSeq0]
    exact hUmem
  have hdiag := diagonal_for_lambda_plus_one (F.restrict D)
      (fun m => {w : ↑(F.restrict D).domain | (F.restrictEquiv D w : ↑F.domain) ∈ A (nSeq m)})
      hdu' lam hlam (y ∘ nSeq) (hy_inj.comp hnSeq_inj)
      (fun m => (htrans m).1.trans (hrank (nSeq m)))
      (fun m => (htrans m).2)
      h0'' hpos'' hconv'' U hUcl hUmem'
  refine ⟨?_, hdiag.2.trans (ScatFun.coRestrict_restrict_reduces F D U)⟩
  rw [← hD_eq]
  exact hdiag.1
