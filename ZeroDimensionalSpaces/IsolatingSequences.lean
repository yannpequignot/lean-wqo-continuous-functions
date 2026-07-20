import ZeroDimensionalSpaces.Basics
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.Cofinite

/-!
# Isolating points among an injective sequence in Baire space

Kept out of `ZeroDimensionalSpaces/Basics.lean` (foundational, widely imported): this is a
narrow, self-contained topic — given an injective `y : ℕ → Baire`, either a finite prefix
isolates a point `y i` from the rest, or it stays an accumulation point forever, and (given a
"cofinite in every neighborhood" convergence fact) an actual convergent reindexing can be built
via `Nat.nth`. Currently only used by `case_N1_finite_nonempty_subcase_b_two`
(`WqoContinuousFunctions/ScatFun/LevelsFinitelyGenerated/Two.lean`) and its planned
`lambda_plus_one` generalization. Import this file only where actually needed.

## Main results

* `isolating_or_always_infinite` — the basic dichotomy for a single point `y i`.
* `exists_uniform_isolating_or_infinite_clopen` — a uniform level `K` working for a whole
  finite index set at once, with pairwise disjoint `nbhd`s.
* `exists_reindexing_of_cofinite_convergent` — builds a genuine convergent enumeration `nSeq` of
  an infinite `S : Set ℕ` (via `Nat.nth`) from a cofinite-convergence hypothesis.
-/

open Set Function

set_option autoImplicit false

/-- Basic neighborhoods shrink as the prefix length grows. -/
lemma nbhd_antitone {x : Baire} {k K : ℕ} (hkK : k ≤ K) :
    nbhd x K ⊆ nbhd x k := by
  intro h hh
  simp only [nbhd, Set.mem_setOf_eq] at hh ⊢
  exact fun j hj => hh j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hkK))

/-- Two points of Baire space differing at some coordinate `< K` have disjoint `nbhd`s of
level `K`. -/
lemma nbhd_disjoint_of_ne {x z : Baire} {d K : ℕ} (hd : d < K) (hxz : x d ≠ z d) :
    Disjoint (nbhd x K) (nbhd z K) := by
  rw [Set.disjoint_left]
  intro h hx hz
  simp only [nbhd, Set.mem_setOf_eq] at hx hz
  exact hxz ((hx d (Finset.mem_range.mpr hd)).symm.trans (hz d (Finset.mem_range.mpr hd)))

/-- Once a `nbhd`-fibre of an injective sequence has shrunk to exactly `{i}`, it stays `{i}`
at every larger level. -/
lemma isolating_persists {y : ℕ → Baire} {i k K : ℕ} (hkK : k ≤ K)
    (hk : {n | y n ∈ nbhd (y i) k} = {i}) :
    {n | y n ∈ nbhd (y i) K} = {i} := by
  apply subset_antisymm
  · intro n hn
    have hn' : n ∈ {n | y n ∈ nbhd (y i) k} := nbhd_antitone hkK hn
    rwa [hk] at hn'
  · intro n hn
    rw [Set.mem_singleton_iff] at hn
    subst hn
    exact fun j _ => rfl

/-- For an injective sequence `y : ℕ → Baire` and a point `y i`, either some finite prefix
length isolates `i` among all `n` with `y n` in that neighborhood, or every prefix length still
catches infinitely many `n`. -/
lemma isolating_or_always_infinite (y : ℕ → Baire) (hy_inj : Function.Injective y)
    (i : ℕ) :
    (∃ K, {n | y n ∈ nbhd (y i) K} = {i}) ∨
    (∀ K, {n | y n ∈ nbhd (y i) K}.Infinite) := by
  by_cases hfin : ∃ k, {n | y n ∈ nbhd (y i) k}.Finite
  · obtain ⟨k, hk⟩ := hfin
    left
    have hp : ∀ n, n ∈ hk.toFinset.erase i → ∃ c, y n c ≠ y i c := fun n hn =>
      Function.ne_iff.mp (hy_inj.ne (Finset.ne_of_mem_erase hn))
    choose! c hc using hp
    refine ⟨max k ((hk.toFinset.erase i).sup c + 1), ?_⟩
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hn
      by_contra hne
      have hnk : n ∈ hk.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact nbhd_antitone (le_max_left k _) hn
      have hnD : n ∈ hk.toFinset.erase i := Finset.mem_erase.mpr ⟨hne, hnk⟩
      have hcK : c n < max k ((hk.toFinset.erase i).sup c + 1) := by
        have h1 := Finset.le_sup (f := c) hnD
        have h2 : (hk.toFinset.erase i).sup c + 1 ≤ max k ((hk.toFinset.erase i).sup c + 1) :=
          le_max_right _ _
        omega
      have heq : y n (c n) = y i (c n) := by
        simp only [nbhd, Set.mem_setOf_eq] at hn
        exact hn (c n) (Finset.mem_range.mpr hcK)
      exact hc n hnD heq
    · intro hn
      subst hn
      exact fun j _ => rfl
  · exact Or.inr (by push_neg at hfin; exact hfin)

/-- Given finitely many indices `I` with `y` injective, there is a single level `K` such that
each `nbhd (y i) K` (`i ∈ I`) either isolates `y i` from every other `y n` or still catches
infinitely many `y n`'s, and distinct `i, j ∈ I` get disjoint `nbhd`s. -/
lemma exists_uniform_isolating_or_infinite_clopen
    (y : ℕ → Baire) (hy_inj : Function.Injective y) (I : Finset ℕ) :
    ∃ K : ℕ,
      (∀ i ∈ I, {n | y n ∈ nbhd (y i) K} = {i} ∨
        ∀ K', {n | y n ∈ nbhd (y i) K'}.Infinite) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (nbhd (y i) K) (nbhd (y j) K)) := by
  have hex : ∀ i : ℕ, ∃ Ki : ℕ, {n | y n ∈ nbhd (y i) Ki} = {i} ∨
      ∀ K, {n | y n ∈ nbhd (y i) K}.Infinite := by
    intro i
    rcases isolating_or_always_infinite y hy_inj i with h | h
    · obtain ⟨K, hK⟩ := h; exact ⟨K, Or.inl hK⟩
    · exact ⟨0, Or.inr h⟩
  choose Ki hKi using hex
  obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ d < N, y i d ≠ y j d := by
    have h_sep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ d, y i d ≠ y j d := fun i _ j _ hij =>
      Function.ne_iff.mp (hy_inj.ne hij)
    choose! d hd using h_sep
    exact ⟨(I ×ˢ I).sup (fun p => d p.1 p.2) + 1, fun i hi j hj hij =>
      ⟨d i j, Nat.lt_succ_of_le (Finset.le_sup (f := fun p => d p.1 p.2)
        (Finset.mk_mem_product hi hj)), hd i hi j hj hij⟩⟩
  refine ⟨max (I.sup Ki) N, ?_, ?_⟩
  · intro i hi
    rcases hKi i with h | h
    · exact Or.inl (isolating_persists
        ((Finset.le_sup (f := Ki) hi).trans (le_max_left _ _)) h)
    · exact Or.inr h
  · intro i hi j hj hij
    obtain ⟨d, hdN, hd⟩ := hN i hi j hj hij
    exact nbhd_disjoint_of_ne (hdN.trans_le (le_max_right _ _)) hd

/-- Given a point `y i₀` and a set `S : Set ℕ` not containing `i₀`, infinite, such that the
family `(y n)_{n ∈ S}` converges to `y i₀` in the "cofinite in every neighborhood" sense
(`hSconv`), build the reindexing `nSeq : ℕ → ℕ` with `nSeq 0 = i₀`, injective, `nSeq (m+1) ∈ S`
for all `m` with `Set.range (fun m => nSeq (m+1)) = S` (an actual *enumeration* of `S`, not just
a subsequence landing in it), and `y ∘ (nSeq ∘ Nat.succ)` genuinely tending to `y i₀`. -/
lemma exists_reindexing_of_cofinite_convergent (y : ℕ → Baire) (i₀ : ℕ) (S : Set ℕ)
    (hi₀S : i₀ ∉ S) (hSinf : S.Infinite)
    (hSconv : ∀ V : Set Baire, IsClopen V → y i₀ ∈ V → {n | n ∈ S ∧ y n ∉ V}.Finite) :
    ∃ nSeq : ℕ → ℕ, nSeq 0 = i₀ ∧ Function.Injective nSeq ∧ (∀ m, nSeq (m + 1) ∈ S) ∧
      Set.range (fun m => nSeq (m + 1)) = S ∧
      Filter.Tendsto (fun m => y (nSeq (m + 1))) Filter.atTop (nhds (y i₀)) := by
  set e : ℕ → ℕ := Nat.nth (fun n => n ∈ S) with hedef
  have he_mem : ∀ m, e m ∈ S := fun m => Nat.nth_mem_of_infinite hSinf m
  have he_inj : Function.Injective e := Nat.nth_injective hSinf
  have he_range : Set.range e = S := Nat.range_nth_of_infinite hSinf
  set nSeq : ℕ → ℕ := fun m => Nat.casesOn m i₀ e with hnSeqdef
  refine ⟨nSeq, rfl, ?_, fun m => he_mem m, he_range, ?_⟩
  · intro a b hab
    rcases a with _ | k <;> rcases b with _ | l
    · rfl
    · exfalso
      have heq : e l = i₀ := hab.symm
      exact hi₀S (heq ▸ he_mem l)
    · exfalso
      have heq : e k = i₀ := hab
      exact hi₀S (heq ▸ he_mem k)
    · exact congrArg (· + 1) (he_inj hab)
  · rw [tendsto_nhds]
    intro V hVopen hVmem
    obtain ⟨K', hK'⟩ := nbhd_basis (y i₀) V hVopen hVmem
    have hVcl' : IsClopen (nbhd (y i₀) K') := baire_nbhd_isClopen (y i₀) K'
    have hfin : {n | n ∈ S ∧ y n ∉ nbhd (y i₀) K'}.Finite :=
      hSconv (nbhd (y i₀) K') hVcl' (fun j _ => rfl)
    have hfin' : {m : ℕ | y (e m) ∉ nbhd (y i₀) K'}.Finite := by
      apply Set.Finite.subset (hfin.preimage he_inj.injOn)
      intro m hm
      exact ⟨he_mem m, hm⟩
    have hfin'' : {m : ℕ | y (e m) ∉ V}.Finite :=
      hfin'.subset (fun m hm hcontra => hm (hK' hcontra))
    have hev : ∀ᶠ m in Filter.cofinite, y (e m) ∈ V := Filter.eventually_cofinite.mpr hfin''
    rwa [Nat.cofinite_eq_atTop] at hev
