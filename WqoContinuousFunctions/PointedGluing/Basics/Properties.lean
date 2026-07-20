import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers
import WqoContinuousFunctions.PointedGluing.CBRank.Helpers
import WqoContinuousFunctions.PointedGluing.Basics.ContinuousOnTau

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Pointed Gluing — Basic Properties (Fact 3.1, Proposition 3.2, Fact 3.3)

## Main results

* `pointedGluingFun_preserves_continuity` — Fact 3.1: preserves continuity
* `pointedGluingFun_preserves_injectivity` — Fact 3.1: preserves injectivity
* `pointedGluingFun_comm_id` — Fact 3.1: commutes with identity
* `zeroStream_continuity_point` — Fact 3.1: 0^ω is a continuity point
* `CBrank_pointedGluing_regular` — Proposition 3.2: CB rank of regular sequence
* `gluing_le_pointedGluing` — Fact 3.3: ⊔_i f_i ≤ pgl_i f_i
-/

noncomputable section

/-
**Lemma (prop:sufficientcondforcont).**
Let `A` and `B` be metrizable spaces and `f : A → B`.
If `U` is an open subset of `A` such that:
1. `f` is continuous on `U` and on `A \ U`, and
2. for all sequences `(x_n)` in `U` converging to `x ∈ A \ U`, `f(x_n) → f(x)`,
then `f` is continuous.

The proof uses sequential continuity in metrizable spaces. If `x ∈ U`, continuity
follows from `f|_U`. If `x ∉ U`, partition the sequence into `I ∩ U` and `J ∩ Uᶜ`
and handle each part using the respective continuity hypotheses.
-/
theorem sufficient_cond_continuity
    {A B : Type*} [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B]
    (f : A → B) (U : Set A) (hU : IsOpen U)
    (hcont_U : ContinuousOn f U)
    (hcont_compl : ContinuousOn f Uᶜ)
    (hseq : ∀ (x : ℕ → A) (a : A),
      (∀ n, x n ∈ U) → a ∈ Uᶜ → Filter.Tendsto x Filter.atTop (nhds a) →
      Filter.Tendsto (f ∘ x) Filter.atTop (nhds (f a))) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hcont_U.continuousAt (hU.mem_nhds hx)
  · by_contra h_discon
    obtain ⟨V, hV⟩ : ∃ V : Set B, IsOpen V ∧ f x ∈ V ∧ ∀ U' ∈ nhds x, ∃ y ∈ U', f y ∉ V := by
      rw [ContinuousAt] at h_discon
      rw [Filter.tendsto_iff_forall_eventually_mem] at h_discon
      simp +zetaDelta only [mem_compl_iff, not_forall, Filter.not_eventually] at *
      rcases h_discon with ⟨V, hV₁, hV₂⟩
      rcases mem_nhds_iff.mp hV₁ with ⟨W, hW₁, hW₂⟩
      exact ⟨W, hW₂.1, hW₂.2, fun U' hU' => by rcases hV₂.and_eventually hU' with h; obtain ⟨y, hy₁, hy₂⟩ := h.exists; exact ⟨y, hy₂, fun hy₃ => hy₁ <| hW₁ hy₃⟩⟩
    -- Since $x \notin U$, we can consider the set $I = \{n \mid x_n \in U\}$.
    obtain ⟨x_n, hx_n⟩ : ∃ x_n : ℕ → A, Filter.Tendsto x_n Filter.atTop (nhds x) ∧ ∀ n, f (x_n n) ∉ V := by
      have := hV.2.2
      rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U', hU'⟩
      choose y hy using fun n => this (U' n) (hU'.1 n |>.2.mem_nhds (hU'.1 n |>.1))
      exact ⟨y, hU'.2.tendsto fun n => hy n |>.1, fun n => hy n |>.2⟩
    -- Since $x \notin U$, we can consider the set $I = \{n \mid x_n \in U\}$. If $I$ is finite, then $x_n$ is eventually in $U^c$, and we can apply the continuity of $f$ on $U^c$.
    by_cases hI_finite : Set.Finite {n | x_n n ∈ U}
    · -- Since $I$ is finite, there exists some $N$ such that for all $n \geq N$, $x_n \in U^c$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, x_n n ∈ Uᶜ := by
        exact ⟨hI_finite.bddAbove.some + 1, fun n hn => fun h => not_lt_of_ge (hI_finite.bddAbove.choose_spec h) hn⟩
      have h_cont_compl : Filter.Tendsto (fun n => f (x_n n)) Filter.atTop (nhds (f x)) := by
        have := hcont_compl x hx
        exact this.tendsto.comp (Filter.tendsto_inf.mpr ⟨hx_n.1, Filter.tendsto_principal.mpr <| Filter.eventually_atTop.mpr ⟨N, fun n hn => hN n hn⟩⟩)
      exact absurd (h_cont_compl.eventually (hV.1.mem_nhds hV.2.1)) fun h => by obtain ⟨n, hn⟩ := h.and (Filter.eventually_ge_atTop N) |> fun h => h.exists; exact hx_n.2 n hn.1
    · -- Since $I$ is infinite, we can extract a subsequence $(x_{n_k})$ such that $x_{n_k} \in U$ for all $k$.
      obtain ⟨n_k, hn_k⟩ : ∃ n_k : ℕ → ℕ, StrictMono n_k ∧ ∀ k, x_n (n_k k) ∈ U := by
        exact ⟨fun k => Nat.recOn k (Nat.find <| Set.Infinite.nonempty hI_finite) fun k ih => Nat.find <| Set.Infinite.exists_gt hI_finite ih, strictMono_nat_of_lt_succ fun k => Nat.find_spec (Set.Infinite.exists_gt hI_finite _) |>.2, fun k => Nat.recOn k (Nat.find_spec <| Set.Infinite.nonempty hI_finite) fun k ih => Nat.find_spec (Set.Infinite.exists_gt hI_finite _) |>.1⟩
      have h_subseq : Filter.Tendsto (fun k => f (x_n (n_k k))) Filter.atTop (nhds (f x)) := by
        exact hseq _ _ hn_k.2 hx (hx_n.1.comp hn_k.1.tendsto_atTop)
      exact absurd (h_subseq.eventually (hV.1.mem_nhds hV.2.1)) fun h => by obtain ⟨k, hk⟩ := h.exists; exact hx_n.2 (n_k k) hk

lemma strip_mem_of_pointedGluingSet (A : ℕ → Set (ℕ → ℕ))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    stripZerosOne (firstNonzero x.val) x.val ∈ A (firstNonzero x.val) := by
  -- Since x ∈ PointedGluingSet A and x ≠ zeroStream, we can write x as prependZerosOne j a for some j and a ∈ A j.
  obtain ⟨j, a, ha₁, ha₂⟩ : ∃ j, ∃ a ∈ A j, (↑x : ℕ → ℕ) = prependZerosOne j a := by
    unfold PointedGluingSet at x; aesop
  unfold prependZerosOne at ha₂; simp_all +decide [firstNonzero]
  convert ha₁ using 1
  · split_ifs <;> simp_all +decide
    · congr! 1
      rw [Nat.find_eq_iff] ; aesop
    · rename_i h; specialize h j le_rfl; aesop
  · convert stripZerosOne_prependZerosOne j a using 1
    congr! 1
    split_ifs <;> simp_all +decide [Nat.find_eq_iff]
    rename_i h; specialize h j; aesop

/--
On a non-zero element, `PointedGluingFun` equals the block formula.
-/
lemma pointedGluingFun_eq_on_block (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    PointedGluingFun A B f x = prependZerosOne (firstNonzero x.val)
      (f (firstNonzero x.val) ⟨stripZerosOne (firstNonzero x.val) x.val,
        strip_mem_of_pointedGluingSet A x hx⟩).val := by
  unfold PointedGluingFun
  grind

/--
`stripZerosOne i` is continuous as a map `(ℕ → ℕ) → (ℕ → ℕ)`.
-/
lemma continuous_stripZerosOne (i : ℕ) : Continuous (stripZerosOne i) := by
  unfold stripZerosOne
  fun_prop

/--
The block set for index `i` (sequences starting with `i` zeros then a nonzero) is
open in `ℕ → ℕ`.
-/
lemma isOpen_block (i : ℕ) :
    IsOpen {x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0} := by
  convert isOpen_pi_iff.mpr _
  intro f hf
  refine ⟨Finset.range (i + 1), fun k => if k < i then { 0 } else { x | x ≠ 0 }, ?_, ?_⟩ <;> simp_all +decide [Set.subset_def]
  · grind
  · grind

/--
`firstNonzero x = i` when `x` starts with `i` zeros and `x i ≠ 0`.
-/
lemma firstNonzero_eq_of_block (x : ℕ → ℕ) (i : ℕ)
    (h : (∀ k, k < i → x k = 0) ∧ x i ≠ 0) :
    firstNonzero x = i := by
  unfold firstNonzero
  split_ifs <;> simp_all +decide [Nat.find_eq_iff]

/--
For `y` in block `i` of the pointed gluing set, `y.val ≠ zeroStream`.
-/
lemma ne_zeroStream_of_block (y : ℕ → ℕ) (i : ℕ)
    (hy : (∀ k, k < i → y k = 0) ∧ y i ≠ 0) : y ≠ zeroStream := by
  exact fun h => hy.2 <| h ▸ rfl

/--
Strip membership for a specific block index.
-/
lemma strip_mem_of_block (A : ℕ → Set (ℕ → ℕ)) (y : PointedGluingSet A) (i : ℕ)
    (hy : (∀ k, k < i → y.val k = 0) ∧ y.val i ≠ 0) :
    stripZerosOne i y.val ∈ A i := by
  convert strip_mem_of_pointedGluingSet A y _
  · exact Eq.symm (firstNonzero_eq_of_block _ _ hy)
  · exact Eq.symm (firstNonzero_eq_of_block _ _ hy)
  · exact fun h => hy.2 <| h ▸ rfl

/--
The restricted function on block `i` is continuous.
-/
lemma continuous_block_restrict
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (hf : ∀ i, Continuous (f i)) (i : ℕ) :
    Continuous (fun (y : {z : PointedGluingSet A // (∀ k, k < i → z.val k = 0) ∧ z.val i ≠ 0}) =>
      prependZerosOne i
        (f i ⟨stripZerosOne i y.val.val,
          strip_mem_of_block A y.val i y.prop⟩).val) := by
  refine continuous_pi_iff.2 fun j => ?_
  by_cases hj : j < i
  · exact continuous_const.congr fun x => by rw [prependZerosOne, if_pos hj]
  · simp +decide [prependZerosOne, hj]
    by_cases h : j = i <;> simp_all +decide
    · exact continuous_const
    · exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| hf _ |> Continuous.comp <| Continuous.subtype_mk (continuous_stripZerosOne _ |> Continuous.comp <| continuous_subtype_val.comp continuous_subtype_val) _

/--
ContinuousAt of PointedGluingFun at a non-zero point.
-/
lemma continuousAt_pointedGluingFun_nonzero
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (hf : ∀ i, Continuous (f i))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    ContinuousAt (fun y : PointedGluingSet A => PointedGluingFun A B f y) x := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (∀ k : ℕ, k < i → x.val k = 0) ∧ x.val i ≠ 0 := by
    exact ⟨Nat.find (show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h), fun k hk => by_contra fun hk' => Nat.find_min (show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h) hk <| by aesop, Nat.find_spec (show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h)⟩
  have hV : IsOpen {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    exact isOpen_block i |> IsOpen.preimage (continuous_subtype_val)
  have h_cont_restrict : ContinuousOn (fun y : PointedGluingSet A => PointedGluingFun A B f y) {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.congr
      (f := fun y => prependZerosOne i (f i ⟨stripZerosOne i y.val.val,
        strip_mem_of_block A y.val i y.prop⟩).val) ?_ ?_
    · exact continuous_block_restrict A B f hf i
    · intro y; ext; simp [PointedGluingFun]
      rw [if_neg (ne_zeroStream_of_block _ _ y.prop)]
      rw [firstNonzero_eq_of_block _ _ y.2]
      grind
  exact h_cont_restrict.continuousAt (hV.mem_nhds ⟨hi.1, hi.2⟩)

/--
**Fact (BasicsOnPointedGluing) — Part 1.**
The pointed gluing operation preserves continuity: if each `f_i` is continuous, then
`pgl_i f_i` is continuous (as a map between subspaces of the Baire space).
-/
theorem pointedGluingFun_preserves_continuity
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun (x : PointedGluingSet A) =>
      (⟨PointedGluingFun A B f x, by
        unfold PointedGluingFun
        split_ifs <;> simp_all +decide [PointedGluingSet]
        grind⟩ : PointedGluingSet B)) := by
  refine Continuous.subtype_mk ?_ ?_
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.val = zeroStream
  · rw [show x = ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ from Subtype.ext hx]
    -- Use the proof of zeroStream_continuity_point inline
    unfold PointedGluingFun
    refine tendsto_pi_nhds.mpr ?_
    intro n
    simp only [dite_eq_ite, ↓reduceDIte, zeroStream, nhds_discrete, Filter.pure_zero, Filter.tendsto_zero]
    rw [nhds_subtype_eq_comap]
    refine ⟨{ y : ℕ → ℕ | ∀ k < n + 1, y k = 0 }, ?_, ?_⟩ <;> norm_num [zeroStream]
    · rw [nhds_pi]
      simp +decide only [zeroStream, nhds_discrete, Filter.pure_zero, Filter.mem_pi, Filter.mem_zero]
      exact ⟨Finset.range (n + 1), Finset.finite_toSet _, fun _ => {0}, fun _ => by norm_num,
        fun y hy k hk => by simpa using hy k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩
    · intro a ha h; split_ifs <;> simp_all +decide [zeroStream]
      unfold firstNonzero
      split_ifs <;> simp_all +decide [prependZerosOne]
      exact False.elim <| ‹¬a = zeroStream› <| funext fun k => by aesop
  · exact continuousAt_pointedGluingFun_nonzero A B f hf x hx

/--
**Fact (BasicsOnPointedGluing) — Part 2.**
Pointed gluing preserves injectivity.
-/
theorem pointedGluingFun_preserves_injectivity
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Injective (f i)) :
    Injective (PointedGluingFun A B f) := by
  intro x y hxy
  by_cases hx : x.val = zeroStream <;> by_cases hy : y.val = zeroStream <;> simp_all +decide [PointedGluingFun]
  · aesop
  · -- Since $y \neq zeroStream$, we have $stripZerosOne (firstNonzero y) y \in A (firstNonzero y)$.
    obtain ⟨i, hi⟩ : ∃ i, y.val ∈ prependZerosOne i '' (A i) := by
      have := y.2
      cases this <;> aesop
    obtain ⟨z, hz, hz'⟩ := hi
    have h_firstNonzero : firstNonzero y.val = i := by
      unfold firstNonzero; simp +decide [← hz', prependZerosOne]
      split_ifs <;> simp_all +decide [Nat.find_eq_iff]
      rename_i h; specialize h i; aesop
    specialize hxy (by
    grind [strip_mem_of_pointedGluingSet])
    replace hxy := congr_fun hxy i ; simp_all +decide [zeroStream, prependZerosOne]
  · have := hxy (by
    have hx_mem : x.val ∈ ⋃ i, prependZerosOne i '' (A i) := by
      exact Or.resolve_left x.2 hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_mem
    generalize_proofs at *
    obtain ⟨a, ha, ha'⟩ := hi
    generalize_proofs at *
    rw [← ha']
    rw [show firstNonzero (prependZerosOne i a) = i from ?_]
    · rw [stripZerosOne_prependZerosOne] ; assumption
    · unfold firstNonzero; simp +decide [prependZerosOne]
      split_ifs <;> simp_all +decide [Nat.find_eq_iff]
      rename_i h; specialize h i; aesop;)
    generalize_proofs at *
    replace this := congr_fun this (firstNonzero x) ; simp_all +decide [prependZerosOne]
    exact absurd this (by unfold zeroStream; norm_num)
  · -- Since $x$ and $y$ are not equal to the zero stream, we can apply the definition of `PointedGluingSet` to obtain that there exist $i$ and $j$ such that $x = \text{prependZerosOne } i z$ and $y = \text{prependZerosOne } j w$ for some $z \in A i$ and $w \in A j$.
    obtain ⟨i, z, hz⟩ : ∃ i z, x.val = prependZerosOne i z ∧ z ∈ A i := by
      have := x.2
      cases this <;> aesop
    obtain ⟨j, w, hw⟩ : ∃ j w, y.val = prependZerosOne j w ∧ w ∈ A j := by
      have := y.2
      cases this <;> aesop
    -- Since $x$ and $y$ are not equal to the zero stream, we have $firstNonzero x = i$ and $firstNonzero y = j$.
    have h_firstNonzero_x : firstNonzero x.val = i := by
      unfold firstNonzero
      split_ifs <;> simp_all +decide [Nat.find_eq_iff]
      · unfold prependZerosOne; aesop
      · exact False.elim <| hx <| funext ‹_›
    have h_firstNonzero_y : firstNonzero y.val = j := by
      unfold firstNonzero
      split_ifs <;> simp_all +decide [prependZerosOne]
      · simp_all +decide [Nat.find_eq_iff]
      · rename_i h; specialize h j le_rfl; aesop
    by_cases hij : i = j <;> simp_all +decide
    · split_ifs at hxy <;> simp_all +decide
      · simp_all +decide [Function.Injective.eq_iff (prependZerosOne_injective j)]
        simp_all +decide [stripZerosOne_prependZerosOne]
        grind +revert
      · exact False.elim <| ‹stripZerosOne j (prependZerosOne j w) ∉ A j› <| by simpa [stripZerosOne_prependZerosOne] using hw.2
      · exact False.elim <| ‹stripZerosOne j (prependZerosOne j z) ∉ A j› <| by simpa [stripZerosOne_prependZerosOne] using hz.2
      · exact False.elim <| ‹stripZerosOne j (prependZerosOne j z) ∉ A j› <| by simpa [stripZerosOne_prependZerosOne] using hz.2
    · split_ifs at hxy <;> simp_all +decide
      · cases lt_or_gt_of_ne hij <;> have := congr_fun hxy ‹_› <;> simp_all +decide [prependZerosOne]
        have := congr_fun hxy i; simp_all +decide [prependZerosOne]
      · simp_all +decide [stripZerosOne_prependZerosOne]
      · exact False.elim <| ‹stripZerosOne i (prependZerosOne i z) ∉ A i› <| by simpa [stripZerosOne_prependZerosOne] using hz.2
      · exact False.elim <| ‹stripZerosOne i (prependZerosOne i z) ∉ A i› <| by simpa [stripZerosOne_prependZerosOne] using hz.2

/--
**Fact (BasicsOnPointedGluing) — Part 3.**
Pointed gluing commutes with identity: `id_{pgl_i X_i} = pgl_i id_{X_i}`.
-/
theorem pointedGluingFun_comm_id (A : ℕ → Set (ℕ → ℕ)) :
    (fun x => PointedGluingFun A A (fun _i => id) x) =
    (fun (x : PointedGluingSet A) => x.val) := by
  unfold PointedGluingFun
  ext x
  split_ifs <;> simp_all +decide [zeroStream]
  have h_mem : ∃ i, ∃ x', x.val = prependZerosOne i x' ∧ x' ∈ A i := by
    rcases x with ⟨x, hx⟩
    cases hx <;> aesop
  obtain ⟨i, x', hx, hx'⟩ := h_mem
  rw [show firstNonzero x.val = i from _]
  · simp +decide [hx, stripZerosOne_prependZerosOne]
    rw [if_pos hx']
  · unfold firstNonzero
    split_ifs <;> simp_all +decide [prependZerosOne]
    · simp_all +decide [Nat.find_eq_iff]
    · rename_i h; specialize h i; aesop

/--
**Fact (BasicsOnPointedGluing) — Part 4.**
The point `0^ω` is a continuity point of the pointed gluing of any sequence of
functions in 𝒞.
-/
theorem zeroStream_continuity_point
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuousAt (PointedGluingFun A B f)
      ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ := by
  unfold PointedGluingFun
  refine tendsto_pi_nhds.mpr ?_
  intro x
  simp only [dite_eq_ite, ↓reduceDIte, zeroStream, nhds_discrete, Filter.pure_zero, Filter.tendsto_zero]
  rw [nhds_subtype_eq_comap]
  refine ⟨{ y : ℕ → ℕ | ∀ k < x + 1, y k = 0 }, ?_, ?_⟩ <;> norm_num [zeroStream]
  · rw [nhds_pi]
    simp +decide only [zeroStream, nhds_discrete, Filter.pure_zero, Filter.mem_pi, Filter.mem_zero]
    exact ⟨Finset.range (x + 1), Finset.finite_toSet _, fun _ => { 0 }, fun _ => by norm_num, fun y hy k hk => by simpa using hy k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩
  · intro a ha h; split_ifs <;> simp_all +decide [zeroStream]
    unfold firstNonzero
    split_ifs <;> simp_all +decide [prependZerosOne]
    exact False.elim <| ‹¬a = zeroStream› <| funext fun k => by aesop

lemma CBLevel_zero_ne_succ_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBLevel f 0 ≠ CBLevel f (Order.succ 0) := by
  intro h
  rw [CBLevel_zero, CBLevel_succ'] at h
  simp +decide only [Set.ext_iff, mem_univ, mem_diff, true_iff] at h
  contrapose! h
  exact Exists.elim (scattered_isolatedLocus_nonempty f hf (CBLevel f 0) (by simp +decide [CBLevel_zero])) fun x hx => ⟨x, fun _ => hx⟩

/--
For scattered functions on a Small.{0} type, the stabilization set for CBRank is nonempty.
-/
lemma CBRank_stabilization_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (_hne : Nonempty X) :
    {α : Ordinal | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  contrapose! hf
  obtain ⟨g, hg⟩ := CBLevel_strictAnti_of_ne f (by
  exact fun α => fun h => hf.subset h)
  exact False.elim (not_injective_of_ordinal g hg)

/--
If f is scattered on a nonempty Small.{0} domain, then CBRank f > 0.
-/
lemma CBRank_pos_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBRank f > 0 := by
  refine pos_iff_ne_zero.mpr ?_
  have := CBLevel_zero_ne_succ_of_scattered_nonempty f hf hne
  exact fun h => this <| h ▸ csInf_mem (CBRank_stabilization_set_nonempty f hf hne)

theorem CBrank_pointedGluing_regular
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (cbranks : ℕ → Ordinal.{0})
    (hreg : IsRegularOrdSeq cbranks)
    (hα : ∀ i, CBRank (fun (x : A i) => (f i x : ℕ → ℕ)) = cbranks i)
    (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n) (hαpos : α > 0) :
    CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) α =
      {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · apply zeroStream_mem_CBLevel_le A B f hf_scat cbranks hreg hα α hαsup hαpos α (le_refl α)
  · apply CBLevel_pointedGluing_subset
    all_goals tauto

/-
Given a sequence `(f_i)_i` in 𝒞, we have `⊔_i f_i ≤ pgl_i f_i`.

The proof uses Gluingaslowerbound with `f = pgl_i f_i` and
`B_i = N_{(0)^i(1)}`. -/
/-- Map from GluingSet to PointedGluingSet: (i)⌢a ↦ (0^i)(1)a -/
noncomputable def gluingToPointed (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) : PointedGluingSet A :=
  let h := GluingSet_inverse_short A x
  let i := h.choose
  let a := unprepend x.val
  ⟨prependZerosOne i a,
    Or.inr (Set.mem_iUnion.mpr ⟨i, a, h.choose_spec.2, rfl⟩)⟩

/-- Map from (ℕ → ℕ) to (ℕ → ℕ): (0^i)(1)b ↦ (i)⌢b, and 0^ω ↦ 0^ω -/
noncomputable def pointedToGluing (y : ℕ → ℕ) : ℕ → ℕ :=
  if y = zeroStream then zeroStream
  else prepend (firstNonzero y) (stripZerosOne (firstNonzero y) y)

theorem prependZerosOne_ne_zeroStream (i : ℕ) (x : ℕ → ℕ) :
    prependZerosOne i x ≠ zeroStream := by
  -- By definition of `prependZerosOne`, `prependZerosOne i x` is not equal to `zeroStream` because `prependZerosOne i x` has a `1` at position `i` while `zeroStream` has `0` everywhere.
  have h_neq : ∃ k, (prependZerosOne i x) k ≠ zeroStream k := by
    exact ⟨i, by simp [prependZerosOne, zeroStream]⟩
  exact fun h => h_neq.choose_spec <| congr_fun h _

theorem firstNonzero_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    firstNonzero (prependZerosOne i x) = i := by
  unfold firstNonzero
  split_ifs <;> simp_all +decide [Nat.find_eq_iff]
  · unfold prependZerosOne; aesop
  · rename_i h; specialize h i; simp_all +decide [prependZerosOne]

theorem continuous_prependZerosOne (i : ℕ) : Continuous (prependZerosOne i) := by
  refine continuous_pi fun n => ?_
  unfold prependZerosOne
  split_ifs <;> continuity

theorem gluing_le_pointedGluing
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuouslyReduces
      (fun (x : GluingSet A) => GluingFunVal A B f x)
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  -- The σ function is continuous because it is a composition of continuous functions.
  have hσ_cont : Continuous (gluingToPointed A) := by
    refine continuous_induced_rng.mpr ?_
    -- The function x ↦ prependZerosOne (x.val 0) (unprepend x.val) is continuous because it is a composition of continuous functions.
    have h_cont : ∀ n, ContinuousOn (fun x : GluingSet A => prependZerosOne n (unprepend x.val)) {x : GluingSet A | x.val 0 = n} := by
      intro n
      have h_cont : Continuous (fun x : ℕ → ℕ => prependZerosOne n (unprepend x)) := by
        exact continuous_pi_iff.mpr fun i => by cases i <;> continuity
      generalize_proofs at *; (
      exact h_cont.comp_continuousOn (continuous_subtype_val.continuousOn))
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    have h_cont_at : ContinuousAt (fun x : GluingSet A => prependZerosOne (x.val 0) (unprepend x.val)) x := by
      have h_cont_at : ∀ᶠ y in nhds x, y.val 0 = x.val 0 := by
        have h_cont_at : IsOpen {y : GluingSet A | y.val 0 = x.val 0} := by
          have h_cont_at : IsOpen {y : ℕ → ℕ | y 0 = x.val 0} := by
            rw [isOpen_pi_iff]
            exact fun f hf => ⟨{ 0 }, fun _ => { y | y = x.val 0 }, by aesop⟩
          generalize_proofs at *
          exact h_cont_at.preimage (continuous_subtype_val)
        generalize_proofs at *
        exact h_cont_at.mem_nhds rfl
      generalize_proofs at *
      exact ContinuousAt.congr (h_cont (x.val 0) |> ContinuousOn.continuousAt <| by filter_upwards [h_cont_at] with y hy; aesop) <| Filter.eventuallyEq_of_mem h_cont_at fun y hy => by aesop
    generalize_proofs at *
    convert h_cont_at using 1
    generalize_proofs at *
    grind +locals
  refine ⟨gluingToPointed A, hσ_cont, pointedToGluing, ?_, ?_⟩
  · -- Since the range of the composition is a subset of the set where pointedToGluing is continuous, we can conclude that pointedToGluing is continuous on the range.
    have h_range_subset : Set.range ((fun x => PointedGluingFun A B f x) ∘ gluingToPointed A) ⊆ {y | y ≠ zeroStream} := by
      intro y hy; obtain ⟨x, rfl⟩ := hy; simp +decide [PointedGluingFun]
      unfold gluingToPointed; simp +decide [prependZerosOne_ne_zeroStream]
      rw [firstNonzero_prependZerosOne]
      convert (GluingSet_inverse_short A x).choose_spec.2 using 1
      exact stripZerosOne_prependZerosOne _ _
    refine ContinuousOn.mono ?_ h_range_subset
    -- The function pointedToGluing is continuous on the set where y is not zeroStream because it is a composition of continuous functions.
    have h_cont : ContinuousOn (fun y => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) y)) {y | y ≠ zeroStream} := by
      -- Since `firstNonzero` is locally constant on `{y | y ≠ zeroStream}`, we can use the fact that the composition of continuous functions is continuous.
      have h_locally_const : ∀ y : ℕ → ℕ, y ≠ zeroStream → ∃ U : Set (ℕ → ℕ), IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, firstNonzero z = firstNonzero y := by
        intro y hy
        use {z | z (firstNonzero y) ≠ 0 ∧ ∀ n < firstNonzero y, z n = 0}
        refine ⟨?_, ?_, ?_⟩
        · simp +decide only [setOf_and, setOf_forall]
          refine IsOpen.inter ?_ ?_
          · exact isOpen_ne.preimage (continuous_apply _)
          · refine isOpen_iff_forall_mem_open.mpr ?_
            intro x hx
            refine ⟨⋂ i ∈ Finset.range (firstNonzero y), { z : ℕ → ℕ | z i = 0 }, ?_, ?_, ?_⟩ <;> simp_all +decide [Set.subset_def]
            rw [show (⋂ i, ⋂ (_ : i < firstNonzero y), { z : ℕ → ℕ | z i = 0 }) = ⋂ i ∈ Finset.range (firstNonzero y), { z : ℕ → ℕ | z i = 0 } by ext; aesop] ; exact isOpen_biInter_finset fun i hi => isOpen_discrete { 0 } |> IsOpen.preimage (continuous_apply i)
        · unfold firstNonzero
          split_ifs <;> simp_all +decide
          · exact Nat.find_spec ‹∃ k, y k ≠ 0›
          · exact hy (funext ‹_›)
        · intro z hz
          refine le_antisymm ?_ ?_ <;> simp_all +decide [firstNonzero]
          · split_ifs at * <;> simp_all +decide [Nat.find_eq_iff]
            grind [Nat.find_le]
          · split_ifs at * <;> simp_all +decide [Nat.find_eq_iff]
      intro y hy
      obtain ⟨U, hU_open, hyU, hU_const⟩ := h_locally_const y hy
      have h_cont_on_U : ContinuousOn (fun z => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) z)) U := by
        refine' Continuous.continuousOn _
        exact continuous_prepend _ |> Continuous.comp <| continuous_pi fun _ => continuous_apply _
      generalize_proofs at *
      exact ContinuousAt.continuousWithinAt (by exact ContinuousAt.congr (h_cont_on_U.continuousAt (hU_open.mem_nhds hyU)) (Filter.eventuallyEq_of_mem (hU_open.mem_nhds hyU) fun z hz => by aesop))
    refine h_cont.congr fun y hy => ?_
    unfold pointedToGluing; aesop
  · unfold GluingFunVal pointedToGluing PointedGluingFun gluingToPointed
    grind [prependZerosOne_ne_zeroStream, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne, Subtype.mk_eq_mk]

/-- At the first nonzero position of `z`, the value is indeed nonzero.
    This tiny fact was proved twice inline in the original; we lift it here. -/
lemma firstNonzero_val_ne {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
    z (firstNonzero z) ≠ 0 := by
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hz (funext fun i => by simp [zeroStream, hall i])
  simp only [firstNonzero, dif_pos hex]
  exact Nat.find_spec hex

/-- All positions strictly before firstNonzero z are zero. -/
lemma firstNonzero_zero {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
    ∀ k, k < firstNonzero z → z k = 0 := by
  -- firstNonzero z = Nat.find hex, and Nat.find_min says:
  -- for any m < Nat.find hex, ¬ (z m ≠ 0), i.e. z m = 0.
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hz (funext fun i => by simp [zeroStream, hall i])
  intro k hk
  simp only [firstNonzero, dif_pos hex] at hk
  -- Nat.find_min : ∀ m < Nat.find h, ¬ P m
  have := Nat.find_min hex hk
  push_neg at this
  exact this

/-
============================================================
HELPER LEMMAS FOR CONSTRUCTING CONTINUOUS REDUCTIONS
============================================================

On each piece (ray block), σ is continuous.
-/
lemma sigma_cont_on_pieces
    {A : Type*} [TopologicalSpace A]
    {C : ℕ → Set (ℕ → ℕ)}
    {An : ℕ → Set A}
    (x : A)
    (σ_n : ∀ n, ↑(C n) → ↑(An n))
    (hσ_n : ∀ n, Continuous (σ_n n))
    (i : ℕ) :
    let σ : ↑(PointedGluingSet C) → A := fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val
    let piece := Subtype.val ⁻¹' RaySet (PointedGluingSet C) zeroStream i
    Continuous (fun z : ↑piece => σ z.val) := by
  refine Continuous.congr
    (f := fun z => (σ_n i ⟨stripZerosOne i z.val.val, strip_mem_of_block C z.val i z.2.2⟩).val)
    ?_ ?_
  · refine Continuous.comp ?_ ?_
    · exact continuous_subtype_val
    · exact hσ_n i |> Continuous.comp <| Continuous.subtype_mk (continuous_stripZerosOne i |> Continuous.comp <| continuous_subtype_val.comp <| continuous_subtype_val) _
  · intro z
    simp only [RaySet, ne_eq, sep_and, preimage_inter, preimage_setOf_eq, Subtype.coe_prop, true_and] at z
    rename_i h
    have := h.2.2
    have h_firstNonzero : firstNonzero h.val.val = i := by
      unfold firstNonzero
      split_ifs <;> simp_all +decide [Nat.find_eq_iff]
      · exact ⟨this.2, fun n hn => rfl⟩
      · exact False.elim (this.2 (by rfl))
    cases h ; aesop

/-- ContinuousOn τ_global on range(f ∘ σ): for any y in the range, ContinuousWithinAt holds.
    Uses that range(f ∘ σ) = {f x} ∪ ⋃ In n, and τ_global is continuous on each In n
    (as τ ∘ inclusion) and satisfies a sequential condition at f x. -/
lemma tau_global_continuousOn
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    (f : A → B) (_hf : Continuous f)
    {C : ℕ → Set (ℕ → ℕ)}
    (x : A)
    (An : ℕ → Set A)
    (hsep : ∀ n, f x ∉ closure (f '' (An n)))
    (σ_n : ∀ n, ↑(C n) → ↑(An n))
    (τ_n : ℕ → B → ℕ → ℕ)
    (_hτ_n : ∀ n, ContinuousOn (τ_n n) (Set.range ((f ∘ Subtype.val) ∘ σ_n n)))
    (_hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n)))
    (σ : ↑(PointedGluingSet C) → A)
    (_σ_cont : Continuous σ)
    (hσ_def : σ = fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val)
    (In : ℕ → Set B)
    (_hIn_def : In = fun n => Set.range ((f ∘ Subtype.val) ∘ σ_n n))
    (h_refine : ∀ n, In n ⊆ f '' (An n))
    (_hrelclop' : IsRelativeClopenPartition In)
    (τi : ↑(⋃ n, In n) → ℕ)
    (hτi_n : ∀ (y : ↑(⋃ n, In n)) (n : ℕ), y.val ∈ In n → τi y = n)
    (_hτi_cont : Continuous τi)
    (τ : ↑(⋃ n, In n) → ℕ → ℕ)
    (hτ_def : τ = fun y => prependZerosOne (τi y) (τ_n (τi y) y.val))
    (hτ_cont : Continuous τ)
    (τ_global : B → ℕ → ℕ)
    (hτg_def : τ_global = fun y => if h : y ∈ ⋃ n, In n then τ ⟨y, h⟩ else zeroStream)
    (hfx_notUI : f x ∉ ⋃ n, In n)
    (h_incl : ∀ z : ↑(PointedGluingSet C), z.val ≠ zeroStream → f (σ z) ∈ ⋃ n, In n)
    (_hcomp : Continuous (fun z : ↑(PointedGluingSet C) => τ_global (f (σ z)))) :
    ContinuousOn τ_global (Set.range (f ∘ σ)) := by
  -- Step 1: range(f ∘ σ) ⊆ {f x} ∪ ⋃ In n
  have hrange : Set.range (f ∘ σ) ⊆ {f x} ∪ ⋃ n, In n := by
    rintro y ⟨z, rfl⟩
    by_cases hz : z.val = zeroStream
    · left; show f (σ z) = f x; congr 1; rw [hσ_def]; simp [hz]
    · right; exact h_incl z hz
  -- Step 2: ContinuousOn τ_global (⋃ In n)
  have h_cont_UI : ContinuousOn τ_global (⋃ n, In n) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hτ_cont.congr (fun ⟨y, hy⟩ => by
      simp only [Set.restrict, hτg_def, dif_pos hy])
  -- Step 3: ContinuousWithinAt at f x (the hard part)
  -- We use continuousWithinAt_pi to reduce to each coordinate.
  -- For coordinate j, τ_global y j = 0 for y near f x in range(f ∘ σ),
  -- because y ∈ In(m) forces m > j when y is close enough to f x.
  have hcwat_fx : ContinuousWithinAt τ_global (range (f ∘ σ)) (f x) := by
    rw [continuousWithinAt_pi]
    intro j
    rw [ContinuousWithinAt]
    have hval : τ_global (f x) j = 0 := by
      rw [hτg_def]; simp [hfx_notUI, zeroStream]
    rw [hval]
    -- The j-th coordinate is eventually 0 near f x, so it tends to 0
    have h_ev : (fun y => τ_global y j) =ᶠ[nhdsWithin (f x) (range (f ∘ σ))] (fun _ => (0 : ℕ)) := by
      have hU : (⋂ m ∈ Finset.range (j+1), (closure (f '' An m))ᶜ) ∈ nhds (f x) :=
        (isOpen_biInter_finset
          (fun m _ => isOpen_compl_iff.mpr isClosed_closure)).mem_nhds
          (Set.mem_iInter₂.mpr (fun m _ => hsep m))
      apply Filter.eventually_of_mem (inter_mem_nhdsWithin _ hU)
      intro y ⟨hy_range, hy_open⟩
      rcases hrange hy_range with h | h
      · rw [Set.mem_singleton_iff.mp h, hτg_def]; simp [hfx_notUI, zeroStream]
      · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp h
        have hm_large : j < m := by
          by_contra hle; push_neg at hle
          exact Set.mem_iInter₂.mp hy_open m (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
            (subset_closure (h_refine m hm))
        show τ_global y j = 0
        simp only [hτg_def, dif_pos h, hτ_def, hτi_n ⟨y, h⟩ m hm]
        exact prependZerosOne_head_eq_zero m _ j hm_large
    exact tendsto_const_nhds.congr' h_ev.symm
  -- Step 4: Combine
  intro y hy
  by_cases hy_UI : y ∈ ⋃ n, In n
  · apply (h_cont_UI y hy_UI).mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    refine ⟨{z | z ≠ f x}, isOpen_ne, ?_, ?_⟩
    · intro heq; exact hfx_notUI (heq ▸ hy_UI)
    · intro z ⟨hz1, hz2⟩
      rcases hrange hz2 with h | h
      · exact absurd (Set.mem_singleton_iff.mp h) hz1
      · exact h
  · have : y = f x := by
      rcases hrange hy with h | h
      · exact Set.mem_singleton_iff.mp h
      · exact absurd h hy_UI
    rw [this]; exact hcwat_fx

/--
The pointed gluing of scattered functions is scattered.
Given nonempty S, if S contains a non-zero element in block i, use ScatteredFun
of f_i to find an open set where the function is constant. If S = {0ω}, trivial.
-/
lemma pointedGluing_scattered
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ))) :
    ScatteredFun (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  intro S hS_nonempty
  by_cases h_zero : S = {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩}
  · refine ⟨Set.univ, isOpen_univ, ?_, ?_⟩ <;> aesop
  · obtain ⟨y, hy⟩ : ∃ y ∈ S, y.val ≠ zeroStream := by
      contrapose! h_zero
      exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hS_nonempty, fun y hy => Subtype.ext <| h_zero y hy⟩
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (∀ k, k < i → y.val k = 0) ∧ y.val i ≠ 0 := by
      exact ⟨Nat.find (show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h), fun k hk => by_contra fun hk' => Nat.find_min (show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h) hk hk', Nat.find_spec (show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h)⟩
    -- Define Block_i as the set of elements in the pointed gluing set whose first nonzero entry is at index i.
    set Block_i : Set (PointedGluingSet A) := {z : PointedGluingSet A | (∀ k, k < i → z.val k = 0) ∧ z.val i ≠ 0}
    -- Since $S$ is nonempty and contains elements with first nonzero entry at index $i$, we can apply the scatteredness of $f_i$ to find an open set $V$ in $A_i$ where $f_i$ is constant.
    obtain ⟨V, hV_open, hV_nonempty, hV_const⟩ : ∃ V : Set (A i), IsOpen V ∧ (V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}).Nonempty ∧ ∀ x ∈ V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}, ∀ x' ∈ V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}, (f i x).val = (f i x').val := by
      apply hf_scat i
      exact ⟨⟨stripZerosOne i y.val, strip_mem_of_block A y i ⟨hi.1, hi.2⟩⟩, ⟨y, ⟨hy.1, hi⟩, rfl⟩⟩
    obtain ⟨V₀, hV₀_open, hV₀_eq⟩ : ∃ V₀ : Set (ℕ → ℕ), IsOpen V₀ ∧ V = Subtype.val ⁻¹' V₀ := by
      obtain ⟨V₀, hV₀_open, rfl⟩ := hV_open; exact ⟨V₀, hV₀_open, rfl⟩
    refine ⟨Block_i ∩ { z : PointedGluingSet A | stripZerosOne i z.val ∈ V₀ }, ?_, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · convert isOpen_block i |> IsOpen.preimage (continuous_subtype_val) using 1
      · exact hV₀_open.preimage (continuous_stripZerosOne i |> Continuous.comp <| continuous_subtype_val)
    · obtain ⟨z, hz⟩ := hV_nonempty
      obtain ⟨y, hy₁, hy₂⟩ := hz.2
      exact ⟨y, ⟨⟨hy₁.2, by aesop⟩, hy₁.1⟩⟩
    · intro x hx x' hx'
      simp_all +decide [PointedGluingFun]
      rw [if_neg, if_neg]
      · rw [firstNonzero_eq_of_block _ _ hx.1.1, firstNonzero_eq_of_block _ _ hx'.1.1]
        grind [strip_mem_of_block]
      · exact ne_zeroStream_of_block _ _ hx'.1.1
      · exact ne_zeroStream_of_block _ _ hx.1.1

/-! ## Joint / relative continuity of the pointed-gluing coding maps

Relocated from `ScatFun/FiniteGluing.lean`; used by `ScatFun.gl_reduces_pgl_direct`. -/

/-
**Joint continuity of `prependZerosOne`.**  The depth index lives in the
discrete space `ℕ`, so `prependZerosOne` is continuous in both arguments at once.
-/
lemma continuous_prependZerosOne_uncurry :
    Continuous (fun p : ℕ × Baire => prependZerosOne p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr ?_;
  intro p;
  refine ContinuousAt.congr (f := fun q => prependZerosOne p.1 q.2) ?_ ?_;
  · exact Continuous.continuousAt ( continuous_prependZerosOne p.1 |> Continuous.comp <| continuous_snd );
  · filter_upwards [ IsOpen.mem_nhds ( isOpen_discrete { p.1 } |> IsOpen.preimage continuous_fst ) ( Set.mem_singleton p.1 ) ] with q hq ; aesop

/-
`firstNonzero` is continuous on any set that avoids the base point `0^ω`
(there it is locally constant).
-/
lemma firstNonzero_continuousOn {S : Set Baire} (hS : ∀ y ∈ S, y ≠ zeroStream) :
    ContinuousOn firstNonzero S := by
  intro y hy;
  refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds;
  intro ε hε;
  -- Since `y ≠ zeroStream`, there exists a neighborhood around `y` where `firstNonzero` is constant.
  obtain ⟨N, hN⟩ : ∃ N, ∀ x, (∀ i ≤ N, x i = y i) → firstNonzero x = firstNonzero y := by
    obtain ⟨N, hN⟩ : ∃ N, firstNonzero y ≤ N ∧ ∀ i < N, y i = 0 := by
      unfold firstNonzero;
      split_ifs <;> simp_all +decide;
      exact ⟨ Nat.find ‹∃ k, y k ≠ 0›, ⟨ _, le_rfl, Nat.find_spec ‹∃ k, y k ≠ 0› ⟩, fun i hi => by_contra fun hi' => Nat.find_min ‹∃ k, y k ≠ 0› hi hi' ⟩;
    use N;
    intro x hx;
    unfold firstNonzero at *;
    split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
    · grind;
    · exact hS y hy ( funext ‹_› );
    · grind;
  rw [ nhds_pi ];
  refine Filter.mem_pi.mpr ?_;
  refine ⟨ Finset.range ( N + 1 ), Finset.finite_toSet _, fun i => if i ≤ N then { y i } else Set.univ, ?_, ?_ ⟩ <;> simp_all +decide [ Set.subset_def ]
