import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.BlockData
import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.WedgeMem
import WqoContinuousFunctions.DoubleSuccessor.Diagonal.SecondCase.Disjointification

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-- **`𝒲_{α+1} ⊆ FinGl 𝒢_{α+2}`** (set-level; the `w`-half analogue of
`diagonalTheorem_firstCase_omegaD_mem`). Each reference function
`w ∈ 𝒲_{α+1} = {maxFun λ} ∪ ω{𝒞_{α+1}}` (`λ = α.limitPart`) lies in `FinGl 𝒢_{α+2}`:
* `w = ω c` for `c ∈ 𝒞_{α+1} ⊆ 𝒞_{α+2}` — the `ω`-image `genStep` clause (as in the first
  case), **proved**;
* `w = maxFun λ` — for `λ` a nonzero limit, `maxFun λ = ℓ_λ ∈ 𝒢_λ ⊆ 𝒢_{α+2}`; for `λ = 0`,
  `maxFun 0` has `CB`-rank `0` hence empty domain, so `≡ empty ∈ FinGl`.

**Fully proved.** -/
theorem omegaRegularSet_add_one_mem_finGl
    (α : Ordinal.{0}) (hα : α < omega1) {w : ScatFun}
    (hw : w ∈ omegaRegularSet (α + 1) (by simpa using omega1_add_nat α hα 1)) :
    w ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := by
  classical
  set lam := α.limitPart with hlamdef
  set m := α.natPart with hmdef
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hαsucc : (α + 1 : Ordinal) = lam + ↑(m + 1) := by
    rw [Ordinal.eq_limitPart_add_natPart α, Nat.cast_add, Nat.cast_one, add_assoc]
  have hlp : (α + 1).limitPart = lam := by
    rw [hαsucc]; exact Ordinal.limitPart_add_natCast lam (m + 1) hlim
  -- A single generator lies in `FinGl 𝒢_{α+2}`.
  have hmem_of_gen : ∀ g : ScatFun, g ∈ ScatFun.Generators (α + 1 + 1) →
      g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun := fun g hg =>
    ScatFun.finGl_of_equiv_glList (L := [g])
      (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hg)
      (ScatFun.glList_single_equiv g)
  have hlam_lt : lam < omega1 :=
    lt_of_le_of_lt (show lam ≤ α by
      rw [hlamdef]; conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
      exact le_self_add) hα
  have harith : α + 1 + 1 = lam + ((m + 2 : ℕ) : Ordinal) := by
    rw [hαsucc, add_assoc]; norm_cast
  rw [omegaRegularSet, Finset.mem_insert] at hw
  rcases hw with hmax | himg
  · -- `w = maxFun λ`.
    subst hmax
    simp only [hlp]
    rcases hlim with hlimit | hzero
    · -- `λ` a nonzero limit: `maxFun λ = ℓ_λ ∈ 𝒢_{λ+1} ⊆ 𝒢_{α+2}`.
      apply hmem_of_gen
      rw [harith]
      refine ScatFun.Generators_mono_of_le (Or.inl hlimit) (show (1 : ℕ) ≤ m + 2 by omega) ?_
      rw [show lam + ((1 : ℕ) : Ordinal) = lam + 1 by norm_cast]
      exact ScatFun.maxFun_mem_Generators_add_one lam hlimit hlam_lt
    · -- `λ = 0`: `maxFun 0` has `CB`-rank `0`, so empty domain, hence `∈ FinGl` (`empty_mem_FinGl`).
      have h0 : (0 : Ordinal.{0}) < omega1 := hzero ▸ hlam_lt
      simp only [hzero]
      refine ScatFun.empty_mem_FinGl _ ?_
      rw [Set.isEmpty_coe_sort, ← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      have hpos := CBRank_pos_of_scattered_nonempty _
        (ScatFun.maxFun 0 h0).hScat ⟨(⟨x, hx⟩ : ↑(ScatFun.maxFun 0 h0).domain)⟩
      rw [ScatFun.maxFun_func, maxFun_cbRank_eq 0 h0] at hpos
      exact lt_irrefl 0 hpos
  · -- `w = ω c`, `c ∈ 𝒞_{α+1}`.
    rw [Finset.mem_image] at himg
    obtain ⟨c, hc, rfl⟩ := himg
    apply hmem_of_gen
    rw [hαsucc, ScatFun.Generators_add_succ_eq hlim (m + 1)]
    refine Finset.mem_union_right _ ?_
    unfold ScatFun.genStep
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    apply Finset.mem_image_of_mem
    exact ScatFun.Centered_add_nat_subset_succ hlim (m + 1) (by rw [← hαsucc]; exact hc)

/-- **`ω` collapses on `𝒲_{α+1}`-gluings: `ω(gl H) ≡ gl H` for `H ⊆ 𝒲_{α+1}`.** Every element of
`𝒲_{α+1} = {maxFun λ} ∪ ω{𝒞_{α+1}}` is `ω`-idempotent up to equivalence — `maxFun λ` by
`omega_maxFun_equiv_self`, and `ω c` (`= gl (fun _ => c)`) by `omega_omega_equiv`
(`ω(ω c) ≡ ω c`). Expanding `ω(gl H) ≡ gl (H.toList.map ω)` (`omega_glList_equiv_glList_omega`)
and collapsing each block pointwise (`gl_reduces_of_pointwise` both directions) gives the claim.

This is the crux that lets the second-case right reduction feed the *plain* block reduction
`gl H ≤ F⇂W` exposed by the Vertical Theorem: the memoir writes `w = gl_{g'} ω H_{g'}` with the
`ω` explicit and `H_{g'} ⊆ 𝒞_{α+1}` centered, whereas the Lean formalization carries the `ω`
inside the `𝒲`-valued `H` already (`ω c ∈ 𝒲_{α+1}`), so the outer `ω` in `w = gl_i ω(gl Hᵢ)` is
redundant and this lemma removes it — no strengthening of the Vertical Theorem needed. -/
theorem omega_glList_equiv_self_of_subset_omegaRegularSet
    (α : Ordinal.{0}) (hα1 : α + 1 < omega1) (H : Finset ScatFun)
    (hHsub : H ⊆ omegaRegularSet (α + 1) hα1) :
    ScatFun.Equiv (ScatFun.omega (ScatFun.glList H.toList)) (ScatFun.glList H.toList) := by
  classical
  -- Each element of `H` is `ω`-idempotent (`ω e ≡ e`).
  have hidem : ∀ e ∈ H.toList, ScatFun.Equiv (ScatFun.omega e) e := by
    intro e he
    have heW := hHsub (Finset.mem_toList.mp he)
    rw [omegaRegularSet, Finset.mem_insert, Finset.mem_image] at heW
    rcases heW with hmax | ⟨c, _, rfl⟩
    · rw [hmax]; exact ScatFun.omega_maxFun_equiv_self _ _
    · exact ScatFun.omega_omega_equiv c
  -- `ω(gl H) ≡ gl(H.toList.map ω) ≡ gl H.toList`, the second `≡` pointwise via `hidem`.
  refine (ScatFun.omega_glList_equiv_glList_omega H.toList).trans ⟨?_, ?_⟩
  · -- `gl (H.toList.map ω) ≤ gl H.toList`: pointwise `ω(H.toList[k]) ≤ H.toList[k]`.
    refine ScatFun.gl_reduces_of_pointwise _ _ (fun k => ?_)
    by_cases hk : k < H.toList.length
    · rw [show (H.toList.map ScatFun.omega).getD k ScatFun.empty
            = ScatFun.omega (H.toList[k]) by
          rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map],
        List.getD_eq_getElem _ _ hk]
      exact (hidem _ (List.getElem_mem hk)).1
    · rw [List.getD_eq_default _ _ (by simpa using not_lt.mp hk),
        List.getD_eq_default _ _ (not_lt.mp hk)]
      exact ContinuouslyReduces.refl _
  · -- `gl H.toList ≤ gl (H.toList.map ω)`: pointwise `H.toList[k] ≤ ω(H.toList[k])`.
    exact ScatFun.glList_reduces_glList_map H.toList ScatFun.omega
      (fun w hw => (hidem w hw).2)

/-- **Greedy pairwise-disjoint clopen selection.** If, for every index and every clopen
neighbourhood `U'` of `y`, there is a clopen `W ⊆ U'` avoiding `y` with property `P a W`, then a
finite family of indices admits *pairwise-disjoint* such choices, all inside a given `U`. Proved
by induction: pick `W₀ ⊆ U`, then recurse inside the shrunk clopen neighbourhood `U ∖ W₀`
(still containing `y`, since `y ∉ W₀`), so every later choice is disjoint from `W₀`. Used to feed
the disjoint-clopen gluing `gl_coRestrict_disjoint_open_reduces` in the second-case right
reduction. -/
theorem exists_pairwise_disjoint_clopen_of_forall_nbhd
    {ι : Type*} (y : Baire) (P : ι → Set Baire → Prop)
    (hex : ∀ (a : ι) (U' : Set Baire), IsClopen U' → y ∈ U' →
      ∃ W, W ⊆ U' ∧ IsClopen W ∧ y ∉ W ∧ P a W) :
    ∀ (n : ℕ) (c : Fin n → ι) (U : Set Baire), IsClopen U → y ∈ U →
      ∃ W : Fin n → Set Baire, (∀ i, W i ⊆ U) ∧ (∀ i, IsClopen (W i)) ∧
        (∀ i, y ∉ W i) ∧ (∀ i, P (c i) (W i)) ∧ Pairwise (Disjoint on W) := by
  intro n
  induction n with
  | zero => exact fun c U _ _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro c U hUcl hyU
    obtain ⟨W0, hW0U, hW0cl, hW0y, hW0P⟩ := hex (c 0) U hUcl hyU
    obtain ⟨Wt, hWtU, hWtcl, hWty, hWtP, hWtdisj⟩ :=
      ih (fun i => c i.succ) (U \ W0) (hUcl.diff hW0cl) ⟨hyU, hW0y⟩
    refine ⟨Fin.cases W0 Wt, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i => Fin.cases hW0U (fun j => (hWtU j).trans Set.diff_subset) i
    · exact fun i => Fin.cases hW0cl hWtcl i
    · exact fun i => Fin.cases hW0y hWty i
    · exact fun i => Fin.cases hW0P hWtP i
    · intro i j hij
      simp only [Function.onFun]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩ <;>
        simp only [Fin.cases_zero, Fin.cases_succ]
      · exact absurd rfl hij
      · exact Set.disjoint_left.2 (fun a ha haWt => (hWtU j' haWt).2 ha)
      · exact Set.disjoint_left.2 (fun a ha haW0 => (hWtU i' ha).2 haW0)
      · exact hWtdisj (fun h => hij (congrArg Fin.succ h))

/-! ### Second-case assembly lemmas

The second-case construction (`diagonalTheorem_secondCase_setup`) is assembled from three
ingredients, following the memoir (`6_double_successor_memo.tex:301-386`):

* `diagonalTheorem_secondCase_construction` — the **geometric heart**: it produces the wedge data
  `n, v, w, D` together with (i) the membership `w ⊕ ⋀(v ∣ gl D) ∈ FinGl 𝒢_{α+2}`, (ii) the
  *left inputs* — a clopen split `univ = A⁰ ⊔ A¹` of `F.domain` with `F↾A⁰ ≤ w` and
  `F↾A¹ ≤ ⋀(v ∣ gl D)` (`:349-386`), and (iii) the *right inputs* — for each clopen `U ∋ y`, two
  disjoint clopen `W, V ⊆ U` with `w ≤ F⇂W` and `⋀(v ∣ gl D) ≤ F⇂V` (`:321-346`). All three
  obligations are now discharged — resting on the Vertical Theorem, the wedge upper/lower
  bounds, cocenter rigidity, and strong solvability, per the memoir. The last piece, the `A^D_n`
  ray-cut diagonal family (`secondCase_ray_cut_diagonal_family`) feeding the left
  `ScatFun.wedge_upper_bound`, is **now fully proved** (the file is complete).
* `ScatFun.reduces_glBin_of_clopen_partition` — the binary **Gluingasupperbound**: from the left
  inputs, `F ≤ w ⊕ ⋀(v ∣ gl D)`.
* `ScatFun.reduces_glBin_coRestrict_of_disjoint` — the binary lower bound: from the right inputs,
  `w ⊕ ⋀(v ∣ gl D) ≤ F⇂U`.

`diagonalTheorem_secondCase_setup` simply wires these together. -/

/-
**Binary `Gluingasupperbound`** (memoir `Gluingasupperbound`, the two-block case). If the
domain of `F` splits as a clopen partition `A0 ⊔ A1 = univ` and `F↾A0 ≤ a`, `F↾A1 ≤ b`, then
`F ≤ a ⊕ b`. Reusable; the second case's `F ≤ w ⊕ ⋀(v ∣ gl D)` is this applied to the
Vertical-Theorem split `A⁰ / A¹`.
-/
theorem ScatFun.reduces_glBin_of_clopen_partition {F : ScatFun} (a b : ScatFun)
    {A0 A1 : Set ↑F.domain} (h0 : IsClopen A0) (h1 : IsClopen A1)
    (hcover : A0 ∪ A1 = Set.univ) (hdisj : Disjoint A0 A1)
    (ha : ScatFun.Reduces (F.restrict A0) a) (hb : ScatFun.Reduces (F.restrict A1) b) :
    ScatFun.Reduces F (ScatFun.glBin a b) := by
  have hF_le_gl : ScatFun.Reduces F (ScatFun.gl (fun n => F.restrict (if n = 0 then A0 else if n = 1 then A1 else ∅))) := by
    apply scatFun_reduces_gl_of_domain_partition F (fun n => if n = 0 then A0 else if n = 1 then A1 else ∅) (by
    constructor;
    · intro n; by_cases hn : n = 0 <;> by_cases hn' : n = 1 <;> simp +decide [ hn, hn', h0, h1 ] ;
      exact isClopen_empty;
    · simp_all +decide [ Set.ext_iff ];
      exact ⟨ fun i j hij => by rcases i with ( _ | _ | i ) <;> rcases j with ( _ | _ | j ) <;> tauto, fun a ha => by rcases hcover a ha with ( h | h ) <;> [ exact ⟨ 0, h ⟩ ; exact ⟨ 1, h ⟩ ] ⟩)
  generalize_proofs at *; (
  -- Reduce the `gl` family `fun n => F.restrict (if n = 0 then A0 else if n = 1 then A1 else ∅)` to `glList [a, b]`.
  have hgl_le_glList : ScatFun.Reduces (ScatFun.gl (fun n => F.restrict (if n = 0 then A0 else if n = 1 then A1 else ∅))) (ScatFun.glList [a, b]) := by
    apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp_all +decide ;
    convert ScatFun.empty_reduces using 1;
    constructor <;> intro h <;> simp_all +decide [ ScatFun.restrict ];
    · exact fun G => empty_reduces G;
    · constructor;
      swap;
      exact fun x => False.elim <| x.2.choose_spec;
      exact ⟨ continuous_of_const fun x y => by cases x; cases y; tauto, fun _ => 0, continuousOn_const, fun x => by cases x; tauto ⟩
  generalize_proofs at *; (
  exact hF_le_gl.trans (hgl_le_glList.trans (ScatFun.finGl_glBin_equiv_glList a b).2) ;))

/-- **Binary gluing of two disjoint corestrictions reduces into the enclosing corestriction**
(memoir `Gluingaslowerbound2`, the two-block case). For disjoint open `W, V ⊆ U`,
`(F⇂W) ⊕ (F⇂V) ≤ F⇂U`. Proof: `F⇂W ≡ (F⇂U)⇂W` and `F⇂V ≡ (F⇂U)⇂V`
(`coRestrict_inter_reduces`), and the binary gluing of two disjoint-open corestrictions of
`F⇂U` reduces into `F⇂U` via `gl_coRestrict_disjoint_open_reduces` (`ScatFun/IntertwineReductions.lean`)
with the ℕ-family `W, V, ∅, ∅, …`. -/
theorem ScatFun.glBin_coRestrict_disjoint_reduces (F : ScatFun) {U W V : Set Baire}
    (hWU : W ⊆ U) (hVU : V ⊆ U) (hWop : IsOpen W) (hVop : IsOpen V) (hdisj : Disjoint W V) :
    ScatFun.Reduces (ScatFun.glBin (F.coRestrict W) (F.coRestrict V)) (F.coRestrict U) := by
  -- The ℕ-family of codomain windows `W, V, ∅, ∅, …`.
  have hUfam_open : ∀ k, IsOpen (if k = 0 then W else if k = 1 then V else (∅ : Set Baire)) := by
    intro k; rcases k with _ | _ | k <;> simp_all [isOpen_empty]
  have hUfam_disj : Pairwise (Disjoint on fun k =>
      if k = 0 then W else if k = 1 then V else (∅ : Set Baire)) := by
    intro k l hkl
    rcases k with _ | _ | k <;> rcases l with _ | _ | l <;>
      simp_all [Function.onFun, Set.disjoint_left]
    all_goals tauto
  -- Step 1: the binary gluing of the two double-corestrictions reduces into `F⇂U`.
  have h1 : ScatFun.Reduces
      (ScatFun.gl (fun k => (F.coRestrict U).coRestrict
        (if k = 0 then W else if k = 1 then V else ∅))) (F.coRestrict U) :=
    ScatFun.gl_coRestrict_disjoint_open_reduces (F.coRestrict U) _ hUfam_open hUfam_disj
  have h2 : ScatFun.Reduces
      (ScatFun.glBin ((F.coRestrict U).coRestrict W) ((F.coRestrict U).coRestrict V))
      (ScatFun.gl (fun k => (F.coRestrict U).coRestrict
        (if k = 0 then W else if k = 1 then V else ∅))) := by
    refine (ScatFun.finGl_glBin_equiv_glList _ _).1.trans ?_
    refine ScatFun.gl_reduces_of_pointwise _ _ ?_
    intro k
    rcases k with _ | _ | i
    · exact ContinuouslyReduces.refl _
    · exact ContinuouslyReduces.refl _
    · have hget : ([((F.coRestrict U).coRestrict W), ((F.coRestrict U).coRestrict V)] :
          List ScatFun).getD (i + 2) ScatFun.empty = ScatFun.empty := by
        simp [List.getD]
      rw [hget]
      simp only [Nat.succ_ne_zero, if_false]
      exact ScatFun.empty_reduces _
  -- Step 2: transport each block into the double corestriction (`coRestrict_inter_reduces`).
  have h3 : ScatFun.Reduces (ScatFun.glBin (F.coRestrict W) (F.coRestrict V))
      (ScatFun.glBin ((F.coRestrict U).coRestrict W) ((F.coRestrict U).coRestrict V)) :=
    ScatFun.glBin_reduces_of_reduces
      (coRestrict_inter_reduces F hWU (Set.Subset.refl W))
      (coRestrict_inter_reduces F hVU (Set.Subset.refl V))
  exact h3.trans (h2.trans h1)

/-- **Binary lower bound into a corestriction** (memoir `Gluingaslowerbound2` combined with
`Gluingasupperbound`, `:346`). If `W, V` are disjoint clopen subsets of `U` and `a ≤ F⇂W`,
`b ≤ F⇂V`, then `a ⊕ b ≤ F⇂U`. Reusable; the second case's `w ⊕ ⋀(v ∣ gl D) ≤ F⇂U` is this
applied with `W = ⋃ W_{g'}` and `V ∋ y` disjoint from `W`. -/
theorem ScatFun.reduces_glBin_coRestrict_of_disjoint {F : ScatFun} (a b : ScatFun)
    {U W V : Set Baire} (hWcl : IsClopen W) (hVcl : IsClopen V)
    (hWU : W ⊆ U) (hVU : V ⊆ U) (hdisj : Disjoint W V)
    (ha : ScatFun.Reduces a (F.coRestrict W)) (hb : ScatFun.Reduces b (F.coRestrict V)) :
    ScatFun.Reduces (ScatFun.glBin a b) (F.coRestrict U) :=
  (ScatFun.glBin_reduces_of_reduces ha hb).trans
    (ScatFun.glBin_coRestrict_disjoint_reduces F hWU hVU hWcl.isOpen hVcl.isOpen hdisj)

/-- **Ray-shrinking convergence** — the analytic content of the `h_ranges` premise of
`ScatFun.wedge_upper_bound` in the second-case construction. If every set `S n` sits inside the
`k n`-th ray of `y` and the ray indices satisfy `k n → ∞`, then the `S n` converge to `y`
(`SetsConvergeTo`): a point of `S n` agrees with `y` on its first `k n` coordinates, and
`k n → ∞` forces agreement on any fixed prefix, i.e. eventual containment in every basic clopen
neighbourhood `nbhd y N` of `y`. This is the fact behind the memoir's "`k_n → ∞`, and in turn
`f(A^D_n) → y`" (`6_double_successor_memo.tex:374`). -/
lemma setsConvergeTo_of_subset_raySet {y : Baire} (S : ℕ → Set Baire) (k : ℕ → ℕ)
    (hsub : ∀ᶠ n in Filter.atTop, S n ⊆ RaySet Set.univ y (k n))
    (hk : Filter.Tendsto k Filter.atTop Filter.atTop) :
    SetsConvergeTo S y := by
  intro U hU hyU
  obtain ⟨N, hN⟩ := nbhd_basis y U hU hyU
  rw [Filter.tendsto_atTop_atTop] at hk
  obtain ⟨m₁, hm₁⟩ := hk N
  rw [Filter.eventually_atTop] at hsub
  obtain ⟨m₂, hm₂⟩ := hsub
  refine ⟨max m₁ m₂, fun n hn z hz => hN (fun i hi => ?_)⟩
  have hz' := hm₂ n (le_of_max_le_right hn) hz
  simp only [RaySet, Set.mem_univ, true_and, Set.mem_setOf_eq] at hz'
  exact hz'.1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) (hm₁ n (le_of_max_le_left hn)))

/-! ### The second-case left reduction `F↾A¹ ≤ ⋀(v ∣ gl D)`

The reduction is `ScatFun.wedge_upper_bound (F.restrict Aᶜ) v (glList D.toList) y` fed by an
`ℕ`-indexed disjoint union `Adiag` and ray indices `kidx` (memoir `6_double_successor_memo.tex:349-386`);
its existence is `secondCase_ray_cut_diagonal_family` (**fully proved**), built from:

* `secondCase_column_rays_reducible` — the columns clause (`:353-354`, cocenter rigidity); the low
  cocenter-`y` pieces `A¹₀` are folded into one column of rank `> λ+1` (their rays `≤ maxFun λ ≤ v i₀`);
* `secondCase_diagonal_block_reduces` — the ray-cut blocks `A^D_r`, `r ≥ 0` (`:374-378`, per-level
  finite-cocenter Vertical Theorem `≤ 2(gl D)`);
* `secondCase_residual_mopup_reduces` — the mop-up `A^D_0 = A^D ∖ W` (`:381-385`, per-piece residual
  corestriction `≤ FinGl D_g` via `ScatFun.residualCorestrict_reduces_finGl` + an `ω`-per-class
  collapse `ω(gl D_g) ≤ pglFinset D_g ≡ g`);
* ray-index convergence `kₙ → ∞` (`firstDiff_tendsto_atTop`) from strong solvability's `yₙ → y`.

**Design note (route B).**  We do *not* enumerate `Y'` as `(yₙ)`; instead we index directly by the
ray-index `r = firstDiff ȳ y_P` (`Blk r`, `SRay r`).  Since `firstDiff` is total this makes
`A^D = ⋃ᵣ Blk r` and `W = ⋃ᵣ SRay r` *automatically clopen* (relative complement in the clopen `A^D`
is `⋃ᵣ (Blk r ∖ SRay r)`, open) — dissolving the "delicate" clopen-ness of the mop-up that the
enumeration-based presentation flags. -/

/-- **A `FinGl`-member reduces to finitely many copies of `gl S`.** If `a ∈ FinGl S`, then
`a ≡ glList L` for some list `L` with entries in `S` (`exists_glList_of_finGl`); mapping each entry
(`≤ gl S` by `mem_reduces_glList`) gives `a ≤ glList (replicate |L| (gl S))`. The `FinGl → replicate`
bridge behind the columns clause; reusable. **Fully proved.** -/
theorem finGl_reduces_replicate_glList {S : Finset ScatFun} {a : ScatFun}
    (ha : a ∈ ScatFun.FinGl S.toFinFun) :
    ∃ m, ScatFun.Reduces a (ScatFun.glList (List.replicate m (ScatFun.glList S.toList))) := by
  obtain ⟨L, hLmem, haE⟩ := ScatFun.exists_glList_of_finGl ha
  refine ⟨L.length, haE.1.trans ?_⟩
  have hmap : L.map (fun _ => ScatFun.glList S.toList)
      = List.replicate L.length (ScatFun.glList S.toList) := List.map_const'
  rw [← hmap]
  exact ScatFun.glList_reduces_glList_map L (fun _ => ScatFun.glList S.toList)
    (fun w hw => ScatFun.mem_reduces_glList (Finset.mem_toList.mpr (hLmem w hw)))

/-- **Columns clause** (`6_double_successor_memo.tex:353-354`). See the section roadmap above.
**Fully proved**: the ray `G.rayOn y C j ≡ (G↾C).rayOn y univ j` (`rayOn_restrict_equiv`, with
cocenter `y` by `hcoc`) reduces into `FinGl M` (`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset`,
Prop 4.4), and `finGl_reduces_replicate_glList` turns that into `replicate m (gl M)`. -/
theorem secondCase_column_rays_reducible
    (G : ScatFun) (y : Baire) (C : Set ↑G.domain) (M : Finset ScatFun)
    (hcent : IsCentered (G.restrict C).func)
    (hcoc : cocenter (G.restrict C).func hcent = y)
    (hpgl : ScatFun.Equiv (G.restrict C) (ScatFun.pglFinset M)) :
    ∀ j : ℕ, ∃ m, ScatFun.Reduces (G.rayOn y C j)
      (ScatFun.glList (List.replicate m (ScatFun.glList M.toList))) := by
  intro j
  obtain ⟨h, hhFinGl, hhred⟩ :=
    ScatFun.rayOn_cocenter_reduces_finGl_of_equiv_pglFinset (G.restrict C) hcent M hpgl j
  rw [hcoc] at hhred
  obtain ⟨m, hmred⟩ := finGl_reduces_replicate_glList hhFinGl
  exact ⟨m, ((ScatFun.rayOn_restrict_equiv G C y j).2.trans hhred).trans hmred⟩

/-- **Single-class block reduces to two copies** (`6_double_successor_memo.tex:378-382`, the
Vertical-Theorem core of `secondCase_diagonal_fiber_reduces`). For a centered `g` of rank
`λ+1 < CB(g)` (`≤ α+2`) with a nonempty `(g, z)`-block, the block `f_{(g,z)} = F↾⋃₀blockPieces g z`
is pseudo-centered at `z`; the variable-rank Vertical Theorem (`secondCase_singleBlockData`, applied
at base point `z`) gives a clopen split `A⁰ ⊔ A¹ = ⋃₀blockPieces g z` with `F↾A⁰ ≤ gl H ≤ g` and
`F↾A¹ ≤ g`, whence `f_{(g,z)} ≤ g ⊕ g` (`reduces_glBin_of_clopen_partition`, transported into
`F.restrict` via `restrict_restrict_equiv`). **Fully proved.** -/
theorem secondCase_singleClass_fiber_reduces
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {z : Baire} (g : ScatFun)
    (hgrank : α.limitPart + 1 < CBRank g.func)
    (hne : (hA.blockPieces g z).Nonempty) :
    ScatFun.Reduces (hA.piece g z) (ScatFun.glBin g g) := by
  classical
  obtain ⟨Mg, Hf, A0, A1, hMgsub, hgMg, hHsub, hA0cl, hA1cl, hdisj, hcover,
      hA0red, hA1red, -, -, hHg, hcoreg, hW⟩ :=
    secondCase_singleBlockData α hα hFG F hFrank hA hfine g hgrank hne
  set E : Set ↑F.domain := ⋃₀ hA.blockPieces g z with hEdef
  have hA0E : A0 ⊆ E := hcover ▸ Set.subset_union_left
  have hA1E : A1 ⊆ E := hcover ▸ Set.subset_union_right
  -- Transport the ambient split `A0 ⊔ A1 = E` into `(F.restrict E).domain`.
  set A0' : Set ↑(F.restrict E).domain :=
    {w | (F.restrictEquiv E w : ↑F.domain) ∈ A0} with hA0'def
  set A1' : Set ↑(F.restrict E).domain :=
    {w | (F.restrictEquiv E w : ↑F.domain) ∈ A1} with hA1'def
  have hcont : Continuous (fun w : ↑(F.restrict E).domain => (F.restrictEquiv E w : ↑F.domain)) :=
    continuous_subtype_val.comp (F.restrictEquiv E).continuous
  -- `hA.piece g z = F.restrict E`, so it suffices to bound `F.restrict E`.
  show ScatFun.Reduces (F.restrict E) (ScatFun.glBin g g)
  refine ScatFun.reduces_glBin_of_clopen_partition (F := F.restrict E) g g
    (hA0cl.preimage hcont) (hA1cl.preimage hcont) ?_ ?_ ?_ ?_
  · -- cover: every `w` lands in `A0 ∪ A1 = E`.
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    -- The goal is defeq to membership in the union.
    change (F.restrictEquiv E w : ↑F.domain) ∈ A0 ∪ A1
    rw [hcover]
    exact (F.restrictEquiv E w).2
  · -- disjoint.
    rw [Set.disjoint_left]
    intro w hw0 hw1
    exact (Set.disjoint_left.mp hdisj) hw0 hw1
  · -- `(F↾E)↾A0' ≡ F↾A0 ≤ gl H ≤ g`.
    exact (ScatFun.restrict_restrict_equiv F E A0 hA0E).1.trans (hA0red.trans hHg)
  · -- `(F↾E)↾A1' ≡ F↾A1 ≤ g`.
    exact (ScatFun.restrict_restrict_equiv F E A1 hA1E).1.trans hA1red

/-- **A sub-union of partition pieces is clopen.** If `𝒮 ⊆ 𝒫` is any sub-collection of the
pieces of a `c`-partition, then `⋃₀ 𝒮` is clopen: it is open (a union of the clopen pieces), and
its complement in `F.domain` is `⋃₀ (𝒫 ∖ 𝒮)` — again a union of clopen pieces, hence open —
because the pieces are pairwise disjoint and cover `F.domain`. This dissolves the apparent
"delicate point" (clopen-ness of an infinite union of pieces) in the diagonal fiber. -/
theorem ScatFun.IsCPartition.sUnion_subfamily_isClopen
    {F : ScatFun} {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {𝒮 : Set (Set ↑F.domain)} (h𝒮 : 𝒮 ⊆ Part) :
    IsClopen (⋃₀ 𝒮) := by
  classical
  have hopen : IsOpen (⋃₀ 𝒮) := by
    rw [Set.sUnion_eq_iUnion]
    exact isOpen_iUnion (fun P => (hA.isClopen P.1 (h𝒮 P.2)).2)
  have hcompl : (⋃₀ 𝒮)ᶜ = ⋃₀ (Part \ 𝒮) := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      have hxuniv : x ∈ ⋃₀ Part := by rw [hA.sUnion_eq]; exact Set.mem_univ x
      obtain ⟨P, hPmem, hxP⟩ := hxuniv
      refine ⟨P, ⟨hPmem, ?_⟩, hxP⟩
      intro hP𝒮
      exact hx (Set.mem_sUnion.mpr ⟨P, hP𝒮, hxP⟩)
    · intro x hx hxS
      obtain ⟨P, hPmem, hxP⟩ := hx
      obtain ⟨Q, hQ𝒮, hxQ⟩ := hxS
      have hPQ : P = Q := by
        by_contra hne
        exact (Set.disjoint_left.mp
          (hA.pairwiseDisjoint hPmem.1 (h𝒮 hQ𝒮) hne)) hxP hxQ
      exact hPmem.2 (hPQ ▸ hQ𝒮)
  have hclosed : IsClosed (⋃₀ 𝒮) := by
    rw [← isOpen_compl_iff, hcompl, Set.sUnion_eq_iUnion]
    exact isOpen_iUnion (fun P => (hA.isClopen P.1 P.2.1).2)
  exact ⟨hclosed, hopen⟩

/-- **Realization bookkeeping.** The value of `F↾P` at the transport of a realized point
`v ∈ P` (through `(F.restrictEquiv P).symm`) is just `F.func v`. -/
lemma ScatFun.restrict_func_restrictEquiv_symm (F : ScatFun) (P : Set ↑F.domain)
    (v : ↑F.domain) (hv : v ∈ P) :
    (F.restrict P).func ((F.restrictEquiv P).symm ⟨v, hv⟩) = F.func v := by
  show F.func (((F.restrictEquiv P) ((F.restrictEquiv P).symm ⟨v, hv⟩) : ↑F.domain)) = F.func v
  rw [Homeomorph.apply_symm_apply]

/-- **Centered localization into a union of open pieces.** If a *centered* `c` reduces into
`F↾⋃₀S` (`S` a family of open pieces), it already reduces into a single `F↾P`, `P ∈ S`: the
image of a center of `c` lands in some piece `P`, and center invariance
(`centerInvariance_reduce`, memoir Fact 4.2 `Centerinvariance`) pushes the whole reduction
into the (open) preimage of `P`, which `restrict_restrict_equiv` identifies with `F↾P`. This
is the formal counterpart of the informal "a centered function reducing into a disjoint union
reduces into one block". Reusable. -/
theorem ScatFun.centered_reduces_restrict_of_reduces_restrict_sUnion
    {F : ScatFun} {S : Set (Set ↑F.domain)} (hopen : ∀ P ∈ S, IsOpen P)
    {c : ScatFun} (hc : IsCentered c.func)
    (hred : ScatFun.Reduces c (F.restrict (⋃₀ S))) :
    ∃ P ∈ S, ScatFun.Reduces c (F.restrict P) := by
  classical
  obtain ⟨x, hx⟩ := hc
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred
  -- The realization of `σ x` in `F.domain` lies in some piece `P ∈ S`.
  obtain ⟨P, hPS, hxP⟩ : ∃ P ∈ S, ((F.restrictEquiv (⋃₀ S)) (σ x) : ↑F.domain) ∈ P :=
    ((F.restrictEquiv (⋃₀ S)) (σ x)).2
  refine ⟨P, hPS, ?_⟩
  -- `P` transported into `(F↾⋃₀S).domain` is open and contains `σ x`.
  have hUopen : IsOpen {w : ↑(F.restrict (⋃₀ S)).domain |
      ((F.restrictEquiv (⋃₀ S)) w : ↑F.domain) ∈ P} :=
    (hopen P hPS).preimage
      (continuous_subtype_val.comp (F.restrictEquiv (⋃₀ S)).continuous)
  -- Center invariance pushes the reduction into that open set, i.e. into `(F↾⋃₀S)↾U ≡ F↾P`.
  have h2 : ScatFun.Reduces c ((F.restrict (⋃₀ S)).restrict
      {w : ↑(F.restrict (⋃₀ S)).domain | ((F.restrictEquiv (⋃₀ S)) w : ↑F.domain) ∈ P}) :=
    (centerInvariance_reduce hx hσ hτ heq hUopen hxP).comp_homeomorph_right _
  exact h2.trans
    (ScatFun.restrict_restrict_equiv F (⋃₀ S) P (Set.subset_sUnion_of_mem hPS)).1

/-- **Single-class block, rank `λ+1` (the single-successor case).** For a class `g` of rank
exactly `λ+1` whose `(g, z)`-block is nonempty, the block `f_{(g,z)} = F↾⋃₀blockPieces g z`
reduces to `g ⊕ g`. This is the boundary case that the double-successor Vertical Theorem
(`secondCase_singleClass_fiber_reduces`, hence `verticalTheorem'`) cannot treat, since `ρ = λ+1`
is a successor of the limit `λ`, not a double successor.

## Proof (and how it differs from the earlier scaffold)

Every piece of the block is `≡ g`, centered with cocenter `z`, of rank `λ+1`; hence the block
`G' = f_{(g,z)}` has rank `λ+1` (`cbRank_restrict_sUnion_const`) and is **simple with
distinguished point `z`** (the direct Prop 4.11 argument, `Simpleiffcoincidenceofcocenters`:
each point of the top CB-level lies in the top level of its piece, where the piece is
constantly its cocenter `z`, `block_const_on_top`). Then:

* `λ = 0`: rank-`1` pieces are locally constant and centered, hence constantly `z`; so `G'`
  is the constant function `z` and reduces into any single piece (`≡ g`) by a
  constant/identity pair.
* `λ` a nonzero limit: classify `G'` by Theorem 4.12 (`simpleFunctionsLambdaPlusOne`, with
  2-BQO below `λ` from `hFG`):
  - `G' ≡ k_{λ+1}`: `k_{λ+1} ≤ g` (`minFun_is_minimum`, since `CB(g) = λ+1`), so
    `G' ≤ g ≤ g ⊕ g`;
  - `G' ≡ k_{λ+1} ⊕ ℓ_λ`: componentwise `k_{λ+1} ≤ g` and `ℓ_λ ≤ g`
    (`maxFun_reduces_of_lam_lt_rank`, `λ < CB(g)`), so `G' ≤ g ⊕ g`
    (`glBin_reduces_of_reduces`);
  - `G' ≡ pgl ℓ_λ`: `pgl ℓ_λ` is centered and reduces into `G'`, hence into a *single* piece
    (`centered_reduces_restrict_of_reduces_restrict_sUnion`), which is `≡ g`; so
    `G' ≤ pgl ℓ_λ ≤ F↾P ≤ g ≤ g ⊕ g`.

**Why not `G' ≤ g` (the earlier scaffolded intermediate)?** That claim is false in general: in
the middle case a block whose pieces are all `≡ k_{λ+1}` with common cocenter `z` can have
`y`-rays of rank exactly `λ` (the ranks of the pieces' rays at a fixed ray index can be
unbounded below `λ` across the infinitely many pieces), and then `G' ≡ k_{λ+1} ⊕ ℓ_λ ⋦
k_{λ+1} ≡ g`, while `G' ≤ g ⊕ g` still holds because `ℓ_λ ≤ k_{λ+1}`. This is consistent with
fineness: `𝒲`-regularity of the block at `z` only forces the set of rank-`λ` ray indices to be
empty or infinite. The memoir elides this boundary case by quoting the Vertical Theorem at all
ranks (`6_double_successor_memo.tex:376`); the `≤ 2g` (not `≤ g`) target is what makes the
statement true. -/
theorem secondCase_block_reduces_glBin_lowRank
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (_hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (_hfine : hA.IsFine α.limitPart)
    {z : Baire} (g : ScatFun)
    (hrank : CBRank g.func = α.limitPart + 1)
    (hne : (hA.blockPieces g z).Nonempty) :
    ScatFun.Reduces (hA.piece g z) (ScatFun.glBin g g) := by
  classical
  set lam := α.limitPart with hlam_def
  have hlam_le : lam ≤ α := by
    rw [hlam_def]
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  have hlam_lt : lam < omega1 := lt_of_le_of_lt hlam_le hα
  set E : Set ↑F.domain := ⋃₀ hA.blockPieces g z with hEdef
  have hEopen : IsOpen E :=
    isOpen_sUnion fun P hP => (hA.isClopen P hP.choose).isOpen
  -- Every block piece is `≡ g`, hence of rank `λ+1`; so is the whole block.
  have hrankP : ∀ P ∈ hA.blockPieces g z, CBRank (F.restrict P).func = lam + 1 :=
    fun P hP => (cbRank_eq_of_equiv hP.choose_spec.1).trans hrank
  have hrankE : CBRank (F.restrict E).func = lam + 1 :=
    cbRank_restrict_sUnion_const (hA.countable.mono fun P hP => hP.choose)
      (fun P hP => hA.isClopen P hP.choose) hne hrankP
  show ScatFun.Reduces (F.restrict E) (ScatFun.glBin g g)
  rcases Ordinal.limitPart_isLimit_or_zero α with hlim | hzero
  · -- **`λ` a nonzero limit.** Classify the block among the three simple rank-`λ+1` classes.
    -- 2-BQO below `λ`, from finite generation below `α+2` (`λ ≤ α < α+2`).
    have hbqo : TwoBQO (ScatFun.LevelLT.reduces lam) :=
      ScatFun.LevelLT.isTwoBQO_of_FG_below
        (ScatFun.FGBelow.mono
          (hlam_le.trans (by rw [add_assoc]; exact le_self_add)) hFG)
    have hsucc : CBRank (F.restrict E).func = Order.succ lam := by
      rw [hrankE, Ordinal.add_one_eq_succ]
    -- The block is *simple* with distinguished point `z` (the Prop 4.11 argument): each
    -- top-level point lies in the top CB-level of its piece, where the piece — centered of
    -- rank `λ+1` with cocenter `z` — takes the value `z` (`block_const_on_top`).
    have hconst_top : ∀ x ∈ CBLevel (F.restrict E).func lam, (F.restrict E).func x = z := by
      intro x hx
      have hx' : ((F.restrictEquiv E) x : ↑F.domain) ∈ CBLevel F.func lam :=
        (cbLevel_block_iff F E hEopen lam x).mp hx
      obtain ⟨P, hPS, hxP⟩ : ∃ P ∈ hA.blockPieces g z,
          ((F.restrictEquiv E) x : ↑F.domain) ∈ P := ((F.restrictEquiv E) x).2
      have hPrank : CBRank (F.restrict P).func = Order.succ lam := by
        rw [hrankP P hPS, Ordinal.add_one_eq_succ]
      have hw : (F.restrictEquiv P).symm ⟨_, hxP⟩ ∈ CBLevel (F.restrict P).func lam := by
        rw [cbLevel_block_iff F P (hA.isClopen P hPS.choose).isOpen lam,
          Homeomorph.apply_symm_apply]
        exact hx'
      have hval := block_const_on_top (F.restrict P) (hA.centered P hPS.choose) lam hPrank
        _ hw
      have hEx : (F.restrict E).func x = F.func ((F.restrictEquiv E) x : ↑F.domain) := rfl
      rw [hEx, ← ScatFun.restrict_func_restrictEquiv_symm F P _ hxP, hval]
      exact hPS.choose_spec.2
    have hsimple : SimpleFun (F.restrict E).func :=
      ⟨lam,
        CBLevel_nonempty_below_rank _ (F.restrict E).hScat lam
          (by rw [hsucc]; exact Order.lt_succ lam),
        by rw [← hsucc]; exact cbLevel_at_cbRank_empty _ (F.restrict E).hScat,
        z, hconst_top⟩
    -- `k_{λ+1} ≤ g` and `ℓ_λ ≤ g` (as `CB(g) = λ+1 > λ`).
    have hrank_lt : lam < CBRank g.func := by
      rw [hrank, Ordinal.add_one_eq_succ]; exact Order.lt_succ lam
    have hming : ScatFun.Reduces (ScatFun.minFun lam hlam_lt) g := by
      show ContinuouslyReduces (ScatFun.minFun lam hlam_lt).func g.func
      rw [ScatFun.minFun_func]
      exact minFun_is_minimum lam hlam_lt g.domain g.func g.hCont g.hScat
        (CBLevel_nonempty_below_rank g.func g.hScat lam hrank_lt)
    have hmaxg : ScatFun.Reduces (ScatFun.maxFun lam hlam_lt) g :=
      ScatFun.maxFun_reduces_of_lam_lt_rank hlam_lt hlim g hrank_lt
    rcases simpleFunctionsLambdaPlusOne lam hlam_lt (Or.inr ⟨hlim, hlim.ne_bot⟩) hbqo
        (F.restrict E) hrankE hsimple with hmin | hGl | hmax
    · -- `G' ≡ k_{λ+1} ≤ g ≤ g ⊕ g`.
      exact (hmin.1.trans hming).trans (ScatFun.reduces_glBin_left g g)
    · -- `G' ≡ k_{λ+1} ⊕ ℓ_λ ≤ g ⊕ g` componentwise — the case the naive `G' ≤ g` misses.
      exact hGl.1.trans (ScatFun.glBin_reduces_of_reduces hming hmaxg)
    · -- `G' ≡ pgl ℓ_λ`: localize the centered `pgl ℓ_λ` into a single piece `≡ g`.
      have hsm_cent : IsCentered (ScatFun.succMaxFun lam hlam_lt).func :=
        ⟨_, succMaxFun_base_isCenter lam hlam_lt⟩
      obtain ⟨P, hPS, hPred⟩ :=
        ScatFun.centered_reduces_restrict_of_reduces_restrict_sUnion
          (S := hA.blockPieces g z)
          (fun P hP => (hA.isClopen P hP.choose).isOpen) hsm_cent hmax.2
      exact ((hmax.1.trans hPred).trans hPS.choose_spec.1.1).trans
        (ScatFun.reduces_glBin_left g g)
  · -- **`λ = 0`.** Rank-`1` pieces are locally constant and centered, hence constantly `z`;
    -- the whole block is the constant `z` and reduces into any single piece `≡ g`.
    have hzero' : lam = 0 := hlam_def.trans hzero
    have hconstP : ∀ P (hP : P ∈ hA.blockPieces g z) (w : ↑(F.restrict P).domain),
        (F.restrict P).func w = z := by
      intro P hP w
      have hlc : IsLocallyConstant (F.restrict P).func :=
        isLocallyConstant_of_cbRank_le_one _
          (le_of_eq (by rw [hrankP P hP, hzero', zero_add]))
      obtain ⟨x, hx⟩ := hA.centered P hP.choose
      -- A centered locally-constant function is constant …
      have hval : ∀ v, (F.restrict P).func v = (F.restrict P).func x := by
        intro v
        obtain ⟨σ, hσ, τ, hτ, heq⟩ := hx
          ((F.restrict P).func ⁻¹' {(F.restrict P).func x}) (hlc _) rfl
        have hτx : ∀ a, (F.restrict P).func a = τ ((F.restrict P).func x) := by
          intro a
          have h := heq a
          simp only [Function.comp_apply] at h
          rwa [show (F.restrict P).func ((σ a) : ↑(F.restrict P).domain)
            = (F.restrict P).func x from (σ a).2] at h
        rw [hτx v, ← hτx x]
      -- … equal to its cocenter, which is `z`.
      rw [hval w, ← hP.choose_spec.2]
      exact (hval (hA.centered P hP.choose).choose).symm
    have hconstE : ∀ w : ↑(F.restrict E).domain, (F.restrict E).func w = z := by
      intro w
      obtain ⟨P, hPS, hwP⟩ : ∃ P ∈ hA.blockPieces g z,
          ((F.restrictEquiv E) w : ↑F.domain) ∈ P := ((F.restrictEquiv E) w).2
      have hEw : (F.restrict E).func w = F.func ((F.restrictEquiv E) w : ↑F.domain) := rfl
      rw [hEw, ← ScatFun.restrict_func_restrictEquiv_symm F P _ hwP]
      exact hconstP P hPS _
    obtain ⟨P₀, hP₀⟩ := hne
    -- Reduce the constant block into the (nonempty, `≡ g`) piece `P₀` by a constant `σ` and
    -- the identity `τ`.
    have hx₀ := (hA.centered P₀ hP₀.choose).choose
    have hredP₀ : ScatFun.Reduces (F.restrict E) (F.restrict P₀) :=
      ⟨fun _ => hx₀, continuous_const, id, continuousOn_id, fun w => by
        rw [hconstE w, id_eq]; exact (hconstP P₀ hP₀ hx₀).symm⟩
    exact (hredP₀.trans hP₀.choose_spec.1.1).trans (ScatFun.reduces_glBin_left g g)

/-- **Single-class block reduces to two copies, both rank cases.** For any class `g` whose
`(g, z)`-block is nonempty, `f_{(g,z)} ≤ g ⊕ g`. Splits on `CB(g)`: the double-successor case
`λ+1 < CB(g)` is `secondCase_singleClass_fiber_reduces` (Vertical Theorem); the boundary case
`CB(g) = λ+1` (forced by fineness `CB(g) > λ`) is `secondCase_block_reduces_glBin_lowRank`. -/
theorem secondCase_block_reduces_glBin
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {z : Baire} (g : ScatFun)
    (hne : (hA.blockPieces g z).Nonempty) :
    ScatFun.Reduces (hA.piece g z) (ScatFun.glBin g g) := by
  by_cases h : α.limitPart + 1 < CBRank g.func
  · exact secondCase_singleClass_fiber_reduces α hα hFG F hFrank hA hfine g h hne
  · obtain ⟨P₀, hP₀mem, hP₀eq, hP₀coc⟩ := hne
    have hgt : α.limitPart < CBRank g.func := by
      rw [← cbRank_eq_of_equiv hP₀eq]; exact hfine.2 P₀ hP₀mem
    have hle1 : α.limitPart + 1 ≤ CBRank g.func := Order.add_one_le_iff.mpr hgt
    have hrank : CBRank g.func = α.limitPart + 1 :=
      le_antisymm (not_lt.mp h) hle1
    exact secondCase_block_reduces_glBin_lowRank α hα hFG F hFrank hA hfine g hrank
      ⟨P₀, hP₀mem, hP₀eq, hP₀coc⟩

/-
**Single-cocenter diagonal fiber** (`6_double_successor_memo.tex:378-382`, the `n > 0`
blocks). If a clopen `E ⊆ F.domain` meets only pieces of a common cocenter `z ≠ y`, then `F↾E`
reduces to finitely many copies of `gl D`. Partition `E = ⊔_{g ∈ D} E_g` by which class `g ∈ D`
the piece is `≡` to (`hDrep`; the clopen-ness of each `E_g`, an infinite union of piece∩E, is the
delicate point), reduce each single-class block by `secondCase_singleClass_fiber_reduces`
(`F↾E_g ≤ 2g`), and assemble over the finite `D` (`scatFun_reduces_gl_of_domain_partition` +
`finGl_reduces_replicate_glList`). This is the `h_diag` reduction for a ray-cut block `A^D_n`
(`n > 0`). **Fully proved** (via `secondCase_block_reduces_glBin`, whose boundary rank-`λ+1`
case is `secondCase_block_reduces_glBin_lowRank`).
-/
theorem secondCase_diagonal_fiber_reduces
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {y z : Baire} (hzy : z ≠ y) (D : Finset ScatFun)
    (hDrep : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g)
    (E : Set ↑F.domain)
    (hEfiber : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), (P ∩ E).Nonempty → hA.cocenterOf hP = z) :
    ∃ m, ScatFun.Reduces (F.restrict E)
      (ScatFun.glList (List.replicate m (ScatFun.glList D.toList))) := by
  classical
  set n := D.toList.length with hn
  set gof : Fin n → ScatFun := fun k => D.toList.get k with hgof
  set S : Fin n → Set ↑F.domain := fun k => ⋃₀ hA.blockPieces (gof k) z with hS
  have hScl : ∀ k, IsClopen (S k) := fun k =>
    ScatFun.IsCPartition.sUnion_subfamily_isClopen hA (fun P hP => hP.1)
  set Q : Fin n → Set ↑F.domain := fun k => S k \ ⋃ (j : Fin n) (_ : j.val < k.val), S j
    with hQ
  have hQcl : ∀ k, IsClopen (Q k) := by
    intro k
    refine' (hScl k).diff _
    exact isClopen_iUnion_of_finite fun j => isClopen_iUnion_of_finite fun _ => hScl j
  have hQdisj : Pairwise (Disjoint on Q) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · refine' Set.disjoint_left.mpr (fun x hxk hxl => _)
      exact hxl.2 (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨h, hxk.1⟩⟩)
    · refine' Set.disjoint_left.mpr (fun x hxk hxl => _)
      exact hxk.2 (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨h, hxl.1⟩⟩)
  have hQE : E ⊆ ⋃ k, Q k := by
    intro x hx
    obtain ⟨P, hPmem, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
      hA.sUnion_eq.symm.subset (Set.mem_univ x)
    have hcoc : hA.cocenterOf hPmem = z := hEfiber P hPmem ⟨x, hxP, hx⟩
    obtain ⟨g, hgD, hg⟩ := hDrep P hPmem (hcoc ▸ hzy)
    obtain ⟨k, hk⟩ : ∃ k : Fin n, gof k = g := by
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hgD)
      exact ⟨k, hk⟩
    have hxSk : x ∈ S k := ⟨P, ⟨hPmem, hk ▸ hg, hcoc⟩, hxP⟩
    set I : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ S i) with hI
    have hIne : I.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxSk⟩⟩
    set k₀ := I.min' hIne with hk₀
    have hk₀I : k₀ ∈ I := I.min'_mem hIne
    have hxSk₀ : x ∈ S k₀ := (Finset.mem_filter.mp hk₀I).2
    refine Set.mem_iUnion.mpr ⟨k₀, hxSk₀, ?_⟩
    intro hxlow
    obtain ⟨j, hj, hxj⟩ : ∃ j : Fin n, j.val < k₀.val ∧ x ∈ S j := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxlow
      obtain ⟨hjlt, hxj⟩ := Set.mem_iUnion.mp hj
      exact ⟨j, hjlt, hxj⟩
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩
    exact absurd (I.min'_le j hjI) (not_le.mpr hj)
  have hpiece : ∀ k, ∃ m ∈ ScatFun.FinGl D.toFinFun, ScatFun.Reduces (F.restrict (Q k)) m := by
    intro k
    by_cases hblock : (hA.blockPieces (gof k) z).Nonempty;
    · have hblock_reduces : ScatFun.Reduces (F.restrict (⋃₀ hA.blockPieces (gof k) z)) (ScatFun.glBin (gof k) (gof k)) := by
        convert secondCase_block_reduces_glBin α hα hFG F hFrank hA hfine ( gof k ) hblock using 1;
      have hblock_reduces : ScatFun.Reduces (F.restrict (Q k)) (ScatFun.glBin (gof k) (gof k)) := by
        have hblock_reduces : ScatFun.Reduces (F.restrict (Q k)) (F.restrict (⋃₀ hA.blockPieces (gof k) z)) := by
          apply restrict_reduces_of_subset;
          exact fun x hx => hx.1;
        exact hblock_reduces.trans ‹_›;
      have hblock_reduces : gof k ∈ ScatFun.FinGl D.toFinFun := by
        have hblock_reduces : gof k ∈ D := by
          exact Finset.mem_toList.mp ( List.get_mem _ _ );
        convert ScatFun.finGl_of_equiv_glList ( L := [ gof k ] ) _ _;
        · aesop;
        · convert ScatFun.glList_single_equiv ( gof k ) using 1;
      have hblock_reduces : ScatFun.glBin (gof k) (gof k) ∈ ScatFun.FinGl D.toFinFun := by
        exact ScatFun.finGl_glBin_mem hblock_reduces hblock_reduces;
      exact ⟨ _, hblock_reduces, by assumption ⟩;
    · have hbe : hA.blockPieces (gof k) z = ∅ := Set.not_nonempty_iff_eq_empty.mp hblock
      have hQk_empty : Q k = ∅ := by
        simp only [hQ, hS, hbe, Set.sUnion_empty, Set.empty_diff]
      refine ⟨ScatFun.empty, ScatFun.empty_mem_FinGl _ ⟨fun x => x.2⟩, ?_⟩
      apply ScatFun.reduces_of_isEmpty_domain
      rw [hQk_empty]
      exact Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])
  have h_union : ScatFun.Reduces (F.restrict E) (F.restrict (⋃ k, Q k)) :=
    restrict_reduces_of_subset F hQE
  have h_finGl : ∃ hh ∈ ScatFun.FinGl D.toFinFun, ScatFun.Reduces (F.restrict (⋃ k, Q k)) hh := by
    apply ScatFun.reduces_finGl_of_finite_union Q hQcl hQdisj D hpiece;
  exact finGl_reduces_replicate_glList h_finGl.choose_spec.1 |> fun ⟨ m, hm ⟩ => ⟨ m, h_union.trans h_finGl.choose_spec.2 |> fun h => h.trans hm ⟩

/-- **Enumeration of `Y' = Y_𝒫 ∖ {y}` converging to `y`** (`6_double_successor_memo.tex:367`,
the combinatorial core of the diagonal construction). Given strong solvability at `y` and a piece
of cocenter `≠ y`, the (infinite, `cocenterSet_diff_singleton_infinite`) set `Y'` — whose sole
accumulation point is `y` (`accPt_cocenterSet_iff`, strong-solvability clause 1: every clopen
`V ∋ y` omits only finitely many cocenters) — admits an **injective** enumeration `yₙ → y`.
The ray indices `kₙ = firstDiff y yₙ` then satisfy `kₙ → ∞` (`firstDiff_tendsto_atTop`) with
`yₙ ∈ RaySet y kₙ` (`firstDiff_mem_raySet`), feeding the `A^D_n` ray-cut. Self-contained
(pure enumeration of a countable discrete-away-from-`y` set); the fibers/cuts are built on top of
`yseq` in the assembly. **Fully proved.** -/
theorem secondCase_diagonal_enumeration
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} {lam : Ordinal.{0}} (hss : hA.IsStronglySolvableAt lam y)
    (hne : ∃ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y) :
    ∃ yseq : ℕ → Baire,
      Function.Injective yseq ∧
      (∀ n, yseq n ∈ hA.cocenterSet ∧ yseq n ≠ y) ∧
      Filter.Tendsto yseq Filter.atTop (nhds y) ∧
      Filter.Tendsto (fun n => firstDiff y (yseq n)) Filter.atTop Filter.atTop := by
  classical
  set Y : Set Baire := hA.cocenterSet \ {y} with hYdef
  have hYinf : Y.Infinite := hss.cocenterSet_diff_singleton_infinite hne
  -- `Y ∩ nbhd y N` is infinite for every `N` (strong-solvability clause 1: `cocenterSet ∖ nbhd y N`
  -- is finite, so `Y` loses only finitely many points inside `nbhd y N`).
  have hcofin : ∀ N, (Y ∩ nbhd y N).Infinite := by
    intro N
    have hfin : (hA.cocenterSet \ nbhd y N).Finite :=
      (hss.2.2 (nbhd y N) (baire_nbhd_isClopen y N) (fun i _ => rfl)).1
    intro hInterFin
    refine hYinf (Set.Finite.subset (hInterFin.union hfin) (fun x hx => ?_))
    by_cases hxN : x ∈ nbhd y N
    · exact Or.inl ⟨hx, hxN⟩
    · exact Or.inr ⟨hx.1, hxN⟩
  -- A point of `Y ∩ nbhd y N` avoiding a given finite exclusion set.
  have hpick : ∀ (N : ℕ) (excl : Finset Baire), ∃ p, p ∈ Y ∩ nbhd y N ∧ p ∉ excl := by
    intro N excl
    obtain ⟨p, hp⟩ := ((hcofin N).diff excl.finite_toSet).nonempty
    exact ⟨p, hp.1, fun h => hp.2 (Finset.mem_coe.mpr h)⟩
  -- Recursively build the sequence together with its accumulated finset of used values.
  set step : ℕ → Baire × Finset Baire := fun n => Nat.rec
    ((hpick 0 ∅).choose, {(hpick 0 ∅).choose})
    (fun n prev => ((hpick (n + 1) prev.2).choose, insert (hpick (n + 1) prev.2).choose prev.2))
    n with hstep
  set yseq : ℕ → Baire := fun n => (step n).1 with hyseqdef
  have hnotin : ∀ n, yseq (n + 1) ∉ (step n).2 := fun n =>
    (hpick (n + 1) (step n).2).choose_spec.2
  have hself : ∀ n, yseq n ∈ (step n).2 := by
    intro n; cases n with
    | zero => exact Finset.mem_singleton_self _
    | succ k => exact Finset.mem_insert_self _ _
  have hmem_le : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → yseq m ∈ (step n).2 := by
    intro n
    induction n with
    | zero => intro m hm; rw [Nat.le_zero.mp hm]; exact hself 0
    | succ k ih =>
      intro m hm
      rcases eq_or_lt_of_le hm with h | h
      · subst h; exact hself (k + 1)
      · exact Finset.mem_insert_of_mem (ih m (Nat.lt_succ_iff.mp h))
  have hinj : Function.Injective yseq := by
    have key : ∀ a b, a < b → yseq a ≠ yseq b := by
      intro a b hab hEq
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      exact hnotin k (hEq ▸ hmem_le k a (by omega))
    intro m n hmn
    rcases lt_trichotomy m n with h | h | h
    · exact absurd hmn (key m n h)
    · exact h
    · exact absurd hmn.symm (key n m h)
  -- Every term lies in `Y ∩ nbhd y n`.
  have hyseq_mem : ∀ n, yseq n ∈ Y ∩ nbhd y n := by
    intro n; cases n with
    | zero => exact (hpick 0 ∅).choose_spec.1
    | succ k => exact (hpick (k + 1) (step k).2).choose_spec.1
  have hne_y : ∀ n, yseq n ≠ y := fun n => (hyseq_mem n).1.2
  -- Convergence `yₙ → y`: `yₙ ∈ nbhd y n ⊆ nbhd y N` for `n ≥ N`, and `nbhd y N` is a basis.
  have hconv : Filter.Tendsto yseq Filter.atTop (nhds y) := by
    rw [tendsto_atTop_nhds]
    intro U hyU hUopen
    obtain ⟨N, hN⟩ := nbhd_basis y U hUopen hyU
    refine ⟨N, fun n hn => hN (fun i hi => ?_)⟩
    exact (hyseq_mem n).2 i (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hn))
  exact ⟨yseq, hinj, fun n => ⟨(hyseq_mem n).1.1, hne_y n⟩, hconv,
    firstDiff_tendsto_atTop hconv hne_y⟩

/-- **Finite-cocenter diagonal block** — the multi-cocenter generalization of
`secondCase_diagonal_fiber_reduces`. If every piece meeting `E` has cocenter in a *finite* set
`Z` of points `≠ y`, then `F↾E` reduces to finitely many copies of `gl D` (memoir `:378-382`,
applied here per ray-index level `Y_r = {y_P | firstDiff y y_P = r}`, which is finite by strong
solvability). Proof: enumerate `Z` injectively; apply the single-cocenter fiber reduction
(`secondCase_diagonal_fiber_reduces`) to each cocenter fibre `A_z = ⋃₀{P | y_P = z}` (`≤ 2(gl D)`,
which lies in `FinGl D`), and glue the finitely many disjoint clopen fibres covering `E`
(`ScatFun.reduces_finGl_of_finite_union`). **Fully proved.** -/
theorem secondCase_diagonal_block_reduces
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {y : Baire} (D : Finset ScatFun)
    (hDrep : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g)
    (Z : Set Baire) (hZfin : Z.Finite) (hZne : ∀ z ∈ Z, z ≠ y)
    (E : Set ↑F.domain)
    (hEfiber : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), (P ∩ E).Nonempty →
      hA.cocenterOf hP ∈ Z) :
    ∃ m, ScatFun.Reduces (F.restrict E)
      (ScatFun.glList (List.replicate m (ScatFun.glList D.toList))) := by
  classical
  -- `glList (replicate m (gl D)) ∈ FinGl D`.
  have hglD_mem : ScatFun.glList D.toList ∈ ScatFun.FinGl D.toFinFun :=
    ScatFun.finGl_of_equiv_glList (fun w hw => Finset.mem_toList.mp hw) (ScatFun.Equiv.refl _)
  have hrep_mem : ∀ m, ScatFun.glList (List.replicate m (ScatFun.glList D.toList)) ∈
      ScatFun.FinGl D.toFinFun := fun m =>
    ScatFun.finGl_glList_of_forall_finGl (fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact hglD_mem)
  -- Injective enumeration of the finite cocenter set `Z`.
  set N := hZfin.toFinset.card with hN_def
  set e : Fin N → Baire := fun k => (hZfin.toFinset.equivFin.symm k : Baire) with he_def
  have hei : Function.Injective e := fun a b hab =>
    hZfin.toFinset.equivFin.symm.injective (Subtype.ext hab)
  have heZ : ∀ k, e k ∈ Z := fun k =>
    hZfin.mem_toFinset.mp (hZfin.toFinset.equivFin.symm k).2
  have hes : ∀ z ∈ Z, z ∈ Set.range e := fun z hz =>
    ⟨hZfin.toFinset.equivFin ⟨z, hZfin.mem_toFinset.mpr hz⟩, by simp [he_def]⟩
  -- The cocenter-`e k` fibres.
  set Q : Fin N → Set ↑F.domain :=
    fun k => ⋃₀ {P | ∃ hP : P ∈ Part, hA.cocenterOf hP = e k} with hQ_def
  have hQcl : ∀ k, IsClopen (Q k) := fun k =>
    hA.sUnion_subfamily_isClopen (fun P hP => hP.choose)
  have hQdisj : Pairwise (Disjoint on Q) := by
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨P, ⟨hP, hPc⟩, hxP⟩ ⟨P', ⟨hP', hP'c⟩, hxP'⟩
    have hPP' : P = P' := by
      by_contra hPP'
      exact (Set.disjoint_left.mp (hA.pairwiseDisjoint hP hP' hPP')) hxP hxP'
    subst hPP'
    exact hkl (hei (hPc.symm.trans hP'c))
  -- Each fibre reduces into `FinGl D`.
  have hpiece : ∀ k, ∃ m ∈ ScatFun.FinGl D.toFinFun, ScatFun.Reduces (F.restrict (Q k)) m := by
    intro k
    obtain ⟨m, hm⟩ := secondCase_diagonal_fiber_reduces α hα hFG F hFrank hA hfine
      (hZne (e k) (heZ k)) D hDrep (Q k) (by
        rintro P hP ⟨x, hxP, hxQ⟩
        obtain ⟨P', ⟨hP', hP'c⟩, hxP'⟩ := hxQ
        have hPP' : P = P' := by
          by_contra hPP'
          exact (Set.disjoint_left.mp (hA.pairwiseDisjoint hP hP' hPP')) hxP hxP'
        subst hPP'; exact hP'c)
    exact ⟨_, hrep_mem m, hm⟩
  -- `E` is covered by the fibres (every piece meeting `E` has cocenter in `Z`).
  have hQE : E ⊆ ⋃ k, Q k := by
    intro x hx
    obtain ⟨P, hPmem, hxP⟩ : ∃ P ∈ Part, x ∈ P := hA.sUnion_eq.symm.subset (Set.mem_univ x)
    obtain ⟨k, hk⟩ := hes _ (hEfiber P hPmem ⟨x, hxP, hx⟩)
    exact Set.mem_iUnion.mpr ⟨k, P, ⟨hPmem, hk.symm⟩, hxP⟩
  obtain ⟨hh, hhmem, hhred⟩ := ScatFun.reduces_finGl_of_finite_union Q hQcl hQdisj D hpiece
  obtain ⟨m, hm⟩ := finGl_reduces_replicate_glList hhmem
  exact ⟨m, ((restrict_reduces_of_subset F hQE).trans hhred).trans hm⟩

/-- **Residual corestriction of a centered function reduces into `FinGl G`** — the *reduction*
half of memoir Cor 4.6 (`ResidualCorestrictionOfCentered`, `4_centered_memo.tex:126`; the repo's
`residualCorestrictionOfCentered` in `Theorems.lean` only extracts the *centeredness* half). If
`P` is centered with `P ≡ pglFinset G`, then for any codomain set `V` covered by finitely many
rays of `P`'s cocenter `c = cocenter P.func`, the corestriction `P⇂V` reduces into `FinGl G`.

Proof (the memoir's): each ray `P.rayOn c univ n ≤ FinGl G` by Prop 4.4
(`rayOn_cocenter_reduces_finGl_of_equiv_pglFinset`); `V ⊆ ⋃_{n<M} RaySet c n` makes
`P⇂V ≤ P.restrict (⋃_{n<M} rays)`, a finite disjoint clopen union whose blocks are exactly the
rays, so `reduces_finGl_of_finite_union` collects them into a single `FinGl G` member.

This is the analytic core of the second-case mop-up block `A^D_0` (`:381-385`): for a diagonal
piece `P ≡ g = pglFinset D_g`, the residual `f↾(P ∩ A^D_0) = (f↾P)⇂(B ∖ ray_{ȳ,k})` has its
codomain window `V = (RaySet ȳ k)ᶜ` covered by the rays `⋃_{n≤k} RaySet y_P n` of `P`'s own
cocenter `y_P` (since `y_P ∈ RaySet ȳ k`, any point closer to `y_P` than coordinate `k` lands in
`RaySet ȳ k`, i.e. outside `V`). Hence the residual `≤ FinGl D_g`, which the `ω`-collapse
`gl_{g∈D} ω D_g ≤ gl_{g∈D} pgl D_g ≡ gl D` then turns into `f↾A^D_0 ≤ gl D`. -/
theorem ScatFun.residualCorestrict_reduces_finGl
    (P : ScatFun) (hcent : IsCentered P.func) (G : Finset ScatFun)
    (hpgl : ScatFun.Equiv P (ScatFun.pglFinset G))
    {V : Set Baire} {M : ℕ}
    (hV : V ⊆ ⋃ n ∈ Finset.range M, RaySet Set.univ (cocenter P.func hcent) n) :
    ∃ h ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (P.coRestrict V) h := by
  classical
  set c := cocenter P.func hcent with hc
  -- The `M` ray-pieces of `P`'s domain.
  set Q : Fin M → Set ↑P.domain := fun k => {a | P.func a ∈ RaySet Set.univ c k} with hQ
  have hQcl : ∀ k, IsClopen (Q k) := fun k =>
    (isClopen_raySet c k).preimage P.hCont
  have hQdisj : Pairwise (Disjoint on Q) := by
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro a hak hal
    simp only [hQ, Set.mem_setOf_eq, RaySet, Set.mem_univ, true_and, Set.mem_setOf_eq] at hak hal
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkl) with h | h
    · exact hak.2 (hal.1 k.val h)
    · exact hal.2 (hak.1 l.val h)
  -- Each ray-piece reduces into `FinGl G` (Prop 4.4).
  have hpiece : ∀ k, ∃ m ∈ ScatFun.FinGl G.toFinFun, ScatFun.Reduces (P.restrict (Q k)) m := by
    intro k
    obtain ⟨m, hmmem, hmred⟩ :=
      ScatFun.rayOn_cocenter_reduces_finGl_of_equiv_pglFinset P hcent G hpgl k.val
    refine ⟨m, hmmem, ?_⟩
    have hru : P.rayOn c Set.univ k.val = P.restrict (Q k) := by
      rw [ScatFun.rayOn, Set.univ_inter]
    rw [← hru]; exact hmred
  obtain ⟨hh, hhmem, hhred⟩ :=
    ScatFun.reduces_finGl_of_finite_union Q hQcl hQdisj G hpiece
  refine ⟨hh, hhmem, ?_⟩
  -- `P⇂V ≤ P.restrict (⋃ Q k)` since `{a | P.func a ∈ V} ⊆ ⋃ k, Q k`.
  refine (restrict_reduces_of_subset P ?_).trans hhred
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  obtain ⟨n, hn, hray⟩ := Set.mem_iUnion₂.mp (hV ha)
  exact Set.mem_iUnion.mpr ⟨⟨n, Finset.mem_range.mp hn⟩, hray⟩

/-- **`(RaySet ȳ r)ᶜ` is covered by the low rays of any point of that ray** — the combinatorial
fact behind the mop-up residual's codomain window (`6_double_successor_memo.tex:381`). If
`z ∈ RaySet ȳ r` (so `z` agrees with `ȳ` up to `r-1` and differs at `r`), then any `w` outside
`RaySet ȳ r` differs from `z` at some coordinate `≤ r`: were `w` to agree with `z` through `r`,
it would agree with `ȳ` up to `r-1` and differ at `r` (like `z`), landing in `RaySet ȳ r`. Hence
`(RaySet ȳ r)ᶜ ⊆ ⋃_{n<r+1} RaySet z n`, so a residual avoiding `RaySet ȳ r` is covered by
finitely many rays of `z`, feeding `residualCorestrict_reduces_finGl` with cocenter `z`. -/
theorem raySet_compl_subset_lowRays (ybar z : Baire) (r : ℕ)
    (hz : z ∈ RaySet Set.univ ybar r) :
    (RaySet Set.univ ybar r)ᶜ ⊆ ⋃ n ∈ Finset.range (r + 1), RaySet Set.univ z n := by
  intro w hw
  have hwz : w ≠ z := by rintro rfl; exact hw hz
  -- `w` agrees with `z` below `firstDiff z w`.
  have hagree : ∀ k, k < firstDiff z w → w k = z k := fun k hk =>
    Classical.not_not.1 (fun hne => absurd (Nat.sInf_le hne) (not_le.mpr hk))
  have hfd_le : firstDiff z w ≤ r := by
    by_contra hgt
    push_neg at hgt
    refine hw ⟨Set.mem_univ _, fun k hk => ?_, ?_⟩
    · rw [hagree k (lt_trans hk hgt)]; exact hz.2.1 k hk
    · rw [hagree r hgt]; exact hz.2.2
  exact Set.mem_iUnion₂.mpr
    ⟨firstDiff z w, Finset.mem_range.mpr (Nat.lt_succ_of_le hfd_le),
      firstDiff_mem_raySet z w hwz⟩

/-- **ω-collapse over a countable clopen subfamily** (centered-free companion of
`ScatFun.IsCPartition.reduces_omega_of_forall_piece_le`). If `𝒮` is a countable pairwise-disjoint
clopen family of subsets of `F.domain`, and every `F↾P` (`P ∈ 𝒮`) reduces into a fixed `g`, then
`F↾(⋃₀ 𝒮) ≤ ω g`. Used for the mop-up: the residual pieces `P ∩ A^D_0` are *not* centered, so the
`IsCPartition` version does not apply — but the collapse only needs the disjoint-union structure. -/
theorem reduces_restrict_omega_of_countable_subfamily {F : ScatFun} {g : ScatFun}
    {𝒮 : Set (Set ↑F.domain)} (hcount : 𝒮.Countable)
    (hcl : ∀ P ∈ 𝒮, IsClopen P) (hdisj : 𝒮.PairwiseDisjoint id)
    (hle : ∀ P ∈ 𝒮, ScatFun.Reduces (F.restrict P) g) :
    ScatFun.Reduces (F.restrict (⋃₀ 𝒮)) (ScatFun.omega g) := by
  classical
  set U : Set ↑F.domain := ⋃₀ 𝒮 with hUdef
  set G : ScatFun := F.restrict U with hGdef
  rcases 𝒮.eq_empty_or_nonempty with h𝒮 | h𝒮
  · -- Empty family ⟹ `⋃₀ 𝒮 = ∅`, so `G` has empty domain.
    have : U = ∅ := by rw [hUdef, h𝒮]; simp
    refine ScatFun.reduces_of_isEmpty_domain ?_
    rw [hGdef]; exact Set.isEmpty_coe_sort.mpr (by rw [this]; ext x; simp [ScatFun.restrict])
  · have : Countable ↑𝒮 := hcount.to_subtype
    obtain ⟨e, he⟩ := Countable.exists_injective_nat ↑𝒮
    -- transport of a piece `P ⊆ U` into `G.domain`.
    set tp : ↑𝒮 → Set ↑G.domain :=
      fun P => {w : ↑G.domain | (F.restrictEquiv U w : ↑F.domain) ∈ P.val} with htp
    set A : ℕ → Set ↑G.domain :=
      fun n => if h : ∃ p : ↑𝒮, e p = n then tp (Classical.choose h) else ∅ with hAdef
    have hcont : Continuous (fun w : ↑G.domain => (F.restrictEquiv U w : ↑F.domain)) :=
      continuous_subtype_val.comp (F.restrictEquiv U).continuous
    have htpcl : ∀ P : ↑𝒮, IsClopen (tp P) := fun P =>
      (hcl P.val P.2).preimage hcont
    have hdu : G.IsDisjointUnion A := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        by_cases h : ∃ p : ↑𝒮, e p = i
        · simp only [hAdef, dif_pos h]; exact htpcl _
        · simp only [hAdef, dif_neg h]; exact isClopen_empty
      · intro i j hij
        by_cases hi : ∃ p : ↑𝒮, e p = i
        · by_cases hj : ∃ q : ↑𝒮, e q = j
          · simp only [hAdef, dif_pos hi, dif_pos hj]
            have hne : (Classical.choose hi).val ≠ (Classical.choose hj).val := by
              intro hval
              have : Classical.choose hi = Classical.choose hj := Subtype.ext hval
              exact hij (by rw [← Classical.choose_spec hi, ← Classical.choose_spec hj, this])
            refine' Set.disjoint_left.mpr (fun w hwi hwj => _)
            exact (Set.disjoint_left.mp
              (hdisj (Classical.choose hi).2 (Classical.choose hj).2 hne)) hwi hwj
          · simp only [hAdef, dif_pos hi, dif_neg hj]; exact disjoint_bot_right
        · simp only [hAdef, dif_neg hi]; exact disjoint_bot_left
      · ext w
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        -- `(restrictEquiv U w).val ∈ U = ⋃₀ 𝒮`, so it lies in some piece `P ∈ 𝒮`.
        obtain ⟨P, hP𝒮, hwP⟩ : ∃ P ∈ 𝒮, (F.restrictEquiv U w : ↑F.domain) ∈ P :=
          (F.restrictEquiv U w).2
        refine ⟨e ⟨P, hP𝒮⟩, ?_⟩
        have hex : ∃ p : ↑𝒮, e p = e ⟨P, hP𝒮⟩ := ⟨⟨P, hP𝒮⟩, rfl⟩
        simp only [hAdef, dif_pos hex]
        have hchoose : Classical.choose hex = ⟨P, hP𝒮⟩ := he (Classical.choose_spec hex)
        rw [htp, hchoose]; exact hwP
    refine (scatFun_reduces_gl_of_domain_partition G A hdu).trans ?_
    apply ScatFun.gl_reduces_omega_of_forall
    intro i
    by_cases h : ∃ p : ↑𝒮, e p = i
    · -- block `i` is the transport of piece `P`, `≡ F↾P ≤ g`.
      have hAi : A i = tp (Classical.choose h) := by simp only [hAdef, dif_pos h]
      rw [hAi]
      have hPU : (Classical.choose h).val ⊆ U :=
        fun x hx => Set.mem_sUnion.mpr ⟨_, (Classical.choose h).2, hx⟩
      refine' (ScatFun.restrict_restrict_equiv F U (Classical.choose h).val hPU).1.trans _
      exact hle _ (Classical.choose h).2
    · have hempty : IsEmpty ↑(G.restrict (A i)).domain := by
        have : A i = ∅ := by simp only [hAdef, dif_neg h]
        rw [this]; exact Set.isEmpty_coe_sort.mpr (by ext x; simp [ScatFun.restrict])
      exact ScatFun.reduces_of_isEmpty_domain hempty

/-- **A domain-subset restriction reduces into the enclosing piece's corestriction.** If
`S ⊆ P` and `F` maps `S` into `V`, then `F↾S ≤ (F↾P)⇂V`: `S ⊆ A := {a ∈ P | F a ∈ V}`, and
`F↾A` is `≡` to `(F↾P)⇂V` (`restrict_restrict_equiv`, the corestriction's domain piece is exactly
the transport of `A`). Bridges a residual `P ∩ A^D_0` to `(F↾P)⇂((RaySet ȳ r)ᶜ)`. -/
theorem restrict_subset_reduces_coRestrict (F : ScatFun) (P : Set ↑F.domain) (V : Set Baire)
    {S : Set ↑F.domain} (hSP : S ⊆ P) (hSV : ∀ a ∈ S, F.func a ∈ V) :
    ScatFun.Reduces (F.restrict S) ((F.restrict P).coRestrict V) := by
  set A : Set ↑F.domain := {a | a ∈ P ∧ F.func a ∈ V} with hAdef
  have hAP : A ⊆ P := fun a ha => ha.1
  have hset : {w : ↑(F.restrict P).domain | (F.restrict P).func w ∈ V}
      = {w : ↑(F.restrict P).domain | (F.restrictEquiv P w : ↑F.domain) ∈ A} := by
    ext w
    refine ⟨fun hw => ⟨(F.restrictEquiv P w).2, hw⟩, fun hw => hw.2⟩
  have hSA : S ⊆ A := fun a ha => ⟨hSP ha, hSV a ha⟩
  refine (restrict_reduces_of_subset F hSA).trans ?_
  have hEq := (ScatFun.restrict_restrict_equiv F P A hAP).2
  rw [← hset] at hEq
  exact hEq

/-- **Per-rep residual bound** (`6_double_successor_memo.tex:381-385`). For a diagonal rep
`g ∈ D`, the residual region `⋃₀{P ∩ Res | P ≡ g}` reduces into `g`. Dichotomy (Thm 4.9):
`g ≡ pglFinset G` — each residual `(F↾P)⇂V ≤ FinGl G ≤ ω(gl G)`, so the `ω`-collapse over the
(infinitely many) pieces lands at `ω(ω(gl G)) ≡ ω(gl G) ≤ pglFinset G ≡ g`; or `g ≡ minFun λ` —
each residual has `CB < λ` so `≤ maxFun λ`, collapsing to `ω(maxFun λ) ≡ maxFun λ ≤ g`. -/
theorem secondCase_perRep_residual_le
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {y : Baire} (Res : Set ↑F.domain) (hRescl : IsClopen Res)
    (hReswindow : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
        ∀ a ∈ P, a ∈ Res →
          F.func a ∉ RaySet Set.univ y (firstDiff y (hA.cocenterOf hP)))
    (g : ScatFun) (hgC : g ∈ ScatFun.Centered (α + 1 + 1))
    (hgreal : ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g) :
    ScatFun.Reduces
      (F.restrict (⋃₀ {Q | ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g ∧ Q = P ∩ Res})) g := by
  classical
  set lam := α.limitPart with hlam_def
  set m := α.natPart with hm_def
  have hlim : Order.IsSuccLimit lam ∨ lam = 0 := Ordinal.limitPart_isLimit_or_zero α
  have hα_eq : α = lam + ↑m := Ordinal.eq_limitPart_add_natPart α
  have hlm1 : lam + ↑(m + 1) = α + 1 := by rw [hα_eq, Nat.cast_add, Nat.cast_one, add_assoc]
  have hlm2 : lam + ↑(m + 1) + 1 = α + 1 + 1 := by rw [hlm1]
  have hlam_le : lam ≤ α := by
    conv_rhs => rw [hα_eq]
    exact le_self_add
  have hlam_lt : lam < omega1 := lt_of_le_of_lt hlam_le hα
  have hgcent : IsCentered g.func := ScatFun.isCentered_of_mem_Centered _ g hgC
  -- Rank bounds for `g` via a realizing piece.
  obtain ⟨P₀, hP₀, hP₀ne, hP₀eq⟩ := hgreal
  have hgrank_lo : lam < CBRank g.func := by
    rw [← cbRank_eq_of_equiv hP₀eq]; exact hfine.2 P₀ hP₀
  have hglvl : g ∈ ScatFun.LevelInter lam (lam + ↑(m + 1) + 1) := by
    refine ⟨le_of_lt hgrank_lo, ?_⟩
    rw [hlm2, ← hFrank, ← cbRank_eq_of_equiv hP₀eq]
    exact ContinuouslyReduces.rank_monotone (F.restrict P₀).hScat F.hScat (restrict_le_self F P₀)
  have hFG' : ScatFun.FGBelow (lam + ↑(m + 1) + 1) := by rw [hlm2]; exact hFG
  -- The residual family `𝒮 = {P ∩ Res | P ≡ g}`.
  set 𝒫g : Set (Set ↑F.domain) :=
    {P | ∃ (hP : P ∈ Part), hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g} with h𝒫g
  set 𝒮 : Set (Set ↑F.domain) := (fun P => P ∩ Res) '' 𝒫g with h𝒮
  have h𝒮eq : {Q | ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g ∧ Q = P ∩ Res} = 𝒮 := by
    ext Q
    constructor
    · rintro ⟨P, hP, hne, heq, rfl⟩; exact ⟨P, ⟨hP, hne, heq⟩, rfl⟩
    · rintro ⟨P, ⟨hP, hne, heq⟩, rfl⟩; exact ⟨P, hP, hne, heq, rfl⟩
  rw [h𝒮eq]
  -- Countable / clopen / disjoint structure of `𝒮`.
  have h𝒫gsub : 𝒫g ⊆ Part := fun P hP => hP.choose
  have hcount : 𝒮.Countable := (hA.countable.mono h𝒫gsub).image _
  have hcl : ∀ Q ∈ 𝒮, IsClopen Q := by
    rintro Q ⟨P, hP𝒫, rfl⟩
    exact (hA.isClopen P (h𝒫gsub hP𝒫)).inter hRescl
  have hdisj : 𝒮.PairwiseDisjoint id := by
    rintro Q₁ ⟨P₁, hP₁𝒫, rfl⟩ Q₂ ⟨P₂, hP₂𝒫, rfl⟩ hne
    have hPne : P₁ ≠ P₂ := fun h => hne (by rw [h])
    exact ((hA.pairwiseDisjoint (h𝒫gsub hP₁𝒫) (h𝒫gsub hP₂𝒫) hPne).mono
      Set.inter_subset_left Set.inter_subset_left)
  -- The dichotomy provides a low bound `glow` with `ω glow ≤ g`, and each piece `≤ glow`.
  obtain ⟨glow, hpiece_le, hcollapse⟩ :
      ∃ glow, (∀ Q ∈ 𝒮, ScatFun.Reduces (F.restrict Q) glow) ∧
        ScatFun.Reduces (ScatFun.omega glow) g := by
    rcases ScatFun.finitenessOfCenteredFunctions_generators hlam_lt hlim (m + 1) hFG' g hglvl hgcent with
      hmin | ⟨k, ι, hk, hpgleq⟩
    · -- **minFun case**: `glow = maxFun lam`.
      refine ⟨ScatFun.maxFun lam hlam_lt, ?_, ?_⟩
      · rintro Q ⟨P, ⟨hP, hne, heqP⟩, rfl⟩
        -- `F↾P ≡ minFun λ` has rank `λ+1`, so its rays at the cocenter have rank `≤ λ`
        -- (`rayOn_cbRank_lt`, using `block_const_on_top`), whence the residual — corestricted to
        -- finitely many of those rays — has rank `≤ λ` (`cbRank_corestrict_W_le`), so `≤ maxFun λ`.
        set hcentP := hA.centered P hP with hcentP_def
        set yP := hA.cocenterOf hP with hyP_def
        set r := firstDiff y yP with hr_def
        set Vray : Set Baire := ⋃ n ∈ Finset.range (r + 1), RaySet Set.univ yP n with hVray_def
        have hyP_ray : yP ∈ RaySet Set.univ y r := firstDiff_mem_raySet y yP hne
        have hVsub : (RaySet Set.univ y r)ᶜ ⊆ Vray := raySet_compl_subset_lowRays y yP r hyP_ray
        have hFPrank : CBRank (F.restrict P).func = Order.succ lam := by
          rw [cbRank_eq_of_equiv (heqP.trans hmin), minFun_cbRank_eq lam hlam_lt]
        have htop : ∀ x ∈ CBLevel (F.restrict P).func lam, (F.restrict P).func x = yP := by
          intro x hx
          exact block_const_on_top (F.restrict P) hcentP lam hFPrank x hx
        have hray_le : ∀ n, CBRank ((F.restrict P).rayOn yP Set.univ n).func ≤ lam := fun n =>
          Order.lt_succ_iff.mp
            (ScatFun.rayOn_cbRank_lt (F.restrict P) lam yP htop Set.univ isOpen_univ n)
        have hwin : ∀ a ∈ P ∩ Res, F.func a ∈ Vray := by
          rintro a ⟨haP, haRes⟩
          exact hVsub (hReswindow P hP hne a haP haRes)
        have hres_le : ScatFun.Reduces (F.restrict (P ∩ Res)) ((F.restrict P).coRestrict Vray) :=
          restrict_subset_reduces_coRestrict F P Vray Set.inter_subset_left hwin
        have hrank_le : CBRank (F.restrict (P ∩ Res)).func ≤ lam :=
          le_trans (ContinuouslyReduces.rank_monotone
              (F.restrict (P ∩ Res)).hScat ((F.restrict P).coRestrict Vray).hScat hres_le)
            (cbRank_corestrict_W_le (F.restrict P) yP lam hray_le (Finset.range (r + 1)))
        exact ScatFun.reduces_maxFun_of_rank_le _ lam hlam_lt hrank_le
      · -- `ω(maxFun lam) ≡ maxFun lam ≤ g`.
        refine (ScatFun.omega_maxFun_equiv_self lam hlam_lt).1.trans ?_
        rcases hlim with hlimit | hzero
        · exact ScatFun.maxFun_reduces_of_lam_lt_rank hlam_lt hlimit g hgrank_lo
        · -- `lam = 0`: `maxFun 0` has empty domain.
          refine ScatFun.reduces_of_isEmpty_domain ?_
          rw [Set.isEmpty_coe_sort, ← Set.not_nonempty_iff_eq_empty]
          rintro ⟨x, hx⟩
          have hpos := CBRank_pos_of_scattered_nonempty _
            (ScatFun.maxFun lam hlam_lt).hScat ⟨(⟨x, hx⟩ : ↑(ScatFun.maxFun lam hlam_lt).domain)⟩
          rw [ScatFun.maxFun_func, maxFun_cbRank_eq lam hlam_lt, hzero] at hpos
          exact lt_irrefl 0 hpos
    · -- **pglFinset case**: `glow = ω(gl G)`, `G = image ι`.
      set G : Finset ScatFun :=
        Finset.image ((ScatFun.Generators (lam + ↑(m + 1))).toFinFun ∘ ι) Finset.univ with hG
      have hgpgl : ScatFun.Equiv g (ScatFun.pglFinset G) :=
        hpgleq.trans (ScatFun.pgl_repSeq_equiv_pglFinset_image _ hk)
      refine ⟨ScatFun.omega (ScatFun.glList G.toList), ?_, ?_⟩
      · rintro Q ⟨P, ⟨hP, hne, heqP⟩, rfl⟩
        -- `F↾(P ∩ Res) ≤ (F↾P)⇂V ≤ FinGl G ≤ ω(gl G)`.
        set hcentP := hA.centered P hP with hcentP_def
        set yP := hA.cocenterOf hP with hyP_def
        have hyPne : yP ≠ y := hne
        have hyP_ray : yP ∈ RaySet Set.univ y (firstDiff y yP) :=
          firstDiff_mem_raySet y yP hyPne
        set r := firstDiff y yP with hr_def
        set V : Set Baire := (RaySet Set.univ y r)ᶜ with hV_def
        have hcocEq : cocenter (F.restrict P).func hcentP = yP := rfl
        have hVsub : V ⊆ ⋃ n ∈ Finset.range (r + 1),
            RaySet Set.univ (cocenter (F.restrict P).func hcentP) n := by
          rw [hcocEq]; exact raySet_compl_subset_lowRays y yP r hyP_ray
        have hPpgl : ScatFun.Equiv (F.restrict P) (ScatFun.pglFinset G) := heqP.trans hgpgl
        obtain ⟨h, hhmem, hhred⟩ :=
          ScatFun.residualCorestrict_reduces_finGl (F.restrict P) hcentP G hPpgl hVsub
        -- transport `F↾(P ∩ Res) ≤ (F↾P)⇂V`.
        have hwin : ∀ a ∈ P ∩ Res, F.func a ∈ V := by
          rintro a ⟨haP, haRes⟩
          exact hReswindow P hP hne a haP haRes
        refine ((restrict_subset_reduces_coRestrict F P V Set.inter_subset_left hwin).trans
          hhred).trans ?_
        exact ScatFun.finGl_reduces_omega_glList hhmem
      · -- `ω(ω(gl G)) ≡ ω(gl G) ≤ pglFinset G ≡ g`.
        refine' (ScatFun.omega_omega_equiv _).1.trans _
        exact (ScatFun.omega_glList_reduces_pglFinset G).trans hgpgl.2
  -- Assemble: `ω`-collapse over `𝒮`, then `ω glow ≤ g`.
  exact (reduces_restrict_omega_of_countable_subfamily hcount hcl hdisj hpiece_le).trans hcollapse

/-- **Second-case mop-up block `A^D_0`** (`6_double_successor_memo.tex:381-385`). The diagonal
residual region `Res` (points of diagonal pieces whose image was cut from their ray) reduces into
`FinGl D`: group by rep `g ∈ D` (`secondCase_perRep_residual_le`, each group `≤ g`), disjointify,
and glue the finitely many `≤ FinGl D` blocks (`reduces_finGl_of_finite_union`). -/
theorem secondCase_residual_mopup_reduces
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    (hfine : hA.IsFine α.limitPart)
    {y : Baire} (D : Finset ScatFun) (hDsub : D ⊆ ScatFun.Centered (α + 1 + 1))
    (hDrep : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g)
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    (Res : Set ↑F.domain) (hRescl : IsClopen Res)
    (hResdiag : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), (P ∩ Res).Nonempty →
      hA.cocenterOf hP ≠ y)
    (hReswindow : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
        ∀ a ∈ P, a ∈ Res →
          F.func a ∉ RaySet Set.univ y (firstDiff y (hA.cocenterOf hP))) :
    ∃ m, ScatFun.Reduces (F.restrict Res)
      (ScatFun.glList (List.replicate m (ScatFun.glList D.toList))) := by
  classical
  set N := D.toList.length with hN
  set gof : Fin N → ScatFun := fun k => D.toList.get k with hgof
  have hgofD : ∀ k, gof k ∈ D := fun k => Finset.mem_toList.mp (List.get_mem _ _)
  -- Per-rep residual region.
  set R : Fin N → Set ↑F.domain :=
    fun k => ⋃₀ {Q | ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) (gof k) ∧ Q = P ∩ Res} with hR
  -- `R k = (⋃₀ pieces≡gof k) ∩ Res`, clopen.
  have hRcl : ∀ k, IsClopen (R k) := by
    intro k
    have heq : R k = (⋃₀ {P | ∃ (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) (gof k)}) ∩ Res := by
      rw [hR]; ext x
      constructor
      · rintro ⟨Q, ⟨P, hP, hne, heq, rfl⟩, hxP, hxRes⟩
        exact ⟨⟨P, ⟨hP, hne, heq⟩, hxP⟩, hxRes⟩
      · rintro ⟨⟨P, ⟨hP, hne, heq⟩, hxP⟩, hxRes⟩
        exact ⟨P ∩ Res, ⟨P, hP, hne, heq, rfl⟩, hxP, hxRes⟩
    rw [heq]
    exact (hA.sUnion_subfamily_isClopen (fun P hP => hP.choose)).inter hRescl
  have hRle : ∀ k, ScatFun.Reduces (F.restrict (R k)) (gof k) := by
    intro k
    obtain ⟨P, hP, hne, heqP⟩ := hDreal (gof k) (hgofD k)
    exact secondCase_perRep_residual_le α hα hFG F hFrank hA hfine Res hRescl hReswindow
      (gof k) (hDsub (hgofD k)) ⟨P, hP, hne, heqP⟩
  -- Disjointify.
  set Q : Fin N → Set ↑F.domain :=
    fun k => R k \ ⋃ (j : Fin N) (_ : j.val < k.val), R j with hQ
  have hQcl : ∀ k, IsClopen (Q k) :=
    fun k => (hRcl k).diff (isClopen_iUnion_of_finite
      fun j => isClopen_iUnion_of_finite fun _ => hRcl j)
  have hQdisj : Pairwise (Disjoint on Q) := by
    intro k l hkl
    rcases lt_or_gt_of_ne (fun h => hkl (Fin.ext h)) with h | h
    · exact Set.disjoint_left.mpr fun x hxk hxl =>
        hxl.2 (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨h, hxk.1⟩⟩)
    · exact Set.disjoint_left.mpr fun x hxk hxl =>
        hxk.2 (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨h, hxl.1⟩⟩)
  have hpiece : ∀ k, ∃ m ∈ ScatFun.FinGl D.toFinFun, ScatFun.Reduces (F.restrict (Q k)) m := by
    intro k
    refine ⟨gof k, ?_, (restrict_reduces_of_subset F (fun x hx => hx.1)).trans (hRle k)⟩
    exact ScatFun.finGl_of_equiv_glList (L := [gof k])
      (by intro w hw; rw [List.mem_singleton] at hw; subst hw
          exact hgofD k)
      (ScatFun.glList_single_equiv (gof k))
  -- `Res ⊆ ⋃ Q k` (every residual point's piece maps to some rep, hence into some `R k`).
  have hResQ : Res ⊆ ⋃ k, Q k := by
    intro x hxRes
    -- `x` lies in a unique piece `P`, which is diagonal (`hResdiag`) and maps to some `gof k`.
    obtain ⟨P, hPmem, hxP⟩ : ∃ P ∈ Part, x ∈ P :=
      hA.sUnion_eq.symm.subset (Set.mem_univ x)
    have hne : hA.cocenterOf hPmem ≠ y := hResdiag P hPmem ⟨x, hxP, hxRes⟩
    obtain ⟨g, hgD, hgeq⟩ := hDrep P hPmem hne
    obtain ⟨k, hk⟩ : ∃ k : Fin N, gof k = g := by
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hgD); exact ⟨k, hk⟩
    have hxRk : x ∈ R k := ⟨P ∩ Res, ⟨P, hPmem, hne, hk ▸ hgeq, rfl⟩, hxP, hxRes⟩
    -- pick the least index whose `R` contains `x`.
    set I : Finset (Fin N) := Finset.univ.filter (fun i => x ∈ R i) with hI
    have hIne : I.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxRk⟩⟩
    set k₀ := I.min' hIne with hk₀
    have hk₀I : k₀ ∈ I := I.min'_mem hIne
    have hxk₀ : x ∈ R k₀ := (Finset.mem_filter.mp hk₀I).2
    refine Set.mem_iUnion.mpr ⟨k₀, hxk₀, ?_⟩
    intro hxlow
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxlow
    obtain ⟨hjlt, hxj⟩ := Set.mem_iUnion.mp hj
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩
    exact absurd (I.min'_le j hjI) (not_le.mpr hjlt)
  obtain ⟨hh, hhmem, hhred⟩ := ScatFun.reduces_finGl_of_finite_union Q hQcl hQdisj D hpiece
  obtain ⟨m, hm⟩ := finGl_reduces_replicate_glList hhmem
  exact ⟨m, ((restrict_reduces_of_subset F hResQ).trans hhred).trans hm⟩

/-- `c ∈ FinGl {c}`: the singleton generator. -/
theorem ScatFun.mem_finGl_self (c : ScatFun) :
    c ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun :=
  ScatFun.finGl_of_equiv_glList (L := [c])
    (by intro w hw; rw [List.mem_singleton] at hw; rw [hw]; exact Finset.mem_singleton.mpr rfl)
    (ScatFun.glList_single_equiv c)

/-- A `FinGl {c}` member reduces to `replicate m c` for some `m` (single-generator specialization
of `finGl_reduces_replicate_glList`, unfolding `glList {c}.toList ≡ c`). -/
theorem ScatFun.finGl_singleton_reduces_replicate {c a : ScatFun}
    (ha : a ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun) :
    ∃ m, ScatFun.Reduces a (ScatFun.glList (List.replicate m c)) := by
  obtain ⟨m, hm⟩ := finGl_reduces_replicate_glList ha
  have htoList : ({c} : Finset ScatFun).toList = [c] := by simp
  rw [htoList] at hm
  refine ⟨m, hm.trans ?_⟩
  have hstep := ScatFun.glList_reduces_glList_map (List.replicate m (ScatFun.glList [c]))
    (fun _ => c) (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact (ScatFun.glList_single_equiv c).2)
  rwa [List.map_replicate] at hstep

/-- Combine two `replicate`-reductions across a `glBin` into a single `replicate`-reduction:
`a ≤ gl(replicate m₁ c)`, `b ≤ gl(replicate m₂ c) ⟹ ∃ m, glBin a b ≤ gl(replicate m c)`. -/
theorem ScatFun.reduces_replicate_glBin {a b c : ScatFun} {m₁ m₂ : ℕ}
    (ha : ScatFun.Reduces a (ScatFun.glList (List.replicate m₁ c)))
    (hb : ScatFun.Reduces b (ScatFun.glList (List.replicate m₂ c))) :
    ∃ m, ScatFun.Reduces (ScatFun.glBin a b) (ScatFun.glList (List.replicate m c)) := by
  have hmemc : c ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun := ScatFun.mem_finGl_self c
  have hM1 : ScatFun.glList (List.replicate m₁ c) ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun :=
    ScatFun.finGl_glList_of_forall_finGl
      (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact hmemc)
  have hM2 : ScatFun.glList (List.replicate m₂ c) ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun :=
    ScatFun.finGl_glList_of_forall_finGl
      (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact hmemc)
  have hglBinMem : ScatFun.glBin (ScatFun.glList (List.replicate m₁ c))
      (ScatFun.glList (List.replicate m₂ c)) ∈ ScatFun.FinGl ({c} : Finset ScatFun).toFinFun :=
    ScatFun.finGl_glBin_mem hM1 hM2
  obtain ⟨m, hm⟩ := ScatFun.finGl_singleton_reduces_replicate hglBinMem
  exact ⟨m, (ScatFun.glBin_reduces_of_reduces ha hb).trans hm⟩

/-- `G↾(A ∪ B) ≤ (G↾A) ⊕ (G↾B)` for disjoint clopen `A, B` — the binary-partition special case of
`reduces_glBin_of_clopen_partition`, transported into `(G↾(A∪B)).domain`. -/
theorem ScatFun.restrict_union_reduces_glBin (G : ScatFun) {A B : Set ↑G.domain}
    (hAcl : IsClopen A) (hBcl : IsClopen B) (hdisj : Disjoint A B) :
    ScatFun.Reduces (G.restrict (A ∪ B)) (ScatFun.glBin (G.restrict A) (G.restrict B)) := by
  have hcont : Continuous (fun w : ↑(G.restrict (A ∪ B)).domain =>
      (G.restrictEquiv (A ∪ B) w : ↑G.domain)) :=
    continuous_subtype_val.comp (G.restrictEquiv (A ∪ B)).continuous
  refine ScatFun.reduces_glBin_of_clopen_partition (F := G.restrict (A ∪ B))
    (G.restrict A) (G.restrict B)
    (A0 := {w | (G.restrictEquiv (A ∪ B) w : ↑G.domain) ∈ A})
    (A1 := {w | (G.restrictEquiv (A ∪ B) w : ↑G.domain) ∈ B})
    (hAcl.preimage hcont) (hBcl.preimage hcont) ?_ ?_ ?_ ?_
  · ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (G.restrictEquiv (A ∪ B) w).2
  · rw [Set.disjoint_left]
    exact fun w hwa hwb => (Set.disjoint_left.mp hdisj) hwa hwb
  · exact (ScatFun.restrict_restrict_equiv G (A ∪ B) A Set.subset_union_left).1
  · exact (ScatFun.restrict_restrict_equiv G (A ∪ B) B Set.subset_union_right).1

/-- Rays distribute over a disjoint clopen union: `rayOn y (A ∪ B) j ≤ (rayOn y A j) ⊕ (rayOn y B j)`. -/
theorem ScatFun.rayOn_union_reduces_glBin (G : ScatFun) (y : Baire) {A B : Set ↑G.domain}
    (hAcl : IsClopen A) (hBcl : IsClopen B) (hdisj : Disjoint A B) (j : ℕ) :
    ScatFun.Reduces (G.rayOn y (A ∪ B) j)
      (ScatFun.glBin (G.rayOn y A j) (G.rayOn y B j)) := by
  have hRJcl : IsClopen {a : ↑G.domain | G.func a ∈ RaySet Set.univ y j} :=
    (isClopen_raySet y j).preimage G.hCont
  have hunion : (A ∪ B) ∩ {a : ↑G.domain | G.func a ∈ RaySet Set.univ y j}
      = (A ∩ {a | G.func a ∈ RaySet Set.univ y j})
        ∪ (B ∩ {a | G.func a ∈ RaySet Set.univ y j}) :=
    Set.union_inter_distrib_right A B _
  unfold ScatFun.rayOn
  rw [hunion]
  exact ScatFun.restrict_union_reduces_glBin G (hAcl.inter hRJcl) (hBcl.inter hRJcl)
    (hdisj.mono Set.inter_subset_left Set.inter_subset_left)

/-- **The ray-cut diagonal family** (`6_double_successor_memo.tex:349-386`) — the existential
consumed by `ScatFun.wedge_upper_bound` in `diagonalTheorem_secondCase_construction`'s left
reduction. Over the `A¹` region `R = Aᶜ = (⋃ᵢ A0 i)ᶜ`, it produces an `ℕ`-indexed clopen disjoint
union `Adiag` and ray indices `kidx → ∞` with three clauses:

* **columns** (`i < n`): rays reduce to `replicate m (v i)` (`secondCase_column_rays_reducible`,
  cocenter rigidity), transported into `R`;
* **diagonal** (`i ≥ n`): each block reduces to `replicate m (gl D)` — the ray-cuts `A^D_r` (`i > n`)
  via `secondCase_diagonal_block_reduces` (per-level Vertical Theorem `≤ 2(gl D)`), the mop-up `A^D_0`
  (`i = n`) via `secondCase_residual_mopup_reduces`;
* **ranges** `⊆ RaySet y (kidx i)` with `kidx → ∞`.

**Index by ray-index, not by an enumeration of `Y'`** (route B).  Sets in `F.domain`:
`Adiff = ⋃₀{P | y_P ≠ y}`, `Blk r = ⋃₀{P | y_P ≠ y ∧ firstDiff ȳ y_P = r}`,
`SRay r = Blk r ∩ f⁻¹(RaySet ȳ r)`, `W = ⋃ᵣ SRay r`; the residual mop-up is `SMop = Adiff ∖ W`.
Totality of `firstDiff` gives `A^D = ⋃ᵣ Blk r` and hence `W` clopen for free — no enumeration
`(yₙ)` and no "accumulating-at-`y`" clopen-ness worry.

**Absorbing `A¹₀`.**  The low cocenter-`y` pieces (rank `λ+1`, not captured by the columns `gM`,
which represent the rank-`> λ+1` classes) form `A¹₀ = R ∖ (⋃SCol ∪ Adiff)`.  They cannot go to the
mop-up (rank-`λ+1`, so `⋠ gl D` when `D = ∅`); instead they are folded into column `i₀`
(`SColA i₀ = SCol i₀ ∪ A¹₀`), where `i₀` has rank `> λ+1` (`hcase` + `hMcover`), so `A¹₀`'s rays
(`≤ maxFun λ` since `F↾A¹₀` is simple of rank `λ+1` and distinguished point `y`) satisfy
`maxFun λ ≤ v i₀`.  **Fully proved**. -/
theorem secondCase_ray_cut_diagonal_family
    (α : Ordinal.{0}) (hα : α < omega1) (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (hcase : ¬ ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1)
    (D : Finset ScatFun) (hDsub : D ⊆ ScatFun.Centered (α + 1 + 1))
    (hDrep : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
      ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g)
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    (n : ℕ) (gM : Fin n → ScatFun) (Mg : Fin n → Finset ScatFun)
    (A0 A1 : Fin n → Set ↑F.domain) (v : Fin n → ScatFun)
    (hv : v = fun i => ScatFun.glList (Mg i).toList)
    (_hgMc : ∀ i, gM i ∈ ScatFun.Centered (α + 1 + 1))
    (hgpgl : ∀ i, ScatFun.Equiv (gM i) (ScatFun.pglFinset (Mg i)))
    (hA1cl : ∀ i, IsClopen (A1 i))
    (hAdisj : ∀ i, Disjoint (A0 i) (A1 i))
    (hAcov : ∀ i, A0 i ∪ A1 i = ⋃₀ hA.blockPieces (gM i) y)
    (hL1 : ∀ i, ScatFun.Reduces (F.restrict (A1 i)) (gM i))
    (hL1' : ∀ i, ScatFun.Reduces (gM i) (F.restrict (A1 i)))
    (hcocA1 : ∀ i, ∀ (h : IsCentered (F.restrict (A1 i)).func),
      cocenter (F.restrict (A1 i)).func h = y)
    (hMreal : ∀ i, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
      hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (gM i))
    (hMcover : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      α.limitPart + 1 < CBRank (F.restrict P).func → ∃ i, ScatFun.Equiv (F.restrict P) (gM i))
    (R : Set ↑F.domain) (hR : R = (⋃ i, A0 i)ᶜ) :
    -- conclusion: the input to `ScatFun.wedge_upper_bound` in `diagonalTheorem_secondCase_construction`
    ∃ (Adiag : ℕ → Set ↑(F.restrict R).domain) (kidx : ℕ → ℕ),
      (F.restrict R).IsDisjointUnion Adiag ∧
      (∀ (i : ℕ) (hi : i < n) (j : ℕ), ∃ m,
        ScatFun.Reduces ((F.restrict R).rayOn y (Adiag i) j)
          (ScatFun.glList (List.replicate m (v ⟨i, hi⟩)))) ∧
      (∀ i, n ≤ i → ∃ m,
        ScatFun.Reduces ((F.restrict R).restrict (Adiag i))
          (ScatFun.glList (List.replicate m (ScatFun.glList D.toList)))) ∧
      (∀ i, n < i →
        Set.range ((F.restrict R).restrict (Adiag i)).func ⊆ RaySet Set.univ y (kidx i)) ∧
      Filter.Tendsto kidx Filter.atTop Filter.atTop := by
  classical
  have hfine : hA.IsFine α.limitPart := hss.1
  -- **Uniqueness of the piece through a point** (partition disjointness). Used throughout to
  -- turn "`x` lies in a cocenter-`z` piece" into "the piece of `x` has cocenter `z`".
  have huniq : ∀ (x : ↑F.domain) (P : Set ↑F.domain), P ∈ Part → ∀ Q ∈ Part,
      x ∈ P → x ∈ Q → P = Q := by
    intro x P hP Q hQ hxP hxQ
    by_contra hPQ
    exact (Set.disjoint_left.mp (hA.pairwiseDisjoint hP hQ hPQ)) hxP hxQ
  -- **Clopen-ness of the `A⁰` blocks** (derived: `A0 i = ⋃₀blockPieces ∖ A1 i`, both clopen).
  have hA0cl : ∀ i, IsClopen (A0 i) := by
    intro i
    have hbc : IsClopen (⋃₀ hA.blockPieces (gM i) y) :=
      hA.sUnion_subfamily_isClopen (fun P hP => hP.choose)
    have heq : A0 i = (⋃₀ hA.blockPieces (gM i) y) \ A1 i := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, fun hx1 => (Set.disjoint_left.mp (hAdisj i)) hx hx1⟩
        rw [← hAcov i]; exact Set.mem_union_left _ hx
      · rintro ⟨hxU, hx1⟩
        rw [← hAcov i] at hxU
        rcases hxU with h | h
        · exact h
        · exact absurd h hx1
    rw [heq]; exact hbc.diff (hA1cl i)
  have hRcl : IsClopen R := by rw [hR]; exact (isClopen_iUnion_of_finite hA0cl).compl
  -- **A column `i₀` of rank `> λ+1`** into which the low cocenter-`y` pieces `A¹₀` are absorbed.
  have hlim : Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 :=
    Ordinal.limitPart_isLimit_or_zero α
  have hlam_le : α.limitPart ≤ α := by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  have hlam_lt : α.limitPart < omega1 := lt_of_le_of_lt hlam_le hα
  -- `hcase` (some cocenter-`y` piece has rank `≠ λ+1`, hence `> λ+1` by fineness) yields a
  -- column `gM i₀` of rank `> λ+1` (via `hMcover`).
  obtain ⟨i₀, hi₀rank⟩ : ∃ i₀ : Fin n, α.limitPart + 1 < CBRank (gM i₀).func := by
    by_contra hcon
    push_neg at hcon
    apply hcase
    intro P hP hPy
    have hlo : α.limitPart < CBRank (F.restrict P).func := hfine.2 P hP
    have hle : CBRank (F.restrict P).func ≤ α.limitPart + 1 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨i, hi⟩ := hMcover P hP hPy hgt
      exact absurd (hcon i) (not_le.mpr (cbRank_eq_of_equiv hi ▸ hgt))
    exact le_antisymm hle (Order.add_one_le_iff.mpr hlo)
  -- `maxFun λ ≤ v i₀`: `rank(gM i₀) = rank(pglFinset (Mg i₀)) = succ (rank (gl (Mg i₀))) = succ (rank (v i₀))`.
  have hvrank : α.limitPart < CBRank (v i₀).func := by
    have h1 : CBRank (gM i₀).func = Order.succ (CBRank (v i₀).func) := by
      rw [cbRank_eq_of_equiv (hgpgl i₀), hv]
      exact ScatFun.cbRank_pgl_const (ScatFun.glList (Mg i₀).toList)
    rw [h1, Ordinal.add_one_eq_succ] at hi₀rank
    exact Order.succ_lt_succ_iff.mp hi₀rank
  have hmaxv0 : ScatFun.Reduces (ScatFun.maxFun α.limitPart hlam_lt) (v i₀) := by
    rcases hlim with hlimit | hzero
    · exact ScatFun.maxFun_reduces_of_lam_lt_rank hlam_lt hlimit (v i₀) hvrank
    · refine ScatFun.reduces_of_isEmpty_domain ?_
      rw [Set.isEmpty_coe_sort, ← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      have hpos := CBRank_pos_of_scattered_nonempty _ (ScatFun.maxFun α.limitPart hlam_lt).hScat
        ⟨(⟨x, hx⟩ : ↑(ScatFun.maxFun α.limitPart hlam_lt).domain)⟩
      rw [ScatFun.maxFun_func, maxFun_cbRank_eq α.limitPart hlam_lt, hzero] at hpos
      exact lt_irrefl 0 hpos
  -- ===================== Route (B): ray-index diagonal blocks =====================
  -- The full diagonal `A^D = ⋃₀{P | y_P ≠ y}`, and for each ray-index `r` the sub-family `Blk r`
  -- of diagonal pieces whose cocenter has `firstDiff y (y_P) = r`.  No enumeration of `Y'` is
  -- needed: `firstDiff` is total, so `A^D = ⋃ᵣ Blk r` automatically — this is exactly what makes
  -- the ray-cut union `W` clopen (the memoir's "delicate point"), and the construction is uniform
  -- (it degenerates correctly when there are no diagonal pieces).
  set Adiff : Set ↑F.domain := ⋃₀ {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ≠ y} with hAdiff_def
  set Blk : ℕ → Set ↑F.domain := fun r =>
    ⋃₀ {P | ∃ hP : P ∈ Part, hA.cocenterOf hP ≠ y ∧ firstDiff y (hA.cocenterOf hP) = r}
    with hBlk_def
  set SRay : ℕ → Set ↑F.domain :=
    fun r => Blk r ∩ {a | F.func a ∈ RaySet Set.univ y r} with hSRay_def
  -- Columns, **disjointified** (each keeps only the part not already in a lower column): distinct
  -- representatives `gM i` may be `Equiv` — then their blocks coincide and the raw `A1 i ∩ R`
  -- overlap — so we assign each shared point to the lowest-index column.
  set SCol : Fin n → Set ↑F.domain :=
    fun i => (A1 i ∩ R) \ ⋃ (j : Fin n) (_ : j < i), (A1 j ∩ R) with hSCol_def
  set W : Set ↑F.domain := ⋃ r, SRay r with hW_def
  -- `A¹₀` — the low cocenter-`y` pieces (rank `λ+1`), i.e. everything in `R` outside the columns
  -- and the diagonal; absorbed into column `i₀`.
  set A10 : Set ↑F.domain := R \ ((⋃ i, SCol i) ∪ Adiff) with hA10_def
  set SColA : Fin n → Set ↑F.domain :=
    fun i => SCol i ∪ (if i = i₀ then A10 else ∅) with hSColA_def
  -- `SMop` is now the *pure diagonal residual* `A^D_0 = A^D ∖ W` (`A¹₀` no longer lands here).
  set SMop : Set ↑F.domain := Adiff \ W with hSMop_def
  -- The `ℕ`-indexed family: `n` columns (column `i₀` absorbing `A¹₀`), the residual mop-up at
  -- index `n`, then the ray-cuts `A^D_r`.
  set S : ℕ → Set ↑F.domain := fun i =>
    if h : i < n then SColA ⟨i, h⟩ else if i = n then SMop else SRay (i - n - 1) with hS_def
  set Adiag : ℕ → Set ↑(F.restrict R).domain :=
    fun i => {w | (F.restrictEquiv R w : ↑F.domain) ∈ S i} with hAdiag_def
  set kidx : ℕ → ℕ := fun i => i - n - 1 with hkidx_def
  -- Value of `S` on the three index ranges.
  have hS_col : ∀ i (hi : i < n), S i = SColA ⟨i, hi⟩ := fun i hi => by
    simp only [hS_def]; rw [dif_pos hi]
  have hS_mop : S n = SMop := by simp only [hS_def]; rw [dif_neg (lt_irrefl n), if_true]
  have hS_ray : ∀ i, n < i → S i = SRay (i - n - 1) := fun i hi => by
    simp only [hS_def]; rw [dif_neg (by omega : ¬ i < n), if_neg (by omega : ¬ i = n)]
  ------------------------------------------------------------------------------------
  -- Structural facts about the `F.domain` sets.
  ------------------------------------------------------------------------------------
  have hBlk_subAdiff : ∀ r, Blk r ⊆ Adiff := fun r =>
    Set.sUnion_mono (fun P hP => ⟨hP.choose, hP.choose_spec.1⟩)
  have hAdiffcl : IsClopen Adiff := hA.sUnion_subfamily_isClopen (fun P hP => hP.choose)
  have hBlkcl : ∀ r, IsClopen (Blk r) := fun r =>
    hA.sUnion_subfamily_isClopen (fun P hP => hP.choose)
  have hSRaycl : ∀ r, IsClopen (SRay r) := fun r =>
    (hBlkcl r).inter ((isClopen_raySet y r).preimage F.hCont)
  have hSColcl : ∀ i, IsClopen (SCol i) := fun i =>
    ((hA1cl i).inter hRcl).diff
      (isClopen_iUnion_of_finite (fun j => isClopen_iUnion_of_finite (fun _ => (hA1cl j).inter hRcl)))
  -- `A^D = ⋃ᵣ Blk r`, and the `Blk r` are pairwise disjoint (one cocenter, one ray-index / piece).
  have hAdiff_eq : Adiff = ⋃ r, Blk r := by
    ext x; constructor
    · rintro ⟨P, ⟨hP, hPne⟩, hxP⟩
      exact Set.mem_iUnion.mpr ⟨firstDiff y (hA.cocenterOf hP), P, ⟨hP, hPne, rfl⟩, hxP⟩
    · rintro hx; obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx; exact hBlk_subAdiff r hr
  have hBlkdisj : ∀ r r', r ≠ r' → Disjoint (Blk r) (Blk r') := by
    intro r r' hrr'
    rw [Set.disjoint_left]
    rintro x ⟨P, ⟨hP, _, hPfd⟩, hxP⟩ ⟨P', ⟨hP', _, hP'fd⟩, hxP'⟩
    have hPP' : P = P' := huniq x P hP P' hP' hxP hxP'
    subst hPP'; exact hrr' (hPfd.symm.trans hP'fd)
  -- **[GAP 1 — the structural crux, NOW PROVED].** `W = ⋃ᵣ A^D_r` is clopen: it is open, and its
  -- relative complement in the clopen `A^D` is `⋃ᵣ (Blk r ∖ SRay r)`, also open, so `W` is closed.
  have hWcl : IsClopen W := by
    refine ⟨?_, isOpen_iUnion (fun r => (hSRaycl r).isOpen)⟩
    have hWsub : W ⊆ Adiff := fun x hx => by
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
      exact hBlk_subAdiff r (Set.inter_subset_left hr)
    have hRes : Adiff \ W = ⋃ r, (Blk r \ SRay r) := by
      rw [hAdiff_eq]; ext x
      simp only [Set.mem_diff, Set.mem_iUnion, hW_def, not_exists]
      constructor
      · rintro ⟨⟨r, hr⟩, hnw⟩; exact ⟨r, hr, hnw r⟩
      · rintro ⟨r, hr, hnsr⟩
        refine ⟨⟨r, hr⟩, fun r' hr' => ?_⟩
        by_cases hrr : r = r'
        · subst hrr; exact hnsr hr'
        · exact (Set.disjoint_left.mp (hBlkdisj r r' hrr)) hr (Set.inter_subset_left hr')
    have hResopen : IsOpen (Adiff \ W) := by
      rw [hRes]; exact isOpen_iUnion (fun r => ((hBlkcl r).diff (hSRaycl r)).isOpen)
    rw [← Set.diff_diff_cancel_left hWsub]
    exact hAdiffcl.isClosed.sdiff hResopen
  have hA10cl : IsClopen A10 :=
    hRcl.diff ((isClopen_iUnion_of_finite hSColcl).union hAdiffcl)
  have hSColAcl : ∀ i, IsClopen (SColA i) := by
    intro i
    refine (hSColcl i).union ?_
    split_ifs
    · exact hA10cl
    · exact isClopen_empty
  have hSMopcl : IsClopen SMop := hAdiffcl.diff hWcl
  have hScl : ∀ i, IsClopen (S i) := by
    intro i; simp only [hS_def]; split_ifs
    · exact hSColAcl _
    · exact hSMopcl
    · exact hSRaycl _
  -- Diagonal pieces avoid the `A⁰`-union, hence `A^D ⊆ R` (and so every `SRay r ⊆ R`).
  have hAdiff_subR : Adiff ⊆ R := by
    intro x hx
    rw [hR]; simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro i hxA0
    obtain ⟨P, ⟨hP, hPne⟩, hxP⟩ := hx
    have hxblock : x ∈ ⋃₀ hA.blockPieces (gM i) y := by
      have hmem : x ∈ A0 i ∪ A1 i := Set.mem_union_left _ hxA0
      rw [hAcov i] at hmem; exact hmem
    obtain ⟨P', hP'block, hxP'⟩ := Set.mem_sUnion.mp hxblock
    obtain ⟨hP'mem, _, hP'coc⟩ := hP'block
    have hPP' : P = P' := huniq x P hP P' hP'mem hxP hxP'
    subst hPP'; exact hPne hP'coc
  have hSRay_subR : ∀ r, SRay r ⊆ R := fun r =>
    (Set.inter_subset_left.trans (hBlk_subAdiff r)).trans hAdiff_subR
  have hSMop_subR : SMop ⊆ R := Set.diff_subset.trans hAdiff_subR
  -- `S` covers `R`: columns cover `⋃SCol`, column `i₀` also holds `A¹₀`, rays cover `W`, the
  -- residual mop-up holds `Adiff ∖ W`, and `A¹₀ = R ∖ (⋃SCol ∪ Adiff)` is the remaining leftover.
  have hScover : R ⊆ ⋃ i, S i := by
    intro x hxR
    by_cases hxc : x ∈ ⋃ i, SCol i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxc
      refine Set.mem_iUnion.mpr ⟨i.val, ?_⟩
      rw [hS_col i.val i.isLt]
      exact Set.mem_union_left _ hi
    · by_cases hxd : x ∈ Adiff
      · by_cases hxw : x ∈ W
        · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hxw
          refine Set.mem_iUnion.mpr ⟨n + 1 + r, ?_⟩
          rw [hS_ray (n + 1 + r) (by omega), show n + 1 + r - n - 1 = r by omega]
          exact hr
        · exact Set.mem_iUnion.mpr ⟨n, by rw [hS_mop]; exact ⟨hxd, hxw⟩⟩
      · refine Set.mem_iUnion.mpr ⟨i₀.val, ?_⟩
        rw [hS_col i₀.val i₀.isLt]
        have hxA10 : x ∈ A10 := ⟨hxR, by rintro (h | h); exacts [hxc h, hxd h]⟩
        show x ∈ SColA i₀
        simp only [hSColA_def]
        exact Set.mem_union_right _ hxA10
  -- **[GAP 2 — pairwise disjointness, NOW PROVED].** Columns are disjoint by disjointification;
  -- a column point has cocenter `y` while a ray-cut point has cocenter `≠ y` (so column ⊥ ray-cut);
  -- ray-cuts at distinct indices are disjoint (`hBlkdisj`); and the mop-up is the complement of
  -- `⋃columns ∪ W`, hence disjoint from every column and ray-cut.
  -- A column point sits in a cocenter-`y` piece; a ray-cut point in a cocenter-`≠y` piece.
  have hSCol_cocy : ∀ (i : Fin n) (x : ↑F.domain), x ∈ SCol i →
      ∃ (P : Set ↑F.domain) (hP : P ∈ Part), x ∈ P ∧ hA.cocenterOf hP = y := by
    intro i x hx
    have hxA1 : x ∈ A1 i := (Set.diff_subset.trans Set.inter_subset_left) hx
    have hxblock : x ∈ ⋃₀ hA.blockPieces (gM i) y := by
      have hmem : x ∈ A0 i ∪ A1 i := Set.mem_union_right _ hxA1
      rw [hAcov i] at hmem; exact hmem
    obtain ⟨Q, ⟨hQmem, _, hQcoc⟩, hxQ⟩ := Set.mem_sUnion.mp hxblock
    exact ⟨Q, hQmem, hxQ, hQcoc⟩
  have hSRay_cocdiag : ∀ (r : ℕ) (x : ↑F.domain), x ∈ SRay r →
      ∃ (P : Set ↑F.domain) (hP : P ∈ Part), x ∈ P ∧ hA.cocenterOf hP ≠ y := by
    intro r x hx
    obtain ⟨P, ⟨hP, hPne, _⟩, hxP⟩ := Set.mem_sUnion.mp hx.1
    exact ⟨P, hP, hxP, hPne⟩
  -- A column point sits in a cocenter-`y` piece and a diagonal (`Adiff`) point in a cocenter-`≠y`
  -- piece, so columns ⊥ `Adiff`; `A¹₀` is disjoint from `⋃SCol` and `Adiff` by construction.
  have hSCol_Adiff : ∀ a : Fin n, Disjoint (SCol a) Adiff := by
    intro a
    refine Set.disjoint_left.mpr fun x hxa hxd => ?_
    obtain ⟨P, hP, hxP, hPcoc⟩ := hSCol_cocy a x hxa
    obtain ⟨Q, ⟨hQ, hQne⟩, hxQ⟩ := hxd
    exact hQne (huniq x Q hQ P hP hxQ hxP ▸ hPcoc)
  have hA10_SCol : Disjoint A10 (⋃ i, SCol i) :=
    Set.disjoint_left.mpr fun x hx hxc => hx.2 (Set.mem_union_left _ hxc)
  have hA10_Adiff : Disjoint A10 Adiff :=
    Set.disjoint_left.mpr fun x hx hxd => hx.2 (Set.mem_union_right _ hxd)
  have hE_sub : ∀ a : Fin n, (if a = i₀ then A10 else (∅ : Set ↑F.domain)) ⊆ A10 := by
    intro a; split_ifs
    · exact subset_rfl
    · exact Set.empty_subset _
  have hE_i₀ : ∀ (a : Fin n) (x : ↑F.domain),
      x ∈ (if a = i₀ then A10 else (∅ : Set ↑F.domain)) → a = i₀ := by
    intro a x hx; split_ifs at hx with h
    · exact h
    · exact absurd hx (Set.notMem_empty x)
  have hSdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    -- bucket disjointness (raw `SCol`)
    have hcc : ∀ a b : Fin n, a ≠ b → Disjoint (SCol a) (SCol b) := by
      intro a b hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact Set.disjoint_left.mpr fun x hxa hxb =>
          hxb.2 (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨h, Set.diff_subset hxa⟩⟩)
      · exact Set.disjoint_left.mpr fun x hxa hxb =>
          hxa.2 (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨h, Set.diff_subset hxb⟩⟩)
    have hcr : ∀ (a : Fin n) (r : ℕ), Disjoint (SCol a) (SRay r) := by
      intro a r
      refine Set.disjoint_left.mpr fun x hxa hxr => ?_
      obtain ⟨P, hP, hxP, hPcoc⟩ := hSCol_cocy a x hxa
      obtain ⟨Q, hQ, hxQ, hQne⟩ := hSRay_cocdiag r x hxr
      exact hQne (huniq x Q hQ P hP hxQ hxP ▸ hPcoc)
    have hrr : ∀ r r' : ℕ, r ≠ r' → Disjoint (SRay r) (SRay r') := fun r r' hrr' =>
      (hBlkdisj r r' hrr').mono Set.inter_subset_left Set.inter_subset_left
    -- augmented columns (`SColA`, with `A¹₀` in slot `i₀`) and residual mop-up `SMop = Adiff ∖ W`
    have hccA : ∀ a b : Fin n, a ≠ b → Disjoint (SColA a) (SColA b) := by
      intro a b hab
      refine Set.disjoint_left.mpr fun x hxa hxb => ?_
      simp only [hSColA_def, Set.mem_union] at hxa hxb
      rcases hxa with hxa | hxa <;> rcases hxb with hxb | hxb
      · exact (Set.disjoint_left.mp (hcc a b hab)) hxa hxb
      · exact (Set.disjoint_left.mp hA10_SCol) (hE_sub b hxb) (Set.mem_iUnion.mpr ⟨a, hxa⟩)
      · exact (Set.disjoint_left.mp hA10_SCol) (hE_sub a hxa) (Set.mem_iUnion.mpr ⟨b, hxb⟩)
      · exact hab ((hE_i₀ a x hxa).trans (hE_i₀ b x hxb).symm)
    have hcmA : ∀ a : Fin n, Disjoint (SColA a) SMop := by
      intro a
      refine Set.disjoint_left.mpr fun x hxa hxm => ?_
      simp only [hSColA_def, Set.mem_union] at hxa
      rcases hxa with hxa | hxa
      · exact (Set.disjoint_left.mp (hSCol_Adiff a)) hxa hxm.1
      · exact (Set.disjoint_left.mp hA10_Adiff) (hE_sub a hxa) hxm.1
    have hcrA : ∀ (a : Fin n) (r : ℕ), Disjoint (SColA a) (SRay r) := by
      intro a r
      refine Set.disjoint_left.mpr fun x hxa hxr => ?_
      simp only [hSColA_def, Set.mem_union] at hxa
      rcases hxa with hxa | hxa
      · exact (Set.disjoint_left.mp (hcr a r)) hxa hxr
      · exact (Set.disjoint_left.mp hA10_Adiff) (hE_sub a hxa)
          (hBlk_subAdiff r (Set.inter_subset_left hxr))
    have hrmA : ∀ r : ℕ, Disjoint (SRay r) SMop := fun r =>
      Set.disjoint_left.mpr fun x hxr hxm => hxm.2 (Set.mem_iUnion.mpr ⟨r, hxr⟩)
    intro i j hij
    rcases lt_trichotomy i n with hi | hi | hi <;> rcases lt_trichotomy j n with hj | hj | hj
    · rw [hS_col i hi, hS_col j hj]
      exact hccA ⟨i, hi⟩ ⟨j, hj⟩ fun h => hij (Fin.val_eq_of_eq h)
    · rw [hS_col i hi, hj, hS_mop]; exact hcmA ⟨i, hi⟩
    · rw [hS_col i hi, hS_ray j hj]; exact hcrA ⟨i, hi⟩ (j - n - 1)
    · rw [hi, hS_mop, hS_col j hj]; exact (hcmA ⟨j, hj⟩).symm
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi, hS_mop, hS_ray j hj]; exact (hrmA (j - n - 1)).symm
    · rw [hS_ray i hi, hS_col j hj]; exact (hcrA ⟨j, hj⟩ (i - n - 1)).symm
    · rw [hS_ray i hi, hj, hS_mop]; exact hrmA (i - n - 1)
    · rw [hS_ray i hi, hS_ray j hj]
      exact hrr (i - n - 1) (j - n - 1) fun h => hij (by omega)
  -- **Finiteness of each ray-index level** `Y_r = {y_P | firstDiff y y_P = r}` (strong solvability
  -- condition 1: `cocenterSet ∖ nbhd y (r+1)` is finite, and `Y_r` sits inside it since
  -- `firstDiff y z = r` forces `z r ≠ y r`, i.e. `z ∉ nbhd y (r+1)`).
  have hYr_fin : ∀ r, {z | z ∈ hA.cocenterSet ∧ z ≠ y ∧ firstDiff y z = r}.Finite := by
    intro r
    apply Set.Finite.subset
      (hss.2.2 (nbhd y (r + 1)) (baire_nbhd_isClopen y (r + 1)) (fun i _ => rfl)).1
    rintro z ⟨hzc, hzne, hzfd⟩
    refine ⟨hzc, fun hznbhd => ?_⟩
    have hray : z ∈ RaySet Set.univ y r := hzfd ▸ firstDiff_mem_raySet y z hzne
    exact hray.2.2 (hznbhd r (Finset.mem_range.mpr (Nat.lt_succ_self r)))
  -- **Fiber structure** of the ray-cuts: a piece meeting `SRay r` has cocenter in `Y_r`.
  have hSRay_fiber : ∀ r, ∀ (P : Set ↑F.domain) (hP : P ∈ Part), (P ∩ SRay r).Nonempty →
      hA.cocenterOf hP ∈ {z | z ∈ hA.cocenterSet ∧ z ≠ y ∧ firstDiff y z = r} := by
    rintro r P hP ⟨x, hxP, hxray⟩
    obtain ⟨P', ⟨hP', hP'ne, hP'fd⟩, hxP'⟩ := Set.mem_sUnion.mp hxray.1
    have hPP' : P = P' := huniq x P hP P' hP' hxP hxP'
    subst hPP'
    exact ⟨⟨⟨P, hP⟩, rfl⟩, hP'ne, hP'fd⟩
  ------------------------------------------------------------------------------------
  -- **`A¹₀` structure and rays.**  Every `A¹₀` point sits in a cocenter-`y` rank-`λ+1` piece, so
  -- `F↾A¹₀` is a simple function of rank `λ+1` with distinguished point `y`; its rays therefore
  -- have `CB`-rank `≤ λ`, hence reduce into `maxFun λ ≤ v i₀`.
  ------------------------------------------------------------------------------------
  -- A point in some `A1 i ∩ R` lies in a disjointified column.
  have hA1R_in_SCol : ∀ (x : ↑F.domain), (∃ i : Fin n, x ∈ A1 i ∩ R) → x ∈ ⋃ k, SCol k := by
    rintro x ⟨i, hxi⟩
    set I : Finset (Fin n) := Finset.univ.filter (fun k => x ∈ A1 k ∩ R) with hI
    have hIne : I.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩⟩
    have hk₀I : I.min' hIne ∈ I := I.min'_mem hIne
    have hxk₀ : x ∈ A1 (I.min' hIne) ∩ R := (Finset.mem_filter.mp hk₀I).2
    refine Set.mem_iUnion.mpr ⟨I.min' hIne, hxk₀, fun hxlow => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxlow
    obtain ⟨hklt, hxk⟩ := Set.mem_iUnion.mp hk
    exact absurd (I.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxk⟩)) (not_le.mpr hklt)
  have hA10_piece : ∀ (x : ↑F.domain), x ∈ A10 →
      ∃ (P : Set ↑F.domain) (hP : P ∈ Part), x ∈ P ∧ hA.cocenterOf hP = y ∧
        CBRank (F.restrict P).func = α.limitPart + 1 := by
    intro x hx
    obtain ⟨P, hPmem, hxP⟩ : ∃ P ∈ Part, x ∈ P := hA.sUnion_eq.symm.subset (Set.mem_univ x)
    have hcocy : hA.cocenterOf hPmem = y := by
      by_contra hne
      exact hx.2 (Set.mem_union_right _ ⟨P, ⟨hPmem, hne⟩, hxP⟩)
    have hlo : α.limitPart < CBRank (F.restrict P).func := hfine.2 P hPmem
    have hle : CBRank (F.restrict P).func ≤ α.limitPart + 1 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨i, hieq⟩ := hMcover P hPmem hcocy hgt
      have hxblock : x ∈ ⋃₀ hA.blockPieces (gM i) y := by
        obtain ⟨Q, hQ, hQy, _⟩ := hMreal i
        exact ⟨P, ⟨hPmem, hieq, hcocy⟩, hxP⟩
      have hxR : x ∈ R := hx.1
      have hxA1 : x ∈ A1 i := by
        obtain ⟨P', hP'block, hxP'⟩ := Set.mem_sUnion.mp hxblock
        have hP'eq : x ∈ A0 i ∪ A1 i := by rw [hAcov i]; exact ⟨P', hP'block, hxP'⟩
        rcases hP'eq with hxA0 | hxA1
        · exact absurd (Set.mem_iUnion.mpr ⟨i, hxA0⟩) (by
            have := hxR; rw [hR] at this; exact this)
        · exact hxA1
      exact hx.2 (Set.mem_union_left _ (hA1R_in_SCol x ⟨i, hxA1, hxR⟩))
    exact ⟨P, hPmem, hxP, hcocy, le_antisymm hle (Order.add_one_le_iff.mpr hlo)⟩
  -- `F↾A¹₀`'s top `CB`-level is constant `= y` (each top point lies in the top level of its
  -- cocenter-`y` rank-`λ+1` piece, where `block_const_on_top` gives its cocenter `y`).
  have hA10top : ∀ z ∈ CBLevel (F.restrict A10).func α.limitPart, (F.restrict A10).func z = y := by
    intro z hz
    have hz' : ((F.restrictEquiv A10) z : ↑F.domain) ∈ CBLevel F.func α.limitPart :=
      (cbLevel_block_iff F A10 hA10cl.isOpen α.limitPart z).mp hz
    obtain ⟨P, hP, hxP, hPcoc, hPrank⟩ := hA10_piece _ ((F.restrictEquiv A10) z).2
    have hPrank' : CBRank (F.restrict P).func = Order.succ α.limitPart := by
      rw [hPrank, Ordinal.add_one_eq_succ]
    have hw : (F.restrictEquiv P).symm ⟨_, hxP⟩ ∈ CBLevel (F.restrict P).func α.limitPart := by
      rw [cbLevel_block_iff F P (hA.isClopen P hP).isOpen α.limitPart, Homeomorph.apply_symm_apply]
      exact hz'
    have hval := block_const_on_top (F.restrict P) (hA.centered P hP) α.limitPart hPrank' _ hw
    have hEz : (F.restrict A10).func z = F.func ((F.restrictEquiv A10) z : ↑F.domain) := rfl
    rw [hEz, ← ScatFun.restrict_func_restrictEquiv_symm F P _ hxP, hval]
    exact hPcoc
  -- The `j`-th ray of `F↾A¹₀` at `y` has rank `≤ λ`, hence reduces into `maxFun λ`.
  have hA10ray : ∀ j, ScatFun.Reduces (F.rayOn y A10 j) (ScatFun.maxFun α.limitPart hlam_lt) := by
    intro j
    have hset : {z : ↑(F.restrict A10).domain | (F.restrict A10).func z ∈ RaySet Set.univ y j}
        = {z | (F.restrictEquiv A10 z : ↑F.domain) ∈
            (A10 ∩ {a | F.func a ∈ RaySet Set.univ y j})} := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun h => ⟨(F.restrictEquiv A10 z).2, h⟩, fun h => h.2⟩
    have hequiv : ScatFun.Equiv ((F.restrict A10).rayOn y Set.univ j) (F.rayOn y A10 j) := by
      rw [ScatFun.rayOn, ScatFun.rayOn, Set.univ_inter, hset]
      exact ScatFun.restrict_restrict_equiv F A10 _ Set.inter_subset_left
    have hrank : CBRank (F.rayOn y A10 j).func ≤ α.limitPart := by
      rw [← cbRank_eq_of_equiv hequiv]
      exact Order.lt_succ_iff.mp
        (ScatFun.rayOn_cbRank_lt (F.restrict A10) α.limitPart y hA10top Set.univ isOpen_univ j)
    exact ScatFun.reduces_maxFun_of_rank_le _ α.limitPart hlam_lt hrank
  ------------------------------------------------------------------------------------
  -- Assemble the five conclusion clauses.
  ------------------------------------------------------------------------------------
  refine ⟨Adiag, kidx, ⟨?clopen, ?disj, ?cover⟩, ?cols, ?diag, ?ranges, ?tend⟩
  case clopen =>
    intro i
    exact (hScl i).preimage (continuous_subtype_val.comp (F.restrictEquiv R).continuous)
  case disj =>
    intro i j hij
    exact Disjoint.preimage _ (hSdisj i j hij)
  case cover =>
    ext w; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hval : (F.restrictEquiv R w : ↑F.domain) ∈ R := (F.restrictEquiv R w).2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hScover hval)
    exact ⟨i, hi⟩
  case cols =>
    -- **Columns** (`:353-354`).  Reusable bound: over any raw column `SCol k`, the disjointified
    -- ray `(F↾R).rayOn y (SCol k) j ≤ F.rayOn y (A1 k) j ≤ replicate (v k)` (cocenter rigidity via
    -- `secondCase_column_rays_reducible`).  For the absorbing column `i₀`, `SColA i₀ = SCol i₀ ∪ A¹₀`
    -- and the ray splits (`rayOn_union_reduces_glBin`) with `A¹₀`'s ray `≤ maxFun λ ≤ v i₀`.
    intro i hi j
    have hColRay : ∀ (k : Fin n), ∃ m, ScatFun.Reduces
        ((F.restrict R).rayOn y {w | (F.restrictEquiv R w : ↑F.domain) ∈ SCol k} j)
        (ScatFun.glList (List.replicate m (v k))) := by
      intro k
      have hpglA1 : ScatFun.Equiv (F.restrict (A1 k)) (ScatFun.pglFinset (Mg k)) :=
        (show ScatFun.Equiv (F.restrict (A1 k)) (gM k) from ⟨hL1 k, hL1' k⟩).trans (hgpgl k)
      have hcentA1 : IsCentered (F.restrict (A1 k)).func :=
        isCentered_of_equiv
          (pgl_isCentered_of_regular (fun _ => ScatFun.glList (Mg k).toList)
            (scatFun_const_isRegularSeq _)) hpglA1
      obtain ⟨m, hm⟩ := secondCase_column_rays_reducible F y (A1 k) (Mg k)
        hcentA1 (hcocA1 k hcentA1) hpglA1 j
      refine ⟨m, ?_⟩
      simp only [hv]
      have hsubR : SCol k ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y j} ⊆ R :=
        Set.inter_subset_left.trans (Set.diff_subset.trans Set.inter_subset_right)
      have h1 : ScatFun.Equiv
          ((F.restrict R).rayOn y {w | (F.restrictEquiv R w : ↑F.domain) ∈ SCol k} j)
          (F.restrict (SCol k ∩ {x | F.func x ∈ RaySet Set.univ y j})) := by
        show ScatFun.Equiv ((F.restrict R).restrict
          {w : ↑(F.restrict R).domain | (F.restrictEquiv R w : ↑F.domain) ∈
            SCol k ∩ {x | F.func x ∈ RaySet Set.univ y j}}) _
        exact ScatFun.restrict_restrict_equiv F R _ hsubR
      have h2 : ScatFun.Reduces (F.restrict (SCol k ∩ {x | F.func x ∈ RaySet Set.univ y j}))
          (F.rayOn y (A1 k) j) :=
        restrict_reduces_of_subset F (fun x hx =>
          ⟨(Set.diff_subset.trans Set.inter_subset_left) hx.1, hx.2⟩)
      exact (h1.1.trans h2).trans hm
    by_cases hii₀ : (⟨i, hi⟩ : Fin n) = i₀
    · -- Absorbing column `i₀`.
      have hAdiag_split : Adiag i = {w | (F.restrictEquiv R w : ↑F.domain) ∈ SCol ⟨i, hi⟩}
          ∪ {w | (F.restrictEquiv R w : ↑F.domain) ∈ A10} := by
        show {w | (F.restrictEquiv R w : ↑F.domain) ∈ S i} = _
        rw [hS_col i hi]
        ext w
        simp only [hSColA_def, if_pos hii₀, Set.mem_union, Set.mem_setOf_eq]
      have htSCcl : IsClopen {w : ↑(F.restrict R).domain |
          (F.restrictEquiv R w : ↑F.domain) ∈ SCol ⟨i, hi⟩} :=
        (hSColcl _).preimage (continuous_subtype_val.comp (F.restrictEquiv R).continuous)
      have htA10cl : IsClopen {w : ↑(F.restrict R).domain |
          (F.restrictEquiv R w : ↑F.domain) ∈ A10} :=
        hA10cl.preimage (continuous_subtype_val.comp (F.restrictEquiv R).continuous)
      have htdisj : Disjoint
          {w : ↑(F.restrict R).domain | (F.restrictEquiv R w : ↑F.domain) ∈ SCol ⟨i, hi⟩}
          {w | (F.restrictEquiv R w : ↑F.domain) ∈ A10} :=
        Set.disjoint_left.mpr fun w hwc hwa =>
          (Set.disjoint_left.mp hA10_SCol) hwa (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hwc⟩)
      rw [hAdiag_split]
      obtain ⟨m1, hm1⟩ := hColRay ⟨i, hi⟩
      -- `A¹₀`'s ray reduces into `glList (replicate 1 (v ⟨i,hi⟩))`.
      have hm2 : ScatFun.Reduces
          ((F.restrict R).rayOn y {w | (F.restrictEquiv R w : ↑F.domain) ∈ A10} j)
          (ScatFun.glList (List.replicate 1 (v ⟨i, hi⟩))) := by
        have hsubR10 : A10 ∩ {x : ↑F.domain | F.func x ∈ RaySet Set.univ y j} ⊆ R :=
          Set.inter_subset_left.trans Set.diff_subset
        have h1' : ScatFun.Equiv
            ((F.restrict R).rayOn y {w | (F.restrictEquiv R w : ↑F.domain) ∈ A10} j)
            (F.rayOn y A10 j) := by
          show ScatFun.Equiv ((F.restrict R).restrict
            {w : ↑(F.restrict R).domain | (F.restrictEquiv R w : ↑F.domain) ∈
              A10 ∩ {x | F.func x ∈ RaySet Set.univ y j}})
            (F.restrict (A10 ∩ {a | F.func a ∈ RaySet Set.univ y j}))
          exact ScatFun.restrict_restrict_equiv F R _ hsubR10
        refine h1'.1.trans ((hA10ray j).trans ?_)
        rw [List.replicate_one]
        exact (hii₀ ▸ hmaxv0).trans (ScatFun.glList_single_equiv (v ⟨i, hi⟩)).1
      obtain ⟨m, hm⟩ := ScatFun.reduces_replicate_glBin hm1 hm2
      exact ⟨m, (ScatFun.rayOn_union_reduces_glBin (F.restrict R) y htSCcl htA10cl htdisj j).trans hm⟩
    · -- Ordinary column `i ≠ i₀`.
      have hAdiag_eq : Adiag i = {w | (F.restrictEquiv R w : ↑F.domain) ∈ SCol ⟨i, hi⟩} := by
        show {w | (F.restrictEquiv R w : ↑F.domain) ∈ S i} = _
        rw [hS_col i hi]
        ext w
        simp only [hSColA_def, if_neg hii₀, Set.union_empty, Set.mem_setOf_eq]
      rw [hAdiag_eq]
      exact hColRay ⟨i, hi⟩
  case diag =>
    -- **Diagonal blocks** (`:367-385`): ray-cuts (`i > n`) via the finite-cocenter block
    -- reduction (`secondCase_diagonal_block_reduces`), mop-up (`i = n`) by the residual argument.
    intro i hni
    rcases eq_or_lt_of_le hni with heq | hlt
    · -- `i = n`: the mop-up block `A^D_0`.
      subst heq
      have hAdiagn : Adiag n = {w | (F.restrictEquiv R w : ↑F.domain) ∈ SMop} := by
        show {w | (F.restrictEquiv R w : ↑F.domain) ∈ S n} = _; rw [hS_mop]
      have hEquiv := ScatFun.restrict_restrict_equiv F R SMop hSMop_subR
      -- **Mop-up reduction `F↾A^D_0 ≤ gl D`** (`:378-385`), now discharged by
      -- `secondCase_residual_mopup_reduces`: `SMop = Adiff ∖ W` is the pure diagonal residual,
      -- so pieces meeting it are diagonal (`hResdiag`) and their `SMop`-part avoids the `y`-ray at
      -- index `firstDiff y y_P` (`hReswindow`, from `a ∉ W ⊇ SRay (firstDiff y y_P)`).
      have hResdiag : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), (P ∩ SMop).Nonempty →
          hA.cocenterOf hP ≠ y := by
        rintro P hP ⟨x, hxP, hxm⟩
        obtain ⟨Q, ⟨hQ, hQne⟩, hxQ⟩ := hxm.1
        have hPQ : P = Q := huniq x P hP Q hQ hxP hxQ
        subst hPQ; exact hQne
      have hReswindow : ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
          ∀ a ∈ P, a ∈ SMop →
            F.func a ∉ RaySet Set.univ y (firstDiff y (hA.cocenterOf hP)) := by
        intro P hP hne a haP haSMop hray
        have hPBlk : a ∈ Blk (firstDiff y (hA.cocenterOf hP)) := ⟨P, ⟨hP, hne, rfl⟩, haP⟩
        exact haSMop.2 (Set.mem_iUnion.mpr
          ⟨firstDiff y (hA.cocenterOf hP), hPBlk, hray⟩)
      obtain ⟨m, hm⟩ := secondCase_residual_mopup_reduces α hα hFG F hFrank hA hfine D hDsub
        hDrep hDreal SMop hSMopcl hResdiag hReswindow
      exact ⟨m, by rw [hAdiagn]; exact hEquiv.1.trans hm⟩
    · -- `i > n`: the ray-cut `A^D_{i-n-1}` (a union of `Y_{i-n-1}`-many single-cocenter fibres).
      have hAdiagi : Adiag i = {w | (F.restrictEquiv R w : ↑F.domain) ∈ SRay (i - n - 1)} := by
        show {w | (F.restrictEquiv R w : ↑F.domain) ∈ S i} = _; rw [hS_ray i hlt]
      have hEquiv := ScatFun.restrict_restrict_equiv F R (SRay (i - n - 1)) (hSRay_subR (i - n - 1))
      obtain ⟨m, hm⟩ := secondCase_diagonal_block_reduces α hα hFG F hFrank hA hfine D hDrep
        {z | z ∈ hA.cocenterSet ∧ z ≠ y ∧ firstDiff y z = i - n - 1} (hYr_fin (i - n - 1))
        (fun z hz => hz.2.1) (SRay (i - n - 1)) (hSRay_fiber (i - n - 1))
      exact ⟨m, by rw [hAdiagi]; exact hEquiv.1.trans hm⟩
  case ranges =>
    -- **Range shrinking** (`:374`): the ray-cut `A^D_{i-n-1}` has `F`-image in `ray_{i-n-1}(y)`.
    -- The underlying point of `w'` lies in `Adiag i`, i.e. `∈ SRay (i-n-1) ⊆ F⁻¹(ray)`, and
    -- `kidx i = i-n-1` by definition.
    intro i hi
    rintro val ⟨w', rfl⟩
    have h2 := ((F.restrict R).restrictEquiv (Adiag i) w').2
    have h3 : (F.restrictEquiv R
        ((F.restrict R).restrictEquiv (Adiag i) w' : ↑(F.restrict R).domain) : ↑F.domain) ∈ S i :=
      h2
    rw [hS_ray i hi] at h3
    exact h3.2
  case tend =>
    -- **`kₙ → ∞`**: `kidx i = i - n - 1 → ∞`.
    exact Filter.tendsto_atTop_atTop.2 (fun b => ⟨b + n + 1, fun a ha => by
      simp only [hkidx_def]; omega⟩)

/-- **Second case — the geometric construction** (`6_double_successor_memo.tex:301-386`). Produces
the wedge data `n, v, w, D` (`v i = gl M_{g_i}` the verticals, `w = gl_i ω H_i`, `D` the diagonal
representatives) together with the three memoir obligations in the *decomposed* form consumed by
`diagonalTheorem_secondCase_setup`:

1. **membership** `w ⊕ ⋀(v ∣ gl D) ∈ FinGl 𝒢_{α+2}` — `genStep` wedge/`ω`-image clauses (cf.
   `wedgeGenerator_bounding`, `ScatFun/Generators/Basics.lean`);
2. **left inputs** — a clopen split `A⁰ ⊔ A¹ = univ` with `F↾A⁰ ≤ w`
   (`reduces_omega_of_forall_piece_le` on the `A⁰_{g'}` union) and `F↾A¹ ≤ ⋀(v ∣ gl D)`
   (`ScatFun.wedge_upper_bound`, fed by the Vertical Theorem's `A⁰/A¹` split, cocenter rigidity for
   the columns, and the `A^D_n` diagonal, `:349-386`);
3. **right inputs** — for each clopen `U ∋ y`, disjoint clopen `W, V ⊆ U` with `w ≤ F⇂W`
   (`intertwine_reductions_omega_centered`, `W = ⋃ W_{g'}`) and `⋀(v ∣ gl D) ≤ F⇂V`
   (`ScatFun.wedge_lower_bound`, the Disjointification Lemma, `:321-346`).

The representative selection is `diagonalTheorem_secondCase_representatives_{M,D}`; the per-`g`
pseudo-centered decomposition and Vertical Theorem application (`secondCase_blockData`) and the
wedge-bound clauses (`secondCase_wedge_le_coRestrict`, `Disjointification.lean`) are **proved**,
as is the `A^D_n` ray-cut diagonal family (`secondCase_ray_cut_diagonal_family`). This construction
is now **fully proved**. -/
theorem diagonalTheorem_secondCase_construction
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (hcase : ¬ ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1) :
    ∃ (n : ℕ) (v : Fin n → ScatFun) (w : ScatFun) (D : Finset ScatFun),
      (ScatFun.glBin w (ScatFun.wedge v (ScatFun.glList D.toList)) ∈
        ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun) ∧
      (∃ A0 A1 : Set ↑F.domain, IsClopen A0 ∧ IsClopen A1 ∧ A0 ∪ A1 = Set.univ ∧
        Disjoint A0 A1 ∧
        ScatFun.Reduces (F.restrict A0) w ∧
        ScatFun.Reduces (F.restrict A1) (ScatFun.wedge v (ScatFun.glList D.toList))) ∧
      (∀ U : Set Baire, IsClopen U → y ∈ U →
        ∃ W V : Set Baire, IsClopen W ∧ IsClopen V ∧ W ⊆ U ∧ V ⊆ U ∧ Disjoint W V ∧
          ScatFun.Reduces w (F.coRestrict W) ∧
          ScatFun.Reduces (ScatFun.wedge v (ScatFun.glList D.toList)) (F.coRestrict V)) := by
  classical
  -- Diagonal representatives `D` for `𝒫_D` (pieces with cocenter `≠ y`); fineness `hss.1.2`
  -- supplies the rank lower bound `> λ` each piece needs.
  obtain ⟨D, hDsub, hDrep, hDreal⟩ :=
    diagonalTheorem_secondCase_representatives_D (y := y) α hα hFG F hFrank hA hss.1.2
  -- Per-block Vertical-Theorem data for the `M`-columns.
  obtain ⟨n, gM, Mg, Hf, A0, A1, hgMc, hMgsub, hgpgl, hHsub, hA0cl, hA1cl,
      hAdisj, hAcov, hL0, hL1, hL1', hcocA1, hHg, hcorestr, hW, hMcover, hMreal⟩ :=
    secondCase_blockData α hα hFG F hFrank hA hss
  -- The wedge data:
  -- • `n` columns, `v i = gl M_{gᵢ}` the vertical of the `i`-th representative;
  -- • `w = gl_i ω (gl Hᵢ)` the gluing of the `ω`-images of the `𝒲`-finsets;
  -- • `D` the diagonal representatives.
  set v : Fin n → ScatFun := fun i => ScatFun.glList (Mg i).toList with hv_def
  set w : ScatFun :=
    ScatFun.glList ((List.finRange n).map (fun i => ScatFun.omega (ScatFun.glList (Hf i).toList)))
    with hw_def
  refine ⟨n, v, w, D, ?mem, ?left, ?right⟩
  case mem =>
    -- **Obligation 1** (`:305`): `w ⊕ ⋀(v ∣ gl D) ∈ FinGl 𝒢_{α+2}`, via the `FinGl` glBin
    -- closure (`finGl_glBin_mem`, now in `GlList.lean`), splitting into the two halves.
    refine ScatFun.finGl_glBin_mem ?hw ?hwedge
    case hw =>
      -- `w = gl_i ω(gl Hᵢ) ∈ FinGl 𝒢_{α+2}`. `finGl_glList_of_forall_finGl` reduces to each
      -- `ω(gl Hᵢ) ∈ FinGl 𝒢_{α+2}`. Per `i`: `ω(gl Hᵢ) ≡ gl Hᵢ` — forward by omega-regularity
      -- (`omega_glList_reduces_glList_of_omega_le` + `omega_le_self_of_mem_omegaRegularSet`),
      -- backward by the block-`0` embedding — and `gl Hᵢ ∈ FinGl 𝒢_{α+2}` since each
      -- `h ∈ Hᵢ ⊆ 𝒲_{α+1}` is in `FinGl 𝒢_{α+2}` (`omegaRegularSet_add_one_mem_finGl`).
      apply ScatFun.finGl_glList_of_forall_finGl
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      have hcollapse : ScatFun.Equiv
          (ScatFun.omega (ScatFun.glList (Hf i).toList)) (ScatFun.glList (Hf i).toList) :=
        ⟨ScatFun.omega_glList_reduces_glList_of_omega_le
            (fun h hh => ScatFun.omega_le_self_of_mem_omegaRegularSet _ _
              (hHsub i (Finset.mem_toList.mp hh))),
          ScatFun.reduces_block_gl (fun _ => ScatFun.glList (Hf i).toList) 0⟩
      refine finGl_closed_equiv _ ?_ hcollapse.symm
      apply ScatFun.finGl_glList_of_forall_finGl
      intro h hh
      exact omegaRegularSet_add_one_mem_finGl α hα (hHsub i (Finset.mem_toList.mp hh))
    case hwedge =>
      -- `⋀(v ∣ gl D)` is a `genStep` wedge generator (`wedgeFinset` over columns
      -- `Mg i ⊆ 𝒞_{α+1} ∪ ω{α+1}`, diagonal `D ⊆ 𝒞_{α+2}`), up to column dedup
      -- (`wedge_congr_equiv`), cf. `wedge_maxFun_minFun_mem_Generators_add_one`.
      exact secondCase_wedge_mem α hα Mg D hMgsub hDsub
        (secondCase_exists_nonempty_column α hα F hFrank hA hss.1.2 hcase gM Mg hgpgl hMcover)
  case left =>
    -- **Obligation 2 / left reduction** (`:349-386`). Split `univ = A⁰ ⊔ A¹` with
    -- `A⁰ = ⋃ᵢ A⁰ᵢ` (the block-`0` halves) and `A¹ = A⁰ᶜ`. The structural obligations
    -- (clopen, cover, disjoint) are discharged here; the two reductions are the content.
    set A := ⋃ i, A0 i with hAdef
    have hAcl : IsClopen A := isClopen_iUnion_of_finite hA0cl
    refine ⟨A, Aᶜ, hAcl, hAcl.compl, Set.union_compl_self A, disjoint_compl_right, ?_, ?_⟩
    · -- `F↾A⁰ ≤ w` (`:350`). Each `F↾A⁰ᵢ ≤ gl Hᵢ ≤ ω(gl Hᵢ)` (`hL0`, then block-`0` embedding)
      -- and `w = gl_i ω(gl Hᵢ)`. The `A⁰ᵢ` need *not* be pairwise disjoint (distinct
      -- representatives `gM i` may be mutually `Equiv`, so their blocks can overlap), so we
      -- disjointify the `ℕ`-padded family `Araw` (`disjointed`), obtain a clopen partition of
      -- `A⁰ = F↾A⁰.domain`, reduce `F↾A⁰` to the `gl` of its blocks
      -- (`scatFun_reduces_gl_of_domain_partition`), and finish blockwise into `w = gl_i ω(gl Hᵢ)`
      -- (`gl_reduces_of_pointwise`): block `k < n` reduces `F↾(Bd k) ≤ F↾A⁰ₖ ≤ gl Hₖ ≤ ω(gl Hₖ)`,
      -- block `k ≥ n` is empty.
      set f : Fin n → ScatFun := fun i => ScatFun.omega (ScatFun.glList (Hf i).toList) with hf_def
      set Araw : ℕ → Set ↑F.domain := fun k => if h : k < n then A0 ⟨k, h⟩ else ∅ with hAraw_def
      have hArawcl : ∀ k, IsClopen (Araw k) := by
        intro k; simp only [hAraw_def]; split
        · exact hA0cl _
        · exact isClopen_empty
      have hArawU : ⋃ k, Araw k = A := by
        rw [hAdef]; ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨k, hk⟩
          simp only [hAraw_def] at hk
          split at hk
          · exact ⟨_, hk⟩
          · exact absurd hk (by simp)
        · rintro ⟨i, hi⟩
          exact ⟨i.val, by simp only [hAraw_def, dif_pos i.isLt, Fin.eta]; exact hi⟩
      set Bd : ℕ → Set ↑F.domain := disjointed Araw with hBd_def
      have hBdcl : ∀ k, IsClopen (Bd k) := fun k => disjointed_clopen Araw hArawcl k
      have hBdle : ∀ k, Bd k ⊆ Araw k := fun k => disjointed_le Araw k
      have hBdU : ⋃ k, Bd k = A := by rw [hBd_def, iUnion_disjointed]; exact hArawU
      have hBdA : ∀ k, Bd k ⊆ A := fun k => hBdU ▸ Set.subset_iUnion _ k
      set g : ScatFun := F.restrict A with hg_def
      set P : ℕ → Set ↑g.domain :=
        fun k => {w | (F.restrictEquiv A w : ↑F.domain) ∈ Bd k} with hP_def
      have hdu : g.IsDisjointUnion P := by
        refine ⟨fun k => IsClopen.preimage (hBdcl k)
            (continuous_subtype_val.comp (F.restrictEquiv A).continuous), ?_, ?_⟩
        · intro i j hij
          rw [Set.disjoint_left]
          exact fun w hw hw' => (Set.disjoint_left.mp (disjoint_disjointed Araw hij) hw) hw'
        · ext w
          simp only [Set.mem_univ, iff_true]
          have hmem2 : (F.restrictEquiv A w : ↑F.domain) ∈ ⋃ k, Bd k := by
            rw [hBdU]; exact Subtype.mem (F.restrictEquiv A w)
          obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem2
          exact Set.mem_iUnion.mpr ⟨k, hk⟩
      refine (scatFun_reduces_gl_of_domain_partition g P hdu).trans ?_
      have hwgl : w = ScatFun.gl (fun k => ((List.finRange n).map f).getD k ScatFun.empty) := by
        rw [hw_def]; rfl
      rw [hwgl]
      apply ScatFun.gl_reduces_of_pointwise
      intro k
      by_cases hk : k < n
      · have hPk : ScatFun.Reduces (g.restrict (P k)) (F.restrict (Bd k)) :=
          (ScatFun.restrict_restrict_equiv F A (Bd k) (hBdA k)).1
        have hArawk : Araw k = A0 ⟨k, hk⟩ := by simp only [hAraw_def, dif_pos hk]
        have hsub : Bd k ⊆ A0 ⟨k, hk⟩ := hArawk ▸ hBdle k
        have hchain : ScatFun.Reduces (F.restrict (Bd k)) (f ⟨k, hk⟩) :=
          ((restrict_reduces_of_subset F hsub).trans (hL0 ⟨k, hk⟩)).trans
            (ScatFun.reduces_block_gl (fun _ => ScatFun.glList (Hf ⟨k, hk⟩).toList) 0)
        have hWblk : ((List.finRange n).map f).getD k ScatFun.empty = f ⟨k, hk⟩ := by
          rw [List.getD_eq_getElem _ _ (by simpa using hk)]
          simp [List.getElem_map, List.getElem_finRange]
        rw [hWblk]
        exact hPk.trans hchain
      · have hArawk : Araw k = ∅ := by simp only [hAraw_def, dif_neg hk]
        have hBdempty : Bd k = ∅ := Set.subset_eq_empty (hBdle k) hArawk
        have hdomempty : IsEmpty ↑(g.restrict (P k)).domain := by
          rw [Set.isEmpty_coe_sort, Set.eq_empty_iff_forall_notMem]
          rintro x ⟨h, hx⟩
          rw [hP_def] at hx
          exact absurd hx (by simp [hBdempty])
        exact ScatFun.reduces_of_isEmpty_domain hdomempty
    · -- `F↾A¹ ≤ ⋀(v ∣ gl D)` (`:355-386`) — **the geometric heart**.
      --
      -- **Provided solution.** Apply `ScatFun.wedge_upper_bound (F.restrict Aᶜ) v (glList D.toList)`
      -- `y` with an `ℕ`-indexed disjoint union `A : ℕ → Set ↑(F.restrict Aᶜ).domain` and its three
      -- premises `h_vertical` / `h_diag` / `h_ranges`:
      --
      -- 1. **Columns** (`:353-354`). Block `i < n` is `A¹ᵢ = A1 i` (transported into `Aᶜ`; note
      --    `A1 i ⊆ Aᶜ` need not hold literally — intersect, `A1 i ∩ Aᶜ`, absorbing the overlap
      --    into the diagonal). `hL1 i : F↾(A1 i) ≤ gM i` and `hgpgl i : Equiv (gM i) (pglFinset (Mg i))`,
      --    and the cocenter of `F↾A¹ᵢ` is `y`. `rigidityOfCocenter_reducibleByPieces`
      --    (`CenteredFunctions/Theorems.lean:581`, memoir `Rigidityofthecocenter`) then gives the
      --    ray premise: `(ray_j (F↾A¹ᵢ, y))_j` is reducible by finite pieces to `𝒫⁺(Mg i)`, i.e.
      --    `∃ m, Reduces (rayOn y (A i) j) (glList (List.replicate m (v i)))` with `v i = glList (Mg i)`.
      -- 2. **Rank-`λ+1` residue** (`:360-364`). If some `P ∈ 𝒫_M` has `CB(F↾P) = λ+1`, set
      --    `A¹₀ = ⋃(𝒫_M \ 𝒫'_M)`; `F↾A¹₀` is simple of rank `λ+1` distinguished at `y`
      --    (`Simpleiffcoincidenceofcocenters`), so `CB(ray_j) ≤ λ` and
      --    `reduces_maxFun_of_rank_le` (`DiagonalForLambdaPlusOne.lean:225`) gives
      --    `ray_j ≤ maxFun λ`; and `maxFun λ ≤ h` for some `h ∈ Mg i` with `CB h ≥ λ+1`
      --    (`maxFun_reduces_of_lam_lt_rank`, `Generators/Basics.lean:187`). Hence `A¹₀` merges into
      --    column `i` without breaking its ray premise.
      -- 3. **Diagonal `A^D_n`** (`:367-385`). Enumerate `Y' = cocenterSet \ {y}` (infinite by
      --    `IsStronglySolvableAt.cocenterSet_diff_singleton_infinite`) as `(yₙ)`, set
      --    `Aₙ = ⋃{P | y_P = yₙ}`, pick `kₙ` with `yₙ ∈ ray_{kₙ}(y)`, `A^D_n = Aₙ ∩ F⁻¹(ray_{kₙ}(y))`,
      --    `A^D_0 = ⋃ₙ (Aₙ \ A^D_n)`. Strong solvability ⟹ `yₙ → y`
      --    (`IsStronglySolvableAt.accPt_cocenterSet_iff`) ⟹ `kₙ → ∞` ⟹ `F(A^D_n) → y` (the
      --    `h_ranges` premise). Each diagonal block `≤ FinGl D` (the `h_diag` premise
      --    `∃ m, Reduces (F↾A^D_n) (glList (replicate m (glList D)))`):
      --    * `n > 0`: `F↾Aₙ ≤ 2(gl D)` — partition `Aₙ = ⊔_{g∈D} A^g_n`, each `F↾A^g_n`
      --      pseudo-centered so `verticalTheorem` gives `F↾A^g_n ≤ 2g`, then
      --      `reduces_glBin_of_clopen_partition` (memoir `Gluingasupperbound`).
      --    * `n = 0`: `F↾A^D_0 ≤ gl D` — per piece `h = F↾(P∩A^D_0) = F↾P⇂(B∖ray_k(y))`;
      --      `residualCorestrictionOfCentered` (`Theorems.lean:644`,
      --      `ResidualCorestrictionOfCentered`) gives `h ≤ FinGl D_g`, and
      --      `omega_reduces_pglFinset` (`PseudoCentered.lean:195`, `GluinglowerthanPgluing`) gives
      --      `ω D_g ≤ pgl D_g = g`.
      --
      -- **Now fully proved** by `secondCase_ray_cut_diagonal_family`: the reduction
      -- is `ScatFun.wedge_upper_bound` on `F.restrict Aᶜ`, with the `h_ranges` premise *derived*
      -- (`setsConvergeTo_of_subset_raySet`) from the diagonal blocks' images sitting in shrinking
      -- rays `RaySet y (kidx i)`, `kidx i → ∞`.  The family is built by *ray-index* (route B: `Blk r`,
      -- `SRay r` indexed by `firstDiff ȳ y_P`), not by an enumeration `(yₙ)` — this makes the mop-up's
      -- clopen-ness automatic; and the rank-`λ+1` residue `A¹₀` (item 2) is folded into a column `i₀`
      -- of rank `> λ+1` rather than the mop-up.  See `secondCase_ray_cut_diagonal_family`.
      obtain ⟨Adiag, kidx, hAdiag_du, hAdiag_vert, hAdiag_diag, hAdiag_ray, hkidx⟩ :=
        secondCase_ray_cut_diagonal_family α hα hFG F hFrank hA hss hcase D hDsub hDrep hDreal
          n gM Mg A0 A1 v hv_def hgMc hgpgl hA1cl hAdisj hAcov hL1 hL1' hcocA1 hMreal hMcover Aᶜ
          (by rw [hAdef])
      have hAdiag_ranges :
          SetsConvergeTo (fun i => Set.range ((F.restrict Aᶜ).restrict (Adiag i)).func) y :=
        setsConvergeTo_of_subset_raySet _ kidx
          (Filter.eventually_atTop.mpr ⟨n + 1, fun i hi => hAdiag_ray i (by omega)⟩) hkidx
      exact ScatFun.wedge_upper_bound (F.restrict Aᶜ) v (ScatFun.glList D.toList) y Adiag
        hAdiag_du hAdiag_vert hAdiag_diag hAdiag_ranges
  case right =>
    -- **Obligation 3 / right reduction** (`:321-346`). Per clopen `U ∋ y`: take the block clopens
    -- `Wᵢ ⊆ U` (from `hW`) and set `W = ⋃ᵢ Wᵢ`, `V = U ∩ Wᶜ`. Structural obligations discharged
    -- here; the two reductions are the content.
    intro U hUcl hyU
    -- Choose the column clopens `Wᵢ ⊆ U` (avoiding `y`, with `gl Hᵢ ≤ F⇂Wᵢ`) **pairwise
    -- disjoint** (greedy shrinking, `exists_pairwise_disjoint_clopen_of_forall_nbhd`), so the
    -- columns route into disjoint parts of `F⇂Wun`.
    obtain ⟨W, hWU, hWcl, hWy, hWred, hWdisj⟩ :=
      exists_pairwise_disjoint_clopen_of_forall_nbhd y
        (fun i Wset => ScatFun.Reduces (ScatFun.glList (Hf i).toList) (F.coRestrict Wset))
        (fun i U' hcl hy => hW i U' hcl hy) n id U hUcl hyU
    set Wun := ⋃ i, W i with hWundef
    have hWuncl : IsClopen Wun := isClopen_iUnion_of_finite hWcl
    have hWunU : Wun ⊆ U := Set.iUnion_subset hWU
    refine ⟨Wun, U ∩ Wunᶜ, hWuncl, hUcl.inter hWuncl.compl, hWunU, Set.inter_subset_left,
      disjoint_compl_right.mono_right Set.inter_subset_right, ?_, ?_⟩
    · -- `w ≤ F⇂Wun` (`:343-346`), `Wun = ⊔ᵢ Wᵢ` **disjoint**.
      --
      -- The memoir writes `w = gl_{g'} ω H_{g'}` and cites `Intertwinereductionsforomegacentered`,
      -- because its `H_{g'} ⊆ 𝒞_{α+1}` are *centered* and the outer `ω` is genuine. Here the Lean
      -- `Hᵢ ⊆ 𝒲_{α+1}` already carry the `ω` (`ω c ∈ 𝒲_{α+1}`), so the outer `ω` is redundant:
      -- `ω(gl Hᵢ) ≡ gl Hᵢ` (`omega_glList_equiv_self_of_subset_omegaRegularSet`). Thus each block
      -- of `w` reduces `ω(gl Hᵢ) ≤ gl Hᵢ ≤ F⇂Wᵢ ≡ (F⇂Wun)⇂Wᵢ` (`coRestrict_inter_reduces`), and
      -- the disjoint `Wᵢ` let the finite gluing collapse into `F⇂Wun`
      -- (`gl_coRestrict_disjoint_open_reduces`) — no `intertwine_reductions`, no
      -- strengthening of the Vertical Theorem.
      set Vfam : ℕ → Set Baire := fun k => if h : k < n then W ⟨k, h⟩ else ∅ with hVfam
      have hVopen : ∀ k, IsOpen (Vfam k) := by
        intro k; simp only [hVfam]
        by_cases hk : k < n
        · rw [dif_pos hk]; exact (hWcl _).isOpen
        · rw [dif_neg hk]; exact isOpen_empty
      have hVdisj : Pairwise (Disjoint on Vfam) := by
        intro i j hij
        simp only [Function.onFun, hVfam]
        by_cases hi : i < n <;> by_cases hj : j < n
        · rw [dif_pos hi, dif_pos hj]
          exact hWdisj (fun h => hij (by simpa using congrArg Fin.val h))
        · rw [dif_pos hi, dif_neg hj]; exact disjoint_bot_right
        · rw [dif_neg hi, dif_pos hj]; exact disjoint_bot_left
        · rw [dif_neg hi, dif_neg hj]; exact disjoint_bot_left
      rw [hw_def]
      refine (ScatFun.gl_reduces_of_pointwise
        (fun k => ((List.finRange n).map
          (fun i => ScatFun.omega (ScatFun.glList (Hf i).toList))).getD k ScatFun.empty)
        (fun k => (F.coRestrict Wun).coRestrict (Vfam k)) (fun k => ?_)).trans
        (ScatFun.gl_coRestrict_disjoint_open_reduces (F.coRestrict Wun) Vfam hVopen hVdisj)
      dsimp only
      by_cases hk : k < n
      · rw [show ((List.finRange n).map
              (fun i => ScatFun.omega (ScatFun.glList (Hf i).toList))).getD k ScatFun.empty
            = ScatFun.omega (ScatFun.glList (Hf ⟨k, hk⟩).toList) by
          rw [List.getD_eq_getElem _ _ (by simpa using hk)]
          simp [List.getElem_map, List.getElem_finRange],
          show Vfam k = W ⟨k, hk⟩ by simp only [hVfam, dif_pos hk]]
        refine ((omega_glList_equiv_self_of_subset_omegaRegularSet α
          (by simpa using omega1_add_nat α hα 1) (Hf ⟨k, hk⟩) (hHsub ⟨k, hk⟩)).1).trans ?_
        exact (hWred ⟨k, hk⟩).trans
          (coRestrict_inter_reduces F (Set.subset_iUnion W ⟨k, hk⟩) (Set.Subset.refl _))
      · rw [show ((List.finRange n).map
              (fun i => ScatFun.omega (ScatFun.glList (Hf i).toList))).getD k ScatFun.empty
            = ScatFun.empty from List.getD_eq_default _ _ (by simpa using not_lt.mp hk)]
        exact ScatFun.empty_reduces _
    · -- `⋀(v ∣ gl D) ≤ F⇂V` (`:321-342`), `V = U ∩ Wᶜ ∋ y`.
      --
      -- **Provided solution.** Apply `ScatFun.wedge_lower_bound (F.coRestrict V) v (glList D.toList)`
      -- `y`, the **Disjointification Lemma** (`ScatFun/Wedge/LowerBound.lean:830`). Anchors: for
      -- each column `i`, pick `Pᵢ ∈ 𝒫_M` with `F↾Pᵢ ≡ gM i` (`hMcover`) and let `xᵢ` be a center of
      -- `F↾Pᵢ` (`x : Fin n → ↥(F⇂V).domain`, `hxy : (F⇂V)(xᵢ) = y`). Verify:
      --   * `h_vert` (`:328-333`): for each `i`, open `U' ∋ xᵢ`, a reduction `(σ,τ)` of
      --     `v i = glList (Mg i)` into `F⇂V` with `im σ ⊆ U'` and `y ∉ closure (im (F∘σ))`. Since
      --     `xᵢ` is a center of `F↾Pᵢ ≡ gM i`, `centerInvariance_reduce`
      --     (`CenteredFunctions/Theorems.lean:146`, `Centerinvariance`) reduces `gM i` into
      --     `F↾(Pᵢ ∩ U')`; the cocenter of `F↾(Pᵢ ∩ U')` is `y`, so `rigidityOfCocenter_separation`
      --     (`Theorems.lean:299`, `Rigidityofthecocenter`) supplies `y ∉ closure`. Transport across
      --     `gM i ≡ pglFinset (Mg i)` (`hgpgl i`) and `pglFinset (Mg i) ≡ glList (Mg i) = v i`.
      --   * `h_diag` (`:335-339`): for open `U'' ∋ y`, a reduction of `gl D` into `F⇂V` with
      --     `im (F∘σ) ⊆ U''` and `y ∉ closure`. Enough per `g ∈ D`: strong solvability clause 2
      --     (`hss.2 … U''`) gives `P ∈ 𝒫_D` with `F↾P ≡ g` and `y_P ∈ U''`; pick a clopen
      --     `V' ⊆ U''` around `y_P` avoiding `y`; `F↾P` centered with cocenter `y_P` gives
      --     `g ≤ F⇂V'` (`reduces_coRestrict_cocenter_nbhd`-style), with the closure avoiding `y`.
      --     Assemble over `D` via `gl_reduces_of_pointwise` / `glList`.
      --
      -- Wired to `secondCase_wedge_le_coRestrict` (the `wedge_lower_bound` application); its two
      -- clause obligations `secondCase_wedge_vertical_clause` / `secondCase_wedge_diag_clause`
      -- are proved in `Disjointification.lean`.
      have hpos : 0 < n := by
        obtain ⟨s, hs⟩ := secondCase_exists_nonempty_column α hα F hFrank hA hss.1.2 hcase gM Mg
          hgpgl hMcover
        obtain ⟨i, -⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hs)
        exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have hyV : y ∈ U ∩ Wunᶜ := ⟨hyU, by
        simp only [Set.mem_compl_iff, hWundef, Set.mem_iUnion, not_exists]; exact hWy⟩
      rw [hv_def]
      exact secondCase_wedge_le_coRestrict α F hA hss hpos gM Mg D hgpgl hMreal hDreal
        (U ∩ Wunᶜ) (hUcl.inter hWuncl.compl) hyV

/-- **Diagonal Theorem — second case** (`6_double_successor_memo.tex:301-386`). The hypothesis
`hcase` is the negation of the first case: some `P ∈ 𝒫_M` (cocenter `y`) has `CB(F↾P) ≠ λ+1`,
i.e. (as `CB(F↾P) ≥ λ+1` always) `CB(F↾P) > λ+1`.

## Provided solution (`:301-386`)

Let `𝒫'_M = {P ∈ 𝒫_M | CB(F↾P) > λ+1}` and pick finite representatives `M ⊆ 𝒞_{α+2}` for
`{F↾P | P ∈ 𝒫'_M}` (`FGconsequences`); write `g' = pgl M_{g'}` with
`M_{g'} ⊆ 𝒞_{α+1} ∪ ω{α+1}`, and `A_{g'} = ⋃{P ∈ 𝒫'_M | F↾P ≡ g'}`. Each `F↾A_{g'}` is
**pseudo-centered**, so the **Vertical Theorem** (`verticalTheorem`, `PseudoCentered.lean`) gives
`H_{g'} ⊆ 𝒲_{α+1}`, a clopen `W_{g'} ⊆ U` with `y ∉ W_{g'}`, and a clopen split
`A_{g'} = A⁰_{g'} ⊔ A¹_{g'}` with `F↾A⁰_{g'} ≤ ω H_{g'} ≤ F↾A⁰_{g'}⇂W_{g'}` and, for all clopen
`V ∋ y`, `F↾A¹_{g'} ≤ g' ≤ F↾A¹_{g'}⇂V`. Let `D` = representatives for `{F↾P | P ∈ 𝒫_D}` (`∅` if
`𝒫_D = ∅`) and `w = gl_{g'∈M} ω H_{g'}`. Set **`g := w ⊕ ⋀((M_{g'})_{g'∈M} ∣ D)`**. Then:

* **Right reduction** `g ≤ F⇂U` (`:321-346`): `w ≤ F⇂W` (`W = ⋃ W_{g'}`,
  `intertwine_reductions_omega_centered`) and `⋀(...∣D) ≤ F⇂V` for a clopen `V ∋ y` disjoint from
  `W`, the latter by the **Disjointification Lemma** (`ScatFun.wedge_lower_bound`,
  `ScatFun/Wedge/LowerBound.lean`, **proved**) whose two premises are center-invariance
  (`Centerinvariance`, Fact 4.2) + cocenter rigidity (`Rigidityofthecocenter`, Prop 4.4) for the
  columns, and strong solvability clause 2 for the diagonal `gl D`. Combine via
  `Gluingasupperbound`: `g ≤ F⇂W ⊕ F⇂V ≤ F⇂U`.
* **Left reduction** `F ≤ g` (`:349-386`): `A⁰ = ⨆_{g'} A⁰_{g'}` is clopen with `F↾A⁰ ≤ w`; for
  `A¹ = A \ A⁰` we use the **wedge upper bound** (`ScatFun.wedge_upper_bound`,
  `ScatFun/Wedge/UpperBound.lean`, **proved**). The columns are the `A¹_{g'}` (rays reducible by
  pieces to `M_{g'}` by rigidity; a rank-`λ+1` residue `A¹_0` from `𝒫_M \ 𝒫'_M` is absorbed into
  some column, `:355-359`), and the diagonal is the `𝒫_D`-part cut along rays of `y`: enumerate
  `Y' = {y_P} \ {y}` as `(y_n)`, set `A^D_n = A_n ∩ F⁻¹(ray_{k_n}(y))` (`A_n = ⋃{P | y_P = y_n}`,
  `y_n ∈ ray_{k_n}(y)`) and `A^D_0 = ⋃_{n} (A_n \ A^D_n)`; strong solvability gives `y_n → y`,
  hence `k_n → ∞` and `F(A^D_n) → y`. Each block reduces into `FinGl D`: for `n > 0`,
  `F↾A_n ≤ 2(gl D)` (each `F↾A^{g'}_n` pseudo-centered, `verticalTheorem` gives `≤ 2g'`); for
  `n = 0`, `F↾A^D_0 ≤ gl_{g'∈D} ω D_{g'} ≤ gl D` via `residualCorestrictionOfCentered`
  (`CenteredFunctions/Theorems.lean:644`) and `ScatFun.omega_reduces_pglFinset`
  (`PseudoCentered.lean:195`).

Membership `w ⊕ ⋀(...∣D) ∈ FinGl 𝒢_{α+2}` follows from the `genStep` wedge and `ω`-image clauses
(cf. `secondCase_wedge_mem`, this file, proved).

## Assembly (current status)

`diagonalTheorem_secondCase_setup` is now **proved by dispatch**: it obtains the wedge data
`n, v, w, D` (with `v i = gl M_{g'_i}` the verticals, `w = gl_{i} ω H_i`, `D` the diagonal
representatives) from `diagonalTheorem_secondCase_construction`, and repackages the three
`_mem`/`_left`/`_right` facts into the single `g = w ⊕ ⋀(v ∣ D) = glBin w (wedge v (glList D))`
obligation via `ScatFun.reduces_glBin_of_clopen_partition` (left) and
`ScatFun.reduces_glBin_coRestrict_of_disjoint` (right). It carries **no gap of its own**.

The three obligations were discharged in `diagonalTheorem_secondCase_construction`:

* **membership** `g ∈ FinGl 𝒢_{α+2}` — **proved**: `ScatFun.finGl_glBin_mem` splitting into `w`
  (`genStep` `ω`-image clauses) and the wedge (`secondCase_wedge_mem`, via the now-proved
  `wedge_reindex_reduces`);
* **left** `F ≤ g` — `F↾A⁰ ≤ w` **proved** (`scatFun_reduces_gl_of_domain_partition` +
  `gl_reduces_of_pointwise` over the `disjointed` block-`0` halves); `F↾A¹ ≤ ⋀(v ∣ gl D)` via
  `ScatFun.wedge_upper_bound` is **proved** (the `A^D_n` ray-cut diagonal,
  `secondCase_ray_cut_diagonal_family`);
* **right** `g ≤ F⇂U` — `⋀(v ∣ gl D) ≤ F⇂V` **proved** (`secondCase_wedge_le_coRestrict`,
  `ScatFun.wedge_lower_bound`), with its two clauses
  `secondCase_wedge_vertical_clause`/`secondCase_wedge_diag_clause` proved in
  `Disjointification.lean`; `w ≤ F⇂W` is likewise
  **proved** — the memoir's `Intertwinereductionsforomegacentered` step is bypassed via
  `omega_glList_equiv_self_of_subset_omegaRegularSet` (`ω(gl Hᵢ) ≡ gl Hᵢ` since the Lean `𝒲`-valued
  `Hᵢ` already absorb the `ω`), so the *plain* block reductions `gl Hᵢ ≤ F⇂Wᵢ` feed a disjoint-clopen
  gluing (`exists_pairwise_disjoint_clopen_of_forall_nbhd` +
  `ScatFun.gl_coRestrict_disjoint_open_reduces`); no strengthening of the Vertical Theorem is needed.

The *left* `A^D_n` ray-cut diagonal family feeding `ScatFun.wedge_upper_bound` is now proved
(`secondCase_ray_cut_diagonal_family`), so this file is **complete**.

Upstream is fully proved: `ScatFun.verticalTheorem` and
`ScatFun.exists_pglFinset_decomp_of_centered_doubleSucc` are proved in `PseudoCentered.lean`;
the variable-rank block data `secondCase_singleBlockData` (`BlockData.lean`, re-instantiating the
Vertical Theorem at a smaller double-successor base) and the boundary rank-`λ+1` kernel
`secondCase_block_reduces_glBin_lowRank` (this file) are also proved. -/
theorem diagonalTheorem_secondCase_setup
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (hcase : ¬ ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1) :
    ∃ (n : ℕ) (v : Fin n → ScatFun) (w : ScatFun) (D : Finset ScatFun),
      (ScatFun.glBin w (ScatFun.wedge v (ScatFun.glList D.toList)) ∈
        ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun) ∧
      ScatFun.Reduces F (ScatFun.glBin w (ScatFun.wedge v (ScatFun.glList D.toList))) ∧
      (∀ U : Set Baire, IsClopen U → y ∈ U →
        ScatFun.Reduces (ScatFun.glBin w (ScatFun.wedge v (ScatFun.glList D.toList))) (F.coRestrict U)) := by
  obtain ⟨n, v, w, D, hmem, ⟨A0, A1, hA0cl, hA1cl, hcover, hdisj, hL0, hL1⟩, hright⟩ :=
    diagonalTheorem_secondCase_construction α hα hFG F hFrank hA hss hcase
  refine ⟨n, v, w, D, hmem, ?_, ?_⟩
  · exact ScatFun.reduces_glBin_of_clopen_partition w
      (ScatFun.wedge v (ScatFun.glList D.toList)) hA0cl hA1cl hcover hdisj hL0 hL1
  · intro U hUcl hyU
    obtain ⟨W, V, hWcl, hVcl, hWU, hVU, hWVdisj, hwW, hwedgeV⟩ := hright U hUcl hyU
    exact ScatFun.reduces_glBin_coRestrict_of_disjoint w
      (ScatFun.wedge v (ScatFun.glList D.toList)) hWcl hVcl hWU hVU hWVdisj hwW hwedgeV

/-- **Diagonal Theorem — second case** (`6_double_successor_memo.tex:301-386`). See
`diagonalTheorem_secondCase_setup` for the construction of `g = w ⊕ ⋀(v ∣ D)` and the memoir map;
this just unpacks it. -/
theorem diagonalTheorem_secondCase
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (hcase : ¬ ∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
      CBRank (F.restrict P).func = α.limitPart + 1) :
    ∃ g ∈ ScatFun.FinGl (ScatFun.Generators (α + 1 + 1)).toFinFun,
      ScatFun.Reduces F g ∧
        ∀ U : Set Baire, IsClopen U → y ∈ U → ScatFun.Reduces g (F.coRestrict U) := by
  obtain ⟨n, v, w, D, hmem, hleft, hright⟩ :=
    diagonalTheorem_secondCase_setup α hα hFG F hFrank hA hss hcase
  exact ⟨_, hmem, hleft, hright⟩


end
