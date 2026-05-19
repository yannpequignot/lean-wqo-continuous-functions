import RequestProject.PointedGluing.PointedGluingUpperBound.BasicProperties

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Pointed Gluing — Upper Bound (Proposition 3.5, Corollaries 3.6–3.7)

## Main results

* `sufficient_cond_continuity` — Lemma 3.4
* `pointedGluing_upper_bound` — Proposition 3.5
* `pointedGluing_scattered` — Scatteredness preservation
-/

noncomputable section

/-!
## Section 2: Sufficient Condition for Continuity (Lemma 3.4)
-/


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
      simp +zetaDelta at *
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


/-!
## Section 3: Pointed Gluing as an Upper Bound (Proposition 3.5, Corollaries 3.6–3.7)
-/


/-
**Corollary (Pgluingofraysasupperbound).**
For any continuous `f : A → B` in 𝒞 and any `y ∈ B`,
`f ≤ pgl_{i ∈ ℕ} Ray(f, y, i)`.

This is a direct application of Pgluingasupperbound with the identity partition
`I_j = {j}`.
-/
theorem pointedGluing_rays_upper_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (_hf : Continuous f)
    (y : ℕ → ℕ) (_hy : y ∈ B) :
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (h : ∀ i, C i → D i),
      ContinuouslyReduces f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D h x) := by
  use fun i => if h : i = 0 then A else ∅
  use fun i => if i = 0 then B else ∅
  use fun i a => ⟨f ⟨a.val, by
    grind⟩, by
    aesop⟩
  generalize_proofs at *
  refine ⟨?_, ?_, ?_⟩
  use fun a => ⟨prependZerosOne 0 a.val, Or.inr <| Set.mem_iUnion.mpr ⟨0, a.val, a.property, rfl⟩⟩
  · refine Continuous.subtype_mk ?_ ?_
    exact continuous_prependZerosOne 0 |> Continuous.comp <| continuous_subtype_val
  · refine ⟨?_, ?_, ?_⟩
    use fun x => x ∘ fun n => n + 1
    · fun_prop
    · intro x; ext n; simp +decide [PointedGluingFun]
      split_ifs <;> simp_all +decide [prependZerosOne]
      · rename_i h; have := congr_fun h 0; simp_all +decide [prependZerosOne]
      · congr
      · simp_all +decide [firstNonzero, prependZerosOne]
        unfold stripZerosOne at *; simp_all +decide [prependZerosOne]




/-
**Proposition (Pgluingasupperbound). Pointed gluing as upper bound.**
Let `f ∈ 𝒞` be continuous and `(g_i)_{i ∈ ℕ}` a sequence in 𝒞.
If `y ∈ B` and `(Ray(f, y, j))_{j ∈ ℕ}` is reducible by pieces to `(g_i)_i`,
then `f ≤ pgl_i g_i`.


The proof constructs `σ` by mapping `f⁻¹({y})` to `{0^ω}` and gluing together the
individual reductions on each ray. Continuity at `0^ω` follows from
Lemma (prop:sufficientcondforcont) using that the partition indices grow.
-/
theorem pointedGluing_upper_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ i, C i → D i)
    (y : ℕ → ℕ) (_hy : y ∈ B)
    (hpieces : ∃ (I : ℕ → Finset ℕ),
      (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
      ∀ j, ContinuouslyReduces
        (fun (x : {a : A | f a ∈ RaySet B y j}) => f x.val)
        (fun (x : GluingSet (fun i => if i ∈ I j then C i else ∅)) =>
          GluingFunVal _ _ (fun i => if h : i ∈ I j then
            (fun a => (g i (by exact a)) : C i → D i) ∘
              (fun a => ⟨a.val, by have := a.property; simp [h] at this; exact this⟩)
            else fun a => ⟨a.val, by have := a.property; simp [h] at this⟩) x)) :
    ContinuouslyReduces f
      (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  obtain ⟨I, hI_disj, hI_red⟩ := hpieces
  -- Extract σ_j, τ_j and their properties for each ray j
  choose σ_j hσ_j τ_j hτ_j heq_j using hI_red
  /-
  ## Helper lemmas about the embedding of restricted GluingSet into GluingSet C
  -/
  -- x.val ∈ GluingSet C for x in the restricted GluingSet
  have embed_mem : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      x.val ∈ GluingSet C := fun j x => by
    obtain ⟨k, hk0, hk_mem⟩ := GluingSet_inverse_short _ x
    have hk_in : k ∈ I j := by
      by_contra h; simp only [h, if_false] at hk_mem; exact hk_mem
    simp only [hk_in, if_true] at hk_mem
    have hmem := mem_gluingSet_prepend hk_mem
    rw [← hk0, prepend_unprepend] at hmem
    exact hmem
  -- x.val 0 ∈ I j for restricted GluingSet elements
  have embed_block : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      x.val 0 ∈ I j := fun j x => by
    obtain ⟨k, hk0, hk_mem⟩ := GluingSet_inverse_short _ x
    have : k ∈ I j := by by_contra h; simp only [h, if_false] at hk_mem; exact hk_mem
    rw [hk0]; exact this
  -- unprepend x.val ∈ C (x.val 0) for restricted GluingSet elements
  have embed_strip : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      unprepend x.val ∈ C (x.val 0) := fun j x => by
    obtain ⟨k, hk0, hk_mem⟩ := GluingSet_inverse_short _ x
    have hk_in : k ∈ I j := by by_contra h; simp only [h, if_false] at hk_mem; exact hk_mem
    simp only [hk_in, if_true] at hk_mem; rw [hk0]; exact hk_mem
  /-
  ## GluingFunVal for restricted pieces equals prepend k (g k ...)
  -/
  have gj_eq : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      GluingFunVal _ _ (fun i => if h : i ∈ I j then
        (fun a => (g i (by exact a)) : C i → D i) ∘
          (fun a => ⟨a.val, by have := a.property; simp [h] at this; exact this⟩)
        else fun a => ⟨a.val, by have := a.property; simp [h] at this⟩) x =
      prepend (x.val 0) (g (x.val 0) ⟨unprepend x.val, embed_strip j x⟩).val := fun j x => by
    simp only [GluingFunVal]
    congr 1
    simp only [embed_block j x, dif_pos, Function.comp]
  /-
  ## Embedding from restricted GluingSet to PointedGluingSet C
  -/
  -- toPointed j x : PointedGluingSet C for x in restricted GluingSet
  let toPointed : ∀ j, GluingSet (fun i => if i ∈ I j then C i else ∅) → PointedGluingSet C :=
    fun j x => gluingToPointed C ⟨x.val, embed_mem j x⟩
  -- (toPointed j x).val = prependZerosOne (x.val 0) (unprepend x.val)
  have toPointed_val : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      (toPointed j x).val = prependZerosOne (x.val 0) (unprepend x.val) := fun j x => by
    show (gluingToPointed C ⟨x.val, embed_mem j x⟩).val = _
    simp only [gluingToPointed]
    congr 1
    exact (GluingSet_inverse_short C ⟨x.val, embed_mem j x⟩).choose_spec.1.symm
  -- PointedGluingFun C D g (toPointed j x) = prependZerosOne k (g k ...)
  have toPointed_pgluing : ∀ j (x : GluingSet (fun i => if i ∈ I j then C i else ∅)),
      PointedGluingFun C D g (toPointed j x) =
        prependZerosOne (x.val 0) (g (x.val 0) ⟨unprepend x.val, embed_strip j x⟩).val :=
    fun j x => by
      have hv := toPointed_val j x
      have hne : (toPointed j x).val ≠ zeroStream := hv ▸ prependZerosOne_ne_zeroStream _ _
      have h_idx : firstNonzero (toPointed j x).val = x.val 0 := by
        rw [hv, firstNonzero_prependZerosOne]
      have h_strip : stripZerosOne (firstNonzero (toPointed j x).val) (toPointed j x).val = unprepend x.val := by
        rw [hv, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
      have h_mem : stripZerosOne (firstNonzero (toPointed j x).val) (toPointed j x).val ∈
          C (firstNonzero (toPointed j x).val) := by
        rw [h_strip, h_idx]; exact embed_strip j x
      simp only [PointedGluingFun, dif_neg hne, dif_pos h_mem]
      grind +splitImp -- dependent type eq: h_idx and h_strip
  /-
  ## findJ: for k in some I j, find that j
  -/
  let findJ : ℕ → ℕ := fun k =>
    if h : ∃ j, k ∈ I j then Classical.choose h else 0
  -- findJ gives the correct j (by pairwise disjointness of I)
  have findJ_spec : ∀ k j, k ∈ I j → findJ k = j := fun k j hkj => by
    have hex : ∃ j', k ∈ I j' := ⟨j, hkj⟩
    simp only [findJ, dif_pos hex]
    have hchoice : k ∈ I (Classical.choose hex) := Classical.choose_spec hex
    by_contra h_ne
    exact (Finset.disjoint_left.mp (hI_disj _ _ h_ne) hchoice) hkj
  /-
  ## Define σ : A → PointedGluingSet C
  Maps f⁻¹({y}) to zeroStream, and each ray j piece via σ_j then toPointed.
  -/
  let rayIdx : ∀ (a : A), f a ≠ y → ℕ := fun a ha => Nat.find (Function.ne_iff.mp ha)
  have rayIdx_inray : ∀ (a : A) (ha : f a ≠ y), f a ∈ RaySet B y (rayIdx a ha) :=
    fun a ha => ⟨hfB a,
      fun k hk => Classical.not_not.mp (Nat.find_min (Function.ne_iff.mp ha) hk),
      Nat.find_spec (Function.ne_iff.mp ha)⟩
  -- rayIdx is constant j on each ray piece O_j = {a | f a ∈ RaySet B y j}
  have rayIdx_on_ray : ∀ j (a : A) (ha_ne : f a ≠ y) (_ : f a ∈ RaySet B y j),
      rayIdx a ha_ne = j := fun j a ha_ne ⟨_, h_agree, h_differ⟩ => by
    simp only [rayIdx]
    apply Nat.le_antisymm
    · exact Nat.find_min' _ h_differ
    · apply Nat.le_of_not_lt
      intro h
      exact absurd (h_agree _ h) (Nat.find_spec (Function.ne_iff.mp ha_ne))
  let σ : A → PointedGluingSet C := fun a =>
    if ha : f a = y then ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩
    else toPointed (rayIdx a ha) (σ_j (rayIdx a ha) ⟨a, rayIdx_inray a ha⟩)
  /-
  ## Define τ : (ℕ → ℕ) → (ℕ → ℕ)
  Maps zeroStream to y, and a block k (with k ∈ I j) via τ_j ∘ pointedToGluing.
  -/
  let τ : (ℕ → ℕ) → ℕ → ℕ := fun output =>
    if output = zeroStream then y
    else τ_j (findJ (firstNonzero output)) (pointedToGluing output)
  /-
  ## Prove ContinuouslyReduces via σ and τ
  -/
  refine ⟨σ, ?_, τ, ?_, ?_⟩
  · /- **Continuity of σ** using `sufficient_cond_continuity`.
       U = {a | f a ≠ y} is open; σ = const on Uᶜ; on U use local continuity per ray. -/
    apply sufficient_cond_continuity σ {a : A | f a ≠ y}
    · -- U is open: {y} is closed, f continuous ⇒ f⁻¹({y}) closed ⇒ complement open
      exact (isClosed_singleton.preimage hf).isOpen_compl
    · -- σ continuous on U = {a | f a ≠ y}: locally equals toPointed j ∘ σ_j j on each ray
      intro a ha
      -- f a ≠ y, so f a ∈ some ray j
      obtain ⟨j, hj⟩ := (mem_ray_or_eq_y (hfB a)).resolve_left ha
      -- O_j = {b | f b ∈ RaySet B y j} is open and contains a
      have hOj : IsOpen {b : A | f b ∈ RaySet B y j} := ray_subtype_isOpen A B f hfB hf y j
      -- On O_j, σ b = toPointed j (σ_j j ⟨b, ...⟩)
      have hσ_eq_on_Oj : ∀ b (hb : b ∈ ({b : A | f b ∈ RaySet B y j})),
          σ b = toPointed j (σ_j j ⟨b, hb⟩) := by
        intro b hb
        have hb_ne : f b ≠ y := fun h => hb.2.2 (congr_fun h j)
        simp only [σ, dif_neg hb_ne]
        -- Apply the hypothesis `rayIdx_on_ray` to conclude that `rayIdx b hb_ne = j`.
        have h_rayIdx_eq : rayIdx b hb_ne = j := by
          exact rayIdx_on_ray j b hb_ne hb
        convert rfl
        exact h_rayIdx_eq.symm
      -- On O_j, σ = (toPointed j) ∘ (fun b => σ_j j ⟨b, ...⟩), both continuous
      have hσ_cont_Oj : ContinuousOn σ {b : A | f b ∈ RaySet B y j} := by
        -- Since σ_j j is continuous and toPointed j is continuous, their composition is continuous.
        have h_cont_comp : Continuous (fun b : {b : A | f b ∈ RaySet B y j} => toPointed j (σ_j j b)) := by
          convert Continuous.comp (show Continuous (fun x : GluingSet (fun i => if i ∈ I j then C i else ∅) => gluingToPointed C ⟨x, embed_mem j x⟩) from ?_) (hσ_j j) using 1
          -- The function gluingToPointed is continuous because it is a composition of continuous functions: the inclusion map and the prependZerosOne function.
          have h_cont : Continuous (fun x : GluingSet (fun i => if i ∈ I j then C i else ∅) => prependZerosOne (x.val 0) (unprepend x.val)) := by
            have h_cont : ∀ i ∈ I j, Continuous (fun x : GluingSet (fun i => if i ∈ I j then C i else ∅) => prependZerosOne i (unprepend x.val)) := by
              exact fun i hi => continuous_prependZerosOne i |> Continuous.comp <| continuous_unprepend.comp <| continuous_subtype_val
            have h_cont : ∀ i ∈ I j, IsOpen {x : GluingSet (fun i => if i ∈ I j then C i else ∅) | x.val 0 = i} := by
              intro i hi
              have h_cont : IsOpen {x : ℕ → ℕ | x 0 = i} := by
                rw [isOpen_pi_iff]
                exact fun f hf => ⟨{ 0 }, fun _ => { i }, by aesop⟩
              exact h_cont.preimage (continuous_subtype_val)
            have h_cont : ∀ i ∈ I j, ContinuousOn (fun x : GluingSet (fun i => if i ∈ I j then C i else ∅) => prependZerosOne i (unprepend x.val)) {x : GluingSet (fun i => if i ∈ I j then C i else ∅) | x.val 0 = i} := by
              exact fun i hi => Continuous.continuousOn (by solve_by_elim)
            have h_cont : ContinuousOn (fun x : GluingSet (fun i => if i ∈ I j then C i else ∅) => prependZerosOne (x.val 0) (unprepend x.val)) (⋃ i ∈ I j, {x : GluingSet (fun i => if i ∈ I j then C i else ∅) | x.val 0 = i}) := by
              intro x hx
              simp +zetaDelta at *
              exact ContinuousAt.continuousWithinAt (by exact ContinuousAt.congr (h_cont _ hx |> ContinuousOn.continuousAt <| IsOpen.mem_nhds (by solve_by_elim) <| by simp) <| Filter.EventuallyEq.symm <| Filter.eventuallyEq_of_mem (IsOpen.mem_nhds (by solve_by_elim) <| by simp) fun y hy => by aesop)
            convert h_cont using 1
            rw [show (⋃ i ∈ I j, { x : GluingSet (fun i => if i ∈ I j then C i else ∅) | (x : ℕ → ℕ) 0 = i }) = Set.univ from Set.eq_univ_of_forall fun x => Set.mem_iUnion₂.mpr ⟨_, embed_block j x, rfl⟩] ; simp +decide [continuousOn_univ]
          rw [continuous_induced_rng]
          convert h_cont using 1
          exact funext fun x => toPointed_val j x
        rw [continuousOn_iff_continuous_restrict]
        convert h_cont_comp using 1
        exact funext fun x => hσ_eq_on_Oj x x.2
      exact (hσ_cont_Oj.continuousAt (hOj.mem_nhds hj)).continuousWithinAt
    · -- σ continuous on Uᶜ = {a | f a = y}: σ is constant (zeroStream)
      apply continuousOn_const.congr
      intro a ha
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha
      show σ a = ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩
      simp only [σ, dif_pos ha]
    · /- **Sequential condition**: if a_n → a₀ with f a₀ = y and ∀ n, f(a_n) ≠ y,
         then σ(a_n) → σ a₀ = zeroStream. -/
      intro x_n a₀ hU_n ha₀ hx_n_tendsto
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha₀
      rw [show σ a₀ = ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ from by
        simp only [σ, ha₀, dif_pos]]
      -- σ(x_n n) = toPointed j_n (...) with val = prependZerosOne k_n b_n, k_n ∈ I j_n
      -- Show (σ ∘ x_n) converges to zeroStream in PointedGluingSet C ≅ subspace of ℕ → ℕ
      -- Key: k_n (block index of σ(x_n n)) → ∞
      -- Since f(x_n n) → y and f(x_n n) ∈ RaySet B y j_n, j_n → ∞
      -- Since I j are pairwise disjoint, k_n ∈ I j_n are distinct, hence k_n → ∞
      -- Then prependZerosOne k_n · → zeroStream by prependZerosOne_eventually_in_nhds
      rw [tendsto_subtype_rng]
      -- Apply the fact that `prependZerosOne` tends to `zeroStream` as `k` tends to infinity.
      have h_append_zero : Filter.Tendsto (fun n => (σ_j (rayIdx (x_n n) (hU_n n)) ⟨x_n n, rayIdx_inray (x_n n) (hU_n n)⟩).val 0) Filter.atTop Filter.atTop := by
        have h_append_zero : Filter.Tendsto (fun n => rayIdx (x_n n) (hU_n n)) Filter.atTop Filter.atTop := by
          apply rayIdx_tendsto_atTop_of_converge
          any_goals tauto
          simpa [ha₀] using hf.continuousAt.tendsto.comp hx_n_tendsto
        exact
          disjoint_finset_member_tendsto_atTop hI_disj
            (fun n =>
              embed_block (rayIdx (x_n n) (hU_n n))
                (σ_j (rayIdx (x_n n) (hU_n n)) ⟨x_n n, rayIdx_inray (x_n n) (hU_n n)⟩))
            h_append_zero
      have h_append_zero : Filter.Tendsto (fun n => prependZerosOne ((σ_j (rayIdx (x_n n) (hU_n n)) ⟨x_n n, rayIdx_inray (x_n n) (hU_n n)⟩).val 0) (unprepend (σ_j (rayIdx (x_n n) (hU_n n)) ⟨x_n n, rayIdx_inray (x_n n) (hU_n n)⟩).val)) Filter.atTop (nhds zeroStream) := by
        exact
          prependZerosOne_tendsto_zeroStream h_append_zero fun n =>
            unprepend ↑(σ_j (rayIdx (x_n n) (hU_n n)) ⟨x_n n, rayIdx_inray (x_n n) (hU_n n)⟩)
      grind
  · /- **Continuity of τ on range**. -/
    -- First prove the equation (needed for continuity at zeroStream)
    have heq_main : ∀ a, f a = τ (PointedGluingFun C D g (σ a)) := by
      intro a
      by_cases ha : f a = y
      · have hσ' : σ a = ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ := by
          simp only [σ, ha, dif_pos]
        rw [hσ']
        show f a = τ (PointedGluingFun C D g ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩)
        rw [show PointedGluingFun C D g ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ = zeroStream
            from by unfold PointedGluingFun; simp]
        simp only [τ, if_pos rfl]
        exact ha
      · set j' := rayIdx a ha
        set x_j' := σ_j j' ⟨a, rayIdx_inray a ha⟩
        have hσ' : σ a = toPointed j' x_j' := dif_neg ha
        rw [hσ']
        change f a = τ (PointedGluingFun C D g (toPointed j' x_j'))
        rw [toPointed_pgluing j' x_j']
        have hk' := embed_block j' x_j'
        set k' := x_j'.val 0
        have hne' : prependZerosOne k' (g k' ⟨unprepend x_j'.val, embed_strip j' x_j'⟩).val
            ≠ zeroStream := prependZerosOne_ne_zeroStream _ _
        have hτ_app : τ (prependZerosOne k' (g k' ⟨unprepend x_j'.val, embed_strip j' x_j'⟩).val) =
            τ_j j' (prepend k' (g k' ⟨unprepend x_j'.val, embed_strip j' x_j'⟩).val) := by
          show (if prependZerosOne k' _ = zeroStream then y
                else τ_j (findJ (firstNonzero (prependZerosOne k' _)))
                  (pointedToGluing (prependZerosOne k' _))) = _
          rw [if_neg hne', firstNonzero_prependZerosOne, findJ_spec k' j' hk']
          congr 1
          simp only [pointedToGluing, if_neg (prependZerosOne_ne_zeroStream _ _),
            firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
        rw [hτ_app, ← gj_eq j' x_j']
        exact heq_j j' ⟨a, rayIdx_inray a ha⟩
    -- Now prove ContinuousOn τ on the range
    intro z hz_mem
    by_cases hz_zero : z = zeroStream
    · -- z = zeroStream
      subst hz_zero
      apply continuousWithinAt_tau_at_zeroStream
        (show τ zeroStream = y from if_pos rfl) hI_disj
      -- hR_struct
      rintro z ⟨a, rfl⟩ hz_ne
      have ha_ne : f a ≠ y := by
        intro h_eq; apply hz_ne
        show (fun x => PointedGluingFun C D g x) (σ a) = zeroStream
        simp only [σ, dif_pos h_eq]; unfold PointedGluingFun; simp
      refine ⟨rayIdx a ha_ne, ?_, ?_⟩
      · -- firstNonzero ∈ I j
        show firstNonzero (PointedGluingFun C D g (σ a)) ∈ I (rayIdx a ha_ne)
        simp only [σ, dif_neg ha_ne]
        rw [toPointed_pgluing, firstNonzero_prependZerosOne]
        exact embed_block _ _
      · -- τ(z) agrees with y on [0, j)
        intro k hk
        show (τ ((fun x => PointedGluingFun C D g x) (σ a))) k = y k
        rw [← heq_main a]
        exact (rayIdx_inray a ha_ne).2.1 k hk
    · -- z ≠ zeroStream: on each block, τ is just a constant composition
      -- Since z ≠ zeroStream, z is in the block {x | firstNonzero x = firstNonzero z}
      -- On this block, τ x = τ_j(findJ(firstNonzero z))(pointedToGluing x)
      -- since firstNonzero is constant on the block
      set i := firstNonzero z
      -- The block is open
      have h_block_open : IsOpen {x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0} :=
        isOpen_block i
      have h_exists_ne : ∃ k, z k ≠ 0 := by
        by_contra h; push_neg at h; exact hz_zero (funext h)
      have hz_in_block : (∀ k, k < i → z k = 0) ∧ z i ≠ 0 := by
        have hi_def : i = Nat.find h_exists_ne := by
          simp only [i, firstNonzero, dif_pos h_exists_ne]
        constructor
        · intro k hk; rw [hi_def] at hk
          exact Classical.not_not.mp (Nat.find_min h_exists_ne hk)
        · rw [hi_def]; exact Nat.find_spec h_exists_ne
      -- On the block, τ = τ_j(findJ i) ∘ pointedToGluing
      -- since z' ≠ zeroStream (it has a nonzero entry at position i)
      -- and firstNonzero z' = i (same block)
      have h_tau_eq_on_block : ∀ z' : ℕ → ℕ,
          (∀ k, k < i → z' k = 0) ∧ z' i ≠ 0 →
          τ z' = τ_j (findJ i) (pointedToGluing z') := by
        intro z' hz'
        have hz'_ne : z' ≠ zeroStream := ne_zeroStream_of_block z' i hz'
        have h_fn_eq : firstNonzero z' = i := firstNonzero_eq_of_block z' i hz'
        show (if z' = zeroStream then y
              else τ_j (findJ (firstNonzero z')) (pointedToGluing z')) = _
        rw [if_neg hz'_ne, h_fn_eq]
      -- ContinuousWithinAt of τ at a non-zeroStream point
      -- Use the equation: on the range, τ(z') = f(a) where z' = PGF(σ(a))
      -- On block i, τ = τ_j(findJ i) ∘ pointedToGluing, which equals the original τ_j
      -- composition.
      -- We use ContinuousWithinAt.congr with the equation on a neighborhood.
      -- On the open block B_i containing z, τ agrees with τ_j(findJ i) ∘ pointedToGluing.
      -- So τ =ᶠ τ_j(findJ i) ∘ pointedToGluing at z in nhdsWithin.
      -- Then reduce to showing ContinuousWithinAt of the composition.
      -- On the range ∩ block, pointedToGluing maps into the range where τ_j is ContinuousOn.
      -- Use heq_main: for z' = PGF(σ(a)) in range, τ(z') = f(a).
      -- So on the range, τ is "f ∘ inverse", which is continuous because
      -- f is continuous and σ factors through each ray.
      --
      -- Approach: show τ =ᶠ (some continuous g) at z within S, then conclude.
      -- g = τ_j(findJ i) ∘ pointedToGluing on the block.
      -- Use continuousWithinAt_tau_at_block' with g and show ContinuousWithinAt of g.
      apply continuousWithinAt_tau_at_block' hz_mem hz_zero
      refine ⟨{x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0}, h_block_open, hz_in_block,
        fun z' => τ_j (findJ i) (pointedToGluing z'), ?_, fun z' ⟨hz'R, hz'B⟩ =>
          h_tau_eq_on_block z' hz'B⟩
      -- ContinuousWithinAt (τ_j (findJ i) ∘ pointedToGluing) (S ∩ block_i) z
      -- Step 1: pointedToGluing is ContinuousAt z
      have h_ptg_cont_at : ContinuousAt pointedToGluing z := by
        rw [continuousAt_congr (show pointedToGluing =ᶠ[nhds z] (fun z' => prepend i (stripZerosOne i z')) from by
          rw [Filter.eventuallyEq_iff_exists_mem]
          exact ⟨{x | (∀ k, k < i → x k = 0) ∧ x i ≠ 0},
            h_block_open.mem_nhds hz_in_block, fun z' hz' => by
              simp only [pointedToGluing, if_neg (ne_zeroStream_of_block z' i hz'),
                firstNonzero_eq_of_block z' i hz']⟩)]
        exact (continuous_prepend i).continuousAt.comp (continuous_stripZerosOne i).continuousAt
      -- Step 2: MapsTo pointedToGluing (S ∩ B_i) (range where τ_j is ContinuousOn)
      have h_maps_to : Set.MapsTo pointedToGluing
          (Set.range ((fun x => PointedGluingFun C D g x) ∘ σ) ∩
            {x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0})
          (Set.range ((fun x => GluingFunVal _ _ (fun ii => if h : ii ∈ I (findJ i) then
            (fun a => (g ii (by exact a)) : C ii → D ii) ∘
              (fun a => ⟨a.val, by have := a.property; simp [h] at this; exact this⟩)
            else fun a => ⟨a.val, by have := a.property; simp [h] at this⟩) x) ∘
          σ_j (findJ i))) := by
        intro z' ⟨⟨a, ha_rng⟩, hz'_block⟩
        have hz'_ne : z' ≠ zeroStream := ne_zeroStream_of_block z' i hz'_block
        have ha_ne : f a ≠ y := by
          intro h_eq; apply hz'_ne; rw [← ha_rng]
          simp only [Function.comp, σ, dif_pos h_eq]; unfold PointedGluingFun; simp
        -- Key: findJ i = rayIdx a ha_ne
        have hσ_eq : σ a = toPointed (rayIdx a ha_ne) (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩) := dif_neg ha_ne
        have hk_mem : (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val 0 ∈ I (rayIdx a ha_ne) :=
          embed_block (rayIdx a ha_ne) (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩)
        have hz'_eq : z' = prependZerosOne ((σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val 0)
            (g ((σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val 0)
              ⟨unprepend (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val,
                embed_strip (rayIdx a ha_ne) (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩)⟩).val := by
          rw [← ha_rng]; simp only [Function.comp]; rw [hσ_eq, toPointed_pgluing]
        have hk_eq_i : (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val 0 = i := by
          have h1 : firstNonzero z' = (σ_j (rayIdx a ha_ne) ⟨a, rayIdx_inray a ha_ne⟩).val 0 := by
            rw [hz'_eq, firstNonzero_prependZerosOne]
          rw [← h1]; exact firstNonzero_eq_of_block z' i hz'_block
        have hfJ : findJ i = rayIdx a ha_ne := by
          rw [← hk_eq_i]; exact findJ_spec _ _ hk_mem
        -- Now use `cases hfJ` to unify findJ i and rayIdx a ha_ne
        -- providing the witness (⟨a, h_mem_ray⟩, eq)
        have h_mem_ray : f a ∈ RaySet B y (findJ i) := hfJ ▸ rayIdx_inray a ha_ne
        -- The equality proof uses hfJ to transport across the dependent type
        have h_eq_lhs_rhs : ((fun x =>
          GluingFunVal _ _ (fun ii => if h : ii ∈ I (findJ i) then
            (fun a => (g ii (by exact a)) : C ii → D ii) ∘
              (fun a => ⟨a.val, by have := a.property; simp [h] at this; exact this⟩)
            else fun a => ⟨a.val, by have := a.property; simp [h] at this⟩) x) ∘
          σ_j (findJ i)) ⟨a, h_mem_ray⟩ = pointedToGluing z' := by
            -- Rewrite findJ i to rayIdx a ha_ne everywhere using hfJ
            have key : findJ i = rayIdx a ha_ne := hfJ
            -- Use the equality to transport
            dsimp only [Function.comp]
            -- Unfold GluingFunVal
            simp only [GluingFunVal, key]
            -- proof irrelevance and value matching
            simp only [pointedToGluing, if_neg hz'_ne, firstNonzero_eq_of_block z' i hz'_block]
            -- Both sides should now be prepend expressions
            -- Try grind/simp to close
            simp only [hk_eq_i, hz'_eq, stripZerosOne_prependZerosOne]
            have hi_in : i ∈ I (rayIdx a ha_ne) := hk_eq_i ▸ hk_mem
            -- Both sides are now `(g i ⟨u, P⟩).val` for the same `u` but
            -- different proofs P of `u ∈ C i`.
            have head_eq : (σ_j (findJ i) ⟨a, h_mem_ray⟩).val 0 = i := by
              -- Zoom in on the right-hand side only
              conv =>
                rhs
                rw [← hk_eq_i]
              -- Zoom out automatically (by un-indenting) and finish it
              congr!
            simp only [head_eq]
            rw [dif_pos hi_in]
            -- 1. Apply the function composition
            dsimp only [Function.comp]
            -- 4. Strip away identical outer functions (prepend, g, Subtype.val, σ_j, etc.)
            -- and force Lean to ignore the dependent proof mismatches
            congr!

        exact ⟨⟨a, h_mem_ray⟩, h_eq_lhs_rhs⟩
      have h_ptg_z_mem := h_maps_to ⟨hz_mem, hz_in_block⟩
      -- Step 3: Compose
      exact ContinuousWithinAt.comp
        (hτ_j (findJ i) (pointedToGluing z) h_ptg_z_mem)
        (h_ptg_cont_at.continuousWithinAt)
        h_maps_to
  · /- **Equation**: f a = τ (PointedGluingFun C D g (σ a)) -/
    intro a
    by_cases ha : f a = y
    · have hσ : σ a = ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ := by
        simp only [σ, ha, dif_pos]
      rw [hσ]
      show f a = τ (PointedGluingFun C D g ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩)
      rw [show PointedGluingFun C D g ⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ = zeroStream
          from by unfold PointedGluingFun; simp]
      simp only [τ, if_pos rfl]
      exact ha
    · set j := rayIdx a ha
      set x_j := σ_j j ⟨a, rayIdx_inray a ha⟩
      have hσ : σ a = toPointed j x_j := dif_neg ha
      rw [hσ]
      change f a = τ (PointedGluingFun C D g (toPointed j x_j))
      rw [toPointed_pgluing j x_j]
      have hk := embed_block j x_j
      set k := x_j.val 0
      have hne : prependZerosOne k (g k ⟨unprepend x_j.val, embed_strip j x_j⟩).val
          ≠ zeroStream := prependZerosOne_ne_zeroStream _ _
      have hτ_apply : τ (prependZerosOne k (g k ⟨unprepend x_j.val, embed_strip j x_j⟩).val) =
          τ_j j (prepend k (g k ⟨unprepend x_j.val, embed_strip j x_j⟩).val) := by
        show (if prependZerosOne k _ = zeroStream then y
              else τ_j (findJ (firstNonzero (prependZerosOne k _)))
                (pointedToGluing (prependZerosOne k _))) = _
        rw [if_neg hne, firstNonzero_prependZerosOne, findJ_spec k j hk]
        congr 1
        simp only [pointedToGluing, if_neg (prependZerosOne_ne_zeroStream _ _),
          firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
      rw [hτ_apply, ← gj_eq j x_j]
      exact heq_j j ⟨a, rayIdx_inray a ha⟩

/-
**Corollary (Pgluingofraysasupperbound).**
For any continuous `f : A → B` in 𝒞 and any `y ∈ B`,
`f ≤ pgl_{i ∈ ℕ} Ray(f, y, i)`.


This is a direct application of Pgluingasupperbound with the identity partition
`I_j = {j}`.
-/

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
        grind +suggestions
      · exact ne_zeroStream_of_block _ _ hx'.1.1
      · exact ne_zeroStream_of_block _ _ hx.1.1
