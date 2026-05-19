import RequestProject.PointedGluing.MaxFun.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

variable
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    {f : A → B}
    {C D : ℕ → Set (ℕ → ℕ)}
    {g : ∀ n, C n → D n}
    {x : A}
    {An : ℕ → Set A}

/-!
## Helper: the equation part of pointedGluing_lower_bound_lemma
-/

/-
Given extracted data from the reductions, the equation
    PointedGluingFun C D g z = τ (f (σ z)) holds for all z.
-/
omit [TopologicalSpace A] [MetrizableSpace A] [MetrizableSpace B] in
lemma pgl_lower_bound_equation
    (σ_n : ∀ n, C n → An n) (τ_n : ∀ _n, B → ℕ → ℕ)
    (hτ_n_eq : ∀ n (z : C n), (g n z : ℕ → ℕ) = τ_n n (f (σ_n n z).val))
    (hsep : ∀ n, f x ∉ closure (f '' (An n)))
    (hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n))) :
    let σ : PointedGluingSet C → A := fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val
    let τ : B → ℕ → ℕ := fun y =>
      if h : ∃ n, y ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) then
        prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y)
      else zeroStream
    ∀ z : PointedGluingSet C, PointedGluingFun C D g z = τ (f (σ z)) := by
  intro σ τ z
  by_cases h : z.val = zeroStream
  · simp +decide [σ, τ, PointedGluingFun, h]
    intro n y hy hxy
    contrapose! hsep
    exact ⟨n, subset_closure ⟨_, σ_n n ⟨y, hy⟩ |>.2, hxy⟩⟩
  · rw [pointedGluingFun_eq_on_block C D g z h]
    simp +zetaDelta at *
    split_ifs ; simp_all +decide [Set.disjoint_left]
    · grind
    · exact False.elim (‹¬∃ n a, ∃ (h_1 : a ∈ C n), f ↑ (σ_n n ⟨a, h_1⟩) = f ↑ (σ_n (firstNonzero z.val) ⟨stripZerosOne (firstNonzero z.val) z.val, strip_mem_of_pointedGluingSet C z h⟩) › ⟨_, _, _, rfl⟩)

/-
The sequential part of the continuity of σ:
    if z_k → zeroStream with z_k.val ≠ zeroStream, then σ(z_k) → x.
-/
omit [MetrizableSpace A] in
lemma pgl_lower_bound_sigma_seq
    (σ_n : ∀ n, C n → An n)
    (hconv : SetsConvergeTo An x) :
    let σ : PointedGluingSet C → A := fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val
    ∀ (z_k : ℕ → PointedGluingSet C) (z₀ : PointedGluingSet C),
      (∀ n, (z_k n).val ≠ zeroStream) →
      z₀.val = zeroStream →
      Filter.Tendsto z_k Filter.atTop (nhds z₀) →
      Filter.Tendsto (σ ∘ z_k) Filter.atTop (nhds (σ z₀)) := by
  intro σ z_k z₀ hz_k hz₀ hz_tendsto
  have h_firstNonzero : Filter.Tendsto (fun n => firstNonzero (z_k n).val) Filter.atTop Filter.atTop := by
    apply firstNonzero_tendsto_of_converge_zeroStream
    · exact hz_k
    · simpa only [hz₀] using tendsto_subtype_rng.mp hz_tendsto
  rw [tendsto_nhds] at *
  intro s hs hx
  obtain ⟨m, hm⟩ := hconv s hs (show x ∈ s from by aesop)
  filter_upwards [h_firstNonzero.eventually_ge_atTop m] with n hn using by aesop

/-
On a specific block, σ agrees with a known-continuous function.
    For y in the block {y | (∀ k < n, y.val k = 0) ∧ y.val n ≠ 0},
    σ y = (σ_n n ⟨stripZerosOne n y.val, ...⟩).val.
-/
omit [TopologicalSpace A] [MetrizableSpace A] in
lemma pgl_sigma_eq_on_block
    (σ_n : ∀ n, C n → An n) (n : ℕ)
    (y : PointedGluingSet C)
    (hy : (∀ k, k < n → y.val k = 0) ∧ y.val n ≠ 0) :
    (fun z : PointedGluingSet C =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val) y =
    (σ_n n ⟨stripZerosOne n y.val, strip_mem_of_block C y n hy⟩).val := by
  -- Since y is not zeroStream, the if condition is false, so we can simplify the expression.
  have h_if_false : ¬(y.val = zeroStream) := by
    exact fun h => hy.2 (h.symm ▸ rfl)
  -- Since firstNonzero y.val = n, we can substitute this into the expression.
  have h_firstNonzero : firstNonzero y.val = n := by
    exact firstNonzero_eq_of_block _ _ hy
  grind

omit [MetrizableSpace A] in
/-- ContinuousOn σ on the set {z | z.val ≠ zeroStream}. -/
lemma pgl_lower_bound_sigma_cont_on_U
    (σ_n : ∀ n, C n → An n)
    (hσ_n : ∀ n, Continuous (σ_n n)) :
    let σ : PointedGluingSet C → A := fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val
    ContinuousOn σ {z : PointedGluingSet C | z.val ≠ zeroStream} := by
  intro σ z hz
  simp only [Set.mem_setOf_eq] at hz
  set n := firstNonzero z.val with hn_def
  -- z has block property
  have hex : ∃ k, z.val k ≠ 0 := not_forall.mp fun h => hz (funext h)
  have hfn_eq : firstNonzero z.val = Nat.find hex := by
    unfold firstNonzero; rw [dif_pos hex]
  have h_block : (∀ k, k < n → z.val k = 0) ∧ z.val n ≠ 0 := by
    constructor
    · intro k hk; by_contra hk'
      exact Nat.find_min hex (hfn_eq ▸ hk) hk'
    · rw [show n = Nat.find hex from hfn_eq]; exact Nat.find_spec hex
  -- Open block V containing z
  set V := {y : PointedGluingSet C | (∀ k, k < n → y.val k = 0) ∧ y.val n ≠ 0}
  have hV_open : IsOpen V := (isOpen_block n).preimage continuous_subtype_val
  have hz_V : z ∈ V := h_block
  -- On V, σ = continuous function
  have h_cont_fn : Continuous (fun y : V =>
      (σ_n n ⟨stripZerosOne n y.val.val, strip_mem_of_block C y.val n y.prop⟩).val) :=
    continuous_subtype_val.comp ((hσ_n n).comp
      (Continuous.subtype_mk
        ((continuous_stripZerosOne n).comp
          (continuous_subtype_val.comp continuous_subtype_val))
        _))
  have h_agree : ∀ y : V, σ y.val = (σ_n n ⟨stripZerosOne n y.val.val, strip_mem_of_block C y.val n y.prop⟩).val :=
    fun y => pgl_sigma_eq_on_block σ_n n y.val y.prop
  have hcont_V : ContinuousOn σ V := by
    rw [continuousOn_iff_continuous_restrict]
    exact h_cont_fn.congr (fun y => (h_agree y).symm)
  exact (hcont_V.continuousAt (hV_open.mem_nhds hz_V)).continuousWithinAt

/-
ContinuousOn τ on range(f ∘ σ).
-/
set_option maxHeartbeats 8000000 in
omit [TopologicalSpace A] [MetrizableSpace A] [MetrizableSpace B] in
lemma pgl_lower_bound_tau_cont
    (σ_n : ∀ n, C n → An n) (τ_n : ∀ _n, B → ℕ → ℕ)
    (hτ_n : ∀ n, ContinuousOn (τ_n n) (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n)))
    (hsep : ∀ n, f x ∉ closure (f '' (An n)))
    (hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n)))
    (hpart_open : ∀ n, IsOpen (f '' (An n) : Set B)) :
    let σ : PointedGluingSet C → A := fun z =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val
    let τ : B → ℕ → ℕ := fun y =>
      if h : ∃ n, y ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) then
        prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y)
      else zeroStream
    ContinuousOn τ (Set.range (f ∘ σ)) := by
  refine fun y hy => ?_
  by_cases hyx : y = f x
  · rw [ContinuousWithinAt]
    simp +decide [hyx, tendsto_pi_nhds]
    intro k
    have h_neighborhood : ∀ᶠ y in 𝓝[range (f ∘ (fun z => if h : z.val = zeroStream then x else (σ_n (firstNonzero z.val) ⟨stripZerosOne (firstNonzero z.val) z.val, strip_mem_of_pointedGluingSet C z h⟩).val))] f x, ∀ n, n ≤ k → y ∉ f '' An n := by
      have h_neighborhood : ∀ n ≤ k, ∀ᶠ y in 𝓝[range (f ∘ (fun z => if h : z.val = zeroStream then x else (σ_n (firstNonzero z.val) ⟨stripZerosOne (firstNonzero z.val) z.val, strip_mem_of_pointedGluingSet C z h⟩).val))] f x, y ∉ f '' An n := by
        intro n hn
        exact Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (isOpen_compl_iff.mpr (isClosed_closure)) (hsep n))) fun y hy => fun hy' => hy <| subset_closure hy'
      rw [eventually_nhdsWithin_iff] at *
      rw [eventually_nhds_iff] at *
      choose! t ht using fun n hn => mem_nhdsWithin.mp (h_neighborhood n hn)
      use ⋂ n ≤ k, t n
      simp_all +decide [Set.subset_def]
      exact ⟨fun y hy x hx hx' n hn x' hx'' => ht n hn |>.2.2 y (hy n hn) x hx hx' x' hx'', by rw [show (⋂ n, ⋂ (_ : n ≤ k), t n) = ⋂ n ∈ Finset.Iic k, t n by ext; simp +decide] ; exact isOpen_biInter_finset fun n hn => ht n (Finset.mem_Iic.mp hn) |>.1⟩
    filter_upwards [h_neighborhood] with y hy
    split_ifs <;> simp_all +decide
    · rename_i h₁ h₂ h₃
      obtain ⟨m, a, b, hm⟩ := h₂
      exact False.elim (hsep m (subset_closure ⟨_, (σ_n m ⟨a, b⟩) |>.2, hm⟩))
    · rename_i h₁ h₂ h₃
      exact prependZerosOne_head_eq_zero _ _ _ (lt_of_not_ge fun h => hy _ h _ (σ_n _ _ |>.2) (Classical.choose_spec h₁ |>.choose_spec.2))
    · have := Classical.choose_spec ‹∃ n a, ∃ b : a ∈ C n, f ↑ (σ_n n ⟨a, b⟩) = f x›
      contrapose! hsep
      exact ⟨_, subset_closure ⟨_, this.choose_spec.choose_spec |> fun h => Subtype.mem _, this.choose_spec.choose_spec⟩⟩
  · -- Since y is in the range of f ∘ σ and y ≠ f x, there exists an n such that y ∈ range(f ∘ val ∘ σ_n n).
    obtain ⟨n, hn⟩ : ∃ n, y ∈ Set.range ((f ∘ Subtype.val) ∘ σ_n n) := by
      grind
    have hτ_eq : ∀ᶠ y' in nhdsWithin y (Set.range ((f ∘ Subtype.val) ∘ σ_n n)), (fun y => if h : ∃ n, y ∈ Set.range ((f ∘ Subtype.val) ∘ σ_n n) then prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y) else zeroStream) y' = prependZerosOne n (τ_n n y') := by
      filter_upwards [self_mem_nhdsWithin] with y' hy'
      split_ifs with h
      · have := hpart (Classical.choose h) n; simp_all +decide [Set.disjoint_left]
        grind +revert
      · exact False.elim (h ⟨n, hy'⟩)
    have hτ_cont : ContinuousWithinAt (fun y => prependZerosOne n (τ_n n y)) (Set.range ((f ∘ Subtype.val) ∘ σ_n n)) y := by
      exact ContinuousWithinAt.comp (continuous_prependZerosOne n |> Continuous.continuousWithinAt) (hτ_n n y hn) (Set.mapsTo_univ _ _)
    have hτ_cont : ContinuousWithinAt (fun y => if h : ∃ n, y ∈ Set.range ((f ∘ Subtype.val) ∘ σ_n n) then prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y) else zeroStream) (Set.range ((f ∘ Subtype.val) ∘ σ_n n)) y := by
      rw [ContinuousWithinAt] at *
      rw [Filter.tendsto_congr' hτ_eq]
      convert hτ_cont using 2
      exact hτ_eq.self_of_nhdsWithin hn
    refine hτ_cont.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨f '' An n, ?_, ?_⟩
    · exact IsOpen.mem_nhds (hpart_open n) (by obtain ⟨z, rfl⟩ := hn; exact Set.mem_image_of_mem _ (σ_n n z |>.2))
    · rintro _ ⟨⟨a, ha, rfl⟩, ⟨z, hz⟩⟩
      by_cases h : z.val = zeroStream <;> simp +decide [h] at hz ⊢
      · exact False.elim (hsep n <| subset_closure <| Set.mem_image_of_mem _ ha |> fun h => hz ▸ h)
      · have := hpart (firstNonzero z.val) n; simp_all +decide [Set.disjoint_left]
        grind

end
