
import WqoContinuousFunctions.PointedGluing.Defs
import WqoContinuousFunctions.BaireSpace.GenRedProp
import WqoContinuousFunctions.PointedGluing.LowerBoundLemma
import WqoContinuousFunctions.PrelimMemo.Scattered.Decomposition


import WqoContinuousFunctions.PointedGluing.MinFun.Helpers
import WqoContinuousFunctions.PointedGluing.MinFun.LowerBound
import WqoContinuousFunctions.PointedGluing.MinFun.LocalHelpers


open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
## Section 6: Pointed Gluing as a Lower Bound (Proposition 3.11)
Lemma and helpers for the main lower bound result are in
`LowerBoundLemma.lean`. This file contains the main theorem and some auxiliary lemmas.
-/

/--
MinFun 0 reduces to any function with nonempty domain.
-/
lemma minFun_zero_reduces {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) -- (hf : Continuous f)
    (hne : A.Nonempty) :
    ContinuouslyReduces (MinFun 0) f := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun _ => ⟨x, hx⟩, ?_, ?_⟩
  · exact continuous_const
  · refine ⟨fun _ => zeroStream, ?_, ?_⟩ <;> norm_num [MinFun]
    · exact continuousOn_const
    · simp +decide [MinDom]
      simp +decide [PointedGluingSet]

theorem pointedGluing_lower_bound
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ i, C i → D i)
    (x : A)
    (hloc : ∀ (i : ℕ) (U : Set A), IsOpen U → x ∈ U →
      ∃ (σ : C i → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
        Continuous σ ∧
        (∀ z, (g i z : ℕ → ℕ) = τ (f (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        f x ∉ closure (Set.range (fun z => f (σ z)))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  -- Cylinder neighborhoods of x in A
  let cyl : ℕ → Set A := fun n => nbhd' A x n
  -- Cylinder neighborhoods of f x in ℕ→ℕ
  let cylfx : ℕ → Set (ℕ → ℕ) := fun n => nbhd (f x) n
  -- Basic facts about cylinders
  have hcyl_clopen : ∀ n, IsClopen (cyl n) := fun n =>
    baire_nbhd'_isClopen A x n
  have hcyl_open : ∀ n, IsOpen (cyl n) := fun n =>
    (hcyl_clopen n).isOpen
  have hx_cyl : ∀ n, x ∈ cyl n := fun n => by
    simp [cyl, nbhd']
  have hcylfx_clopen : ∀ n, IsClopen (cylfx n) := fun n =>
    baire_nbhd_isClopen (f x) n
  have hcylfx_open : ∀ n, IsOpen (cylfx n) := fun n =>
    (hcylfx_clopen n).isOpen
  have hfx_cylfx : ∀ n, f x ∈ cylfx n := fun n => by
    simp [cylfx, nbhd]
  -- Neighborhood basis at x in A
  have hbasis_x : ∀ U : Set A, IsOpen U → x ∈ U → ∃ n, cyl n ⊆ U :=
    nbhd_basis' A x
  -- Neighborhood basis at f x in ℕ→ℕ
  have hbasis_fx : ∀ U : Set (ℕ → ℕ), IsOpen U → f x ∈ U → ∃ n, cylfx n ⊆ U :=
    nbhd_basis (f x)
  -- Helper: find m such that closure S ∩ cylfx m = ∅, given f x ∉ closure S
  have find_m : ∀ S : Set (ℕ → ℕ), f x ∉ closure S →
      ∃ m, closure S ∩ cylfx m = ∅ := by
    intro S hclos
    have hopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
    have hfx_mem : f x ∈ (closure S)ᶜ := hclos
    obtain ⟨m, hm⟩ := hbasis_fx _ hopen hfx_mem
    exact ⟨m, by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy_clos hy_cyl
      exact hm hy_cyl hy_clos⟩
  -- Helper: find l such that f '' cyl l ⊆ cylfx m
  have find_l : ∀ m : ℕ, ∃ l, ∀ a ∈ cyl l, f a ∈ cylfx m := by
    intro m
    have hpre : IsOpen (f ⁻¹' cylfx m) := (hcylfx_open m).preimage hf
    have hx_pre : x ∈ f ⁻¹' cylfx m := hfx_cylfx m
    obtain ⟨l, hl⟩ := hbasis_x _ hpre hx_pre
    exact ⟨l, fun a ha => hl ha⟩
  -- ----------------------------------------------------------------
  -- Build the sequence (σ n, τ n) with data (k n, l n, m n)
  -- Using explicit recursion via Nat.rec to preserve the cross-step
  -- invariant kseq (n+1) = lseq n.
  -- ----------------------------------------------------------------
  have cyl_antitone : ∀ m n : ℕ, m ≤ n → cyl n ⊆ cyl m := by
    intro m n hmn a ha i hi
    exact ha i (Finset.range_mono hmn hi)
  -- Step function: given n and prevl (= kseq n), produce (l, m, σ, τ)
  -- with l ≥ prevl + 1, σ mapping into cyl prevl, etc.
  have mkStep : ∀ (n : ℕ) (prevl : ℕ), ∃ (l m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      l ≥ prevl + 1 ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl prevl) ∧
      closure (Set.range (fun z => f (σ z))) ∩ cylfx m = ∅ ∧
      (∀ a ∈ cyl l, f a ∈ cylfx m) := by
    intro n prevl
    obtain ⟨σ, τ, hσc, hcomm, hτc, hσU, hclos⟩ :=
      hloc n (cyl prevl) (hcyl_open prevl) (hx_cyl prevl)
    obtain ⟨m, hm⟩ := find_m _ hclos
    obtain ⟨l₀, hl₀⟩ := find_l m
    exact ⟨max l₀ (prevl + 1), m, σ, τ, le_max_right _ _, hσc, hcomm, hτc, hσU, hm,
      fun a ha => hl₀ a (fun i hi => ha i (Finset.range_mono (le_max_left _ _) hi))⟩
  -- Build kseq (= prevl values) by explicit Nat.rec:
  --   kseq 0 = 0
  --   kseq (n+1) = l from step n = (mkStep n (kseq n)).choose
  let kseq : ℕ → ℕ := Nat.rec 0 (fun n prev => (mkStep n prev).choose)
  -- lseq n = kseq (n+1) = the l output from step n
  let lseq : ℕ → ℕ := fun n => kseq (n + 1)
  -- Extract step data via choose from mkStep n (kseq n)
  -- Note: lseq n = kseq (n+1) = (mkStep n (kseq n)).choose by definition
  have stepSpec : ∀ n, ∃ (m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      lseq n ≥ kseq n + 1 ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl (kseq n)) ∧
      closure (Set.range (fun z => f (σ z))) ∩ cylfx m = ∅ ∧
      (∀ a ∈ cyl (lseq n), f a ∈ cylfx m) := by
    intro n
    exact (mkStep n (kseq n)).choose_spec
  choose mseq σseq τseq hstep using stepSpec
  -- Unpack properties
  have hl    : ∀ n, lseq n ≥ kseq n + 1         := fun n => (hstep n).1
  have hσc   : ∀ n, Continuous (σseq n)          := fun n => (hstep n).2.1
  have hcomm : ∀ n z, (g n z : ℕ → ℕ) = τseq n (f (σseq n z)) :=
                                                     fun n => (hstep n).2.2.1
  have hτc   : ∀ n, ContinuousOn (τseq n)
      (Set.range (fun z => f (σseq n z)))         := fun n => (hstep n).2.2.2.1
  have hσcyl : ∀ n z, σseq n z ∈ cyl (kseq n)   := fun n => (hstep n).2.2.2.2.1
  have hclos : ∀ n, closure (Set.range (fun z => f (σseq n z))) ∩
      cylfx (mseq n) = ∅                         := fun n => (hstep n).2.2.2.2.2.1
  have hfl   : ∀ n a, a ∈ cyl (lseq n) → f a ∈ cylfx (mseq n) :=
                                                     fun n => (hstep n).2.2.2.2.2.2
  -- Key monotonicity: kseq is strictly increasing
  have kseq_strictMono : StrictMono kseq := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl) (hl n)
  -- kseq n ≥ n
  have hk : ∀ n, kseq n ≥ n := by
    intro n; induction n with
    | zero => simp [kseq]
    | succ n ih =>
      -- kseq (n+1) = lseq n ≥ kseq n + 1 ≥ n + 1
      show lseq n ≥ n + 1
      calc lseq n ≥ kseq n + 1 := hl n
        _ ≥ n + 1 := Nat.add_le_add_right ih 1
  -- ----------------------------------------------------------------
  -- The threading lemma: f(σseq q z) ∈ cylfx (mseq p) for all q > p
  -- ----------------------------------------------------------------
  have threading : ∀ p q : ℕ, p < q → ∀ z, f (σseq q z) ∈ cylfx (mseq p) := by
    intro p q hpq z
    apply hfl p
    apply cyl_antitone (lseq p) (kseq q)
    · -- lseq p = kseq (p+1) ≤ kseq q since kseq is strictly mono and p+1 ≤ q
      exact kseq_strictMono.monotone hpq
    · exact hσcyl q z
  -- ----------------------------------------------------------------
  -- Define An and apply pointedGluing_lower_bound_lemma
  -- ----------------------------------------------------------------
  let An : ℕ → Set A := fun n => Set.range (σseq n)
  let σ_n : ∀ n, C n → An n := fun n z => ⟨σseq n z, Set.mem_range_self z⟩
  apply pointedGluing_lower_bound_lemma f hf C D g x An
  · -- hsep: ∀ n, f x ∉ closure (f '' An n)
    intro n
    -- f '' An n = range (f ∘ σseq n)
    -- hclos n says closure(range(f ∘ σseq n)) ∩ cylfx (mseq n) = ∅
    -- hfx_cylfx says f x ∈ cylfx (mseq n)
    -- So f x ∉ closure(range(f ∘ σseq n)) = closure(f '' An n)
    -- Since $f x \in \text{cylfx } (mseq n)$ and $\text{closure } (\text{range } (f \circ \sigmaseq n)) \cap \text{cylfx } (mseq n) = \emptyset$, it follows that $f x \notin \text{closure } (\text{range } (f \circ \sigmaseq n))$.
    have h_not_in_closure : f x ∉ closure (range (fun z => f (σseq n z))) := by
      exact fun h => Set.notMem_empty _ <| hclos n ▸ Set.mem_inter h (hfx_cylfx _)
    convert h_not_in_closure using 1
    simp +decide [An, Set.image]
    congr! 2
    exact Set.ext fun x => ⟨by rintro ⟨a, ha, ⟨b, hb, hab⟩, rfl⟩ ; exact ⟨⟨b, hb⟩, by simp [hab]⟩, by rintro ⟨⟨a, ha⟩, rfl⟩ ; exact ⟨_, _, ⟨a, ha, rfl⟩, rfl⟩⟩
  · -- hrelclop: IsRelativeClopenPartition (fun m => f '' An m)
    constructor
    · intro i j hij
      -- Since $i \neq j$, without loss of generality, assume $i < j$.
      wlog hij : i < j generalizing i j
      · exact Disjoint.symm (this _ _ (Ne.symm ‹_›) (lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm ‹_›)))
      · have h_disjoint : f '' An j ⊆ cylfx (mseq i) := by
          exact Set.image_subset_iff.mpr fun z hz => by obtain ⟨w, rfl⟩ := hz; exact threading i j hij w
        have h_disjoint : f '' An i ⊆ closure (range (fun z => f (σseq i z))) := by
          exact Set.image_subset_iff.mpr fun x hx => subset_closure <| by obtain ⟨z, rfl⟩ := hx; exact Set.mem_range_self z
        exact Set.disjoint_left.mpr fun x hx₁ hx₂ => Set.notMem_empty x <| hclos i ▸ Set.mem_inter (h_disjoint hx₁) (‹f '' An j ⊆ cylfx (mseq i) › hx₂)
    · intro n
      -- Let's define the clopen set C_n.
      set C_n := (cylfx (mseq n))ᶜ ∩ ⋂ m ∈ Finset.range n, cylfx (mseq m)
      -- By definition of $C_n$, we know that $f '' An n \subseteq C_n$.
      have h_subset : ∀ z ∈ An n, f z ∈ C_n := by
        rintro _ ⟨z, rfl⟩
        refine ⟨?_, ?_⟩
        · exact fun h => hclos n |> fun h' => h' |> fun h'' => h'' |> fun h''' => h''' |> fun h'''' => h'''' |> fun h''''' => h''''' |> fun h'''''' => h'''''' |> fun h''''''' => h''''''' |> fun h'''''''' => by
            exact h'''''''' |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => by
              have := h
              exact this.subset ⟨subset_closure ⟨z, rfl⟩, by assumption⟩
        · exact Set.mem_iInter₂.mpr fun m hm => threading m n (Finset.mem_range.mp hm) z
      -- By definition of $C_n$, we know that $f '' An j \cap C_n = \emptyset$ for $j \neq n$.
      have h_disjoint : ∀ j, j ≠ n → ∀ z ∈ An j, f z ∉ C_n := by
        intros j hj z hz hC_n
        by_cases h_cases : j < n
        · obtain ⟨w, rfl⟩ := hz
          exact hclos j |> fun h => h.subset ⟨subset_closure <| Set.mem_range_self w, hC_n.2 |> Set.mem_iInter₂.mp |> fun h => h j (Finset.mem_range.mpr h_cases)⟩
        · grind
      -- Since $C_n$ is clopen, the preimage of $C_n$ under the inclusion map is open.
      have h_preimage_open : IsOpen (Subtype.val ⁻¹' C_n : Set (⋃ j, f '' An j)) := by
        refine IsOpen.preimage ?_ ?_
        · exact continuous_subtype_val
        · exact IsOpen.inter (isOpen_compl_iff.mpr (hcylfx_clopen _ |>.1)) (isOpen_biInter_finset fun _ _ => hcylfx_open _)
      convert h_preimage_open using 1
      ext ⟨z, hz⟩; simp
      constructor
      · rintro ⟨a, ha, ha', rfl⟩ ; exact h_subset _ ha'
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
        grind
  · -- hconv: SetsConvergeTo An x
    intro U hU hxU
    obtain ⟨m₀, hm₀⟩ := hbasis_x U hU hxU
    exact ⟨m₀, fun n hn a ha => by
      obtain ⟨z, rfl⟩ := ha
      exact hm₀ (cyl_antitone m₀ (kseq n) (le_trans hn (hk n)) (hσcyl n z))⟩
  · -- hred: ContinuouslyReduces (g n) (f ∘ Subtype.val)
    intro n
    refine ⟨σ_n n, (hσc n).subtype_mk ?_, τseq n, ?_, fun z => hcomm n z⟩
    · exact fun x => ⟨x, rfl⟩
    · convert hτc n using 2

private lemma pgl_val_to_minFun_succ' (γ : Ordinal.{0}) {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet (fun _ => MinDom γ)) => (z.val : ℕ → ℕ)) f →
    ContinuouslyReduces (MinFun (Order.succ γ)) f := by
  intro ⟨σ, hσ, τ, hτ, heq⟩
  have h_eq : MinDom (Order.succ γ) = PointedGluingSet (fun _ => MinDom γ) := MinDom_succ γ
  refine ⟨fun z => σ ⟨z.val, h_eq ▸ z.prop⟩, ?_, τ, ?_, fun z => heq ⟨z.val, h_eq ▸ z.prop⟩⟩
  · exact hσ.comp (Continuous.subtype_mk continuous_subtype_val _)
  · convert hτ using 1
    ext y; constructor <;> rintro ⟨z, rfl⟩
    · exact ⟨⟨z.val, h_eq ▸ z.prop⟩, rfl⟩
    · exact ⟨⟨z.val, by rw [h_eq]; exact z.prop⟩, rfl⟩

private lemma pgl_val_to_minFun_limit' (α : Ordinal.{0})
    (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet (fun n => MinDom (cofinalSeq α n))) => (z.val : ℕ → ℕ)) f →
    ContinuouslyReduces (MinFun α) f := by
  intro ⟨σ, hσ, τ, hτ, heq⟩
  have h_eq : MinDom α = PointedGluingSet (fun n => MinDom (cofinalSeq α n)) :=
    MinDom_limit α hlim hne
  refine ⟨fun z => σ ⟨z.val, h_eq ▸ z.prop⟩, ?_, τ, ?_, fun z => heq ⟨z.val, h_eq ▸ z.prop⟩⟩
  · exact hσ.comp (Continuous.subtype_mk continuous_subtype_val _)
  · convert hτ using 1
    ext y; constructor <;> rintro ⟨z, rfl⟩
    · exact ⟨⟨z.val, h_eq ▸ z.prop⟩, rfl⟩
    · exact ⟨⟨z.val, by rw [h_eq]; exact z.prop⟩, rfl⟩

private lemma pgl_fun_id_eq_val' (C : ℕ → Set (ℕ → ℕ)) :
    (fun (z : PointedGluingSet C) => PointedGluingFun C C (fun _ => id) z) =
    (fun (z : PointedGluingSet C) => z.val) := by
  funext z; exact PointedGluingFun_id C z

private lemma CBLevel_AW_iff
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ)
    (W : Set (ℕ → ℕ))
    (β' : Ordinal.{0}) (z : ℕ → ℕ) (hzA : z ∈ A) (hzW : z ∈ W) :
    (⟨z, hzA, hzW⟩ : {u : ℕ → ℕ | u ∈ A ∧ u ∈ W}) ∈
      CBLevel (fun ⟨u, hu⟩ => f ⟨u, hu.1⟩) β' ↔
    (⟨⟨z, hzA⟩, hzW⟩ : {a : A | a.val ∈ W}) ∈
      CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) β' := by
  -- prove the universal statement by induction, then specialize
  suffices h : ∀ (u : ℕ → ℕ) (huA : u ∈ A) (huW : u ∈ W),
      (⟨u, huA, huW⟩ : {u : ℕ → ℕ | u ∈ A ∧ u ∈ W}) ∈
        CBLevel (fun ⟨u, hu⟩ => f ⟨u, hu.1⟩) β' ↔
      (⟨⟨u, huA⟩, huW⟩ : {a : A | a.val ∈ W}) ∈
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) β' from
    h z hzA hzW
  induction' β' using Ordinal.induction with β' ihβ
  induction' β' using Ordinal.limitRecOn with β' ih'
  · intro u huA huW; simp [CBLevel_zero]
  · intro u huA huW
    simp only [CBLevel_succ', isolatedLocus, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨(ihβ β' (Order.lt_succ β') u huA huW).mp h1, fun h3 => h2 ?_⟩
      obtain ⟨_, U, hU_open, hU_mem, hU_const⟩ := h3
      refine ⟨h1,
              (fun a : {v : ℕ → ℕ | v ∈ A ∧ v ∈ W} =>
                (⟨⟨a.val, a.prop.1⟩, a.prop.2⟩ : {a : A | a.val ∈ W})) ⁻¹' U,
              hU_open.preimage (by fun_prop), hU_mem,
              fun y hmem => ?_⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage] at hmem
      have hy_cb' : (⟨⟨y.val, y.prop.1⟩, y.prop.2⟩ : {a : A | a.val ∈ W}) ∈
          CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) β' :=
        (ihβ β' (Order.lt_succ β') y.val y.prop.1 y.prop.2).mp hmem.2
      simpa using hU_const ⟨⟨y.val, y.prop.1⟩, y.prop.2⟩ ⟨hmem.1, hy_cb'⟩
    · intro ⟨h1, h2⟩
      refine ⟨(ihβ β' (Order.lt_succ β') u huA huW).mpr h1, fun h3 => h2 ?_⟩
      obtain ⟨_, U, hU_open, hU_mem, hU_const⟩ := h3
      refine ⟨h1,
              (fun a : {a : A | a.val ∈ W} =>
                (⟨a.val.val, a.val.prop, a.prop⟩ : {v : ℕ → ℕ | v ∈ A ∧ v ∈ W})) ⁻¹' U,
              hU_open.preimage (by fun_prop), hU_mem,
              fun y hmem => ?_⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage] at hmem
      have hy_cb' : (⟨y.val.val, y.val.prop, y.prop⟩ : {v : ℕ → ℕ | v ∈ A ∧ v ∈ W}) ∈
          CBLevel (fun x : {v : ℕ → ℕ | v ∈ A ∧ v ∈ W} => f ⟨x.val, x.prop.1⟩) β' :=
        (ihβ β' (Order.lt_succ β') y.val.val y.val.prop y.prop).mpr hmem.2
      exact hU_const ⟨y.val.val, y.val.prop, y.prop⟩ ⟨hmem.1, hy_cb'⟩
  · rename_i o hlim _
    intro u huA huW
    rw [CBLevel_limit (fun x : {v : ℕ → ℕ | v ∈ A ∧ v ∈ W} => f ⟨x.val, x.prop.1⟩) o hlim,
        CBLevel_limit (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) o hlim]
    simp only [Set.mem_iInter]
    exact ⟨fun h i hi => (ihβ i hi u huA huW).mp (h i hi),
           fun h i hi => (ihβ i hi u huA huW).mpr (h i hi)⟩


private lemma minFun_local_condition'
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) (hf : Continuous f) (hscat : ScatteredFun f)
    (α : Ordinal.{0}) (hα : α < omega1)
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (hlevel_ne : (CBLevel f α).Nonempty)
    (hlevel_succ_empty : CBLevel f (Order.succ α) = ∅)
    (x : A) (hx : x ∈ CBLevel f α)
    (ih : ∀ (β : Ordinal.{0}), β < α → β < omega1 →
      ∀ (A' : Set (ℕ → ℕ)) (f' : A' → ℕ → ℕ),
      Continuous f' → ScatteredFun f' →
      (CBLevel f' β).Nonempty → CBLevel f' (Order.succ β) = ∅ →
      (∃ y' : ℕ → ℕ, ∀ x' ∈ CBLevel f' β, f' x' = y') →
      ContinuouslyReduces (MinFun β) f')
    (β : Ordinal.{0}) (hβ : β < α)
    (U : Set A) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (σ : MinDom β → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      Continuous σ ∧
      (∀ z : MinDom β, (z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ U) ∧
      f x ∉ closure (Set.range (fun z => f (σ z))) := by
  -- Step 1: Get open V in ℕ → ℕ with U = val⁻¹(V)
  obtain ⟨V, hV_open, rfl⟩ : ∃ V : Set (ℕ → ℕ), IsOpen V ∧ U = Subtype.val ⁻¹' V := by
    rw [isOpen_induced_iff] at hU; obtain ⟨t, ht, htU⟩ := hU; exact ⟨t, ht, htU.symm⟩
  -- Step 2: Find point p with exit ordinal γ, in V, and f p N ≠ y N
  obtain ⟨p, γ, N, hpV, hp_cb, hp_exit, hβγ, hγα, hpN⟩ :=
    find_ray_point f hf hscat α hα y hy_simple hlevel_ne hlevel_succ_empty x hx β hβ V hV_open hxU
  -- Step 3: Decompose at p
  obtain ⟨W, hW_clopen, hpW, hW_V, hW_simple, hW_ray⟩ :=
    decompose_at_point f hf hscat p γ N hp_cb hp_exit y hpN V hV_open hpV
  -- Step 4: Set up restricted domain A_W and function f_W
  set A_W : Set (ℕ → ℕ) := {z | z ∈ A ∧ z ∈ W}
  set f_W : A_W → ℕ → ℕ := fun ⟨z, hz⟩ => f ⟨z, hz.1⟩
  -- Step 5: Unpack SimpleFun for {a:A|a.val∈W} and f∘Subtype.val
  obtain ⟨hf_W_scat, δ, hδ_ne, hδ_succ, y_W, hy_W⟩ := hW_simple
  have hf_W_cont : Continuous (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) :=
    hf.comp continuous_subtype_val
  -- Step 6: Transfer CB data from {a:A|a.val∈W} to A_W using CBLevel_AW_iff
  have hδ_ne_W : (CBLevel f_W δ).Nonempty := by
    obtain ⟨⟨⟨z, hzA⟩, hzW⟩, hmem⟩ := hδ_ne
    exact ⟨⟨z, hzA, hzW⟩, (CBLevel_AW_iff f W δ z hzA hzW).mpr hmem⟩
  have hδ_succ_W : CBLevel f_W (Order.succ δ) = ∅ := by
    ext ⟨z, hzA, hzW⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hmem => hδ_succ.subset
      ((CBLevel_AW_iff f W (Order.succ δ) z hzA hzW).mp hmem) |>.elim
  have hy_W_W : ∃ y' : ℕ → ℕ, ∀ x' ∈ CBLevel f_W δ, f_W x' = y' :=
    ⟨y_W, fun ⟨z, hzA, hzW⟩ hmem =>
      hy_W ⟨⟨z, hzA⟩, hzW⟩ ((CBLevel_AW_iff f W δ z hzA hzW).mp hmem)⟩
  -- Step 7: f_W is scattered (from hf_W_scat after converting)
  have hf_W_scat' : ScatteredFun f_W := by
    intro S hS
    set fwd : A_W → {a : A | a.val ∈ W} :=
      fun a => ⟨⟨a.val, a.prop.1⟩, a.prop.2⟩
    obtain ⟨U', hU'_open, hU'_ne, hU'_const⟩ :=
      hf_W_scat (fwd '' S) (hS.image _)
    refine ⟨fwd ⁻¹' U', hU'_open.preimage (by fun_prop), ?_, ?_⟩
    · obtain ⟨_, hzU', ⟨w, hw, rfl⟩⟩ := hU'_ne
      exact ⟨w, by exact hzU', hw⟩
    · intro a ha b hb
      exact hU'_const (fwd a) ⟨ha.1, a, ha.2, rfl⟩ (fwd b) ⟨hb.1, b, hb.2, rfl⟩
  -- Step A: δ < α
  have hδα : δ < α := by
    by_contra h
    push_neg at h
    obtain ⟨⟨⟨z, hzA⟩, hzW⟩, hcb⟩ := hδ_ne
    have hcb_α : (⟨⟨z, hzA⟩, hzW⟩ : {a : A | a.val ∈ W}) ∈
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) α :=
      CBLevel_antitone _ h hcb
    have h_local : Subtype.val ''
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) α =
        CBLevel f α ∩ Subtype.val ⁻¹' W :=
      local_cb_derivative (Subtype.val ⁻¹' W)
        (hW_clopen.isOpen.preimage continuous_subtype_val) α
    have hz_f_α : (⟨z, hzA⟩ : A) ∈ CBLevel f α :=
      (h_local.subset ⟨_, hcb_α, rfl⟩).1
    exact hW_ray ⟨z, hzA⟩ hzW (congr_fun (hy_simple ⟨z, hzA⟩ hz_f_α) N)
  -- Step B: δ < omega1
  have hδω : δ < omega1 := hδα.trans hα
  -- Step C: β ≤ δ
  have hβδ : β ≤ δ := by
    by_contra h
    push_neg at h
    have hemp : CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) β = ∅ :=
      Set.eq_empty_of_subset_empty
        (hδ_succ ▸ CBLevel_antitone _ (Order.succ_le_of_lt h))
    have hp_f_β : p ∈ CBLevel f β := CBLevel_antitone f hβγ hp_cb
    have h_local : Subtype.val ''
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) β =
        CBLevel f β ∩ Subtype.val ⁻¹' W :=
      local_cb_derivative (Subtype.val ⁻¹' W)
        (hW_clopen.isOpen.preimage continuous_subtype_val) β
    obtain ⟨q, hq, _⟩ := h_local.symm.subset ⟨hp_f_β, hpW⟩
    exact hemp.subset hq |>.elim
  -- Step D: apply ih at δ to (A_W, f_W)
  have hred_δ : ContinuouslyReduces (MinFun δ) f_W :=
    ih δ hδα hδω A_W f_W
      (by exact hf.comp (by fun_prop))
      hf_W_scat' hδ_ne_W hδ_succ_W hy_W_W
  -- Step E: chain with MinFun_monotone
  have hred_β : ContinuouslyReduces (MinFun β) f_W :=
    (MinFun_monotone β δ (hβ.trans hα) hδω hβδ).trans hred_δ
  -- Step F: convert to {a:A|a.val∈W} for compose_reduction_from_subtype
  have hred_S : ContinuouslyReduces (MinFun β)
      (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) := by
    obtain ⟨σ₀, hσ₀, τ₀, hτ₀, hτ₀eq⟩ := hred_β
    have hσ_cont : Continuous (fun z => (⟨⟨(σ₀ z).val, (σ₀ z).prop.1⟩, (σ₀ z).prop.2⟩ :
        {a : A | a.val ∈ W})) := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp hσ₀
    refine ⟨fun z => ⟨⟨(σ₀ z).val, (σ₀ z).prop.1⟩, (σ₀ z).prop.2⟩,
            hσ_cont, τ₀, ?_, hτ₀eq⟩
    apply hτ₀.mono
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  -- Step G: closed separating set
  have hC_closed : IsClosed ({z : ℕ → ℕ | z N ≠ y N}) := by
    have : {z : ℕ → ℕ | z N ≠ y N} = (fun z : ℕ → ℕ => z N) ⁻¹' {y N}ᶜ := by
      ext z; simp
    rw [this]
    exact (isClosed_compl_iff.mpr (isOpen_discrete _)).preimage (continuous_apply N)
  -- Step H: apply compose_reduction_from_subtype
  exact compose_reduction_from_subtype f β
    {a : A | a.val ∈ W}
    hred_S
    (Subtype.val ⁻¹' V)
    (fun (a : A) (ha : a.val ∈ W) => hW_V ha)
    {z | z N ≠ y N}
    hC_closed
    (fun ⟨a, (ha : a.val ∈ W)⟩ => hW_ray a ha)
    x
    (by simp only [Set.mem_setOf_eq, not_not]; exact congr_fun (hy_simple x hx) N)


-- **Proposition (Minfunctions). Minimum functions.**

-- Warning MinFun α has CB rank α+1!
/--
PROVIDED SOLUTION

For $\alpha=0$, note that MinFun 0 continuously reduces to any non\-empty function.
So suppose that $\alpha>0$ and that the statement holds for every $\beta<\alpha$.

Take a simple function $f\in\sC_{\alpha+1}$ and let $y\in\im f$ be the distinguished point of $f$.
Seeing that $\Minimalfct{\alpha+1}$ is a pointed gluing, we seek to apply \cref{Pgluingaslowerbound2} for some point $x\in\CB_\alpha(f)$. Let $U\ni x$ be any open set of $\dom f$.
Notice first that as $x\in\CB_\alpha(f)$ and $x\in U$ we get that $f_U=f\restr{U}$ is simple and $\CB(f_U)=\alpha+1$ by \cref{CBbasics0}~\cref{CBbasicsfromJSL2}.
Note that by \cref{CBrankofPgluingofregularsequence2simple} the sequence $(\CB(\ray{f_{U}}{y,n}))_n$ is regular of supremum $\alpha$. If $\alpha=\beta+1$ is successor, then there exists $N$ such that $\alpha=\CB(\ray{f_U}{y,N})$. By the induction hypothesis combined with our first remark, we get $\Minimalfct{\alpha}\leq \ray{f_{U}}{y,N}$.
Notice that if $(\sigma, \tau)$ witnesses this reduction then both $\im \sigma \subseteq U$ and $\overline{\im f\sigma}\subseteq \ray{B}{y,N}$ hold. This ensures that $\Minimalfct{\alpha+1}=\pgl \Minimalfct{\alpha} \leq f$ by \cref{Pgluingaslowerbound2}.


If $\alpha$ is limit, for all $\beta< \alpha$ there exists $N$ such that $\beta+1\leq \CB(\ray{f_{U}}{y,N})< \alpha$. So by the induction hypothesis combined with our first remark, we get $\Minimalfct{\beta+1}\leq \ray{f_{U}}{y,N}$.
So similarly as in the successor case, we get $\Minimalfct{\alpha+1}=\pgl_{k}\Minimalfct{\beta_k+1}\leq f$, for $(\beta_k)_k$ cofinal in $\alpha$.
-/
lemma minFun_is_minimum_simple
    (α : Ordinal.{0}) (hα : α < omega1)
    (A : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hlevel_ne : (CBLevel f α).Nonempty)
    (hlevel_succ_empty : CBLevel f (Order.succ α) = ∅)
    (h_simple : ∃ y : ℕ → ℕ, ∀ x ∈ CBLevel f α, f x = y) :
      ContinuouslyReduces (MinFun α) f := by
    revert A
    induction α using Ordinal.induction with
    | h α ih =>
    intro A f hf hscat hlevel_ne hlevel_succ_empty h_simple
    -- Base case: α = 0
    by_cases hα0 : α = 0
    · subst hα0
      exact minFun_zero_reduces f ⟨(hlevel_ne.some).val, (hlevel_ne.some).property⟩
    -- Extract data from hypotheses
    obtain ⟨y, hy_simple⟩ := h_simple
    have hlevel_ne' := hlevel_ne
    obtain ⟨x, hx⟩ := hlevel_ne'
    have hfx : f x = y := hy_simple x hx
    -- Case split: successor or limit
    by_cases hlim : Order.IsSuccLimit α
    · -- Limit case: α is a limit ordinal
      apply pgl_val_to_minFun_limit' α hlim hα0
      rw [← pgl_fun_id_eq_val' (fun n => MinDom (cofinalSeq α n))]
      apply @pointedGluing_lower_bound A f hf
        (fun n => MinDom (cofinalSeq α n)) (fun n => MinDom (cofinalSeq α n)) (fun _ => id) x
      intro i U hU hxU
      exact minFun_local_condition' f hf hscat α hα y hy_simple hlevel_ne hlevel_succ_empty x hx
        (fun β hβ hβω A' f' hf' hscat' hne' hempty' hsimple' =>
          ih β hβ hβω A' f' hf' hscat' hne' hempty' hsimple')
        (cofinalSeq α i) (cofinalSeq_lt α hlim hα0 i) U hU hxU
    · -- Successor case: α = Order.succ γ
      have : ¬ Order.IsSuccPrelimit α := by
        intro hp; exact hlim ⟨not_isMin_iff_ne_bot.mpr hα0, hp⟩
      rw [Order.not_isSuccPrelimit_iff] at this
      obtain ⟨γ, _, rfl⟩ := this
      apply pgl_val_to_minFun_succ' γ
      rw [← pgl_fun_id_eq_val' (fun _ => MinDom γ)]
      apply @pointedGluing_lower_bound A f hf
        (fun _ => MinDom γ) (fun _ => MinDom γ) (fun _ => id) x
      intro i U hU hxU
      exact minFun_local_condition' f hf hscat (Order.succ γ) hα y hy_simple hlevel_ne hlevel_succ_empty x hx
        (fun β hβ hβω A' f' hf' hscat' hne' hempty' hsimple' =>
          ih β hβ hβω A' f' hf' hscat' hne' hempty' hsimple')
        γ (Order.lt_succ_of_not_isMax (not_isMax γ)) U hU hxU

private lemma minFun_reduces_to_subtype_reduces
    {α : Ordinal.{0}}
    {A : Set (ℕ → ℕ)} {f : A → ℕ → ℕ} {V : Set (ℕ → ℕ)}
    (h : ContinuouslyReduces (MinFun α)
      (fun (z : {u : ℕ → ℕ | u ∈ A ∧ u ∈ V}) => f ⟨z.val, z.prop.1⟩)) :
    ContinuouslyReduces (MinFun α) f := by
  obtain ⟨σ_V, hσ_V_cont, τ_V, hσ_V_range, hσ_V_τ_V⟩ := h
  refine ⟨?_, ?_⟩
  exact fun x => ⟨σ_V x |>.1, σ_V x |>.2.1⟩
  refine ⟨?_, τ_V, ?_, ?_⟩
  · fun_prop
  · grind +revert
  · exact hσ_V_τ_V

private lemma isolated_point_exists_in_CBLevel
    {A : Set (ℕ → ℕ)} {f : A → ℕ → ℕ}
    (hscat : ScatteredFun f) (α : Ordinal.{0})
    (hne : (CBLevel f α).Nonempty) :
    ∃ x : A, x ∈ isolatedLocus f (CBLevel f α) := by
  have := hscat (CBLevel f α) hne
  obtain ⟨U, hU₁, hU₂, hU₃⟩ := this; obtain ⟨x, hx₁, hx₂⟩ := hU₂; use x; simp_all +decide [isolatedLocus]
  exact ⟨U, hU₁, hx₁, fun a ha ha' ha'' => hU₃ _ _ ha' ha'' _ _ hx₁ hx₂ ▸ rfl⟩

theorem minFun_is_minimum
    (α : Ordinal.{0}) (hα : α < omega1)
    (A : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hne : (CBLevel f α).Nonempty) :  -- this implies CBRank f ≥ α+1
        ContinuouslyReduces (MinFun α) f := by
  -- Step 1: Find x in the isolated locus of CBLevel f α
  obtain ⟨x, hx_iso⟩ := isolated_point_exists_in_CBLevel hscat α hne
  have hx_level : x ∈ CBLevel f α := hx_iso.1
  -- Step 2: Get open U with separation properties
  obtain ⟨U, hU_open, hxU, hU_empty, hU_const⟩ :=
    isolatedLocus_gives_simple_neighborhood α x hx_iso
  -- Step 3: Get clopen V ⊆ U in the Baire space
  obtain ⟨W, hW_open, hxW, hW_sub⟩ : ∃ W : Set (ℕ → ℕ), IsOpen W ∧ x.val ∈ W ∧
      Subtype.val ⁻¹' W ⊆ U := by
    rw [isOpen_induced_iff] at hU_open
    obtain ⟨t, ht, htU⟩ := hU_open
    refine ⟨t, ht, ?_, ?_⟩
    · have : x ∈ Subtype.val ⁻¹' t := htU ▸ hxU; exact this
    · intro a ha; exact htU ▸ ha
  obtain ⟨V, hV_clopen, hxV, hV_sub_W⟩ :=
    baire_exists_clopen_subset_of_open x.val W hW_open hxW
  have hV_sub_U : Subtype.val ⁻¹' V ⊆ U := fun a ha => hW_sub (hV_sub_W ha)
  -- Step 4: Establish properties of the restriction to V
  have hV_empty : CBLevel f (Order.succ α) ∩ (Subtype.val ⁻¹' V : Set A) = ∅ :=
    Set.eq_empty_of_forall_notMem fun y hy => hU_empty.subset ⟨hy.1, hV_sub_U hy.2⟩ |>.elim
  -- Step 5: Set up A_V and f_V
  set A_V : Set (ℕ → ℕ) := {z | z ∈ A ∧ z ∈ V}
  set f_V : A_V → ℕ → ℕ := fun ⟨z, hz⟩ => f ⟨z, hz.1⟩
  -- Step 6: Transfer CBLevel data to A_V
  have hf_V_cont : Continuous f_V := hf.comp (by fun_prop)
  have hf_V_scat : ScatteredFun f_V := by
    intro S hS
    set fwd : A_V → {a : A | a.val ∈ V} := fun a => ⟨⟨a.val, a.prop.1⟩, a.prop.2⟩
    have hfwd_cont : Continuous fwd := by fun_prop
    have h_scat_V : ScatteredFun (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) :=
      scattered_restrict f hscat _
    obtain ⟨U', hU'_open, hU'_ne, hU'_const⟩ := h_scat_V (fwd '' S) (hS.image _)
    refine ⟨fwd ⁻¹' U', hU'_open.preimage hfwd_cont, ?_, ?_⟩
    · obtain ⟨_, hzU', ⟨w, hw, rfl⟩⟩ := hU'_ne
      exact ⟨w, hzU', hw⟩
    · intro a ha b hb
      exact hU'_const (fwd a) ⟨ha.1, a, ha.2, rfl⟩ (fwd b) ⟨hb.1, b, hb.2, rfl⟩
  have hne_V : (CBLevel f_V α).Nonempty :=
    ⟨⟨x.val, x.prop, hxV⟩, (CBLevel_AW_iff f V α x.val x.prop hxV).mpr
      ((CBLevel_open_restrict f _ (hV_clopen.isOpen.preimage continuous_subtype_val) α
        ⟨x, hxV⟩).mpr hx_level)⟩
  have hempty_V : CBLevel f_V (Order.succ α) = ∅ := by
    ext ⟨z, hzA, hzV⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hmem
    have h1 : (⟨⟨z, hzA⟩, hzV⟩ : {a : A | a.val ∈ V}) ∈
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) (Order.succ α) :=
      (CBLevel_AW_iff f V (Order.succ α) z hzA hzV).mp hmem
    have h2 : (⟨z, hzA⟩ : A) ∈ CBLevel f (Order.succ α) :=
      (CBLevel_open_restrict f _ (hV_clopen.isOpen.preimage continuous_subtype_val)
        (Order.succ α) ⟨⟨z, hzA⟩, hzV⟩).mp h1
    exact hV_empty.subset ⟨h2, hzV⟩ |>.elim
  have hconst_V : ∃ y : ℕ → ℕ, ∀ z ∈ CBLevel f_V α, f_V z = y := by
    refine ⟨f x, fun ⟨z, hzA, hzV⟩ hmem => ?_⟩
    have hmem' : (⟨⟨z, hzA⟩, hzV⟩ : {a : A | a.val ∈ V}) ∈
        CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) α :=
      (CBLevel_AW_iff f V α z hzA hzV).mp hmem
    have hmem'' : (⟨z, hzA⟩ : A) ∈ CBLevel f α :=
      (CBLevel_open_restrict f _ (hV_clopen.isOpen.preimage continuous_subtype_val)
        α ⟨⟨z, hzA⟩, hzV⟩).mp hmem'
    exact hU_const ⟨z, hzA⟩ ⟨hV_sub_U hzV, hmem''⟩
  -- Step 7: Apply minFun_is_minimum_simple
  have h_red := minFun_is_minimum_simple α hα A_V f_V hf_V_cont hf_V_scat hne_V hempty_V hconst_V
  -- Step 8: Compose with inclusion
  exact minFun_reduces_to_subtype_reduces h_red
