import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers

/-!
# Self-similarity of pointed gluing structures

This file establishes self-similarity properties of pointed gluing sets, showing
that iterating the gluing construction can be "flattened" via continuous reductions.
-/

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

lemma gluingSet_flatten_const (S : Set (ℕ → ℕ)) :
    ContinuouslyReduces
      (fun x : GluingSet (fun _ => GluingSet (fun _ => S)) => x.val)
      (fun x : GluingSet (fun _ => S) => x.val) := by
  constructor
  swap
  exact fun x => ⟨prepend (Nat.pair (x.val 0) (x.val 1)) (fun k => x.val (k + 2)), by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.2
    obtain ⟨y, hy, hy'⟩ := hi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    obtain ⟨z, hz, rfl⟩ := hj
    simp +decide [← hy', prepend]
    exact Set.mem_iUnion.mpr ⟨Nat.pair i j, Set.mem_image_of_mem _ hz⟩⟩
  all_goals generalize_proofs at *
  refine ⟨?_, ?_⟩
  · refine Continuous.subtype_mk ?_ ?_
    refine continuous_pi fun k => ?_
    induction' k with k ih
    · exact Continuous.comp (show Continuous fun x : ℕ × ℕ => Nat.pair x.1 x.2 from by continuity) (Continuous.prodMk (continuous_apply 0 |> Continuous.comp <| continuous_subtype_val) (continuous_apply 1 |> Continuous.comp <| continuous_subtype_val))
    · exact continuous_apply (k + 2) |> Continuous.comp <| continuous_subtype_val
  · refine ⟨?_, ?_, ?_⟩
    exact fun x => fun k => if k = 0 then Nat.unpair (x 0) |>.1 else if k = 1 then Nat.unpair (x 0) |>.2 else x (k - 1)
    · refine Continuous.continuousOn ?_
      fun_prop
    · intro x; ext k; rcases k with (_ | _ | k) <;> simp +decide [prepend]

lemma gluingSet_copies_reduces_to_MaxFun_succ (β : Ordinal.{0}) :
    ContinuouslyReduces
      (fun x : GluingSet (fun _ => MaxDom (Order.succ β)) => (x.val : ℕ → ℕ))
      (MaxFun (Order.succ β)) := by
  convert gluingSet_flatten_const (SuccMaxDom β) using 1
  all_goals congr! 1
  all_goals norm_num [MaxDom_succ, MaxFun]
  all_goals congr! 1
  · ext; simp [MaxDom_succ]; grind
  · ext; simp [MaxDom, SuccMaxDom]

lemma gluingSet_MaxDom_limit_inner_mem
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (z : GluingSet (fun _ => MaxDom α)) :
    (fun k => z.val (k + 2)) ∈ MaxDom (enumBelow α (z.val 1)) := by
  have hz : ∃ i, ∃ x ∈ MaxDom α, z.val = prepend i x := by
    rcases z with ⟨z, hz⟩; rw [GluingSet] at hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz; use i; aesop
  obtain ⟨i, x, hx, hz⟩ := hz; simp_all +decide [MaxDom_limit α hlim hne]
  unfold GluingSet at hx; aesop

lemma mem_MaxDom_limit_prepend
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (j : ℕ) (z : ℕ → ℕ) (hz : z ∈ MaxDom (enumBelow α j)) :
    prepend j z ∈ MaxDom α := by
  rw [MaxDom_limit α hlim hne]; exact mem_gluingSet_prepend hz

lemma gluingSet_empty_isEmpty :
    IsEmpty (GluingSet (fun _ => (∅ : Set (ℕ → ℕ)))) := by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := hx
  aesop

lemma gluingSet_MaxDom_limit_inner_gluing
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (z : GluingSet (fun _ => MaxDom α)) :
    prepend (z.val 0) (fun k => z.val (k + 2)) ∈
      GluingSet (fun _ => MaxDom (enumBelow α (z.val 1))) := by
  exact mem_gluingSet_prepend (gluingSet_MaxDom_limit_inner_mem α hlim hne z)

/-!
## Coordinate-wise continuity for functions depending on a locally constant index

The function σ_raw(z) = prepend (z 1) (σ_{z 1}(w_z)).val has the property
that z.val 1 is locally constant. On each clopen piece {z | z.val 1 = n},
σ_raw is a composition of continuous functions.
-/

/--
In the Baire space, {x | x n = c} is clopen.
-/
lemma baire_coord_eq_clopen (n : ℕ) (c : ℕ) :
    IsClopen {x : ℕ → ℕ | x n = c} := by
  have h_proj : Continuous (fun x : ℕ → ℕ => x n) := by
    fun_prop
  generalize_proofs at *; (
  exact ⟨isClosed_eq h_proj continuous_const, h_proj.isOpen_preimage { c } (by simp +decide)⟩)

/--
The coordinate projection is locally constant: z.val k is constant in a
    neighborhood of any point (for the product topology).
-/
lemma baire_subtype_coord_locally_const {S : Set (ℕ → ℕ)} (k : ℕ) (z : S) :
    ∀ᶠ w in nhds z, w.val k = z.val k := by
  rw [eventually_nhds_iff]
  refine ⟨{ w : S | w.val k = z.val k }, ?_, ?_, ?_⟩ <;> norm_num
  exact IsOpen.preimage (continuous_subtype_val) (baire_coord_eq_clopen k (z.val k) |>.2)

/--
A function that is piecewise defined on a clopen set is continuous
    if both branches are continuous.
-/
lemma continuous_piecewise_clopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsClopen s)
    {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    [∀ a, Decidable (a ∈ s)] :
    Continuous (s.piecewise f g) := by
  apply_rules [Continuous.if, continuous_const]
  simp +decide [hs.frontier_eq]

/--
On a clopen neighborhood, a function that agrees with a continuous
    function is ContinuousAt.
-/
lemma continuousAt_of_locally_eq_on_clopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : X → Y} {x : X} {s : Set X}
    (hs : IsClopen s) (hx : x ∈ s)
    (hg : Continuous g)
    (heq : ∀ y ∈ s, f y = g y) :
    ContinuousAt f x := by
  exact ContinuousAt.congr (hg.continuousAt) (Filter.eventually_of_mem (hs.isOpen.mem_nhds hx) (fun y hy => Eq.symm (heq y hy)))

/--
For a function z ↦ F(z.val 1, z) where z.val 1 is locally constant
    and F(n, ·) is continuous for each n, the whole function is continuous.
-/
lemma continuous_of_locally_constant_index
    {S : Set (ℕ → ℕ)} (F : ℕ → S → ℕ)
    (hF : ∀ n, Continuous (F n))
    (_hF_eq : ∀ (z : S), F (z.val 1) z =
      (fun z => F (z.val 1) z) z) :
    Continuous (fun z : S => F (z.val 1) z) := by
  rw [continuous_iff_continuousAt]
  intro x
  -- Since z.val 1 is locally constant, there exists an open neighborhood U around x where z.val 1 is constant.
  obtain ⟨U, hU_open, hxU, hU_const⟩ : ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, z.val 1 = x.val 1 := by
    have := baire_subtype_coord_locally_const 1 x
    exact Exists.imp (by tauto) (mem_nhds_iff.mp this)
  exact ContinuousAt.congr (hF (x.val 1) |> Continuous.continuousAt) (Filter.eventuallyEq_of_mem (hU_open.mem_nhds hxU) fun y hy => by aesop)

/-!
## Self-similarity: GluingSet(fun _ => MaxDom α) ≤ MaxFun α
-/

/--
σ continuity for the limit case: the composition
    z ↦ prepend (z.val 1) (σ_n (z.val 1) ⟨prepend (z.val 0) (tail² z), ...⟩).val
    is continuous as a map into the subtype MaxDom α.
-/
lemma limit_sigma_continuous
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (σ_n : (n : ℕ) → GluingSet (fun _ => MaxDom (enumBelow α n)) →
      MaxDom (enumBelow α n))
    (hσ_n : ∀ n, Continuous (σ_n n)) :
    Continuous (fun (z : GluingSet (fun _ => MaxDom α)) =>
      (⟨prepend (z.val 1)
        (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
          gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).val,
        mem_MaxDom_limit_prepend α hlim hne _ _
          (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
            gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).prop⟩
        : MaxDom α)) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro z
  set n₀ := z.val 1
  -- The set {z | z.val 1 = n₀} is clopen.
  have h_clopen : IsClopen {z : GluingSet (fun _ => MaxDom α) | z.val 1 = n₀} := by
    have h_clopen : IsClopen {x : ℕ → ℕ | x 1 = n₀} := by
      exact baire_coord_eq_clopen 1 n₀
    exact ⟨h_clopen.1.preimage continuous_subtype_val, h_clopen.2.preimage continuous_subtype_val⟩
  refine ContinuousOn.continuousAt ?_ (h_clopen.isOpen.mem_nhds rfl)
  rw [continuousOn_iff_continuous_restrict]
  refine Continuous.subtype_mk ?_ ?_
  have h_cont : Continuous (fun x : {x : GluingSet (fun _ => MaxDom α) | x.val 1 = n₀} => prepend n₀ (σ_n n₀ ⟨prepend (x.val.val 0) (fun k => x.val.val (k + 2)), by
    convert gluingSet_MaxDom_limit_inner_gluing α hlim hne x.val using 1
    grind⟩).val) := by
    all_goals generalize_proofs at *
    refine Continuous.comp (continuous_prepend n₀) ?_
    refine Continuous.comp (continuous_subtype_val) (hσ_n n₀ |> Continuous.comp <| ?_)
    refine Continuous.subtype_mk ?_ ?_
    refine continuous_pi fun k => ?_
    unfold prepend; split_ifs <;> [exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val.comp <| continuous_subtype_val; exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| continuous_subtype_val]
  generalize_proofs at *
  grind

/--
Equation verification for the limit case
-/
lemma limit_eq_verification
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (σ_n : (n : ℕ) → GluingSet (fun _ => MaxDom (enumBelow α n)) →
      MaxDom (enumBelow α n))
    (τ_n : ℕ → (ℕ → ℕ) → (ℕ → ℕ))
    (hτ_n_eq : ∀ n (x : GluingSet (fun _ => MaxDom (enumBelow α n))),
      x.val = τ_n n ((σ_n n x).val))
    (z : GluingSet (fun _ => MaxDom α)) :
    z.val = (fun y : ℕ → ℕ =>
      let n := y 0
      let v := τ_n n (unprepend y)
      prepend (v 0) (prepend n (unprepend v)))
      ((⟨prepend (z.val 1)
        (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
          gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).val,
        mem_MaxDom_limit_prepend α hlim hne _ _
          (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
            gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).prop⟩
        : MaxDom α).val) := by
  ext k
  rcases k with (_ | _ | k) <;> simp +decide [prepend, unprepend]
  · convert congr_fun (hτ_n_eq (z.val 1) ⟨prepend (z.val 0) fun k => z.val (k + 2), gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩) 0 using 1
  · convert congr_fun (hτ_n_eq (z.val 1) ⟨prepend (z.val 0) fun k => z.val (k + 2), gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩) (k + 1) using 1

/--
ContinuousOn τ on the range for the limit case
-/
lemma limit_tau_continuousOn
    (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hne : α ≠ 0)
    (σ_n : (n : ℕ) → GluingSet (fun _ => MaxDom (enumBelow α n)) →
      MaxDom (enumBelow α n))
    (_hσ_n : ∀ n, Continuous (σ_n n))
    (τ_n : ℕ → (ℕ → ℕ) → (ℕ → ℕ))
    (hτ_n_contOn : ∀ n, ContinuousOn (τ_n n)
      (Set.range (Subtype.val ∘ σ_n n))) :
    ContinuousOn
      (fun y : ℕ → ℕ =>
        let n := y 0
        let v := τ_n n (unprepend y)
        prepend (v 0) (prepend n (unprepend v)))
      (Set.range (MaxFun α ∘
        fun (z : GluingSet (fun _ => MaxDom α)) =>
          (⟨prepend (z.val 1)
            (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
              gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).val,
            mem_MaxDom_limit_prepend α hlim hne _ _
              (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
                gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).prop⟩
            : MaxDom α))) := by
  convert continuousOn_piecewise_clopen (τ_i := fun n y => prepend (τ_n n (unprepend y) 0) (prepend n (unprepend (τ_n n (unprepend y))))) (S_i := fun n => { y : ℕ → ℕ | y 0 = n }) _ _ _ _ _ using 1
  case convert_1 => exact range (MaxFun α ∘ fun z : GluingSet (fun _ => MaxDom α) => ⟨prepend (z.val 1) (σ_n (z.val 1) ⟨prepend (z.val 0) fun k => z.val (k + 2), gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).val, mem_MaxDom_limit_prepend α hlim hne _ _ (σ_n (z.val 1) ⟨prepend (z.val 0) fun k => z.val (k + 2), gluingSet_MaxDom_limit_inner_gluing α hlim hne z⟩).prop⟩)
  all_goals norm_num
  · constructor
    · intro h τ hτ
      refine h.congr ?_
      rintro _ ⟨z, rfl⟩ ; exact hτ _ _ z.2 rfl
    · grind +revert
  · -- The set {y | y 0 = i} is clopen because it is the preimage of a clopen set under a continuous function.
    intros i
    apply baire_coord_eq_clopen
  · intro n
    refine ContinuousOn.comp (show ContinuousOn (fun y => prepend (τ_n n y 0) (prepend n (unprepend (τ_n n y)))) (range (Subtype.val ∘ σ_n n)) from ?_) ?_ ?_
    · refine ContinuousOn.comp (show ContinuousOn (fun y => prepend (y 0) (prepend n (unprepend y))) (Set.univ : Set (ℕ → ℕ)) from ?_) ?_ ?_
      · refine Continuous.continuousOn ?_
        refine continuous_pi_iff.mpr ?_
        intro i; induction i <;> simp +decide [*, prepend, unprepend] ; continuity
        split_ifs <;> [exact continuous_const; exact continuous_apply _]
      · exact hτ_n_contOn n
      · exact fun x hx => Set.mem_univ _
    · exact Continuous.continuousOn (by exact continuous_unprepend)
    · intro y hy; aesop

/-!
## Main self-similarity theorem
-/
lemma gluingSet_copies_reduces_to_MaxFun (α : Ordinal.{0}) (hα : α < omega1) :
    ContinuouslyReduces
      (fun x : GluingSet (fun _ => MaxDom α) => (x.val : ℕ → ℕ))
      (MaxFun α) := by
  induction α using Ordinal.induction with
  | h α ih =>
  by_cases h0 : α = 0
  · -- Zero case
    subst h0
    have hempty : GluingSet (fun _ => MaxDom 0) = ∅ := by
      ext x; simp [GluingSet, MaxDom_zero]
    haveI : IsEmpty (GluingSet (fun _ => MaxDom 0)) := by
      rw [hempty]; exact Set.isEmpty_coe_sort.mpr rfl
    exact ⟨isEmptyElim, continuous_of_discreteTopology,
      fun _ => 0, continuousOn_const, isEmptyElim⟩
  · by_cases hlim : Order.IsSuccLimit α
    · -- Limit case
      have ih_at : ∀ n, ContinuouslyReduces
          (fun x : GluingSet (fun _ => MaxDom (enumBelow α n)) => x.val)
          (MaxFun (enumBelow α n)) :=
        fun n => ih (enumBelow α n) (enumBelow_lt α h0 n)
          (lt_trans (enumBelow_lt α h0 n) hα)
      choose σ_n hσ_n_cont τ_n hτ_n_contOn hτ_n_eq using ih_at
      exact ⟨
        fun z => ⟨prepend (z.val 1)
            (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
              gluingSet_MaxDom_limit_inner_gluing α hlim h0 z⟩).val,
            mem_MaxDom_limit_prepend α hlim h0 _ _
              (σ_n (z.val 1) ⟨prepend (z.val 0) (fun k => z.val (k + 2)),
                gluingSet_MaxDom_limit_inner_gluing α hlim h0 z⟩).prop⟩,
        limit_sigma_continuous α hlim h0 σ_n hσ_n_cont,
        fun y => let n := y 0; let v := τ_n n (unprepend y)
          prepend (v 0) (prepend n (unprepend v)),
        limit_tau_continuousOn α hlim h0 σ_n hσ_n_cont τ_n hτ_n_contOn,
        fun z => limit_eq_verification α hlim h0 σ_n τ_n
          (fun n x => hτ_n_eq n x) z⟩
    · -- Successor case
      have : ¬ Order.IsSuccPrelimit α := by
        intro h
        exact hlim ⟨fun hmin => h0 (le_antisymm (hmin (zero_le α)) (zero_le α)), h⟩
      rw [Order.not_isSuccPrelimit_iff] at this
      obtain ⟨β, _, rfl⟩ := this
      exact gluingSet_copies_reduces_to_MaxFun_succ β

end
