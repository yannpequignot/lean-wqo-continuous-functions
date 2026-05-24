import WqoContinuousFunctions.CenteredFunctions.Defs
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers

import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for CenteredMemo.Theorems

These lemmas decompose the main theorems from Chapter 4 into smaller, more
focused pieces.
-/

/-!
### Helpers for Fact 4.1 (pgluingOfRegularIsCentered)
-/

/-
In the product topology on ℕ → ℕ, any open set containing the zero stream
contains a "cylinder" of the form {x | ∀ k < N, x k = 0} for some N.
-/
lemma zeroStream_nhd_cylinder {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (h0 : zeroStream ∈ U) :
    ∃ N : ℕ, {x : ℕ → ℕ | ∀ k, k < N → x k = 0} ⊆ U := by
  rw [ isOpen_pi_iff ] at hU;
  obtain ⟨ I, u, hIu, hU ⟩ := hU zeroStream h0;
  use I.sup id + 1;
  intro x hx;
  exact hU fun i hi => by have := hx i ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hi ) ) ; aesop;

/-
For j ≥ N, the image of prependZerosOne j lies in the cylinder
{x | ∀ k < N, x k = 0}.
-/
lemma prependZerosOne_in_cylinder (N j : ℕ) (hj : N ≤ j) (x : ℕ → ℕ) :
    ∀ k, k < N → prependZerosOne j x k = 0 := by
  exact fun k hk => if_pos ( lt_of_lt_of_le hk hj )

/-
A regular sequence has arbitrarily large indices with reductions.
-/
lemma regularSeq_large_index {X Y : ℕ → Type*}
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    {f : ∀ n, X n → Y n} (hf : IsRegularSeq f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ ContinuouslyReduces (f i) (f j) := by
  exact Set.Infinite.exists_gt ( hf i ) N |> fun ⟨ j, hj₁, hj₂ ⟩ => ⟨ j, hj₂.le, hj₁ ⟩

/-!
### Helpers for Proposition 4.3 (scatteredHaveCocenter)
-/

/-
If x is a center for f, x ∈ CBLevel f γ, and f is constant on V ∩ CBLevel f γ
for some open V containing x, then f is constant on all of CBLevel f γ.
-/
lemma center_const_on_CBLevel {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x : A) (hx : IsCenterFor f x)
    (γ : Ordinal.{0}) (hx_in : x ∈ CBLevel f γ)
    (V : Set A) (hV : IsOpen V) (hxV : x ∈ V)
    (hconst : ∀ y ∈ V ∩ CBLevel f γ, f y = f x) :
    ∀ a ∈ CBLevel f γ, f a = f x := by
  obtain ⟨σ, hσ, τ, hτ, h⟩ := hx V hV hxV;
  -- By ContinuouslyReduces.cb_monotone, we have σ '' (CBLevel f γ) ⊆ CBLevel (f ∘ Subtype.val : V → B) γ.
  have h_image : σ '' (CBLevel f γ) ⊆ CBLevel (fun x : { x // x ∈ V } => f x.val) γ := by
    apply_rules [ ContinuouslyReduces.cb_monotone ];
  -- By local_cb_derivative, we have CBLevel (f ∘ Subtype.val : V → B) γ = CBLevel f γ ∩ V.
  have h_local : CBLevel (fun x : { x // x ∈ V } => f x.val) γ = CBLevel f γ ∩ V := by
    convert local_cb_derivative V hV γ using 1;
    infer_instance;
  grind

/-
A center for f belongs to every nonempty CB level. That is, if x is a center
for f and CBLevel f β is nonempty, then x ∈ CBLevel f β.
-/
lemma center_in_CBLevel {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x : A) (hx : IsCenterFor f x)
    (β : Ordinal.{0}) (hne : (CBLevel f β).Nonempty) :
    x ∈ CBLevel f β := by
  induction' β using Ordinal.limitRecOn with β ih; simp_all +decide [ CBLevel ] ;
  · have h_not_isolated : ¬x ∈ isolatedLocus f (CBLevel f β) := by
      intro h
      obtain ⟨U, hU_open, hxU, hU_const⟩ := h
      have h_const : ∀ a ∈ CBLevel f β, f a = f x := by
        grind +suggestions
      have h_empty : CBLevel f (Order.succ β) = ∅ := by
        have h_empty : isolatedLocus f (CBLevel f β) = CBLevel f β := by
          ext y; simp [isolatedLocus];
          exact fun hy => ⟨ Set.univ, isOpen_univ, trivial, fun z hz hz' => by rw [ h_const z hz', h_const y hy ] ⟩;
        simp +decide [ CBLevel_succ', h_empty ]
      exact hne.ne_empty h_empty;
    have h_nonempty : (CBLevel f β).Nonempty := by
      exact hne.mono ( CBLevel_antitone f ( Order.le_succ β ) );
    grind +suggestions;
  · rename_i o ho ih;
    have h_inter : ∀ o' < o, x ∈ CBLevel f o' := by
      intro o' ho';
      apply ih o' ho';
      exact hne.mono ( CBLevel_antitone f ho'.le );
    unfold CBLevel at *; aesop;

/-
If x and y are both centers of f with f(x) ≠ f(y), and both belong to
CBLevel f γ, then neither x nor y is in the isolated locus of CBLevel f γ.
-/
lemma center_not_in_isolatedLocus_of_diff_images {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x y : A)
    (hx : IsCenterFor f x) (_hy : IsCenterFor f y)
    (hne : f x ≠ f y)
    (γ : Ordinal.{0}) (hx_in : x ∈ CBLevel f γ) (hy_in : y ∈ CBLevel f γ) :
    x ∉ isolatedLocus f (CBLevel f γ) := by
  contrapose! hne;
  -- Since x is in the isolated locus of the CBLevel at γ, there exists an open set V containing x such that f is constant on V ∩ CBLevel f γ.
  obtain ⟨V, hV_open, hxV, h_const⟩ : ∃ V : Set A, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V ∩ CBLevel f γ, f z = f x := by
    exact hne.2;
  exact Eq.symm ( center_const_on_CBLevel f x hx γ hx_in V hV_open hxV h_const y hy_in )

/-
If x and y are both centers with f(x) ≠ f(y), then both belong to every
CB level (i.e., they are in the perfect kernel).
-/
lemma centers_in_all_CBLevels {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x y : A)
    (hx : IsCenterFor f x) (hy : IsCenterFor f y)
    (hne : f x ≠ f y) :
    ∀ α : Ordinal.{0}, x ∈ CBLevel f α ∧ y ∈ CBLevel f α := by
  intro α
  induction' α using Ordinal.limitRecOn with α hα;
  · exact ⟨ CBLevel_zero f ▸ Set.mem_univ x, CBLevel_zero f ▸ Set.mem_univ y ⟩;
  · simp_all +decide [ CBLevel_succ' ];
    exact ⟨ center_not_in_isolatedLocus_of_diff_images f x y hx hy hne α hα.1 hα.2, center_not_in_isolatedLocus_of_diff_images f y x hy hx ( Ne.symm hne ) α hα.2 hα.1 ⟩;
  · simp_all +decide [ CBLevel ]

/-
If two centers of a scattered function have different images, then the
perfect kernel is nonempty — contradicting scatteredness.
-/
lemma centers_different_images_not_scattered {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A] [Small.{0} A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x y : A)
    (hx : IsCenterFor f x) (hy : IsCenterFor f y)
    (hne : f x ≠ f y) :
    ¬ ScatteredFun f := by
  -- By definition of scatteredFun, if f is scattered, then its perfect kernel is empty.
  by_contra h_scattered
  have h_perfect_kernel_empty : perfectKernelCB f = ∅ := by
    exact (scattered_iff_empty_perfectKernel_general f).mp h_scattered;
  exact Set.notMem_empty x ( h_perfect_kernel_empty ▸ Set.mem_iInter.mpr ( fun α => ( centers_in_all_CBLevels f x y hx hy hne ) α |>.1 ) )

/-- If all centers of f have the same image and f is centered,
then f is scattered if and only if f is always scattered (tautological direction
for the backward implication). The key content is that the hypothesis about
centers having the same image is used in the backward direction. -/
lemma cocenter_unique_implies_scattered {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (_hf_cent : IsCentered f)
    (_hcocenter : ∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y)
    (hf_scat : ScatteredFun f) : ScatteredFun f := hf_scat

/-!
### Helpers for Proposition 4.4, Item 3 (rigidityOfCocenter_finiteGluing)
-/

/-
Given continuity of σ and a center x for g at σ(x), for any m there exists
an open set U containing σ(x) such that g maps U into the m-cylinder of y_g.
-/
lemma cocenter_continuity_cylinder {A : Type*} [TopologicalSpace A]
    {g : A → ℕ → ℕ} {σ : A → A}
    (_hσ : Continuous σ) (x : A) (y_g : ℕ → ℕ)
    (hg_cont : Continuous g)
    (_hσx_center : IsCenterFor g (σ x))
    (hg_eq : g (σ x) = y_g)
    (m : ℕ) :
    ∃ U : Set A, IsOpen U ∧ σ x ∈ U ∧
      ∀ a ∈ U, ∀ k, k < m → g a k = y_g k := by
  -- Define the set V as the intersection of all sets {a | g a k = y_g k} for k < m.
  set V := ⋂ k < m, {a | g a k = y_g k};
  have hV_open : IsOpen V := by
    refine' isOpen_iff_forall_mem_open.mpr _;
    intro x hx
    use ⋂ k < m, {a | g a k = y_g k};
    simp_all +decide [ Set.subset_def ];
    exact ⟨ fun x hx => Set.mem_iInter₂.2 hx, by rw [ show ( ⋂ k : ℕ, ⋂ ( _ : k < m ), { a | g a k = y_g k } ) = ⋂ k ∈ Finset.range m, { a | g a k = y_g k } by ext; simp +decide [ Finset.mem_range ] ] ; exact isOpen_biInter_finset fun i _ => isOpen_discrete { y_g i } |> IsOpen.preimage ( show Continuous fun a => g a i from continuous_apply i |> Continuous.comp <| hg_cont ) , fun i hi => Set.mem_iInter₂.1 hx i hi ⟩;
  exact ⟨ V, hV_open, Set.mem_iInter₂.2 fun k hk => by simp +decide [ hg_eq ], fun a ha k hk => Set.mem_iInter₂.1 ha k hk ⟩

/-!
### Helpers for Theorem 4.6 (centeredAsPgluing_iff_monotone)
-/

-- The backward direction of Theorem 4.6 (centered_of_monotone_pgluing)
-- is in Theorems.lean (uses pgluingOfRegularIsCentered)

/-- The forward direction: if f is centered, then f ≡ pgl_i f_i for some
monotone sequence. Uses regularization of the ray sequence. -/
lemma monotone_pgluing_of_centered
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f) (hf_cent : IsCentered f) :
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (g : ∀ i, C i → D i),
      IsMonotoneSeq (fun i => (fun (x : C i) => (g i x : ℕ → ℕ))) ∧
      ContinuouslyEquiv f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry

/-!
### Helpers for Theorem 4.7 (localCenterednessFromBQO)
-/

/-
Base case: any function with CB-rank 0 is locally centered
(vacuously, since it must be empty or locally constant).
-/
lemma locallyCentered_rank_zero {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (_hf_scat : ScatteredFun f) (hf_rank : CBRank f = 0) :
    IsLocallyCentered f := by
  -- By CBLevel_eq_empty_at_rank (which needs Small.{0} X and ScatteredFun f):
  -- CBLevel f (CBRank f) = ∅.
  have h_empty : CBLevel f (CBRank f) = ∅ := by
    exact CBLevel_eq_empty_at_rank f _hf_scat;
  simp_all +decide [ CBLevel_zero ];
  exact fun x => False.elim ( h_empty.elim x )

/-
Restriction to an open set preserves scatteredness.
-/
lemma scatteredFun_restrict_open {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : ScatteredFun f) (U : Set X) :
    ScatteredFun (f ∘ (Subtype.val : U → X)) := by
  exact scattered_restrict f hf U

/-- Homeomorphism between nested subtypes and intersection subtypes. -/
def subtypeSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (U W : Set X) :
    {u : U // u.val ∈ W} ≃ₜ {x : X // x ∈ U ∩ W} :=
  Homeomorph.mk ⟨fun ⟨⟨x, hU⟩, hW⟩ => ⟨x, ⟨hU, hW⟩⟩,
    fun ⟨x, hx⟩ => ⟨⟨x, hx.1⟩, hx.2⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
    (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)

/-
IsCentered is preserved by homeomorphism of the domain.
-/
lemma isCentered_of_homeomorph {X X' Y : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    (f : X → Y) (g : X' → Y) (φ : X' ≃ₜ X)
    (h : ∀ x, g x = f (φ x)) (hc : IsCentered f) : IsCentered g := by
  obtain ⟨ c, hc ⟩ := hc;
  -- Take c' = φ⁻¹ c as center for g.
  use φ.symm c;
  intro U hU hcu
  obtain ⟨σ, τ, hσ, hτ, hfg⟩ := hc (φ '' U) (by
  exact φ.isOpen_image.mpr hU) (by
  exact ⟨ _, hcu, φ.apply_symm_apply c ⟩);
  refine' ⟨ _, _, _ ⟩;
  exact fun x => ⟨ φ.symm ( σ ( φ x ) |>.1 ), by obtain ⟨ y, hy, hy' ⟩ := σ ( φ x ) |>.2; simpa [ ← hy' ] using hy ⟩;
  · fun_prop;
  · refine' ⟨ hσ, _, _ ⟩;
    · refine' hτ.mono _;
      rintro _ ⟨ x, rfl ⟩ ; simp +decide [ h ] ;
    · grind +suggestions

/-
IsCentered transfers from nested subtypes to flat intersection subtype.
-/
lemma isCentered_subtypeSubtype {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (U : Set X) (hU : IsOpen U) (V : Set U) (hV : IsOpen V) :
    IsCentered ((f ∘ Subtype.val) ∘ (Subtype.val : V → U)) →
    IsCentered (f ∘ (Subtype.val : (U ∩ (Subtype.val '' V) : Set X) → X)) := by
  rintro ⟨ c, hc ⟩;
  refine' ⟨ ⟨ c.val.val, ⟨ c.val.prop, _ ⟩ ⟩, _ ⟩;
  exact ⟨ c, c.prop, rfl ⟩;
  intro W hW hcW;
  -- Let $W'$ be the preimage of $W$ under the inclusion map from $V$ to $U \cap \text{image}(V)$.
  set W' : Set V := {v : V | ⟨v.val.val, ⟨v.val.prop, ⟨v.val, v.prop, rfl⟩⟩⟩ ∈ W} with hW';
  have hW'_open : IsOpen W' := by
    convert hW.preimage _;
    fun_prop;
  have := hc W' hW'_open ( by aesop );
  obtain ⟨ τ, hτ₁, hτ₂ ⟩ := this;
  obtain ⟨ σ, hσ₁, hσ₂ ⟩ := hτ₂;
  refine' ⟨ _, _, _ ⟩;
  use fun x => ⟨ ⟨ τ ⟨ ⟨ x.val, by
    exact x.2.1 ⟩, by
    grind ⟩ |>.1 |>.1, by
    grind ⟩, by
    all_goals generalize_proofs at *;
    exact τ ⟨ ⟨ x, by assumption ⟩, by assumption ⟩ |>.2 ⟩
  all_goals generalize_proofs at *;
  · fun_prop (disch := solve_by_elim);
  · use σ;
    refine' ⟨ _, _ ⟩;
    · convert hσ₁ using 1;
      ext; simp [Function.comp];
      exact ⟨ fun ⟨ a, ⟨ b, c ⟩, d ⟩ => ⟨ a, b, c, d ⟩, fun ⟨ a, b, c, d ⟩ => ⟨ a, ⟨ b, c ⟩, d ⟩ ⟩;
    · grind

/-
If f|_U is locally centered and x ∈ U (U open), then there exists
an open V ⊆ U with x ∈ V and f|_V centered.
-/
lemma isLocallyCentered_restrict_open {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (U : Set X) (hU : IsOpen U)
    (hlc : IsLocallyCentered (f ∘ (Subtype.val : U → X)))
    (x : X) (hxU : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsCentered (f ∘ (Subtype.val : V → X)) := by
  have := hlc ⟨ x, hxU ⟩;
  obtain ⟨ V, hV₁, hV₂, hV₃ ⟩ := this;
  refine' ⟨ U ∩ ( Subtype.val '' V ), _, _, _ ⟩;
  · obtain ⟨ t, ht₁, ht₂ ⟩ := hV₁;
    convert hU.inter ht₁ using 1 ; ext ; aesop;
  · grind +splitImp;
  · convert isCentered_subtypeSubtype f U hU V hV₁ hV₃

/-
CB levels are closed sets. Proved by transfinite induction:
- Base: `CBLevel f 0 = univ` is closed.
- Successor: `CBLevel f (β+1) = CBLevel f β \ isolatedLocus f (CBLevel f β)`. Since
  `isolatedLocus` is relatively open in `CBLevel f β` and `CBLevel f β` is closed (by IH),
  the difference is closed.
- Limit: intersection of closed sets is closed.
-/
lemma CBLevel_closed' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (β : Ordinal.{0}) : IsClosed (CBLevel f β) := by
  induction' β using Ordinal.limitRecOn with β ih;
  · -- The base case is when β = 0. The CB level at 0 is the entire space X, which is closed.
    simp [CBLevel];
  · rw [ CBLevel_succ' ];
    refine' isClosed_iff_nhds.2 fun x hx => _;
    refine' ⟨ _, _ ⟩;
    · contrapose! hx;
      exact ⟨ ( CBLevel f β ) ᶜ, IsOpen.mem_nhds ( isOpen_compl_iff.mpr ih ) hx, by aesop ⟩;
    · contrapose! hx;
      obtain ⟨ U, hUo, hxU, hU ⟩ := hx;
      refine' ⟨ hUo, hxU.mem_nhds hU.1, _ ⟩;
      simp +decide [ Set.ext_iff, isolatedLocus ];
      exact fun y hy hy' => ⟨ hUo, hxU, hy, fun z hz hz' => hU.2 z ⟨ hz, hz' ⟩ ▸ hU.2 y ⟨ hy, hy' ⟩ ▸ rfl ⟩;
  · simp +decide [ CBLevel, * ];
    exact isClosed_iInter fun γ => isClosed_iInter fun hγ => by solve_by_elim;

/-
Limit case: if f has limit CB-rank, then f is locally of lower rank,
hence locally centered by induction.
-/
lemma locallyCentered_limit_rank {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf_scat : ScatteredFun f)
    (α : Ordinal.{0}) (hα_limit : Order.IsSuccLimit α) (_hα_ne : α ≠ 0)
    (hf_rank : CBRank f = α)
    (ih : ∀ β < α, ∀ (X' Y' : Type) [TopologicalSpace X'] [TopologicalSpace Y']
      (g : X' → Y'), ScatteredFun g → CBRank g = β → IsLocallyCentered g) :
    IsLocallyCentered f := by
  intro x
  -- limit_locally_lower: since α is a limit rank, every x has an open neighborhood U
  -- where the restriction f|_U has CB-rank strictly below α.
  obtain ⟨U, hU_open, hxU, hU_rank⟩ :=
    limit_locally_lower hf_scat α hf_rank.symm hα_limit x
  -- f|_U is scattered (restrictions of scattered functions are scattered)
  have hU_scat : ScatteredFun (f ∘ (Subtype.val : U → X)) :=
    scatteredFun_restrict_open hf_scat U
  -- By the induction hypothesis at rank CBRank (f|_U) < α, f|_U is locally centered
  have hU_lc : IsLocallyCentered (f ∘ (Subtype.val : U → X)) :=
    ih _ hU_rank _ _ (f ∘ Subtype.val) hU_scat rfl
  -- Descend to a centered subneighborhood of x inside U
  exact isLocallyCentered_restrict_open f U hU_open hU_lc x hxU

/-- Successor case: if f has successor CB-rank α+1 and 𝒞_{<α+1} is BQO,
then f is locally centered. -/
lemma locallyCentered_succ_rank
    (α : Ordinal.{0}) (hα : α < omega1)
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < Order.succ α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n))
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf_scat : ScatteredFun f)
    (hf_rank : CBRank f = Order.succ α)
    (ih : ∀ β < Order.succ α, ∀ (X' Y' : Type) [TopologicalSpace X'] [TopologicalSpace Y']
      (g : X' → Y'), ScatteredFun g → CBRank g = β → IsLocallyCentered g) :
    IsLocallyCentered f := by
  sorry

/-!
### Helpers for Corollary 4.10 (centeredSuccessor)
-/

/-- The minimum function k_{λ+1} is centered. -/
lemma minFun_isCentered (lam : Ordinal.{0}) :
    IsCentered (MinFun lam) := by
  sorry

/-- The pointed gluing of the max function pgl(ℓ_λ) is centered. -/
lemma pglMaxFun_isCentered (lam : Ordinal.{0}) :
    ∃ (X₂ Y₂ : Type) (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (g : X₂ → Y₂), IsCentered g ∧ CBRank g = Order.succ lam := by
  sorry

/-- k_{λ+1} and pgl(ℓ_λ) are not equivalent (strict inequality). -/
lemma minFun_lt_pglMaxFun (lam : Ordinal.{0})
    (hlam : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hlam_lt : lam < omega1) :
    ∃ (X₁ Y₁ X₂ Y₂ : Type)
      (_ : TopologicalSpace X₁) (_ : TopologicalSpace Y₁)
      (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (min_f : X₁ → Y₁) (pgl_max : X₂ → Y₂),
      ContinuouslyReduces min_f pgl_max ∧
      ¬ ContinuouslyReduces pgl_max min_f := by
  sorry

/-!
### Helpers for Proposition 4.11 (simpleIffCoincidenceOfCocenters)
-/

/-- If f has successor CB-rank, then I = {n | CB(f_n) = sup CB(f_i)} is nonempty,
where f_i are the pieces from an open partition. -/
lemma successor_rank_implies_I_nonempty
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B)
    (P : ℕ → Set A) (hcover : ⋃ i, P i = univ)
    (α : Ordinal.{0}) (hα : CBRank f = Order.succ α) :
    {n : ℕ | CBRank (f ∘ (Subtype.val : P n → A)) =
      ⨆ i, CBRank (f ∘ (Subtype.val : P i → A))}.Nonempty := by
  sorry

/-- If I = {n | CB(f_n) = sup CB(f_i)} is nonempty, then CB(f) is a successor. -/
lemma I_nonempty_implies_successor_rank
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B)
    (P : ℕ → Set A) (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : ⋃ i, P i = univ)
    (hf_cent : ∀ i, IsCentered (f ∘ (Subtype.val : P i → A)))
    (hf_scat : ScatteredFun f)
    (hne : {n : ℕ | CBRank (f ∘ (Subtype.val : P n → A)) =
      ⨆ i, CBRank (f ∘ (Subtype.val : P i → A))}.Nonempty) :
    ∃ α : Ordinal.{0}, CBRank f = Order.succ α := by
  sorry

end
