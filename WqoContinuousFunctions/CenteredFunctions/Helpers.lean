import WqoContinuousFunctions.CenteredFunctions.Defs
import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers
import WqoContinuousFunctions.ScatFun.Operations

import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for CenteredFunctions.Theorems

These lemmas decompose the main theorems from Chapter 4 into smaller, more
focused pieces.
-/

/-!
### Helpers for Fact 4.1 (pgluingOfRegularIsCentered)
-/

-- Note: a zero-stream neighborhood contains a cylinder via `nbhd_basis zeroStream`
-- (`ZeroDimensionalSpaces/Basics.lean`); for `prependZerosOne` heads being zero use
-- `prependZerosOne_head_eq_zero` (`PointedGluing/Defs.lean`).  A regular sequence has
-- arbitrarily large dominating indices via `Preorder.IsRegularSeq.exists_ge` (`BQO/WQO.lean`),
-- strengthened to a strictly monotone dominating reindexing by
-- `Preorder.IsRegularSeq.exists_strictMono_dominating` (`BQO/TwoBQO.lean`).

open ScatFun in
/-- **`0^ω` is a center of `pgl F`, from a local condition.**  To show the base point
`0^ω` is a center for `pgl F`, it suffices to provide, for each block `i` and each open
neighbourhood `V` of `0^ω` *in the gluing domain*, a continuous reduction of `(F i).func`
into `pgl F` whose image stays in `V` and the closure of whose image avoids `0^ω`.

This packages, once and for all, the awkward parts of the `IsCenterFor` case that the
plain `pointedGluing_lower_bound` does not handle: realizing the subspace restriction
`(pgl F)|_V` as a genuine `Set Baire` and transporting the resulting reduction back
along the realization homeomorphism.  Callers only supply the block redirection. -/
lemma pgl_isCenterFor_of_local (F : ℕ → ScatFun)
    (hloc : ∀ (i : ℕ) (V : Set ↥(pgl F).domain), IsOpen V →
        (⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ : ↥(pgl F).domain) ∈ V →
      ∃ (σ : (F i).domain → ↥(pgl F).domain) (τ : Baire → Baire),
        Continuous σ ∧
        (∀ z, (F i).func z = τ ((pgl F).func (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => (pgl F).func (σ z))) ∧
        (∀ z, σ z ∈ V) ∧
        zeroStream ∉ closure (Set.range (fun z => (pgl F).func (σ z)))) :
    IsCenterFor (pgl F).func ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ := by
  intro U hU hzU
  set x₀ : ↥(pgl F).domain := ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ with hx₀
  -- `A_U` : the Baire-realization of `U`; `f_target` : `pgl F` restricted to it.
  set A_U : Set Baire :=
    {x : Baire | ∃ h : x ∈ (pgl F).domain, (⟨x, h⟩ : ↥(pgl F).domain) ∈ U} with hA_U
  set f_target : ↥A_U → Baire :=
    fun z => (pgl F).func ⟨z.val, z.prop.choose⟩ with hf_target
  have hf_target_cont : Continuous f_target :=
    (pgl F).hCont.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hzAU : zeroStream ∈ A_U := ⟨zeroStream_mem_pointedGluingSet _, hzU⟩
  set xb : ↥A_U := ⟨zeroStream, hzAU⟩ with hxb
  have hfxb : f_target xb = zeroStream := by
    simp only [hf_target]; exact pgl_func_zeroStream F _
  -- Inline homeomorphism `↥U ≃ₜ ↥A_U`, with `f_target (e p) = (pgl F).func p.val`.
  let e : ↥U ≃ₜ ↥A_U :=
  { toFun := fun w => ⟨w.val.val, ⟨w.val.prop, w.property⟩⟩
    invFun := fun z => ⟨⟨z.val, z.prop.choose⟩, z.prop.choose_spec⟩
    left_inv := fun w => by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun z => by apply Subtype.ext; rfl
    continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }
  have hfe : ∀ p : ↥U, f_target (e p) = (pgl F).func p.val := fun _ => rfl
  have hCR : ContinuouslyReduces (pgl F).func f_target := by
    obtain ⟨σ0, hσ0, -, τ0, hτ0, heq0⟩ := pointedGluing_lower_bound (A := A_U) f_target
      hf_target_cont (fun i => (F i).domain) (fun _ => (Set.univ : Set Baire)) (pglBlock F) xb (by
    intro i W hW hxW
    -- Push the inner neighbourhood `W ⊆ ↥A_U` to a neighbourhood `V` of `x₀`.
    set V : Set ↥(pgl F).domain := Subtype.val '' (⇑e.symm '' W) with hV
    have hV_open : IsOpen V :=
      hU.isOpenMap_subtype_val _ (e.symm.isOpenMap _ hW)
    have hx₀V : x₀ ∈ V := ⟨e.symm xb, ⟨xb, hxW, rfl⟩, by apply Subtype.ext; rfl⟩
    obtain ⟨σ, τ, hσ, heq, hcont, hmem, hclos⟩ := hloc i V hV_open hx₀V
    have hVU : ∀ p ∈ V, p ∈ U := by rintro p ⟨q, _, rfl⟩; exact q.property
    have hσU : ∀ z, (σ z) ∈ U := fun z => hVU _ (hmem z)
    set σ' : (F i).domain → ↥A_U := fun z => e ⟨σ z, hσU z⟩ with hσ'
    -- `f_target ∘ σ' = (pgl F).func ∘ σ`.
    have hf' : ∀ z, f_target (σ' z) = (pgl F).func (σ z) := fun z => hfe ⟨σ z, hσU z⟩
    have hfun : (fun z => f_target (σ' z)) = (fun z => (pgl F).func (σ z)) := funext hf'
    refine ⟨σ', τ, ?_, ?_, ?_, ?_, ?_⟩
    · exact e.continuous.comp (Continuous.subtype_mk hσ hσU)
    · intro z; show (F i).func z = τ (f_target (σ' z)); rw [hf' z]; exact heq z
    · rw [hfun]; exact hcont
    · -- `σ' z ∈ W`
      intro z
      obtain ⟨q, ⟨a, haW, hae⟩, hqσ⟩ := hmem z
      have : σ' z = a := by
        show e ⟨σ z, hσU z⟩ = a
        rw [show (⟨σ z, hσU z⟩ : ↥U) = q from Subtype.ext hqσ.symm, ← hae,
          e.apply_symm_apply]
      rw [this]; exact haW
    · rw [hfxb, hfun]; exact hclos)
    exact ⟨σ0, hσ0, τ0, hτ0, heq0⟩
  -- Transport along `e`.
  have hres := hCR.comp_homeomorph_right e
  have hgoal : f_target ∘ ⇑e = (pgl F).func ∘ (Subtype.val : ↥U → ↥(pgl F).domain) := by
    funext w; rfl
  rw [hgoal] at hres
  exact hres

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
    (γ : Ordinal) (hx_in : x ∈ CBLevel f γ)
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
    (β : Ordinal) (hne : (CBLevel f β).Nonempty) :
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
    (γ : Ordinal) (hx_in : x ∈ CBLevel f γ) (hy_in : y ∈ CBLevel f γ) :
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
    ∀ α : Ordinal, x ∈ CBLevel f α ∧ y ∈ CBLevel f α := by
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
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x y : A)
    (hx : IsCenterFor f x) (hy : IsCenterFor f y)
    (hne : f x ≠ f y) :
    ¬ ScatteredFun f := by
  -- By definition of scatteredFun, if f is scattered, then its perfect kernel is empty.
  by_contra h_scattered
  have h_perfect_kernel_empty : perfectKernelCB f = ∅ := by
    exact (scattered_iff_empty_perfectKernel f).mp h_scattered;
  exact Set.notMem_empty x ( h_perfect_kernel_empty ▸ Set.mem_iInter.mpr ( fun α => ( centers_in_all_CBLevels f x y hx hy hne ) α |>.1 ) )

/-! If all centers of f have the same image and f is centered,
then f is scattered if and only if f is always scattered (tautological direction
for the backward implication). The key content is that the hypothesis about
centers having the same image is used in the backward direction. wrong formal statement-/
-- lemma cocenter_unique_implies_scattered {A B : Type*}
--     [TopologicalSpace A] [MetrizableSpace A]
--     [TopologicalSpace B] [T2Space B]
--     (f : A → B) (_hf_cent : IsCentered f)
--     (_hcocenter : ∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y)
--     (hf_scat : ScatteredFun f) : ScatteredFun f := hf_scat

/-- **Simple structure of a scattered centered function** (Proposition 4.3, full form).
If `f` is scattered and centered with cocenter `y`, then `CBRank f` is a successor
`α + 1`, the level `CB_α(f)` is nonempty, `CB_{α+1}(f) = ∅`, and `f` is constant equal
to `y` on `CB_α(f)`, in particular `f` is simple.

The rank is a successor because a center belongs to every nonempty CB-level
(`center_in_CBLevel`): it cannot be `0` (the domain is nonempty) nor a limit (else the
center would survive into the empty top level).  Constancy on `CB_α` follows since the
center is `CB_α`-isolated (as `CB_{α+1} = ∅`), so `f` is locally constant there, and
`center_const_on_CBLevel` propagates this to all of `CB_α`. -/
lemma centered_scattered_simple_structure {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf_scat : ScatteredFun f) (hf_cent : IsCentered f)
    (y : B) (hy : ∀ x, IsCenterFor f x → f x = y) :
    ∃ α : Ordinal, CBRank f = Order.succ α ∧ (CBLevel f α).Nonempty ∧
      CBLevel f (Order.succ α) = ∅ ∧ ∀ x ∈ CBLevel f α, f x = y := by
  obtain ⟨c, hc⟩ := hf_cent
  have hfc : f c = y := hy c hc
  have hempty_rank : CBLevel f (CBRank f) = ∅ := cbLevel_at_cbRank_empty f hf_scat
  -- `CBRank f` is a successor `α + 1`.
  obtain ⟨α, hα⟩ : ∃ α, CBRank f = Order.succ α := by
    rcases eq_or_ne (CBRank f) 0 with h0 | h0
    · -- rank `0` ⟹ `CB_0 = univ = ∅`, impossible since `c` is in the domain.
      have hc0 : c ∈ CBLevel f (CBRank f) := by rw [h0, CBLevel_zero]; trivial
      rw [hempty_rank] at hc0; exact hc0.elim
    · by_cases hlim : Order.IsSuccLimit (CBRank f)
      · -- limit rank ⟹ `c` survives into `CB_{rank} = ∅`, impossible.
        have hc_lim : c ∈ CBLevel f (CBRank f) := by
          rw [CBLevel_limit f (CBRank f) hlim]
          exact Set.mem_iInter₂.mpr fun β hβ =>
            center_in_CBLevel f c hc β (CBLevel_nonempty_below_rank f hf_scat β hβ)
        rw [hempty_rank] at hc_lim; exact hc_lim.elim
      · contrapose! hlim
        exact ⟨fun h => h0 h.eq_bot, fun α hα => hlim α hα.succ_eq.symm⟩
  have hne : (CBLevel f α).Nonempty :=
    CBLevel_nonempty_below_rank f hf_scat α (hα ▸ Order.lt_succ α)
  have hempty : CBLevel f (Order.succ α) = ∅ := hα ▸ hempty_rank
  -- `f` is constant `= y` on `CB_α`.
  have hc_α : c ∈ CBLevel f α := center_in_CBLevel f c hc α hne
  have hiso : CBLevel f α ⊆ isolatedLocus f (CBLevel f α) := by
    rw [CBLevel_succ'] at hempty; exact Set.diff_eq_empty.mp hempty
  obtain ⟨-, V, hV_open, hcV, hconst⟩ := hiso hc_α
  refine ⟨α, hα, hne, hα ▸ hempty_rank, fun x hx => ?_⟩
  exact (center_const_on_CBLevel f c hc α hc_α V hV_open hcV hconst x hx).trans hfc

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
    refine isOpen_iff_forall_mem_open.mpr ?_;
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

-- The forward direction `monotone_pgluing_of_centered` (if `f` is centered then
-- `f ≡ pgl_i g_i` for some monotone `(g_i)_i`) was relocated to
-- `CenteredFunctions/LocallyCentered/Theorem.lean`: it needs `ScatFun.rayOn`,
-- `ray_separation` and the keystone `centeredAsPgluing_backward`, all of which live
-- downstream of this file.


/-!
### Helpers for Theorem 4.7 (localCenterednessFromTwoBQO)
-/

/-
Base case: any function with CB-rank 0 is locally centered
(vacuously, since it must be empty or locally constant).
-/
lemma locallyCentered_rank_zero {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (_hf_scat : ScatteredFun f) (hf_rank : CBRank f = 0) :
    IsLocallyCentered f := by
  -- By CBLevel_eq_empty_at_rank (which needs Small.{0} X and ScatteredFun f):
  -- CBLevel f (CBRank f) = ∅.
  have h_empty : CBLevel f (CBRank f) = ∅ := by
    exact CBLevel_eq_empty_at_rank f _hf_scat;
  simp_all +decide [ CBLevel_zero ];
  exact fun x => False.elim ( h_empty.elim x )

/-- `ScatFun` specialization of `locallyCentered_rank_zero`: a `ScatFun` of CB-rank
`0` is locally centered.  The `Small.{0}` instance is automatic since the domain is a
subtype of `Baire : Type 0`. -/
lemma locallyCentered_rank_zero_scatFun (F : ScatFun) (hF_rank : CBRank F.func = 0) :
    IsLocallyCentered F.func :=
  locallyCentered_rank_zero F.func F.hScat hF_rank

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
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ φ.symm ( σ ( φ x ) |>.1 ), by obtain ⟨ y, hy, hy' ⟩ := σ ( φ x ) |>.2; simpa [ ← hy' ] using hy ⟩;
  · fun_prop;
  · refine ⟨ hσ, ?_, ?_ ⟩;
    · refine hτ.mono ?_;
      rintro _ ⟨ x, rfl ⟩ ; simp +decide [ h ] ;
    · grind +suggestions

/-
IsCentered transfers from nested subtypes to flat intersection subtype.
-/
lemma isCentered_subtypeSubtype {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (U : Set X) (_ : IsOpen U) (V : Set U) (_ : IsOpen V) :
    IsCentered ((f ∘ Subtype.val) ∘ (Subtype.val : V → U)) →
    IsCentered (f ∘ (Subtype.val : (U ∩ (Subtype.val '' V) : Set X) → X)) := by
  rintro ⟨ c, hc ⟩;
  refine ⟨ ⟨ c.val.val, ⟨ c.val.prop, ?_ ⟩ ⟩, ?_ ⟩;
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
  refine ⟨ ?_, ?_, ?_ ⟩;
  use fun x => ⟨ ⟨ τ ⟨ ⟨ x.val, by
    exact x.2.1 ⟩, by
    grind ⟩ |>.1 |>.1, by
    grind ⟩, by
    all_goals generalize_proofs at *;
    exact τ ⟨ ⟨ x, by assumption ⟩, by assumption ⟩ |>.2 ⟩
  all_goals generalize_proofs at *;
  · fun_prop (disch := solve_by_elim);
  · use σ;
    refine ⟨ ?_, ?_ ⟩;
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
  refine ⟨ U ∩ ( Subtype.val '' V ), ?_, ?_, ?_ ⟩;
  · obtain ⟨ t, ht₁, ht₂ ⟩ := hV₁;
    convert hU.inter ht₁ using 1 ; ext ; aesop;
  · grind +splitImp;
  · convert isCentered_subtypeSubtype f U hU V hV₁ hV₃


/-
Limit case: if f has limit CB-rank, then f is locally of lower rank,
hence locally centered by induction.
-/
lemma locallyCentered_limit_rank_scatFun
    (F : ScatFun)
    (α : Ordinal.{0}) (hα_limit : Order.IsSuccLimit α) (_hα_ne : α ≠ 0)
    (hF_rank : CBRank F.func = α)
    (ih : ∀ β < α, ∀ (G : ScatFun), CBRank G.func = β → IsLocallyCentered G.func) :
    IsLocallyCentered F.func := by
  intro x
  obtain ⟨U, hU_open, hxU, hU_rank⟩ :=
    limit_locally_lower F.hScat α hF_rank.symm hα_limit x
  have hU_scat : ScatteredFun (F.func ∘ (Subtype.val : ↑U → ↑F.domain)) :=
    scattered_restrict F.func F.hScat U
  have hU_cont : Continuous (F.func ∘ (Subtype.val : ↑U → ↑F.domain)) :=
    F.hCont.comp continuous_subtype_val
  set G : ScatFun := F.restrict U
  have hG_rank : CBRank G.func = CBRank (F.func ∘ (Subtype.val : ↑U → ↑F.domain)) :=
    CBRank_comp_homeomorph (F.restrictEquiv U) (F.func ∘ Subtype.val)
  have hG_lc : IsLocallyCentered G.func :=
    ih _ (hG_rank ▸ hU_rank) G rfl
  have hU_lc : IsLocallyCentered (F.func ∘ (Subtype.val : ↑U → ↑F.domain)) :=
    (IsLocallyCentered_comp_homeomorph (F.restrictEquiv U) (F.func ∘ Subtype.val)).mp hG_lc
  exact isLocallyCentered_restrict_open F.func U hU_open hU_lc x hxU


/-!
### Helpers for Corollary 4.10 (centeredSuccessor)
-/

open ScatFun in
/-- If every block function of `F` acts as the underlying-stream coercion, then so does
the pointed gluing `pgl F`.  (Mirror of `PointedGluingFun_id` for `ScatFun.pgl`.) -/
lemma scatFun_pgl_func_eq_val (F : ℕ → ScatFun)
    (hF : ∀ (i : ℕ) (a : ↥(F i).domain), (F i).func a = (a : ℕ → ℕ))
    (z : ↥(ScatFun.pgl F).domain) :
    (ScatFun.pgl F).func z = (z : ℕ → ℕ) := by
  show PointedGluingFun (fun i => (F i).domain) (fun _ => Set.univ) (ScatFun.pglBlock F) z
      = z.val
  by_cases hz : z.val = zeroStream
  · simp [PointedGluingFun, hz]
  · have h_eq : z.val = prependZerosOne (firstNonzero z.val)
        (stripZerosOne (firstNonzero z.val) z.val) := by
      rcases z.property with h | h
      · exact absurd h hz
      · simp only [Set.mem_iUnion, Set.mem_image] at h
        obtain ⟨i, x, hx, hxe⟩ := h
        rw [← hxe, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
    have hmem : stripZerosOne (firstNonzero z.val) z.val ∈ (F (firstNonzero z.val)).domain :=
      strip_mem_of_pointedGluingSet _ z hz
    unfold PointedGluingFun
    rw [dif_neg hz, dif_pos hmem]
    show prependZerosOne (firstNonzero z.val)
      ((F (firstNonzero z.val)).func ⟨stripZerosOne (firstNonzero z.val) z.val, hmem⟩) = z.val
    rw [hF]
    exact h_eq.symm

open ScatFun in
/-- A constant sequence of `ScatFun`s is regular (it is even monotone). -/
lemma scatFun_const_isRegularSeq (G : ScatFun) :
    Preorder.IsRegularSeq ScatFun.Reduces (fun _ : ℕ => G) :=
  IsMonotoneSeq.isRegularSeq _ (fun _ _ _ => ContinuouslyReduces.refl G.func)

open ScatFun in
/-- A pointed gluing of a regular sequence of `ScatFun`s is centered (at `0^ω`).
This is the `IsCentered` form of `pgluingOfRegularIsCentered`, proved directly via
`pgl_isCenterFor_of_local`. -/
lemma pgl_isCentered_of_regular (F : ℕ → ScatFun)
    (hf_reg : Preorder.IsRegularSeq ScatFun.Reduces F) :
    IsCentered (ScatFun.pgl F).func := by
  refine ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, ?_⟩
  apply pgl_isCenterFor_of_local
  intro i V hV hzV
  obtain ⟨n, hn⟩ :=
    nbhd_basis' (ScatFun.pgl F).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hV hzV
  obtain ⟨j, hjn, hred⟩ := hf_reg.exists_ge i n
  obtain ⟨σ₀, hσ₀cont, τ₀, hτ₀cont, hστ₀⟩ := hred
  set σ : (F i).domain → ↥(ScatFun.pgl F).domain :=
    fun z => ⟨prependZerosOne j (σ₀ z).val,
      prependZerosOne_mem_pointedGluingSet _ j _ (σ₀ z).prop⟩ with hσ
  have hfs : ∀ z, (ScatFun.pgl F).func (σ z) = prependZerosOne j ((F j).func (σ₀ z)) :=
    fun z => ScatFun.pgl_func_block F j (σ₀ z)
  refine ⟨σ, fun y => τ₀ (stripZerosOne j y), ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk
      ((continuous_prependZerosOne j).comp (continuous_subtype_val.comp hσ₀cont)) _
  · intro z
    show (F i).func z = τ₀ (stripZerosOne j ((ScatFun.pgl F).func (σ z)))
    rw [hfs z, stripZerosOne_prependZerosOne]
    exact hστ₀ z
  · apply hτ₀cont.comp (continuous_stripZerosOne j).continuousOn
    rintro _ ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    show ((F j).func ∘ σ₀) z = stripZerosOne j ((ScatFun.pgl F).func (σ z))
    rw [hfs z, stripZerosOne_prependZerosOne]
    rfl
  · intro z
    refine hn ?_
    intro k hk
    exact prependZerosOne_head_eq_zero j _ k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjn)
  · have hCcl : IsClosed {y : Baire | y j = 1} :=
      isClosed_singleton.preimage (continuous_apply j)
    have hsub : Set.range (fun z => (ScatFun.pgl F).func (σ z)) ⊆ {y : Baire | y j = 1} := by
      rintro _ ⟨z, rfl⟩
      simp only [Set.mem_setOf_eq, hfs z]
      exact prependZerosOne_at_i j _
    intro h
    have : zeroStream ∈ {y : Baire | y j = 1} := hCcl.closure_subset_iff.mpr hsub h
    simp [zeroStream] at this

open ScatFun in
/-- Centeredness transport: if a set `S` of streams coincides with the domain of a
pointed gluing `pgl F` of a regular sequence whose blocks act as the stream coercion,
then the coercion `S → (ℕ → ℕ)` is centered. -/
lemma isCentered_val_of_pgl (S : Set (ℕ → ℕ)) (F : ℕ → ScatFun)
    (hreg : Preorder.IsRegularSeq ScatFun.Reduces F)
    (hF : ∀ (i : ℕ) (a : ↥(F i).domain), (F i).func a = (a : ℕ → ℕ))
    (hdom : S = (ScatFun.pgl F).domain) :
    IsCentered (fun (z : ↥S) => (z : ℕ → ℕ)) := by
  have hval : ∀ z : ↥(ScatFun.pgl F).domain, (ScatFun.pgl F).func z = (z : ℕ → ℕ) :=
    scatFun_pgl_func_eq_val F hF
  have hcent : IsCentered (ScatFun.pgl F).func := pgl_isCentered_of_regular F hreg
  let e : ↥S ≃ₜ ↥(ScatFun.pgl F).domain := Homeomorph.setCongr hdom
  have heq : (fun (z : ↥S) => (z : ℕ → ℕ)) = (ScatFun.pgl F).func ∘ e := by
    funext z
    rw [Function.comp_apply, hval (e z)]
    rfl
  rw [heq, IsCentered_comp_homeomorph]
  exact hcent

open ScatFun in
/-- For limit `lam < ω₁`, the cofinal sequence of minimum functions feeding
`MinDom lam` is regular (by monotonicity of `MinFun` and cofinality). -/
lemma minFun_cofinalSeq_isRegularSeq (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) :
    Preorder.IsRegularSeq ScatFun.Reduces
      (fun n => ScatFun.minFun (cofinalSeq lam n)
        (lt_trans (cofinalSeq_lt lam hlim hne n) hlam)) := by
  intro i;
  refine Set.infinite_of_forall_exists_gt ?_;
  intro a
  obtain ⟨b, hb⟩ : ∃ b > a, cofinalSeq lam i ≤ cofinalSeq lam b := by
    have h_cofinal : ∀ β < lam, ∃ n, β ≤ cofinalSeq lam n := by
      exact fun β a => cofinalSeq_eventually_ge lam hlam hlim hne β a
    obtain ⟨ b, hb ⟩ := h_cofinal ( Order.succ ( Finset.sup ( Finset.range ( a + 1 ) ) ( fun k => cofinalSeq lam k ) ⊔ cofinalSeq lam i ) ) ( by
      refine hlim.succ_lt ?_;
      refine max_lt ?_ ?_;
      · induction' a with a ih;
        · simp +decide [ cofinalSeq_lt lam hlim hne ];
        · rw [ Finset.range_add_one, Finset.sup_insert ];
          exact max_lt ( cofinalSeq_lt _ hlim hne _ ) ih;
      · exact cofinalSeq_lt lam hlim hne i );
    refine ⟨ b, ?_, ?_ ⟩;
    · contrapose! hb;
      exact lt_of_le_of_lt ( Finset.le_sup ( f := fun k => cofinalSeq lam k ) ( Finset.mem_range.mpr ( by linarith ) ) ) ( lt_of_le_of_lt ( le_max_left _ _ ) ( Order.lt_succ _ ) );
    · exact le_trans ( le_max_right _ _ ) ( le_trans ( le_of_lt ( Order.lt_succ _ ) ) hb );
  refine ⟨ b, ?_, hb.1 ⟩;
  convert MinFun_monotone ( cofinalSeq lam i ) ( cofinalSeq lam b ) _ _ hb.2 using 1;
  · exact lt_of_le_of_lt ( cofinalSeq_lt lam hlim hne i |> le_of_lt ) hlam;
  · exact lt_of_lt_of_le ( cofinalSeq_lt _ hlim hne _ ) hlam.le

open ScatFun in
/-- The minimum function k_{λ+1} is centered. -/
lemma minFun_isCentered (lam : Ordinal.{0}) (hlam : lam < omega1) :
    IsCentered (MinFun lam) := by
  rcases eq_or_ne lam 0 with h0 | h0
  · subst h0
    refine isCentered_val_of_pgl (MinDom 0) (fun _ => ScatFun.empty)
      (scatFun_const_isRegularSeq _)
      (fun _ a => (Set.notMem_empty a.1 a.2).elim) ?_
    rw [MinDom_zero, ScatFun.pgl_domain]
    rfl
  · by_cases hlim : Order.IsSuccLimit lam
    · refine isCentered_val_of_pgl (MinDom lam)
        (fun n => ScatFun.minFun (cofinalSeq lam n)
          (lt_trans (cofinalSeq_lt lam hlim h0 n) hlam))
        (minFun_cofinalSeq_isRegularSeq lam hlam hlim h0)
        (fun _ a => by rw [ScatFun.minFun_func]; rfl) ?_
      rw [MinDom_limit lam hlim h0, ScatFun.pgl_domain]
      rfl
    · obtain ⟨γ, rfl⟩ : ∃ γ, lam = Order.succ γ := by
        contrapose! hlim
        exact ⟨fun h => h0 h.eq_bot, fun γ hγ => hlim γ hγ.succ_eq.symm⟩
      have hγ : γ < omega1 := lt_trans (Order.lt_succ γ) hlam
      refine isCentered_val_of_pgl (MinDom (Order.succ γ))
        (fun _ => ScatFun.minFun γ hγ)
        (scatFun_const_isRegularSeq _)
        (fun _ a => by rw [ScatFun.minFun_func]; rfl) ?_
      rw [MinDom_succ, ScatFun.pgl_domain]
      rfl

open ScatFun in
/-- The pointed gluing of the max function pgl(ℓ_λ) is centered. -/
lemma pglSuccMaxFun_isCentered (lam : Ordinal.{0}) (hlam : lam < omega1) :
    IsCentered (SuccMaxFun lam) := by
  refine isCentered_val_of_pgl (SuccMaxDom lam) (fun _ => ScatFun.maxFun lam hlam)
    (scatFun_const_isRegularSeq _)
    (fun _ a => by rw [ScatFun.maxFun_func]; rfl) ?_
  rw [ScatFun.pgl_domain]
  rfl

open ScatFun in
/-- `pgl(ℓ_lam)` realised as the function field of the bundled `ScatFun`
`pgl (fun _ => maxFun lam hlam)`. -/
lemma succMaxFun_eq_pgl (lam : Ordinal.{0}) (hlam : lam < omega1) :
    SuccMaxFun lam = (ScatFun.pgl (fun _ => ScatFun.maxFun lam hlam)).func := by
  funext z
  exact (scatFun_pgl_func_eq_val (fun _ => ScatFun.maxFun lam hlam)
    (fun _ a => by rw [ScatFun.maxFun_func]; rfl) z).symm

open ScatFun in
/-- The underlying function of the bundled `ScatFun.succMaxFun lam` is the raw
`SuccMaxFun lam` (both are `pgl ℓ_lam`). -/
@[simp] lemma succMaxFun_func (lam : Ordinal.{0}) (hlam : lam < omega1) :
    (ScatFun.succMaxFun lam hlam).func = SuccMaxFun lam :=
  (succMaxFun_eq_pgl lam hlam).symm

open ScatFun in
/-- `pgl(ℓ_lam)` is scattered. -/
lemma succMaxFun_scattered (lam : Ordinal.{0}) (hlam : lam < omega1) :
    ScatteredFun (SuccMaxFun lam) := by
  rw [succMaxFun_eq_pgl lam hlam]
  exact (ScatFun.pgl (fun _ => ScatFun.maxFun lam hlam)).hScat

open ScatFun in
/-- The CB-level of `ℓ_lam` at its own index `lam` is empty (so `CBRank ≤ lam`). -/
lemma maxFun_cbLevel_self_empty (lam : Ordinal.{0}) (hlam : lam < omega1) :
    CBLevel (MaxFun lam) lam = ∅ := by
  induction' lam using Ordinal.induction with lam ih;
  by_cases hlam_zero : lam = 0;
  · convert Set.eq_empty_of_isEmpty ( MaxDom lam );
    · constructor <;> intro h <;> simp_all +decide [ CBLevel ];
    · exact hlam_zero.symm ▸ by exact ⟨ by simp +decide [ MaxDom ] ⟩ ;
  · by_cases hlam_succ : ∃ β, lam = Order.succ β;
    · obtain ⟨β, rfl⟩ := hlam_succ;
      convert gluingSet_CBLevel_empty ( fun _ => PointedGluingSet ( fun _ => MaxDom β ) ) _ ( Order.succ β ) _ using 1;
      · rw [ show MaxFun ( Order.succ β ) = ( fun x : MaxDom ( Order.succ β ) => ( x : ℕ → ℕ ) ) from rfl ];
        rw [ MaxDom_succ ];
      · convert gluingSet_subtype_val_scattered ( fun _ => PointedGluingSet ( fun _ => MaxDom β ) ) _ using 1;
        exact fun _ => pointedGluingSet_subtype_val_scattered _ ( fun _ => maxfun_is_scatter_leq_α β ( lt_trans ( Order.lt_succ β ) hlam ) |>.1 );
      · intro i
        have h_ind : CBLevel (fun x : PointedGluingSet (fun _ => MaxDom β) => (x : ℕ → ℕ)) (Order.succ β) = ∅ := by
          apply pointedGluingSet_subtype_val_CBLevel_empty;
          exact fun _ => maxfun_is_scatter_leq_α β ( lt_trans ( Order.lt_succ β ) hlam ) |>.1;
          exact fun _ => ih β ( Order.lt_succ β ) ( lt_trans ( Order.lt_succ β ) hlam );
          exact le_rfl
        exact h_ind;
    · obtain ⟨β, hβ⟩ : ∃ β, lam = β ∧ Order.IsSuccLimit β ∧ lam ≠ 0 := by
        simp_all +decide [ Order.IsSuccLimit ];
        exact fun x hx => hlam_succ x <| by rw [ eq_comm ] ; exact CovBy.succ_eq hx;
      -- Apply `gluingSet_CBLevel_empty` at level `lam` with `F := fun n => MaxDom (enumBelow lam n)`.
      have h_gluingSet_CBLevel_empty : CBLevel (fun x : GluingSet (fun n => MaxDom (enumBelow lam n)) => (x.val : ℕ → ℕ)) lam = ∅ := by
        apply gluingSet_CBLevel_empty;
        · apply gluingSet_subtype_val_scattered;
          intro i;
          apply maxfun_is_scatter_leq_α (enumBelow lam i) (lt_trans (enumBelow_lt lam hlam_zero i) hlam) |>.1;
        · intro i
          have h_enum_lt : enumBelow lam i < lam := by
            apply enumBelow_lt lam hlam_zero i
          have h_enum_lt_omega1 : enumBelow lam i < omega1 := by
            exact lt_trans h_enum_lt hlam
          have h_cbLevel_empty : CBLevel (MaxFun (enumBelow lam i)) lam = ∅ := by
            apply (maxfun_is_scatter_leq_α (enumBelow lam i) h_enum_lt_omega1).2 lam h_enum_lt
          exact h_cbLevel_empty;
      unfold MaxFun;
      grind +suggestions

open ScatFun in
/-- `pgl(ℓ_β) = SuccMaxFun β` is the `0`-th block of `ℓ_{β+1} = MaxFun (β+1)`, hence
reduces to it. -/
lemma succMaxFun_le_maxFun_succ (β : Ordinal.{0}) :
    ContinuouslyReduces (SuccMaxFun β) (MaxFun (Order.succ β)) := by
  convert gluingSet_block_reduces ( fun _ => SuccMaxDom β ) 0 using 1;
  · rw [ MaxDom_succ ];
    rfl;
  · congr! 1;
    convert MaxDom_succ β using 1;
  · convert rfl;
    rotate_left;
    exact True;
    exact True.intro;
    simp +decide only [MaxFun, iff_true];
    congr! 1;
    convert MaxDom_succ β using 1

open ScatFun in
/-- The CB-level `lam` of `pgl(ℓ_lam)` is the singleton `{0^ω}`, given that `ℓ_lam` has
CB-rank `lam`.  (Stated with the rank as a hypothesis so that `maxFun_cbRank_eq` can use
it inside its transfinite induction.) -/
lemma succMaxFun_cbLevel_self_singleton (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlam_ne : lam ≠ 0) (hrank : CBRank (MaxFun lam) = lam) :
    CBLevel (SuccMaxFun lam) lam =
      {⟨zeroStream, zeroStream_mem_pointedGluingSet (fun _ => MaxDom lam)⟩} := by
  have := @CBrank_pointedGluing_regular ( fun _ => MaxDom lam ) ( fun _ => Set.univ ) ( fun i x => ⟨ ( ScatFun.maxFun lam hlam ).func x, Set.mem_univ _ ⟩ ) ?_ ( fun _ => lam ) ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
  convert this;
  convert succMaxFun_eq_pgl lam hlam;
  · convert ( ScatFun.maxFun lam hlam ).hScat using 1;
  · exact fun m => ⟨ m + 1, Nat.lt_succ_self _, le_rfl ⟩;
  · convert hrank using 1;
  · rfl;
  · exact pos_of_ne_zero hlam_ne

open ScatFun in
/-- The maximum function `ℓ_lam` has CB-rank exactly `lam`. -/
lemma maxFun_cbRank_eq (lam : Ordinal.{0}) (hlam : lam < omega1) :
    CBRank (MaxFun lam) = lam := by
  have key : ∀ l : Ordinal.{0}, l < omega1 → CBRank (MaxFun l) = l := by
    intro l
    induction l using Ordinal.induction with
    | _ l ih =>
    intro hl
    refine le_antisymm
      (CBRank_le_of_CBLevel_empty _ _ (maxFun_cbLevel_self_empty l hl)) ?_
    refine le_of_not_gt fun h => ?_
    obtain ⟨β, hβ₁, hβ₂⟩ : ∃ β < l, CBLevel (MaxFun l) β = ∅ :=
      ⟨CBRank (MaxFun l), h,
        CBLevel_eq_empty_at_rank (MaxFun l) (maxfun_is_scatter_leq_α l hl).1⟩
    have hβω : β < omega1 := lt_trans hβ₁ hl
    have h_red : ContinuouslyReduces (SuccMaxFun β) (MaxFun l) :=
      (succMaxFun_le_maxFun_succ β).trans
        (MaxFun_monotone (Order.succ β) l (lt_of_le_of_lt (Order.succ_le_of_lt hβ₁) hl)
          hl (Order.succ_le_of_lt hβ₁))
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := h_red
    have h_sub : σ '' (CBLevel (SuccMaxFun β) β) ⊆ CBLevel (MaxFun l) β :=
      ContinuouslyReduces.cb_monotone hσ heq β
    have h_ne : (CBLevel (SuccMaxFun β) β).Nonempty := by
      rcases eq_or_ne β 0 with hβ0 | hβ0
      · subst hβ0
        rw [CBLevel_zero]
        exact ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, Set.mem_univ _⟩
      · exact (succMaxFun_cbLevel_self_singleton β hβω hβ0 (ih β hβ₁ hβω)).symm ▸
          Set.singleton_nonempty _
    obtain ⟨y, hy⟩ := h_ne
    exact Set.notMem_empty _ (hβ₂ ▸ h_sub (Set.mem_image_of_mem σ hy))
  exact key lam hlam

open ScatFun in
/-- `0^ω` lies in the CB-level `lam` of `pgl(ℓ_lam)`; in particular that level is
nonempty (so `pgl(ℓ_lam)` has CB-rank `lam + 1`). -/
lemma pglMaxFun_cbLevel_lam_nonempty (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlam_ne : lam ≠ 0) :
    (CBLevel (SuccMaxFun lam) lam).Nonempty :=
  (succMaxFun_cbLevel_self_singleton lam hlam hlam_ne (maxFun_cbRank_eq lam hlam)).symm ▸
    Set.singleton_nonempty _

open ScatFun in
/-- `k_{lam+1} = MinFun lam` reduces to `pgl(ℓ_lam) = SuccMaxFun lam` (minimality). -/
lemma minFun_le_pglMaxFun (lam : Ordinal.{0}) (hlam : lam < omega1) (hlam_ne : lam ≠ 0) :
    ContinuouslyReduces (MinFun lam) (SuccMaxFun lam) :=
  minFun_is_minimum lam hlam (SuccMaxDom lam) (SuccMaxFun lam) continuous_subtype_val
    (succMaxFun_scattered lam hlam) (pglMaxFun_cbLevel_lam_nonempty lam hlam hlam_ne)

-- NB: the two conclusion lemmas of Corollary 4.10 — `pglMaxFun_not_le_minFunPlusOne`
-- (strict non-reduction) and `minFun_lt_pglMaxFun` (the packaged strict inequality) —
-- live in `CenteredFunctions/Theorems.lean`, not here: their proof needs the
-- cocenter-rigidity results of Proposition 4.4 (`rigidityOfCocenter_*`), which are
-- defined there.  All the supporting facts above (`maxFun_cbRank_eq`,
-- `minFun_le_pglMaxFun`, …) are imported by that file.

end
