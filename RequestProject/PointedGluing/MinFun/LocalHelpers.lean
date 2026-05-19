import RequestProject.PointedGluing.Theorems
import RequestProject.PointedGluing.Defs
import RequestProject.BaireSpace.GenRedProp
-- import RequestProject.PointedGluing.LowerBoundLemma
import RequestProject.PrelimMemo.Scattered.Decomposition
import RequestProject.PointedGluing.MaxFun.Helpers
import RequestProject.PointedGluing.MinFun.Helpers
import RequestProject.PointedGluing.MinFun.LowerBound

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for minFun_local_condition'
-/

/-- Given sup of ray CB ranks equals α and β < α, there exists N with ray CB rank > β. -/
lemma exists_ray_cbrank_gt
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
    (α : Ordinal.{0})
    (y : ℕ → ℕ) (_hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (_hlevel_ne : (CBLevel f α).Nonempty)
    (β : Ordinal.{0}) (hβ : β < α)
    (B : Set (ℕ → ℕ)) (_hfB : ∀ a : A, f a ∈ B)
    (hsup : ⨆ n, CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) = α) :
    ∃ N, CBRank (fun (x : {a : A | f a ∈ RaySet B y N}) => f x.val) > β := by
  contrapose! hβ
  exact hsup ▸ ciSup_le hβ

/-- A point in a ray of a simple function has exit ordinal < α. -/
lemma exit_ordinal_of_ray_point
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (α : Ordinal.{0})
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (_hlevel_succ_empty : CBLevel f (Order.succ α) = ∅)
    (N : ℕ) (B : Set (ℕ → ℕ))
    (p : A) (hp_ray : f p ∈ RaySet B y N)
    (β' : Ordinal.{0})
    (hp_cb : p ∈ CBLevel f β')
    (_hβα : β' ≤ α) :
    ∃ γ : Ordinal.{0}, β' ≤ γ ∧ γ < α ∧ p ∈ CBLevel f γ ∧ p ∉ CBLevel f (Order.succ γ) := by
  obtain ⟨γ, hγ_lt, hγ_in, hγ_out⟩ : ∃ γ, γ < α ∧ p ∈ CBLevel f γ ∧ p ∉ CBLevel f (Order.succ γ) := by
    apply exit_ordinal_is_successor
    intro h; specialize hy_simple p h; simp_all +decide [RaySet]
  refine ⟨γ, ?_, hγ_lt, hγ_in, hγ_out⟩
  contrapose! hγ_out
  exact CBLevel_antitone f (Order.succ_le_of_lt hγ_out) hp_cb

/-- If f|_{A ∩ W₁} is simple and W₂ ⊆ W₁ is clopen with
    a point of the right CB level, then f|_{A ∩ W₂} is also simple. -/
lemma simple_restrict_clopen
    (A : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ)
    (hscat : ScatteredFun f)
    (W₁ W₂ : Set (ℕ → ℕ)) (hW₂₁ : W₂ ⊆ W₁) (hW₂_clopen : IsClopen W₂)
    (γ : Ordinal.{0})
    (hW₁_ne : ∃ a : A, a.val ∈ W₂ ∧ a ∈ CBLevel f γ)
    (hW₁_empty : CBLevel f (Order.succ γ) ∩ (Subtype.val ⁻¹' W₁ : Set A) = ∅)
    (hW₁_const : ∃ c : ℕ → ℕ, ∀ a ∈ (Subtype.val ⁻¹' W₁ : Set A) ∩ CBLevel f γ, f a = c) :
    SimpleFun (f ∘ (Subtype.val : {a : A | a.val ∈ W₂} → A)) := by
  convert restriction_to_clopen_is_simple f hscat γ W₂ hW₂_clopen ?_ ?_ ?_ using 1
  · exact hW₁_ne
  · exact Set.eq_empty_of_forall_notMem fun x hx => hW₁_empty.subset ⟨hx.1, hW₂₁ hx.2⟩
  · exact ⟨hW₁_const.choose, fun z hz => hW₁_const.choose_spec z ⟨hW₂₁ hz.1, hz.2⟩⟩

/--
Compose a reduction MinFun β ≤ f|_S (where S ⊆ A is a subtype)
    to produce σ : MinDom β → A with σ mapping into U and separation.
-/
lemma compose_reduction_from_subtype
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ)
    (β : Ordinal.{0})
    (S : Set A)
    (hred : ContinuouslyReduces (MinFun β) (f ∘ (Subtype.val : S → A)))
    (U : Set A) (hS_U : S ⊆ U)
    (C : Set (ℕ → ℕ)) (hC_closed : IsClosed C)
    (hS_C : ∀ a : S, f a.val ∈ C)
    (x : A) (hx_notC : f x ∉ C) :
    ∃ (σ : MinDom β → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      Continuous σ ∧
      (∀ z : MinDom β, (z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ U) ∧
      f x ∉ closure (Set.range (fun z => f (σ z))) := by
  -- From hred, extract σ₀ : MinDom β → S and τ₀ with Continuous σ₀, z.val = τ₀ ((f ∘ Subtype.val) (σ₀ z)), and ContinuousOn τ₀ on the range.
  obtain ⟨σ₀, τ₀, hσ₀_cont, hτ₀_eq, hτ₀_cont⟩ := hred
  refine ⟨fun z => (σ₀ z).val, hσ₀_cont, ?_, ?_, hτ₀_eq, ?_, ?_⟩
  · fun_prop
  · convert hτ₀_cont using 1
  · exact fun z => hS_U <| σ₀ z |>.2
  · exact fun h => hx_notC <| hC_closed.closure_subset_iff.mpr (Set.range_subset_iff.mpr fun z => hS_C _) h

/-
Removed sup_ray_cb_eq_alpha_restricted, using flat Set (ℕ → ℕ) approach instead

Given f : A → ℕ → ℕ simple at α with β < α, open V ∋ x.val, x ∈ CBLevel f α,
    find a point p ∈ A with:
    (1) p.val ∈ V
    (2) p ∈ CBLevel f γ for some β ≤ γ < α
    (3) p ∉ CBLevel f (succ γ)
    (4) f p N ≠ y N for some N
-/
lemma find_ray_point
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) (hf : Continuous f) (hscat : ScatteredFun f)
    (α : Ordinal.{0}) (_hα : α < omega1)
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (_hlevel_ne : (CBLevel f α).Nonempty)
    (hlevel_succ_empty : CBLevel f (Order.succ α) = ∅)
    (x : A) (hx : x ∈ CBLevel f α)
    (β : Ordinal.{0}) (hβ : β < α)
    (V : Set (ℕ → ℕ)) (hV : IsOpen V) (hxV : x.val ∈ V) :
    ∃ (p : A) (γ : Ordinal.{0}) (N : ℕ),
      p.val ∈ V ∧ p ∈ CBLevel f γ ∧ p ∉ CBLevel f (Order.succ γ) ∧
      β ≤ γ ∧ γ < α ∧ f p N ≠ y N := by
  -- Work with A' = A ∩ V : Set (ℕ → ℕ) and g = f ∘ inclusion
  set A' : Set (ℕ → ℕ) := A ∩ V
  have hA'_sub : A' ⊆ A := Set.inter_subset_left
  let g : A' → ℕ → ℕ := f ∘ Set.inclusion hA'_sub
  have hg_cont : Continuous g := hf.comp (continuous_inclusion hA'_sub)
  have hg_scat : ScatteredFun g := by
    intro S hS
    obtain ⟨U, hU, hU_ne, hU_const⟩ := hscat (Set.inclusion hA'_sub '' S) (hS.image _)
    refine ⟨Set.inclusion hA'_sub ⁻¹' U, hU.preimage (continuous_inclusion hA'_sub), ?_, ?_⟩
    · obtain ⟨z, hzU, w, hwS, rfl⟩ := hU_ne
      exact ⟨w, hzU, hwS⟩
    · intro a ha b hb; exact hU_const _ ⟨ha.1, _, ha.2, rfl⟩ _ ⟨hb.1, _, hb.2, rfl⟩
  have hx_A' : x.val ∈ A' := ⟨x.prop, hxV⟩
  -- The map ι from A' to A (as Set (ℕ → ℕ) subtypes)
  -- Relating CBLevel g to CBLevel f:
  -- Since A' = A ∩ V is homeomorphic to {a : ↑A | a.val ∈ V} as a subspace of ℕ → ℕ,
  -- CBLevel g β at ⟨z, ⟨hz_A, hz_V⟩⟩ iff CBLevel f β at ⟨z, hz_A⟩.
  -- This follows from CBLevel_open_restrict applied to f and S = val⁻¹(V).
  have cb_transfer : ∀ (β' : Ordinal.{0}) (z : ℕ → ℕ) (hz : z ∈ A'),
      ⟨z, hz⟩ ∈ CBLevel g β' ↔ ⟨z, hz.1⟩ ∈ CBLevel f β' := by
    -- By induction on β', we can show that the CBLevel of g at β' is equal to the preimage of the CBLevel of f at β' under the inclusion map.
    intro β' z hz_A'
    induction' β' using Ordinal.induction with β' ih generalizing z
    rw [CBLevel, CBLevel]
    induction' β' using Ordinal.limitRecOn with β' ih generalizing z
    · simp +decide [Ordinal.limitRecOn]
    · simp +decide [Ordinal.limitRecOn_succ]
      constructor <;> rintro ⟨h₁, h₂⟩
      · refine ⟨?_, ?_⟩
        · convert ih β' (Order.lt_succ β') z hz_A' |>.1 h₁ using 1
        · contrapose! h₂
          obtain ⟨U, hU_open, hU_z, hU_isolated⟩ := h₂
          refine ⟨?_, ?_, ?_⟩
          exact h₁
          exact { y : A' | ⟨y.val, y.property.1⟩ ∈ hU_open }
          refine ⟨?_, ?_, ?_⟩
          · exact hU_z.preimage (continuous_subtype_val.subtype_mk fun x => x.2.1)
          · exact hU_isolated.1
          · simp +zetaDelta at *
            grind
      · refine ⟨?_, ?_⟩
        · convert ih β' (Order.lt_succ β') z hz_A' |>.2 h₁ using 1
        · contrapose! h₂
          obtain ⟨U, hU₁, hU₂⟩ := h₂
          refine ⟨?_, ?_, ?_⟩
          exact h₁
          exact { y : A | ∃ x : A', x ∈ hU₁ ∧ y = x.val }
          refine ⟨?_, ?_, ?_⟩
          · obtain ⟨t, ht₁, ht₂⟩ := hU₂.1
            use t ∩ V
            simp +decide [← ht₂, Set.ext_iff]
            exact ⟨ht₁.inter hV, fun a ha ha' => ⟨fun ha'' => ⟨ha, ha''⟩, fun ha'' => ha''.2⟩⟩
          · exact ⟨_, hU₂.2.1, rfl⟩
          · simp +zetaDelta at *
            grind
    · rename_i o ho ih'
      simp +decide [ho, Ordinal.limitRecOn_limit]
      constructor <;> intro h i hi
      · convert ih i hi z hz_A' |>.1 (h i hi) using 1
      · exact ih' i hi (fun k hk => ih k (lt_trans hk hi)) z hz_A' |>.2 (h i hi)
  -- CBLevel g α nonempty
  have hg_ne : (CBLevel g α).Nonempty :=
    ⟨⟨x.val, hx_A'⟩, (cb_transfer α x.val hx_A').mpr hx⟩
  -- g constant on CBLevel g α
  have hg_simple : ∀ z ∈ CBLevel g α, g z = y := by
    intro ⟨z, hz⟩ h
    exact hy_simple ⟨z, hz.1⟩ ((cb_transfer α z hz).mp h)
  -- sup of ray CB ranks of g = α
  have hsup : ⨆ n, CBRank (fun (q : {a : A' | g a ∈ RaySet Set.univ y n}) => g q.val) = α :=
    sup_ray_cb_eq_alpha g (fun _ => mem_univ _) hg_cont hg_scat α hg_ne y hg_simple
      (fun n => CBRank (fun (q : {a : A' | g a ∈ RaySet Set.univ y n}) => g q.val))
      (fun _ => rfl) (fun n => ray_cb_le_alpha g hg_cont α y hg_simple n)
  -- Find N with ray CBRank > β
  have hN : ∃ N, CBRank (fun (q : {a : A' | g a ∈ RaySet Set.univ y N}) => g q.val) > β := by
    contrapose! hβ; exact hsup ▸ ciSup_le hβ
  obtain ⟨N, hN⟩ := hN
  -- Get point in ray's CBLevel β
  have hray_scat : ScatteredFun (fun (q : {a : A' | g a ∈ RaySet Set.univ y N}) => g q.val) :=
    scattered_restrict g hg_scat _
  obtain ⟨q, hq⟩ := CBLevel_nonempty_below_rank
    (fun (q : {a : A' | g a ∈ RaySet Set.univ y N}) => g q.val) hray_scat β hN
  -- q.val : A', q.val.val : ℕ → ℕ
  set p : A := ⟨q.val.val, q.val.prop.1⟩
  -- p.val ∈ V
  have hpV : p.val ∈ V := q.val.prop.2
  -- f p N ≠ y N (from RaySet condition)
  have hpN : f p N ≠ y N := by
    have := q.prop; simp only [RaySet, Set.mem_univ, true_and] at this
    exact this.2
  -- p ∈ CBLevel f β
  have hp_cb : p ∈ CBLevel f β := by
    have hray_open : IsOpen ({a : A' | g a ∈ RaySet Set.univ y N} : Set A') :=
      ray_subtype_isOpen A' Set.univ g (fun _ => mem_univ _) hg_cont y N
    have hq_in_g : q.val ∈ CBLevel g β :=
      (CBLevel_open_restrict g _ hray_open β q).mp hq
    exact (cb_transfer β q.val.val q.val.prop).mp hq_in_g
  -- f p ∈ RaySet Set.univ y N
  have hp_ray : f p ∈ RaySet Set.univ y N := by
    have := q.prop; simp only [g, Function.comp, Set.inclusion] at this
    simp only [RaySet, Set.mem_univ, true_and]
    exact ⟨by intro k hk; have := q.prop; simp [RaySet] at this; exact this.1 k hk, hpN⟩
  -- Apply exit_ordinal_of_ray_point
  obtain ⟨γ, hγβ, hγα, hγ_in, hγ_out⟩ :=
    exit_ordinal_of_ray_point f α y hy_simple hlevel_succ_empty N Set.univ p
      hp_ray β hp_cb (le_of_lt hβ)
  exact ⟨p, γ, N, hpV, hγ_in, hγ_out, hγβ, hγα, hpN⟩

/--
Given a point p with exit ordinal γ in f, produce a clopen neighborhood W
    such that f|_{A ∩ W} is simple at γ, W ⊆ V, and f differs from y at coordinate N on A ∩ W.
-/
lemma decompose_at_point
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) (hf : Continuous f) (hscat : ScatteredFun f)
    (p : A) (γ : Ordinal.{0}) (N : ℕ)
    (hp_cb : p ∈ CBLevel f γ) (hp_exit : p ∉ CBLevel f (Order.succ γ))
    (y : ℕ → ℕ)
    (hp_ray : f p N ≠ y N)
    (V : Set (ℕ → ℕ)) (hV : IsOpen V) (hpV : p.val ∈ V) :
    ∃ (W : Set (ℕ → ℕ)),
      IsClopen W ∧ p.val ∈ W ∧ W ⊆ V ∧
      SimpleFun (f ∘ (Subtype.val : {a : A | a.val ∈ W} → A)) ∧
      (∀ a : A, a.val ∈ W → f a N ≠ y N) := by
  obtain ⟨W₁, hW₁_clopen, hpW₁, hW₁⟩ : ∃ W₁ : Set (ℕ → ℕ), IsClopen W₁ ∧ p.val ∈ W₁ ∧ SimpleFun (f ∘ (Subtype.val : {a : A | a.val ∈ W₁} → A)) ∧ CBLevel f (Order.succ γ) ∩ (Subtype.val ⁻¹' W₁ : Set A) = ∅ ∧ ∃ c : ℕ → ℕ, ∀ a ∈ (Subtype.val ⁻¹' W₁ : Set A) ∩ CBLevel f γ, f a = c := by
    obtain ⟨U, hU⟩ : ∃ U : Set (ℕ → ℕ), IsOpen U ∧ p.val ∈ U ∧ CBLevel f (Order.succ γ) ∩ (Subtype.val ⁻¹' U : Set A) = ∅ ∧ ∃ c : ℕ → ℕ, ∀ a ∈ (Subtype.val ⁻¹' U : Set A) ∩ CBLevel f γ, f a = c := by
      have h_isolated : p ∈ isolatedLocus f (CBLevel f γ) := by
        grind +suggestions
      obtain ⟨U, hU₁, hU₂, hU₃, hU₄⟩ := isolatedLocus_gives_simple_neighborhood γ p h_isolated
      obtain ⟨V, hV₁, hV₂⟩ := hU₁; use V; aesop
    obtain ⟨W₁, hW₁_clopen, hpW₁⟩ : ∃ W₁ : Set (ℕ → ℕ), IsClopen W₁ ∧ p.val ∈ W₁ ∧ W₁ ⊆ U := by
      have := baire_exists_clopen_subset_of_open p.val U hU.1 hU.2.1; aesop
    refine ⟨W₁, hW₁_clopen, hpW₁.1, ?_, ?_, ?_⟩
    · grind +suggestions
    · exact Set.eq_empty_of_forall_notMem fun x hx => hU.2.2.1.subset ⟨hx.1, hpW₁.2 hx.2⟩
    · exact ⟨hU.2.2.2.choose, fun a ha => hU.2.2.2.choose_spec a ⟨hpW₁.2 ha.1, ha.2⟩⟩
  have h_open : IsOpen {a : A | f a N ≠ y N} := by
    exact isOpen_ne.preimage (show Continuous fun a : A => f a N from continuous_apply N |> Continuous.comp <| hf)
  obtain ⟨O', hO'_open, hpO', hO'⟩ : ∃ O' : Set (ℕ → ℕ), IsOpen O' ∧ p.val ∈ O' ∧ ∀ a : A, a.val ∈ O' → f a N ≠ y N := by
    have := h_open.mem_nhds hp_ray
    rw [mem_nhds_subtype] at this
    rcases this with ⟨u, hu, hu'⟩ ; rcases mem_nhds_iff.mp hu with ⟨v, hv₁, hv₂, hv₃⟩ ; use v; aesop
  obtain ⟨W, hW_clopen, hpW, hW⟩ : ∃ W : Set (ℕ → ℕ), IsClopen W ∧ p.val ∈ W ∧ W ⊆ V ∩ W₁ ∩ O' := by
    have := baire_exists_clopen_subset_of_open p.val (V ∩ W₁ ∩ O') ?_ ?_
    · exact this
    · exact IsOpen.inter (IsOpen.inter hV hW₁_clopen.isOpen) hO'_open
    · aesop
  refine ⟨W, hW_clopen, hpW, fun x hx => hW hx |>.1 |>.1, ?_, ?_⟩
  · apply_rules [simple_restrict_clopen]
    · exact ⟨p, hpW, hp_cb⟩
    · grind
    · exact ⟨hW₁.2.2.choose, fun a ha => hW₁.2.2.choose_spec a ⟨by aesop, ha.2⟩⟩
  · exact fun a ha => hO' a <| hW ha |>.2

end
