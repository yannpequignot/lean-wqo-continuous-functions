import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.PointedGluing.Defs
open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for CBrank_regular_simple (Proposition 3.8)
-/

lemma RaySet_cond_isOpen (y : ℕ → ℕ) (n : ℕ) :
    IsOpen {x : ℕ → ℕ | (∀ k, k < n → x k = y k) ∧ x n ≠ y n} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ⟨{z | ∀ k ≤ n, z k = x k}, ?_, ?_, fun k hk => rfl⟩
  · grind
  · rw [isOpen_pi_iff]; intro f hf; use Finset.Iic n; use fun k => {z | z = x k}; aesop

lemma ray_subtype_isOpen (A : Set (ℕ → ℕ)) (B : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f) (y : ℕ → ℕ) (n : ℕ) :
    IsOpen ({a : A | f a ∈ RaySet B y n} : Set A) := by
  unfold RaySet; convert RaySet_cond_isOpen y n |>.preimage hf using 1; aesop

lemma RaySet_subtype_eq_preimage (A : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) :
    (Subtype.val ⁻¹' RaySet Set.univ y n : Set A) = Subtype.val ⁻¹' RaySet A y n := by
  ext ⟨x, hx⟩; simp [RaySet]

lemma ray_subtype_isOpen' (A : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) :
    IsOpen (Subtype.val ⁻¹' RaySet A y n : Set A) := by
  rw [← RaySet_subtype_eq_preimage]
  exact ray_subtype_isOpen A Set.univ Subtype.val (fun a => Set.mem_univ a.val)
    continuous_subtype_val y n

lemma mem_ray_or_eq_y {B : Set (ℕ → ℕ)} {y x : ℕ → ℕ} (hx : x ∈ B) :
    x = y ∨ ∃ n, x ∈ RaySet B y n := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr ⟨Nat.find (Function.ne_iff.mp hxy),
      hx, fun k hk => Classical.not_not.1 fun h => Nat.find_min (Function.ne_iff.mp hxy) hk h,
      Nat.find_spec (Function.ne_iff.mp hxy)⟩

lemma CBRank_le_of_CBLevel_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal.{0}) (h : CBLevel f α = ∅) : CBRank f ≤ α := by
  refine csInf_le' ?_; simp +decide [h, CBLevel_succ']

lemma ray_CBLevel_alpha_empty {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (_hf : Continuous f) (α : Ordinal.{0})
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y) (n : ℕ) :
    CBLevel (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) α = ∅ := by
  contrapose! hy_simple; simp_all +decide [CBLevel]
  obtain ⟨x, hx⟩ := hy_simple
  refine ⟨x.1, x.1.2, ?_, fun h => x.2.2.2 <| by simp [h]⟩
  induction' α using Ordinal.limitRecOn with α ih generalizing x <;> simp_all +decide [Ordinal.limitRecOn]
  · exact ⟨ih _ x.1.2 x.2 hx.1, fun h => hx.2 <| by
      obtain ⟨U, hU₁, hU₂, hU₃⟩ := h
      exact ⟨hx.1, {y : {x : A // f x ∈ RaySet B y n} | y.val ∈ hU₁},
        ⟨hU₂.preimage continuous_subtype_val, hU₃.1, fun y hy => hU₃.2 _ <| by aesop⟩⟩⟩
  · grind

lemma ray_cb_le_alpha {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f) (α : Ordinal.{0})
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y) (n : ℕ) :
    CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ α :=
  CBRank_le_of_CBLevel_empty _ _ (ray_CBLevel_alpha_empty f hf α y hy_simple n)

lemma CBLevel_all_rays_le_implies_const {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f) (y : ℕ → ℕ) (β : Ordinal.{0})
    (hray_le : ∀ n, CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β) :
    ∀ x ∈ CBLevel f β, f x = y := by
  intro x hx
  have h_ray_empty : ∀ n, CBLevel (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) β = ∅ := by
    intro n
    exact Set.eq_empty_of_forall_notMem fun x hx => by
      have := CBLevel_antitone (fun x : {a : A | f a ∈ RaySet B y n} => f x.val) (hray_le n) hx
      exact (CBLevel_eq_empty_at_rank _ (scattered_restrict f hf_scat _)).subset this
  contrapose! h_ray_empty
  obtain ⟨n, hn⟩ := mem_ray_or_eq_y (hfB x) |>.resolve_left h_ray_empty
  exact ⟨n, ⟨⟨x, hn⟩, CBLevel_open_restrict f _ (ray_subtype_isOpen A B f hfB hf y n) _ _ |>.2 hx⟩⟩

lemma CBLevel_const_succ_empty {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (β : Ordinal.{0})
    (hconst : ∀ x ∈ CBLevel f β, ∀ x' ∈ CBLevel f β, f x = f x') :
    CBLevel f (Order.succ β) = ∅ := by
  rw [CBLevel_succ']
  exact Set.diff_eq_empty.mpr fun x hx =>
    ⟨hx, Set.univ, isOpen_univ, trivial, fun y hy => hconst y hy.2 x hx⟩

lemma sup_ray_cb_eq_alpha {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f) (α : Ordinal.{0})
    (hcb_ne : (CBLevel f α).Nonempty) (y : ℕ → ℕ)
    (_hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (ray_cb : ℕ → Ordinal.{0})
    (hray_cb : ∀ n, ray_cb n = CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val))
    (hray_le : ∀ n, ray_cb n ≤ α) :
    ⨆ n, ray_cb n = α := by
  contrapose! hcb_ne
  obtain ⟨β, hβ⟩ : ∃ β : Ordinal.{0}, β < α ∧ ∀ n, ray_cb n ≤ β :=
    ⟨⨆ n, ray_cb n, lt_of_le_of_ne (ciSup_le hray_le) hcb_ne,
     fun n => le_ciSup (Ordinal.bddAbove_range ray_cb) n⟩
  have h_const : ∀ x ∈ CBLevel f β, f x = y := by
    apply CBLevel_all_rays_le_implies_const f hfB hf hf_scat y β; aesop
  exact Set.eq_empty_of_forall_notMem fun x hx => by
    have := CBLevel_antitone f (Order.succ_le_of_lt hβ.1) hx
    exact (CBLevel_const_succ_empty f β fun x hx x' hx' => h_const x hx ▸ h_const x' hx' ▸ rfl).subset this

lemma regularity_contradiction {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f) (α : Ordinal.{0})
    (y : ℕ → ℕ) (_hy : y ∈ B) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (m : ℕ) (β : Ordinal.{0}) (hβα : β < α)
    (hbound : ∀ n, n > m → CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β)
    (_hle : ∀ n, CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ α) :
    CBLevel f α = ∅ := by
  set T := {a : A | ∀ k ≤ m, f a k = y k}
  have hT_open : IsOpen T := by
    convert isOpen_biInter_finset (s := Finset.range (m + 1)) fun k hk =>
      (isOpen_discrete {y k}).preimage (show Continuous fun a : A => f a k from
        (continuous_apply k).comp hf) using 1
    ext; simp [T, Finset.mem_range]
  have hT_const : ∀ x : T, x.val ∈ CBLevel f β → f x.val = y := by
    intro x hx
    by_cases h : ∃ n, f x.val ∈ RaySet B y n
    · obtain ⟨n, hn⟩ := h
      by_cases hn' : n ≤ m
      · exact absurd (x.2 n hn') (by have := hn.2; aesop)
      · have h_ray_empty : CBLevel (fun x : {a : A | f a ∈ RaySet B y n} => f x.val) β = ∅ := by
          have h1 := CBLevel_eq_empty_at_rank (fun x : {a : A | f a ∈ RaySet B y n} => f x.val) (scattered_restrict _ hf_scat _)
          exact h1 ▸ Set.Subset.antisymm (fun x hx => CBLevel_antitone _ (hbound n (not_le.mp hn')) hx)
              (fun x hx => by grind)
        exact False.elim (h_ray_empty.subset
          (CBLevel_open_restrict (fun x => f x) _ (ray_subtype_isOpen A B f hfB hf y n) β
            ⟨x.val, hn⟩ |>.2 hx))
    · exact Or.resolve_right (mem_ray_or_eq_y (hfB x)) h
  have hT_succ_empty : CBLevel (fun x : T => f x.val) (Order.succ β) = ∅ :=
    CBLevel_const_succ_empty _ _ fun x hx x' hx' =>
      hT_const x (CBLevel_open_restrict _ _ hT_open β x |>.1 hx) ▸
        hT_const x' (CBLevel_open_restrict f T hT_open β x' |>.1 hx') ▸ rfl
  have hT_alpha_empty : CBLevel (fun x : T => f x.val) α = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => by
      have := CBLevel_antitone (fun x : T => f x.val) (Order.succ_le_of_lt hβα); aesop
  have hT_inter_empty : T ∩ CBLevel f α = ∅ := by
    exact Set.eq_empty_of_forall_notMem fun x hx =>
      hT_alpha_empty.subset ((CBLevel_open_restrict _ _ hT_open _ ⟨x, hx.1⟩).2 hx.2)
  exact Set.eq_empty_of_forall_notMem fun x hx =>
    Set.eq_empty_iff_forall_notMem.mp hT_inter_empty x
      ⟨fun k hk => hy_simple x hx ▸ rfl, hx⟩

end
