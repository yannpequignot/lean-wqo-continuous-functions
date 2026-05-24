import WqoContinuousFunctions.PointedGluing.SelfSimilarity
import WqoContinuousFunctions.ContinuousReducibility.Gluing.UpperBound

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section



/-- If every point of A has a clopen neighborhood in A where f reduces to MaxFun α,
    then f globally reduces to MaxFun α. -/
lemma locally_reduces_to_maxfun_implies_reduces
    (α : Ordinal.{0}) (hα : α < omega1)
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hloc : ∀ x : A, ∃ C : Set A, IsClopen C ∧ x ∈ C ∧
        ContinuouslyReduces (fun a : C => f a.val) (MaxFun α)) :
    ContinuouslyReduces f (MaxFun α) := by
  -- Extract clopen cover and reductions
  obtain ⟨S, hS⟩ : ∃ S : Set A, S.Countable ∧ ⋃ x ∈ S, (Classical.choose (hloc x)) = Set.univ := by
    have h_lindelof : IsLindelof (Set.univ : Set A) := by
      exact isLindelof_univ
    have := h_lindelof.elim_nhds_subcover (fun x => Classical.choose (hloc x)) fun x _ => Classical.choose_spec (hloc x) |>.1.2.mem_nhds (Classical.choose_spec (hloc x) |>.2.1) ; aesop
  have := hS.1.exists_eq_range
  by_cases hS_empty : S = ∅ <;> simp_all +decide [Set.ext_iff]
  · constructor
    swap
    exact fun x => False.elim <| hS x x.2
    exact ⟨continuous_of_const fun x y => by tauto, fun _ => 0, continuousOn_const, fun x => by tauto⟩
  · obtain ⟨g, hg⟩ := this ⟨_, hS_empty.choose_spec.choose_spec⟩
    -- Let $P_n = \text{disjointed}(C(g(n)))$.
    set P : ℕ → Set A := fun n => disjointed (fun n => Classical.choose (hloc (g n))) n
    -- Each $P_n$ is clopen and pairwise disjoint.
    have hP_clopen : ∀ n, IsClopen (P n) := by
      intro n
      apply disjointed_clopen
      exact fun n => Classical.choose_spec (hloc (g n)) |>.1
    have hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
      exact fun i j hij => disjoint_disjointed _ hij
    have hP_cover : ⋃ i, P i = Set.univ := by
      ext x; simp [P]
      have := hS.2 x x.2
      obtain ⟨i, hi, hi', hi''⟩ := this
      obtain ⟨n, hn⟩ := hg _ hi |>.1 hi'
      have h_exists_n : ∃ n, x ∈ Classical.choose (hloc (g n)) ∧ ∀ m < n, x ∉ Classical.choose (hloc (g m)) := by
        exact ⟨Nat.find (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))), Nat.find_spec (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))), fun m mn => Nat.find_min (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))) mn⟩
      obtain ⟨n, hn₁, hn₂⟩ := h_exists_n; use n; simp_all +decide [disjointed]
    -- Each $P_n$ reduces to $MaxFun \alpha$.
    have hP_reduces : ∀ n, ContinuouslyReduces (fun x : P n => f x.val) (MaxFun α) := by
      intro n
      have := Classical.choose_spec (hloc (g n))
      exact ContinuouslyReduces.restrict_of_subset (show P n ⊆ Classical.choose (hloc (g n)) from disjointed_subset _ _) this.2.2
    convert clopen_partition_to_gluing_reduces f P hP_clopen hP_disj hP_cover hP_reduces |> fun h => h.trans (gluingSet_copies_reduces_to_MaxFun α hα) using 1

/-- Homeomorphism between {a : A | a.val ∈ U} and A ∩ U -/
def subtypeInterHomeo (A U : Set (ℕ → ℕ)) :
    {a : A | (a : ℕ → ℕ) ∈ U} ≃ₜ (A ∩ U : Set (ℕ → ℕ)) where
  toFun a := ⟨a.val.val, ⟨a.val.prop, a.prop⟩⟩
  invFun x := ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
  left_inv a := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := by
    exact continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val |>.subtype_mk _

/-- Transfer: f ∘ Subtype.val on {a ∈ A | a.val ∈ U} equals f' ∘ e. -/
lemma subtype_inter_fun_eq (A U : Set (ℕ → ℕ)) (f : A → ℕ → ℕ) :
    f ∘ (Subtype.val : {a : A | (a : ℕ → ℕ) ∈ U} → A) =
    (fun x : (A ∩ U : Set (ℕ → ℕ)) => f ⟨x.val, x.prop.1⟩) ∘ (subtypeInterHomeo A U) := by
  ext a; simp [subtypeInterHomeo]

end
