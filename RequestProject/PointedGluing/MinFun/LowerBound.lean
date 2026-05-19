import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.BaireSpace.GenRedProp
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankHelpers
import RequestProject.PointedGluing.CBLevelOpenRestrict
import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PointedGluing.UpperBoundHelpers
import RequestProject.PointedGluing.ContinuousOnTau
import RequestProject.PointedGluing.Theorems
import RequestProject.PointedGluing.MaxFun.Helpers
import RequestProject.PointedGluing.MinFun.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helpers for the pointed gluing lower bound
-/

/-- In the Baire space, cylinder sets form a neighborhood basis. -/
lemma baire_cylinder_mem_nhds (p : ℕ → ℕ) (U : Set (ℕ → ℕ)) (hU : IsOpen U) (hp : p ∈ U) :
    ∃ m : ℕ, {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = p i} ⊆ U := by
  rw [isOpen_pi_iff] at hU
  obtain ⟨I, u, hu, hU⟩ := hU p hp
  use I.sup id + 1
  intro h hh; specialize hU; simp_all +decide [Set.subset_def]
  exact hU _ fun i hi => by simpa [hh i (Finset.le_sup (f := id) hi)] using hu i hi

/-- In a subspace of the Baire space, cylinder sets form a neighborhood basis. -/
lemma baire_subspace_cylinder_mem_nhds {A : Set (ℕ → ℕ)} (x : A)
    (U : Set A) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ m : ℕ, (Subtype.val ⁻¹' {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = x.val i}) ⊆ U := by
  induction hU
  rename_i V hV
  rcases baire_cylinder_mem_nhds x.val V hV.1 (hV.2.symm.subset hx) with ⟨m, hm⟩ ; exact ⟨m, fun y hy => hV.2.subset <| hm hy⟩

/--
Iterative step: given a cylinder index k and codomain bound m_min,
produce reduction data with separation.
-/
lemma pgl_lower_bound_step
    {A _B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    {C D : ℕ → Set (ℕ → ℕ)}
    (g : ∀ i, C i → D i)
    (x : A)
    (hloc : ∀ (i : ℕ) (U : Set A), IsOpen U → x ∈ U →
      ∃ (σ : C i → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
        Continuous σ ∧
        (∀ z, (g i z : ℕ → ℕ) = τ (f (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        f x ∉ closure (Set.range (fun z => f (σ z))))
    (n k m_min : ℕ) :
    ∃ (l m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      m_min ≤ m ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ (Subtype.val ⁻¹' {h | ∀ i ∈ Finset.range k, h i = x.val i} : Set A)) ∧
      Disjoint (closure (Set.range (fun z => f (σ z))))
        {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = (f x) i} ∧
      f '' (Subtype.val ⁻¹' {h | ∀ i ∈ Finset.range l, h i = x.val i} : Set A) ⊆
        {h : ℕ → ℕ | ∀ i ∈ Finset.range m, h i = (f x) i} := by
  obtain ⟨σ, τ, hσ, hτ₁, hστ₁, hστ₂, hστ₃⟩ := hloc n (Subtype.val ⁻¹' { h | ∀ i ∈ Finset.range k, h i = x.val i }) (by exact IsOpen.preimage (continuous_subtype_val) <| show IsOpen { h : ℕ → ℕ | ∀ i ∈ Finset.range k, h i = x.val i } from by
                                                                                                                                                                                  convert baire_cylinder_isClopen (Finset.range k) x.val |> IsClopen.isOpen using 1) (by
                                                                                                                                                                                  exact fun i hi => rfl)
  -- By the properties of the Baire space, we can find such m.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≥ m_min ∧ Disjoint (closure (Set.range (fun z => f (σ z))) : Set (ℕ → ℕ)) {h | ∀ i ∈ Finset.range m, h i = f x i} := by
    obtain ⟨m, hm⟩ := baire_cylinder_mem_nhds (f x) (closure (Set.range fun z => f (σ z)))ᶜ (isOpen_compl_iff.mpr <| isClosed_closure) hστ₃
    exact ⟨m + m_min, by linarith, Set.disjoint_left.mpr fun y hy₁ hy₂ => hm (fun i hi => hy₂ i (Finset.mem_range.mpr (by linarith [Finset.mem_range.mp hi]))) hy₁⟩
  -- By the properties of the Baire space, we can find such l.
  obtain ⟨l, hl⟩ : ∃ l : ℕ, f '' (Subtype.val ⁻¹' {h | ∀ i ∈ Finset.range l, h i = x.val i}) ⊆ {h | ∀ i ∈ Finset.range m, h i = f x i} := by
    have := baire_subspace_cylinder_mem_nhds x (f ⁻¹' { h | ∀ i ∈ Finset.range m, h i = f x i }) (hf.isOpen_preimage _ <| by
      convert baire_cylinder_isClopen (Finset.range m) (f x) |> IsClopen.isOpen using 1) (by
      aesop)
    exact ⟨this.choose, Set.image_subset_iff.mpr this.choose_spec⟩
  exact ⟨l, m, σ, τ, hm.1, hσ, hτ₁, hστ₁, hστ₂, hm.2, hl⟩

end
