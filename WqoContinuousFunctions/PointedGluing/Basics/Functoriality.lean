import WqoContinuousFunctions.PointedGluing.MinFun.Theorems
import Mathlib.Tactic
import Mathlib.Topology.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Pointed Gluing Functoriality

Helper lemmas establishing that pointed gluing is functorial for continuous reductions:
if `A ≤ B` then `pgl(A) ≤ pgl(B)`, and that `ω · pgl(X) ≤ pgl(pgl(X))`.

## Main results

* `pgl_functorial_val` — functoriality of pointed gluing for constant sequences
* `omega_pgl_le_pgl_pgl` — ω · pgl(X) ≤ pgl(pgl(X))
-/

/-- For non-zeroStream x in PointedGluingSet,
x = prependZerosOne (firstNonzero x) (stripZerosOne (firstNonzero x) x) -/
lemma pgs_reconstruct {A : ℕ → Set (ℕ → ℕ)}
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    x.val = prependZerosOne (firstNonzero x.val) (stripZerosOne (firstNonzero x.val) x.val) := by
  have : ∃ j, ∃ a ∈ A j, (↑x : ℕ → ℕ) = prependZerosOne j a := by
    rcases x with ⟨v, hv⟩; simp [PointedGluingSet] at hv
    rcases hv with rfl | ⟨j, a, ha, rfl⟩
    · exact absurd rfl hx
    · exact ⟨j, a, ha, rfl⟩
  obtain ⟨j, a, _, ha⟩ := this
  rw [ha, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]

/-- PointedGluingFun maps into PointedGluingSet -/
lemma pgl_fun_mem (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) :
    PointedGluingFun A B f x ∈ PointedGluingSet B := by
  unfold PointedGluingFun; split_ifs with h1
  · exact Or.inl rfl
  · simp only []; split_ifs with h2
    · exact Or.inr (Set.mem_iUnion.mpr ⟨_, _, (f _ ⟨_, h2⟩).prop, rfl⟩)
    · exact absurd (strip_mem_of_pointedGluingSet A x h1) h2

private lemma pgl_tau_cwat_zero (A B : Set (ℕ → ℕ))
    (σ : A → B) (_hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (_hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (_heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    let τ' := fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y))
    let R := Set.range (Subtype.val ∘
      (fun x : PointedGluingSet (fun _ => A) =>
        (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
          pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))
    ContinuousWithinAt τ' R zeroStream := by
  -- Apply the lemma continuousWithinAt_tau_at_zeroStream with the given parameters.
  apply continuousWithinAt_tau_at_zeroStream
  exact List.map_inj.mp rfl
  rotate_right
  use fun n => { n }
  · simp +contextual
  · simp +zetaDelta at *
    intro z x hx hz hz' k hk; rw [if_neg hz'] ; exact prependZerosOne_head_eq_zero _ _ _ hk

/--
Helper: ContinuousWithinAt at non-zeroStream points for the τ' map.
-/
private lemma pgl_tau_cwat_block (A B : Set (ℕ → ℕ))
    (σ : A → B) (_hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (_heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    let τ' := fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y))
    let R := Set.range (Subtype.val ∘
      (fun x : PointedGluingSet (fun _ => A) =>
        (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
          pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))
    ∀ z₀ ∈ R, z₀ ≠ zeroStream → ContinuousWithinAt τ' R z₀ := by
  intro τ' R z₀ hz₀ hz₀_ne
  -- Let $i₀ = firstNonzero z₀$.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, firstNonzero z₀ = i₀ ∧ (∀ k < i₀, z₀ k = 0) ∧ z₀ i₀ ≠ 0 := by
    unfold firstNonzero; simp +decide
    split_ifs with h <;> simp_all +singlePass [funext_iff]
    · exact Nat.find_spec h
    · exact hz₀_ne.elim fun n hn => hn <| by unfold zeroStream; simp +decide
  -- On R ∩ U, every z has firstNonzero z = i₀ (by firstNonzero_eq_of_block), so:
  have h_block : ∀ z ∈ R, z ∈ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0} → firstNonzero z = i₀ := by
    intros z hz hz_block
    unfold firstNonzero at *
    split_ifs at * <;> simp_all +singlePass [Nat.find_eq_iff]
  -- Let $g = \text{prependZerosOne } i₀ \circ \tau \circ \text{stripZerosOne } i₀$.
  set g : (ℕ → ℕ) → (ℕ → ℕ) := fun y => prependZerosOne i₀ (τ (stripZerosOne i₀ y))
  -- We need to show that $g$ is continuous on $R \cap U$.
  have h_g_cont : ContinuousOn g (R ∩ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0}) := by
    refine ContinuousOn.comp (show ContinuousOn (fun y => prependZerosOne i₀ y) (Set.range (fun y => τ (stripZerosOne i₀ y))) from ?_) ?_ ?_
    · exact Continuous.continuousOn (continuous_prependZerosOne _)
    · refine hτ.comp ?_ ?_
      · exact Continuous.continuousOn (continuous_stripZerosOne i₀)
      · intro x hx; obtain ⟨y, rfl⟩ := hx.1; simp +decide [PointedGluingFun] at *
        split_ifs at hx <;> simp_all +singlePass
        · exact False.elim <| hx.2.2 <| by rfl
        · grind [prependZerosOne_head_eq_zero, prependZerosOne_ne_zeroStream, firstNonzero_prependZerosOne, firstNonzero_val_ne, stripZerosOne_prependZerosOne]
        · exact False.elim <| hx.2.2 <| by simp +decide [zeroStream]
    · exact fun x hx => Set.mem_range_self _
  have h_g_eq : ∀ z ∈ R, z ∈ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0} → τ' z = g z := by
    simp +zetaDelta only [Subtype.forall, mem_range, comp_apply, Subtype.exists, ne_eq, mem_setOf_eq, and_imp, forall_exists_index] at *
    intro z x hx hz hz' hz''; rw [if_neg (by rintro rfl; exact hz'' (by simp +decide [zeroStream]))] ; rw [h_block z x hx hz hz' hz'']
  have h_g_eq : ContinuousWithinAt τ' (R ∩ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0}) z₀ := by
    exact ContinuousOn.continuousWithinAt (h_g_cont.congr fun x hx => h_g_eq x hx.1 hx.2 ▸ rfl) (by aesop)
  rw [ContinuousWithinAt] at *
  rw [nhdsWithin_inter] at h_g_eq
  convert h_g_eq using 1
  rw [inf_eq_left.mpr]
  rw [nhdsWithin_le_iff]
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  use {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0}
  exact ⟨isOpen_block i₀ |> IsOpen.mem_nhds <| by tauto, fun x hx => hx.1⟩

/-- ContinuousOn for the τ' in pgl_functorial_val. -/
lemma pgl_tau_continuousOn (A B : Set (ℕ → ℕ))
    (σ : A → B) (hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    ContinuousOn
      (fun y => if y = zeroStream then zeroStream
        else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y)))
      (Set.range (Subtype.val ∘
        (fun x : PointedGluingSet (fun _ => A) =>
          (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
            pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))) := by
  intro z hz
  by_cases hz0 : z = zeroStream
  · subst hz0; exact pgl_tau_cwat_zero A B σ hσ τ hτ heq
  · exact pgl_tau_cwat_block A B σ hσ τ hτ heq z hz hz0

/-- Functoriality of PointedGluing for constant sequences. -/
lemma pgl_functorial_val (A B : Set (ℕ → ℕ))
    (h : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (Subtype.val : B → ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : PointedGluingSet (fun _ => A) → ℕ → ℕ)
      (Subtype.val : PointedGluingSet (fun _ => B) → ℕ → ℕ) := by
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := h
  refine ⟨fun x => ⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
    pgl_fun_mem _ _ _ x⟩, ?_, ?_⟩
  · exact pointedGluingFun_preserves_continuity _ _ _ (fun _ => hσ)
  · refine ⟨fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y)),
      pgl_tau_continuousOn A B σ hσ τ hτ heq, ?_⟩
    intro x
    show x.val = _
    simp only []
    by_cases hx : x.val = zeroStream
    · have : PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x = zeroStream := by
        unfold PointedGluingFun; simp [hx]
      rw [this, if_pos rfl, hx]
    · have hmem := strip_mem_of_pointedGluingSet (fun _ => A) x hx
      rw [pointedGluingFun_eq_on_block (fun _ => A) (fun _ => B) (fun _ => σ) x hx]
      rw [if_neg (prependZerosOne_ne_zeroStream _ _)]
      rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
      conv_lhs => rw [pgs_reconstruct x hx]
      congr 1
      exact heq ⟨_, hmem⟩

/-- The GluingSet of copies of PointedGluingSet reduces to PointedGluingSet of PointedGluingSet.
This is ω · pgl(X) ≤ pgl(pgl(X)). -/
lemma omega_pgl_le_pgl_pgl (A : Set (ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : GluingSet (fun _ => PointedGluingSet (fun _ => A)) → ℕ → ℕ)
      (Subtype.val : PointedGluingSet (fun _ => PointedGluingSet (fun _ => A)) → ℕ → ℕ) := by
  convert gluing_le_pointedGluing (fun _ => PointedGluingSet (fun _ => A))
    (fun _ => PointedGluingSet (fun _ => A)) (fun _ => id)
  · ext; simp [GluingFunVal]
    rename_i k; cases k <;> simp +decide [prepend, unprepend]
  · exact funext fun x => Eq.symm (PointedGluingFun_id _ _)

end
