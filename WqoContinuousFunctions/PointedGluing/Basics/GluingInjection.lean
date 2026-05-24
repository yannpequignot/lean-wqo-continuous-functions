import WqoContinuousFunctions.PointedGluing.Basics.Functoriality
import WqoContinuousFunctions.BQO.OrdinalBQO

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Gluing with Injection and Successor Step

This file contains the successor step for MaxFun ≤ MinFun and the gluing-to-pointed-gluing
reduction via an injective index map.

## Main results

* `MaxFun_le_MinFun_succ` — successor step: MaxFun(succ α) ≤ MinFun(succ(succ β))
* `gluing_reduces_to_pgluing_via_injection` — gluing of reductions with an injection
-/

/--
Successor step for MaxFun_le_MinFun:
If MaxFun(α) ≤ MinFun(β), then MaxFun(succ α) ≤ MinFun(succ (succ β)).
-/
lemma MaxFun_le_MinFun_succ (α β : Ordinal.{0})
    (h : ContinuouslyReduces (MaxFun α) (MinFun β)) :
    ContinuouslyReduces (MaxFun (Order.succ α)) (MinFun (Order.succ (Order.succ β))) := by
  have h_maxFun_succ : MaxFun (Order.succ α) = Subtype.val := by
    -- By definition of MaxFun, we know that MaxFun (Order.succ α) is the subtype val.
    funext x; simp [MaxFun]
  convert h_maxFun_succ using 1
  constructor <;> intro h
  · lia
  · convert omega_pgl_le_pgl_pgl (MaxDom α) |> fun h => h.trans (pgl_functorial_val _ _ <| pgl_functorial_val _ _ ‹MaxFun α ≤ MinFun β›) using 1
    all_goals congr! 1
    all_goals norm_num [MaxFun, MinFun, MaxDom_succ, MinDom_succ]
    · grind
    · rfl
    · congr! 1
      ext; simp [MaxDom_succ]
    · congr! 1
      ext; simp [MinDom_succ]

/--
Membership: unprepend x.val ∈ A (x.val 0) for x ∈ GluingSet A.
-/
private lemma unprepend_mem_of_gluingSet (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    unprepend x.val ∈ A (x.val 0) := by
  exact GluingSet_inverse_short A x |> fun ⟨i, hi1, hi2⟩ => hi1 ▸ hi2

/--
σ' is continuous: on each block, it's a composition of continuous functions.
-/
private lemma gluing_to_pgluing_sigma_cont
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ)
    (σ_n : ∀ n, A n → B (p n))
    (hσc : ∀ n, Continuous (σ_n n)) :
    Continuous (fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)) := by
  refine Continuous.subtype_mk ?_ ?_
  have h_unprepend_cont : Continuous (fun x : GluingSet A => unprepend x.val) := by
    exact continuous_unprepend.comp continuous_subtype_val
  have h_cont : ∀ n, Continuous (fun x : {x : GluingSet A | x.val 0 = n} => prependZerosOne (p n) ((σ_n n ⟨unprepend x.val, by
    convert unprepend_mem_of_gluingSet A x ; aesop⟩).val)) := by
    intro n
    have h_cont : Continuous (fun x : {x : GluingSet A | x.val 0 = n} => (σ_n n ⟨unprepend x.val, by
      convert unprepend_mem_of_gluingSet A x ; aesop⟩).val) := by
      exact Continuous.comp (continuous_subtype_val) (hσc n |> Continuous.comp <| Continuous.subtype_mk (h_unprepend_cont.comp <| continuous_subtype_val) _)
    generalize_proofs at *
    exact Continuous.comp (show Continuous (fun x : ℕ → ℕ => prependZerosOne (p n) x) from continuous_prependZerosOne _) h_cont
  generalize_proofs at *
  have h_cont : ∀ n, ContinuousOn (fun x : GluingSet A => prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val, by
    solve_by_elim⟩).val)) {x : GluingSet A | x.val 0 = n} := by
    intro n
    generalize_proofs at *
    rw [continuousOn_iff_continuous_restrict]
    convert h_cont n using 1
    grind
  generalize_proofs at *
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have := h_cont (x.val 0)
  convert this.continuousAt _ using 1
  rw [mem_nhds_iff]
  refine ⟨{ y : GluingSet A | y.val 0 = x.val 0 }, ?_, ?_, ?_⟩ <;> norm_num
  refine ⟨{ y : ℕ → ℕ | y 0 = x.val 0 }, ?_, ?_⟩
  · rw [isOpen_pi_iff]
    exact fun f hf => ⟨{ 0 }, fun _ => { y | y = x.val 0 }, by aesop⟩
  · rfl

/--
Elements of the range in block p(n₀) come from σ_n₀.
-/
private lemma gluing_sigma_range_block
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (σ_n : ∀ n, A n → B (p n))
    (n₀ : ℕ) :
    let σ' := fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)
    ∀ y ∈ Set.range (Subtype.val ∘ σ') ∩
        {y : ℕ → ℕ | (∀ k < p n₀, y k = 0) ∧ y (p n₀) ≠ 0},
      stripZerosOne (p n₀) y ∈ Set.range (Subtype.val ∘ σ_n n₀) := by
  intro σ' y hy
  obtain ⟨x, hx⟩ := hy.left
  simp only [comp_def] at hx
  have h_firstNonzero_eq : firstNonzero y = p n₀ := by
    apply firstNonzero_eq_of_block
    exact hy.2
  grind +suggestions

/--
τ' is ContinuousOn the range.
-/
private lemma gluing_to_pgluing_tau_cont
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (σ_n : ∀ n, A n → B (p n))
    (_hσc : ∀ n, Continuous (σ_n n))
    (τ_n : ∀ _n, (ℕ → ℕ) → (ℕ → ℕ))
    (hτc : ∀ n, ContinuousOn (τ_n n) (Set.range (Subtype.val ∘ σ_n n)))
    (_heq : ∀ n (a : A n), a.val = τ_n n ((σ_n n a).val)) :
    let σ' := fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)
    ContinuousOn
      (fun y => prepend (Function.invFun p (firstNonzero y)) (τ_n (Function.invFun p (firstNonzero y)) (stripZerosOne (firstNonzero y) y)))
      (Set.range (Subtype.val ∘ σ')) := by
  intro x
  refine fun y hy => continuousWithinAt_tau_at_block ?_ ?_ ?_
  · exact hy
  · obtain ⟨x, rfl⟩ := hy
    exact prependZerosOne_ne_zeroStream _ _
  · refine ⟨{ z | (∀ k < firstNonzero y, z k = 0) ∧ z (firstNonzero y) ≠ 0 }, isOpen_block _, ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := hy
      unfold firstNonzero; simp +decide
      split_ifs with h
      · exact ⟨fun k hk => by simpa using Nat.find_min (show ∃ k, ¬ (x z : ℕ → ℕ) k = 0 from h) hk, Nat.find_spec (show ∃ k, ¬ (x z : ℕ → ℕ) k = 0 from h)⟩
      · simp +zetaDelta at *
        exact absurd (h (p (z.val 0))) (by simp +decide [prependZerosOne])
    · refine ⟨fun z => prepend (invFun p (firstNonzero z))
            (τ_n (invFun p (firstNonzero z)) (stripZerosOne (firstNonzero z) z)), ?_, fun z _ => rfl⟩
      apply ContinuousOn.congr
      pick_goal 3
      · exact fun z => prepend (invFun p (firstNonzero y))
            (τ_n (invFun p (firstNonzero y)) (stripZerosOne (firstNonzero y) z))
      · refine ContinuousOn.comp (t := Set.univ) (continuous_prepend _ |> Continuous.continuousOn) ?_ ?_
        · refine ContinuousOn.comp (hτc _) ?_ ?_
          · exact Continuous.continuousOn (continuous_stripZerosOne _)
          · intro z hz
            convert gluing_sigma_range_block A B p hp σ_n (invFun p (firstNonzero y)) z _ using 1
            · rw [invFun_eq (show ∃ n, p n = firstNonzero y from _)]
              grind +suggestions
            · rw [invFun_eq (show ∃ n, p n = firstNonzero y from _)]
              · exact hz
              · grind +suggestions
        · exact fun _ _ => Set.mem_univ _
      · intro z hz
        have h_firstNonzero : firstNonzero z = firstNonzero y := by
          apply firstNonzero_eq_of_block
          exact hz.2
        grind +splitImp

/-- Gluing of reductions with an injection. -/
lemma gluing_reduces_to_pgluing_via_injection
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (h : ∀ n, ContinuouslyReduces
      (Subtype.val : A n → ℕ → ℕ) (Subtype.val : B (p n) → ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : GluingSet A → ℕ → ℕ)
      (Subtype.val : PointedGluingSet B → ℕ → ℕ) := by
  choose σ_n hσc τ_n hτc heq using h
  refine ⟨fun x => ⟨prependZerosOne (p (x.val 0))
      ((σ_n (x.val 0) ⟨unprepend x.val, unprepend_mem_of_gluingSet A x⟩ :
        B (p (x.val 0))).val),
      prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩,
    gluing_to_pgluing_sigma_cont A B p σ_n hσc, ?_⟩
  refine ⟨fun y => prepend (Function.invFun p (firstNonzero y))
      (τ_n (Function.invFun p (firstNonzero y)) (stripZerosOne (firstNonzero y) y)),
    gluing_to_pgluing_tau_cont A B p hp σ_n hσc τ_n hτc heq, ?_⟩
  -- Equation: x.val = τ((σ x).val)
  intro x
  simp only []
  rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne,
      Function.leftInverse_invFun hp]
  rw [← heq (x.val 0) ⟨unprepend x.val, unprepend_mem_of_gluingSet A x⟩]
  exact (prepend_unprepend x.val).symm

end
