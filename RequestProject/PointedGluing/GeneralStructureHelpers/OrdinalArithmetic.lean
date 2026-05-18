import RequestProject.PointedGluing.Defs
import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Ordinal Arithmetic Helpers

Helper lemmas about ordinal decomposition and cofinal sequences used in the
General Structure Theorem.

## Main results

* `limit_add_nat_lt` — adding a finite number to an ordinal below a limit stays below
* `ordinal_limit_nat_decomposition` — every ordinal decomposes as limit + ℕ
* `cofinalSeq_eventually_ge` — cofinal sequences eventually exceed any target
-/

/-- For limit η, adding a finite natural number m stays below η. -/
lemma limit_add_nat_lt (η : Ordinal.{0}) (hlim : Order.IsSuccLimit η) (_hne : η ≠ 0)
    (α : Ordinal.{0}) (hα : α < η) (m : ℕ) :
    α + ↑m < η := by
  induction' m with m ih
  · simpa using hα
  · convert hlim.succ_lt ih using 1
    simp +decide [Ordinal.add_succ]

lemma omega1_add_nat (η : Ordinal.{0}) (hη : η < omega1) (n : ℕ) :
    η + ↑n < omega1 := by
  induction n with
  | zero => simpa
  | succ n ih =>
    calc η + (↑(n + 1) : Ordinal) = Order.succ (η + ↑n) := by
          rw [Nat.cast_succ, ← Ordinal.add_one_eq_succ, add_assoc]
    _ < omega1 :=
          (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)).succ_lt ih


/-- Every ordinal can be decomposed as α' + m where α' is limit or 0 and m ∈ ℕ. -/
lemma ordinal_limit_nat_decomposition (α : Ordinal.{0}) :
    ∃ (α' : Ordinal.{0}) (m : ℕ),
      (Order.IsSuccLimit α' ∨ α' = 0) ∧ α = α' + ↑m := by
  by_contra! h_contra
  induction' α using Ordinal.induction with α ih
  by_cases hα : Order.IsSuccLimit α ∨ α = 0
  · exact h_contra α 0 hα (by simp +decide)
  · obtain ⟨β, rfl⟩ : ∃ β, α = Order.succ β := by
      simp_all +decide [Order.IsSuccLimit]
      simp_all +decide [Order.IsSuccPrelimit]
      exact Exists.elim (hα.1 hα.2) fun x hx => ⟨x, hx.succ_eq.symm⟩
    specialize ih β (Order.lt_succ β) ; simp_all +decide
    obtain ⟨α', hα', m, hm⟩ := ih; specialize h_contra α' (m + 1) ; simp_all +decide
    exact h_contra (by rw [Ordinal.add_succ])


/-- The limit part of an ordinal: the unique limit-or-zero ordinal `λ` such that
    `α = λ + n` for some `n : ℕ`. -/
noncomputable def Ordinal.limitPart (α : Ordinal.{0}) : Ordinal.{0} :=
  (ordinal_limit_nat_decomposition α).choose

/-- The natural part of an ordinal: the unique `n : ℕ` such that
    `α = α.limitPart + n`. -/
noncomputable def Ordinal.natPart (α : Ordinal.{0}) : ℕ :=
  (ordinal_limit_nat_decomposition α).choose_spec.choose

lemma Ordinal.limitPart_isLimit_or_zero (α : Ordinal.{0}) :
    Order.IsSuccLimit α.limitPart ∨ α.limitPart = 0 :=
  (ordinal_limit_nat_decomposition α).choose_spec.choose_spec.1

lemma Ordinal.eq_limitPart_add_natPart (α : Ordinal.{0}) :
    α = α.limitPart + α.natPart :=
  (ordinal_limit_nat_decomposition α).choose_spec.choose_spec.2

/-- Uniqueness of the limit-plus-nat decomposition. -/
lemma ordinal_limit_nat_decomposition_unique
    {lam0 lam1 : Ordinal.{0}} {n0 n1 : ℕ}
    (hlam0 : Order.IsSuccLimit lam0 ∨ lam0 = 0)
    (hlam1 : Order.IsSuccLimit lam1 ∨ lam1 = 0)
    (heq : lam0 + ↑n0 = lam1 + ↑n1) :
    lam0 = lam1 ∧ n0 = n1 := by
  rcases lt_trichotomy lam0 lam1 with h | rfl | h
  · exfalso
    have hlt : lam0 + ↑n0 < lam1 := by
      rcases hlam1 with hlim1 | rfl
      · exact limit_add_nat_lt lam1 hlim1
            (Order.IsSuccLimit.ne_bot hlim1) lam0 h n0
      · simp at h
    exact absurd heq (ne_of_lt (hlt.trans_le le_self_add))
  · -- lam0 = lam1: cancel to get n0 = n1
    refine ⟨rfl, ?_⟩
    have : (n0 : Ordinal) = n1 := add_left_cancel heq
    exact_mod_cast this
  · exfalso
    have hlt : lam1 + ↑n1 < lam0 := by
      rcases hlam0 with hlim0 | rfl
      · exact limit_add_nat_lt lam0 hlim0
            (Order.IsSuccLimit.ne_bot hlim0) lam1 h n1
      · simp at h
    exact absurd heq.symm (ne_of_lt (hlt.trans_le le_self_add))
    
/-- `limitPart` of an explicit `lam + n` is `lam`. -/
lemma Ordinal.limitPart_add_natCast
    (lam : Ordinal.{0}) (n : ℕ)
    (hlam : Order.IsSuccLimit lam ∨ lam = 0) :
    (lam + ↑n).limitPart = lam :=
  (ordinal_limit_nat_decomposition_unique
    (Ordinal.limitPart_isLimit_or_zero (lam + ↑n))
    hlam
    (Ordinal.eq_limitPart_add_natPart (lam + ↑n)).symm).1

/-- `natPart` of an explicit `lam + n` is `n`. -/
lemma Ordinal.natPart_add_natCast
    (lam : Ordinal.{0}) (n : ℕ)
    (hlam : Order.IsSuccLimit lam ∨ lam = 0) :
    (lam + ↑n).natPart = n :=
  (ordinal_limit_nat_decomposition_unique
    (Ordinal.limitPart_isLimit_or_zero (lam + ↑n))
    hlam
    (Ordinal.eq_limitPart_add_natPart (lam + ↑n)).symm).2

/-- For every ordinal β < η (limit), there exists n such that cofinalSeq η n ≥ β. -/
lemma cofinalSeq_eventually_ge (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η) (hne : η ≠ 0)
    (β : Ordinal.{0}) (hβ : β < η) :
    ∃ n : ℕ, β ≤ cofinalSeq η n := by
  have h_surj : Function.Surjective (fun n => ⟨cofinalSeq η n, cofinalSeq_lt η hlim hne n⟩ : ℕ → Iio η) := by
    convert enumBelow_surj η hη hne using 1
    unfold cofinalSeq; aesop
  cases' h_surj ⟨β, hβ⟩ with n hn ; use n ; aesop

end
