import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LevelLTTwoBQO
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.Two
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LambdaPlusOne
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.DoubleSuccessor

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Finite generation of `CB`-rank levels — the induction assembly

Assembles `ScatFun.levels_finitely_generated` (the memoir's `PreciseStructureThm`, temporarily
commented out in `LevelsFinitelyGenerated.lean`) from the level-by-level instances by strong
induction on `α < ω₁`, splitting `α` into `0` / limit / successor, and (for the successor case)
further into `β = 0` / `β` limit / `β` itself a successor:

* `α = 0` — `Generators_zero_finitely_generates`.
* `α` a nonzero limit — `Generators_lambda_finitely_generates`.
* `α = 0 + 1 = 1` — `Generators_one_finitely_generates`.
* `α = β + 1`, `β` a nonzero limit — 2-BQO of `LevelLT (β+1)` follows from `FG(<β+1)` (which is
  `FG(<β)`, the induction hypothesis, together with `FG(β)` itself,
  `Generators_lambda_finitely_generates`) via `LevelLT.isTwoBQO_of_FG_below`, discharging the
  extra hypothesis of `Generators_lambdaPlusOne_finitely_generates`.
* `α = γ + 1 + 1 = 2` (`γ = 0`) — `Generators_two_finitely_generates` (proved directly, no
  induction hypothesis needed).
* `α = γ + 1 + 1`, `γ ≠ 0` (general successor-of-successor) —
  `Generators_doubleSuccessor_finitely_generates` (`DoubleSuccessor.lean`), the memoir's
  "double successor" chapter, resting on the §6.1–6.4 chain in
  `DoubleSuccessor/{Fine,PseudoCentered,Diagonal,Solvable}.lean` (fully assembled;
  its two remaining open leaves live in `Solvable.lean`).

This file must not be imported by `Two.lean`/`LambdaPlusOne.lean` (it imports *them*), which is
exactly why the assembly cannot live in `LevelsFinitelyGenerated.lean` itself.
-/

namespace ScatFun

/-- `Order.succ 0 = 1` for ordinals, via `Ordinal.add_one_eq_succ` and `zero_add`. -/
private lemma succ_zero_eq_one : Order.succ (0 : Ordinal.{0}) = 1 := by
  rw [← Ordinal.add_one_eq_succ]; norm_num

/-- `Order.succ 1 = 2` for ordinals, via `Ordinal.add_one_eq_succ`. -/
private lemma succ_one_eq_two : Order.succ (1 : Ordinal.{0}) = 2 := by
  rw [← Ordinal.add_one_eq_succ]; norm_num

/-- **Finite generation of `CB`-rank levels** (memoir `PreciseStructureThm`). For every
`α < ω₁`, every `F : ScatFun` of `CB`-rank `α` lies in `FinGl (Generators α).toFinFun`.

Every case is now wired to a named theorem; the general successor-of-successor step
(`α = γ+2`, `γ ≠ 0`) rests on `Generators_doubleSuccessor_finitely_generates`
(`DoubleSuccessor.lean`), whose §6.1–6.4 dependency chain is fully assembled up to two open
leaves in `Solvable.lean`. -/
theorem levels_finitely_generated : ∀ (α : Ordinal.{0}), α < omega1 →
    ∀ F : ScatFun, CBRank F.func = α → F ∈ FinGl (Generators α).toFinFun := by
  intro α
  induction α using Ordinal.induction with
  | h α ih =>
  intro hα
  by_cases hα0 : α = 0
  · subst hα0
    exact Generators_zero_finitely_generates
  · by_cases hαsucc : ∃ β, α = Order.succ β
    · obtain ⟨β, rfl⟩ := hαsucc
      by_cases hβ0 : β = 0
      · subst hβ0
        rw [succ_zero_eq_one]
        exact Generators_one_finitely_generates
      · by_cases hβsucc : ∃ γ, β = Order.succ γ
        · obtain ⟨γ, rfl⟩ := hβsucc
          by_cases hγ0 : γ = 0
          · subst hγ0
            rw [succ_zero_eq_one, succ_one_eq_two]
            exact Generators_two_finitely_generates
          · -- `α = γ + 1 + 1` for `γ ≠ 0` (successor of a successor, neither `0` nor `2`):
            -- the memoir's double-successor chapter,
            -- `Generators_doubleSuccessor_finitely_generates`
            -- (`LevelsFinitelyGenerated/DoubleSuccessor.lean`, resting on two open `Solvable.lean` leaves);
            -- `FG(<γ+2)` is exactly the induction hypothesis.
            have hγ : γ < omega1 :=
              lt_of_le_of_lt ((Order.le_succ γ).trans (Order.le_succ _)) hα
            simp only [← Ordinal.add_one_eq_succ] at hα ⊢
            exact Generators_doubleSuccessor_finitely_generates γ hγ
              (fun β hβ G hG =>
                ih β (by simpa only [← Ordinal.add_one_eq_succ] using hβ)
                  (lt_trans hβ hα) G hG)
        · -- `β` is a nonzero limit ordinal (α = Order.succ β = β + 1).
          obtain ⟨β0, hβ0eq, hβlim, -⟩ : ∃ β0, β = β0 ∧ Order.IsSuccLimit β0 ∧ β ≠ 0 := by
            simp_all +decide [Order.IsSuccLimit]
            exact fun x hx => hβsucc x <| by rw [eq_comm]; exact CovBy.succ_eq hx
          have hβlim' : Order.IsSuccLimit β := by rw [hβ0eq]; exact hβlim
          rw [← Ordinal.add_one_eq_succ] at hα ⊢
          have hβlt : β < omega1 := lt_of_le_of_lt le_self_add hα
          have hbqo : TwoBQO (ScatFun.LevelLT.reduces (β + 1)) := by
            apply LevelLT.isTwoBQO_of_FG_below
            intro γ hγ F hF
            rw [Ordinal.add_one_eq_succ, Order.lt_succ_iff] at hγ
            rcases hγ.lt_or_eq with hγlt | rfl
            · exact ih γ (lt_trans hγlt (Order.lt_succ β)) (lt_trans hγlt hβlt) F hF
            · exact Generators_lambda_finitely_generates γ hβlim' hβlt F hF
          exact Generators_lambdaPlusOne_finitely_generates β hβlim' hβlt hbqo
    · -- `α` is a nonzero limit ordinal.
      obtain ⟨α0, hα0eq, hαlim, -⟩ : ∃ α0, α = α0 ∧ Order.IsSuccLimit α0 ∧ α ≠ 0 := by
        simp_all +decide [Order.IsSuccLimit]
        exact fun x hx => hαsucc x <| by rw [eq_comm]; exact CovBy.succ_eq hx
      have hαlim' : Order.IsSuccLimit α := by rw [hα0eq]; exact hαlim
      exact Generators_lambda_finitely_generates α hαlim' hα

end ScatFun

end
