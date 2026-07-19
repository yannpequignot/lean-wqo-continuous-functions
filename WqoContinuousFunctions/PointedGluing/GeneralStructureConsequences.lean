import WqoContinuousFunctions.PointedGluing.GeneralStructure

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# `ConsequencesGeneralStructureThm`, item 2 (`3_general_struct_memo.tex:518-535`)

`Corollary ConsequencesGeneralStructureThm` states two consequences of the General
Structure Theorem (`general_structure_theorem`) for a limit ordinal `λ`. Item 1 is
formalized, at the `ScatFun` level, as `consequencesGeneralStructure_pgl_le_minFun`
(`CenteredFunctions/Theorems.lean:1070`). Item 2 — `CB(f) ≥ λ+2 → pgl ℓ_λ ≤ f` — was
explicitly left unformalized there (its docstring notes "Item 2 ... is likewise not used
by 4.12"); this file closes that gap at the raw `PointedGluing` level. (A `ScatFun`-level
wrapper lives in `ScatFun/PreciseStructure/ConsequencesGeneralStructureItem2.lean`, since the
`ScatFun` bundling machinery is not available to this foundational layer.)

## Provided solution (`3_general_struct_memo.tex:534-535`)

"By the General Structure Theorem `ℓ_λ ≤ k_{λ+1}` (`Maxfunctions`/`Minfunctions`), so
`pgl ℓ_λ ≤ pgl k_{λ+1} = k_{λ+2}`. Since `CB(f) ≥ λ+2`, `k_{λ+2} ≤ f`, so `pgl ℓ_λ ≤ f`."

Translated to the existing raw API:
* `ℓ_λ ≤ k_{λ+1}` is `maxFun_reduces_minFun_of_limit` (`PointedGluing/GeneralStructure.lean:361`).
* Pointed-gluing functoriality (`pgl_functorial_val`,
  `PointedGluing/Basics/Functoriality.lean:159`) lifts this to
  `pgl ℓ_λ ≤ (val : PointedGluingSet (fun _ => MinDom λ) → _)`.
* That target is literally `k_{λ+2} = MinFun (Order.succ λ)` after unfolding `MinDom_succ`
  (`PointedGluing/MaxFun/Helpers.lean`) — the `MinDom_succ` rewrite.
* `k_{λ+2} ≤ f` is `minFun_is_minimum` (`PointedGluing/MinFun/Theorems.lean:573`), applicable
  since `CB(f) ≥ λ+2` gives `Order.succ λ < CB(f)`.
-/

/-- **`ConsequencesGeneralStructureThm`, item 2 (raw form).** If `CB(f) ≥ λ+2` for `λ` limit
or `0`, then `pgl ℓ_λ` (`SuccMaxFun λ`) reduces to `f`. -/
theorem consequencesGeneralStructure_pgl_maxFun_le
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (B : Set Baire) (f : B → Baire) (hfc : Continuous f) (hf : ScatteredFun f)
    (hrank : Order.succ (Order.succ lam) ≤ CBRank f) :
    ContinuouslyReduces (SuccMaxFun lam) f := by
  have hstep : ContinuouslyReduces (SuccMaxFun lam) (MinFun (Order.succ lam)) := by
    show ContinuouslyReduces (Subtype.val : SuccMaxDom lam → _)
        (Subtype.val : MinDom (Order.succ lam) → _)
    rw [MinDom_succ]
    exact pgl_functorial_val (MaxDom lam) (MinDom lam)
      (maxFun_reduces_minFun_of_limit lam hlam_lt hlim)
  have hsucclt : Order.succ lam < CBRank f :=
    lt_of_lt_of_le (Order.lt_succ _) hrank
  have hsucc_lt_omega1 : Order.succ lam < omega1 := by
    have h1 : lam + ((1 : ℕ) : Ordinal.{0}) < omega1 := omega1_add_nat lam hlam_lt 1
    rwa [Nat.cast_one, Ordinal.add_one_eq_succ] at h1
  exact hstep.trans (minFun_is_minimum (Order.succ lam) hsucc_lt_omega1 B f hfc hf
    (CBLevel_nonempty_below_rank f hf (Order.succ lam) hsucclt))

end
