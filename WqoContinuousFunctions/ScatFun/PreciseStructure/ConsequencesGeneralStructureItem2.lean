import WqoContinuousFunctions.PointedGluing.GeneralStructureConsequences
import WqoContinuousFunctions.CenteredFunctions.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# `ConsequencesGeneralStructureThm`, item 2 — `ScatFun` form

`ScatFun`-bundled wrapper around `consequencesGeneralStructure_pgl_maxFun_le`
(`PointedGluing/GeneralStructureConsequences.lean`), using `succMaxFun_func`
(`CenteredFunctions/Helpers.lean:642`) to identify `(ScatFun.succMaxFun lam hlam).func`
with the raw `SuccMaxFun lam`. Split out from the raw-level file since the `ScatFun`
bundling machinery lives above `PointedGluing` and must not be imported by it.
-/

/-- **`ConsequencesGeneralStructureThm`, item 2 (`ScatFun` form).** If `CBRank F.func ≥ λ+2`
for `λ` limit or `0`, then `succMaxFun λ` (`pgl ℓ_λ`) reduces to `F`. -/
theorem consequencesGeneralStructure_succMaxFun_le
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (F : ScatFun) (hrank : Order.succ (Order.succ lam) ≤ CBRank F.func) :
    ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) F := by
  show ContinuouslyReduces (ScatFun.succMaxFun lam hlam_lt).func F.func
  rw [succMaxFun_func]
  exact consequencesGeneralStructure_pgl_maxFun_le lam hlam_lt hlim F.domain F.func F.hCont
    F.hScat hrank

end
