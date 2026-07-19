import WqoContinuousFunctions.ScatFun.Operations.Pgl
import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers
import WqoContinuousFunctions.PointedGluing.CBRank.Helpers
import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers
import WqoContinuousFunctions.PointedGluing.MinFun.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# The bundled generators `ℓ_α` (`maxFun`) and `k_{α+1}` (`minFun`)

Split out of the former monolithic `ScatFun/Operations.lean`.

* `ScatFun.maxFun`     — the maximum function `ℓ_α`, bundled
* `ScatFun.minFun`     — the minimum function `k_{α+1}`, bundled
* `ScatFun.succMaxFun` — `pgl ℓ_α`, the canonical non-minimal centered function at level `α + 1`
-/

namespace ScatFun

/-- The bundled **maximum function** `ℓ_α`.  `MaxFun α` is the subtype coercion on
`MaxDom α`, hence continuous for free; scatteredness comes from
`maxfun_is_scatter_leq_α`.  By that lemma all CB-levels strictly above `α` are
empty, so `CBRank (maxFun α).func ≤ α` (see `maxFun_cbRank_le`). -/
def maxFun (α : Ordinal.{0}) (hα : α < omega1) : ScatFun where
  domain := MaxDom α
  func := MaxFun α
  hScat := (maxfun_is_scatter_leq_α α hα).1
  hCont := continuous_subtype_val

@[simp] lemma maxFun_func (α : Ordinal.{0}) (hα : α < omega1) :
    (maxFun α hα).func = MaxFun α := rfl

/-- All CB-levels strictly above `α` are empty for `ℓ_α`. -/
lemma maxFun_cbLevel_empty (α : Ordinal.{0}) (hα : α < omega1)
    {β : Ordinal.{0}} (hβ : α < β) : CBLevel (maxFun α hα).func β = ∅ :=
  (maxfun_is_scatter_leq_α α hα).2 β hβ

/-- `ℓ_α` has CB-rank at most `α + 1` (its level above `α` is already empty). -/
lemma maxFun_cbRank_le (α : Ordinal.{0}) (hα : α < omega1) :
    CBRank (maxFun α hα).func ≤ Order.succ α :=
  CBRank_le_of_CBLevel_empty _ _ (maxFun_cbLevel_empty α hα (Order.lt_succ α))

/-- The bundled **minimum function** `k_{α+1}` (note the index shift: `minFun α`
is `k_{α+1}`, of CB-rank `α + 1`).  Continuity is free (`MinFun = Subtype.val`);
scatteredness comes from `minfun_is_scatter_leq_succ_α`. -/
def minFun (α : Ordinal.{0}) (hα : α < omega1) : ScatFun where
  domain := MinDom α
  func := MinFun α
  hScat := (minfun_is_scatter_leq_succ_α α hα).1
  hCont := continuous_subtype_val

@[simp] lemma minFun_func (α : Ordinal.{0}) (hα : α < omega1) :
    (minFun α hα).func = MinFun α := rfl

/-- All CB-levels strictly above `α + 1` are empty for `k_{α+1}`. -/
lemma minFun_cbLevel_empty (α : Ordinal.{0}) (hα : α < omega1)
    {β : Ordinal.{0}} (hβ : Order.succ α < β) : CBLevel (minFun α hα).func β = ∅ :=
  (minfun_is_scatter_leq_succ_α α hα).2 β hβ

/-- The bundled **successor maximum function** `pgl ℓ_α`. -/
def succMaxFun (α : Ordinal.{0}) (hα : α < omega1) : ScatFun :=
  pgl (fun _ => maxFun α hα)

@[simp] lemma succMaxFun_eq (α : Ordinal.{0}) (hα : α < omega1) :
    succMaxFun α hα = pgl (fun _ => maxFun α hα) := rfl

end ScatFun

end
