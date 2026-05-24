import Mathlib
import WqoContinuousFunctions.PointedGluing.GeneralStructure

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## `ScatFun`: scattered continuous functions on Baire space

**Design note.** `ScatFun.Level β` is a *subtype* of `ScatFun`, not an
independent sigma type.  This means the underlying `ScatFun` is accessed
via `.val` without any `Eq.rec` cast, and the only cast lemma needed is
`ScatFun.Level.cast_val`.
-/

/-- A **scattered continuous function** on Baire space: a domain set together
    with a continuous scattered function on that domain. -/
structure ScatFun where
  domain : Set Baire
  func   : ↑domain → Baire
  hScat  : ScatteredFun func
  hCont  : Continuous func

namespace ScatFun

/-- The **level-β fragment**: scattered continuous functions of CB-rank `β`.
    Defined as a subtype of `ScatFun` so that `.val` recovers the underlying
    function without any cast. -/
def Level (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func = β }

def LevelLE (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func ≤ β }

def LevelLT (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func < β }

/-- Continuous reducibility between two `ScatFun`s. -/
def Reduces (F G : ScatFun) : Prop :=
  ContinuouslyReduces F.func G.func

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def Level.reduces (β : Ordinal.{0}) :
    ScatFun.Level β → ScatFun.Level β → Prop :=
  fun F G => ScatFun.Reduces F.val G.val

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def LevelLE.reduces (β : Ordinal.{0}) :
    ScatFun.LevelLE β → ScatFun.LevelLE β → Prop :=
  fun F G => ScatFun.Reduces F.val G.val

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def LevelLT.reduces (β : Ordinal.{0}) :
    ScatFun.LevelLT β → ScatFun.LevelLT β → Prop :=
  fun F G => ScatFun.Reduces F.val G.val

/-! ## Cast lemma -/

/-- Casting a `ScatFun.Level` element does not change the underlying `ScatFun`.
    This is the only cast lemma needed in the whole development. -/
lemma Level.cast_val {α β : Ordinal.{0}} (h : α = β) (F : ScatFun.Level α) :
    (h ▸ F).val = F.val := by subst h; rfl

/-! ## Embedding into the sigma type `Σ β, ScatFun.Level β` -/

/-- Embed `F : ScatFun` into the level of its CB-rank. -/
@[reducible] def toLevel (F : ScatFun) : ScatFun.Level (CBRank F.func) :=
  ⟨F, rfl⟩

/-- The canonical equivalence between `ScatFun` and `Σ β, ScatFun.Level β`. -/
def equivSigmaLevel : ScatFun ≃ Σ β : Ordinal.{0}, ScatFun.Level β where
  toFun    F := ⟨CBRank F.func, ⟨F, rfl⟩⟩
  invFun   p := p.2.val
  left_inv F := rfl
  right_inv p := by
    obtain ⟨β, F, hβ⟩ := p
    exact Sigma.ext hβ (by subst hβ; rfl)


end ScatFun
