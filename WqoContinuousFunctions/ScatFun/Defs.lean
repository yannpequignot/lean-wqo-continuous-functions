import Mathlib.Tactic
import Mathlib.SetTheory.Ordinal.Basic
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

/-- The subset `A ⊆ ↑F.domain` is homeomorphic to its "re-realization" as a
subset of `Baire`. -/
def restrictEquiv (F : ScatFun) (A : Set ↑F.domain) :
    ↑{x : Baire | ∃ h : x ∈ F.domain, (⟨x, h⟩ : ↑F.domain) ∈ A} ≃ₜ A where
  toFun  := fun y => ⟨⟨y.1, y.2.choose⟩, y.2.choose_spec⟩
  invFun := fun a => ⟨a.1.1, ⟨a.1.2, by simp [a.2]⟩⟩
  left_inv := fun y => by ext; rfl
  right_inv := fun a => by ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_val

def restrict (F : ScatFun) (A : Set ↑F.domain) : ScatFun where
  domain := {x : Baire | ∃ h : x ∈ F.domain, (⟨x, h⟩ : ↑F.domain) ∈ A}
  func   := (F.func ∘ (Subtype.val : A → ↑F.domain)) ∘ (restrictEquiv F A)
  hScat  := (scattered_restrict F.func F.hScat A).comp_homeomorph (restrictEquiv F A)
  hCont  := (F.hCont.comp continuous_subtype_val).comp (restrictEquiv F A).continuous

/-- The **level-β fragment**: scattered continuous functions of CB-rank `β`.
    Defined as a subtype of `ScatFun` so that `.val` recovers the underlying
    function without any cast. -/
def Level (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func = β }

def LevelLE (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func ≤ β }

def LevelLT (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func < β }

/-- The **level interval** `𝒞_{[α,β]}`: scattered continuous functions whose
CB-rank lies in `[α, β]`.

This is the `ScatFun`-level analogue of `InCBLevelInterval`
(`PreciseStructure/Defs.lean`).  Because the `ScatFun` bundle already carries
scatteredness and continuity, the predicate only pins the rank bounds. -/
def LevelInter (α β : Ordinal.{0}) : Set ScatFun :=
  fun F => α ≤ CBRank F.func ∧ CBRank F.func ≤ β

/-- Continuous reducibility between two `ScatFun`s. -/
def Reduces (F G : ScatFun) : Prop :=
  ContinuouslyReduces F.func G.func

instance : IsPreorder ScatFun Reduces where
  refl := fun F => ContinuouslyReduces.refl F.func
  trans := fun _ _ _ hFG hGH => ContinuouslyReduces.trans hFG hGH

/-- **Continuous equivalence** of two scattered continuous functions: each
reduces to the other.  This is the memoir's `F ≡ G` at the `ScatFun` level (the
bundled analogue of `ContinuouslyEquiv` on the underlying `.func`s). -/
def Equiv (F G : ScatFun) : Prop :=
  Reduces F G ∧ Reduces G F

/-- Continuous equivalence is reflexive. -/
theorem Equiv.refl (F : ScatFun) : Equiv F F :=
  ⟨ContinuouslyReduces.refl F.func, ContinuouslyReduces.refl F.func⟩

/-- Continuous equivalence is symmetric. -/
theorem Equiv.symm {F G : ScatFun} (h : Equiv F G) : Equiv G F :=
  ⟨h.2, h.1⟩

/-- Continuous equivalence is transitive. -/
theorem Equiv.trans {F G H : ScatFun} (h1 : Equiv F G) (h2 : Equiv G H) : Equiv F H :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

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
