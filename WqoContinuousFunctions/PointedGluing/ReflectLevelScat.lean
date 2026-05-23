import Mathlib
import WqoContinuousFunctions.PointedGluing.GeneralStructure
import WqoContinuousFunctions.Bqo.TwoBQO
import WqoContinuousFunctions.Bqo.TwonLTmIsTwoBQO

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

/-!
## Co-homomorphism lemma
-/

/-- **Co-homomorphism lemma.**
The lifting map `f ↦ (CBRank f.func, f)` from `ScatFun` into the lex sum
`Σ β, ScatFun.Level β` is a co-homomorphism for continuous reducibility:
a bad pair-sequence in `ScatFun` lifts to a bad pair-sequence in the lex sum.

**Proof.** Suppose for contradiction that the lifted sequence has a good triple
`m < n < l`.  Two cases from `TwoBQO.LexSumRelQO`:
- `leBullet (CBRank F) (CBRank G)` with `CBRank F ≠ CBRank G`: the General
  Structure Theorem gives `ScatFun.Reduces F G`, contradicting `hbad`.
- `CBRank F = CBRank G` and `ScatFun.Reduces F G`: directly contradicts `hbad`.
-/
lemma liftToLex_bad
    (f : PairSeq ScatFun)
    (hbad : PairSeq.IsBad ScatFun.Reduces f) :
    PairSeq.IsBad
      (TwoBQO.LexSumRelQO Ordinal.leBullet (fun β => ScatFun.Level β)
                   (fun _ F G => ScatFun.Reduces F.val G.val))
      (fun m n h => (⟨CBRank (f m n h).func, (f m n h).toLevel⟩ :
                      Σ β : Ordinal.{0}, ScatFun.Level β)) := by
  have limitPart_le : ∀ α : Ordinal.{0}, α.limitPart ≤ α := fun α => by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  intro m n l hmn hnl hrel
  simp only [TwoBQO.LexSumRelQO, ScatFun.toLevel] at hrel
  set η := CBRank (f m n hmn).func with hη_def
  set ζ := CBRank (f n l hnl).func with hζ_def
  have hFsc : ScatteredFun (f m n hmn).func := (f m n hmn).hScat
  have hFct : Continuous    (f m n hmn).func := (f m n hmn).hCont
  have hGsc : ScatteredFun (f n l hnl).func  := (f n l hnl).hScat
  have hGct : Continuous    (f n l hnl).func  := (f n l hnl).hCont
  rcases hrel with ⟨hbul, hne⟩ | ⟨heq, htrel⟩
  · -- Case A: leBullet η ζ  and  η ≠ ζ.
    have hη_lt  : η < omega1 := CBRank_lt_omega1 hFsc
    have hη₀_lt : η.limitPart < omega1 :=
      lt_of_le_of_lt (limitPart_le η) hη_lt
    have hη₀_lim : Order.IsSuccLimit η.limitPart ∨ η.limitPart = 0 :=
      η.limitPart_isLimit_or_zero
    have hFrank : CBRank (f m n hmn).func = η.limitPart + ↑η.natPart :=
      Ordinal.eq_limitPart_add_natPart η
    rw [Ordinal.leBullet_iff_decomp] at hbul
    rcases hbul with hlt_lim | ⟨heqlim, htwoLT⟩
    · -- Sub-case A1: η.limitPart < ζ.limitPart.
      have hζlim_pos : ζ.limitPart ≠ 0 := by
        intro h0; rw [h0] at hlt_lim; simp at hlt_lim
      have hζlim_lim : Order.IsSuccLimit ζ.limitPart := by
        rcases ζ.limitPart_isLimit_or_zero with h | h
        · exact h
        · exact absurd h hζlim_pos
      have hbound : η.limitPart + 2 * ↑η.natPart < ζ.limitPart := by
        have h := limit_add_nat_lt ζ.limitPart hζlim_lim hζlim_pos
                    η.limitPart hlt_lim (2 * η.natPart)
        push_cast at h ⊢; exact h
      have hge : CBRank (f n l hnl).func ≥ η.limitPart + 2 * ↑η.natPart + 1 :=
        calc η.limitPart + 2 * ↑η.natPart + 1
            ≤ ζ.limitPart               := Order.succ_le_of_lt hbound
          _ ≤ ζ.limitPart + ↑ζ.natPart := le_self_add
          _ = ζ                         := (Ordinal.eq_limitPart_add_natPart ζ).symm
      exact hbad m n l hmn hnl
        ((general_structure_theorem
            (f m n hmn).domain (f n l hnl).domain
            (f m n hmn).func  (f n l hnl).func
            hFsc hGsc hFct hGct η.limitPart hη₀_lt hη₀_lim).2
          η.natPart ⟨hFrank, hge⟩)
    · -- Sub-case A2: η.limitPart = ζ.limitPart  and  TwoLT η.natPart ζ.natPart.
      rcases htwoLT with heqnat | hstrict
      · -- TwoLT equality: η = ζ, contradicts hne.
        exact hne (by
          calc η = η.limitPart + ↑η.natPart  := Ordinal.eq_limitPart_add_natPart η
            _ = ζ.limitPart + ↑ζ.natPart     := by rw [heqlim, heqnat]
            _ = ζ                             := (Ordinal.eq_limitPart_add_natPart ζ).symm)
      · -- TwoLT strict: 2 * η.natPart < ζ.natPart.
        have hGrank : CBRank (f n l hnl).func = η.limitPart + ↑ζ.natPart :=
          calc CBRank (f n l hnl).func
              = ζ                         := rfl
            _ = ζ.limitPart + ↑ζ.natPart := Ordinal.eq_limitPart_add_natPart ζ
            _ = η.limitPart + ↑ζ.natPart := by rw [heqlim]
        have hge : CBRank (f n l hnl).func ≥ η.limitPart + 2 * ↑η.natPart + 1 := by
          rw [hGrank]
          have hle : (2 * η.natPart + 1 : ℕ) ≤ ζ.natPart := hstrict
          have hcast : η.limitPart + 2 * (η.natPart : Ordinal) + 1
                     = η.limitPart + ↑(2 * η.natPart + 1) := by
            simp [Nat.cast_add, add_assoc]
          rw [hcast]; gcongr
        exact hbad m n l hmn hnl
          ((general_structure_theorem
              (f m n hmn).domain (f n l hnl).domain
              (f m n hmn).func  (f n l hnl).func
              hFsc hGsc hFct hGct η.limitPart hη₀_lt hη₀_lim).2
            η.natPart ⟨hFrank, hge⟩)
  · -- Case B: same CB-rank, fibre relation gives a ScatFun.Reduces step.
    -- htrel : ScatFun.Reduces ⟨f m n hmn, rfl⟩.val (heq ▸ ⟨f n l hnl, rfl⟩).val
    -- cast_val: (heq ▸ ⟨f n l hnl, rfl⟩).val = f n l hnl
    apply hbad m n l hmn hnl
    simp only [ScatFun.Level.cast_val] at htrel
    exact htrel

/-!
## Main theorem: every bad pair-sequence restricts to a single level

**Proposition (FGgivesBQO_2).**
If `𝒞_β` is 2-BQO for all `β < α`, then `𝒞_{<α}` is 2-BQO.

**Proof.** By `ScatFun.liftToLex_bad`, `hbad` implies the lifted sequence is
bad in the lex sum.  `TwoBQO.lexSigmaQO_reflect` forces it to concentrate on a
single level β (bad-index branch ruled out by `Ordinal.leBullet.isTwoBQO`).
-/
theorem bad_restricts_to_level
    (f : PairSeq ScatFun)
    (hbad : PairSeq.IsBad ScatFun.Reduces f) :
    ∃ (β : Ordinal.{0}) (_ : β < omega1)
      (e : ℕ → ℕ) (he : StrictMono e),
      PairSeq.IsBad ScatFun.Reduces (PairSeq.restrict f e he) ∧
      ∀ m n (h : m < n), CBRank (PairSeq.restrict f e he m n h).func = β := by
  let t : ∀ (β : Ordinal.{0}), ScatFun.Level β → ScatFun.Level β → Prop :=
    fun _ F G => ScatFun.Reduces F.val G.val
  let f_lex : PairSeq (Σ β : Ordinal.{0}, ScatFun.Level β) :=
    fun m n h => ⟨CBRank (f m n h).func, (f m n h).toLevel⟩
  obtain ⟨e, he, hbad_idx | ⟨β, hmem, hbad_fib⟩⟩ :=
    TwoBQO.lexSigmaQO_reflect
      Ordinal.leBullet
      (fun β => ScatFun.Level β)
      t
      f_lex
      (ScatFun.liftToLex_bad f hbad)
  · -- Bad-index branch: contradicts Ordinal.leBullet.isTwoBQO.
    obtain ⟨m, n, l, hmn, hnl, hrel⟩ :=
      Ordinal.leBullet.isTwoBQO (fun m n hmn => (f_lex (e m) (e n) (he hmn)).1)
    exact absurd hrel (hbad_idx m n l hmn hnl)
  · -- Constant-fibre branch: all pairs along e have CB-rank β.
    have hβ_lt : β < omega1 := by
      have h01 := hmem 0 1 (by norm_num)
      simp only [f_lex] at h01
      rw [← h01]
      exact CBRank_lt_omega1 (f (e 0) (e 1) (he (by norm_num))).hScat
    refine ⟨β, hβ_lt, e, he, ?_, ?_⟩
    · -- Restricted sequence is bad for ScatFun.Reduces.
      intro m n l hmn hnl hrel
      apply hbad_fib m n l hmn hnl
      simp only [t, f_lex, ScatFun.toLevel, ScatFun.Level.cast_val]
      exact hrel
    · -- Every pair along e has CB-rank β.
      intro m n h
      have := hmem m n h
      simp only [f_lex] at this
      exact this

/-!
Here is the final step of the proof of `FGgivesBQO_2`:
if there are no bad pair-sequences
-/
theorem Level.no_bad (β : Ordinal.{0}) (hβ : β < omega1)
    (ih : ¬ ∃ f : PairSeq (ScatFun.LevelLT β), PairSeq.IsBad (ScatFun.LevelLT.reduces β) f)
    : ¬ ∃ f : PairSeq (ScatFun.Level β), PairSeq.IsBad (ScatFun.Level.reduces β) f := by
    sorry

/-!
## Assembling the proof of MainTheorem3

The next three declarations assemble `ScatFun.bad_restricts_to_level` and
`ScatFun.Level.no_bad` into the full theorem.

**Proof architecture.**

1. `ScatFun.no_bad_all_levels` — transfinite induction on `β < ω₁`:
   assume no bad sequence exists at any level `γ < β` (induction hypothesis),
   show no bad sequence exists at level `β`.
   The inductive step consists of providing the `ih` that `ScatFun.Level.no_bad` expects:
   if a bad `PairSeq (ScatFun.LevelLT β)` existed, we would coerce it to
   `PairSeq ScatFun`, apply `ScatFun.bad_restricts_to_level` to land at some level `γ`,
   observe `γ < β` from the membership bound, and contradict the induction hypothesis.

2. `ScatFun.Reduces.isTwoBQO` — if a bad `PairSeq ScatFun` existed,
   `ScatFun.bad_restricts_to_level` would produce a bad sequence at some level `β < ω₁`,
   contradicting `ScatFun.no_bad_all_levels β`.

3. `ScatFun.Reduces.isWQO` — WQO corollary via `TwoBQO.wellQuasiOrdered`.
-/

/-- **Auxiliary (transfinite induction).** For every `β < ω₁`, there is no bad
pair-sequence in `ScatFun.Level β`. The proof is by strong transfinite induction
on `β`, using `ScatFun.Level.no_bad` as the inductive step. -/
theorem no_bad_all_levels (β : Ordinal.{0}) (hβ : β < omega1) :
    ¬ ∃ f : PairSeq (ScatFun.Level β), PairSeq.IsBad (ScatFun.Level.reduces β) f := by
  revert hβ
  induction β using Ordinal.induction with
  | h β ih_β =>
    intro hβ
    -- Apply ScatFun.Level.no_bad; it suffices to supply the inductive hypothesis,
    -- i.e., that no bad pair-sequence exists in ScatFun.LevelLT β.
    apply ScatFun.Level.no_bad β hβ
    intro ⟨f, hbad⟩
    -- Coerce f : PairSeq (ScatFun.LevelLT β) to a PairSeq ScatFun by forgetting the bound.
    let g : PairSeq ScatFun := fun m n h => (f m n h).val
    have hbad_g : PairSeq.IsBad ScatFun.Reduces g :=
      fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel
    -- ScatFun.bad_restricts_to_level gives a level γ < ω₁ and a bad restriction there.
    obtain ⟨γ, hγ_ω1, e, he, hbad_γ, hrank⟩ := ScatFun.bad_restricts_to_level g hbad_g
    -- Since every element of f has CB-rank < β, we get γ < β.
    have hγ_lt_β : γ < β :=
      -- hrank 0 1 h : CBRank (f (e 0) (e 1) (he h)).val.func = γ
      -- (f (e 0) (e 1) (he h)).prop : CBRank (f (e 0) (e 1) (he h)).val.func < β
      hrank 0 1 (by norm_num : (0:ℕ) < 1) ▸
        (f (e 0) (e 1) (he (by norm_num : (0:ℕ) < 1))).prop
    -- Build a bad pair-sequence at level γ and contradict the induction hypothesis.
    let f_γ : PairSeq (ScatFun.Level γ) :=
      fun m n h => ⟨PairSeq.restrict g e he m n h, hrank m n h⟩
    exact ih_β γ hγ_lt_β (hγ_lt_β.trans hβ)
      ⟨f_γ, fun m n l hmn hnl hrel => hbad_γ m n l hmn hnl hrel⟩

end ScatFun

/-- **Main Theorem 3 for ScatFun — 2-BQO strengthening.**
Continuous reducibility is a 2-BQO on scattered continuous functions from
subsets of Baire space to Baire space (i.e., on `ScatFun`).

This is the specialisation of Theorem 1.5 of the memoir to `ScatFun`.
It is stronger than WQO: every pair-sequence has a good triple.

**Proof.** If a bad `PairSeq ScatFun` existed, `ScatFun.bad_restricts_to_level`
would produce a bad sequence at some level `β < ω₁`, contradicting
`ScatFun.no_bad_all_levels`. -/
theorem ScatFun.Reduces.isTwoBQO : TwoBQO ScatFun.Reduces := by
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  obtain ⟨β, hβ, e, he, hbad_level, hrank⟩ := ScatFun.bad_restricts_to_level f hbad
  let f_β : PairSeq (ScatFun.Level β) :=
    fun m n h => ⟨PairSeq.restrict f e he m n h, hrank m n h⟩
  exact ScatFun.no_bad_all_levels β hβ
    ⟨f_β, fun m n l hmn hnl hrel => hbad_level m n l hmn hnl hrel⟩

/-- **Main Theorem 3 for ScatFun — WQO version.**
Continuous reducibility is a well-quasi-order on `ScatFun`.

This is the specialisation of `MainTheorem3` (in `IntroMemo.lean`) to the
class `ScatFun` of scattered continuous functions `A → (ℕ → ℕ)` where
`A : Set (ℕ → ℕ)`. It follows immediately from the stronger `ScatFun.Reduces.isTwoBQO`. -/
theorem ScatFun.Reduces.isWQO : WellQuasiOrdered ScatFun.Reduces :=
  TwoBQO.wellQuasiOrdered ScatFun.Reduces.isTwoBQO
