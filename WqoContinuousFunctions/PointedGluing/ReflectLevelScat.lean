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

**Design note.** `ScatFun_level β` is a *subtype* of `ScatFun`, not an
independent sigma type.  This means the underlying `ScatFun` is accessed
via `.val` without any `Eq.rec` cast, and the only cast lemma needed is
`ScatFun_level.cast_val`.
-/

/-- A **scattered continuous function** on Baire space: a domain set together
    with a continuous scattered function on that domain. -/
structure ScatFun where
  domain : Set Baire
  func   : ↑domain → Baire
  hScat  : ScatteredFun func
  hCont  : Continuous func

/-- The **level-β fragment**: scattered continuous functions of CB-rank `β`.
    Defined as a subtype of `ScatFun` so that `.val` recovers the underlying
    function without any cast. -/
def ScatFun_level (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func = β }

def ScatFun_level_le (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func ≤ β }

def ScatFun_level_lt (β : Ordinal.{0}) : Type :=
  { F : ScatFun // CBRank F.func < β }

/-- Continuous reducibility between two `ScatFun`s. -/
def scatReduces (F G : ScatFun) : Prop :=
  ContinuouslyReduces F.func G.func

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def scatReduces_level (β : Ordinal.{0}) :
    ScatFun_level β → ScatFun_level β → Prop :=
  fun F G => scatReduces F.val G.val

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def scatReduces_level_le (β : Ordinal.{0}) :
    ScatFun_level_le β → ScatFun_level_le β → Prop :=
  fun F G => scatReduces F.val G.val

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def scatReduces_level_lt (β : Ordinal.{0}) :
    ScatFun_level_lt β → ScatFun_level_lt β → Prop :=
  fun F G => scatReduces F.val G.val
/-! ## Cast lemma -/

/-- Casting a `ScatFun_level` element does not change the underlying `ScatFun`.
    This is the only cast lemma needed in the whole development. -/
lemma ScatFun_level.cast_val {α β : Ordinal.{0}} (h : α = β) (F : ScatFun_level α) :
    (h ▸ F).val = F.val := by subst h; rfl

/-! ## Embedding into the sigma type `Σ β, ScatFun_level β` -/

/-- Embed `F : ScatFun` into the level of its CB-rank. -/
@[reducible] def ScatFun.toLevel (F : ScatFun) : ScatFun_level (CBRank F.func) :=
  ⟨F, rfl⟩

/-- The canonical equivalence between `ScatFun` and `Σ β, ScatFun_level β`. -/
def ScatFun.equivSigmaLevel : ScatFun ≃ Σ β : Ordinal.{0}, ScatFun_level β where
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
`Σ β, ScatFun_level β` is a co-homomorphism for continuous reducibility:
a bad pair-sequence in `ScatFun` lifts to a bad pair-sequence in the lex sum.

**Proof.** Suppose for contradiction that the lifted sequence has a good triple
`m < n < l`.  Two cases from `LexSumRelQO`:
- `leBullet (CBRank F) (CBRank G)` with `CBRank F ≠ CBRank G`: the General
  Structure Theorem gives `scatReduces F G`, contradicting `hbad`.
- `CBRank F = CBRank G` and `scatReduces F G`: directly contradicts `hbad`.
-/
lemma scatFun_liftToLex_bad
    (f : PairSeq ScatFun)
    (hbad : BadPairSeq scatReduces f) :
    BadPairSeq
      (LexSumRelQO Ordinal.leBullet (fun β => ScatFun_level β)
                   (fun _ F G => scatReduces F.val G.val))
      (fun m n h => (⟨CBRank (f m n h).func, (f m n h).toLevel⟩ :
                      Σ β : Ordinal.{0}, ScatFun_level β)) := by
  have limitPart_le : ∀ α : Ordinal.{0}, α.limitPart ≤ α := fun α => by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  intro m n l hmn hnl hrel
  simp only [LexSumRelQO, ScatFun.toLevel] at hrel
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
  · -- Case B: same CB-rank, fibre relation gives a scatReduces step.
    -- htrel : scatReduces ⟨f m n hmn, rfl⟩.val (heq ▸ ⟨f n l hnl, rfl⟩).val
    -- cast_val: (heq ▸ ⟨f n l hnl, rfl⟩).val = f n l hnl
    apply hbad m n l hmn hnl
    simp only [ScatFun_level.cast_val] at htrel
    exact htrel

/-!
## Main theorem: every bad pair-sequence restricts to a single level

**Proposition (FGgivesBQO_2).**
If `𝒞_β` is 2-BQO for all `β < α`, then `𝒞_{<α}` is 2-BQO.

**Proof.** By `scatFun_liftToLex_bad`, `hbad` implies the lifted sequence is
bad in the lex sum.  `TwoBQO.lexSigmaQO_reflect` forces it to concentrate on a
single level β (bad-index branch ruled out by `Ordinal.leBullet.TwoBQO`).
-/
theorem bad_pairseq_restricts_to_level
    (f : PairSeq ScatFun)
    (hbad : BadPairSeq scatReduces f) :
    ∃ (β : Ordinal.{0}) (_ : β < omega1)
      (e : ℕ → ℕ) (he : StrictMono e),
      BadPairSeq scatReduces (restrictPairSeq f e he) ∧
      ∀ m n (h : m < n), CBRank (restrictPairSeq f e he m n h).func = β := by
  let t : ∀ (β : Ordinal.{0}), ScatFun_level β → ScatFun_level β → Prop :=
    fun _ F G => scatReduces F.val G.val
  let f_lex : PairSeq (Σ β : Ordinal.{0}, ScatFun_level β) :=
    fun m n h => ⟨CBRank (f m n h).func, (f m n h).toLevel⟩
  obtain ⟨e, he, hbad_idx | ⟨β, hmem, hbad_fib⟩⟩ :=
    TwoBQO.lexSigmaQO_reflect
      Ordinal.leBullet
      (fun i j h1 h2 => Ordinal.leBullet_antisymm h1 h2)
      (fun β => ScatFun_level β)
      t
      f_lex
      (scatFun_liftToLex_bad f hbad)
  · -- Bad-index branch: contradicts Ordinal.leBullet.TwoBQO.
    obtain ⟨m, n, l, hmn, hnl, hrel⟩ :=
      Ordinal.leBullet.TwoBQO (fun m n hmn => (f_lex (e m) (e n) (he hmn)).1)
    exact absurd hrel (hbad_idx m n l hmn hnl)
  · -- Constant-fibre branch: all pairs along e have CB-rank β.
    have hβ_lt : β < omega1 := by
      have h01 := hmem 0 1 (by norm_num)
      simp only [f_lex, ScatFun.toLevel] at h01
      rw [← h01]
      exact CBRank_lt_omega1 (f (e 0) (e 1) (he (by norm_num))).hScat
    refine ⟨β, hβ_lt, e, he, ?_, ?_⟩
    · -- Restricted sequence is bad for scatReduces.
      intro m n l hmn hnl hrel
      apply hbad_fib m n l hmn hnl
      simp only [t, f_lex, ScatFun.toLevel, ScatFun_level.cast_val]
      exact hrel
    · -- Every pair along e has CB-rank β.
      intro m n h
      have := hmem m n h
      simp only [f_lex, ScatFun.toLevel] at this
      exact this

/-!
Here is the final step of the proof of `FGgivesBQO_2`:
if there are no bad pair-sequences
-/
theorem no_bad_pairseq_level (β : Ordinal.{0}) (hβ : β < omega1)
    (ih : ¬ ∃ f : PairSeq (ScatFun_level_lt β), BadPairSeq (scatReduces_level_lt β) f)
    : ¬ ∃ f : PairSeq (ScatFun_level β), BadPairSeq (scatReduces_level β) f := by
    sorry
