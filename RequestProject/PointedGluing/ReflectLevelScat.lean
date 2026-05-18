import Mathlib
import RequestProject.PointedGluing.GeneralStructure
import RequestProject.Bqo.TwoBQO
import RequestProject.Bqo.TwonLTmIsTwoBQO

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

/-- Continuous reducibility between two `ScatFun`s. -/
def scatReduces (F G : ScatFun) : Prop :=
  ContinuouslyReduces F.func G.func

/-- Level-wise reduction: forget to `ScatFun` via `.val`. -/
@[reducible] def scatReduces_level (β : Ordinal.{0}) :
    ScatFun_level β → ScatFun_level β → Prop :=
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
## Main theorem: every bad pair-sequence restricts to a single level

**Proposition (FGgivesBQO_2).**
If `𝒞_β` is 2-BQO for all `β < α`, then `𝒞_{<α}` is 2-BQO.

**Proof sketch.**
The map `f ↦ (CBRank f.func, f)` into `Σ β, ScatFun_level β` with the
lexicographic order `LexSumRelQO Ordinal.leBullet _ t` is a co-homomorphism
for continuous reducibility (by the General Structure Theorem).
So any bad pair-sequence in `ScatFun` lifts to a bad pair-sequence in the
lex sum.  By `TwoBQO.lexSigmaQO_reflect`, this restricts either to a bad
sequence in `Ordinal.leBullet` (impossible, since it is 2-BQO) or to a bad
sequence concentrated on a single level β.
-/
theorem bad_pairseq_restricts_to_level
    (f : PairSeq ScatFun)
    (hbad : BadPairSeq scatReduces f) :
    ∃ (β : Ordinal.{0}) (_ : β < omega1)
      (e : ℕ → ℕ) (he : StrictMono e),
      BadPairSeq scatReduces (restrictPairSeq f e he) ∧
      ∀ m n (h : m < n), CBRank (restrictPairSeq f e he m n h).func = β := by
  -- The fibre relation: reduction at a fixed level β.
  -- Using `scatReduces F.val G.val` means `ScatFun_level.cast_val` eliminates
  -- every `Eq.rec` cast that arises from `LexSumRelQO`.
  let t : ∀ (β : Ordinal.{0}), ScatFun_level β → ScatFun_level β → Prop :=
    fun _ F G => scatReduces F.val G.val
  -- Lift f to the lex sum by tagging each pair with its CB-rank.
  let f_lex : PairSeq (Σ β : Ordinal.{0}, ScatFun_level β) :=
    fun m n h => ⟨CBRank (f m n h).func, ⟨f m n h, rfl⟩⟩
  have limitPart_le : ∀ α : Ordinal.{0}, α.limitPart ≤ α := fun α => by
    conv_rhs => rw [Ordinal.eq_limitPart_add_natPart α]
    exact le_self_add
  -- ---------------------------------------------------------------
  -- Step 1.  `f_lex` is bad for `LexSumRelQO Ordinal.leBullet _ t`.
  -- ---------------------------------------------------------------
  have hlex_bad : BadPairSeq (LexSumRelQO Ordinal.leBullet _ t) f_lex := by
    intro m n l hmn hnl hrel
    simp only [f_lex, LexSumRelQO] at hrel
    set η := CBRank (f m n hmn).func with hη_def
    set ζ := CBRank (f n l hnl).func with hζ_def
    have hFsc : ScatteredFun (f m n hmn).func := (f m n hmn).hScat
    have hFct : Continuous    (f m n hmn).func := (f m n hmn).hCont
    have hGsc : ScatteredFun (f n l hnl).func  := (f n l hnl).hScat
    have hGct : Continuous    (f n l hnl).func  := (f n l hnl).hCont
    rcases hrel with ⟨hbul, hne⟩ | ⟨heq, htrel⟩
    · -- Case A: Ordinal.leBullet η ζ  and  η ≠ ζ.
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
        · -- TwoLT equality branch: η = ζ, contradicts hne.
          exact hne (by
            calc η = η.limitPart + ↑η.natPart  := Ordinal.eq_limitPart_add_natPart η
              _ = ζ.limitPart + ↑ζ.natPart     := by rw [heqlim, heqnat]
              _ = ζ                             := (Ordinal.eq_limitPart_add_natPart ζ).symm)
        · -- TwoLT strict branch: 2 * η.natPart < ζ.natPart.
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
    · -- Case B: same CB-rank, the fibre relation gives a scatReduces step.
      -- `htrel : t η ⟨f m n hmn, rfl⟩ (heq ▸ ⟨f n l hnl, rfl⟩)`
      -- Unfolding `t` and applying `cast_val` shows this is exactly
      -- `scatReduces (f m n hmn) (f n l hnl)`.
      apply hbad m n l hmn hnl
      simp only [t, ScatFun_level.cast_val] at htrel
      exact htrel
  -- ---------------------------------------------------------------
  -- Step 2.  Apply `TwoBQO.lexSigmaQO_reflect`.
  -- ---------------------------------------------------------------
  obtain ⟨e, he, hbad_idx | ⟨β, hmem, hbad_fib⟩⟩ :=
    TwoBQO.lexSigmaQO_reflect
      Ordinal.leBullet
      (fun i j h1 h2 => Ordinal.leBullet_antisymm h1 h2)
      (fun β => ScatFun_level β)
      t
      f_lex
      hlex_bad
  · -- Bad-index branch: `Ordinal.leBullet` is 2-BQO, contradiction.
    obtain ⟨m, n, l, hmn, hnl, hrel⟩ :=
      Ordinal.leBullet.TwoBQO (fun m n hmn => (f_lex (e m) (e n) (he hmn)).1)
    exact absurd hrel (hbad_idx m n l hmn hnl)
  · -- Constant-fibre branch: all pairs along `e` have CB-rank `β`.
    have hβ_lt : β < omega1 := by
      have h01 := hmem 0 1 (by norm_num)
      simp only [f_lex] at h01
      rw [← h01]
      exact CBRank_lt_omega1 (f (e 0) (e 1) (he (by norm_num))).hScat
    refine ⟨β, hβ_lt, e, he, ?_, ?_⟩
    · -- The restricted sequence is bad for `scatReduces`.
      -- `hbad_fib` expects `t β (cast F_mn) (cast F_nl)`.
      -- Unfolding `t` and applying `cast_val` reduces this to
      -- `scatReduces (f (e m) (e n) _) (f (e n) (e l) _)` = `hrel`.
      intro m n l hmn hnl hrel
      apply hbad_fib m n l hmn hnl
      simp only [t, f_lex, ScatFun_level.cast_val]
      exact hrel
    · -- Every pair along `e` has CB-rank equal to `β`.
      intro m n h
      have := hmem m n h
      simp only [f_lex] at this
      exact this

/-!
Here is the final step of the proof of `FGgivesBQO_2`:
if there are no bad pair-sequences
-/
theorem no_bad_pairseq_level (β : Ordinal.{0}) (hβ : β < omega1)
    (ih : ∀ γ < β, ¬ ∃ f : PairSeq (ScatFun_level γ), BadPairSeq scatReduces_level f)
    : ¬ ∃ f : PairSeq (ScatFun_level β), BadPairSeq scatReduces_level f := by
    sorry
