import WqoContinuousFunctions.BQO.TwoBQO
import WqoContinuousFunctions.BQO.OrdinalBQO
import WqoContinuousFunctions.ScatFun.LiftToLex

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

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


end ScatFun
