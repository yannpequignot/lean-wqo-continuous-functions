import BQO.TwoBQO
import BQO.OrdinalBQO
import WqoContinuousFunctions.ScatFun.ReflectLevel
import WqoContinuousFunctions.ScatFun.FiniteGluing

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Assembling the proof of MainTheorem3 (2-BQO of `ScatFun`)

**Proof architecture.**  The whole result rests on the structural input
`levels_finitely_generated` (in `MainResults/Main.lean`):

1. `ScatFun.Level.isTwoBQO` — each CB-rank level `α < ω₁` is 2-BQO.  By
   `levels_finitely_generated` the level embeds into a single `FinGl B`, which is
   2-BQO by `ScatFun.FinGl.isTwoBQO`; pull back with `TwoBQO.comap`.

2. `levels_no_bad` — the `iff_noBad` reformulation of (1): no bad pair-sequence at
   any level.

3. `ScatFun.Reduces.isTwoBQO` — `ScatFun.bad_restricts_to_level` reflects any bad
   `PairSeq ScatFun` onto a single level `β < ω₁`, where (2) forbids it.  In other
   words, `bad_restricts_to_level` is exactly the statement that
   `ScatFun.Level.isTwoBQO` (all levels 2-BQO) implies `ScatFun.Reduces.isTwoBQO`.

4. `ScatFun.Reduces.isWQO` — WQO corollary via `TwoBQO.wellQuasiOrdered`.

This replaces the earlier transfinite-induction route (`no_bad_all_levels` resting
on the `ScatFun.Level.no_bad` inductive step): the induction is now encapsulated in
the eventual proof of `levels_finitely_generated`, and the order-theoretic glue is
the single reflection lemma `bad_restricts_to_level`.
-/

/-- **Each CB-rank level is 2-BQO.**  By `levels_finitely_generated` the whole
level `α` embeds into a single `FinGl B`, which is 2-BQO by `ScatFun.FinGl.isTwoBQO`;
pull back along the inclusion `Level α ↪ FinGl B` with `TwoBQO.comap`. -/
theorem ScatFun.Level.isTwoBQO (α : Ordinal.{0}) (hα : α < omega1) :
    TwoBQO (ScatFun.Level.reduces α) := by
  obtain ⟨n, B, hB⟩ := ScatFun.levels_finitely_generated α hα
  exact (ScatFun.FinGl.isTwoBQO B).comap
    (fun F : ScatFun.Level α => ⟨F.val, hB F.val F.prop⟩)

/-- **No bad pair-sequence at any level**, the `iff_noBad` form of
`ScatFun.Level.isTwoBQO`. -/
theorem levels_no_bad (α : Ordinal.{0}) (hα : α < omega1) :
    ¬ ∃ f : PairSeq (ScatFun.Level α), PairSeq.IsBad (ScatFun.Level.reduces α) f :=
  (TwoBQO.iff_noBad _).mp (ScatFun.Level.isTwoBQO α hα)

/-- **Main Theorem 3 for ScatFun — 2-BQO strengthening.**
Continuous reducibility is a 2-BQO on scattered continuous functions from
subsets of Baire space to Baire space (i.e., on `ScatFun`).

This is the specialisation of Theorem 1.5 of the memoir to `ScatFun`.
It is stronger than WQO: every pair-sequence has a good triple.

**Proof.** If a bad `PairSeq ScatFun` existed, `ScatFun.bad_restricts_to_level`
would reflect it onto a single level `β < ω₁`, contradicting `levels_no_bad β`
(i.e. `ScatFun.Level.isTwoBQO β`). -/
theorem ScatFun.Reduces.isTwoBQO : TwoBQO ScatFun.Reduces := by
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  obtain ⟨β, hβ, e, he, hbad_level, hrank⟩ := ScatFun.bad_restricts_to_level f hbad
  let f_β : PairSeq (ScatFun.Level β) :=
    fun m n h => ⟨PairSeq.restrict f e he m n h, hrank m n h⟩
  exact levels_no_bad β hβ
    ⟨f_β, fun m n l hmn hnl hrel => hbad_level m n l hmn hnl hrel⟩

/-- **Main Theorem 3 for ScatFun — WQO version.**
Continuous reducibility is a well-quasi-order on `ScatFun`.

This is the specialisation of `MainTheorem3` (in `IntroMemo.lean`) to the
class `ScatFun` of scattered continuous functions `A → (ℕ → ℕ)` where
`A : Set (ℕ → ℕ)`. It follows immediately from the stronger `ScatFun.Reduces.isTwoBQO`. -/
theorem ScatFun.Reduces.isWQO : WellQuasiOrdered ScatFun.Reduces :=
  TwoBQO.wellQuasiOrdered ScatFun.Reduces.isTwoBQO
