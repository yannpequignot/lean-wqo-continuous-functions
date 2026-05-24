import WqoContinuousFunctions.BQO.TwoBQO
import WqoContinuousFunctions.BQO.OrdinalBQO
import WqoContinuousFunctions.ScatFun.ReflectLevel

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

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
