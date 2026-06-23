import WqoContinuousFunctions.PointedGluing.GeneralStructure
import BQO.TwoBQO
import BQO.OrdinalBQO
import WqoContinuousFunctions.ScatFun.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

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

end ScatFun
