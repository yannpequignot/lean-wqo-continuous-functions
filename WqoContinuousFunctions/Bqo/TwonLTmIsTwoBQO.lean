import Mathlib
import WqoContinuousFunctions.PrelimMemo.Basic
import WqoContinuousFunctions.Bqo.Ramsey
import WqoContinuousFunctions.Bqo.TwoBQO
import WqoContinuousFunctions.Ordinals.Arithmetic

open Set

set_option autoImplicit false

/-!
# 2n < m implies Two-BQO

This file proves that continuous reducibility restricted to functions
with certain CB-rank bounds forms a better-quasi-order.
-/

noncomputable section

open Classical

/-- `n ≤₂ m` iff `n = m` or `2 * n < m` -/
def TwoLT (n m : ℕ) : Prop := n = m ∨ 2 * n < m

notation:50 n " ≤₂ " m => TwoLT n m

namespace TwoLT
/--
We define and prove that the partial order TwoLT is 2-Bqo
-/

theorem refl (n : ℕ) : n ≤₂ n := Or.inl rfl

theorem antisymm {n m : ℕ} (h : n ≤₂ m) (h' : m ≤₂ n) : n = m := by
  rcases h with rfl | h
  · rfl
  · rcases h' with rfl | h'
    · rfl
    · omega

theorem trans {n m k : ℕ} (h : n ≤₂ m) (h' : m ≤₂ k) : n ≤₂ k := by
  rcases h with rfl | h
  · exact h'
  · rcases h' with rfl | h'
    · exact Or.inr h
    · exact Or.inr (by omega)

end TwoLT

theorem TwoLT.constant_or_strict (f : ℕ → ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
    ((∃ k : ℕ, ∀ n, f (e n) = k) ∨
     (∀ m n, m < n → 2 * f (e m) < f (e n))) := by
  -- Case: is the range of f bounded or not?
  by_cases hbdd : ∃ M, ∀ n, f n ≤ M
  · -- BOUNDED CASE: range finite, apply pigeonhole to get constant subsequence.
    obtain ⟨M, hM⟩ := hbdd
    -- Factor f through Fin (M + 1)
    let f' : ℕ → Fin (M + 1) := fun n => ⟨f n, Nat.lt_succ_of_le (hM n)⟩
    obtain ⟨e, he, k, hk⟩ := infinite_pigeonhole' f'
    refine ⟨e, he, Or.inl ⟨k.val, fun n => ?_⟩⟩
    have := hk n
    simp only [f'] at this
    exact congrArg Fin.val this
  · -- UNBOUNDED CASE: ∀ M, ∃ n, f n > M.
    -- Build e by recursion: e 0 = 0, e (n+1) chosen so that
    --   e (n+1) > e n  AND  f (e (n+1)) > 2 * f (e n).
    push_neg at hbdd
    have hstep : ∀ j v, ∃ k, j < k ∧ v < f k := by
      intro j v
      by_contra h
      push_neg at h
      -- h : ∀ k > j, f k ≤ v
      -- Then f is bounded by max v (sup_{i ≤ j} f i)
      let B := max v (Finset.sup (Finset.range (j + 1)) f)
      obtain ⟨n, hn⟩ := hbdd B
      by_cases hjn : n ≤ j
      · have : f n ≤ Finset.sup (Finset.range (j + 1)) f :=
          Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjn))
        omega
      · push_neg at hjn
        have : f n ≤ v := h n hjn
        omega
    -- Build e recursively.
    -- At each step we need k > e n and f k > 2 * f (e n).
    -- Package the invariant: we track the current index.
    let e : ℕ → ℕ := fun n => Nat.rec 0
      (fun n prev => Nat.find (hstep prev (2 * f prev))) n
    -- The spec at each successor step.
    let e : ℕ → ℕ := fun n => Nat.rec 0
      (fun _ prev => Classical.choose (hstep prev (2 * f prev))) n
    have he_spec : ∀ n, e n < e (n + 1) ∧ 2 * f (e n) < f (e (n + 1)) := fun n =>
      Classical.choose_spec (hstep (e n) (2 * f (e n)))
    -- e is strictly monotone.
    have he_mono : StrictMono e :=
      strictMono_nat_of_lt_succ (fun n => (he_spec n).1)
    -- The doubling property extends to all m < n by induction.
    have he_double : ∀ m n, m < n → 2 * f (e m) < f (e n) := by
      intro m n hmn
      induction hmn with
      | refl =>
        -- base: 2 * f(e m) < f(e (m+1))
        exact (he_spec m).2
      | @step n hmn ih =>
        have h1 := (he_spec n).2  -- 2 * f(e n) < f(e(n+1))
        have h2 : f (e n) ≤ 2 * f (e n) := Nat.le_mul_of_pos_left _ (by norm_num)
        exact Nat.lt_trans ih (Nat.lt_of_le_of_lt h2 h1)
    exact ⟨e, he_mono, Or.inr he_double⟩

private structure PairSeqState (f : PairSeq ℕ) where
  vert  : ℕ
  succ  : Set ℕ
  hInf  : succ.Infinite
  hgt   : ∀ x ∈ succ, vert < x
  prop  : (∃ k : ℕ, ∀ x ∈ succ, ∀ h : vert < x, f vert x h = k) ∨
          (∀ x ∈ succ, ∀ y ∈ succ, ∀ (hx : vert < x) (hy : vert < y),
            x < y → 2 * f vert x hx < f vert y hy)

theorem TwoLT.pairSeqCanon_weak (f : PairSeq ℕ) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
    ∀ n : ℕ,
      (∃ k : ℕ, ∀ m (hmn : n < m), f (e n) (e m) (he hmn) = k) ∨
      (∀ m l (hnm : n < m) (hml : m < l),
        2 * f (e n) (e m) (he hnm) < f (e n) (e l) (he (hnm.trans hml))) := by
  have step : ∀ s : PairSeqState f, ∃ s' : PairSeqState f,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, S, hSinf, hSgt, _⟩
    set a' := Nat.find hSinf.nonempty
    have ha'S  : a' ∈ S := Nat.find_spec hSinf.nonempty
    have ha'min : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.find_min' hSinf.nonempty hx
    have hTinf : (S \ {a'}).Infinite := hSinf.diff (Set.finite_singleton a')
    have hTgt : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
      Nat.lt_of_le_of_ne (ha'min x hxS) (fun h => hxne (h ▸ rfl))
    obtain ⟨enum, henum_mono, henum_mem⟩ := hTinf.exists_strictMono
    let fan : ℕ → ℕ := fun n => f a' (enum n) (hTgt _ (henum_mem n))
    obtain ⟨idx, hidx, hconst | hdouble⟩ := constant_or_strict fan
    · obtain ⟨k, hk⟩ := hconst
      exact ⟨⟨a', Set.range (enum ∘ idx),
        Set.infinite_range_of_injective (henum_mono.comp hidx).injective,
        fun x hx => by obtain ⟨n, rfl⟩ := hx; exact hTgt _ (henum_mem (idx n)),
        Or.inl ⟨k, fun x hx _ => by obtain ⟨n, rfl⟩ := hx; exact hk n⟩⟩,
        ha'S,
        fun x hx => by obtain ⟨n, rfl⟩ := hx; exact (henum_mem (idx n)).1⟩
    · exact ⟨⟨a', Set.range (enum ∘ idx),
        Set.infinite_range_of_injective (henum_mono.comp hidx).injective,
        fun x hx => by obtain ⟨n, rfl⟩ := hx; exact hTgt _ (henum_mem (idx n)),
        Or.inr fun x hx y hy _ _ hxy => by
          obtain ⟨m, rfl⟩ := hx
          obtain ⟨n, rfl⟩ := hy
          exact hdouble m n ((henum_mono.comp hidx).lt_iff_lt.mp hxy)⟩,
        ha'S,
        fun x hx => by obtain ⟨n, rfl⟩ := hx; exact (henum_mem (idx n)).1⟩
  -- Initial state
  have hTinf₀ : (Set.Ioi 0 : Set ℕ).Infinite :=
    Set.infinite_of_injective_forall_mem Nat.succ_injective (fun n => Nat.succ_pos n)
  obtain ⟨enum₀, henum₀, henum₀_mem⟩ := hTinf₀.exists_strictMono
  let fan₀ : ℕ → ℕ := fun n => f 0 (enum₀ n) (henum₀_mem n)
  obtain ⟨idx₀, hidx₀, hprop₀⟩ := constant_or_strict fan₀
  let s₀ : PairSeqState f := ⟨0, Set.range (enum₀ ∘ idx₀),
    Set.infinite_range_of_injective (henum₀.comp hidx₀).injective,
    fun x hx => by obtain ⟨n, rfl⟩ := hx; exact henum₀_mem (idx₀ n),
    hprop₀.imp
      (fun ⟨k, hk⟩ => ⟨k, fun x hx _ => by obtain ⟨n, rfl⟩ := hx; exact hk n⟩)
      (fun hd x hx y hy _ _ hxy => by
        obtain ⟨m, rfl⟩ := hx
        obtain ⟨n, rfl⟩ := hy
        exact hd m n ((henum₀.comp hidx₀).lt_iff_lt.mp hxy))⟩
  -- Iterate
  let states : ℕ → PairSeqState f :=
    fun n => n.rec s₀ (fun _ s => (step s).choose)
  have I1 : ∀ n, (states (n+1)).vert ∈ (states n).succ :=
    fun n => (step (states n)).choose_spec.1
  have I2 : ∀ n, (states (n+1)).succ ⊆ (states n).succ :=
    fun n => (step (states n)).choose_spec.2
  have I3 : ∀ n, (states n).vert < (states (n+1)).vert :=
    fun n => (states n).hgt _ (I1 n)
  have I4 : ∀ (i j : ℕ), i ≤ j → (states j).succ ⊆ (states i).succ := by
    intro (i : ℕ) (j : ℕ) (hij : i ≤ j)
    induction j with
    | zero =>
      have := Nat.le_zero.mp hij
      subst this
      exact le_refl _
    | succ j ih =>
      rcases Nat.lt_or_eq_of_le hij with h | rfl
      · exact (I2 j).trans (ih (Nat.lt_succ_iff.mp h))
      · exact le_refl _
  have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
    intro m n hmn
    cases n with
    | zero => exact absurd hmn (Nat.not_lt_zero m)
    | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
  have verts_mono : StrictMono (fun n => (states n).vert) :=
    strictMono_nat_of_lt_succ I3
  refine ⟨fun n => (states n).vert, verts_mono, fun n => ?_⟩
  rcases (states n).prop with ⟨k, hk⟩ | hd
  · exact Or.inl ⟨k, fun m hmn => hk _ (I5 n m hmn) (verts_mono hmn)⟩
  · exact Or.inr fun m l hnm hml =>
      hd _ (I5 n m hnm) _ (I5 n l (hnm.trans hml))
        (verts_mono hnm) (verts_mono (hnm.trans hml)) (verts_mono hml)

theorem TwoLT.pairSeqCanon (f : PairSeq ℕ) :
    ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
    (∀ n : ℕ, ∃ k : ℕ, ∀ m (hmn : n < m), f (e n) (e m) (he hmn) = k) ∨
    (∀ n : ℕ, ∀ m l (hnm : n < m) (hml : m < l),
        2 * f (e n) (e m) (he hnm) < f (e n) (e l) (he (hnm.trans hml))) := by
  -- Apply the weak version
  obtain ⟨e, he, hcanon⟩ := pairSeqCanon_weak f
  -- Color each n with 0 if fan is constant, 1 if doubling
  let color : ℕ → Fin 2 := fun n =>
    if (∃ k, ∀ m (hmn : n < m), f (e n) (e m) (he hmn) = k) then 0 else 1
  -- Apply pigeonhole to get monochromatic subsequence
  obtain ⟨idx, hidx, c, hc⟩ := infinite_pigeonhole' color
  refine ⟨e ∘ idx, he.comp hidx, ?_⟩
  -- Case split on the monochromatic color
  fin_cases c
  · -- Color 0: all fans along idx are constant
    left
    intro n
    have hn : color (idx n) = 0 := hc n
    simp only [color] at hn
    split_ifs at hn with h
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, fun m hmn => hk (idx m) (hidx hmn)⟩
    · simp at hn
  · -- Color 1: all fans along idx are doubling
    right
    intro n m l hnm hml
    have hn : color (idx n) = 1 := hc n
    simp only [color] at hn
    split_ifs at hn with h
    · simp at hn
    · push_neg at h
      rcases hcanon (idx n) with ⟨k, hk⟩ | hdouble
      ·  -- h : ¬ ∃ k, ∀ m hmn, f (e (idx n)) (e m) _ = k
        rcases hcanon (idx n) with ⟨k, hk⟩ | hdouble
        · obtain ⟨m', hm', hne⟩ := h k
          exact absurd (hk m' hm') hne
        · exact hdouble (idx m) (idx l) (hidx hnm) (hidx hml)
      · exact hdouble (idx m) (idx l) (hidx hnm) (hidx hml)

theorem TwoLT.isTwoBQO : TwoBQO TwoLT := by
  intro f
  obtain ⟨e, he, hall | hdouble⟩ := pairSeqCanon f
  · -- All fans constant: define g n = constant value of fan at n
    let g : ℕ → ℕ := fun n => (hall n).choose
    have hg : ∀ n m (h : n < m), f (e n) (e m) (he h) = g n :=
      fun n => (hall n).choose_spec
    obtain ⟨idx, hidx, ⟨k, hk⟩ | hstrict⟩ := constant_or_strict g
    · -- g constant: f(e(idx 0), e(idx 1)) = k = f(e(idx 1), e(idx 2)) → TwoLT k k
      refine ⟨e (idx 0), e (idx 1), e (idx 2),
        he (hidx (by norm_num)), he (hidx (by norm_num)), ?_⟩
      rw [hg (idx 0) (idx 1) (hidx (by norm_num)),
          hg (idx 1) (idx 2) (hidx (by norm_num)),
          hk 0, hk 1]
      exact Or.inl rfl
    · -- g strictly doubling: f(e(idx 0), e(idx 1)) = g(idx 0),
      --   f(e(idx 1), e(idx 2)) = g(idx 1) > 2 * g(idx 0) → TwoLT
      refine ⟨e (idx 0), e (idx 1), e (idx 2),
        he (hidx (by norm_num)), he (hidx (by norm_num)), ?_⟩
      rw [hg (idx 0) (idx 1) (hidx (by norm_num)),
          hg (idx 1) (idx 2) (hidx (by norm_num))]
      exact Or.inr (hstrict 0 1 (by norm_num))
  · -- All fans doubling.
    -- Let n = f(e 0)(e 1). Fan at 1 is doubling, so ∃ k > 1 with f(e 1)(e k) > 2*n.
    set n := f (e 0) (e 1) (he (by norm_num))
    have hunbdd : ∃ k, ∃ (hk : 1 < k), 2 * n < f (e 1) (e k) (he hk) := by
      by_contra h
      push_neg at h
      let val : ℕ → ℕ := fun j => f (e 1) (e (j + 2)) (he (by omega : 1 < j + 2))
      have hstrict : ∀ j, val j < val (j + 1) := fun j => by
        have h := hdouble 1 (j + 2) (j + 3) (by omega) (by omega)
        simp only [val, show j + 1 + 2 = j + 3 from by omega]
        linarith
      have hbound : ∀ j, val j ≤ 2 * n :=
        fun j => h (j + 2) (by omega)
      have hgrow : ∀ j, f (e 1) (e 2) (he (by norm_num)) + j ≤ val j := by
        intro j
        induction j with
        | zero => simp [val]
        | succ j ih =>
          have := hstrict j
          simp only [val] at *
          omega
      have := hgrow (2 * n + 1)
      have := hbound (2 * n + 1)
      simp only [val] at *
      omega
    obtain ⟨k, hk1, hk2⟩ := hunbdd
    exact ⟨e 0, e 1, e k, he (by norm_num), he hk1, Or.inr hk2⟩



/-- The `≤•` (bullet) preorder on `Ordinal.{0}`, extending the `2nLTm` relation on `ℕ`
    lexicographically over the decomposition `α = limitPart α + natPart α`:

    `λ₀ + n₀ ≤• λ₁ + n₁  ↔  λ₀ < λ₁  ∨  (λ₀ = λ₁  ∧  (n₀ = n₁  ∨  2 * n₀ < n₁))` -/
def Ordinal.leBullet (α β : Ordinal.{0}) : Prop :=
  α.limitPart < β.limitPart ∨
  (α.limitPart = β.limitPart ∧
    (α.natPart = β.natPart ∨ 2 * α.natPart < β.natPart))

/-- Correct characterization of leBullet via decomposition. -/
theorem Ordinal.leBullet_iff_decomp (α β : Ordinal.{0}) :
    Ordinal.leBullet α β ↔
    α.limitPart < β.limitPart ∨
    (α.limitPart = β.limitPart ∧ TwoLT α.natPart β.natPart) := by
  simp [Ordinal.leBullet, TwoLT]


/-- The strict bullet order. -/
def Ordinal.ltBullet (α β : Ordinal.{0}) : Prop :=
  Ordinal.leBullet α β ∧ ¬ Ordinal.leBullet β α


/-! Basic API -/

lemma Ordinal.leBullet_refl (α : Ordinal.{0}) : Ordinal.leBullet α α := by
  right; exact ⟨rfl, Or.inl rfl⟩

lemma Ordinal.leBullet_trans {α β γ : Ordinal.{0}}
    (h₁ : Ordinal.leBullet α β) (h₂ : Ordinal.leBullet β γ) : Ordinal.leBullet α γ := by
  rcases h₁ with h | ⟨hlam1, hn₁⟩ <;> rcases h₂ with h' | ⟨hlam2, hn₂⟩
  · exact Or.inl (h.trans h')
  · exact Or.inl (hlam2 ▸ h)
  · exact Or.inl (hlam1 ▸ h')
  · refine Or.inr ⟨hlam1.trans hlam2, ?_⟩
    rcases hn₁ with hn₁ | hn₁ <;> rcases hn₂ with hn₂ | hn₂
    · exact Or.inl (hn₁.trans hn₂)
    · exact Or.inr (hn₁ ▸ hn₂)
    · exact Or.inr (hn₂ ▸ hn₁)
    · exact Or.inr (by omega)



lemma Ordinal.leBullet_antisymm {α β : Ordinal.{0}}
    (h1 : Ordinal.leBullet α β) (h2 : Ordinal.leBullet β α) : α = β := by
  simp only [Ordinal.leBullet] at h1 h2
  -- h1 : α.limitPart < β.limitPart ∨ (α.limitPart = β.limitPart ∧ (...))
  -- h2 : β.limitPart < α.limitPart ∨ (β.limitPart = α.limitPart ∧ (...))
  rcases h1 with h1 | ⟨hlam1, hn1⟩ <;> rcases h2 with h2 | ⟨hlam2, hn2⟩
  · -- limitPart α < limitPart β and limitPart β < limitPart α: contradiction
    exact absurd (h1.trans h2) (lt_irrefl _)
  · -- limitPart α < limitPart β but limitPart β = limitPart α: contradiction
    exact absurd (hlam2 ▸ h1) (lt_irrefl _)
  · -- limitPart α = limitPart β but limitPart β < limitPart α: contradiction
    exact absurd (hlam1 ▸ h2) (lt_irrefl _)
  · -- limitPart α = limitPart β and TwoLT on natParts in both directions
    have hlam : α.limitPart = β.limitPart := hlam1
    have hnat : α.natPart = β.natPart := TwoLT.antisymm
      (show TwoLT α.natPart β.natPart from hn1)
      (show TwoLT β.natPart α.natPart from hn2)
    calc α = α.limitPart + α.natPart := Ordinal.eq_limitPart_add_natPart α
      _ = β.limitPart + β.natPart := by rw [hlam, hnat]
      _ = β := (Ordinal.eq_limitPart_add_natPart β).symm

/-! The type used to represent leBullet as a LexSigma:
    an element of `Σ (λ : LimitOrZero), ℕ` where `LimitOrZero` is
    the subtype of limit-or-zero ordinals, ordered by `<`. -/

/-- The subtype of limit-or-zero ordinals below ω₁, well-ordered by `<`. -/
abbrev LimitOrdinal := {α : Ordinal.{0} // Order.IsSuccLimit α ∨ α = 0}

/-- The equivalence between `Ordinal.{0}` and `Σ (λ : LimitOrdinal), ℕ`
    given by the decomposition `α = λ + n`. -/
noncomputable def Ordinal.toBulletRepr (α : Ordinal.{0}) :
    Σ (_ : LimitOrdinal), ℕ :=
  ⟨⟨α.limitPart, α.limitPart_isLimit_or_zero⟩, α.natPart⟩

/-- leBullet coincides with LexSumRel on the sigma type. -/
theorem Ordinal.leBullet.isTwoBQO : TwoBQO Ordinal.leBullet := by
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  let f_lim : PairSeq LimitOrdinal :=
    fun m n h => ⟨(f m n h).limitPart, (f m n h).limitPart_isLimit_or_zero⟩
  obtain ⟨e, he, hperf | hbad_lim⟩ :=
    PairSeq.perfect_or_bad (fun (a b : LimitOrdinal) => a.val ≤ b.val) f_lim
  · by_cases hconst : ∀ m n l (hmn : m < n) (hnl : n < l),
        (f (e m) (e n) (he hmn)).limitPart = (f (e n) (e l) (he hnl)).limitPart
    · let f_nat : PairSeq ℕ :=
        fun m n h => (f (e m) (e n) (he h)).natPart
      obtain ⟨m, n, l, hmn, hnl, hrel⟩ := TwoLT.isTwoBQO f_nat
      refine absurd ?_ (hbad (e m) (e n) (e l) (he hmn) (he hnl))
      exact Or.inr ⟨hconst m n l hmn hnl, hrel⟩
    · push_neg at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      refine absurd ?_ (hbad (e m) (e n) (e l) (he hmn) (he hnl))
      exact Or.inl (lt_of_le_of_ne (hperf m n l hmn hnl) hne)
  · exfalso
    have hstrict : ∀ k,
        (f (e (k+1)) (e (k+2)) (he (Nat.lt_succ_self (k+1)))).limitPart
        < (f (e k) (e (k+1)) (he (Nat.lt_succ_self k))).limitPart :=
      fun k => not_le.mp (hbad_lim k (k+1) (k+2)
        (Nat.lt_succ_self k) (Nat.lt_succ_self (k+1)))
    -- Strictly decreasing sequence of ordinals is impossible
    obtain ⟨k, hk⟩ := @WellFounded.not_rel_apply_succ Ordinal.{0} (· < ·)
      ⟨Ordinal.lt_wf⟩
      (fun k => (f (e k) (e (k+1)) (he (Nat.lt_succ_self k))).limitPart)
    exact hk (hstrict k)
