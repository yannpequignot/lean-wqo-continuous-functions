
import Mathlib
import RequestProject.PrelimMemo.Basic
import RequestProject.Bqo.Ramsey
open Set

set_option autoImplicit false

noncomputable section

open Classical


/-
TwoBQO.lean
===========

A Lean 4 / Mathlib formalization of 2-better-quasi-orders (2-BQO).

Goals of this file (following Pequignot, EMS Surveys 2017):
  (A) Definition of 2-BQO via bad pair-sequences on [ℕ]²
  (B) Ever pair-sequence restricts to either a bad or perfect pair-sequence
  (C) 2-BQO → WQO
  (D) ω₁ is 2-BQO
  (E) Finite products of 2-BQOs are 2-BQO
  (F) Sum of 2-BQOs along a 2-BQO is 2-BQO  (key theorem)
-/

/-!
## §2  Bad pair-sequences and 2-BQO
-/

/-- A **pair-sequence** in `α` assigns a value to every pair `(m, n)` with `m < n`. -/
abbrev PairSeq (α : Type*) := ∀ (m n : ℕ), m < n → α

def restrictPairSeq {α : Type*} (f : PairSeq α) (e : ℕ → ℕ) (he_mono : StrictMono e) :
    PairSeq α :=
  fun m n hmn => f (e m) (e n) (he_mono hmn)

/-- A pair-sequence `f` is **bad** for `r` if:
    for all `m < n < l`, `f(m,n)` and `f(n,l)` are not `r`-related.

    This is the specialisation of Pequignot's "bad super-sequence" to the
    rank-2 front `[ℕ]²`. -/
def BadPairSeq {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    ¬ r (f m n hmn) (f n l hnl)

def PerfectPairSeq {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)


/-- `r` is **2-BQO** if there is no bad pair-sequence for `r`. -/
def TwoBQO_n {α : Type*} (r : α → α → Prop) : Prop :=
  ¬ ∃ f : PairSeq α, BadPairSeq r f

def TwoBQO {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ (f : PairSeq α), ∃ m n l : ℕ, ∃ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)

theorem isTwoBQO_iff {α : Type*} (r : α → α → Prop) :
    TwoBQO r ↔ TwoBQO_n r := by
  simp [TwoBQO_n, BadPairSeq, not_exists, not_forall]
  exact Iff.symm (Eq.to_iff rfl)

theorem perfect_or_bad {α : Type*} (r : α → α → Prop)
    (f : PairSeq α) : ∃ e : ℕ → ℕ, ∃ (he_mono : StrictMono e),
    (PerfectPairSeq r (restrictPairSeq f e he_mono)
     ∨ BadPairSeq r (restrictPairSeq f e he_mono)) := by
  obtain ⟨e, he_mono, k, hk⟩ := @infinite_ramsey_triples Bool inferInstance
    (fun h i j (hs : h < i ∧ i < j) => decide (r (f h i hs.1) (f i j hs.2)))
  refine ⟨e, he_mono, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hk_false | hk_true
  · left
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_false] at h_color
    simpa [decide_eq_false_iff_not] using h_color
  · right
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_true] at h_color
    simpa [decide_eq_true_eq] using h_color

/-!
## §3  2-BQO implies WQO
-/

/-- **2-BQO implies WQO** (Pequignot, Proposition 2.2).

**Proof:** Given a sequence `g : ℕ → α`, apply 2-BQO to the pair-sequence
`(m, n, _) ↦ g m`. A good triple `m < n < l` yields `r (g m) (g n)`. -/
theorem TwoBQO.wellQuasiOrdered {α : Type*} {r : α → α → Prop}
    (h : TwoBQO r) : WellQuasiOrdered r := fun g =>
  let ⟨m, n, _, hmn, _, hrel⟩ := h (fun m _ _ => g m)
  ⟨m, n, hmn, hrel⟩

/-!
## §4  Well-orders are 2-BQO
-/

/-- **Well-orders are 2-BQO.**

**Proof:** if `f` is bad for a well-order `<`, the sequence `n ↦ f(n, n+1)`
is strictly decreasing, contradicting well-foundedness. -/
theorem TwoBQO.of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    TwoBQO (α := α) (· ≤ ·) := by
  rw [isTwoBQO_iff]
  intro ⟨f, hbad⟩
  have hstrict : ∀ n, f (n+1) (n+2) (Nat.lt_succ_self _)
                        < f n (n+1) (Nat.lt_succ_self _) :=
    fun n => not_le.mp
      (hbad n (n+1) (n+2) (Nat.lt_succ_self n) (Nat.lt_succ_self (n+1)))
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    (fun n => f n (n+1) (Nat.lt_succ_self n))
  exact hn (hstrict n)

/-!
## §5  ω₁ is 2-BQO

The ordinal ω₁ is 2-BQO because it is a well-order.
-/

/-- **ω₁ is 2-BQO** with respect to `≤`. -/
theorem Ordinal.omega1_le_isTwoBQO :
    TwoBQO (α := Set.Iio omega1) (· ≤ ·) :=
  TwoBQO.of_wellFoundedLT

/-!
## §6  Closure properties

### 6.1  Monotone preimage (downward closure)
-/

/-- 2-BQO is closed under monotone preimage: if `φ : β → α` is monotone
and `r` on `α` is 2-BQO, then the pullback of `r` along `φ` is 2-BQO. -/
theorem TwoBQO.comap {α β : Type*} {r : α → α → Prop}
    (h : TwoBQO r) (φ : β → α) :
    TwoBQO (fun a b => r (φ a) (φ b)) := by
  rw [isTwoBQO_iff] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨fun m n hmn => φ (f m n hmn),
    fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel⟩

/-- **Subtype closure.** -/
theorem IsTwoBQO.subtype {α : Type*} {r : α → α → Prop}
    (h : TwoBQO r) (p : α → Prop) :
    TwoBQO (fun a b : Subtype p => r a.val b.val) :=
  h.comap Subtype.val

theorem TwoBQO.mono {α : Type*} {r s : α → α → Prop}
    (h : TwoBQO r)
    (hincl : ∀ a b, r a b → s a b) :
    TwoBQO s := by
  rw [isTwoBQO_iff] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨f, fun m n l hmn hnl hrel => hbad m n l hmn hnl (hincl _ _ hrel)⟩

/-!
### 6.2  Finite products (Dickson's lemma for 2-BQO)

**Theorem:** If `r` and `s` are 2-BQO then the componentwise product
`r × s` on `α × β` is 2-BQO.

**Proof:** Let `f : PairSeq (α × β)` be bad for `r × s`.
Write `f₁(m,n) = (f m n).1` and `f₂(m,n) = (f m n).2`.

Step 1: Apply RT² to the colouring of pairs:
  colour `(m,n)` by 0 if `r (f₁ m n) (f₁ n ?)` ... wait, RT² colours
  by a fixed colour, but we need to compare consecutive values.

Actually the cleanest argument does NOT need RT²:

If `f` is bad for `r × s`, then `f₁ = (·).1 ∘ f` is bad for `r`:
- Suppose `f₁` has a good triple `m < n < l`: `r (f₁ m n) (f₁ n l)`.
- Since `f` is bad: `¬ (r (f₁ m n) (f₁ n l) ∧ s (f₂ m n) (f₂ n l))`.
- So `¬ s (f₂ m n) (f₂ n l)`.

So the triple that's good for `r` is bad for `s`. We need to find a pair-
sequence that is globally bad for `s`, not just bad at one triple.

This is where RT² enters: apply it to colour pairs by whether r holds.
Get an infinite monochromatic set.
- If r always holds: then for s, the restricted f₂ is bad → contradiction.
- If r never holds: then f₁ is bad → contradiction with r being 2-BQO.
-/

/-- **Product closure** (Dickson's lemma for 2-BQO).

If `r` on `α` and `s` on `β` are 2-BQO, then the componentwise product
`fun (a₁,b₁) (a₂,b₂) => r a₁ a₂ ∧ s b₁ b₂` on `α × β` is 2-BQO. -/
theorem TwoBQO.prod {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (hr : TwoBQO r) (hs : TwoBQO s) :
    TwoBQO (fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2) := by
  rw [isTwoBQO_iff] at hr hs ⊢
  intro ⟨f, hbad⟩
  -- f₁ : PairSeq α  is the first-coordinate projection
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  -- Apply perfect_or_bad to f₁ under r
  obtain ⟨e₁, he₁, hperf₁ | hbad₁⟩ := perfect_or_bad r f₁
  · -- f₁ is perfect along e₁: r holds on every consecutive pair.
    -- Look at the second coordinate of f restricted to e₁.
    let f₂ : PairSeq β := fun m n h => (restrictPairSeq f e₁ he₁ m n h).2
    -- Apply perfect_or_bad to f₂ under s
    obtain ⟨e₂, he₂, hperf₂ | hbad₂⟩ := perfect_or_bad s f₂
    · -- Both coordinates perfect: derive a contradiction from hbad.
      -- At the triple (e₁(e₂ 0), e₁(e₂ 1), e₁(e₂ 2)), r and s both hold,
      -- but hbad says the product never holds.
      exact hbad (e₁ (e₂ 0)) (e₁ (e₂ 1)) (e₁ (e₂ 2))
        (he₁ (he₂ (by norm_num : 0 < 1))) (he₁ (he₂ (by norm_num : 1 < 2)))
        ⟨hperf₁ (e₂ 0) (e₂ 1) (e₂ 2) (he₂ (by norm_num : 0 < 1)) (he₂ (by norm_num : 1 < 2)),
         hperf₂ 0 1 2 (by norm_num : 0 < 1) (by norm_num : 1 < 2)⟩
    · -- f₂ restricted to e₂ is bad for s: contradicts hs
      exact hs ⟨restrictPairSeq f₂ e₂ he₂, hbad₂⟩
  · -- f₁ restricted to e₁ is bad for r: contradicts hr
    exact hr ⟨restrictPairSeq f₁ e₁ he₁, hbad₁⟩

/-- **Iterated finite product.** For a Fintype index `ι`, the product
`∀ i, α i` with pointwise quasi-order is 2-BQO when each component is. -/
theorem TwoBQO.pi : ∀ (n : ℕ) (α : Fin n → Type*)
    (r : ∀ i : Fin n, α i → α i → Prop)
    (_h : ∀ i, TwoBQO (r i)),
    TwoBQO (fun f g : ∀ i, α i => ∀ i, r i (f i) (g i)) := by
  intro n
  induction n with
  | zero =>
    intro α r h f
    exact ⟨0, 1, 2, by norm_num, by norm_num, fun i => i.elim0⟩  | succ n ih =>
    intro α r h
    have hpi := ih (fun i => α (Fin.castSucc i))
                   (fun i => r (Fin.castSucc i))
                   (fun i => h (Fin.castSucc i))
    have hprod := (h (Fin.last n)).prod hpi
    have key : TwoBQO (fun f g : ∀ i : Fin (n+1), α i =>
        r (Fin.last n) (f (Fin.last n)) (g (Fin.last n)) ∧
        ∀ i : Fin n, r (Fin.castSucc i) (f (Fin.castSucc i)) (g (Fin.castSucc i))) :=
      hprod.comap (fun (f : ∀ i : Fin (n+1), α i) => (f (Fin.last n), fun i => f (Fin.castSucc i)))
    convert key using 2
    ext f
    constructor
    · intro hall
      exact ⟨hall (Fin.last n), fun i => hall (Fin.castSucc i)⟩
    · intro ⟨hlast, hcast⟩ i
      exact Fin.lastCases hlast hcast i

theorem TwoBQO.prodN : ∀ (n : ℕ),
    TwoBQO (fun f g : Fin n → ℕ => ∀ i, f i ≤ g i) := by
  intro n
  exact TwoBQO.pi n (fun _ => ℕ) (fun _ => (· ≤ ·)) (fun _ => TwoBQO.of_wellFoundedLT)



/-!
### 6.3  Sum along a 2-BQO (the main closure theorem)

**Setup:** Given a quasi-order `r` on `ι` and quasi-orders `s i` on `α i`,
the **sum** `Σᵢ αᵢ` is ordered by:
  `(i, x) ≤ (j, y)` iff `r i j ∧ i ≠ j`  (strictly above)
  or  `i = j ∧ s i x y`                   (same fibre).

This is Pequignot's Proposition 2.4(iii) lifted to 2-BQO.

**Proof:**
Suppose `f : PairSeq (Σ i, α i)` is bad for the sum order.
Write `idx(m,n) = (f m n).1 : ι`.

Apply RT² to the colouring of pairs `(m,n)` by `idx(m,n)` — but `ι` may be
infinite. Instead, apply 2-BQO of `r` directly to the pair-sequence
`(m,n) ↦ idx(m,n)`: since `r` is 2-BQO, there exist `m < n < l` with
`r (idx m n) (idx n l)`.

Case 1: `idx(m,n) ≠ idx(n,l)`. Then the sum order holds (left disjunct).
  But `f` is bad: contradiction.

Case 2: `idx(m,n) = idx(n,l)` (call it `i`). Then the sum order requires
  `s i (f m n).2 (h ▸ (f n l).2)`. Since `f` is bad, this fails.
  So the pair-sequence `(m,n) ↦ (f m n).2` (in `α i`, along pairs with
  both index equal to `i`) is bad for `s i`.
  To make this precise, we need an infinite set of pairs where the index
  is always `i`, for which we use RT² on the index pair-sequence.
  Then `hs i` gives a contradiction.
-/

/-- The **lexicographic sum order along a wellorder** on `Σ i, α i`:
    `(i,x) ≤ (j,y)` iff `i` is strictly below `j` in `r`, or `i = j`
    and `x ≤ y` in `s i`. -/
def LexSumRel {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (s : α → Type*) (t : ∀ i, s i → s i → Prop) :
    (Σ i, s i) → (Σ i, s i) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ =>
      (i < j) ∨
      ∃ h : i = j, t i x (h ▸ y)

/-- **Sum theorem for 2-BQO.**

If `r` on `ι` is 2-BQO and each `s i` on `α i` is 2-BQO, then
`Σ i, α i` with `LexSumRel r s` is 2-BQO. -/
theorem TwoBQO.lexSigma
    {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (s : α → Type*)
    (t : ∀ i, s i → s i → Prop)
    (hs : ∀ i, TwoBQO (t i)) :
    TwoBQO (LexSumRel s t) := by
  intro f
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad⟩ := perfect_or_bad (α := α) (· ≤ ·) f₁
  · -- PERFECT CASE: f₁ along e is non-decreasing.
    -- Sub-case on whether the index is ever strictly increasing.
    by_cases hconst : ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
        (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · -- Index is constant = c := (f (e 0) (e 1) _).1 along e.
      set c := (f (e 0) (e 1) (he (by norm_num : (0:ℕ) < 1))).1
      -- Prove val(m,n) = c for all m < n.
      have hmem : ∀ m n : ℕ, (hmn : m < n) →
          (f (e m) (e n) (he hmn)).1 = c := by
        -- First prove val(n, n+1) = c for all n, independently of m.
        have hsucc : ∀ n : ℕ,
            (f (e n) (e (n+1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n+1) (n+2)
              (Nat.lt_succ_self n) (Nat.lt_succ_self (n+1))).symm.trans ih
        -- Then use hsucc to conclude val(m,n) = c.
        intro m n hmn
        exact (hconst m n (n+1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      -- Build a pair-sequence in s c.
      let g : PairSeq (s c) := fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      -- Get a good triple for t c.
      obtain ⟨m, n, l, hmn, hnl, hrel⟩ := hs c g
      -- The good triple for LexSumRel: use right disjunct (same index c).
      refine ⟨e m, e n, e l, he hmn, he hnl, ?_⟩
      show LexSumRel s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      -- Both sigma values have first component c; use ∃ heq, t ...
      have h_mn : (f (e m) (e n) (he hmn)).1 = c := hmem m n hmn
      have h_nl : (f (e n) (e l) (he hnl)).1 = c := hmem n l hnl
      -- Rewrite the sigma values: (f ...) = ⟨c, g m n hmn⟩ and ⟨c, g n l hnl⟩.
      have hfmn : f (e m) (e n) (he hmn) = ⟨c, g m n hmn⟩ := by
        ext
        · exact h_mn
        · simp [g]
      have hfnl : f (e n) (e l) (he hnl) = ⟨c, g n l hnl⟩ := by
        ext
        · exact h_nl
        · simp [g]
      rw [hfmn, hfnl]
      show (c < c) ∨ ∃ h : c = c, t c (g m n hmn) (h ▸ g n l hnl)
      exact Or.inr ⟨rfl, hrel⟩
    · -- Strict index increase at some triple → good triple via left disjunct.
      push_neg at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      exact ⟨e m, e n, e l, he hmn, he hnl,
        Or.inl (lt_of_le_of_ne (hperf m n l hmn hnl) hne)⟩
  · -- BAD CASE: f₁ along e is strictly decreasing → contradicts WellFoundedLT.
    exfalso
    have hstrict : ∀ k : ℕ,
        (f (e (k+1)) (e (k+2)) (he (Nat.lt_succ_self (k+1)))).1
        < (f (e k) (e (k+1)) (he (Nat.lt_succ_self k))).1 :=
      fun k => not_le.mp
        (hbad k (k+1) (k+2) (Nat.lt_succ_self k) (Nat.lt_succ_self (k+1)))
    obtain ⟨k, hk⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
      (fun k => (f (e k) (e (k+1)) (he (Nat.lt_succ_self k))).1)
    exact hk (hstrict k)

/-- The **lexicographic sum order along a quasi-order** on `Σ i, α i`:
    `(i,x) ≤ (j,y)` iff `r i j` and `i ≠ j` (strictly above in r),
    or `i = j` and `x ≤ y` in `t i`. -/
def LexSumRelQO {ι : Type*} (r : ι → ι → Prop)
    (s : ι → Type*) (t : ∀ i, s i → s i → Prop) :
    (Σ i, s i) → (Σ i, s i) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ =>
      (r i j ∧ i ≠ j) ∨
      ∃ h : i = j, t i x (h ▸ y)

variable {ι : Type*} (r : ι → ι → Prop)
         (s : ι → Type*) (t : ∀ i, s i → s i → Prop)

/-- `LexSumRelQO r s t` is reflexive whenever each `t i` is. -/
lemma LexSumRelQO.refl
    (ht_refl : ∀ i (x : s i), t i x x)
    (σ : Σ i, s i) :
    LexSumRelQO r s t σ σ := by
  obtain ⟨i, x⟩ := σ
  -- Use the right disjunct with the reflexivity proof h = rfl.
  exact Or.inr ⟨rfl, ht_refl i x⟩

/-! ### Transitivity -/

/-- `LexSumRelQO r s t` is transitive whenever `r` is reflexive,
antisymmetric, and transitive, and each `t i` is transitive. -/
lemma LexSumRelQO.trans
    (hr_refl    : ∀ i, r i i)
    (hr_antisymm : ∀ i j, r i j → r j i → i = j)
    (hr_trans   : ∀ i j k, r i j → r j k → r i k)
    (ht_trans   : ∀ i (x y z : s i), t i x y → t i y z → t i x z)
    {σ₁ σ₂ σ₃ : Σ i, s i}
    (h₁₂ : LexSumRelQO r s t σ₁ σ₂)
    (h₂₃ : LexSumRelQO r s t σ₂ σ₃) :
    LexSumRelQO r s t σ₁ σ₃ := by
  -- Destructure all three sigma values.
  obtain ⟨i, x⟩ := σ₁
  obtain ⟨j, y⟩ := σ₂
  obtain ⟨k, z⟩ := σ₃
  -- Unfold both hypotheses.
  simp only [LexSumRelQO] at h₁₂ h₂₃ ⊢
  rcases h₁₂ with ⟨hrij, hij_ne⟩ | ⟨hij, htxy⟩ <;>
  rcases h₂₃ with ⟨hrjk, hjk_ne⟩ | ⟨hjk, htyz⟩
  · -- (strict, strict): r i j, i ≠ j, r j k, j ≠ k  →  r i k, i ≠ k
    left
    refine ⟨hr_trans i j k hrij hrjk, ?_⟩
    intro hik
    -- If i = k then r k j and r j k give k = j, so i = j, contradiction.
    have hrki : r k i := hik ▸ hr_refl i
    have hrjk' := hrjk
    -- r i j and r k i (= r i i since i=k) ... use antisymmetry on j and k:
    -- We have r i j, r j k, i = k, so r k j and r j k → j = k, contradicting j ≠ k.
    have hrkj : r k j := hik ▸ hrij
    exact hjk_ne (hr_antisymm j k hrjk' hrkj)
  · -- (strict, same): r i j, i ≠ j, j = k
    left
    exact ⟨hjk ▸ hrij, hjk ▸ hij_ne⟩
  · -- (same, strict): i = j, r j k, j ≠ k
    left
    exact ⟨hij ▸ hrjk, hij ▸ hjk_ne⟩
  · -- (same, same): i = j, j = k  →  i = k, compose t-steps
    right
    refine ⟨hij.trans hjk, ?_⟩
    -- Transport z from s k to s i along hij.trans hjk.
    -- htxy : t i x (hij ▸ y)   (y : s j = s i via hij)
    -- htyz : t j y (hjk ▸ z)   (z : s k = s j via hjk)
    -- We need: t i x ((hij.trans hjk) ▸ z)
    -- First unify j with i via hij, then k with i via hij.trans hjk.
    subst hij
    -- Now j = i, htxy : t i x y, htyz : t i y (hjk ▸ z), goal: t i x (hjk ▸ z)
    subst hjk
    -- Now k = i, htyz : t i y z, goal: t i x z
    exact ht_trans i x y z htxy htyz

/-! **Sum theorem for 2-BQO along a quasi-order with antisymmetry.**

If `r` on `ι` is 2-BQO, `r` is antisymmetric, and each `t i` on `s i`
is 2-BQO, then `Σ i, s i` with `LexSumRelQO r s t` is 2-BQO. -/
-- lemma TwoBQO.lexSigmaQO_reflect
--     {ι : Type*}
--     (r : ι → ι → Prop)
--     (hr_antisymm : ∀ i j, r i j → r j i → i = j)
--     (s : ι → Type*)
--     (t : ∀ i, s i → s i → Prop)
--     (f : PairSeq LexSumRelQO r s t)
--     (hbad : BadPairSeq (LexSumRelQO r s t) f) :
--     ∃ e : ℕ → ℕ, ∃ (he_mono : StrictMono e),
--     BadPairSeq r (fun m n hmn => (f (e m) (e n) (he hmn)).1)
--      ∨ ∃ i : ι, ∀ m n : ℕ, (hmn : m < n) →
--         (f (e m) (e n) (he hmn)).1 = i ∧
--         BadPairSeq (t i) (fun m n hmn => (f (e m) (e n) (he_mono hmn)).2) := by
--   sorry
/--
The constructive content of the sum theorem for 2-BQO along a partial order.
-/
lemma TwoBQO.lexSigmaQO_reflect
    {ι : Type*}
    (r : ι → ι → Prop)
    (hr_antisymm : ∀ i j, r i j → r j i → i = j)
    (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop)
    (f : PairSeq (Σ i, s i))
    (hf_bad : BadPairSeq (LexSumRelQO r s t) f) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      BadPairSeq r (fun m n hmn => (f (e m) (e n) (he_mono hmn)).1)
      ∨
      ∃ i : ι,
        ∃ hmem : ∀ m n (hmn : m < n), (f (e m) (e n) (he_mono hmn)).1 = i,
        BadPairSeq (t i)
          (fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he_mono hmn)).2) := by
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad₁⟩ := perfect_or_bad r f₁
  · by_cases hconst :
        ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
          (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · set c := (f (e 0) (e 1) (he (by norm_num : (0 : ℕ) < 1))).1
      have hmem : ∀ m n : ℕ, (hmn : m < n) →
          (f (e m) (e n) (he hmn)).1 = c := by
        have hsucc : ∀ n : ℕ,
            (f (e n) (e (n + 1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n + 1) (n + 2)
              (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1))).symm.trans ih
        intro m n hmn
        exact (hconst m n (n + 1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      let g : PairSeq (s c) :=
        fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      have hg_bad : BadPairSeq (t c) g := by
        intro m n l hmn hnl htrel
        apply hf_bad (e m) (e n) (e l) (he hmn) (he hnl)
        -- Name the two sigma values so we can subst their index components.
        set σ_mn := f (e m) (e n) (he hmn) with hσ_mn
        set σ_nl := f (e n) (e l) (he hnl) with hσ_nl
        -- The index equalities in terms of the named sigma values.
        have h_mn : σ_mn.1 = c := hmem m n hmn
        have h_nl : σ_nl.1 = c := hmem n l hnl
        -- Rewrite σ_mn and σ_nl as ⟨c, _⟩ using the index equalities.
        -- We work with the Sigma.eta expansion and the equalities.
        rw [show σ_mn = ⟨c, h_mn ▸ σ_mn.2⟩ from by ext <;> simp [h_mn]]
        rw [show σ_nl = ⟨c, h_nl ▸ σ_nl.2⟩ from by ext <;> simp [h_nl]]
        -- Goal is now: LexSumRelQO r s t ⟨c, h_mn ▸ σ_mn.2⟩ ⟨c, h_nl ▸ σ_nl.2⟩
        -- and htrel : t c (hmem m n hmn ▸ σ_mn.2) (hmem n l hnl ▸ σ_nl.2)
        -- These casts are the same (h_mn = hmem m n hmn etc.), so:
        unfold LexSumRelQO
        exact Or.inr ⟨rfl, htrel⟩
      exact ⟨e, he, Or.inr ⟨c, hmem, hg_bad⟩⟩
    · exfalso
      push_neg at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      exact hf_bad (e m) (e n) (e l) (he hmn) (he hnl)
        (Or.inl ⟨hperf m n l hmn hnl, hne⟩)
  · exact ⟨e, he, Or.inl hbad₁⟩

theorem TwoBQO.lexSigmaQO
    {ι : Type*}
    (r : ι → ι → Prop)
    (hr : TwoBQO r)
    (hr_antisymm : ∀ i j, r i j → r j i → i = j)
    (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop)
    (ht : ∀ i, TwoBQO (t i)) :
    TwoBQO (LexSumRelQO r s t) := by
  intro f
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad⟩ := perfect_or_bad r f₁
  · -- PERFECT CASE: f₁ along e is non-decreasing under r.
    by_cases hconst : ∀ m n l : ℕ, (hmn : m < n) → (hnl : n < l) →
        (f (e m) (e n) (he hmn)).1 = (f (e n) (e l) (he hnl)).1
    · -- CONSTANT CASE: index is constant = c along e.
      set c := (f (e 0) (e 1) (he (by norm_num : (0:ℕ) < 1))).1
      have hmem : ∀ m n : ℕ, (hmn : m < n) →
          (f (e m) (e n) (he hmn)).1 = c := by
        have hsucc : ∀ n : ℕ,
            (f (e n) (e (n+1)) (he (Nat.lt_succ_self n))).1 = c := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            exact (hconst n (n+1) (n+2)
              (Nat.lt_succ_self n) (Nat.lt_succ_self (n+1))).symm.trans ih
        intro m n hmn
        exact (hconst m n (n+1) hmn (Nat.lt_succ_self n)).trans (hsucc n)
      let g : PairSeq (s c) :=
        fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he hmn)).2
      obtain ⟨m, n, l, hmn, hnl, hrel⟩ := ht c g
      refine ⟨e m, e n, e l, he hmn, he hnl, ?_⟩
      show LexSumRelQO r s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      unfold LexSumRelQO
      apply Or.inr
      have h_mn : (f (e m) (e n) (he hmn)).fst = c := hmem m n hmn
      have h_nl : (f (e n) (e l) (he hnl)).fst = c := hmem n l hnl
      use Eq.trans h_mn h_nl.symm
      revert hrel
      simp only [g]
      intro hrel
      convert hrel using 1 <;> simp
    · -- STRICT INCREASE CASE: index strictly increases at some triple.
      -- "Strictly increases" means: r i j but i ≠ j, i.e. not (r j i → i = j).
      -- hperf gives r (f₁ m n) (f₁ n l), and hconst says they're not all equal.
      -- So ∃ m n l with r (f₁ m n) (f₁ n l) and f₁ m n ≠ f₁ n l.
      -- This gives the left disjunct of LexSumRelQO.
      push_neg at hconst
      obtain ⟨m, n, l, hmn, hnl, hne⟩ := hconst
      refine ⟨e m, e n, e l, he hmn, he hnl, ?_⟩
      show LexSumRelQO r s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      exact Or.inl ⟨hperf m n l hmn hnl, hne⟩
  · -- BAD CASE: f₁ along e is bad under r.
    -- Contradicts hr (r is 2-BQO).
    exfalso
    rw [isTwoBQO_iff] at hr
    exact hr ⟨restrictPairSeq f₁ e he, hbad⟩
