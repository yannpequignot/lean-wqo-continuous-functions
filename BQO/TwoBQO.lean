import Mathlib.Tactic
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.WellFounded
import Mathlib.Order.RelClasses
import Mathlib.Data.Bool.Basic
import Mathlib.SetTheory.Ordinal.Basic
import BQO.WQO
import BQO.Ramsey

open Set

set_option autoImplicit false

noncomputable section

open Classical
open Preorder


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

namespace PairSeq

def restrict {α : Type*} (f : PairSeq α) (e : ℕ → ℕ) (he_mono : StrictMono e) :
    PairSeq α :=
  fun m n hmn => f (e m) (e n) (he_mono hmn)

/-- A pair-sequence `f` is **bad** for `r` if:
    for all `m < n < l`, `f(m,n)` and `f(n,l)` are not `r`-related.
-/
def IsBad {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    ¬ r (f m n hmn) (f n l hnl)

def IsPerfect {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)

theorem perfect_or_bad {α : Type*} (r : α → α → Prop)
    (f : PairSeq α) : ∃ e : ℕ → ℕ, ∃ (he_mono : StrictMono e),
    (IsPerfect r (restrict f e he_mono)
     ∨ IsBad r (restrict f e he_mono)) := by
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

end PairSeq


/-- `r` is **2-BQO** if there is no bad pair-sequence for `r`. -/
private def TwoBQO_n {α : Type*} (r : α → α → Prop) : Prop :=
  ¬ ∃ f : PairSeq α, PairSeq.IsBad r f

def TwoBQO {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ (f : PairSeq α), ∃ m n l : ℕ, ∃ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)

theorem TwoBQO.iff_noBad {α : Type*} (r : α → α → Prop) :
    TwoBQO r ↔ TwoBQO_n r := by
  simp only [TwoBQO_n, PairSeq.IsBad, not_exists, not_forall, Decidable.not_not]
  exact Iff.symm (Eq.to_iff rfl)

/-!
## §3  2-BQO implies WQO
-/

/-- **2-BQO implies WQO** .

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
  rw [TwoBQO.iff_noBad]
  intro ⟨f, hbad⟩
  have hstrict : ∀ n, f (n+1) (n+2) (Nat.lt_succ_self _)
                        < f n (n+1) (Nat.lt_succ_self _) :=
    fun n => not_le.mp
      (hbad n (n+1) (n+2) (Nat.lt_succ_self n) (Nat.lt_succ_self (n+1)))
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    (fun n => f n (n+1) (Nat.lt_succ_self n))
  exact hn (hstrict n)

/-!
## §5  Ordinals are 2-BQO

Ordinals are 2-BQO because they are well-ordered.
-/

/-- **Ordinals are 2-BQO** with respect to `≤`. -/
theorem Ordinal.isTwoBQO : TwoBQO (α := Ordinal) (· ≤ ·) :=
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
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨fun m n hmn => φ (f m n hmn),
    fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel⟩

/-- **Subtype closure.** -/
theorem TwoBQO.subtype {α : Type*} {r : α → α → Prop}
    (h : TwoBQO r) (p : α → Prop) :
    TwoBQO (fun a b : Subtype p => r a.val b.val) :=
  h.comap Subtype.val

theorem TwoBQO.mono {α : Type*} {r s : α → α → Prop}
    (h : TwoBQO r)
    (hincl : ∀ a b, r a b → s a b) :
    TwoBQO s := by
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨f, fun m n l hmn hnl hrel => hbad m n l hmn hnl (hincl _ _ hrel)⟩

/-!
### 6.2  Union of two parts, and finite colourings

Both rest on Ramsey for pairs (`infinite_ramsey_pairs`): a 2-colouring of pairs by which
*part* (resp. which *colour*) the single value `f m n` lands in has an infinite homogeneous
restriction, on which the relevant 2-BQO (resp. same-colour relation) gives a good triple.
-/

/-- **Union of two 2-BQO parts is 2-BQO.**  If `p, q` cover `α` and `r` is 2-BQO on each
sub-part `{x // p x}` and `{x // q x}`, then `r` is 2-BQO on `α`.

2-colour each pair `(m,n)` by whether `p (f m n)` holds; Ramsey-for-pairs gives an infinite
restriction landing wholly in one part, where the corresponding 2-BQO supplies a good triple. -/
theorem TwoBQO.union {α : Type*} (r : α → α → Prop) (p q : α → Prop)
    (hcover : ∀ a, p a ∨ q a)
    (hp : TwoBQO (fun a b : {x : α // p x} => r a.val b.val))
    (hq : TwoBQO (fun a b : {x : α // q x} => r a.val b.val)) :
    TwoBQO r := by
  classical
  intro f
  obtain ⟨e, he, k, hk⟩ :=
    infinite_ramsey_pairs (fun m n h => (decide (p (f m n h)) : Bool))
  cases k with
  | true =>
    have hpf : ∀ i j (h : i < j), p (f (e i) (e j) (he h)) :=
      fun i j h => of_decide_eq_true (hk i j h)
    obtain ⟨i, j, l, hij, hjl, hrel⟩ :=
      hp (fun i j h => ⟨f (e i) (e j) (he h), hpf i j h⟩)
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩
  | false =>
    have hqf : ∀ i j (h : i < j), q (f (e i) (e j) (he h)) :=
      fun i j h => (hcover _).resolve_left (of_decide_eq_false (hk i j h))
    obtain ⟨i, j, l, hij, hjl, hrel⟩ :=
      hq (fun i j h => ⟨f (e i) (e j) (he h), hqf i j h⟩)
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩

/-- **A quasi-order with finitely many classes is 2-BQO.**  If `c : α → κ` with `κ` finite and
*same colour ⟹ `r`-related*, then `r` is 2-BQO: colour pairs by `c (f m n)`, Ramsey-for-pairs
makes the restriction monochromatic, so any triple is good.  (The "finite up-to-equivalence ⟹
2-BQO" fact.) -/
theorem TwoBQO.of_finite_coloring {α κ : Type*} [Fintype κ] (r : α → α → Prop)
    (c : α → κ) (hc : ∀ a b, c a = c b → r a b) :
    TwoBQO r := by
  intro f
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_pairs (fun m n h => c (f m n h))
  exact ⟨e 0, e 1, e 2, he (by norm_num), he (by norm_num),
    hc _ _ ((hk 0 1 (by norm_num)).trans (hk 1 2 (by norm_num)).symm)⟩

/-- **Monotone image of a 2-BQO, up to equivalence.**

Let `r` be a preorder on `Q` and `rι` a 2-BQO on `ι`.  If `G : ι → Q` is
*monotone* (`rι a b → r (G a) (G b)`), then `r` is 2-BQO on the class of
elements that are `r`-equivalent to some `G i`.

This is the abstract skeleton of the `FinGl` argument: take `ι = ℕⁿ` with its
(2-BQO) product order, `G = Gl B`, and the class is `FinGl B`.

**Proof.**  Each element `q` of the subtype carries a witness `i` with
`q ≡ G i`; let `w q` be that witness.  `rι` is 2-BQO, so by `comap` the pulled-
back relation `rι (w a) (w b)` is 2-BQO on the subtype.  And it implies the
target: `rι (w a) (w b)` gives `r (G (w a)) (G (w b))` by monotonicity, which
chains with `a ≤ G (w a)` and `G (w b) ≤ b` to give `r a b`.  Conclude by
`mono`. -/
theorem TwoBQO.monotone_image_equiv {ι Q : Type*}
    {rι : ι → ι → Prop} {r : Q → Q → Prop} [IsPreorder Q r]
    (hι : TwoBQO rι) (G : ι → Q)
    (hmono : ∀ a b, rι a b → r (G a) (G b)) :
    TwoBQO (fun a b : {q : Q // ∃ i, r (G i) q ∧ r q (G i)} => r a.val b.val) := by
  refine (hι.comap (fun q => q.prop.choose)).mono ?_
  intro a b hab
  -- `hab : rι (w a) (w b)` where `w q := q.prop.choose`.
  have ha := a.prop.choose_spec  -- `r (G (w a)) a.val ∧ r a.val (G (w a))`
  have hb := b.prop.choose_spec  -- `r (G (w b)) b.val ∧ r b.val (G (w b))`
  -- `a.val ≤ G (w a) ≤ G (w b) ≤ b.val`.
  exact trans_of r ha.2 (trans_of r (hmono _ _ hab) hb.1)

/-!
### 6.2  Finite products (Dickson's lemma for 2-BQO)

**Theorem:** If `r` and `s` are 2-BQO then the componentwise product
`r × s` on `α × β` is 2-BQO.

-/

/-- **Product closure** (Dickson's lemma for 2-BQO).

If `r` on `α` and `s` on `β` are 2-BQO, then the componentwise product
`fun (a₁,b₁) (a₂,b₂) => r a₁ a₂ ∧ s b₁ b₂` on `α × β` is 2-BQO. -/
theorem TwoBQO.prod {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (hr : TwoBQO r) (hs : TwoBQO s) :
    TwoBQO (fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2) := by
  rw [TwoBQO.iff_noBad] at hr hs ⊢
  intro ⟨f, hbad⟩
  -- f₁ : PairSeq α  is the first-coordinate projection
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  -- Apply PairSeq.perfect_or_bad to f₁ under r
  obtain ⟨e₁, he₁, hperf₁ | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
  · -- f₁ is perfect along e₁: r holds on every consecutive pair.
    -- Look at the second coordinate of f restricted to e₁.
    let f₂ : PairSeq β := fun m n h => (PairSeq.restrict f e₁ he₁ m n h).2
    -- Apply PairSeq.perfect_or_bad to f₂ under s
    obtain ⟨e₂, he₂, hperf₂ | hbad₂⟩ := PairSeq.perfect_or_bad s f₂
    · -- Both coordinates perfect: derive a contradiction from hbad.
      -- At the triple (e₁(e₂ 0), e₁(e₂ 1), e₁(e₂ 2)), r and s both hold,
      -- but hbad says the product never holds.
      exact hbad (e₁ (e₂ 0)) (e₁ (e₂ 1)) (e₁ (e₂ 2))
        (he₁ (he₂ (by norm_num : 0 < 1))) (he₁ (he₂ (by norm_num : 1 < 2)))
        ⟨hperf₁ (e₂ 0) (e₂ 1) (e₂ 2) (he₂ (by norm_num : 0 < 1)) (he₂ (by norm_num : 1 < 2)),
         hperf₂ 0 1 2 (by norm_num : 0 < 1) (by norm_num : 1 < 2)⟩
    · -- f₂ restricted to e₂ is bad for s: contradicts hs
      exact hs ⟨PairSeq.restrict f₂ e₂ he₂, hbad₂⟩
  · -- f₁ restricted to e₁ is bad for r: contradicts hr
    exact hr ⟨PairSeq.restrict f₁ e₁ he₁, hbad₁⟩

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
  obtain ⟨e, he, hperf | hbad⟩ := PairSeq.perfect_or_bad (α := α) (· ≤ ·) f₁
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

namespace TwoBQO

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

namespace LexSumRelQO

/-- `LexSumRelQO r s t` is reflexive whenever each `t i` is. -/
lemma refl
    (ht_refl : ∀ i (x : s i), t i x x)
    (σ : Σ i, s i) :
    LexSumRelQO r s t σ σ := by
  obtain ⟨i, x⟩ := σ
  -- Use the right disjunct with the reflexivity proof h = rfl.
  exact Or.inr ⟨rfl, ht_refl i x⟩

/-! ### Transitivity -/

/-- `LexSumRelQO r s t` is transitive whenever `r` is reflexive,
antisymmetric, and transitive, and each `t i` is transitive. -/
lemma trans
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

end LexSumRelQO

end TwoBQO

/-! **Sum theorem for 2-BQO along a quasi-order with antisymmetry.**

If `r` on `ι` is 2-BQO, `r` is antisymmetric, and each `t i` on `s i`
is 2-BQO, then `Σ i, s i` with `LexSumRelQO r s t` is 2-BQO.

Antisymmetry of `r` is needed to ensure transitivity of `LexSumRelQO r s t`,
which is needed to apply the perfect-or-bad dichotomy to it.


The constructive content of the sum theorem for 2-BQO along a partial order.
-/
lemma TwoBQO.lexSigmaQO_reflect
    {ι : Type*}
    (r : ι → ι → Prop)
    (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop)
    (f : PairSeq (Σ i, s i))
    (hf_bad : PairSeq.IsBad (TwoBQO.LexSumRelQO r s t) f) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      PairSeq.IsBad r (fun m n hmn => (f (e m) (e n) (he_mono hmn)).1)
      ∨
      ∃ i : ι,
        ∃ hmem : ∀ m n (hmn : m < n), (f (e m) (e n) (he_mono hmn)).1 = i,
        PairSeq.IsBad (t i)
          (fun m n hmn => (hmem m n hmn) ▸ (f (e m) (e n) (he_mono hmn)).2) := by
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
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
      have hg_bad : PairSeq.IsBad (t c) g := by
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
        unfold TwoBQO.LexSumRelQO
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
    -- (hr_antisymm : ∀ i j, r i j → r j i → i = j)
    (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop)
    (ht : ∀ i, TwoBQO (t i)) :
    TwoBQO (TwoBQO.LexSumRelQO r s t) := by
  intro f
  let f₁ : PairSeq ι := fun m n h => (f m n h).1
  obtain ⟨e, he, hperf | hbad⟩ := PairSeq.perfect_or_bad r f₁
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
      show TwoBQO.LexSumRelQO r s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      unfold TwoBQO.LexSumRelQO
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
      show TwoBQO.LexSumRelQO r s t (f (e m) (e n) (he hmn)) (f (e n) (e l) (he hnl))
      exact Or.inl ⟨hperf m n l hmn hnl, hne⟩
  · -- BAD CASE: f₁ along e is bad under r.
    -- Contradicts hr (r is 2-BQO).
    exfalso
    rw [TwoBQO.iff_noBad] at hr
    exact hr ⟨PairSeq.restrict f₁ e he, hbad⟩


/-! ## Domination Order on subsets -/

def DomOrder {α : Type*} (r : α → α → Prop) (X Y : Set α) : Prop :=
  ∀ x ∈ X, ∃ y ∈ Y, r x y


lemma badSeq_dom_to_pairSeq {α : Type*} {r : α → α → Prop}
    (f : ℕ → Set α)
    (hbad : ∀ m n, m < n → ¬ DomOrder r (f m) (f n)) :
    ∃ f_ : PairSeq α,
      (∀ m n (hmn : m < n), f_ m n hmn ∈ f m) ∧
      PairSeq.IsBad r f_ := by
  have hex : ∀ m n, m < n → ∃ x, x ∈ f m ∧ ∀ y ∈ f n, ¬ r x y := by
    intro m n hmn
    have h := hbad m n hmn
    unfold DomOrder at h
    push_neg at h
    exact h
  let g : ∀ m n, m < n → α := fun m n hmn => Classical.choose (hex m n hmn)
  have hg_mem : ∀ m n (hmn : m < n), g m n hmn ∈ f m :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).1
  have hg_bad : ∀ m n (hmn : m < n), ∀ y ∈ f n, ¬ r (g m n hmn) y :=
    fun m n hmn => (Classical.choose_spec (hex m n hmn)).2
  refine ⟨g, hg_mem, ?_⟩
  intro m n l hmn hnl
  exact hg_bad m n hmn (g n l hnl) (hg_mem n l hnl)


theorem TwoBQO.dom_twoBQO {α : Type*} {r : α → α → Prop} (hr : TwoBQO r) :
    WellQuasiOrdered (DomOrder r) := by
  intro g
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ m n, m < n → ¬ DomOrder r (g m) (g n)
  obtain ⟨f_, _, hf_bad⟩ := badSeq_dom_to_pairSeq g hcon
  rw [TwoBQO.iff_noBad] at hr
  exact hr ⟨f_, hf_bad⟩

/-! ## Infinite sequences
Infinite sequences `:ℕ → Q` in a 2-BQO `Q` are wqo under EmbeddingForall
-/
def EmbedForAll {α : Type*} (r : α → α → Prop) (s : ℕ → α) (s' : ℕ → α) : Prop :=
  ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (s n) (s' (e n))

/-- `EmbedForAll r` is a preorder on `ℕ → Q` whenever `r` is (reflexivity via the
identity reindexing, transitivity via composition of strictly monotone reindexings). -/
instance EmbedForAll.isPreorder {Q : Type*} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (ℕ → Q) (EmbedForAll r) where
  refl s := ⟨id, strictMono_id, fun n => refl_of r (s n)⟩
  trans := by
    rintro s s' s'' ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩
    exact ⟨e₂ ∘ e₁, he₂.comp he₁, fun n => trans_of r (h₁ n) (h₂ (e₁ n))⟩



private lemma exists_strictMono_of_greedy {P : ℕ → ℕ → Prop}
    (hbuild : ∀ (start i : ℕ), ∃ j, start < j ∧ P i j) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, P i (e i) := by
  let e : ℕ → ℕ := fun i =>
    Nat.rec (motive := fun _ => ℕ)
      (hbuild 0 0).choose
      (fun n prev => (hbuild prev (n + 1)).choose)
      i
  have he0 : e 0 = (hbuild 0 0).choose := rfl
  have hesucc : ∀ n, e (n + 1) = (hbuild (e n) (n + 1)).choose := fun n => rfl
  have hP0 : P 0 (e 0) := he0 ▸ (hbuild 0 0).choose_spec.2
  have hPsucc : ∀ n, P (n + 1) (e (n + 1)) := fun n =>
    (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.2
  have hlt : ∀ n, e n < e (n + 1) := fun n =>
    (hesucc n) ▸ (hbuild (e n) (n + 1)).choose_spec.1
  refine ⟨e, strictMono_nat_of_lt_succ hlt, fun i => ?_⟩
  cases i with
  | zero => exact hP0
  | succ n => exact hPsucc n

/-- **Strengthening of regularity.** If `f` is a regular sequence in a preorder, then
for every threshold `n` there is a strictly monotone reindexing `e : ℕ → ℕ` whose values
all lie at or above `n` and which dominates `f` pointwise: `n ≤ e i` and `f i ≤ f (e i)`
for every `i`.  Proved greedily via `exists_strictMono_of_greedy`, picking at each step a
later index that is both `> ` the previous one and `≥ n`, available by regularity. -/
theorem Preorder.IsRegularSeq.exists_strictMono_dominating {Q : Type*} {le : Q → Q → Prop}
    [IsPreorder Q le] {f : ℕ → Q} (hf : IsRegularSeq le f) (n : ℕ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, n ≤ e i ∧ le (f i) (f (e i)) := by
  apply exists_strictMono_of_greedy (P := fun i j => n ≤ j ∧ le (f i) (f j))
  intro start i
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt (max start n)
  exact ⟨j, lt_of_le_of_lt (le_max_left _ _) hj_gt,
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hj_gt), hj_mem⟩

/-
**Key lemma A**: if `List.SublistForall₂ r l₁ l₂` then there is a strictly
monotone `φ : Fin l₁.length → Fin l₂.length` with `r (l₁.get i) (l₂.get (φ i))`
for all `i`.
-/
private lemma sublistForall₂_to_embedding {α : Type*} (r : α → α → Prop)
    (l₁ l₂ : List α) (h : List.SublistForall₂ r l₁ l₂) :
    ∃ φ : Fin l₁.length → Fin l₂.length, StrictMono φ ∧
      ∀ i, r (l₁.get i) (l₂.get (φ i)) := by
  induction h;
  · simp +decide [ StrictMono ];
  · simp_all +decide [ Fin.forall_fin_succ, StrictMono ];
    obtain ⟨ φ, hφ₁, hφ₂ ⟩ := ‹_›; use Fin.cons 0 ( Fin.succ ∘ φ ) ; aesop;
  · rename_i l₁ l₂ h ih; obtain ⟨ φ, hφ₁, hφ₂ ⟩ := ih; use fun i => Fin.succ ( φ i ) ; simp_all +decide [ StrictMono ] ;

/-
standard fact about List.SublistForall₂, provable by induction on h

**Key lemma B**: combine a strictly monotone embedding `ψ` of an initial
segment `[0, ka)` and a strictly monotone embedding `eG` of the tail (shifted by
`kb`) into a single strictly monotone embedding `e : ℕ → ℕ` witnessing `r (Fa n)
(Fb (e n))` for every `n`.
-/
private lemma embed_combine {α : Type*} (r : α → α → Prop)
    (Fa Fb : ℕ → α) (ka kb : ℕ)
    (ψ : ℕ → ℕ)
    (hψ_lt : ∀ n, n < ka → ψ n < kb)
    (hψ_mono : ∀ m n, m < n → n < ka → ψ m < ψ n)
    (hψ_rel : ∀ n, n < ka → r (Fa n) (Fb (ψ n)))
    (eG : ℕ → ℕ) (heG_mono : StrictMono eG)
    (heG_rel : ∀ i, r (Fa (i + ka)) (Fb (eG i + kb))) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (Fa n) (Fb (e n)) := by
  refine ⟨ fun n => if hn : n < ka then ψ n else eG ( n - ka ) + kb, ?_, ?_ ⟩;
  · intro m n hmn;
    by_cases hm : m < ka <;> by_cases hn : n < ka <;> simp +decide [ hm, hn ];
    · exact hψ_mono m n hmn hn;
    · linarith [ hψ_lt m hm, heG_mono.monotone ( Nat.zero_le ( n - ka ) ) ];
    · linarith;
    · exact heG_mono ( by omega );
  · grind

theorem TwoBQO.embedForAll_wqo {α : Type*} {r : α → α → Prop} [IsPreorder α r]
    (hr : TwoBQO r) :
    WellQuasiOrdered (EmbedForAll r) := by
  intro F
  -- Step 0: split each F n into a regular tail G n, preceded by a finite head w n.
  have hreg : ∀ n, ∃ k, IsRegularSeq r (fun i => F n (i + k)) :=
    fun n => hr.wellQuasiOrdered.eventuallyRegular r (F n)
  choose kk hkk using hreg
  set G : ℕ → ℕ → α := fun n i => F n (i + kk n) with hG_def
  set w : ℕ → List α := fun n => (List.range (kk n)).map (F n) with hw_def
  have hw_len : ∀ n, (w n).length = kk n := fun n => by simp [hw_def]
  have hw_get : ∀ n (i : ℕ) (h : i < (w n).length), (w n)[i] = F n i := fun n i h => by
    simp [hw_def, List.getElem_map, List.getElem_range]
  -- Step 1: Higman's WQO on lists (Mathlib's `partiallyWellOrderedOn_sublistForall₂`,
  -- specialized from an arbitrary subset to `univ`) gives a < b with w a Higman-embeds in w b.
  have hwqo_list : WellQuasiOrdered (List.SublistForall₂ r) := by
    rw [← partiallyWellOrderedOn_univ_iff]
    simpa [Set.eq_univ_iff_forall] using
      (partiallyWellOrderedOn_univ_iff.mpr hr.wellQuasiOrdered).partiallyWellOrderedOn_sublistForall₂ r
  -- Step 2: DomOrder r is WQO (from 2-BQO)
  have hdom_wqo : WellQuasiOrdered (DomOrder r) := hr.dom_twoBQO
  set S : ℕ → Set α := fun n => {x : α | ∃ i, r x (G n i)} with hS_def
  -- Step 3: product of the two WQOs applied to (w n, S n)
  have hprod_wqo : WellQuasiOrdered
      (fun p q : List α × Set α => List.SublistForall₂ r p.1 q.1 ∧ DomOrder r p.2 q.2) :=
    WellQuasiOrdered.prod hwqo_list hdom_wqo
  obtain ⟨a, b, hab, hwgood, hSgood⟩ := hprod_wqo (fun n => (w n, S n))
  -- Step 4: build the index embedding for the regular tails using hSgood + regularity
  have hpt : ∀ i, ∃ j, r (G a i) (G b j) := fun i => by
    obtain ⟨y, ⟨j, hy_mem⟩, hy_rel⟩ := hSgood (G a i) ⟨i, refl (G a i)⟩
    exact ⟨j, _root_.trans hy_rel hy_mem⟩
  have hbuild : ∀ (start i : ℕ), ∃ j, start < j ∧ r (G a i) (G b j) := fun start i => by
    obtain ⟨j0, hj0⟩ := hpt i
    obtain ⟨j, hmem, hgt⟩ := Set.Infinite.exists_gt (hkk b j0) start
    exact ⟨j, hgt, IsTrans.trans _ _ _ hj0 hmem⟩
  obtain ⟨eG, heG_mono, heG_rel⟩ := exists_strictMono_of_greedy hbuild
  -- Step 5: build the index embedding for the finite heads from hwgood
  obtain ⟨φ, hφ_mono, hφ_rel⟩ := sublistForall₂_to_embedding r (w a) (w b) hwgood
  -- Step 6: combine the head embedding `φ` (below `kk a`) and the tail embedding
  -- `eG` (shifted by `kk b`) into a single strictly monotone `e : ℕ → ℕ` using
  -- `embed_combine`.
  refine ⟨a, b, hab, ?_⟩
  refine embed_combine r (F a) (F b) (kk a) (kk b)
    (fun n => if h : n < kk a then
        (φ (Fin.cast (hw_len a).symm ⟨n, h⟩)).val else 0)
    ?_ ?_ ?_ eG heG_mono ?_
  · -- bound: the head map stays below `kk b`
    intro n hn
    simp only [dif_pos hn]
    have h := (φ (Fin.cast (hw_len a).symm ⟨n, hn⟩)).isLt
    have hl := hw_len b
    omega
  · -- monotonicity of the head map
    intro m n hmn hn
    have hm : m < kk a := lt_trans hmn hn
    simp only [dif_pos hm, dif_pos hn]
    have h := hφ_mono (a := Fin.cast (hw_len a).symm ⟨m, hm⟩)
                      (b := Fin.cast (hw_len a).symm ⟨n, hn⟩) (by simpa using hmn)
    simpa using h
  · -- the head map witnesses `r`
    intro n hn
    simp only [dif_pos hn]
    have h := hφ_rel (Fin.cast (hw_len a).symm ⟨n, hn⟩)
    simpa [hw_def, List.get_eq_getElem, List.getElem_map, List.getElem_range,
      Fin.val_cast] using h
  · -- the tail map witnesses `r` (definitionally `G`)
    exact heG_rel

/-- **Abstract WQO double selection.**  Given a doubly-indexed family `s n i` in a
2-BQO preorder that is *antitone in `n`* (`s n i ≤ s m i` for `m ≤ n`), there is a
depth `m` and an offset `j` such that the shifted row `i ↦ s m (i + j)` is a regular
sequence and is dominated, term by term, into every deeper row at indices `≥ j`. -/
lemma wqo_double_selection {Q : Type*} {r : Q → Q → Prop} [IsPreorder Q r]
    (hbqo : TwoBQO r) (s : ℕ → ℕ → Q)
    (hdec : ∀ m n i : ℕ, m ≤ n → r (s n i) (s m i)) :
    ∃ (m j : ℕ),
      IsRegularSeq r (fun i => s m (i + j)) ∧
      ∀ n : ℕ, m < n → ∀ i : ℕ, ∃ i' : ℕ, j ≤ i' ∧ r (s m (i + j)) (s n i') := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ n, IsRegularSeq r (fun i => s n (i + k n)) := by
    have hwqo := hbqo.wellQuasiOrdered;
    exact ⟨ fun n => Classical.choose ( hwqo.eventuallyRegular r ( fun i => s n i ) ), fun n => Classical.choose_spec ( hwqo.eventuallyRegular r ( fun i => s n i ) ) ⟩;
  set j : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup k with hj_def;
  -- Step 3: The row sequence is EmbedForAll-antitone.
  have h_antitone : ∀ m n : ℕ, m ≤ n → EmbedForAll r (fun i => s n (i + j n)) (fun i => s m (i + j m)) := by
    intro m n hmn
    use fun i => i + (j n - j m);
    simp +decide only [StrictMono, add_lt_add_iff_right, imp_self, implies_true, true_and];
    intro i; convert hdec m n ( i + j n ) hmn using 1; rw [ add_assoc, tsub_add_cancel_of_le ( show j m ≤ j n from Finset.sup_mono ( Finset.range_mono ( by linarith ) ) ) ] ;
  obtain ⟨ m, hm ⟩ := WellQuasiOrdered.exists_forall_le_of_antitone ( hbqo.embedForAll_wqo ) ( fun n => fun i => s n ( i + j n ) ) h_antitone;
  refine ⟨ m, j m, ?_, ?_ ⟩;
  · have h_tail : IsRegularSeq r (fun i => s m (i + k m)) := by
      exact hk m;
    convert IsRegularSeq.tail h_tail ( j m - k m ) using 1;
    exact funext fun i => by rw [ add_assoc, Nat.sub_add_cancel ( show k m ≤ j m from Finset.le_sup ( f := k ) ( Finset.mem_range.mpr ( Nat.lt_succ_self m ) ) ) ] ;
  · intro n hn i
    obtain ⟨e, he_mono, he⟩ := hm n (le_of_lt hn);
    refine ⟨ e i + j n, ?_, ?_ ⟩;
    · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Finset.sup_mono ( Finset.range_mono ( by linarith ) ) );
    · exact he i
