
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic
import BQO.Ramsey

open Set

set_option autoImplicit false

noncomputable section

open Classical

/-- The first uncountable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord
/-!
## Perfect vs Bad dichotomy for sequences in a quasi-order `(Q, ≤)`:
-/
namespace Sequences

def IsBad {α : Type*} (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ (m n : ℕ), m < n → ¬ r (f m) (f n)

def IsPerfect {α : Type*} (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ (m n : ℕ), m < n → r (f m) (f n)

theorem perfect_or_bad {α : Type*} (r : α → α → Prop)
    (f : ℕ → α) : ∃ e : ℕ → ℕ, ∃ (_he_mono : StrictMono e),
    (IsPerfect r (f ∘ e) ∨ IsBad r (f ∘ e)) := by
  obtain ⟨e, he_mono, k, hk⟩ := @infinite_ramsey_pairs Bool inferInstance
    (fun m n (hmn : m < n) => decide (¬ r (f m) (f n)))
  refine ⟨e, he_mono, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hk_true | hk_false
  · right
    intro m n hmn
    have h_color := hk m n hmn
    rw [hk_true] at h_color
    simpa [decide_eq_true_eq, Function.comp] using h_color
  · left
    intro m n hmn
    have h_color := hk m n hmn
    rw [hk_false] at h_color
    simpa [decide_eq_false_iff_not, Function.comp] using h_color

end Sequences

/-!
## Regular sequences
A sequence `(f i)_{i ∈ ℕ}` in a quasi-order `(Q, ≤)` is **regular**
if for every `i : ℕ`, the set `{j : ℕ | f i ≤ f j}` is infinite. -/
namespace Preorder

def IsRegularSeq {Q : Type*} (le : Q → Q → Prop) [IsPreorder Q le]
    (f : ℕ → Q) : Prop :=
  ∀ i : ℕ, Set.Infinite {j : ℕ | le (f i) (f j)}

/-- A regular sequence has arbitrarily large indices dominating any given index:
for every `i` and threshold `N` there is `j ≥ N` with `f i ≤ f j`. -/
lemma IsRegularSeq.exists_ge {Q : Type*} {le : Q → Q → Prop} [IsPreorder Q le]
    {f : ℕ → Q} (hf : IsRegularSeq le f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ le (f i) (f j) := by
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt N
  exact ⟨j, hj_gt.le, hj_mem⟩

/-- A tail of a regular sequence is regular. -/
lemma IsRegularSeq.tail {Q : Type*} {r : Q → Q → Prop} [IsPreorder Q r]
    {f : ℕ → Q} (hf : IsRegularSeq r f) (k : ℕ) :
    IsRegularSeq r (fun i => f (i + k)) := by
  intro i;
  have h_infinite : Set.Infinite {j | r (f (i + k)) (f j)} := by
    exact hf ( i + k );
  exact Set.infinite_of_forall_exists_gt fun n => by rcases h_infinite.exists_gt ( n + k ) with ⟨ j, hj₁, hj₂ ⟩ ; exact ⟨ j - k, by simpa [ Nat.sub_add_cancel ( show k ≤ j from by linarith ) ] using hj₁, by linarith [ Nat.sub_add_cancel ( show k ≤ j from by linarith ) ] ⟩ ;

end Preorder

open Preorder

private lemma key_reformulation {Q : Type*} (le : Q → Q → Prop) (f : ℕ → Q)
    (hcon : ∀ n, ∃ i, {j : ℕ | le (f (i + n)) (f (j + n))}.Finite) :
    ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | le (f i) (f j)}.Finite := by
  intro m
  obtain ⟨i, hfin⟩ := hcon m
  refine ⟨i + m, by omega, ?_⟩
  have hsplit : {j : ℕ | le (f (i+m)) (f j)}
      = {j : ℕ | j < m ∧ le (f (i+m)) (f j)}
        ∪ (fun k => k + m) '' {k : ℕ | le (f (i+m)) (f (k+m))} := by
    ext j
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hj
      rcases lt_or_ge j m with h | h
      · exact Or.inl ⟨h, hj⟩
      · exact Or.inr ⟨j - m, by simpa [Nat.sub_add_cancel h] using hj,
                       Nat.sub_add_cancel h⟩
    · rintro (⟨_, hj⟩ | ⟨k, hk, rfl⟩)
      · exact hj
      · exact hk
  rw [hsplit]
  apply Set.Finite.union
  · exact (Set.finite_Iio m).subset (fun j ⟨hj, _⟩ => hj)
  · exact hfin.image _

private lemma exists_bad_seq {Q : Type*} (le : Q → Q → Prop) (f : ℕ → Q)
    (key : ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | le (f i) (f j)}.Finite) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧
      ∀ m n, m < n → ¬ le (f (idx m)) (f (idx n)) := by
  let S := {p : ℕ × ℕ // ∀ j, le (f p.1) (f j) → j ≤ p.2}
  have succ_step : ∀ p : S, ∃ q : S, p.1.1 < q.1.1 ∧ p.1.2 < q.1.1 := by
    rintro ⟨⟨i, B⟩, hB⟩
    obtain ⟨i', hi'_ge, hfin'⟩ := key (max (i + 1) (B + 1))
    obtain ⟨B', hB'⟩ := hfin'.bddAbove
    refine ⟨⟨(i', max B' i'), fun j hj => le_trans (hB' hj) (le_max_left _ _)⟩, ?_, ?_⟩
    · show i < i'
      have h := le_trans (le_max_left (i+1) (B+1)) hi'_ge
      omega
    · show B < i'
      have h := le_trans (le_max_right (i+1) (B+1)) hi'_ge
      omega
  -- starting point
  obtain ⟨i₀, _, hfin₀⟩ := key 0
  obtain ⟨B₀, hB₀⟩ := hfin₀.bddAbove
  let p0 : S := ⟨(i₀, B₀), hB₀⟩
  let nextOf : S → S := fun p => (succ_step p).choose
  let seq : ℕ → S := fun k => Nat.rec p0 (fun _ q => nextOf q) k
  have hseq_succ : ∀ k, seq (k+1) = nextOf (seq k) := fun k => rfl
  have hstep : ∀ p : S, p.1.1 < (nextOf p).1.1 ∧ p.1.2 < (nextOf p).1.1 :=
    fun p => (succ_step p).choose_spec
  set idx : ℕ → ℕ := fun k => (seq k).1.1 with hidx
  set bd : ℕ → ℕ := fun k => (seq k).1.2 with hbd
  have hidx_lt : ∀ k, idx k < idx (k+1) := fun k => by
    show (seq k).1.1 < (seq (k+1)).1.1
    rw [hseq_succ k]
    exact (hstep (seq k)).1
  have hbd_lt_idx : ∀ k, bd k < idx (k+1) := fun k => by
    show (seq k).1.2 < (seq (k+1)).1.1
    rw [hseq_succ k]
    exact (hstep (seq k)).2
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ hidx_lt
  -- bd is also increasing in the same "rate": bd k < idx (k+1) ≤ idx n for n > k
  refine ⟨idx, hidx_mono, ?_⟩
  intro m n hmn hle
  have hbound := (seq m).2  -- ∀ j, le (f (idx m)) (f j) → j ≤ bd m
  have h1 : idx n ≤ bd m := hbound (idx n) hle
  have h2 : bd m < idx (m+1) := hbd_lt_idx m
  have h3 : idx (m+1) ≤ idx n := hidx_mono.le_iff_le.mpr hmn
  omega

/--
In a WQO every sequence is eventually regular.
In fact, this is an equivalent definition of WQO,
since a bad sequence is precisely a sequence with no tail that is regular.
-/
theorem WellQuasiOrdered.eventuallyRegular {Q : Type*} (le : Q → Q → Prop) [IsPreorder Q le]
    (hwqo : WellQuasiOrdered le) (f : ℕ → Q) :
    ∃ n : ℕ, IsRegularSeq le (fun i => f (i + n)) := by
  by_contra hcon
  push_neg at hcon
  simp only [IsRegularSeq, not_forall, Set.not_infinite] at hcon
  have key := key_reformulation le f hcon
  obtain ⟨idx, _, hbad⟩ := exists_bad_seq le f key
  obtain ⟨m, n, hmn, hrel⟩ := hwqo (fun k => f (idx k))
  exact hbad m n hmn hrel

/-- In a WQO, an antitone sequence stabilizes from above: there is an index `m` from
which the sequence becomes `r`-dominated by `a m` (so, together with antitonicity,
`a m` is `r`-equivalent to every later term). -/
lemma WellQuasiOrdered.exists_forall_le_of_antitone {β : Type*} {r : β → β → Prop}
    [IsPreorder β r] (hwqo : WellQuasiOrdered r) (a : ℕ → β)
    (hanti : ∀ m n : ℕ, m ≤ n → r (a n) (a m)) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → r (a m) (a n) := by
  by_contra h_contra;
  obtain ⟨idx, hidx⟩ : ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ k, ¬r (a (idx k)) (a (idx (k + 1))) := by
    have h_seq : ∀ k, ∃ n > k, ¬r (a k) (a n) := by
      exact fun k => by push_neg at h_contra; obtain ⟨ n, hn₁, hn₂ ⟩ := h_contra k; exact ⟨ n, lt_of_le_of_ne hn₁ ( by aesop_cat ), hn₂ ⟩ ;
    choose f hf using h_seq;
    use fun k => Nat.recOn k 0 fun k ih => f ih;
    exact ⟨ strictMono_nat_of_lt_succ fun k => hf _ |>.1, fun k => hf _ |>.2 ⟩;
  obtain ⟨ k, l, hkl, h ⟩ := hwqo ( fun n => a ( idx n ) );
  have := hidx.1.monotone ( Nat.succ_le_of_lt hkl );
  exact hidx.2 k ( by exact ‹IsPreorder β r›.trans _ _ _ h ( hanti _ _ this ) )

/-!
## Higman's order on finite sequences

Given a quasi-order `(Q, ≤Q)`, Higman's order on `List Q` relates `l₁ ≤ l₂` iff `l₁` embeds into
`l₂` as a pointwise-`≤Q`-dominated subsequence. Mathlib already provides this as
`List.SublistForall₂ (· ≤ ·)`, with `Std.Refl`/`IsTrans` instances and Higman's lemma itself
(`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`); we only need to bundle the
former into an `IsPreorder` instance (Mathlib doesn't do so automatically), used below by
`WellQuasiOrdered.prod` in `TwoBQO.embedForAll_wqo`.
-/

instance List.SublistForall₂.instIsPreorder {α : Type*} (r : α → α → Prop) [IsPreorder α r] :
    IsPreorder (List α) (List.SublistForall₂ r) where
  refl := (List.SublistForall₂.is_refl (Rₐ := r)).refl
  trans := (List.SublistForall₂.is_trans (Rₐ := r)).trans
