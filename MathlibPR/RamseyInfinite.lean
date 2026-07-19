/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Nth

/-!
# The infinite Ramsey theorem for pairs and triples

This file proves the infinite Ramsey theorem (RT²) for `κ`-colourings of pairs of naturals, and
its iterate (RT³) for triples. Both are proved by the same "fan" argument, iterated pigeonhole on
a decreasing chain of infinite sets of vertices.

## Main results

* `infinite_ramsey_pairs`: every finite colouring `c` of the pairs `m < n` of `ℕ` has an infinite
  monochromatic set, i.e. a strictly monotone `e : ℕ → ℕ` and a colour `k` with
  `c (e m) (e n) = k` for every `m < n`.
* `infinite_ramsey_triples`: the analogous statement for triples `m < n < l`, proved by applying
  `infinite_ramsey_pairs` one dimension up.

## Implementation notes

`infinite_ramsey_pairs` is proved by building an infinite sequence of "states" `(aₙ, colₙ, Sₙ)`,
where `Sₙ` is an infinite set of naturals above `aₙ` on which the fan coloured from `aₙ` is
constantly `colₙ`; a final pigeonhole on the (finitely many) fan colours `colₙ` produces the
monochromatic subsequence. `infinite_ramsey_triples` repeats the same construction one level up,
using `infinite_ramsey_pairs` itself to colour the fan from each vertex.
-/

open Set

noncomputable section

/-- Every infinite set of naturals can be enumerated by a strictly monotone function. -/
theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s :=
  ⟨Nat.nth (· ∈ s), Nat.nth_strictMono hs, Nat.nth_mem_of_infinite hs⟩

/-- Pigeonhole for a finite colouring of `ℕ`: some colour class is infinite, and it can be
enumerated by a strictly monotone function. -/
theorem Function.exists_strictMono_eq_of_finite_coloring {κ : Type*} [Fintype κ]
    (f : ℕ → κ) : ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ k : κ, ∀ i, f (e i) = k := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  have hk' : (f ⁻¹' {k}).Infinite := Set.infinite_coe_iff.mp hk
  obtain ⟨e, he, hmem⟩ := hk'.exists_strictMono
  exact ⟨e, he, k, hmem⟩

/-- An intermediate state in the construction of `infinite_ramsey_pairs`: a vertex `vert`, the
constant colour `col` of the fan from `vert` into the infinite successor set `succ`, all of whose
elements exceed `vert`. -/
private structure RamseyState (κ : Type*) [Fintype κ]
    (c : ∀ (m n : ℕ), m < n → κ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hcol : ∀ x ∈ succ, ∀ h : vert < x, c vert x h = col

/-- **The infinite Ramsey theorem for pairs (RT²).** Every finite colouring of the pairs `m < n`
of `ℕ` has an infinite monochromatic set: a strictly monotone `e : ℕ → ℕ` and a colour `k` such
that `c (e m) (e n) = k` for every `m < n`.

Proved by iterated pigeonhole: maintain a decreasing chain of states `(aₙ, colₙ, Sₙ)` where
`Sₙ` is infinite, lies above `aₙ`, and the fan from `aₙ` into `Sₙ` is constantly `colₙ`; then
pigeonhole once more on the (finitely many) fan colours `colₙ` to extract a monochromatic
subsequence of vertices. -/
theorem infinite_ramsey_pairs {κ : Type*} [Fintype κ]
    (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by
  -- Given a vertex `a` and an infinite successor set `S` above it, produce the next vertex
  -- `a' = min S`, the fan-colour `col` from `a'`, and an infinite monochromatic `S' ⊆ S` above
  -- `a'`.
  have step :
      ∀ (a : ℕ) (S : Set ℕ), S.Infinite → (∀ x ∈ S, a < x) →
      ∃ a' ∈ S, ∃ col : κ, ∃ S' : Set ℕ,
        S'.Infinite ∧ S' ⊆ S ∧
        (∀ x ∈ S', a' < x) ∧
        (∀ x ∈ S', ∀ h : a' < x, c a' x h = col) := by
    intro a S hS hlt
    set a' := sInf S with ha'_def
    have ha'S : a' ∈ S := Nat.sInf_mem hS.nonempty
    have ha'mn : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.sInf_le hx
    -- `S \ {a'}` is infinite, all elements strictly above `a'`.
    have hS'inf : (S \ {a'}).Infinite := hS.diff (Set.finite_singleton a')
    have hS'gt : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
      Nat.lt_of_le_of_ne (ha'mn x hxS)
        (fun h => hxne (h ▸ Set.mem_singleton_iff.mpr rfl))
    -- Enumerate `S \ {a'}` and pigeonhole on the fan colouring.
    obtain ⟨enum, henum_mono, henum_mem⟩ := hS'inf.exists_strictMono
    let fanCol : ℕ → κ := fun n => c a' (enum n) (hS'gt _ (henum_mem n))
    obtain ⟨enum', henum'_mono, col, hcol⟩ := fanCol.exists_strictMono_eq_of_finite_coloring
    refine ⟨a', ha'S, col, Set.range (enum ∘ enum'),
        Set.infinite_range_of_injective (henum_mono.injective.comp henum'_mono.injective),
        ?_, ?_, ?_⟩
    · rintro x ⟨n, rfl⟩; exact (henum_mem (enum' n)).1
    · rintro x ⟨n, rfl⟩; exact hS'gt _ (henum_mem (enum' n))
    · rintro x ⟨n, rfl⟩ h
      have : fanCol (enum' n) = col := hcol n
      simpa [fanCol] using this
  -- Build the chain of states starting from `(0, Set.Ioi 0)`.
  obtain ⟨a₀, _, col₀, S₀, hS₀inf, _, hS₀gt, hS₀col⟩ :=
    step 0 (Set.Ioi 0)
      (Set.infinite_of_injective_forall_mem Nat.succ_injective fun n => Nat.succ_pos n)
      fun x hx => hx
  let s₀ : RamseyState κ c := ⟨a₀, col₀, S₀, hS₀inf, hS₀gt, hS₀col⟩
  have advance : ∀ s : RamseyState κ c, ∃ s' : RamseyState κ c,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, _col, S, hSinf, hSgt, _hScol⟩
    obtain ⟨a', ha'S, col', S', hS'inf, hS'sub, hS'gt, hS'col⟩ := step a S hSinf hSgt
    exact ⟨⟨a', col', S', hS'inf, hS'gt, hS'col⟩, ha'S, hS'sub⟩
  let states : ℕ → RamseyState κ c := fun n => n.rec s₀ fun _ s => (advance s).choose
  have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
    fun n => (advance (states n)).choose_spec.1
  have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
    fun n => (advance (states n)).choose_spec.2
  have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
    fun n => (states n).hgt _ (I1 n)
  have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
    intro m n hmn
    induction n with
    | zero => simp [Nat.le_zero.mp hmn]
    | succ n ih =>
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · exact (I2 n).trans (ih (Nat.lt_succ_iff.mp h))
      · exact le_refl _
  have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
    intro m n hmn
    cases n with
    | zero => exact absurd hmn (Nat.not_lt_zero m)
    | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
  have verts_strictMono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
  have I6 : ∀ m n (hmn : m < n),
      c (states m).vert (states n).vert (verts_strictMono hmn) = (states m).col :=
    fun m n hmn => (states m).hcol _ (I5 m n hmn) _
  -- Final pigeonhole on the (finitely many) fan colours `colₙ`.
  obtain ⟨idx, hidx, k, hk⟩ := (fun n => (states n).col).exists_strictMono_eq_of_finite_coloring
  refine ⟨fun n => (states (idx n)).vert, verts_strictMono.comp hidx, k, ?_⟩
  intro i j hij
  have h1 := I6 (idx i) (idx j) (hidx hij)
  have h2 := hk i
  convert h1.trans h2 using 2

/-- An intermediate state in the construction of `infinite_ramsey_triples`: a vertex `vert` such
that the colour of every triple `(vert, n, l)` with `n < l` both in the infinite successor set
`succ` above `vert` is constantly `col`. -/
private structure TripleState (κ : Type*) [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hcol : ∀ n ∈ succ, ∀ l ∈ succ, ∀ (hn : vert < n) (hl : n < l),
    c vert n l ⟨hn, hl⟩ = col

/-- **The infinite Ramsey theorem for triples (RT³).** Every finite colouring of the triples
`m < n < l` of `ℕ` has an infinite monochromatic set: a strictly monotone `e : ℕ → ℕ` and a
colour `k` such that `c (e h) (e i) (e j) = k` for every `h < i < j`.

Proved by replicating the pairs argument one level up: each step colours the fan from the current
vertex `a'` by applying `infinite_ramsey_pairs` to the induced pair-colouring
`(i, j) ↦ c (a', enumᵢ, enumⱼ)` on an enumeration of the successor set. -/
theorem infinite_ramsey_triples {κ : Type*} [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by
  have step :
      ∀ (a : ℕ) (S : Set ℕ), S.Infinite → (∀ x ∈ S, a < x) →
      ∃ a' ∈ S, ∃ col : κ, ∃ S' : Set ℕ,
        S'.Infinite ∧ S' ⊆ S ∧
        (∀ x ∈ S', a' < x) ∧
        (∀ n ∈ S', ∀ l ∈ S', ∀ (hn : a' < n) (hl : n < l),
          c a' n l ⟨hn, hl⟩ = col) := by
    intro a S hS hlt
    set a' := sInf S with ha'_def
    have ha'S : a' ∈ S := Nat.sInf_mem hS.nonempty
    have ha'mn : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.sInf_le hx
    have hTinf : (S \ {a'}).Infinite := hS.diff (Set.finite_singleton a')
    have hTgt : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
      Nat.lt_of_le_of_ne (ha'mn x hxS)
        (fun h => hxne (h ▸ Set.mem_singleton_iff.mpr rfl))
    obtain ⟨enum, henum_mono, henum_mem⟩ := hTinf.exists_strictMono
    -- Induce a pair-colouring on indices and apply RT².
    let c_pair : ∀ i j : ℕ, i < j → κ := fun i j hij =>
      c a' (enum i) (enum j) ⟨hTgt _ (henum_mem i), henum_mono hij⟩
    obtain ⟨idx, hidx, col, hcol⟩ := infinite_ramsey_pairs c_pair
    refine ⟨a', ha'S, col, Set.range (enum ∘ idx),
        Set.infinite_range_of_injective (henum_mono.injective.comp hidx.injective),
        ?_, ?_, ?_⟩
    · rintro x ⟨n, rfl⟩; exact (henum_mem (idx n)).1
    · rintro x ⟨n, rfl⟩; exact hTgt _ (henum_mem (idx n))
    · rintro n ⟨i, rfl⟩ l ⟨j, rfl⟩ hn hl
      have hij_idx : idx i < idx j := henum_mono.lt_iff_lt.mp (by exact_mod_cast hl)
      have hij : i < j := hidx.lt_iff_lt.mp hij_idx
      have key : c_pair (idx i) (idx j) hij_idx = col := hcol i j hij
      convert key using 2
  obtain ⟨a₀, _, col₀, S₀, hS₀inf, _, hS₀gt, hS₀col⟩ :=
    step 0 (Set.Ioi 0)
      (Set.infinite_of_injective_forall_mem Nat.succ_injective fun n => Nat.succ_pos n)
      fun x hx => hx
  let s₀ : TripleState κ c := ⟨a₀, col₀, S₀, hS₀inf, hS₀gt, hS₀col⟩
  have advance : ∀ s : TripleState κ c, ∃ s' : TripleState κ c,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, _col, S, hSinf, hSgt, _⟩
    obtain ⟨a', ha'S, col', S', hS'inf, hS'sub, hS'gt, hS'col⟩ := step a S hSinf hSgt
    exact ⟨⟨a', col', S', hS'inf, hS'gt, hS'col⟩, ha'S, hS'sub⟩
  let states : ℕ → TripleState κ c := fun n => n.rec s₀ fun _ s => (advance s).choose
  have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
    fun n => (advance (states n)).choose_spec.1
  have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
    fun n => (advance (states n)).choose_spec.2
  have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
    fun n => (states n).hgt _ (I1 n)
  have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
    intro m n hmn
    induction n with
    | zero => simp [Nat.le_zero.mp hmn]
    | succ n ih =>
      rcases Nat.lt_or_eq_of_le hmn with h | rfl
      · exact (I2 n).trans (ih (Nat.lt_succ_iff.mp h))
      · exact le_refl _
  have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
    intro m n hmn
    cases n with
    | zero => exact absurd hmn (Nat.not_lt_zero m)
    | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
  have verts_strictMono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
  have I6 : ∀ m n l (hmn : m < n) (hnl : n < l),
      c (states m).vert (states n).vert (states l).vert
        ⟨verts_strictMono hmn, verts_strictMono hnl⟩ = (states m).col := by
    intro m n l hmn hnl
    exact (states m).hcol
      _ (I5 m n hmn) _ (I5 m l (hmn.trans hnl))
      (verts_strictMono hmn) (verts_strictMono hnl)
  obtain ⟨idx, hidx, k, hk⟩ := (fun n => (states n).col).exists_strictMono_eq_of_finite_coloring
  refine ⟨fun n => (states (idx n)).vert, verts_strictMono.comp hidx, k, ?_⟩
  intro h i j ⟨hhi, hij⟩
  have h1 := I6 (idx h) (idx i) (idx j) (hidx hhi) (hidx hij)
  have h2 := hk h
  convert h1.trans h2 using 2

end
