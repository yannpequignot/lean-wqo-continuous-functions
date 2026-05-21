import WqoContinuousFunctions.PrelimMemo.Gluing

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `3_general_struct_memo.tex` — Definitions

This file contains the definitions from Chapter 3 (Pointed Gluing and the General
Structure) of the memoir on continuous reducibility between functions.

## Main definitions

* `zeroStream` — the constant zero sequence `0^ω` in the Baire space
* `prependZerosOne` — prepend `i` zeros and a `1` to a sequence
* `stripZerosOne` — strip `i` zeros and a `1` from a sequence
* `PointedGluingSet` — pointed gluing of a sequence of subsets of the Baire space
* `PointedGluingFun` — pointed gluing of a sequence of functions on the Baire space
* `IsRegularOrdSeq` — a sequence of ordinals is regular
* `RaySet` — the n-th ray of a set at a point
* `IsReducibleByPieces` — a sequence of functions is reducible by finite pieces to another
* `SetsConvergeTo` — a sequence of sets converges to a point
* `MaxDom` / `MaxFun` — domain and maximum function `ℓ_α` (Definition 3.5)
* `MinDom` / `MinFun` — domain and minimum function `k_{α+1}` (Definition 3.5)
-/

noncomputable section

/-!
## Baire space operations for pointed gluing
-/



/-- Prepend `i` zeros followed by a `1` to a sequence `x : ℕ → ℕ`.
This produces the sequence `(0)^i ⌢ (1) ⌢ x`. -/
def prependZerosOne (i : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if k < i then 0
    else if k = i then 1
    else x (k - i - 1)

/-- Strip `i` zeros and a `1` from the front of a sequence.
Inverse of `prependZerosOne i` when the sequence starts with `(0)^i ⌢ (1)`. -/
def stripZerosOne (i : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => x (k + i + 1)

theorem stripZerosOne_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    stripZerosOne i (prependZerosOne i x) = x := by
  ext k; simp only [stripZerosOne, prependZerosOne]
  have h1 : ¬ (k + i + 1 < i) := by omega
  have h2 : ¬ (k + i + 1 = i) := by omega
  simp [h1, h2]
  congr 1; omega

theorem prependZerosOne_head_eq_zero (i : ℕ) (x : ℕ → ℕ) (k : ℕ) (hk : k < i) :
    prependZerosOne i x k = 0 := by
  simp [prependZerosOne, hk]

theorem prependZerosOne_at_i (i : ℕ) (x : ℕ → ℕ) :
    prependZerosOne i x i = 1 := by
  simp [prependZerosOne]

/-- A sequence starts with `i` zeros followed by a `1`. -/
def StartsWithZerosOne (i : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ k, k < i → x k = 0) ∧ x i = 1

theorem startsWithZerosOne_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    StartsWithZerosOne i (prependZerosOne i x) :=
  ⟨fun k hk => prependZerosOne_head_eq_zero i x k hk,
   prependZerosOne_at_i i x⟩

/-- `prependZerosOne i` is injective. -/
theorem prependZerosOne_injective (i : ℕ) : Injective (prependZerosOne i) := by
  intro x y h
  have := congr_arg (stripZerosOne i) h
  rwa [stripZerosOne_prependZerosOne, stripZerosOne_prependZerosOne] at this

/-!
## Pointed Gluing of Sets
-/

/-- The pointed gluing of a sequence `(F_i)_{i ∈ ℕ}` of subsets of the Baire space:
$$\mathrm{pgl}_{i \in \mathbb{N}} F_i = \{0^\omega\} \cup \bigcup_{i \in \mathbb{N}} (0)^i (1) F_i$$
-/
def PointedGluingSet (F : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {zeroStream} ∪ ⋃ i, prependZerosOne i '' (F i)

/-- `zeroStream` is always in the pointed gluing. -/
theorem zeroStream_mem_pointedGluingSet (F : ℕ → Set (ℕ → ℕ)) :
    zeroStream ∈ PointedGluingSet F :=
  Or.inl rfl

/-- If `x ∈ F i`, then `prependZerosOne i x ∈ PointedGluingSet F`. -/
theorem prependZerosOne_mem_pointedGluingSet (F : ℕ → Set (ℕ → ℕ)) (i : ℕ) (x : ℕ → ℕ)
    (hx : x ∈ F i) : prependZerosOne i x ∈ PointedGluingSet F :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hx⟩)

/-!
## Pointed Gluing of Functions

We define the pointed gluing abstractly, specifying its behavior on the base point
`0^ω` and on each block `(0)^i(1) · A_i`.
-/

/-- The first index `k` where `x k ≠ 0`, if it exists. For sequences in the pointed
gluing (other than `0^ω`), this is the block index `i`. -/
noncomputable def firstNonzero (x : ℕ → ℕ) : ℕ :=
  if h : ∃ k, x k ≠ 0 then Nat.find h else 0



/-- The pointed gluing of a sequence of functions `(f_i : A_i → B_i)_{i ∈ ℕ}` on the
Baire space. Maps:
- `(0)^i (1) x' ↦ (0)^i (1) f_i(x')` if `x' ∈ A_i`
- `0^ω ↦ 0^ω` (and anything else to `0^ω`)
-/
noncomputable def PointedGluingFun
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) : ℕ → ℕ :=
  if _ : x.val = zeroStream then zeroStream
  else
    let i := firstNonzero x.val
    if hmem : stripZerosOne i x.val ∈ A i then
      prependZerosOne i (f i ⟨stripZerosOne i x.val, hmem⟩).val
    else zeroStream

/-!
## Regular Ordinal Sequences
-/

/-- A sequence `(α_n)_{n ∈ ℕ}` of ordinals is *regular* when for all `m ∈ ℕ` there
exists `n > m` such that `α_m ≤ α_n`. Equivalently, the sequence is cofinal
in its supremum infinitely often. -/
def IsRegularOrdSeq (α : ℕ → Ordinal.{0}) : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, m < n ∧ α m ≤ α n

/-!
## Rays of Sets and Functions
-/

/-- For `B ⊆ ℕ → ℕ`, `y ∈ ℕ → ℕ`, and `n ∈ ℕ`, the *n-th ray of `B` at `y`* is:
$$\mathrm{Ray}(B, y, n) = \{x \in B \mid y|_n \sqsubseteq x \text{ and } y|_{n+1} \not\sqsubseteq x\}$$
The elements of `B` that agree with `y` on the first `n` coordinates but differ at
position `n`. This is a clopen subset of `B`. -/
def RaySet (B : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {x ∈ B | (∀ k, k < n → x k = y k) ∧ x n ≠ y n}

/-!
## Reducibility by Pieces
-/

/-- A sequence of functions `(f_i)_{i ∈ ℕ}` is *reducible by finite pieces* to a
sequence `(g_j)_{j ∈ ℕ}` if there is a family `(I_n)_{n ∈ ℕ}` of pairwise disjoint
finite subsets of `ℕ` such that for all `n`, `f_n ≤ ⊔_{i ∈ I_n} g_i`. -/
def IsReducibleByPieces
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : ℕ → (X → Y)) (g : ℕ → (X' → Y')) : Prop :=
  ∃ (I : ℕ → Finset ℕ),
    (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
    ∀ n, ∃ (σ : X → X') (τ : Y' → Y), Continuous σ ∧ Continuous τ ∧
      ∀ x, f n x = τ (g n (σ x))

/-!
## Convergence of Sets to a Point
-/

/-- A sequence of subsets `(A_n)_{n ∈ ℕ}` of a topological space *converges* to a
point `a` if for every open neighborhood `U` of `a`, there exists `m` such that
`A_n ⊆ U` for all `n ≥ m`. -/
def SetsConvergeTo {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (a : X) : Prop :=
  ∀ U : Set X, IsOpen U → a ∈ U → ∃ m : ℕ, ∀ n, m ≤ n → A n ⊆ U


/-!
## Minimum and Maximum Function Domains (Definition 3.5 / Def_MinMaxFunc)

We define by transfinite induction on `α` two families of subsets of the Baire space:
- `MaxDom α` — the domain of the maximum function `ℓ_α` in `𝒞_{≤α}`
- `MinDom α` — the domain of the minimum function `k_{α+1}` in `𝒞_{α+1}`

The functions themselves are identities on their domains (cf. the remark after the
definition in the memoir).

### Base cases
- `MaxDom 0 = ∅` (the empty function)
- `MinDom 0 = PointedGluingSet (fun _ => ∅)` = `{0^ω}` (i.e., `k_1 = pgl(∅)`)

### Successor step (`α = β + 1`)
- `MaxDom (β + 1) = GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom β))`
  (i.e., `ℓ_{β+1} = ω · pgl(ℓ_β)`)
- `MinDom (β + 1) = PointedGluingSet (fun _ => MinDom β)`
  (i.e., `k_{β+2} = pgl(k_{β+1})`)

### Limit step
- `MaxDom α = GluingSet (fun n => MaxDom (enumBelow α n))`
  (i.e., `ℓ_α = ⊔_n ℓ_{β_n}` for an enumeration `(β_n)_n` of `α`)
- `MinDom α = PointedGluingSet (fun n => MinDom (cofinalSeq α n))`
  (i.e., `k_{α+1} = pgl_n k_{α_n+1}` for a cofinal sequence `(α_n)_n` in `α`)

The notation `MinDom α` corresponds to the domain of `k_{α+1}`, not `k_α`.
-/

/-- An enumeration of ordinals below a countable ordinal `α`.
For a nonzero `α`, returns a function `ℕ → Ordinal.{0}` whose range covers `{β | β < α}`
whenever `α < ω₁` (i.e., when `Iio α` is countable).
For `α = 0`, returns the constant 0 function. The specific enumeration is chosen
by `Classical.choice`; up to continuous equivalence, the definitions do not depend
on this choice (see the remark after Definition 3.5 in the memoir). -/
noncomputable def enumBelow (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : α = 0 then fun _ => 0
  else
    have : Nonempty (Iio α) := ⟨⟨0, bot_lt_iff_ne_bot.mpr h⟩⟩
    if hc : ∃ f : ℕ → Iio α, Function.Surjective f then
      fun n => (hc.choose n).val
    else
      fun n => (Classical.arbitrary (ℕ → Iio α) n).val

/-- `enumBelow α n < α` whenever `α > 0`. -/
theorem enumBelow_lt (α : Ordinal.{0}) (hα : α ≠ 0) (n : ℕ) : enumBelow α n < α := by
  have hne : Nonempty (Set.Iio α) := ⟨⟨0, bot_lt_iff_ne_bot.mpr hα⟩⟩
  unfold enumBelow; rw [dif_neg hα]
  split
  · exact (‹∃ f : ℕ → Iio α, Function.Surjective f›.choose _).prop
  · exact (Classical.arbitrary (ℕ → Set.Iio α) n).prop

/-- `enumBelow α` is surjective onto `Iio α` whenever `α < ω₁` and `α ≠ 0`. -/
theorem enumBelow_surj (α : Ordinal.{0}) (hα : α < omega1) (hne : α ≠ 0) :
    Function.Surjective (fun n => ⟨enumBelow α n, enumBelow_lt α hne n⟩ : ℕ → Iio α) := by
  have hne' : Nonempty (Set.Iio α) := ⟨⟨0, bot_lt_iff_ne_bot.mpr hne⟩⟩
  have hc : (Set.Iio α).Countable := by
    rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
    unfold omega1 at hα; by_contra h; push_neg at h; exact not_le.mpr hα (Cardinal.ord_le.mpr h)
  have hc' : Countable (Set.Iio α) := hc.to_subtype
  have hsurj : ∃ f : ℕ → Iio α, Function.Surjective f := exists_surjective_nat (Set.Iio α)
  intro ⟨β, hβ⟩
  have key : ∃ n, (hsurj.choose n) = ⟨β, hβ⟩ := hsurj.choose_spec ⟨β, hβ⟩
  obtain ⟨n, hn⟩ := key
  use n
  simp only [Subtype.mk.injEq]
  show enumBelow α n = β
  unfold enumBelow; rw [dif_neg hne, dif_pos hsurj]
  exact congr_arg Subtype.val hn

/-- An arbitrary cofinal sequence in a countable limit ordinal `α`.
For limit `α > 0`, returns a sequence `(α_n)_n` that is cofinal in `α` and
satisfies `α_n < α` for all `n`. For non-limit or zero `α`, returns the constant
0 function. -/
noncomputable def cofinalSeq (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if _ : Order.IsSuccLimit α ∧ α ≠ 0 then enumBelow α
  else fun _ => 0

/-- `cofinalSeq α n < α` whenever `α` is a nonzero limit ordinal. -/
theorem cofinalSeq_lt (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (hα : α ≠ 0) (n : ℕ) :
    cofinalSeq α n < α := by
  unfold cofinalSeq; rw [dif_pos ⟨hlim, hα⟩]
  exact enumBelow_lt α hα n

/-- Domain of the maximum function `ℓ_α` (Definition 3.5 in the memoir).
`MaxDom α` is the domain of the function `ℓ_α`, which is the maximum
of `𝒞_{≤α}` (all scattered functions of CB-rank at most `α`). -/
noncomputable def MaxDom : Ordinal.{0} → Set (ℕ → ℕ) :=
  fun α => α.limitRecOn
    (∅ : Set (ℕ → ℕ))
    (fun _ dom_β => GluingSet (fun _ => PointedGluingSet (fun _ => dom_β)))
    (fun o hlim ih => GluingSet (fun n => ih (enumBelow o n)
      (enumBelow_lt o (Order.IsSuccLimit.ne_bot hlim) n)))

/-- Domain of the successor maximum function `ℓ_{succ α}` (Definition 3.5).
`SuccMaxDom α = PointedGluingSet (fun _ => MaxDom α)`. -/
noncomputable def SuccMaxDom : Ordinal.{0} → Set (ℕ → ℕ) :=
  fun α => PointedGluingSet (fun _ => MaxDom α)


/-- Domain of the minimum function `k_{α+1}` (Definition 3.5 in the memoir).
`MinDom α` is the domain of the function `k_{α+1}`, which is the minimum
of `𝒞_{≥α+1}` (all scattered functions of CB-rank at least `α + 1`).

Note: `MinDom α` corresponds to `k_{α+1}` in the memoir notation.-/
noncomputable def MinDom : Ordinal.{0} → Set (ℕ → ℕ) :=
  fun α => α.limitRecOn
    (PointedGluingSet (fun _ => ∅))
    (fun _ dom_β => PointedGluingSet (fun _ => dom_β))
    (fun o hlim ih => PointedGluingSet (fun n => ih (cofinalSeq o n)
      (cofinalSeq_lt o hlim (Order.IsSuccLimit.ne_bot hlim) n)))

/-- The maximum function `ℓ_α : MaxDom α → ℕ → ℕ` is the identity on `MaxDom α`.
Since the Gluing and Pointed Gluing operations commute with the identity, the
min and max functions are identity functions on their domains (subtype coercion). -/
noncomputable def MaxFun (α : Ordinal.{0}) : MaxDom α → (ℕ → ℕ) :=
  Subtype.val

/-- The successor maximum function `ℓ_{succ α}` (Definition 3.5).
Like `MaxFun`, this is just the subtype coercion. -/
noncomputable def SuccMaxFun (α : Ordinal.{0}) : SuccMaxDom α → (ℕ → ℕ) :=
  Subtype.val

/-- The minimum function `k_{α+1} : MinDom α → ℕ → ℕ` is the identity on `MinDom α`.
Since the Gluing and Pointed Gluing operations commute with the identity, the
min and max functions are identity functions on their domains (subtype coercion).
Warning MinFun α has CB rank α +1!
-/
noncomputable def MinFun (α : Ordinal.{0}) : MinDom α → (ℕ → ℕ) :=
  Subtype.val

end
