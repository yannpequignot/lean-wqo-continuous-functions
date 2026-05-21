
import Mathlib

open Set

set_option autoImplicit false

noncomputable section

open Classical


/-!
## §1  Infinite Ramsey for pairs (RT²)

#PROVIDED SOLUTION
**Statement:** For every colouring `c : (m n : ℕ) → m < n → κ` with `κ` finite,
there exist a strictly increasing `e : ℕ → ℕ` and a colour `k` such that
`c (e m) (e n) = k` for all `m < n`.

**Proof** via iterated pigeonhole:

We build by recursion a sequence of triples `(aₙ, Xₙ, kₙ)` where
- `a₀ < a₁ < a₂ < ...` are natural numbers (the vertices of our eventual set),
- `Xₙ` is an infinite set of naturals, all `> aₙ`,
- `kₙ : κ` is the colour of the "fan" from `aₙ` into `Xₙ`:
  `c aₙ j = kₙ` for every `j ∈ Xₙ`.

**Initialisation:** Set `X₋₁ = ℕ`, `a₀ = 0`, colour the fan from `a₀` into
`ℕ \ {0}` using pigeonhole on κ to get `k₀` and infinite `X₀`.

**Inductive step:** Given `(aₙ, Xₙ, kₙ)`, set `aₙ₊₁ = min Xₙ`, colour the
fan from `aₙ₊₁` into `Xₙ \ {aₙ₊₁}` by pigeonhole to get `kₙ₊₁` and `Xₙ₊₁`.

The sequence `n ↦ kₙ` is a colouring of ℕ with κ. By pigeonhole on κ again,
some colour `k∗` appears for an infinite set of indices `N ⊆ ℕ`. The
subsequence `(aₙ)_{n ∈ N}` is strictly increasing and has
`c (aₘ) (aₙ) = k∗` for all `m < n` (because `aₙ ∈ Xₘ` and the fan colour
at `aₘ` over `Xₘ` is `k∗`).
-/

/-- Infinite pigeonhole: if `f : ℕ → κ` and `κ` is finite, some fibre is infinite. -/
theorem infinite_pigeonhole {κ : Type*} [Fintype κ] (f : ℕ → κ) :
    ∃ k : κ, (f ⁻¹' {k}).Infinite := by
  by_contra h
  push_neg at h
  have hfin : (univ : Set ℕ).Finite := by
    have : (univ : Set ℕ) = ⋃ k : κ, f ⁻¹' {k} := by ext; simp
    rw [this]
    exact finite_iUnion (fun k => h k)
  exact infinite_univ hfin

theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s := by
  have unbounded : ∀ n, ∃ m ∈ s, n < m := fun n => by
    by_contra h; push_neg at h
    exact hs (Set.Finite.subset (Set.finite_Iic n) (fun x hx => h x hx))
  -- Build e by primitive recursion, packaging (e n, proof) together.
  let P : ℕ → Type := fun _ => {v : ℕ // v ∈ s}
  let step : ∀ n, P n → P (n + 1) := fun n ⟨v, _⟩ =>
    let w := unbounded v
    ⟨Nat.find w, (Nat.find_spec w).1⟩
  let e : ℕ → ℕ := fun n =>
    (Nat.rec (motive := P)
      ⟨Nat.find (unbounded 0), (Nat.find_spec (unbounded 0)).1⟩
      step n).1
  have he_lt : ∀ n, e n < e (n + 1) := fun n =>
    (Nat.find_spec (unbounded (e n))).2
  have he_mem : ∀ n, e n ∈ s := fun n =>
    (Nat.rec (motive := P)
      ⟨Nat.find (unbounded 0), (Nat.find_spec (unbounded 0)).1⟩
      step n).2
  exact ⟨e, strictMono_nat_of_lt_succ he_lt, he_mem⟩

theorem Set.Infinite.from_strictMono {s : Set ℕ}
    (he : ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s) : s.Infinite := by
  obtain ⟨e, he_mono, he_mem⟩ := he
  exact Set.infinite_of_injective_forall_mem he_mono.injective he_mem

/-- Infinite pigeonhole: if `f : ℕ → κ` and `κ` is finite, some fibre is infinite. -/
theorem infinite_pigeonhole' {κ : Type*} [Fintype κ] (f : ℕ → κ) :
    ∃ (e : ℕ → ℕ), ∃ (_he : StrictMono e), ∃ k : κ, ∀ i : ℕ, f (e i) = k := by
  obtain ⟨k, hk⟩ := infinite_pigeonhole f
  obtain ⟨e, he, hek⟩ := hk.exists_strictMono
  exact ⟨e, he, k, fun i => hek i⟩



private structure RamseyState (κ : Type*) [Fintype κ]
    (c : ∀ (m n : ℕ), m < n → κ) where
  vert : ℕ
  col  : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt  : ∀ x ∈ succ, vert < x
  hcol : ∀ x ∈ succ, ∀ h : vert < x, c vert x h = col


/-
  Proof of infinite_ramsey_pairs.

  The argument uses two pigeonholes:
    (1) At each step, the fan colouring from the current vertex into its
        infinite successor set is monochromatic on an infinite sub-set
        (by infinite_pigeonhole).
    (2) The resulting sequence of fan-colours is monochromatic on an
        infinite sub-set of indices (by infinite_pigeonhole').

  The key invariant:
    state n = (aₙ, colₙ, Sₙ) where
      • Sₙ is infinite
      • every x ∈ Sₙ satisfies aₙ < x
      • c aₙ x _ = colₙ for every x ∈ Sₙ
      • aₙ₊₁ ∈ Sₙ  and  Sₙ₊₁ ⊆ Sₙ

  Consequence: for m < n, aₙ ∈ Sₘ, so c aₘ aₙ _ = colₘ.
-/
theorem infinite_ramsey_pairs {κ : Type*} [Fintype κ]
    (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by
  -- ----------------------------------------------------------------
  -- STEP LEMMA
  -- ----------------------------------------------------------------
  -- Given: vertex a, infinite set S with all elements > a.
  -- Returns: next vertex a' (= min S), fan-colour col, and an
  --          infinite monochromatic sub-set S' ⊆ S with all elements > a'.
  -- Also returns the membership a' ∈ S (needed for I1).
  have step :
      ∀ (a : ℕ) (S : Set ℕ), S.Infinite → (∀ x ∈ S, a < x) →
      ∃ a' ∈ S, ∃ col : κ, ∃ S' : Set ℕ,
        S'.Infinite ∧ S' ⊆ S ∧
        (∀ x ∈ S', a' < x) ∧
        (∀ x ∈ S', ∀ h : a' < x, c a' x h = col) := by
    intro a S hS hlt
    -- a' = minimum of S
    set a' := Nat.find hS.nonempty with ha'_def
    have ha'S  : a' ∈ S         := Nat.find_spec hS.nonempty
    have ha'mn : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.find_min' hS.nonempty hx
    -- S \ {a'} is infinite, all elements strictly above a'
    have hS'inf : (S \ {a'}).Infinite := by
      exact Set.Infinite.diff hS (Set.finite_singleton a')


    have hS'gt : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
    Nat.lt_of_le_of_ne (ha'mn x hxS)
      (fun h => hxne (h ▸ Set.mem_singleton_iff.mpr rfl))
    -- Enumerate S \ {a'}, apply pigeonhole to the fan colouring
    obtain ⟨enum, henum_mono, henum_mem⟩ := hS'inf.exists_strictMono
    let fanCol : ℕ → κ := fun n => c a' (enum n) (hS'gt _ (henum_mem n))
    obtain ⟨col, hcol_inf⟩ := infinite_pigeonhole fanCol
    -- S'' = image of the monochromatic index-set under enum
    refine ⟨a', ha'S, col, enum '' (fanCol ⁻¹' {col}),
        hcol_inf.image henum_mono.injective.injOn, ?_, ?_, ?_⟩
    · rintro x ⟨n, -, rfl⟩; exact (henum_mem n).1        -- S'' ⊆ S
    · rintro x ⟨n, -, rfl⟩; exact hS'gt _ (henum_mem n) -- elements > a'
    · rintro x ⟨n, hn, rfl⟩ h                           -- fan colour = col
      have : fanCol n = col := hn
      simp only [fanCol] at this
      convert this using 2
  -- ----------------------------------------------------------------
  -- INITIAL STATE
  -- ----------------------------------------------------------------
  obtain ⟨a₀, ha₀S, col₀, S₀, hS₀inf, _, hS₀gt, hS₀col⟩ :=
    step 0 (Set.Ioi 0)
      (Set.infinite_of_injective_forall_mem
        (Nat.succ_injective) (fun n => Nat.succ_pos n))
      (fun x hx => hx)
  -- ----------------------------------------------------------------
  -- ITERATION
  -- ----------------------------------------------------------------
  let s₀ : RamseyState κ c := ⟨a₀, col₀, S₀, hS₀inf, hS₀gt, hS₀col⟩
  have advance : ∀ s : RamseyState κ c, ∃ s' : RamseyState κ c,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, _col, S, hSinf, hSgt, _hScol⟩
    obtain ⟨a', ha'S, col', S', hS'inf, hS'sub, hS'gt, hS'col⟩ :=
      step a S hSinf hSgt
    exact ⟨⟨a', col', S', hS'inf, hS'gt, hS'col⟩, ha'S, hS'sub⟩
  let states : ℕ → RamseyState κ c :=
    fun n => n.rec s₀ (fun _ s => (advance s).choose)
  -- ----------------------------------------------------------------
  -- INVARIANTS
  -- ----------------------------------------------------------------
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
    | succ n =>
      have h1 : (states (n + 1)).vert ∈ (states n).succ := I1 n
      exact I4 m n (Nat.lt_succ_iff.mp hmn) h1
  have verts_strictMono : StrictMono (fun n => (states n).vert) :=
    strictMono_nat_of_lt_succ I3
  have I6 : ∀ m n (hmn : m < n),
      c (states m).vert (states n).vert (verts_strictMono hmn) = (states m).col :=
    fun m n hmn => (states m).hcol _ (I5 m n hmn) _
  -- ----------------------------------------------------------------
  -- PIGEONHOLE ON COLOURS
  -- ----------------------------------------------------------------
  obtain ⟨idx, hidx, k, hk⟩ := infinite_pigeonhole' (fun n => (states n).col)
  refine ⟨fun n => (states (idx n)).vert, verts_strictMono.comp hidx, k, ?_⟩
  intro i j hij
  have h1 := I6 (idx i) (idx j) (hidx hij)
  have h2 := hk i
  convert h1.trans h2 using 2



-- ----------------------------------------------------------------
-- Private structure for the triples proof (mirrors RamseyState for pairs)
-- ----------------------------------------------------------------
private structure TripleState (κ : Type*) [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) where
  vert : ℕ
  col  : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt  : ∀ x ∈ succ, vert < x
  -- For all n < l both in succ, c(vert, n, l) = col
  hcol : ∀ n ∈ succ, ∀ l ∈ succ, ∀ (hn : vert < n) (hl : n < l),
           c vert n l ⟨hn, hl⟩ = col

theorem infinite_ramsey_triples {κ : Type*} [Fintype κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by
  /-
    Strategy: replicate the pairs proof one level up.

    We maintain TripleStates (a, col, S) where
      • S is infinite,  all elements of S exceed a
      • for every n < l both in S, c(a, n, l) = col

    Step: given (a, col, S), pick a' = min S, enumerate S \ {a'},
    apply RT² (infinite_ramsey_pairs) to the pair colouring
      (i, j) ↦ c(a', enumᵢ, enumⱼ)
    to get a monochromatic subsequence idx with colour col'.
    Set S' = enum '' (range idx).  Return (a', col', S').

    Invariant consequence: for m < n < l,
      state_l.vert ∈ state_m.succ  (by I4 + I1)
    so c(state_m.vert, state_n.vert, state_l.vert) = state_m.col.

    Final pigeonhole on the colour sequence picks a monochromatic k.
  -/

  -- ----------------------------------------------------------------
  -- STEP LEMMA FOR TRIPLES
  -- ----------------------------------------------------------------
  have step :
      ∀ (a : ℕ) (S : Set ℕ), S.Infinite → (∀ x ∈ S, a < x) →
      ∃ a' ∈ S, ∃ col : κ, ∃ S' : Set ℕ,
        S'.Infinite ∧ S' ⊆ S ∧
        (∀ x ∈ S', a' < x) ∧
        (∀ n ∈ S', ∀ l ∈ S', ∀ (hn : a' < n) (hl : n < l),
          c a' n l ⟨hn, hl⟩ = col) := by
    intro a S hS hlt
    set a' := Nat.find hS.nonempty with ha'_def
    have ha'S  : a' ∈ S      := Nat.find_spec hS.nonempty
    have ha'mn : ∀ x ∈ S, a' ≤ x := fun x hx => Nat.find_min' hS.nonempty hx
    -- T = S \ {a'} is infinite; all elements strictly above a'
    have hTinf : (S \ {a'}).Infinite := hS.diff (Set.finite_singleton a')
    have hTgt  : ∀ x ∈ S \ {a'}, a' < x := fun x ⟨hxS, hxne⟩ =>
      Nat.lt_of_le_of_ne (ha'mn x hxS)
        (fun h => hxne (h ▸ Set.mem_singleton_iff.mpr rfl))
    -- Enumerate S \ {a'}
    obtain ⟨enum, henum_mono, henum_mem⟩ := hTinf.exists_strictMono
    -- Define the induced pair colouring on indices
    let c_pair : ∀ (i j : ℕ), i < j → κ := fun i j hij =>
      c a' (enum i) (enum j) ⟨hTgt _ (henum_mem i), henum_mono hij⟩
    -- Apply RT² to c_pair
    obtain ⟨idx, hidx, col, hcol⟩ := infinite_ramsey_pairs c_pair
    -- S' = {enum (idx n) | n : ℕ}
    refine ⟨a', ha'S, col, Set.range (enum ∘ idx),
        Set.infinite_range_of_injective (henum_mono.injective.comp hidx.injective),
        ?_, ?_, ?_⟩
    · -- S' ⊆ S (actually S' ⊆ S \ {a'} ⊆ S)
      rintro x ⟨n, rfl⟩; exact (henum_mem (idx n)).1
    · -- elements of S' > a'
      rintro x ⟨n, rfl⟩; exact hTgt _ (henum_mem (idx n))
    · -- c(a', n, l) = col for n < l both in S'
      rintro n ⟨i, rfl⟩ l ⟨j, rfl⟩ hn hl
      -- enum (idx i) < enum (idx j) means idx i < idx j (strict mono of enum)
      have hij_idx : idx i < idx j := henum_mono.lt_iff_lt.mp (by exact_mod_cast hl)
      -- i < j follows from strict mono of idx
      have hij : i < j := hidx.lt_iff_lt.mp hij_idx
      -- Now use hcol
      have key : c_pair (idx i) (idx j) hij_idx = col := hcol i j hij
      convert key using 2

  -- ----------------------------------------------------------------
  -- INITIAL STATE
  -- ----------------------------------------------------------------
  obtain ⟨a₀, _, col₀, S₀, hS₀inf, _, hS₀gt, hS₀col⟩ :=
    step 0 (Set.Ioi 0)
      (Set.infinite_of_injective_forall_mem Nat.succ_injective (fun n => Nat.succ_pos n))
      (fun x hx => hx)

  -- ----------------------------------------------------------------
  -- ITERATION
  -- ----------------------------------------------------------------
  let s₀ : TripleState κ c := ⟨a₀, col₀, S₀, hS₀inf, hS₀gt, hS₀col⟩
  have advance : ∀ s : TripleState κ c, ∃ s' : TripleState κ c,
      s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
    intro ⟨a, _col, S, hSinf, hSgt, _⟩
    obtain ⟨a', ha'S, col', S', hS'inf, hS'sub, hS'gt, hS'col⟩ :=
      step a S hSinf hSgt
    exact ⟨⟨a', col', S', hS'inf, hS'gt, hS'col⟩, ha'S, hS'sub⟩
  let states : ℕ → TripleState κ c :=
    fun n => n.rec s₀ (fun _ s => (advance s).choose)

  -- ----------------------------------------------------------------
  -- INVARIANTS (identical bookkeeping to the pairs proof)
  -- ----------------------------------------------------------------
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
  have verts_strictMono : StrictMono (fun n => (states n).vert) :=
    strictMono_nat_of_lt_succ I3
  -- Key triple invariant: c(stateₘ.vert, stateₙ.vert, stateₗ.vert) = stateₘ.col
  have I6 : ∀ m n l (hmn : m < n) (hnl : n < l),
      c (states m).vert (states n).vert (states l).vert
        ⟨verts_strictMono hmn, verts_strictMono hnl⟩ = (states m).col := by
    intro m n l hmn hnl
    exact (states m).hcol
      _ (I5 m n hmn) _ (I5 m l (hmn.trans hnl))
      (verts_strictMono hmn) (verts_strictMono hnl)

  -- ----------------------------------------------------------------
  -- PIGEONHOLE ON COLOURS
  -- ----------------------------------------------------------------
  obtain ⟨idx, hidx, k, hk⟩ := infinite_pigeonhole' (fun n => (states n).col)
  refine ⟨fun n => (states (idx n)).vert, verts_strictMono.comp hidx, k, ?_⟩
  intro h i j ⟨hhi, hij⟩
  have h1 := I6 (idx h) (idx i) (idx j) (hidx hhi) (hidx hij)
  have h2 := hk h
  convert h1.trans h2 using 2
