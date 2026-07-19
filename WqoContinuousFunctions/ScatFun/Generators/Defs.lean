import WqoContinuousFunctions.ScatFun.Operations
import WqoContinuousFunctions.ScatFun.Wedge.Defs
import WqoContinuousFunctions.ScatFun.IntertwineReductions
import WqoContinuousFunctions.ScatFun.FiniteGluing

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# The centered functions `𝒞_α` and generators `𝒢_α` (memoir §5, Def. `subsectionGenerators`)

For every `α < ω₁` the memoir defines by induction a finite set of *centered functions*
`𝒞_α` and a finite set of *generators* `𝒢_α`, and states as the goal of the chapter
(`PreciseStructureThm`) that every function of `ScatFun`-level `α` is a finite gluing of
elements of `𝒢_α`.  `ScatFun.levels_finitely_generated` (`ScatFun/LevelsFinitelyGenerated.lean`)
is exactly that statement, stated there with the *explicit* witness `Generators α` defined in
this file (and the auxiliary `Centered α`), instead of an existential family.

## Design

We represent `𝒞_α`/`𝒢_α` as `Finset ScatFun` (not as a literal growing `Fin n → ScatFun`
family): finiteness is then free (`Finset.finite_toSet`), monotonicity in `α` is a set
inclusion, and we only convert to `Fin n → ScatFun` at the point of use
(`ScatFun.levels_finitely_generated`), via `Finset.toFinFun` below.

**No transfinite recursion is needed.**  Reading the memoir definition closely: `𝒞_λ = ∅` for
*every* limit-or-zero `λ`, and `𝒢_λ` is `∅` (if `λ = 0`) or `{ℓ_λ}` (if `λ` limit) — both are
*closed forms*, with no reference to `𝒞`/`𝒢` at smaller ordinals.  The only genuine recursion
is the **`ℕ`-indexed block recursion** within a fixed block `λ, λ+1, λ+2, …`, which is exactly
`Ordinal.limitPart`/`Ordinal.natPart` (`BQO/OrdinalBQO.lean`) applied to `α`.  So:

* `CentBlock λ`, `GenBlock λ : ℕ → Finset ScatFun` are defined by plain `Nat.rec`
  (`CentBlock λ n = 𝒞_{λ+n+1}`, `GenBlock λ n = 𝒢_{λ+n}`, reindexed — see below).
* `Centered α`, `Generators α` read off `α.limitPart`/`α.natPart` in closed form.

## Reindexing of `CentBlock`/`GenBlock`

The memoir's "for `n > 0`" step computes `𝒞_{λ+n+1}` from `𝒞_{λ+n}`, and `𝒢_{λ+n}` from
`𝒞_{λ+n}` and `𝒢_{λ+n-1}` — both valid for every `n ≥ 1`, i.e. genuinely a recursion in
`n` starting from the *given* base value `𝒞_{λ+1}` (not from `𝒞_λ = ∅`, since plugging
`𝒞_λ = ∅` into the "`n > 0`" formula for `𝒞_{λ+1}` would (wrongly) give `∅` again — the base
case `𝒞_{λ+1}` is genuinely separate data).  So we set, for `n : ℕ`:

* `CentBlock λ n := 𝒞_{λ+n+1}`, seeded at `n = 0` by the base value `𝒞_{λ+1}` and stepped by
  the "`n > 0`" formula for all `n ≥ 0` (`CentBlock λ (n+1) = centStep (CentBlock λ n)`
  corresponds to `𝒞_{λ+n+2}` from `𝒞_{λ+n+1}`, i.e. the memoir's step at index `n+1 > 0`).
* `GenBlock λ n := 𝒢_{λ+n}`, seeded at `n = 0` by the base value `𝒢_λ` and stepped by
  `GenBlock λ (n+1) = genStep (CentBlock λ n) (GenBlock λ n)`, i.e. `𝒢_{λ+n+1}` from
  `𝒞_{λ+n+1} = CentBlock λ n` and `𝒢_{λ+n} = GenBlock λ n` (the memoir's step at index
  `n+1 > 0`).

Then, for `α < ω₁` with `λ := α.limitPart`, `n := α.natPart` (so `α = λ + n`):

* `Centered α = ∅` if `n = 0` (this is `𝒞_λ`), else `CentBlock λ (n - 1)` (this is
  `𝒞_{λ+n} = 𝒞_{λ+(n-1)+1}`).
* `Generators α = GenBlock λ n` (this is `𝒢_{λ+n}` directly, for every `n`, including `n = 0`).
-/

namespace ScatFun

/-! ## A `Finset`-to-`Fin` conversion, for feeding `pgl`/`wedge`/`FinGl`. -/

/-- Read a `Finset` off as a family indexed by `Fin S.card`, via `S.toList`.  Used to feed
finite sets of `ScatFun`s into the `Fin n →`-indexed operations `pgl`, `wedge`, `Gl`. -/
def _root_.Finset.toFinFun {α : Type*} (S : Finset α) : Fin S.card → α :=
  fun i => S.toList.get (i.cast S.length_toList.symm)

/-! ## Basic set-of-functions notation from the memoir preamble (`5_precise_struct_memo.tex:428-430`) -/

/-- `𝒫⁺(F)`: the nonempty subsets of a finite set `F`.  Stated generically (not just for
`Finset ScatFun`) so it can also be applied to `F : Finset (Finset ScatFun)`, as needed for the
"nonempty finite sets of nonempty subsets" ranging over wedge generators in `genStep`. -/
def nonemptySubsets {α : Type*} [DecidableEq α] (F : Finset α) : Finset (Finset α) :=
  F.powerset.erase ∅

/-- `𝒫⁺` is monotone. -/
lemma nonemptySubsets_mono {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    nonemptySubsets s ⊆ nonemptySubsets t :=
  Finset.erase_subset_erase _ (Finset.powerset_mono.mpr h)

/-- `ω{F} = {ω f : f ∈ F}`. -/
def omegaImage (F : Finset ScatFun) : Finset ScatFun :=
  F.image omega

/-- `pgl F` for a *finite set* `F`: the pointed gluing of countably many copies of
`glList F.toList` (one block enumerating all of `F`, repeated).  Agrees up to continuous
equivalence with the memoir's `\pgl F` for any enumeration of `F`. -/
def pglFinset (F : Finset ScatFun) : ScatFun :=
  pgl (fun _ => glList F.toList)

/-- `⋀(F_0,…,F_k ∣ F_{k+1})` for `S = [F_0,…,F_k]` a list of vertical sets (already spelled
out as `List ScatFun`) and `D = F_{k+1}` the diagonal set, per `5_precise_struct_memo.tex:430`.
Distinctness of the `F_i` (memoir's "distinct `F_0,…,F_k`") is *not* enforced by the type — it
is a side condition on `S` supplied by the caller (`genStep` supplies `S` as the image of an
injective enumeration of a `Finset (Finset ScatFun)`, which is automatically duplicate-free). -/
def wedgeFinset (S : List (List ScatFun)) (D : List ScatFun) : ScatFun :=
  wedgeList (fun i : Fin S.length => S.get i) D

/-! ## The block step formulas (memoir "For `n > 0`", `5_precise_struct_memo.tex:441-451`) -/

/-- The `𝒞`-step: `𝒞_{λ+n+1} = 𝒞_{λ+n} ∪ \pgl 𝒫⁺(𝒞_{λ+n} ∪ ω{𝒞_{λ+n}})`. -/
def centStep (C : Finset ScatFun) : Finset ScatFun :=
  C ∪ (nonemptySubsets (C ∪ omegaImage C)).image pglFinset

/-- `centStep` only adds elements: `C ⊆ centStep C`. -/
lemma centStep_supset (C : Finset ScatFun) : C ⊆ centStep C :=
  Finset.subset_union_left

/-- The `𝒢`-step: `𝒢_{λ+n} = 𝒞_{λ+n} ∪ ω{𝒞_{λ+n}} ∪ {wedge generators}`, where the wedge
generators range over nonempty finite sets `S ⊆ 𝒫⁺(𝒢_{λ+n-1})` of *distinct* nonempty vertical
sets and finite diagonal sets `D ⊆ 𝒞_{λ+n}`. -/
def genStep (Cn Gprev : Finset ScatFun) : Finset ScatFun :=
  Cn ∪ omegaImage Cn ∪
    ((nonemptySubsets (nonemptySubsets Gprev)).biUnion
      (fun S => Cn.powerset.image
        (fun D => wedgeFinset (S.toList.map Finset.toList) D.toList)))

/-! ## The `ℕ`-indexed block recursion at a fixed limit-or-zero `λ` -/

/-- `CentBlock λ C1 n = 𝒞_{λ+n+1}`, seeded by the base value `C1 = 𝒞_{λ+1}`. -/
def CentBlock (C1 : Finset ScatFun) : ℕ → Finset ScatFun
  | 0 => C1
  | n + 1 => centStep (CentBlock C1 n)

/-- **Monotonicity of `𝒞`** (memoir `BasicsOnGenerators` item 1, `𝒞` half):
`𝒞_{λ+n} ⊆ 𝒞_{λ+n+1}` for every `n`. -/
lemma CentBlock_subset_succ (C1 : Finset ScatFun) (n : ℕ) :
    CentBlock C1 n ⊆ CentBlock C1 (n + 1) :=
  centStep_supset _

/-- `GenBlock G0 C1 n = 𝒢_{λ+n}`, seeded by the base value `G0 = 𝒢_λ`; uses `CentBlock C1`
for the `𝒞_{λ+n}` argument of `genStep`.

Mirroring `CentBlock`/`centStep`, each step **re-unions the previous level in verbatim**
(`GenBlock G0 C1 n ∪ genStep …`), rather than replacing it: the memoir's `genStep` formula
alone does not literally reproduce every earlier element (e.g. at a limit `λ`, `ℓ_λ ∈ 𝒢_λ` is
not literally reproduced by any `wedge`-term of `genStep`, only dominated by one), so without
this explicit re-union `𝒢_{λ+n} ⊆ 𝒢_{λ+n+1}` would fail as literal `Finset` inclusion. This is
a harmless enlargement (it does not change `FinGl`-closure — everything carried forward this
way is already dominated by something `genStep` produces) and it trivializes monotonicity,
exactly as `centStep_supset` does for `CentBlock`. -/
def GenBlock (G0 C1 : Finset ScatFun) : ℕ → Finset ScatFun
  | 0 => G0
  | n + 1 => GenBlock G0 C1 n ∪ genStep (CentBlock C1 n) (GenBlock G0 C1 n)

/-- **Monotonicity of `𝒢`** (memoir `BasicsOnGenerators` item 1, `𝒢` half):
`𝒢_{λ+n} ⊆ 𝒢_{λ+n+1}` for every `n`. -/
lemma GenBlock_subset_succ (G0 C1 : Finset ScatFun) (n : ℕ) :
    GenBlock G0 C1 n ⊆ GenBlock G0 C1 (n + 1) :=
  Finset.subset_union_left

/-! ## The base data at a limit-or-zero `λ` (memoir base/limit cases, `5_precise_struct_memo.tex:436-439`) -/

/-- `𝒢_λ`: `∅` if `λ = 0`, `{ℓ_λ}` if `λ` is a limit ordinal.  (Junk `∅` if `λ ≥ ω₁`, which
never arises when `λ = α.limitPart` for `α < ω₁`.) -/
def genBase (lam : Ordinal.{0}) : Finset ScatFun :=
  if lam = 0 then ∅
  else if h : lam < omega1 then {maxFun lam h} else ∅

/-- `𝒞_{λ+1}`: `{k_1}` if `λ = 0`; `{k_{λ+1}, \pgl ℓ_λ}` if `λ` is a limit ordinal.  (Junk
`∅` if `λ ≥ ω₁`.) -/
def centBase1 (lam : Ordinal.{0}) : Finset ScatFun :=
  if lam = 0 then
    (if h : (0 : Ordinal.{0}) < omega1 then {minFun 0 h} else ∅)
  else if h : lam < omega1 then {minFun lam h, succMaxFun lam h} else ∅

/-! ## The definitions proper -/

/-- `𝒞_α`, the memoir's `\centered{α}`. -/
def Centered (α : Ordinal.{0}) : Finset ScatFun :=
  if α.natPart = 0 then ∅
  else CentBlock (centBase1 α.limitPart) (α.natPart - 1)

/-- `𝒢_α`, the memoir's `\generator{α}`. -/
def Generators (α : Ordinal.{0}) : Finset ScatFun :=
  GenBlock (genBase α.limitPart) (centBase1 α.limitPart) α.natPart

/-! ## Sanity checks (memoir `AlreadyKnownGenerators`, `5_precise_struct_memo.tex:456-465`) -/

@[simp] lemma limitPart_zero : (0 : Ordinal.{0}).limitPart = 0 := by
  have h0 : (0 : Ordinal.{0}) = (0 : Ordinal.{0}) + (0 : ℕ) := by simp
  conv_lhs => rw [h0]
  exact Ordinal.limitPart_add_natCast 0 0 (Or.inr rfl)

@[simp] lemma natPart_zero : (0 : Ordinal.{0}).natPart = 0 := by
  have h0 : (0 : Ordinal.{0}) = (0 : Ordinal.{0}) + (0 : ℕ) := by simp
  conv_lhs => rw [h0]
  exact Ordinal.natPart_add_natCast 0 0 (Or.inr rfl)

/-- `𝒢_0 = ∅` (the empty function is the sole element of CB-rank `0`, generated by no
generators — memoir remark after Def. `subsectionGenerators`). -/
lemma Generators_zero : Generators 0 = ∅ := by
  simp [Generators, GenBlock, genBase]

@[simp] lemma limitPart_omega0 : Ordinal.omega0.limitPart = Ordinal.omega0 := by
  have h0 : Ordinal.omega0 = Ordinal.omega0 + (0 : ℕ) := by simp
  conv_lhs => rw [h0]
  exact Ordinal.limitPart_add_natCast Ordinal.omega0 0 (Or.inl Ordinal.isSuccLimit_omega0)

@[simp] lemma natPart_omega0 : Ordinal.omega0.natPart = 0 := by
  have h0 : Ordinal.omega0 = Ordinal.omega0 + (0 : ℕ) := by simp
  conv_lhs => rw [h0]
  exact Ordinal.natPart_add_natCast Ordinal.omega0 0 (Or.inl Ordinal.isSuccLimit_omega0)

/-- `𝒢_ω = {ℓ_ω}` (the limit case: `ω` is a limit ordinal, so `𝒢_ω` is the singleton
maximum function `ℓ_ω`, per the memoir's `Limit case λ`). -/
lemma Generators_omega0 (h : Ordinal.omega0 < omega1) :
    Generators Ordinal.omega0 = {maxFun Ordinal.omega0 h} := by
  simp only [Generators, GenBlock, genBase, limitPart_omega0, natPart_omega0]
  rw [if_neg Ordinal.omega0_ne_zero, dif_pos h]

/-- `𝒞_0 = ∅` (base case). -/
lemma Centered_zero : Centered 0 = ∅ := by
  simp [Centered]

@[simp] lemma limitPart_one : (1 : Ordinal.{0}).limitPart = 0 := by
  have h1 : (1 : Ordinal.{0}) = (0 : Ordinal.{0}) + ((1 : ℕ) : Ordinal.{0}) := by simp
  conv_lhs => rw [h1]
  exact Ordinal.limitPart_add_natCast 0 1 (Or.inr rfl)

@[simp] lemma natPart_one : (1 : Ordinal.{0}).natPart = 1 := by
  have h1 : (1 : Ordinal.{0}) = (0 : Ordinal.{0}) + ((1 : ℕ) : Ordinal.{0}) := by simp
  conv_lhs => rw [h1]
  exact Ordinal.natPart_add_natCast 0 1 (Or.inr rfl)

/-- `𝒞_1 = {k_1}` (base case: `λ = 0`, so `𝒞_{λ+1} = 𝒞_1` is the base value `centBase1 0`). -/
lemma Centered_one (h : (0 : Ordinal.{0}) < omega1) :
    Centered 1 = {minFun 0 h} := by
  simp only [Centered, natPart_one, limitPart_one]
  norm_num
  rw [CentBlock, centBase1, if_pos rfl, dif_pos h]

/-- `𝒞_ω = ∅` (limit case: `𝒞_λ = ∅` for every limit-or-zero `λ`, in particular `λ = ω`). -/
lemma Centered_omega0 : Centered Ordinal.omega0 = ∅ := by
  simp [Centered, natPart_omega0]

/-! ## Further basic structural facts about `Centered`/`Generators`

Moved here from `Generators/Basics.lean`: these are `Centered`/`Generators`-level structural
facts with no dependence on the finite-generation machinery that file otherwise needs, so they
belong alongside the definitions rather than forcing every consumer through the heavier import. -/

/-- Iterated `centStep` monotonicity: `𝒞`-blocks grow with the index. -/
lemma CentBlock_mono (C1 : Finset ScatFun) {m n : ℕ} (h : m ≤ n) :
    CentBlock C1 m ⊆ CentBlock C1 n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (CentBlock_subset_succ C1 _)

/-- `𝒞_{λ+n+1} = CentBlock (centBase1 λ) n` for `λ` limit-or-zero. -/
lemma Centered_lam_add_succ {lam : Ordinal.{0}} (hlim : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ) :
    Centered (lam + ↑n + 1) = CentBlock (centBase1 lam) n := by
  have hcast : (lam + ↑n + 1 : Ordinal) = lam + ↑(n + 1) := by push_cast; rw [add_assoc]
  rw [hcast, Centered, Ordinal.natPart_add_natCast lam (n + 1) hlim,
    Ordinal.limitPart_add_natCast lam (n + 1) hlim]
  simp

/-- `k_{λ+1} = minFun λ ∈ 𝒞_{λ+n+1}` for every `n`. -/
lemma minFun_mem_Centered {lam : Ordinal.{0}} (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam ∨ lam = 0) (n : ℕ) :
    minFun lam hlam ∈ Centered (lam + ↑n + 1) := by
  rw [Centered_lam_add_succ hlim]
  refine CentBlock_mono (centBase1 lam) (Nat.zero_le n) ?_
  show minFun lam hlam ∈ centBase1 lam
  rw [centBase1]
  rcases hlim with hl | hl
  · have hne : lam ≠ 0 := by simpa using hl.ne_bot
    rw [if_neg hne, dif_pos hlam]
    exact Finset.mem_insert_self _ _
  · subst hl
    rw [if_pos rfl, dif_pos hlam]
    exact Finset.mem_singleton_self _

/-- `\pgl ℓ_λ = succMaxFun λ ∈ 𝒞_{λ+n+1}` for `λ` limit and every `n`. -/
lemma succMaxFun_mem_Centered {lam : Ordinal.{0}} (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (n : ℕ) :
    succMaxFun lam hlam ∈ Centered (lam + ↑n + 1) := by
  rw [Centered_lam_add_succ (Or.inl hlim)]
  refine CentBlock_mono (centBase1 lam) (Nat.zero_le n) ?_
  show succMaxFun lam hlam ∈ centBase1 lam
  have hne : lam ≠ 0 := by simpa using hlim.ne_bot
  rw [centBase1, if_neg hne, dif_pos hlam]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-
Every member of the finite set `Centered α` is a centered function.
-/
lemma isCentered_of_mem_Centered (α : Ordinal.{0}) (x : ScatFun) (hx : x ∈ Centered α) :
    IsCentered x.func := by
  have h_ind : ∀ m, ∀ x ∈ ScatFun.CentBlock (ScatFun.centBase1 α.limitPart) m, IsCentered x.func := by
    intro m x hx; induction' m with m ih generalizing x <;> simp_all +decide [ ScatFun.CentBlock ] ;
    · unfold ScatFun.centBase1 at hx; split_ifs at hx <;> simp_all +decide [ Finset.mem_singleton ] ;
      · exact hx.symm ▸ minFun_isCentered 0 ‹_›;
      · rcases hx with ( rfl | rfl ) <;> [ exact minFun_isCentered _ _; exact pgl_isCentered_of_regular _ ( scatFun_const_isRegularSeq _ ) ];
        grind +suggestions;
    · unfold centStep at hx; simp_all +decide [ nonemptySubsets ] ;
      rcases hx with ( hx | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ pglFinset ];
      apply pgl_isCentered_of_regular;
      exact scatFun_const_isRegularSeq _;
  unfold Centered at hx; aesop;

/-
At a limit base `lam`, `Generators lam = {ℓ_lam}`.
-/
lemma Generators_lam_limit {lam : Ordinal.{0}} (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) : Generators lam = {maxFun lam hlam} := by
  unfold Generators;
  have h_n : lam.natPart = 0 := by
    convert Ordinal.natPart_add_natCast lam 0 ( Or.inl hlim ) using 1;
    norm_num
  have h_l : lam.limitPart = lam := by
    convert Ordinal.limitPart_add_natCast lam 0 ( Or.inl hlim ) using 1;
    norm_num
  rw [h_n, h_l];
  unfold genBase centBase1; aesop;

/-
`𝒞`-blocks are monotone across one natural successor of the base level.
-/
lemma Centered_add_nat_subset_succ {lam : Ordinal.{0}}
    (hlim : Order.IsSuccLimit lam ∨ lam = 0) (j : ℕ) :
    Centered (lam + ↑j) ⊆ Centered (lam + ↑j + 1) := by
  -- We'll prove this by induction on `j`.
  induction' j with j ih;
  · unfold Centered;
    grind +suggestions;
  · convert ScatFun.CentBlock_subset_succ _ _ using 1;
    convert ScatFun.Centered_lam_add_succ hlim j using 1;
    · norm_num [ add_assoc ];
    · convert ScatFun.Centered_lam_add_succ hlim ( j + 1 ) using 1

end ScatFun

end
