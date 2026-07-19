import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.LimitCase
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessor.LamOne

/-!
# §4.3 — Simple functions at a successor of a limit

This file scaffolds the §4.3 results of `4_centered_memo.tex`:

* `CBrank_succ_iff_index_nonempty` — Proposition 4.11 `Simpleiffcoincidenceofcocenters`,
  item 1.
* `simple_implies_cocenters_eq_distinguished` / `cocenters_coincide_implies_simple` —
  Proposition 4.11, the "in particular" simple characterisation, split into its two
  implications: `f` simple ⟹ the block cocenters on `I` coincide with `f`'s distinguished
  point; and conversely coincidence of those cocenters ⟹ `f` simple.
* `simpleFunctionsLambdaPlusOne` — **Theorem 4.12 `simplefunctionslambda+1damuddafuckaz`**:
  a simple function of CB-rank `λ+1` (`λ` limit or `1`) is continuously equivalent to one
  of the three generators `k_{λ+1}`, `k_{λ+1} ⊕ ℓ_λ`, or `pgl ℓ_λ`.

Status: Proposition 4.11 (`CBrank_succ_iff_index_nonempty`,
`simple_implies_cocenters_eq_distinguished`, `cocenters_coincide_implies_simple`) and the
`gl`-equivalence criterion (`equiv_gl_of_codomain_clopen_partition` and its two bounds
`reduces_F_gl_of_codomain` / `reduces_gl_F_of_codomain`) are fully proved.  The
prefix-cylinder strengthening of local centeredness
(`scatFun_centered_cylinder_witness`, together with its helpers
`cyl_restrict_witness_transfer`, `cbRank_cyl_restrict_eq`,
`simpleFun_restrict_open_of_rank_eq`, `simpleFun_restrict_open_subset_of_rank_eq`, and
`scatFun_centered_cylinder_caseB`) is now also fully proved.

The **non-zero-limit case is now complete**: the Case-B diagonal argument
(`simple_caseB_g_reduces_Gl`) and all of its supporting lemmas are fully proved, so for
`λ` a non-zero limit Theorem 4.12 holds unconditionally.  The diagonal is assembled from:
* `centered_lamPlusOne_rayOn_lt` — a centered, non-maximal block of rank `λ+1` has all rays
  `< λ` (via `rigidityOfCocenter_reducibleByPieces` to the `pgl` form of `minFun`), with
  helpers `cbRank_corestrict_W_lt`, `rayOn_cbRank_eq_rayFun`, `cocenter_eq_distinguished`,
  `cocenter_pgl_eq_zeroStream`, `pgl_rayOn_zeroStream_cbRank_lt`;
* `caseB_block_rayOn_lt` / `caseB_local_in_class` / `caseB_decomposition` — the
  restriction-closed `"all rays < λ"` class gives a countable clopen domain partition
  (`locally_implies_disjointUnion_nat`);
* `caseB_C1_reduces_minFun` (sub-diagonal `≤ k_{λ+1}`, via `cbRank_restrict_iUnion_finset_lt`
  and `restrict_restrict_realize_reduces`) and `caseB_C0_reduces_maxFun` (super-diagonal
  `≤ ℓ_λ`, since `C₀` avoids the `y`-fibre so its top CB-level is empty);
* assembled with `scatFun_reduces_gl_of_domain_partition` and `gl_reduces_of_pointwise`.

The `λ = 1` **base case is now also complete** (`simple_dichotomy_lam_one`), so Theorem 4.12
holds unconditionally for `λ` equal to `1` or any non-zero limit.  The limit-only ray-rank
dichotomy is invalid at `λ = 1` (a rank-`1` ray may be `≡ ℓ₁ ≡ id_ℕ` rather than `< 1`), so the
`λ = 1` diagonal mirrors the limit case with the restriction-closed block class "the ray has
*finite image*" replacing "rays of rank `< λ`".  It is assembled from:
* `centered_two_rayOn_finImage` — a centered, non-maximal block of rank `2` is `≡ k₂ = pgl (const k₁)`,
  whose rays (via `rigidityOfCocenter_reducibleByPieces`, `pgl_rayOn_zeroStream_finImage`,
  `corestrict_finUnion_raysets_finImage`, `reduces_finite_range`) have finite image;
* `lamOne_caseB_block_rayOn_finImage` / `lamOne_caseB_local_in_class` / `lamOne_caseB_decomposition`
  — the finite-image-ray class gives a countable clopen domain partition, using
  `lamOne_twoBQO_levelLT_two` (2-BQO at level `2` from finite generation, replacing
  `twoBQO_levelLT_succ`) and ruling out a rank-`1` centered cylinder being `≡ ℓ₁` via
  `not_isCentered_id`;
* the C₁ collapse `lamOne_caseB_C1_reduces_minFun` (`pgl` of finite-image rays `≤ k₂`, via
  `lamOne_finImage_mem_finGl_single` + `finitegenerationAndPgluing_upper` with `B = ![k₁]` and
  `pgl_const_minFun_zero_equiv_minFun_one`) and `caseB_C0_reduces_maxFun` (general in `lam`);
* the lower bound `lamOne_Gl_reduces_g` (codomain split with a ray `≡ ℓ₁`, from
  `lamOne_ray_infImage_equiv_maxFun`) and the diagonal upper bound `lamOne_g_reduces_Gl`.
Each docstring records the informal proof (`## Provided solution`) transcribed from the memoir.

The whole file is now complete.

## Notation dictionary (memoir ⇄ Lean)

**Two distinct operators** (do not conflate — the memoir keeps them apart):
* `⊕` = **finite gluing** (memoir `\gl` / `\glbin`, rendered `⊕`): `ScatFun.Gl` / `ScatFun.gl`.
  Tags the codomain with the block index.  This is the middle *generator* `k_{λ+1} ⊕ ℓ_λ`.
* `⊔` = **disjoint union** (memoir `\sqcup`): a single `F : ScatFun` together with a clopen
  partition of its *domain*; the blocks are the restrictions `F.restrict (Aᵢ)`, and `F`'s
  codomain is left untouched.  This is `f = ⊔ᵢ fᵢ` (`F.IsDisjointUnion A`).

| memoir | Lean |
|---|---|
| `k_{λ+1}`  (`Minimalfct{λ+1}`) | `ScatFun.minFun lam hlam_lt` |
| `ℓ_λ`      (`Maximalfct{λ}`)   | `ScatFun.maxFun lam hlam_lt` |
| `pgl ℓ_λ`  (`pgl Maximalfct{λ}`) | `ScatFun.succMaxFun lam hlam_lt` |
| `k_{λ+1} ⊕ ℓ_λ` (`k_{λ+1} \gl ℓ_λ`) | `ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt` (`ScatFun.glBin`) |
| `f = ⊔ᵢ fᵢ` (`\bigsqcup`) | `F.IsDisjointUnion A` (clopen partition `A : ℕ → Set ↑F.domain`); block `fᵢ = F.restrict (A i)` |
| `≤` is bqo on `𝒞_{<λ}` | `TwoBQO (ScatFun.LevelLT.reduces lam)` |
| cocenter `y_n` of `f_n` | `cocenter (F.restrict (A n)).func (hcent n)` |

(Corollary 4.13 `finitedegreedamuddafuckaz` — finite generation of the finite-degree
functions of `𝒞_{λ+1}` by `{ℓ_λ, k_{λ+1}, pgl ℓ_λ}` — is a downstream consequence via the
Decomposition Lemma; it is not scaffolded here.)
-/

open scoped Topology ScatFun
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section


/-- **Base case `lam = 1` of the dichotomy.**  A simple function `g` of CB-rank `2` that is
*not* equivalent to the maximum `pgl ℓ₁` is equivalent to `k₂` (and hence, since at `lam = 1`
the middle generator collapses `k₂ ⊕ ℓ₁ ≡ k₂`, also to `k₂ ⊕ ℓ₁`).

The limit-only ray-rank dichotomy used for non-zero limit `lam` is *invalid* at `lam = 1`:
there are non-maximal simple functions of CB-rank `2` with infinitely many rank-`1` rays
(so `simple_highRays_finite` is false at `lam = 1`).  This base case is therefore handled
separately.

## Provided solution

The key obstruction to reusing the limit argument: its Case-B step "a rank-`λ` ray is `≡ ℓ_λ`"
(`limit_rank_equiv_maxFun`, which needs `λ` limit) is **false** at `λ = 1` — a rank-`1` ray may
be `≡ k₁ = minFun 1` (a single isolated point) rather than `≡ ℓ₁ = maxFun 1`.  So the dichotomy
must split on whether a ray *attains* `ℓ₁`, not on its rank.

Setup (shared with the limit case).  `𝒞_{<1} = 𝒞_0` is trivially 2-BQO, so `g = ⊔ᵢ fᵢ` with each
`fᵢ` centered of rank `≤ 2` (Thm 4.7 `localCenterednessFromTwoBQO_scatFun` + Prop 2.14).  By
Corollary 4.10 (`centeredSuccessor`) every rank-`2` centered block is `≡ k₂` (it cannot be
`≡ pgl ℓ₁`, the maximum, by `hnotmax` together with `g ≤ pgl ℓ₁`).  All rays are taken at the
distinguished point `ȳ`, and `CB(ray g n) ≤ 1` for all `n` by simplicity.

Dichotomy on whether some ray of `g` at `ȳ` is `≡ ℓ₁`:

* **No ray `≡ ℓ₁`** (each ray is `≡ k₁` or empty).  Then `g ≡ k₂`: `k₂ ≤ g` always
  (`minFun_is_minimum`), and `g ≤ k₂` because `g` is the pointed gluing of its rays
  (`reduces_pgl_rays`) and a pointed gluing of functions `≤ k₁` is `≤ k₂`.  (First disjunct.)
* **Some ray `≡ ℓ₁`** on the clopen codomain piece `W = ray B N`.  Then `ℓ₁ ≤ g│_W` (the ray
  *is* `ℓ₁`, no limit step needed) and `k₂ ≤ g│_{Wᶜ}` (centeredness of `k₂`), so
  `k₂ ⊕ ℓ₁ ≤ g` via `equiv_gl_of_codomain_clopen_partition` (binary `B = ![¬W, W]`); the reverse
  `g ≤ k₂ ⊕ ℓ₁` is the `λ = 1` instance of the diagonal argument (the construction of
  `simple_caseB_g_reduces_Gl`, whose core does not use limitness).  Hence `g ≡ k₂ ⊕ ℓ₁`.
  (Second disjunct.)

Equivalently: `k₂ ≤ g` always, so `g ≡ k₂` exactly when `g ≤ k₂`, which fails precisely when some
ray reaches `ℓ₁`. -/
lemma simple_dichotomy_lam_one (hlam_lt : (1 : Ordinal.{0}) < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces (1 : Ordinal.{0})))
    (g : ScatFun) (hg_rank : CBRank g.func = 1 + 1) (hg_simple : SimpleFun g.func)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun 1 hlam_lt) g) :
    ScatFun.Equiv g (ScatFun.minFun 1 hlam_lt) ∨
      ScatFun.Equiv g
        (ScatFun.minFun 1 hlam_lt ⊕ ScatFun.maxFun 1 hlam_lt) := by
  obtain ⟨hne, hempty, y, hconst⟩ := simple_lam_data 1 g hg_rank hg_simple
  by_cases hA : ∀ n, (Set.range (g.rayOn y Set.univ n).func).Finite
  · exact Or.inl (lamOne_caseA_equiv_minFun g hg_rank hg_simple y hconst hA)
  · push_neg at hA
    obtain ⟨N, hN⟩ := hA
    have hrayN := lamOne_ray_infImage_equiv_maxFun g y hconst N hN
    exact Or.inr ⟨lamOne_g_reduces_Gl hbqo g hg_rank hg_simple y hconst hnotmax,
      lamOne_Gl_reduces_g g hg_rank hg_simple y hconst N hrayN⟩


/-- **Hard core of Theorem 4.12.**  A simple function `g` of CB-rank `lam+1` that is *not*
equivalent to the maximum `pgl ℓ_λ` (equivalently `pgl ℓ_λ ⋠ g`, since `g ≤ pgl ℓ_λ` always)
is equivalent to `k_{λ+1}` or to `k_{λ+1} ⊕ ℓ_λ`.  This is the ray-based `Case A`/`Case B`
argument of the memoir. -/
lemma simple_below_max_dichotomy (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlam_cases : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1) (hg_simple : SimpleFun g.func)
    (hnotmax : ¬ ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g) :
    ScatFun.Equiv g (ScatFun.minFun lam hlam_lt) ∨
      ScatFun.Equiv g
        (ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt) := by
  rcases hlam_cases with rfl | ⟨hlim, hlam_ne⟩
  · -- `lam = 1`: the limit-only ray dichotomy is invalid here (e.g. a function consisting of
    -- infinitely many rank-`1` rays can be non-maximal), so this base case is handled
    -- separately via the finite-generation classification of `𝒞_{≤2}`.
    exact simple_dichotomy_lam_one hlam_lt hbqo g hg_rank hg_simple hnotmax
  · -- `lam` a non-zero limit: the ray-rank dichotomy is valid.
    obtain ⟨hne, hempty, y, hconst⟩ := simple_lam_data lam g hg_rank hg_simple
    have hray_le : ∀ n, CBRank (g.rayOn y Set.univ n).func ≤ lam := by
      intro n
      have h := ScatFun.rayOn_cbRank_lt g lam y hconst Set.univ isOpen_univ n
      exact Order.lt_succ_iff.mp h
    by_cases hA : ∀ n, CBRank (g.rayOn y Set.univ n).func < lam
    · exact Or.inl
        (simple_caseA_equiv_minFun lam hlam_lt (Or.inr ⟨hlim, hlam_ne⟩) g hg_rank hg_simple y
          hconst hA)
    · push_neg at hA
      obtain ⟨N, hN⟩ := hA
      exact Or.inr (simple_caseB_equiv_Gl lam hlam_lt hlim hlam_ne hbqo g hg_rank hg_simple y
        hconst hray_le ⟨N, hN⟩ hnotmax)


/-- **Theorem 4.12 (`simplefunctionslambda+1damuddafuckaz`).**
Let `λ` be `1` or a non-zero limit ordinal, and assume continuous reducibility is 2-BQO on
`𝒞_{<λ}`.  Then every simple function `g ∈ 𝒞_{λ+1}` is continuously equivalent to one of the
three generators `k_{λ+1}`, `k_{λ+1} ⊕ ℓ_λ`, or `pgl ℓ_λ`.

## Provided solution

Since `≤` is bqo on `𝒞_{<λ}`, by the General Structure Theorem
(`general_structure_theorem`) it is bqo on `𝒞_{≤λ}`, so by Theorem 4.7
(`localCenterednessFromTwoBQO_scatFun`) and Prop 2.14 we may write
`g = ⊔_{i ∈ I} f_i` with each `f_i` centered.

* As `g` is simple, `g ≤ pgl ℓ_λ` by `maxFun_is_maximum` (`Maxfunctions`).  Hence if some
  `f_i ≡ pgl ℓ_λ`, then `g ≡ pgl ℓ_λ` and we are in the third case.
* By Corollary 4.10 (`centeredSuccessor`), `pgl ℓ_λ` and `k_{λ+1}` are the only two centered
  functions in `𝒞_{λ+1}`.  So we may assume that for all `n ∈ I` with `CB(f_n) > λ` we have
  `f_n ≡ k_{λ+1}`.

By Proposition 4.11 (`simpleIffCoincidenceOfCocenters`), some `f_i ≡ k_{λ+1}`, and the
distinguished point `ȳ` of `g` is the cocenter of every such `f_i`.  All rays below are taken
at `ȳ`.  By simplicity `CB_λ(g) ⊆ g⁻¹({ȳ})`, so `CB(ray g n) ≤ λ` for all `n`.  Also
`CB(ray f_i j) < λ` for all `i, j` (using `rigidityOfCocenter` when `f_i ≡ k_{λ+1}`).

**Case A — `CB(ray g n) < λ` for all `n`.**  Then `g ≤ pgl_n (ray g n)` by
`Pgluingofraysasupperbound` (Lean: `ScatFun.reduces_pgl_rays`), and
`pgl_n (ray g n) ≤ k_{λ+1}` by `ConsequencesGeneralStructureThm` item 1 (Lean:
`consequencesGeneralStructure_pgl_le_minFun`, the rays lying in `𝒞_{<λ}`).  With
`k_{λ+1} ≤ g` from `minFun_is_minimum`, this gives `g ≡ k_{λ+1}` (first case).

**Case B — `CB(ray g n) = λ` for some `n`.**  Fix `W = ray B n`; then `ȳ ∉ W`,
`ℓ_λ ≤ g│_W` by `general_structure_theorem`, and `k_{λ+1} ≤ g│_{B∖W}` by centeredness of
`k_{λ+1}`.  Since `W` is clopen, `g│_{B∖W} ⊕ g│_W ≡ g` by `UsefulcriterionforequivFinGl`
(Lean: `equiv_gl_of_codomain_clopen_partition`, binary case `B = ![¬W, W]`), so
`k_{λ+1} ⊕ ℓ_λ ≤ g`.

  For the reverse `g ≤ k_{λ+1} ⊕ ℓ_λ`, split `g` "along the diagonal".  For `j ∈ ℕ` set
  `g_j = ⊔_{i ≤ j} ray f_i j` and `h_j = ⊔_{i > j} ray f_i j`, with clopen blocks
  `C^j_i = dom(ray f_i j) = A_i ∩ g⁻¹(ray B j)`.  Let `C₀ = ⋃ {C^j_i | i > j}` and
  `C₁ = A ∖ C₀`.  Since `CB(ray f_i j) < λ` for all `i, j`, we have `CB(h_j) ≤ λ`, so
  `g│_{C₀} ≤ ℓ_λ` by `Maxfunctions`.  Each `g_j = ⊔_{i ≤ j} ray f_i j` has `CB(g_j) < λ`,
  and the `g_j` are the rays of `g│_{C₁}` at `ȳ`, so by `ScatFun.reduces_pgl_rays` and
  `consequencesGeneralStructure_pgl_le_minFun`, `g│_{C₁} ≤ pgl_j g_j ≤ k_{λ+1}`.

  Finally `C₀` is open (union of clopens), and `C₁ = ⋃_i (A_i ∖ C₀)` with
  `A_i ∖ C₀ = ⋃_{j ≤ i} C^j_i` clopen, so `C₁` is open too: `A = C₀ ⊔ C₁` is a clopen
  partition with `g│_{C₀} ≤ ℓ_λ` and `g│_{C₁} ≤ k_{λ+1}`, whence `g ≤ k_{λ+1} ⊕ ℓ_λ` by
  `Gluingasupperbound` (`clopen_partition_to_gluing_reduces`).  Combined with
  `k_{λ+1} ⊕ ℓ_λ ≤ g`, this gives `g ≡ k_{λ+1} ⊕ ℓ_λ` (second case). -/
theorem simpleFunctionsLambdaPlusOne (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlam_cases : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces lam))
    (g : ScatFun) (hg_rank : CBRank g.func = lam + 1)
    (hg_simple : SimpleFun g.func) :
    ScatFun.Equiv g (ScatFun.minFun lam hlam_lt) ∨
      ScatFun.Equiv g
        (ScatFun.minFun lam hlam_lt ⊕ ScatFun.maxFun lam hlam_lt) ∨
      ScatFun.Equiv g (ScatFun.succMaxFun lam hlam_lt) := by
  by_cases hcent : IsCentered g.func
  · -- **Centered case (Corollary 4.10).**  A centered simple function of rank `λ+1`
    -- is equivalent to `k_{λ+1}` or to `pgl ℓ_λ`.
    rcases centeredSuccessor lam hlam_lt hlam_cases g hg_rank hcent with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · -- **Non-centered case.**  Split on whether `g` attains the maximum `pgl ℓ_λ`.
    by_cases h3 : ScatFun.Reduces (ScatFun.succMaxFun lam hlam_lt) g
    · -- `pgl ℓ_λ ≤ g`; with `g ≤ pgl ℓ_λ` this gives `g ≡ pgl ℓ_λ` (third case).
      exact Or.inr (Or.inr ⟨simple_reduces_succMaxFun lam hlam_lt g hg_rank hg_simple, h3⟩)
    · -- `pgl ℓ_λ ⋠ g`: the ray-based dichotomy gives `g ≡ k_{λ+1}` or `g ≡ k_{λ+1} ⊕ ℓ_λ`.
      exact (simple_below_max_dichotomy lam hlam_lt hlam_cases hbqo g hg_rank hg_simple h3).imp
        id Or.inl

end
