import WqoContinuousFunctions.CenteredFunctions.LocallyCentered.Helpers
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Section 2 & 3: Centered functions and structure of continuous reducibility (§4.2–4.3)

This file contains the main theorems of Chapter 4 that depend on the successor-case
machinery in `SuccessorCase/Helpers.lean`.

## Main results

### §4.2
* `localCenterednessFromTwoBQO_scatFun` — Theorem 4.7

(Theorem 4.9 `finitenessOfCenteredFunctions` now lives in `CenteredFunctions/Finiteness.lean`;
Theorem 4.6 `centeredAsPgluing_*` in `CenteredFunctions/CenteredAsPgluing.lean`.)

(Proposition 4.8 `finitegenerationAndPgluing_upper` / `_lower` now lives in
`ScatFun/FiniteGluing.lean`, stated with the `FinGl` / `pgl` operations.)

(§4.3 — Proposition 4.11 `simpleIffCoincidenceOfCocenters`, Theorem 4.12
`simpleFunctionsLambdaPlusOne`, Corollary 4.13 `finiteDegreeLambdaPlusOne` — is not
yet formalized; only the Proposition 4.11 helper scaffolding lives in
`CenteredFunctions/Helpers.lean`.)
-/

noncomputable section

-- **Theorem 4.6 (CenteredAsPgluing)** (forward/backward/equiv/monotone/iff) →
-- `CenteredFunctions/CenteredAsPgluing.lean`.
-- **Theorem 4.9 (`finitenessOfCenteredFunctions`)** → `CenteredFunctions/Finiteness.lean`.
/-!
## Section 2: Centered Functions and Structure of Continuous Reducibility (§4.2)
-/

/- Main result is `localCenterednessFromTwoBQO_scatFun` which states that if continuous reducibility on ScatFun is 2-bqo below an ordinal α, then functions in level α of ScatFun are locally centered.
The crux of the proof by induction is the Successor case: if f has successor CB-rank α+1 and 𝒞_{<α+1} (`ScatFun.levelLT α`) is 2-BQO,
then f is locally centered.

PROVIDED SOLUTION

Let `f` be in `ScatFun` with rank `α + 1`. By `decomposition_lemma_baire`, `f` is locally
simple, so without loss of generality we can suppose that `f` is simple.

We let `ȳ` be the distinguished point of `f`, so that for all `x ∈ CBLevel f α` we have
`f x = ȳ`. Write `R i` for the ray of the whole Baire space at `ȳ` and `fR i` for the ray
of `f` at `ȳ`. Note that we have `CB(fR i) < α` for all `i ∈ ℕ` by `sup_ray_cb_eq_alpha`.
Let `x ∈ A`; we show that it admits a neighbourhood `U` such that `f|_U` is centered.

If there exists `s ⊑ x` such that `CB(f|_{N_s}) < CB(f)` then, by induction hypothesis, we
are done.

Otherwise, assume that for all `s ⊑ x` we have `CB(f|_{N_s}) = CB(f)`. Hence, we have
`N_s ∩ CB_α(f) ≠ ∅` for all `s ⊑ x`. This means that for every `x|n` there exists
`y_n ∈ N_{x|n} ∩ CB_α(f)`. Since `y_n → x` and `CB_α(f)` is closed, `x ∈ CB_α(f)`. Hence,
we have `f x = ȳ` (and each function `f|_{N_s}` is simple).

Define `dom: ℕ → ℕ→ Set(ℕ→ℕ)`by `dom i n = (Nbhd x n) ∩ {a : f.dom | (∀ k, k < n → f a k = y k) ∧ f a n ≠ y n}` (in symbols `N_{x|n}∩ f^{-1}(RaySet univ y i)`)
We define the sequence `ξ : ℕ → (ℕ → ScatFun.LevelLT α)` by `\xi i n = (fun z: dom i n => f z`.

For each `n`, the sequence of rays `i ↦ ξ i n` takes values in
`ScatFun.LevelLT α`. Since `ScatFun.LevelLT α` is `TwoBQO` (hence WQO by
`TwoBQO.wellQuasiOrdered`) by assumption, infinite sequences in `ScatFun.LevelLT α` are WQO
under `EmbedForAll` by `TwoBQO.embedForAll_wqo`. We can choose by induction a non-decreasing
sequence `(j_n)_n` in `ℕ` such that the sequence of functions
`ρ_n = ξ i (n+j_n)` is regular for all `n` by `WQO.eventuallyRegular`.
Note that `m < n` implies `ρ_m ≥_{(ScatFun.LevelLT α)^ℕ} ρ_n`, since `N_{x|m} ⊇ N_{x|n}` implies
`(fR i)|_{N_{x|m}} ≥ (fR i)|_{N_{x|n}}` for all `i ≥ j_n`, so `(ρ_n)_n` is decreasing in
`(ScatFun.LevelLT α)^ℕ`. Since `(ScatFun.LevelLT α)^ℕ` is WQO, there exists `m` such that for all `n > m` we have
`ρ_m ≡_{(ScatFun.LevelLT α)^ℕ} ρ_n`. Define `U = N_{x|m} \ f⁻¹(⋃_{i < j_m} R i)`; we show that
`f|_U ≡ pgl ρ_m`. Since `ρ_m` is regular, `pgl ρ_m` is centered by
`centeredAsPgluing_iff_monotone` and so will be `f|_U` by `centerInvariance_equiv`.

The fact that `f|_U ≤ pgl ρ_m` follows from `pointedGluing_rays_upper_bound`. To show that
`pgl ρ_m ≤ f|_U` using `pointedGluing_lower_bound`, it is enough to show that for every
`i ≥ j_m` and every `n > m`, there exists `(σ, τ)` that continuously reduces
`(fR i)|_{N_{x|m}}` to `f|_U` such that `im σ ⊆ N_{x|n}` and `ȳ ∉ closure (im (f|_U ∘ σ))`.
This is possible since `ρ_m ≤ ρ_n` and so for every `i ≥ j_m` there exists `i' ≥ j_n ≥ j_m`
with `(fR i)|_{N_{x|m}} ≤ (fR i')|_{N_{x|n}}`, as desired.
 -/

/--
**Theorem 4.8 (LocalCenterednessFromBQO).**
For all `α < ω₁`, if `𝒞_{<α}` is BQO, then every function in `𝒞_α` is locally
centered.

Here we use the intermediate property 2-BQO instead, which is sufficient to propagate the induction step, and is simpler than the full BQO property.
*Proof by strong induction on `α`:*
- *`α = 0`:* The empty function is trivially locally centered.
- *`α` limit:* `f` has limit CB-rank, so is locally in `𝒞_{<α}`, hence locally centered
  by induction.
- *`α` successor:* Apply `locallyCentered_succ_rank_scatFun`. -/
theorem localCenterednessFromTwoBQO_scatFun
    (α : Ordinal.{0}) (hα : α < omega1)
    (hbqo : TwoBQO (ScatFun.LevelLT.reduces α)) :
    ∀ (F : ScatFun), CBRank F.func = α → IsLocallyCentered F.func := by
  induction α using Ordinal.induction with
  | _ α ih =>
  intro F hF_rank
  have hbqo_le : ∀ β, β ≤ α → TwoBQO (ScatFun.LevelLT.reduces β) :=
    fun β hβα => hbqo.comap
      (fun G : ScatFun.LevelLT β => (⟨G.val, lt_of_lt_of_le G.prop hβα⟩ : ScatFun.LevelLT α))
  have h_ind : ∀ β < α, ∀ (G : ScatFun), CBRank G.func = β → IsLocallyCentered G.func :=
    fun β hβ G hG => ih β hβ (hβ.trans hα) (hbqo_le β hβ.le) G hG
  rcases eq_or_ne α 0 with hα0 | hα0
  · exact locallyCentered_rank_zero_scatFun F (hα0 ▸ hF_rank)
  · by_cases hlim : Order.IsSuccLimit α
    · exact locallyCentered_limit_rank_scatFun F α hlim hα0 hF_rank h_ind
    · obtain ⟨γ, rfl⟩ : ∃ γ, α = Order.succ γ := by
        contrapose! hlim
        exact ⟨fun h => hα0 h.eq_bot, fun γ hγ => hlim γ hγ.succ_eq.symm⟩
      exact locallyCentered_succ_rank_scatFun γ
        (lt_of_le_of_lt (Order.le_succ γ) hα) hbqo F hF_rank h_ind



end
