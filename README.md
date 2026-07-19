# A well-quasi-order for continuous functions — a Lean 4 formalization

[![CI](https://github.com/yannpequignot/lean-wqo-continuous-functions/actions/workflows/ci.yml/badge.svg)](https://github.com/yannpequignot/lean-wqo-continuous-functions/actions/workflows/ci.yml)
![Lean 4](https://img.shields.io/badge/Lean-v4.28.0-purple.svg)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)
![sorry-free](https://img.shields.io/badge/headline%20results-sorry--free-success.svg)

A **Lean 4** formalization of the results in the preprint
**[A well-quasi-order for continuous functions](https://arxiv.org/abs/2410.13150)**
(R. Carroy & Y. Pequignot). The three main theorems and the central 2-BQO result are
**fully proved and `sorry`-free**; a green [CI run](#-verification--auditing) is a
machine-checked certificate of that claim (see below).

## 🧠 Mathematical overview

A **well-quasi-order** (WQO) is a quasi-order in which every infinite sequence
$(x_i)_{i\in\mathbb N}$ contains an increasing pair $x_i \le x_j$ with $i < j$. WQO theory
is central to termination arguments, ordinal analysis, and the theory of Borel/continuous
reducibility in descriptive set theory.

We study the following quasi-order on functions.

>**Definition** A function `f : X → Y'` **continuously reduces** to `g : X' → Y'`, written `f ≤ g`, if there is a continuous `σ : X → X'` and a function `τ : Y' → Y` that is continuous on `im(g ∘ σ)` such that `f(x) = τ(g(σ(x)))` for all `x` in `X`.

```mermaid
flowchart LR
    A(" ") -. σ .-> C
    C(" ") -- g --> D(" ")
    D -. τ .-> B
    A -- f --> B(" ")

    style C stroke-width:0px,stroke-dasharray:0,fill:transparent
    style D fill:transparent,stroke-width:0px,stroke-dasharray:0
    style A fill:transparent,stroke-width:0px,stroke-dasharray:0
    style B fill:transparent,stroke-width:0px,stroke-dasharray:0
```

**A note on the formalization.** The definition above is the memoir's, formalized *verbatim*
as `ContinuouslyReduces_range_based` (with `τ` a bundled continuous map
`im(g ∘ σ) → im f`). The development, however, mostly works with the slightly different
`ContinuouslyReduces`, which asks instead for a **total** map `τ : Y' → Y` that is continuous
*on* `im(g ∘ σ)`. This is far more convenient in Lean: the type of `τ` is then fixed and does
not depend on the data `σ, f, g`, so composing reductions or pre-composing with a homeomorphism
never forces a transport across changing subtypes. The two notions **coincide whenever the
codomain is nonempty** (`continuouslyReduces_iff_range_based`) — in particular on `ScatFun`,
where the codomain is Baire space — and differ only for the empty function, which the
range-based version (matching the paper) handles vacuously. Both definitions, and the bridge
between them, live in [`ContinuousReducibility/Defs.lean`](WqoContinuousFunctions/ContinuousReducibility/Defs.lean).

> **Main Theorem 1.** Continuous reducibility is a well-quasi-order on the class of
> continuous functions between separable metrizable spaces with Polish zero-dimensional domains.

> **Main Theorem 2.** Continuous reducibility is a well-quasi-order on the class of
> continuous functions between separable metrizable spaces with zero-dimensional domains and countable codomains.

> **Main Theorem 3.** Continuous reducibility is a well-quasi-order on the class of
> **scattered** continuous functions from a zero-dimensional separable metrizable space to a metrizable space.


Because WQOs are not closed under the infinitary operations the proof requires, the theorem
is obtained by establishing the stronger property of being a **better-quasi-order** (BQO) —
in fact the formalization uses **2-BQO**, an intermediate strengthening of WQO that suffices to run the argument.

## 📖 Where the mathematics lives

Each memoir result maps to a named Lean declaration. `#print axioms <name>` on any of these
lists only the three standard axioms — no `sorryAx`.

| Memoir | Statement | Lean declaration | File |
| --- | --- | --- | --- |
| Main Theorem 1 | WQO, Polish zero-dimensional source | `MainTheorem1` | [`MainResults/Main.lean`](WqoContinuousFunctions/MainResults/Main.lean) |
| Main Theorem 2 | WQO, countable codomain | `MainTheorem2` | [`MainResults/Main.lean`](WqoContinuousFunctions/MainResults/Main.lean) |
| Main Theorem 3 | WQO, zero-dim. separable metrizable source | `MainTheorem3` | [`MainResults/Main.lean`](WqoContinuousFunctions/MainResults/Main.lean) |
| (core) the 2-BQO version of Theorem 1.4 | Continuous reducibility on `ScatFun` --- scattered continuous functions $f:A\to \mathbb{N}^\mathbb{N}$ with $A\subseteq \mathbb{N}^\mathbb{N}$ ---  is a 2-BQO | `ScatFun.Reduces.isTwoBQO` | [`MainResults/ScatFunBQO.lean`](WqoContinuousFunctions/MainResults/ScatFunBQO.lean) |
| Thm 4.7 | Centered ⟺ a pointed gluing (monotone) | `centeredAsPgluing_iff_monotone` | [`CenteredFunctions/CenteredAsPgluing.lean`](WqoContinuousFunctions/CenteredFunctions/CenteredAsPgluing.lean) |
| Thm 4.8 | Local centeredness from 2-BQO | `localCenterednessFromTwoBQO_scatFun` | [`CenteredFunctions/LocallyCentered/Theorem.lean`](WqoContinuousFunctions/CenteredFunctions/LocallyCentered/Theorem.lean) |
| Thm 4.10 | Finiteness of centered functions | `finitenessOfCenteredFunctions` | [`CenteredFunctions/Finiteness.lean`](WqoContinuousFunctions/CenteredFunctions/Finiteness.lean) |
| Proposition 2.11 | `f` scattered ⟺ empty perfect kernel | `scattered_iff_empty_perfectKernel` | [`ContinuousReducibility/Scattered/CBAnalysis.lean`](WqoContinuousFunctions/ContinuousReducibility/Scattered/CBAnalysis.lean) |
| Theorem 2.7 | Non-scattered `f` ⇒ `id_ℚ` embeds (`CantorRat` model) | `nonscattered_embeds_idCantorRat` | [`ContinuousReducibility/Scattered/NonScattered.lean`](WqoContinuousFunctions/ContinuousReducibility/Scattered/NonScattered.lean) |
| Proposition 2.10 | Non-scattered `f` on a Polish domain ⇒ `id_𝒩` embeds (`CantorSpace` model; weak Perfect Function Property) | `nonscattered_embeds_idCantor` | [`ContinuousReducibility/Scattered/NonScattered.lean`](WqoContinuousFunctions/ContinuousReducibility/Scattered/NonScattered.lean) |

For the full proof tree — every lemma, and how the chapters fit together — see
[STRUCTURE.md](STRUCTURE.md).

## ✅ Verification & auditing

Since the memoir is under review, this repository doubles as a **machine-checked
certificate**: the Lean kernel accepts every proof, and a script re-checks that the headline
results use no `sorry`. Nothing needs to be trusted beyond Lean's kernel and the pinned
Mathlib version.

There are two independent ways an auditor can confirm this:

1. **Continuous integration.** Every push and pull request runs
   [`.github/workflows/ci.yml`](.github/workflows/ci.yml): it builds the entire development
   with the pinned Mathlib (`v4.28.0`) and kernel-checks every proof. The badge at the top of
   this file reflects the latest run. A green badge ⇒ everything compiles and the axiom audit
   passed.

2. **The axiom audit.** [`WqoContinuousFunctions/AxiomAudit.lean`](WqoContinuousFunctions/AxiomAudit.lean)
   is part of the default build. For each headline theorem it collects the axioms its proof
   depends on and **fails the build** unless that set is contained in
   `{propext, Classical.choice, Quot.sound}` — the three standard axioms of classical Lean.
   Since `sorry` elaborates to the extra axiom `sorryAx`, this rejects any hidden `sorry`.

To reproduce locally:

```bash
git clone https://github.com/yannpequignot/lean-wqo-continuous-functions.git
cd lean-wqo-continuous-functions
lake exe cache get      # download the prebuilt Mathlib cache (do this first!)
lake build              # builds + kernel-checks everything, incl. the axiom audit
```

> ⚠️ **Run `lake exe cache get` before `lake build`.** Without the cache, `lake` compiles all
> of Mathlib from source (hours, and frequently out of memory). With it, a clean build takes a
> few minutes. Install [`elan`](https://github.com/leanprover/elan) first — it reads
> `lean-toolchain` and fetches the correct Lean version automatically.

To spot-check a single result interactively, add e.g.

```lean
#print axioms ScatFun.Reduces.isTwoBQO
```

to any file; the output lists `sorryAx` **iff** a `sorry` is reachable from that theorem.

## 📦 Project layout

The package bundles four Lean libraries; each builds on its own:

```bash
lake build BQO                     # better-quasi-order foundations (Mathlib-only)
lake build ZeroDimensionalSpaces   # Baire/Cantor topology + Sierpiński universality (Mathlib-only)
lake build GeneralTopology         # general point-set topology helpers (Mathlib-only)
lake build WqoContinuousFunctions  # the main development (default target)
```

- **`BQO`** — better-quasi-order foundations: Ramsey-type theorems, 2-BQO closure properties,
  ordinal BQO. Depends only on Mathlib.
- **`ZeroDimensionalSpaces`** — Baire/Cantor space basics, zero-dimensional spaces, the
  Cantor-scheme embedding machinery, and **Sierpiński universality** (every countable
  metrizable space embeds into any nonempty perfect countable metrizable space), which
  supplies the universal top element of Main Theorem 2. Depends only on Mathlib.
- **`GeneralTopology`** — general point-set facts (countable clopen partitions, discrete
  subspaces, disjoint open neighbourhoods) that are Mathlib candidates. Depends only on
  Mathlib.
- **`WqoContinuousFunctions`** — the main development, building on all three.

## 🚀 Status

- [x] **Core definitions** — continuous reducibility, scattered functions, and 2-BQO.
- [x] **Main Theorems 1–3** — all three stated and **fully proved, `sorry`-free**, end to end
  (the scattered/non-scattered dichotomy, the WQO/BQO machinery, the universality top
  elements).
- [x] **Centered functions (Chapter 4)** — fully formalized and `sorry`-free: the consequences
  of the General Structure Theorem, the centered-as-pointed-gluing characterization (Thm 4.6),
  local centeredness from 2-BQO (Thm 4.7), finiteness of centered functions (Thm 4.9), and the
  successor classification (Cor 4.10).
- [x] **Precise Structure (Ch. 5) & Double Successor (Ch. 6)** — the input
  `ScatFun.levels_finitely_generated` (finite generation of each CB-rank level) is fully
  formalized, resting on the §6.4 solvable-functions development in
  `DoubleSuccessor/Solvable.lean`.

## 💻 Core definitions in Lean

```lean
/-- The memoir's definition (verbatim): `τ` is a bundled continuous map
`im(g ∘ σ) → im f`.  See the note above on why the development prefers the total-`τ`
variant below; the two agree on `ScatFun` via `continuouslyReduces_iff_range_based`. -/
def ContinuouslyReduces_range_based (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : C(X, X'),
  ∃ τ : C(Set.range (g ∘ σ), Set.range f),
    ∀ x : X, τ ⟨g (σ x), Set.mem_range_self x⟩ = ⟨f x, Set.mem_range_self x⟩

/-- The working definition used throughout the development: `f` continuously reduces to `g`
if there is a continuous `σ : X → X'` and a **total** function `τ : Y' → Y` that is continuous
on `im(g ∘ σ)` such that `f x = τ (g (σ x))` for all `x`. -/
def ContinuouslyReduces {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : X → X', Continuous σ ∧
  ∃ τ : Y' → Y, ContinuousOn τ (Set.range (g ∘ σ)) ∧
    ∀ x : X, f x = τ (g (σ x))

/-- A function `f : X → Y` is *scattered* if every nonempty `S ⊆ X` contains a nonempty
relatively open subset on which `f` is constant. -/
def ScatteredFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ S : Set X, S.Nonempty → ∃ U : Set X, IsOpen U ∧ (U ∩ S).Nonempty ∧
    ∀ x ∈ U ∩ S, ∀ x' ∈ U ∩ S, f x = f x'
```

## 📄 References

1. R. Carroy & Y. Pequignot (2024). *A well-quasi-order for continuous functions.*
   [arXiv:2410.13150](https://arxiv.org/abs/2410.13150).
2. Y. Pequignot (2017). *Towards better: a motivated introduction to better-quasi-orders.*
   EMS Surveys in Mathematical Sciences.
   [ems.press](https://ems.press/journals/emss/articles/15096).

## 🙏 Acknowledgements

This formalization was developed with the assistance of frontier AI proof assistants,
including **[Aristotle](https://aristotle.harmonic.fun)** (Harmonic), **Claude Code**.
