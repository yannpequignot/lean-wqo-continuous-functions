# Mathlib-guideline compliance — honest assessment

**Date:** 2026-07-20
**Scope:** the **public repository** — all `.lean` files *except* `MathlibPR/` (a staging copy of
the `BQO` library for upstreaming). Confirmed against `.publishignore`: `.tex`/`.pdf`, internal
notes, and `MathlibPR/` are excluded from the public showcase; no Lean chapters are excluded.
**Size:** 117 `.lean` files · 49,916 lines · 1,616 declarations.
**Build:** green — `lake build` = 3231 jobs, 0 errors, 0 warnings.

This document is a *self-assessment against Mathlib's contribution guidelines*, not a claim that
the repo is Mathlib-submittable as-is. It distinguishes **verification integrity** (is the maths
actually proved and sound?) from **mechanical compliance** (does the code meet Mathlib's stylistic
and reproducibility conventions?).

---

## 1. Verification integrity — clean

| Check | Status | Evidence |
|---|---|---|
| Build | ✅ green | 3231 jobs, 0 errors, 0 warnings |
| Real `sorry`s | ✅ **0** | only two *prose* mentions in `AxiomAudit.lean`'s docstring |
| Crown results certified | ✅ | `#assert_standard_axioms` on `MainTheorem1/2/3`, `ScatFun.Reduces.isTwoBQO`, `localCenterednessFromTwoBQO_scatFun` — standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), so no `sorryAx` anywhere in their dependency tree |
| `native_decide` | ✅ 0 | — |
| `unsafe` declarations | ✅ 0 | — |

The five headline results are machine-checkably complete: a green build of `AxiomAudit.lean` is
itself the certificate. The whole development is 0-sorry.

---

## 2. Mechanical compliance — compliant / essentially done

| Guideline | Metric | Notes |
|---|---|---|
| `grind +suggestions` eliminated | **1** remaining (was 111) | `+suggestions` feeds a non-reproducible library-suggestion engine into `grind`; converted to explicit `grind [lemmas]`. The one remaining site (`FinitenessHelpers`, `Gl_subfamily_mem`) genuinely can't be surfaced as an explicit set and is documented in-file. |
| `set_option maxHeartbeats` right-sized | **12** overrides (was 16); max **3.2M** (was 8M) | Total override budget ~74M → ~14M; 4 removed outright (fit under the 200k default). The 12 survivors are build-necessary; shrinking them further needs real proof optimization. |
| `set_option autoImplicit false` | **all declaration-bearing files** | Only 3 zero-declaration re-export shims lack it (`ContinuousReducibility/Gluing.lean`, `.../Scattered.lean`, `ScatFun/Operations.lean`), where it is irrelevant. |
| `haveI` / `letI` → `have` / `let` | **7** left | Near-eliminated. |
| Module docstrings | **115 / 117** | Two files lack a `/-!` header. |
| `native_decide` / `unsafe` | 0 / 0 | — |
| Dead/orphan code | crown-relevant | Removed the `RegularSimple` orphan (Prop 3.8, unused by any main result); the repo is now crown-relevant apart from two intentional above-crown modules: `WqoContinuousFunctions/Main.lean` (re-export umbrella) and `AxiomAudit.lean` (verification harness). |

---

## 3. Mechanical compliance — not yet met

| Guideline | Metric | Assessment |
|---|---|---|
| **Line length ≤ 100** | **1,657** lines (210 comment/docstring · **1,447 code**) | The largest gap. The 1,447 code lines are *not* safely bulk-automatable — each needs a hand-chosen break point (after `,`/`:=`/an operator); a blind wrapper would mass-break the build. Best handled opportunistically. |
| **Proof length ≤ 50** | ~**207** declarations | The figure is inflated (a decl followed by a docstring'd decl absorbs that docstring); the true count is lower. The longest proofs (600 / 512 / 507 / … lines) are *phase-structured* and legitimately do **not** factor into named sub-lemmas without threading 20+ parameters, which would worsen readability. Only genuinely case-structured medium proofs are worth splitting. |
| `refine'` → `refine` | **97** | A prior audit found the remainder genuinely require `refine'` (elaboration-order differences). |
| Terminal / `only`-`simp` discipline | ~230 non-`only` `simp` (noisy estimate) | Over-counts legitimate terminal `simp`; needs case-by-case review, low priority. |
| `+decide` usage | **1,024** | Not a hard violation, but heavy; contributes to elaboration cost. |
| Naming (snake_case theorems, lowerCamelCase defs) | `MainTheorem1/2/3` (PascalCase), a handful of camelCase Props, some scheme-code names | **Intentionally deferred** by the author ("labels for now, rename later"). Object-prefixed names such as `CBLevel_*` are idiomatic Mathlib, **not** violations. |

---

## 4. Bottom line

- **As a verified artifact: excellent.** 0 sorries, standard axioms only, green build; the main
  theorem chain is machine-checkably complete.
- **As Mathlib-submittable code: partial — mostly for defensible reasons.** The finite, high-signal
  mechanical items (`grind +suggestions`, `maxHeartbeats`, `autoImplicit`) are done. What remains
  (line length, proof length, `refine'`, naming) is either genuinely hard to automate safely,
  legitimately non-conforming (giant proofs that do not factor), or deliberately deferred.
- **Scope reality:** most of this repo is a **private memoir formalization**. Only the `MathlibPR/`
  staging area is actually headed upstream and should be held to the full bar; applying strict
  mechanics to all ~50k lines is low ROI.

---

## 5. Metric summary (at a glance)

| Metric | Value |
|---|---|
| `.lean` files (public scope) | 117 |
| Lines | 49,916 |
| Declarations | 1,616 |
| Real `sorry`s | **0** |
| Build | green (3231 jobs, 0 errors, 0 warnings) |
| `native_decide` / `unsafe` | 0 / 0 |
| `grind +suggestions` | 1 |
| `set_option maxHeartbeats` overrides (max value) | 12 (3.2M) |
| Files missing `autoImplicit false` (with declarations) | 0 |
| Module docstrings present | 115 / 117 |
| `haveI` / `letI` | 7 |
| `refine'` | 97 |
| Lines > 100 chars (code / comment) | 1,657 (1,447 / 210) |
| Declarations with proof body > 50 lines | ~207 (docstring-inflated) |
| `+decide` occurrences | 1,024 |
