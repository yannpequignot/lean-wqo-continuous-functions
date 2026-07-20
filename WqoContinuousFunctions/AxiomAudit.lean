/-
# Axiom audit — a machine-checkable certificate of soundness

This file is part of the default `lake build` target. It does **not** prove any new
mathematics; instead it re-checks, at compile time, that the project's headline results
rest on nothing but the three standard axioms of Lean's classical logic:

* `propext`          — propositional extensionality,
* `Classical.choice` — the axiom of choice,
* `Quot.sound`       — soundness of quotients.

In particular this rules out `sorryAx`: if any proof in the dependency tree of a checked
theorem contained a `sorry` (or any other extra axiom), the command below throws and the
build fails. So a *green build of this file is itself the certificate* that the listed
theorems are fully proved — there is nothing to run and no trust in the author required
beyond trusting Lean's kernel and the pinned Mathlib.

To audit interactively instead, Lean's built-in `#print axioms <name>` prints the same
axiom set for any declaration (it lists `sorryAx` iff a `sorry` is reachable).
-/

import WqoContinuousFunctions.MainResults.Main
import WqoContinuousFunctions.MainResults.ScatFunBQO
import WqoContinuousFunctions.CenteredFunctions.LocallyCentered.Theorem
import WqoContinuousFunctions.CenteredFunctions.Finiteness

set_option autoImplicit false

open Lean Elab Command in
/-- `#assert_standard_axioms foo` fails the build unless every axiom reachable from `foo`'s
proof is one of the three standard classical axioms `propext`, `Classical.choice`,
`Quot.sound`. In particular it fails if `foo` (transitively) uses `sorryAx`. -/
elab "#assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axs ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError
      "Axiom audit FAILED: `{name}` depends on non-standard axiom(s) {bad.toList}.\n\
       Only propext, Classical.choice, Quot.sound are permitted (this catches sorryAx)."

-- === Main Theorems (Chapter 3) ==============================================
-- Continuous reducibility is a WQO on scattered continuous functions, in three
-- ambient-space regimes (see `MainResults/Main.lean`).
#assert_standard_axioms MainTheorem1
#assert_standard_axioms MainTheorem2
#assert_standard_axioms MainTheorem3

-- The central strengthening: continuous reducibility of the `ScatFun` invariants is a
-- 2-BQO. Everything above reduces to this.
#assert_standard_axioms ScatFun.Reduces.isTwoBQO

-- === Centered functions (Chapter 4) =========================================
#assert_standard_axioms localCenterednessFromTwoBQO_scatFun  -- Theorem 4.8
#assert_standard_axioms finitenessOfCenteredFunctions        -- Theorem 4.10

-- === Scattered/non-scattered dichotomy (Chapter 2) ==========================
#assert_standard_axioms scattered_iff_empty_perfectKernel     -- `scatterediffemptykernel`
#assert_standard_axioms nonscattered_embeds_idCantorRat       -- `prop:nlc_implies_nonscattered`
#assert_standard_axioms nonscattered_embeds_idCantor          -- `uncountablerange` (weak PFP)
