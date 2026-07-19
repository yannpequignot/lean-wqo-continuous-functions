import WqoContinuousFunctions.ScatFun.Operations.Gl
import WqoContinuousFunctions.ScatFun.Operations.Pgl
import WqoContinuousFunctions.ScatFun.Operations.GlReduces
import WqoContinuousFunctions.ScatFun.Operations.MaxMinFun

/-!
# Bundled operations on `ScatFun` (re-export shim)

Historically this file held **all** the bundled `ScatFun` operations.  It has been split into
focused modules so that downstream consumers can import only what they use (and so that editing
one cluster no longer perturbs the global declaration environment of the others — see the
`grind`-env-sensitivity notes in the project memory):

* `ScatFun.Operations.Gl`        — plain gluing `gl`, `empty`, `reduces_iff` (light)
* `ScatFun.Operations.Pgl`       — pointed gluing `pgl`, `rayOn`, `pgl_reduces_of_local*`
* `ScatFun.Operations.GlReduces` — reduction combinators for `gl` (and `gl ↪ pgl`)
* `ScatFun.Operations.MaxMinFun` — the bundled generators `maxFun` / `minFun` / `succMaxFun`

This module now merely re-exports the four, so existing `import WqoContinuousFunctions.ScatFun.Operations`
lines keep resolving every previous name unchanged.  New code should prefer importing the specific
sub-module(s) it needs.
-/
