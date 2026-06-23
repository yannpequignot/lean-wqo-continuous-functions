import Mathlib.Tactic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import ZeroDimensionalSpaces.CantorRat
import ZeroDimensionalSpaces.Engine
import ZeroDimensionalSpaces.SierpinskiAux
import ZeroDimensionalSpaces.SierpinskiForth

/-!
# Sierpiński universality

* `sierpinski_universal` — every countable metrizable space embeds topologically into any
  nonempty perfect countable metrizable space (`∃ h : X → Y, IsEmbedding h`). This is the
  "mutual embeddability" form of Sierpiński's theorem: strictly weaker than the homeomorphism
  characterisation `X ≃ₜ ℚ` (only the one-directional "forth" embedding is needed), relying
  solely on the abstract properties shared by `ℚ` — countable, metrizable, perfect.

It is proved by composing the two directional embeddings through the canonical model `CantorRat`:

* `countable_metrizable_embeds_cantorRat` (in `SierpinskiForth.lean`) — `X ↪ CantorRat`;
* `cantorRat_embeds_perfect` (in `SierpinskiAux.lean`) — `CantorRat ↪ Y`.

The first is exactly the consequence the WQO development needs for `MainTheorem2`: every
countable metrizable space embeds into `CantorRat`.
-/

open scoped Topology
open Set Function TopologicalSpace SierpinskiBuild

set_option autoImplicit false

/-! ## Strategy: factor through `CantorRat`

`sierpinski_universal` is proved by composing the two directional embeddings through the
canonical model `CantorRat`:

* `countable_metrizable_embeds_cantorRat` (in `SierpinskiForth.lean`): every countable metrizable
  space embeds into `CantorRat`. This is the genuine "forth" construction — a refining binary
  tree of clopen cells whose `0`-branch always tracks the least-indexed point, so each point's
  address sequence is eventually zero (lands in `CantorRat`). Completeness is never used because
  each value is fixed at a finite stage.
* `cantorRat_embeds_perfect` (in `SierpinskiAux.lean`): `CantorRat` embeds into any nonempty
  perfect metrizable space, via a binary Cantor scheme of nested sibling-disjoint closed balls
  fed to `cantor_sigma_isEmbedding`.

Composing gives `X ↪ CantorRat ↪ Y`.
 -/

/-- **Sierpiński universality.** Every countable metrizable space embeds topologically into any
nonempty perfect (no isolated points) countable metrizable space.

Proof: compose `X ↪ CantorRat` (`countable_metrizable_embeds_cantorRat`) with `CantorRat ↪ Y`
(`cantorRat_embeds_perfect`). Neither perfectness nor nonemptiness of the source `X` is needed;
only the target `Y` must be nonempty and perfect. -/
theorem sierpinski_universal {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [Countable X]
    [TopologicalSpace Y] [MetrizableSpace Y] [Countable Y] [Nonempty Y]
    (hniY : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) :
    ∃ h : X → Y, Topology.IsEmbedding h := by
  obtain ⟨f, hf⟩ := countable_metrizable_embeds_cantorRat (X := X)
  obtain ⟨g, hg⟩ := cantorRat_embeds_perfect hniY
  exact ⟨g ∘ f, hg.comp hf⟩
