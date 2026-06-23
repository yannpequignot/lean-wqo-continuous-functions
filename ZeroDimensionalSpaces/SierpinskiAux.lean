import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Uniformity
import ZeroDimensionalSpaces.CantorRat
import ZeroDimensionalSpaces.Engine
import ZeroDimensionalSpaces.CantorScheme

/-!
# Auxiliary constructions for Sierpiński universality

This file isolates the two directional embedding lemmas used to prove
`sierpinski_universal` in `Embedding.lean`:

* `cantorRat_embeds_perfect` — `CantorRat` embeds topologically into any nonempty perfect
  countable metrizable space `Y`.  This is the "easy" direction: it builds a binary Cantor
  scheme of nested, sibling-disjoint closed balls in `Y` (using perfectness to find a second
  point at each node) and feeds it to `cantor_sigma_isEmbedding`.

The genuinely hard "forth" direction (`X ↪ CantorRat`) is developed in `SierpinskiForth.lean`.
-/

open scoped Topology
open Set Function TopologicalSpace SierpinskiBuild Metric

set_option autoImplicit false

namespace SierpinskiAux

variable {Y : Type*} [MetricSpace Y]

/-- **One node of the scheme.** In a metric space with no isolated points, given a centre `y0`
and a radius `ρ > 0`, we can pick a second centre `y1` and two radii `r0, r1` (encoded as a
triple `t = (y1, r0, r1)`), each `≤ ρ/2`, whose closed balls sit inside `ball y0 ρ` and are
disjoint. The first ball is centred at `y0` itself (this realises the `0`-child, keeping the
centre), the second at the new point `y1` (the `1`-child). -/
lemma scheme_step (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y0 : Y) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : Y × ℝ × ℝ, 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.2.1 ≤ ρ / 2 ∧ t.2.2 ≤ ρ / 2 ∧
      Metric.closedBall y0 t.2.1 ⊆ Metric.ball y0 ρ ∧
      Metric.closedBall t.1 t.2.2 ⊆ Metric.ball y0 ρ ∧
      Disjoint (Metric.closedBall y0 t.2.1) (Metric.closedBall t.1 t.2.2) := by
  have hinf : (Metric.ball y0 ρ).Infinite :=
    open_infinite hni Metric.isOpen_ball ⟨y0, Metric.mem_ball_self hρ⟩
  obtain ⟨y1, hy1, hy1ne⟩ : ∃ y1 ∈ Metric.ball y0 ρ, y1 ≠ y0 := by
    obtain ⟨y1, hy1⟩ := (hinf.diff (Set.finite_singleton y0)).nonempty
    exact ⟨y1, hy1.1, by simpa using hy1.2⟩
  set d := dist y1 y0 with hd
  have hd_pos : 0 < d := dist_pos.mpr hy1ne
  have hd_lt : d < ρ := Metric.mem_ball.mp hy1
  set δ := min (ρ - d) d / 3 with hδ
  have hmin_le1 : min (ρ - d) d ≤ ρ - d := min_le_left _ _
  have hmin_le2 : min (ρ - d) d ≤ d := min_le_right _ _
  have hδ_pos : 0 < δ := by
    have : 0 < min (ρ - d) d := lt_min (by linarith) hd_pos
    positivity
  have hδ_lt1 : δ < ρ - d := by rw [hδ]; linarith
  have hδ_le2 : δ ≤ d := by rw [hδ]; linarith
  refine ⟨(y1, δ, δ), hδ_pos, hδ_pos, by linarith, by linarith, ?_, ?_, ?_⟩
  · exact Metric.closedBall_subset_ball (by linarith)
  · intro z hz
    rw [Metric.mem_closedBall] at hz
    dsimp only at hz
    rw [Metric.mem_ball]
    calc dist z y0 ≤ dist z y1 + dist y1 y0 := dist_triangle z y1 y0
      _ ≤ δ + d := by rw [← hd]; linarith
      _ < ρ := by linarith
  · rw [Set.disjoint_left]
    intro z hz0 hz1
    rw [Metric.mem_closedBall] at hz0 hz1
    dsimp only at hz0 hz1
    have hcontr : d ≤ 2 * δ := by
      calc d = dist y1 y0 := hd
        _ ≤ dist y1 z + dist z y0 := dist_triangle y1 z y0
        _ = dist z y1 + dist z y0 := by rw [dist_comm y1 z]
        _ ≤ δ + δ := by linarith
        _ = 2 * δ := by ring
    linarith

/-- The data chosen at a node: from a centre `y0` and radius `ρ`, the triple `(y1, r0, r1)`.
A junk value is returned when `ρ ≤ 0` (never used, since all radii stay positive). -/
noncomputable def childData (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y0 : Y) (ρ : ℝ) :
    Y × ℝ × ℝ :=
  if h : 0 < ρ then (scheme_step hni y0 h).choose else (y0, ρ, ρ)

lemma childData_spec (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y0 : Y) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < (childData hni y0 ρ).2.1 ∧ 0 < (childData hni y0 ρ).2.2 ∧
      (childData hni y0 ρ).2.1 ≤ ρ / 2 ∧ (childData hni y0 ρ).2.2 ≤ ρ / 2 ∧
      Metric.closedBall y0 (childData hni y0 ρ).2.1 ⊆ Metric.ball y0 ρ ∧
      Metric.closedBall (childData hni y0 ρ).1 (childData hni y0 ρ).2.2 ⊆ Metric.ball y0 ρ ∧
      Disjoint (Metric.closedBall y0 (childData hni y0 ρ).2.1)
        (Metric.closedBall (childData hni y0 ρ).1 (childData hni y0 ρ).2.2) := by
  rw [childData, dif_pos hρ]
  exact (scheme_step hni y0 hρ).choose_spec

/-- The recursive scheme data: for each finite binary string `l`, the centre and radius at that
node. The `0`-child keeps the parent centre; the `1`-child moves to the new point. -/
noncomputable def schemeData (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) :
    List (Fin 2) → Y × ℝ
  | [] => (y₀, 1)
  | a :: l =>
      let p := schemeData hni y₀ l
      let ch := childData hni p.1 p.2
      if a = 0 then (p.1, ch.2.1) else (ch.1, ch.2.2)

/-- Centre map of the scheme. -/
noncomputable def schemeCentre (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y)
    (l : List (Fin 2)) : Y := (schemeData hni y₀ l).1

/-- Radius map of the scheme. -/
noncomputable def schemeRadius (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y)
    (l : List (Fin 2)) : ℝ := (schemeData hni y₀ l).2

lemma schemeRadius_pos (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) (l : List (Fin 2)) :
    0 < schemeRadius hni y₀ l := by
  induction' l with a l ih;
  · exact zero_lt_one;
  · fin_cases a <;> simp +decide [ schemeRadius, schemeData ];
    · exact childData_spec hni _ ih |>.1;
    · exact childData_spec hni _ ih |>.2.1

lemma scheme_hc_zero (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) (l : List (Fin 2)) :
    schemeCentre hni y₀ (0 :: l) = schemeCentre hni y₀ l := by
  rfl

lemma scheme_hr_half (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) (l : List (Fin 2))
    (a : Fin 2) : schemeRadius hni y₀ (a :: l) ≤ schemeRadius hni y₀ l / 2 := by
  grind +locals

lemma scheme_hball (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) (l : List (Fin 2))
    (a : Fin 2) :
    Metric.closedBall (schemeCentre hni y₀ (a :: l)) (schemeRadius hni y₀ (a :: l)) ⊆
      Metric.ball (schemeCentre hni y₀ l) (schemeRadius hni y₀ l) := by
  fin_cases a <;> simp +decide [ schemeCentre, schemeRadius, schemeData ];
  · exact childData_spec hni _ ( schemeRadius_pos hni y₀ l ) |>.2.2.2.2.1;
  · convert ( childData_spec hni ( schemeData hni y₀ l |>.1 ) ( schemeRadius_pos hni y₀ l ) ) |>.2.2.2.2.2.1 using 1

lemma scheme_hdisj (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) (y₀ : Y) (l : List (Fin 2)) :
    Disjoint (Metric.closedBall (schemeCentre hni y₀ (0 :: l)) (schemeRadius hni y₀ (0 :: l)))
      (Metric.closedBall (schemeCentre hni y₀ (1 :: l)) (schemeRadius hni y₀ (1 :: l))) := by
  convert ( childData_spec hni ( schemeCentre hni y₀ l ) ( schemeRadius_pos hni y₀ l ) ).2.2.2.2.2.2 using 1

end SierpinskiAux

/-- **`CantorRat` embeds into any nonempty perfect countable metrizable space.**

We choose a compatible metric on `Y`, build a binary Cantor scheme of nested,
sibling-disjoint closed balls (`SierpinskiAux.schemeCentre` / `schemeRadius`) using perfectness
to obtain a fresh point at each node, and apply `cantor_sigma_isEmbedding`. -/
theorem cantorRat_embeds_perfect {Y : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [Nonempty Y] (hni : ∀ y : Y, ¬ IsOpen ({y} : Set Y)) :
    ∃ f : CantorRat → Y, Topology.IsEmbedding f := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  refine ⟨fun x => SierpinskiAux.schemeCentre hni y₀ (cantorRatPrefix x), ?_⟩
  exact cantor_sigma_isEmbedding
    (SierpinskiAux.schemeRadius_pos hni y₀)
    (SierpinskiAux.scheme_hc_zero hni y₀)
    (SierpinskiAux.scheme_hr_half hni y₀)
    (SierpinskiAux.scheme_hball hni y₀)
    (SierpinskiAux.scheme_hdisj hni y₀)