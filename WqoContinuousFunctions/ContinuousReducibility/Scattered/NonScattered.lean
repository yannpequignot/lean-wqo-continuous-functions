import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import Mathlib.Topology.MetricSpace.Polish
import ZeroDimensionalSpaces.CantorRat
import ZeroDimensionalSpaces.CantorScheme
import ZeroDimensionalSpaces.CantorSchemeComplete

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Non-Scattered Embedding Theorem

If `f : X → Y` is continuous from a metrizable space to a Hausdorff space and `f` is
not scattered, then a perfect countable space (`CantorRat`, or the full `2^ℕ` when the
domain is complete) continuously reduces to `f`.

## Main results

* `nonscattered_embeds_idCantorRat` — non-scattered implies a `CantorRat`-embedding (the
  Sierpiński-free lower bound used by `MainTheorem2`)
* `nonscattered_embeds_idCantor` — non-scattered implies a `2^ℕ`-embedding (used by
  `MainTheorem1`)
-/

section NonScatteredTheorem

/-!
## Theorem 2.5 (prop:nlc_implies_nonscattered)

If `f : X → Y` is continuous from a metrizable space to a Hausdorff space and `f` is
not scattered, then `id_ℚ` continuously reduces to `f`.

**Formalization note:** The original statement used `TopologicallyEmbedsFun (@id ℚ) f`,
which requires a *global* topological embedding `τ : Y → ℚ`. This is impossible when
`Y` is uncountable (e.g. `ℝ`), since there is no injection from an uncountable type to `ℚ`.
The corrected statement uses `ContinuouslyReduces`, which only requires continuous (not
necessarily injective) maps. Even this formulation requires `τ : Y → ℚ` to be total and
continuous, which is only possible when `Y` is zero-dimensional (since `ℚ` is totally
disconnected). A fully faithful formalization would require a notion of reduction where
`τ` is only defined on a subset of `Y`.
-/

set_option maxHeartbeats 8000000 in
/-
**Splitting Lemma.** If `g` is continuous and NLC from a pseudo-metric space to a
T₂ space, then any metric ball can be split into two smaller sub-balls with disjoint
closures whose g-images lie in disjoint open sets.
-/
lemma splitting_lemma_nlc {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {g : X → Y} (hg : Continuous g) (hnlc : NowhereLocallyConstant g)
    (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ (x' : X) (ε' : ℝ),
      0 < ε' ∧ ε' < ε ∧
      Metric.closedBall x ε' ⊆ Metric.ball x ε ∧
      Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧
      Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧
      ∃ (U₀ U₁ : Set Y), IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧
        g '' (Metric.ball x ε') ⊆ U₀ ∧
        g '' (Metric.ball x' ε') ⊆ U₁ := by
  -- By NLC, find x' ∈ ball(x,ε) with g(x) ≠ g(x').
  obtain ⟨x', hx'⟩ : ∃ x' ∈ Metric.ball x ε, g x ≠ g x' := by
    contrapose! hnlc
    exact fun h => by have := h (Metric.ball x ε) (Metric.isOpen_ball) ⟨x, Metric.mem_ball_self hε⟩ ; obtain ⟨x', hx', x'', hx'', hne⟩ := this; exact hne (hnlc x' hx' ▸ hnlc x'' hx'' ▸ rfl)
  -- By T2, separate g(x) and g(x') by disjoint open U₀, U₁.
  obtain ⟨U₀, U₁, hU₀, hU₁, h_disjoint⟩ : ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧ g x ∈ U₀ ∧ g x' ∈ U₁ := by
    rcases t2_separation hx'.2 with ⟨U₀, U₁, hU₀, hU₁, hU₀₁⟩ ; use U₀, U₁ ; aesop
  -- By continuity, find δ₁, δ₂ > 0 with ball(x,δ₁) ⊆ g⁻¹(U₀) and ball(x',δ₂) ⊆ g⁻¹(U₁).
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, Metric.ball x δ₁ ⊆ g ⁻¹' U₀ := by
    exact Metric.mem_nhds_iff.1 (hg.continuousAt (hU₀.mem_nhds h_disjoint.2.1))
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, Metric.ball x' δ₂ ⊆ g ⁻¹' U₁ := by
    exact Metric.mem_nhds_iff.1 (hg.continuousAt (hU₁.mem_nhds h_disjoint.2.2))
  -- Choose ε' = min(min(min ε δ₁) δ₂)(min((ε - dist x x')/2)(dist x x' / 3)) / 2.
  obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < ε ∧ ε' < δ₁ ∧ ε' < δ₂ ∧ ε' < (ε - dist x x') / 2 ∧ ε' < dist x x' / 3 := by
    obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < min (min (min ε δ₁) δ₂) (min ((ε - dist x x') / 2) (dist x x' / 3)) := by
      refine exists_between ?_
      -- The lower bound 0 is strictly below the min of all five quantities.
      -- dist x x' > 0 because g x ≠ g x' implies x ≠ x' (MetricSpace).
      -- dist x x' < ε because x' ∈ ball(x, ε).
      -- mem_ball gives dist x' x (member first); dist_pos gives dist x x'.
      -- Supply dist_comm to linarith so it can bridge the two orderings.
      have hd    : dist x' x < ε := Metric.mem_ball.mp hx'.1
      have hdpos : 0 < dist x x' := dist_pos.mpr (fun hh => hx'.2 (congrArg g hh))
      simp only [lt_min_iff]
      exact ⟨⟨⟨hε, hδ₁_pos⟩, hδ₂_pos⟩,
             by linarith [dist_comm x' x],
             by linarith [dist_comm x' x]⟩
    exact ⟨ε', hε'_pos, by aesop⟩
  refine ⟨x', ε', hε'_pos, hε'_lt.1, ?_, ?_, ?_, ?_⟩ <;> simp_all +decide [Set.disjoint_left]
  · exact fun y hy => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) hε'_lt.1)
  · intro y hy; rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball] ; linarith [dist_triangle y x' x, dist_comm x' x]
  · intro y hy; have := dist_triangle_left x x' y; have := dist_triangle_right x x' y; norm_num at *; linarith
  · exact ⟨U₀, hU₀, U₁, hU₁, h_disjoint.1, fun y hy => hδ₁ <| Metric.ball_subset_ball (by linarith) hy, fun y hy => hδ₂ <| Metric.ball_subset_ball (by linarith) hy⟩




-- The `CantorRat` (`CantorEventuallyZero`) definitions — `IsEventuallyZero`,
-- `CantorEventuallyZero`, the `CantorRat` notation, its `TopologicalSpace` instance, and
-- `cantorRatPrefix` — now live in `ZeroDimensionalSpaces.CantorRat` (imported above).

/--
**Splitting lemma.** In a nowhere locally constant continuous function on a metric space
into a T₂ space, any ball contains two disjoint sub-balls with separated images.
-/
lemma nlc_splitting_lemma {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) :
    ∀ x : X, ∀ ε > 0, ∃ x' : X, ∃ ε' > 0, ε' < ε ∧
      Metric.closedBall x ε' ⊆ Metric.ball x ε ∧
      Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧
      Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧
      ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧
        g '' (Metric.ball x ε') ⊆ U₀ ∧ g '' (Metric.ball x' ε') ⊆ U₁ := by
  exact fun x ε a => splitting_lemma_nlc hg hnlc x ε a

/-!
**Cantor scheme existence.** Given a continuous NLC function, there exist
center/radius/open-set assignments satisfying all the Cantor scheme properties.
-/
lemma cantor_scheme_exists {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) (x₀ : X) :
    ∃ (c : List (Fin 2) → X) (r : List (Fin 2) → ℝ) (U : List (Fin 2) → Set Y),
      c [] = x₀ ∧
      (∀ l, 0 < r l) ∧
      (∀ l, c (0 :: l) = c l) ∧
      (∀ l (a : Fin 2), r (a :: l) ≤ r l / 2) ∧
      (∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
        Metric.ball (c l) (r l)) ∧
      (∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                      (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) ∧
      (∀ l (a : Fin 2), IsOpen (U (a :: l))) ∧
      (∀ l, Disjoint (U (0 :: l)) (U (1 :: l))) ∧
      (∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) := by
  -- Define the functions c, r, U by recursion on lists using the splitting lemma.
  have h_split : ∀ x : X, ∀ ε > 0, ∃ x' : X, ∃ ε' > 0, ε' < ε ∧ Metric.closedBall x ε' ⊆ Metric.ball x ε ∧ Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧ Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧ ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧ g '' (Metric.ball x ε') ⊆ U₀ ∧ g '' (Metric.ball x' ε') ⊆ U₁ := by
    exact nlc_splitting_lemma g hg hnlc
  choose! x' ε' hε' hε'_lt hε'_closedBall hε'_closedBall' hε'_disjoint hU₀ hU₁ hU₀_open hU₁_open hU₀_disjoint hU₀_image hU₁_image using h_split
  -- Define the functions c, r, U by recursion on lists using the splitting lemma and the chosen functions x', ε', hU₀, hU₁.
  have h_rec : ∃ (F : List (Fin 2) → X × ℝ × Set Y), F [] = (x₀, 1, Set.univ) ∧ (∀ l, 0 < (F l).2.1) ∧ (∀ l, (F (0 :: l)).1 = (F l).1) ∧ (∀ l, (F (1 :: l)).1 = x' (F l).1 (F l).2.1) ∧ (∀ l, (F (0 :: l)).2.1 = min ((F l).2.1 / 2) (ε' (F l).1 (F l).2.1)) ∧ (∀ l, (F (1 :: l)).2.1 = min ((F l).2.1 / 2) (ε' (F l).1 (F l).2.1)) ∧ (∀ l, (F (0 :: l)).2.2 = hU₀ (F l).1 (F l).2.1) ∧ (∀ l, (F (1 :: l)).2.2 = hU₁ (F l).1 (F l).2.1) := by
    refine ⟨fun l => List.foldr (fun a p => if a = 0 then (p.1, min (p.2.1 / 2) (ε' p.1 p.2.1), hU₀ p.1 p.2.1) else (x' p.1 p.2.1, min (p.2.1 / 2) (ε' p.1 p.2.1), hU₁ p.1 p.2.1)) (x₀, 1, Set.univ) l, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide
    intro l; induction l <;> simp +decide [*]
    split_ifs <;> simp +decide [*]
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄, hF₅, hF₆, hF₇, hF₈⟩ := h_rec; use fun l => F l |>.1, fun l => F l |>.2.1, fun l => F l |>.2.2; simp_all +decide [Fin.forall_fin_two]
  refine ⟨?_, ?_, ?_⟩
  · intro l; exact ⟨by
    exact Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self (hF₂ l))), by
      exact Set.Subset.trans (Metric.closedBall_subset_closedBall (min_le_right _ _)) (hε'_closedBall' _ _ (hF₂ _))⟩
  · intro l; specialize hε'_disjoint (F l |>.1) (F l |>.2.1) (hF₂ l) ; simp_all +decide [Set.disjoint_left]
  · intro l; specialize hU₀_image (F l |>.1) (F l |>.2.1) (hF₂ l) ; specialize hU₁_image (F l |>.1) (F l |>.2.1) (hF₂ l) ; simp_all +decide [Set.subset_def]

set_option maxHeartbeats 4000000 in
/-- The map `σ : CantorRat → X` defined by `σ(x) = c(prefix(x))` is an embedding,
and `g ∘ σ` is also an embedding, given the Cantor scheme properties. -/
lemma nlc_countable_embedding_concrete {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) [Nonempty X] :
    ∃ (σ : CantorRat → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨x₀⟩ := id ‹Nonempty X›
  obtain ⟨c, r, U, _, hr_pos, hc_zero, hr_half, hball, hdisj, hU_open, hU_disj, hU_img⟩ :=
    cantor_scheme_exists g hg hnlc x₀
  let σ : CantorRat → X := fun x => c (cantorRatPrefix x)
  refine ⟨σ, ?_, ?_⟩
  · exact cantor_sigma_isEmbedding hr_pos hc_zero hr_half hball hdisj
  · exact cantor_g_sigma_isEmbedding (U := U) g hg hr_pos hc_zero hr_half hball hdisj
      hU_open hU_disj hU_img

/-
**Cantor scheme construction.** If `g : X → Y` is continuous and NLC from a
nonempty metrizable space to a T₂ space, then there exists a countable nonempty
subset `S ⊆ X` such that:
- `S` has no isolated points (in the subspace topology)
- The restriction of `g` to `S` is a topological embedding into `Y`
-/
lemma nlc_countable_embedding {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) [Nonempty X] :
    ∃ (S : Set X), S.Countable ∧ S.Nonempty ∧
      (∀ x : S, ¬ IsOpen ({x} : Set S)) ∧
      Topology.IsEmbedding (fun (x : S) => g x.val) := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := nlc_countable_embedding_concrete g hg hnlc
  refine ⟨Set.range σ, ?_, ?_, ?_, ?_⟩
  · -- `Countable CantorRat` is now in scope (from `ZeroDimensionalSpaces.CantorRat`), so the
    -- range is countable directly; the former manual support-counting argument is unnecessary.
    exact Set.countable_range σ
  · exact ⟨_, ⟨⟨fun _ => 0, ⟨0, fun _ _ => rfl⟩⟩, rfl⟩⟩
  · intro x hx
    -- Since CantorRat has no isolated points, the image of CantorRat under σ also has no isolated points.
    have h_no_isolated : ∀ x : CantorEventuallyZero, ¬IsOpen ({x} : Set CantorEventuallyZero) := by
      intro x hx
      have h_no_isolated : ∀ x : CantorEventuallyZero, ¬IsOpen ({x} : Set CantorEventuallyZero) := by
        intro x hx
        have h_seq : ∃ seq : ℕ → CantorEventuallyZero, Filter.Tendsto seq Filter.atTop (nhds x) ∧ ∀ n, seq n ≠ x := by
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, x.val n = 0 := by
            exact x.2
          refine ⟨fun n => ⟨fun i => if i = N + n + 1 then 1 else x.val i, ?_⟩, ?_, ?_⟩ <;> simp_all +decide
          use N + n + 2
          grind
          · rw [tendsto_subtype_rng]
            rw [tendsto_pi_nhds]
            intro n; by_cases hn : n = N + n + 1 <;> simp_all +decide [Nat.ne_of_lt]
            exact ⟨n + 1, by intros; linarith⟩
          · intro n hn; have := congr_arg (fun f => f.val (N + n + 1)) hn; simp +decide at this
            rw [hN _ (by linarith)] at this ; contradiction
        obtain ⟨seq, hseq₁, hseq₂⟩ := h_seq
        exact absurd (hseq₁.eventually (hx.mem_nhds rfl)) fun h => by obtain ⟨n, hn⟩ := h.exists; exact hseq₂ n hn
      exact h_no_isolated x hx
    obtain ⟨y, hy⟩ := x.2
    have h_preimage : IsOpen (σ ⁻¹' {↑x}) := by
      convert hx.preimage (show Continuous (fun z : CantorEventuallyZero => ⟨σ z, Set.mem_range_self z⟩) from hσ₁.continuous.subtype_mk _) using 1
      grind
    exact h_no_isolated y (by simpa [show σ ⁻¹' { (x : X) } = { y } from Set.eq_singleton_iff_unique_mem.mpr ⟨by aesop, fun z hz => hσ₁.injective <| by aesop⟩] using h_preimage)
  · rw [Topology.isEmbedding_iff] at *
    constructor
    · rw [Topology.isInducing_iff_nhds] at *
      simp +decide
      intro a x hx; specialize hσ₂; have := hσ₂.1 x; simp_all +decide [Filter.ext_iff]
      intro s; specialize this (σ ⁻¹' (Subtype.val '' s)) ; simp_all +decide [Set.subset_def]
      rw [mem_nhds_subtype]
      grind
    · intro x y hxy
      rcases x with ⟨x, ⟨x', rfl⟩⟩ ; rcases y with ⟨y, ⟨y', rfl⟩⟩ ; have := hσ₂.2 (by aesop : g (σ x') = g (σ y')) ; aesop


/-- If `f` is continuous from a metrizable to a Hausdorff space and not scattered, then
`id_CantorRat` topologically embeds in `f`.  This uses the Cantor scheme
`nlc_countable_embedding_concrete` directly (which already lands in `CantorRat`), so it needs
no Sierpiński input. -/
theorem nonscattered_embeds_idCantorRat {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hns : ¬ ScatteredFun f) :
    ∃ (σ : CantorRat → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (f ∘ σ) := by
  rw [not_scattered_iff_exists_nlc] at hns
  obtain ⟨A, hA, hnlc⟩ := hns
  haveI : Nonempty A := hA.to_subtype
  have hcont : Continuous (f ∘ Subtype.val : A → Y) := hf.comp continuous_subtype_val
  obtain ⟨σ, hσ, hgσ⟩ := nlc_countable_embedding_concrete (f ∘ Subtype.val) hcont hnlc
  exact ⟨Subtype.val ∘ σ,
    Topology.IsEmbedding.subtypeVal.comp hσ,
    hgσ⟩


/-! ### A non-empty closed nowhere-locally-constant set (route to the Cantor embedding)

For the Cantor-space embedding we need to run the Cantor scheme inside a *complete*
carrier.  The perfect kernel `K = perfectKernelCB f` is closed (hence a complete Polish
subspace), non-empty when `f` is not scattered, and `f|_K` is nowhere locally constant. -/

section PerfectKernelNLC

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace Y] in
/-- Stability of the CB derivative propagates upward: if `CBLevel f α = CBLevel f (α+1)`
then `CBLevel f β = CBLevel f α` for every `β ≥ α`. -/
lemma CBLevel_eq_of_stable (f : X → Y) {α : Ordinal}
    (hstab : CBLevel f α = CBLevel f (Order.succ α)) :
    ∀ β, α ≤ β → CBLevel f β = CBLevel f α := by
  intro β
  induction' β using Ordinal.limitRecOn with γ ih lam hlam ih
  · intro hβ; rw [nonpos_iff_eq_zero.mp hβ]
  · intro hβ
    rcases eq_or_lt_of_le hβ with h | h
    · rw [← h]
    · have hαγ : α ≤ γ := Order.lt_succ_iff.mp h
      rw [CBLevel_succ', ih hαγ, ← CBLevel_succ' f α, ← hstab]
  · intro hβ
    rcases eq_or_lt_of_le hβ with h | h
    · rw [← h]
    · rw [CBLevel_limit f lam hlam]
      apply le_antisymm
      · exact Set.iInter₂_subset α h
      · refine Set.subset_iInter₂ fun γ hγ => ?_
        rcases le_total α γ with hαγ | hγα
        · exact (ih γ hγ hαγ).ge
        · exact CBLevel_antitone f hγα

omit [TopologicalSpace Y] in
/-- When `X` is `Small.{0}`, the CB derivative stabilises at some countable stage. -/
lemma exists_CBLevel_stable (f : X → Y) :
    ∃ α : Ordinal, CBLevel f α = CBLevel f (Order.succ α) := by
  by_contra h
  push_neg at h
  obtain ⟨g, hg⟩ := CBLevel_strictAnti_of_ne f h
  exact not_injective_of_ordinal g hg

omit [TopologicalSpace Y] in
/-- The perfect kernel equals a stable CB-level. -/
lemma perfectKernelCB_eq_stable (f : X → Y) :
    ∃ α : Ordinal, perfectKernelCB f = CBLevel f α ∧
      CBLevel f α = CBLevel f (Order.succ α) := by
  obtain ⟨α, hα⟩ := exists_CBLevel_stable f
  refine ⟨α, le_antisymm (Set.iInter_subset _ α) ?_, hα⟩
  refine Set.subset_iInter fun β => ?_
  rcases le_total α β with h | h
  · exact (CBLevel_eq_of_stable f hα β h).ge
  · exact CBLevel_antitone f h

omit [TopologicalSpace Y] in
/-- The perfect kernel has no `f`-isolated points. -/
lemma isolatedLocus_perfectKernelCB_empty (f : X → Y) :
    isolatedLocus f (perfectKernelCB f) = ∅ := by
  obtain ⟨α, hK, hα⟩ := perfectKernelCB_eq_stable f
  rw [hK]
  have hdiff : CBLevel f α \ isolatedLocus f (CBLevel f α) = CBLevel f α := by
    rw [← CBLevel_succ' f α]; exact hα.symm
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxK : x ∈ CBLevel f α := hx.1
  rw [← hdiff] at hxK
  exact hxK.2 hx

omit [TopologicalSpace Y] in
/-- If `f` has no isolated points on `S`, then `f|_S` is nowhere locally constant. -/
lemma nlc_of_isolatedLocus_empty (f : X → Y) {S : Set X}
    (h : isolatedLocus f S = ∅) :
    NowhereLocallyConstant (f ∘ (Subtype.val : S → X)) := by
  intro U hU hUne
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x, hxS⟩, hxU⟩ := hUne
  rw [isOpen_induced_iff] at hU
  obtain ⟨V, hV, rfl⟩ := hU
  have hxin : x ∈ isolatedLocus f S := by
    refine ⟨hxS, V, hV, hxU, ?_⟩
    intro y hyVS
    have := hcon ⟨y, hyVS.2⟩ hyVS.1 ⟨x, hxS⟩ hxU
    simpa using this
  exact Set.notMem_empty x (h ▸ hxin)

/-- **Non-scattered ⟹ a non-empty closed nowhere-locally-constant restriction.**
The witness is the perfect kernel `perfectKernelCB f`. -/
lemma exists_closed_nonempty_nlc (f : X → Y) (hns : ¬ ScatteredFun f) :
    ∃ K : Set X, IsClosed K ∧ K.Nonempty ∧
      NowhereLocallyConstant (f ∘ (Subtype.val : K → X)) := by
  refine ⟨perfectKernelCB f, isClosed_iInter (fun α => CBLevel_isClosed f α), ?_, ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    exact fun h => hns (scattered_of_empty_perfectKernel f h)
  · exact nlc_of_isolatedLocus_empty f (isolatedLocus_perfectKernelCB_empty f)

end PerfectKernelNLC

/-! ### Full Cantor-space embedding from a scheme in a complete carrier

These mirror the `cantor_sigma_*` lemmas but use the *full* Cantor space `2^ℕ` instead of
its eventually-zero (≅ ℚ) part.  The branch map `σ(z) = limₙ c(z|ₙ)` exists because the
carrier `Z` is complete and the radii shrink geometrically.  All facts live in the complete
`Z`, so disjointness/openness apply to the limit points; the embedding conclusions then come
for free from compactness of `2^ℕ`. -/

section CantorFullScheme

/-- **Step 5 (assembly).** A continuous nowhere-locally-constant map from a *complete*
metric space embeds `2^ℕ` (both `σ` and `g ∘ σ`). -/
lemma nlc_cantor_embedding_concrete {Z Y : Type*}
    [MetricSpace Z] [CompleteSpace Z] [Nonempty Z]
    [TopologicalSpace Y] [T2Space Y]
    (g : Z → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) :
    ∃ (σ : CantorSpace → Z), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by
  obtain ⟨x₀⟩ := ‹Nonempty Z›
  obtain ⟨c, r, U, _, hr_pos, _hc_zero, hr_half, hball, hdisj, _hU_open, hU_disj, hU_img⟩ :=
    cantor_scheme_exists g hg hnlc x₀
  exact ⟨cantorSigmaFull c,
    cantorSigmaFull_isEmbedding hr_pos hr_half hball hdisj,
    g_cantorSigmaFull_isEmbedding (U := U) g hg hr_pos hr_half hball hU_disj hU_img⟩

end CantorFullScheme

/-- **Cantor-space strengthening.** For `X` Polish (complete), a non-scattered continuous
`f : X → Y` (into a Hausdorff space) admits a topological embedding `σ : 2^ℕ → X` with
`f ∘ σ` also an embedding — i.e. `id_{2^ℕ} ⊑ f`.  This upgrades `nonscattered_embeds_idCantorRat`
from `ℚ` (the eventually-zero branches) to the full Cantor space, using completeness to
take branch limits.

ROADMAP / what's still needed (this is *not* a black-box corollary of
`nonscattered_embeds_idCantorRat`):

The existing ℚ-embedding is built by `nlc_countable_embedding_concrete`, which runs the
Cantor scheme (`cantor_scheme_exists`) on the *subspace* `A` (an arbitrary non-empty set
on which `f` is nowhere locally constant), under `A`'s own `metrizableSpaceMetric`.  Two
facts block a direct extension to `2^ℕ`:
  1. `A` need not be complete, so the branch limits `σ(z) = limₙ c(z|ₙ)` need not exist in
     `A`; and even taken in `X`, they land in `closure A`, possibly outside `A`.
  2. The scheme only exposes closed-ball **disjointness inside `A`**
     (`Metric.closedBall` in `A`), which does *not* lift to disjointness of the ambient
     `X`-balls — so injectivity of the extended map cannot be recovered from the existing
     data.  (The underlying gap `ε' < dist x x' / 3` in `splitting_lemma_nlc` *is* metric
     and would lift, but it is not surfaced by `cantor_scheme_exists`.)

The clean fix is to run the scheme inside a **complete** carrier where the branch limits
stay and disjointness is meaningful for the limit points:
  • take `K := perfectKernelCB f` (closed in `X`, hence a complete Polish subspace) on
    which `f` is nowhere locally constant, OR re-run `cantor_scheme_exists` using `X`'s
    Polish (complete) metric with centres kept in the nlc-set;
  • define `σ z := limₙ (c (PiNat.res z n))` (Cauchy since `r(z|ₙ) ≤ r[]/2ⁿ`, complete);
  • `σ` continuous (uniform modulus `dist ≤ 2·r(z|ₙ)`, cf. `cantor_sigma_continuous`),
    `σ` injective (scheme disjointness, now valid for limit points), and `f ∘ σ` injective
    (image separation `g_sigma_in_U`, valid since `σ z` lies in the *open* parent ball);
  • conclude both are embeddings *for free* from compactness of `2^ℕ`: an injective
    continuous map from a compact space to a `T2` space is a closed embedding. -/
theorem nonscattered_embeds_idCantor {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hns : ¬ ScatteredFun f) :
    ∃ (σ : CantorSpace → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (f ∘ σ) := by
  -- run the scheme inside the complete carrier `K = perfectKernelCB f`
  obtain ⟨K, hK_closed, hK_ne, hnlc⟩ := exists_closed_nonempty_nlc f hns
  haveI : Nonempty K := hK_ne.to_subtype
  haveI : PolishSpace K := hK_closed.polishSpace
  letI := upgradeIsCompletelyMetrizable K
  have hg : Continuous (f ∘ (Subtype.val : K → X)) := hf.comp continuous_subtype_val
  obtain ⟨σ, hσ, hgσ⟩ := nlc_cantor_embedding_concrete (f ∘ Subtype.val) hg hnlc
  exact ⟨Subtype.val ∘ σ,
    hK_closed.isClosedEmbedding_subtypeVal.isEmbedding.comp hσ,
    hgσ⟩

end NonScatteredTheorem
