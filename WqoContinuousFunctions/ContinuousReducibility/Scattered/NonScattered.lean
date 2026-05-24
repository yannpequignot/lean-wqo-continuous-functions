import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Non-Scattered Embedding Theorem

If `f : X → Y` is continuous from a metrizable space to a Hausdorff space and `f` is
not scattered, then `id_ℚ` continuously reduces to `f`.

## Main results

* `nonscattered_embeds_idQ` — Theorem 2.5: non-scattered implies ℚ-embedding
* `nlc_to_rat_embedding` — Key helper: NLC implies ℚ-embedding
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

/-- **Sierpiński’s Theorem.** Every nonempty countable metrizable space without
isolated points is homeomorphic to ℚ. -/
theorem sierpinski_rat_homeomorph {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [Countable X] [Nonempty X]
    (hni : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    Nonempty (X ≃ₜ ℚ) := by
  sorry



-- 1. Define the base Cantor Space (infinite binary sequences)
abbrev CantorSpace := ℕ → Fin 2

-- 2. Define the property of being eventually zero
def IsEventuallyZero (x : CantorSpace) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, x n = 0

-- 3. Define the Subspace
def CantorEventuallyZero : Type :=
  { x : CantorSpace // IsEventuallyZero x }

-- 4. Define your custom shorthand notation
notation "CantorRat" => CantorEventuallyZero

instance : TopologicalSpace CantorEventuallyZero := instTopologicalSpaceSubtype

/-- Helper: extract the canonical prefix of an eventually-zero sequence. -/
noncomputable def cantorRatPrefix (x : CantorEventuallyZero) : List (Fin 2) := by
  classical
  exact PiNat.res x.val (Nat.find x.prop)

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

/--
Centers are nested: any descendant's center lies in the ancestor's closed ball.
-/
lemma scheme_center_in_closedBall {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l)) :
    ∀ (l₁ l₂ : List (Fin 2)), c (l₁ ++ l₂) ∈ Metric.closedBall (c l₂) (r l₂) := by
  intro l₁ l₂
  induction' l₁ with a l₁ ih
  · exact Metric.mem_closedBall_self (le_of_lt (hr_pos _))
  · have h_center : ∀ l₁ l₂, Metric.closedBall (c (l₁ ++ l₂)) (r (l₁ ++ l₂)) ⊆ Metric.closedBall (c l₂) (r l₂) := by
      intro l₁ l₂; induction' l₁ with a l₁ ih generalizing l₂; aesop
      exact Set.Subset.trans (hball _ _) (Metric.ball_subset_closedBall.trans (ih _))
    exact h_center (a :: l₁) l₂ (Metric.mem_closedBall_self (hr_pos _ |> le_of_lt))

/--
Radius bound: the radius at depth n is at most r([]) / 2^n.
-/
lemma scheme_radius_bound {r : List (Fin 2) → ℝ}
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2) :
    ∀ (l : List (Fin 2)), r l ≤ r [] / 2 ^ l.length := by
  intro l
  induction' l with l ih
  · norm_num
  · simpa only [pow_succ', div_div, List.length_cons] using le_trans (hr_half _ _) (by ring_nf at *; linarith)

/--
Two list prefixes (in Cantor scheme convention) that diverge give centers
in disjoint closed balls. This implies injectivity of the center map.
-/
lemma scheme_disjoint_of_ne {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l))))
    {l₁ l₂ : List (Fin 2)} (hne : l₁ ≠ l₂) (hlen : l₁.length = l₂.length) :
    c l₁ ≠ c l₂ := by
  -- By induction on the length of the lists, we can show that for any two different lists of the same length, their corresponding closed balls are disjoint.
  have h_ind : ∀ n : ℕ, ∀ (l₁ l₂ : List (Fin 2)), l₁.length = n → l₂.length = n → l₁ ≠ l₂ → Disjoint (Metric.closedBall (c l₁) (r l₁)) (Metric.closedBall (c l₂) (r l₂)) := by
    intro n
    induction' n with n ih
    · aesop
    · intro l₁ l₂ hl₁ hl₂ hne
      obtain ⟨a₁, l₁', rfl⟩ : ∃ a₁ l₁', l₁ = a₁ :: l₁' := by
        exact List.exists_cons_of_ne_nil (by rintro rfl; contradiction)
      obtain ⟨a₂, l₂', rfl⟩ : ∃ a₂ l₂', l₂ = a₂ :: l₂' := by
        exact List.exists_cons_of_ne_nil (by rintro rfl; contradiction)
      by_cases h : l₁' = l₂' <;> simp_all +decide [Set.disjoint_left]
      · fin_cases a₁ <;> fin_cases a₂ <;> simp_all +decide
        intro a ha; specialize hdisj l₂'; contrapose! hdisj; aesop
      · intro x hx; specialize ih l₁' l₂' hl₁ hl₂ h; fin_cases a₁ <;> fin_cases a₂ <;> simp_all +decide
        · contrapose! ih
          exact ⟨x, hball l₁' |>.1 hx |> fun h => by simpa using h.le, hball l₂' |>.1 ih |> fun h => by simpa using h.le⟩
        · contrapose! ih
          exact ⟨x, hball _ |>.1 hx |> Metric.mem_ball.mp |> le_of_lt, hball _ |>.2 ih |> Metric.mem_ball.mp |> le_of_lt⟩
        · contrapose! ih
          exact ⟨x, hball _ |>.2 hx |> fun h => by simpa using h.le, hball _ |>.1 ih |> fun h => by simpa using h.le⟩
        · contrapose! ih
          exact ⟨x, hball _ |>.2 hx |> fun h => by simpa using h.le, hball _ |>.2 ih |> fun h => by simpa using h.le⟩
  exact fun h => Set.disjoint_left.mp (h_ind _ _ _ hlen rfl hne) (Metric.mem_closedBall_self (le_of_lt (hr_pos _))) (h.symm ▸ Metric.mem_closedBall_self (le_of_lt (hr_pos _)))

/--
Prepending zeros to a list doesn't change the center.
-/
lemma scheme_center_replicate_zero {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X}
    (hc_zero : ∀ l, c (0 :: l) = c l) :
    ∀ (n : ℕ) (l : List (Fin 2)), c (List.replicate n 0 ++ l) = c l := by
  intro n l; induction' n with n ih generalizing l <;> simp_all +decide [List.replicate]

/--
cantorRatPrefix has length Nat.find x.prop.
-/
lemma cantorRatPrefix_length (x : CantorEventuallyZero) :
    (cantorRatPrefix x).length = @Nat.find _ (Classical.decPred _) x.prop := by
  convert PiNat.res_length x.val (Nat.find x.prop)

/--
For n ≥ Nat.find, x.val n = 0.
-/
lemma cantorRat_zero_beyond (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) : x.val n = 0 := by
  grind

/--
Extending PiNat.res beyond the prefix length just prepends zeros.
-/
lemma res_extends_prefix (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) :
    PiNat.res x.val n = List.replicate (n - @Nat.find _ (Classical.decPred _) x.prop) 0 ++ cantorRatPrefix x := by
  induction' n with n ih
  · unfold cantorRatPrefix
    grind +suggestions
  · by_cases h : n ≥ Nat.find x.prop
    · rw [Nat.succ_sub h, PiNat.res]
      grind
    · cases hn.eq_or_lt <;> simp_all +decide [Nat.sub_eq_zero_of_le, PiNat.res]
      · unfold cantorRatPrefix
        simp +decide [*]
      · grind

/--
The center at PiNat.res x.val n equals the center at cantorRatPrefix x for n ≥ prefix length.
-/
lemma center_of_extended_res {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} (hc_zero : ∀ l, c (0 :: l) = c l)
    (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) :
    c (PiNat.res x.val n) = c (cantorRatPrefix x) := by
  convert scheme_center_replicate_zero hc_zero (n - Nat.find x.prop) (cantorRatPrefix x) using 1
  rw [res_extends_prefix x n hn]

/--
The σ map is injective: different CantorRat elements give different centers.
-/
lemma cantor_sigma_injective {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Function.Injective (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  intro x y hxy
  have h_prefix_eq : PiNat.res x.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length) = PiNat.res y.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length) := by
    have h_prefix_eq : c (PiNat.res x.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) = c (PiNat.res y.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) := by
      convert hxy using 1
      · apply center_of_extended_res hc_zero x (max (cantorRatPrefix x).length (cantorRatPrefix y).length)
        exact le_max_of_le_left (by rw [cantorRatPrefix_length])
      · apply center_of_extended_res hc_zero y (max (cantorRatPrefix x).length (cantorRatPrefix y).length) (by
        exact le_max_of_le_right (by rw [cantorRatPrefix_length]))
    have := @scheme_disjoint_of_ne X _ c r hr_pos hball hdisj (PiNat.res x.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) (PiNat.res y.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) ; simp_all +decide
  refine Subtype.ext ?_
  grind +suggestions

/--
σ(x) is always in the closed ball at any truncation level n.
-/
lemma sigma_in_closedBall_res {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (x : CantorEventuallyZero) (n : ℕ) :
    c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
  by_cases h : n ≤ Nat.find x.prop
  · -- Since cantorRatPrefix x is the prefix of x up to the point where it becomes zero, and n ≤ Nat.find x.prop, we can write cantorRatPrefix x as l₁ ++ PiNat.res x.val n for some l₁.
    obtain ⟨l₁, hl₁⟩ : ∃ l₁ : List (Fin 2), cantorRatPrefix x = l₁ ++ PiNat.res x.val n := by
      have h_decomp : ∀ m n : ℕ, m ≤ n → ∃ l₁ : List (Fin 2), PiNat.res x.val n = l₁ ++ PiNat.res x.val m := by
        intro m n hmn
        induction' hmn with n hn ih
        · exact ⟨[ ], rfl⟩
        · obtain ⟨l₁, hl₁⟩ := ih; use x.val n :: l₁; simp +decide [hl₁]
      exact h_decomp _ _ h
    convert scheme_center_in_closedBall hr_pos hball l₁ (PiNat.res x.val n) using 1
    rw [hl₁]
  · have h_center_eq : c (PiNat.res x.val n) = c (cantorRatPrefix x) := by
      apply center_of_extended_res hc_zero x n (le_of_not_ge h)
    simp +decide [h_center_eq]
    exact le_of_lt (hr_pos _)

set_option maxHeartbeats 8000000 in
/--
The σ map is continuous from CantorRat to X.
-/
lemma cantor_sigma_continuous {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l)) :
    Continuous (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  refine Metric.tendsto_nhds.mpr ?_
  intro ε εpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * r (PiNat.res x.val n) < ε := by
    -- Since $r(PiNat.res x.val n) \leq r([]) / 2^n$, we can choose $n$ such that $2 * r([]) / 2^n < \epsilon$.
    have h_bound : ∃ n : ℕ, 2 * r [] / 2 ^ n < ε := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) |> fun h => h.eventually (gt_mem_nhds εpos) |> fun h => h.exists
    obtain ⟨n, hn⟩ := h_bound
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    convert mul_le_mul_of_nonneg_left (scheme_radius_bound hr_half (PiNat.res x.val n)) zero_le_two using 1 ; ring_nf
    simp +decide
  have h_open : IsOpen {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} := by
    have h_open : IsOpen (PiNat.cylinder x.val n) :=
      PiNat.isOpen_cylinder (E := fun _ => Fin 2) x.val n
    convert h_open.preimage _ using 1
    rotate_left
    use fun y => y.val
    · exact continuous_subtype_val
    · -- Goal: {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} =
      --       Subtype.val ⁻¹' PiNat.cylinder x.val n
      ext y; simp [PiNat.cylinder_eq_res]
  have h_cont : ∀ y : CantorEventuallyZero, PiNat.res y.val n = PiNat.res x.val n → dist (c (cantorRatPrefix y)) (c (cantorRatPrefix x)) < ε := by
    intro y hy
    have h_dist : dist (c (cantorRatPrefix y)) (c (cantorRatPrefix x)) ≤ 2 * r (PiNat.res x.val n) := by
      have h_dist : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) ∧ c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
        exact ⟨by simpa only [hy] using sigma_in_closedBall_res hr_pos hc_zero hball y n, by simpa only [hy] using sigma_in_closedBall_res hr_pos hc_zero hball x n⟩
      exact le_trans (dist_triangle_right _ _ _) (by linarith [Metric.mem_closedBall.mp h_dist.1, Metric.mem_closedBall.mp h_dist.2])
    linarith [h_dist]
  exact Filter.mem_of_superset (IsOpen.mem_nhds h_open (by
  rfl)) (by
  exact fun y hy => h_cont y hy)

set_option maxHeartbeats 8000000 in
/--
The embedding property of σ : CantorRat → X.
Given a Cantor scheme with the standard properties, the map
σ(x) = c(cantorRatPrefix x) is a topological embedding.
-/
lemma cantor_sigma_isEmbedding {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (g : X → Y) (_hg : Continuous g) (_hnlc : NowhereLocallyConstant g)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Topology.IsEmbedding (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  have h_embedding : Function.Injective (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) ∧ Continuous (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
    exact ⟨cantor_sigma_injective hr_pos hc_zero hball hdisj, cantor_sigma_continuous hr_pos hc_zero hr_half hball⟩
  have h_embedding : ∀ x : CantorEventuallyZero, ∀ n : ℕ, ∃ V ∈ nhds (c (cantorRatPrefix x)), ∀ y : CantorEventuallyZero, c (cantorRatPrefix y) ∈ V → PiNat.res y.val n = PiNat.res x.val n := by
    intro x n
    use Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n))
    refine ⟨Metric.isOpen_ball.mem_nhds ?_, ?_⟩
    · by_cases hN : @Nat.find _ (Classical.decPred _) x.prop ≤ n
      · have h_sigma_in_closedBall_res : c (cantorRatPrefix x) = c (PiNat.res x.val n) := by
          apply Eq.symm; exact (by
            have := center_of_extended_res hc_zero x n hN
            exact this
          )
        aesop
      · have h_closedBall_subset_ball : Metric.closedBall (c (cantorRatPrefix x)) (r (cantorRatPrefix x)) ⊆ Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
          have h_closedBall_subset_ball : ∀ k ≥ n + 1, Metric.closedBall (c (PiNat.res x.val k)) (r (PiNat.res x.val k)) ⊆ Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
            intro k hk
            induction' hk with k hk ih
            · convert hball (PiNat.res x.val n) (x.val n) using 1
            · refine Set.Subset.trans ?_ ih
              convert hball (PiNat.res x.val k) (x.val k) |> Set.Subset.trans <| Metric.ball_subset_closedBall using 1
          convert h_closedBall_subset_ball (Nat.find x.prop) (by linarith) using 1
        exact h_closedBall_subset_ball (Metric.mem_closedBall_self (le_of_lt (hr_pos _)))
    · intro y hy
      by_contra h_neq
      obtain ⟨k, hk⟩ : ∃ k < n, PiNat.res y.val (k + 1) ≠ PiNat.res x.val (k + 1) ∧ ∀ j < k, PiNat.res y.val (j + 1) = PiNat.res x.val (j + 1) := by
        have h_exists_k : ∃ k < n, PiNat.res y.val (k + 1) ≠ PiNat.res x.val (k + 1) := by
          exact ⟨n - 1, Nat.pred_lt (by aesop), by cases n <;> aesop⟩
        generalize_proofs at *; (
        exact ⟨Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨by linarith [Nat.find_spec h_exists_k |>.1], h⟩⟩)
      generalize_proofs at *; (
      -- Since $c(cantorRatPrefix y) \in Metric.ball(c(res x n), r(res x n))$, we have $c(cantorRatPrefix y) \in Metric.closedBall(c(res x (k+1)), r(res x (k+1)))$.
      have h_closedBall : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
        have h_closedBall : Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) ⊆ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
          have h_closedBall : ∀ m ≥ k + 1, Metric.closedBall (c (PiNat.res x.val m)) (r (PiNat.res x.val m)) ⊆ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
            intro m hm
            induction' hm with m hm ih
            generalize_proofs at *; (
            exact Set.Subset.rfl)
            refine Set.Subset.trans ?_ ih
            generalize_proofs at *; (
            have := hball (PiNat.res x.val m) (x.val m) ; simp_all +decide [PiNat.res]
            exact Set.Subset.trans this (Metric.ball_subset_closedBall))
          generalize_proofs at *; (
          exact h_closedBall n (by linarith))
        generalize_proofs at *; (
        exact h_closedBall <| Metric.ball_subset_closedBall hy)
      generalize_proofs at *; (
      have h_closedBall_y : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res y.val (k + 1))) (r (PiNat.res y.val (k + 1))) := by
        apply sigma_in_closedBall_res
        · exact hr_pos
        · exact hc_zero
        · exact hball
      generalize_proofs at *; (
      have h_disjoint : Disjoint (Metric.closedBall (c (PiNat.res y.val (k + 1))) (r (PiNat.res y.val (k + 1)))) (Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1)))) := by
        have h_disjoint : ∀ l : List (Fin 2), ∀ a b : Fin 2, a ≠ b → Disjoint (Metric.closedBall (c (a :: l)) (r (a :: l))) (Metric.closedBall (c (b :: l)) (r (b :: l))) := by
          intro l a b hab; fin_cases a <;> fin_cases b <;> simp_all +decide
          exact Disjoint.symm (hdisj l)
        generalize_proofs at *; (
        convert h_disjoint (PiNat.res (y.val) k) (y.val k) (x.val k) _ using 1 <;> simp_all +decide [PiNat.res]
        · grind +suggestions
        · grind +suggestions)
      generalize_proofs at *; (
      exact h_disjoint.le_bot ⟨h_closedBall_y, h_closedBall⟩))))
  have h_embedding : ∀ x : CantorEventuallyZero, ∀ U ∈ nhds x, ∃ V ∈ nhds (c (cantorRatPrefix x)), ∀ y : CantorEventuallyZero, c (cantorRatPrefix y) ∈ V → y ∈ U := by
    intro x U hU
    obtain ⟨n, hn⟩ : ∃ n : ℕ, {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} ⊆ U := by
      rw [mem_nhds_iff] at hU
      obtain ⟨t, ht₁, ht₂, ht₃⟩ := hU
      rcases ht₂ with ⟨s, hs₁, rfl⟩
      rw [isOpen_pi_iff] at hs₁
      obtain ⟨I, u, hu₁, hu₂⟩ := hs₁ _ ht₃
      use I.sup id + 1
      intro y hy
      refine ht₁ ?_
      -- Goal: ↑y ∈ s. Since hu₂ : (↑I).pi u ⊆ s, it suffices to show ↑y ∈ (↑I).pi u.
      -- For each i ∈ I, i ≤ I.sup id, so i < I.sup id + 1. From hy (res equality),
      -- y.val i = x.val i. Since hu₁ gives x.val i ∈ u i, we get y.val i ∈ u i.
      apply hu₂
      simp only [Set.mem_pi, Finset.mem_coe]
      intro i hi
      have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
      have heq : y.val i = x.val i := PiNat.res_eq_res.mp hy (Nat.lt_succ_of_le hle)
      rw [heq]
      exact (hu₁ i hi).2
    exact Exists.elim (h_embedding x n) fun V hV => ⟨V, hV.1, fun y hy => hn (hV.2 y hy)⟩
  refine ⟨?_, ?_⟩
  · refine Topology.isInducing_iff_nhds.2 fun x => ?_
    refine le_antisymm ?_ ?_
    · exact Filter.tendsto_iff_comap.mp (‹ (Injective fun x => c (cantorRatPrefix x)) ∧ Continuous fun x => c (cantorRatPrefix x) ›.2.tendsto x)
    · intro U hU
      rcases h_embedding x U hU with ⟨V, hV, hV'⟩ ; exact ⟨V, hV, fun y hy => hV' y hy⟩
  · exact And.left ‹_›

/--
g(σ(x)) is in the open set U at level n+1 when σ(x) is in the corresponding ball.
-/
lemma g_sigma_in_U {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    {U : List (Fin 2) → Set Y} (g : X → Y)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l))
    (x : CantorEventuallyZero) (n : ℕ) :
    g (c (cantorRatPrefix x)) ∈ U (PiNat.res x.val (n + 1)) := by
  by_cases h : @Nat.find _ (Classical.decPred _) x.prop ≤ n + 1
  · have := center_of_extended_res hc_zero x (n + 1) h
    rw [← this]
    convert hU_img (PiNat.res x.val n) (x.val n) (Set.mem_image_of_mem _ _) using 1
    convert Metric.mem_ball_self (hr_pos _) using 1
  · have h_closed_ball : c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val (n + 1 + 1))) (r (PiNat.res x.val (n + 1 + 1))) := by
      apply sigma_in_closedBall_res
      · exact hr_pos
      · exact hc_zero
      · exact hball
    grind +suggestions

set_option maxHeartbeats 4000000 in
/-- The embedding property of `g ∘ σ : CantorRat → Y`. -/
lemma cantor_g_sigma_isEmbedding {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    {U : List (Fin 2) → Set Y}
    (g : X → Y) (hg : Continuous g) (_hnlc : NowhereLocallyConstant g)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l))))
    (hU_open : ∀ l (a : Fin 2), IsOpen (U (a :: l)))
    (hU_disj : ∀ l, Disjoint (U (0 :: l)) (U (1 :: l)))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) :
    Topology.IsEmbedding (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
  have h_subspace : Continuous (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
    exact hg.comp (cantor_sigma_continuous hr_pos hc_zero hr_half hball)
  have h_injective : Function.Injective (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
    intro x y hxy
    by_contra hneq
    obtain ⟨k, hk⟩ : ∃ k, (PiNat.res x.val k) = (PiNat.res y.val k) ∧ x.val k ≠ y.val k := by
      obtain ⟨k, hk⟩ : ∃ k, (PiNat.res x.val k) ≠ (PiNat.res y.val k) ∧ ∀ j < k, (PiNat.res x.val j) = (PiNat.res y.val j) := by
        have h_exists_k : ∃ k, (PiNat.res x.val k) ≠ (PiNat.res y.val k) := by
          contrapose! hneq
          generalize_proofs at *
          exact Subtype.ext (funext fun n => by have := hneq (n + 1) ; have := hneq n; simp_all +decide [PiNat.res])
        generalize_proofs at *
        exact ⟨Nat.find h_exists_k, Nat.find_spec h_exists_k, fun j hj => by simpa using Nat.find_min h_exists_k hj⟩
      generalize_proofs at *
      rcases k <;> simp_all +decide [PiNat.res]
      grind
    generalize_proofs at *
    have h_contradiction : g (c (cantorRatPrefix x)) ∈ U (PiNat.res x.val (k + 1)) ∧ g (c (cantorRatPrefix y)) ∈ U (PiNat.res y.val (k + 1)) := by
      exact ⟨g_sigma_in_U g hr_pos hc_zero hball hU_img x k, g_sigma_in_U g hr_pos hc_zero hball hU_img y k⟩
    generalize_proofs at *; exact (by
    cases Fin.exists_fin_two.mp ⟨x.val k, rfl⟩ <;> cases Fin.exists_fin_two.mp ⟨y.val k, rfl⟩ <;> simp_all +decide [PiNat.res]
    · exact Set.disjoint_left.mp (hU_disj _) h_contradiction.1 h_contradiction.2
    · exact Set.disjoint_left.mp (hU_disj _) h_contradiction.2 h_contradiction.1)
  refine ⟨?_, ?_⟩
  · refine Topology.isInducing_iff_nhds.2 fun x => le_antisymm ?_ ?_
    · exact h_subspace.tendsto x |> fun h => h.le_comap
    · intro s hs
      -- Since $s$ is a neighborhood of $x$, there exists an $n$ such that the cylinder set $\{y \mid \text{res } y n = \text{res } x n\}$ is contained in $s$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} ⊆ s := by
        rw [mem_nhds_subtype] at hs
        rcases hs with ⟨u, hu, hs⟩
        rw [mem_nhds_iff] at hu
        rcases hu with ⟨t, ht₁, ht₂, ht₃⟩
        rw [isOpen_pi_iff] at ht₂
        obtain ⟨I, u, hu₁, hu₂⟩ := ht₂ _ ht₃
        use I.sup id + 1
        intro y hy
        refine hs (ht₁ (hu₂ ?_))
        -- Goal: ↑y ∈ (↑I).pi u. For each i ∈ I, i ≤ I.sup id < I.sup id + 1,
        -- so from hy (res equality) y.val i = x.val i, and hu₁ gives x.val i ∈ u i.
        simp only [Set.mem_pi, Finset.mem_coe]
        intro i hi
        have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
        have heq : y.val i = x.val i := PiNat.res_eq_res.mp hy (Nat.lt_succ_of_le hle)
        rw [heq]
        exact (hu₁ i hi).2
      refine ⟨⋂ k ∈ Finset.range n, U (PiNat.res x.val (k + 1)), ?_, ?_⟩
      · refine IsOpen.mem_nhds ?_ ?_
        · refine isOpen_biInter_finset fun k hk => ?_
          convert hU_open (PiNat.res x.val k) (x.val k) using 1
        · exact Set.mem_iInter₂.2 fun k hk => g_sigma_in_U g hr_pos hc_zero hball hU_img x k
      · intro y hy; contrapose! hy; simp_all +decide [Set.subset_def]
        -- Since $y \notin s$, there exists some $k < n$ such that $y.val k \neq x.val k$.
        obtain ⟨k, hk₁, hk₂⟩ : ∃ k < n, y.val k ≠ x.val k ∧ ∀ j < k, y.val j = x.val j := by
          have h_exists_k : ∃ k < n, y.val k ≠ x.val k := by
            grind +suggestions
          exact ⟨Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨by linarith [Nat.find_spec h_exists_k |>.1], h⟩⟩
        refine ⟨k, hk₁, ?_⟩
        have h_g_sigma_in_U : g (c (cantorRatPrefix y)) ∈ U (PiNat.res y.val (k + 1)) := by
          apply g_sigma_in_U
          exact hr_pos
          · exact hc_zero
          · intro l a; specialize hball l; fin_cases a <;> simp_all +decide [Metric.closedBall, Metric.ball]
          · intro l a; specialize hU_img l; fin_cases a <;> simp_all +decide [Set.image_subset_iff]
            · exact fun x hx => hU_img.1 x hx
            · exact fun x hx => hU_img.2 x <| by simpa using hx
        have h_g_sigma_in_U : PiNat.res y.val (k + 1) = y.val k :: PiNat.res x.val k := by
          grind +suggestions
        cases Fin.exists_fin_two.mp ⟨y.val k, rfl⟩ <;> cases Fin.exists_fin_two.mp ⟨x.val k, rfl⟩ <;> simp_all +decide [Set.disjoint_left]
        exact fun h => hU_disj _ h ‹_›
  · exact h_injective

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
  · exact cantor_sigma_isEmbedding g hg hnlc hr_pos hc_zero hr_half hball hdisj
  · exact cantor_g_sigma_isEmbedding (U := U) g hg hnlc hr_pos hc_zero hr_half hball hdisj
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
  · convert Set.countable_range σ
    have h_countable : Set.Countable (⋃ N : ℕ, {x : ℕ → Fin 2 | ∀ n ≥ N, x n = 0}) := by
      refine Set.countable_iUnion fun N => ?_
      refine Set.Countable.mono ?_ (Set.countable_range (fun x : Fin N → Fin 2 => fun n => if h : n < N then x ⟨n, h⟩ else 0))
      intro x hx; use fun n => x n; ext n; aesop
    exact h_countable.mono fun x hx => by aesop
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

/-- **Key helper for Theorem 2.5.** If `g : X → Y` is continuous from a nonempty
metrizable space to a T₂ space, and `g` is nowhere locally constant, then there exists
a topological embedding `σ : ℚ → X` such that `g ∘ σ` is also a topological embedding. -/
lemma nlc_to_rat_embedding {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocallyConstant g) [Nonempty X] :
    ∃ (σ : ℚ → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by
  obtain ⟨S, hcount, hne, hni, hemb_g⟩ := nlc_countable_embedding g hg hnlc
  haveI : Countable S := hcount.to_subtype
  haveI : Nonempty S := hne.to_subtype
  obtain ⟨h⟩ := sierpinski_rat_homeomorph hni
  exact ⟨Subtype.val ∘ h.symm,
    Topology.IsEmbedding.subtypeVal.comp h.symm.isEmbedding,
    hemb_g.comp h.symm.isEmbedding⟩

/-- **Theorem 2.5 (weakened formulation).** If `f` is continuous from a metrizable to a
Hausdorff space and not scattered, then there exists a topological embedding `σ : ℚ → X`
such that `f ∘ σ` is also a topological embedding (into `Y`). -/
theorem nonscattered_embeds_idQ {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hns : ¬ ScatteredFun f) :
    ∃ (σ : ℚ → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (f ∘ σ) := by
  rw [not_scattered_iff_exists_nlc] at hns
  obtain ⟨A, hA, hnlc⟩ := hns
  haveI : Nonempty A := hA.to_subtype
  have hcont : Continuous (f ∘ Subtype.val : A → Y) := hf.comp continuous_subtype_val
  obtain ⟨σ, hσ, hgσ⟩ := nlc_to_rat_embedding (f ∘ Subtype.val) hcont hnlc
  exact ⟨Subtype.val ∘ σ,
    Topology.IsEmbedding.subtypeVal.comp hσ,
    hgσ⟩

end NonScatteredTheorem
