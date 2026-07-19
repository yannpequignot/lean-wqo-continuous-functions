import WqoContinuousFunctions.PointedGluing.UpperBound.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Continuity of the backward map τ

This file proves continuity results for the backward map `τ` used in the
pointed gluing upper bound construction, including `ContinuousWithinAt`
at the zero stream and at block points.
-/

noncomputable section

/-- If a sequence in ℕ → ℕ converges to zeroStream and all terms are nonzero,
then firstNonzero of the terms tends to infinity. -/
lemma firstNonzero_tendsto_of_converge_zeroStream
    {z : ℕ → ℕ → ℕ} (hz_ne : ∀ n, z n ≠ zeroStream)
    (hz_conv : Filter.Tendsto z Filter.atTop (nhds zeroStream)) :
    Filter.Tendsto (fun n => firstNonzero (z n)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr ?_
  intro b
  have h_eventually_zero : ∀ᶠ n in Filter.atTop, ∀ k < b, z n k = 0 := by
    simp_all +decide [tendsto_pi_nhds]
    choose! a ha using hz_conv
    exact ⟨Finset.sup (Finset.range b) a, fun n hn k hk => ha k n (le_trans (Finset.le_sup (f := a) (Finset.mem_range.mpr hk)) hn)⟩
  filter_upwards [h_eventually_zero] with n hn
  unfold firstNonzero
  split_ifs <;> simp_all +decide
  exact False.elim <| hz_ne n <| funext ‹_›

lemma continuousWithinAt_tau_at_zeroStream
    {y : ℕ → ℕ} {τ : (ℕ → ℕ) → ℕ → ℕ}
    {R : Set (ℕ → ℕ)}
    (hτ_zero : τ zeroStream = y)
    {I : ℕ → Finset ℕ} (_hI_disj : ∀ m n, m ≠ n → Disjoint (I m) (I n))
    (hR_struct : ∀ z ∈ R, z ≠ zeroStream →
      ∃ j, firstNonzero z ∈ I j ∧ ∀ k, k < j → τ z k = y k) :
    ContinuousWithinAt τ R zeroStream := by
  refine tendsto_pi_nhds.mpr ?_
  intro k
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  rw [nhdsWithin, Filter.EventuallyEq, Filter.eventually_inf_principal]
  -- Let $M$ be a number such that for all $j < N$, $I(j)$ is contained in $\{0, 1, ..., M-1\}$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ j < k + 1, ∀ i ∈ I j, i < M := by
    exact ⟨Finset.sup (Finset.biUnion (Finset.range (k + 1)) I) id + 1, fun j hj i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hi⟩))⟩
  filter_upwards [(show { x : ℕ → ℕ | ∀ i < M, x i = 0 } ∈ 𝓝 zeroStream from by
                      rw [nhds_pi]
                      simp +decide only [nhds_discrete, Filter.mem_pi, Filter.mem_pure]
                      exact ⟨Finset.range M, Finset.finite_toSet _, fun _ => { 0 }, fun _ => by simp +decide [zeroStream], fun x hx i hi => by simpa using hx i (Finset.mem_range.mpr hi)⟩)] with x hx hxR
  by_cases hx_zero : x = zeroStream <;> simp_all +decide [firstNonzero]
  grind

/--
ContinuousWithinAt for a function τ at a non-zeroStream point z₀,
given that τ agrees with a ContinuousOn function on a neighborhood.
-/
lemma continuousWithinAt_tau_at_block
    {τ : (ℕ → ℕ) → ℕ → ℕ} {R : Set (ℕ → ℕ)}
    {z₀ : ℕ → ℕ} (hz₀ : z₀ ∈ R) (_hz₀_ne : z₀ ≠ zeroStream)
    (hlocal : ∃ (U : Set (ℕ → ℕ)), IsOpen U ∧ z₀ ∈ U ∧
      ∃ (g : (ℕ → ℕ) → ℕ → ℕ), ContinuousOn g (R ∩ U) ∧
        ∀ z ∈ R ∩ U, τ z = g z) :
    ContinuousWithinAt τ R z₀ := by
  obtain ⟨U, hU₁, hU₂, g, hg₁, hg₂⟩ := hlocal
  have h_cont : ContinuousWithinAt g (R ∩ U) z₀ := by
    exact hg₁ z₀ ⟨hz₀, hU₂⟩
  rw [ContinuousWithinAt] at *
  rw [← Filter.tendsto_congr']
  convert h_cont.mono_left _ using 1
  · rw [hg₂ z₀ ⟨hz₀, hU₂⟩]
  · simp +decide [nhdsWithin, Filter.mem_inf_principal]
    exact Filter.mem_of_superset (hU₁.mem_nhds hU₂) fun x hx hx' => hx
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU₁.mem_nhds hU₂)] with x hx₁ hx₂ using hg₂ x ⟨hx₁, hx₂⟩ ▸ rfl

/--
Weaker variant: only requires ContinuousWithinAt of g at z₀ (not full ContinuousOn).
-/
lemma continuousWithinAt_tau_at_block'
    {τ : (ℕ → ℕ) → ℕ → ℕ} {R : Set (ℕ → ℕ)}
    {z₀ : ℕ → ℕ} (hz₀ : z₀ ∈ R) (_hz₀_ne : z₀ ≠ zeroStream)
    (hlocal : ∃ (U : Set (ℕ → ℕ)), IsOpen U ∧ z₀ ∈ U ∧
      ∃ (g : (ℕ → ℕ) → ℕ → ℕ), ContinuousWithinAt g (R ∩ U) z₀ ∧
        ∀ z ∈ R ∩ U, τ z = g z) :
    ContinuousWithinAt τ R z₀ := by
  obtain ⟨U, hU₁, hU₂, g, hg₁, hg₂⟩ := hlocal
  rw [ContinuousWithinAt] at *
  rw [← Filter.tendsto_congr']
  convert hg₁.mono_left _ using 1
  · rw [hg₂ z₀ ⟨hz₀, hU₂⟩]
  · simp +decide [nhdsWithin, Filter.mem_inf_principal]
    exact Filter.mem_of_superset (hU₁.mem_nhds hU₂) fun x hx hx' => hx
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU₁.mem_nhds hU₂)] with x hx₁ hx₂ using hg₂ x ⟨hx₁, hx₂⟩ ▸ rfl

end
