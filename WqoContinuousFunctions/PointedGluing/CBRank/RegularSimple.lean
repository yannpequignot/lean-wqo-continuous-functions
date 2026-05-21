import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section
/-- **Proposition (CBrankofPgluingofregularsequence2simple).**
If `f ∈ 𝒞` is scattered of CB-rank `α + 1` and simple with distinguished point `y`,
then the sequence `(CB(Ray(f, y, n)))_n` is regular with supremum `α`.


The proof shows: by simplicity, `CB_α(f) ⊆ f⁻¹({y})`, so
`CB_α(Ray(f, y, i)) = ∅`, giving each `α_i ≤ α`. For regularity: if `∀ n > m`,
`α_n ≤ β < α`, then restricting `f` away from the first `m` rays gives
`CB(g) ≤ β + 1 ≤ α`, and the disjoint union decomposition contradicts
`CB(f) = α + 1`.

Note: `Continuous f` is required for the CB-level analysis of ray restrictions.
In the paper, all functions are in 𝒞 (continuous functions on the Baire space).

Error in manuscript: It is possible that $\alpha$ is limit
and $(\CB(\ray{f}{y,n}))=\alpha$ for only finitely many $n$,
in which case the conclusion fails. This proposition is really
about simple functions with double successors rank
The statement was updated accordingly-/
theorem CBrank_regular_simple
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (α : Ordinal.{0})
    (h_succ: ∃ γ, α = Order.succ γ) -- added α is successor
    (hcb_ne : (CBLevel f α).Nonempty)
    (hcb_empty : CBLevel f (Order.succ α) = ∅)
    (y : ℕ → ℕ) (hy : y ∈ B) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (ray_cb : ℕ → Ordinal.{0})
    (hray_cb : ∀ n, ray_cb n = CBRank
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)) :
    IsRegularOrdSeq ray_cb ∧ ⨆ n, ray_cb n = α := by
  have hray_le : ∀ n, ray_cb n ≤ α := by
    intro n; rw [hray_cb]; exact ray_cb_le_alpha f hf α y hy_simple n
  have hsup : ⨆ n, ray_cb n = α :=
    sup_ray_cb_eq_alpha f hfB hf hf_scat α hcb_ne y hy_simple ray_cb hray_cb hray_le
  refine ⟨?_, hsup⟩
  -- Regularity: cofinality argument
  -- First prove cofinality: ∀ β < α, ∀ m, ∃ n > m, ray_cb n > β
  have hcofinal : ∀ (β : Ordinal.{0}), β < α → ∀ (m : ℕ), ∃ n, m < n ∧ β < ray_cb n := by
    intro β hβ m
    by_contra h
    push_neg at h
    -- ∀ n > m, ray_cb n ≤ β
    have hbound : ∀ n, n > m → CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β := by
      intro n hn; rw [← hray_cb]; exact h n hn
    exact hcb_ne.ne_empty (regularity_contradiction f hfB hf hf_scat α y hy hy_simple m β hβ
      hbound (fun n => hray_cb n ▸ hray_le n))
  -- Derive regularity from cofinality
  intro m
  by_cases hlt : ray_cb m < α
  · obtain ⟨n, hn1, hn2⟩ := hcofinal (ray_cb m) hlt m
    exact ⟨n, hn1, le_of_lt hn2⟩
  · -- ray_cb m = α
    have heq : ray_cb m = α := le_antisymm (hray_le m) (not_lt.mp hlt)
    -- Case split on whether α is zero, successor, or limit
    have h_trichotomy : α = 0 ∨ (∃ γ, α = Order.succ γ) ∨ Order.IsSuccLimit α := by
      induction α using Ordinal.limitRecOn with
      | zero => left; rfl
      | succ a _ => right; left; exact ⟨a, rfl⟩
      | limit o hlim _ => right; right; exact hlim
    rcases h_trichotomy with h0 | ⟨γ, hγ⟩ | hlim
    · -- α = 0: trivial, any n > m works since ray_cb n ≥ 0
      exact ⟨m + 1, Nat.lt_succ_of_le le_rfl, by rw [heq, h0]; exact bot_le⟩
    · -- α = γ + 1 (successor): use cofinality with β = γ
      subst hγ
      obtain ⟨n, hn1, hn2⟩ := hcofinal γ (Order.lt_succ_of_not_isMax (not_isMax γ)) m
      exact ⟨n, hn1, by rw [heq]; exact Order.succ_le_of_lt hn2⟩
    · -- by contradiction with h_succ
      obtain ⟨γ, hγ⟩ := h_succ
      exact absurd hγ.symm (Order.IsSuccLimit.succ_ne hlim γ)
