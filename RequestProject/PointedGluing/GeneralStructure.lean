import Mathlib
import RequestProject.PointedGluing.MaxFun.LimitRank
import RequestProject.PointedGluing.Basics.OrdinalArithmetic
import RequestProject.PointedGluing.Basics.GluingInjection
import RequestProject.PointedGluing.MinFun.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# General Structure Theorem (Theorem 3.13)

This file proves the General Structure Theorem for continuous reducibility
between scattered functions on the Baire space.
-/

/-! ## Helper definitions and lemmas for MaxFun_le_limit_rank -/

/-- Restricted domain: {x ∈ B | (g x) 0 = k} as a Set (ℕ → ℕ). -/
def gRestrDom (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), (g ⟨x, h⟩) 0 = k}

/-- Restricted function on gRestrDom. -/
def gRestrFun (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (k : ℕ) :
    gRestrDom B g k → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

private lemma gRestrDom_sub (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (k : ℕ) :
    gRestrDom B g k ⊆ B :=
  fun _ ⟨h, _⟩ => h

private lemma gRestrFun_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (k : ℕ) :
    Continuous (gRestrFun B g k) :=
  hgc.comp (Continuous.subtype_mk continuous_subtype_val _)

private lemma gRestrFun_scattered (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hg : ScatteredFun g) (k : ℕ) :
    ScatteredFun (gRestrFun B g k) := by
  have : ContinuouslyReduces (gRestrFun B g k) g :=
    ⟨fun x => ⟨x.val, (gRestrDom_sub B g k) x.prop⟩,
     Continuous.subtype_mk continuous_subtype_val _,
     id, continuousOn_id, fun x => rfl⟩
  exact this.scattered hg

private lemma gRestrFun_first_coord (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (k : ℕ)
    (x : gRestrDom B g k) : (gRestrFun B g k x) 0 = k := by
  simp [gRestrFun]; exact x.prop.choose_spec

/--
If CBLevel of each restriction is empty, then CBLevel of g is empty.
-/
private lemma gRestrFun_CBLevel_union_empty (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (β : Ordinal.{0})
    (h : ∀ k : ℕ, CBLevel (gRestrFun B g k) β = ∅) :
    CBLevel g β = ∅ := by
  convert CBLevel_open_union_empty g (fun k => { b : B | (g b) 0 = k }) (fun k => ?_) (fun x => ?_) β ?_
  · exact hgc.comp continuous_id' |> Continuous.comp (continuous_apply 0) |> Continuous.isOpen_preimage |> fun h => h { k } <| by simp +decide
  · exact ⟨_, rfl⟩
  · intro k
    have h_homeo : ∃ (e : {b : B | (g b) 0 = k} ≃ₜ gRestrDom B g k), (gRestrFun B g k) ∘ e = (g ∘ Subtype.val : {b : B | (g b) 0 = k} → ℕ → ℕ) := by
      refine ⟨?_, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      refine ⟨fun x => ⟨x.val, ⟨x.1.2, x.2⟩⟩, fun x => ⟨⟨x.val, x.2.choose⟩, x.2.choose_spec⟩, ?_, ?_⟩ <;> simp +decide
      all_goals norm_num [funext_iff, LeftInverse, RightInverse]
      · fun_prop (disch := solve_by_elim)
      · fun_prop (disch := solve_by_elim)
      · intro; simp [gRestrFun]
    obtain ⟨e, he⟩ := h_homeo
    have := CBLevel_homeomorph e (gRestrFun B g k) β; aesop

/--
For each γ < η = CBRank g, some k has CBRank(gRestrFun k) > γ.
-/
private lemma gRestrFun_CBRank_cofinal (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (hg : ScatteredFun g)
    (η : Ordinal.{0}) (hrank : CBRank g = η)
    (γ : Ordinal.{0}) (hγ : γ < η) :
    ∃ k : ℕ, γ < CBRank (gRestrFun B g k) := by
  contrapose! hγ
  -- By assumption, CBLevel(gRestrFun B g k) γ = ∅ for all k.
  have h_empty : ∀ k : ℕ, CBLevel (gRestrFun B g k) γ = ∅ := by
    intro k
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    have := CBLevel_eq_empty_at_rank (gRestrFun B g k) (gRestrFun_scattered B g hg k)
    exact this.subset (CBLevel_antitone _ (hγ k) hx)
  exact hrank ▸ CBRank_le_of_CBLevel_empty g γ (gRestrFun_CBLevel_union_empty B g hgc γ h_empty)



private lemma cblevel_empty_of_le
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) (hf_scat : ScatteredFun f)
    (β : Ordinal.{0}) (hle : CBRank f ≤ β) :
    CBLevel f β = ∅ :=
  Set.eq_empty_of_subset_empty
    ((CBLevel_eq_empty_at_rank f hf_scat) ▸ CBLevel_antitone f hle)

/-- Base case: MaxFun(η) ≤ MinFun(η) for η = 0. -/
private lemma MaxFun_le_MinFun_zero :
    ContinuouslyReduces (MaxFun 0) (MinFun 0) := by
  haveI : IsEmpty (MaxDom 0) := by rw [MaxDom_zero]; exact Set.isEmpty_coe_sort.mpr rfl
  exact continuouslyReduces_of_empty (MaxFun 0) (MinFun 0)

/-- For any sequence of ordinals below a limit, there's an injective
    map into ℕ picking indices of cofinalSeq above each target. -/
private lemma exists_injection_above_targets (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η)
    (β : ℕ → Ordinal.{0}) (hβ : ∀ n, β n < η) :
    ∃ p : ℕ → ℕ, Function.Injective p ∧ ∀ n, β n ≤ cofinalSeq η (p n) := by
  have := @enumBelow_surj η hη (by
  rintro rfl; specialize hβ 0; simp_all +decide ;)
  generalize_proofs at *
  rw [show cofinalSeq η = fun n => enumBelow η n from ?_]
  · have h_infinite : ∀ n, Set.Infinite {m : ℕ | β n ≤ enumBelow η m} := by
      intro n
      have h_infinite : Set.Infinite {m | β n ≤ m ∧ m < η} := by
        have h_infinite : ∀ m : Ordinal.{0}, β n ≤ m ∧ m < η → ∃ m' : Ordinal.{0}, β n ≤ m' ∧ m' < η ∧ m < m' := by
          exact fun m hm => ⟨Order.succ m, hm.1.trans (Order.le_succ _), hlim.succ_lt hm.2, Order.lt_succ m⟩
        contrapose! h_infinite
        exact ⟨Finset.max' (h_infinite.toFinset) ⟨β n, h_infinite.mem_toFinset.mpr ⟨le_rfl, hβ n⟩⟩, h_infinite.mem_toFinset.mp (Finset.max'_mem _ _), fun m' hm₁ hm₂ => Finset.le_max' _ _ (h_infinite.mem_toFinset.mpr ⟨hm₁, hm₂⟩)⟩
      intro h_finite
      exact h_infinite <| Set.Finite.subset (h_finite.image fun m => enumBelow η m) fun x hx => by cases' this ⟨x, hx.2⟩ with m hm; aesop
    use fun n => Nat.recOn n (Nat.find <| Set.Infinite.nonempty <| h_infinite 0) fun n ih => Nat.find <| Set.Infinite.exists_gt (h_infinite (n + 1)) ih
    refine ⟨?_, ?_⟩
    · refine strictMono_nat_of_lt_succ ?_ |> StrictMono.injective
      exact fun n => Nat.find_spec (h_infinite _ |> Set.Infinite.exists_gt <| _) |>.2
    · intro n; induction n <;> simp_all +decide
      · exact Nat.find_spec (h_infinite 0 |> Set.Infinite.nonempty)
      · exact Nat.find_spec (h_infinite _ |> Set.Infinite.exists_gt <| _) |>.1
  · unfold cofinalSeq; aesop

set_option maxHeartbeats 8000000 in
/-- Core inequality: `MaxFun(η + n) ≤ MinFun(η + 2n)`, by well-founded induction on `η`
    and regular induction on `n`. -/
private lemma MaxFun_le_MinFun : ∀ (η : Ordinal.{0}), η < omega1 →
    (Order.IsSuccLimit η ∨ η = 0) → ∀ (n : ℕ),
    ContinuouslyReduces (MaxFun (η + ↑n)) (MinFun (η + 2 * ↑n)) := by
  intro η hη hlam
  -- Well-founded induction on η
  induction η using Ordinal.induction with
  | h η ih_η =>
    intro n
    induction n with
    | zero =>
      have : η + ↑(0 : ℕ) = η := by norm_num
      have : η + 2 * ↑(0 : ℕ) = η := by norm_num
      rw [‹η + ↑(0 : ℕ) = η›, ‹η + 2 * ↑(0 : ℕ) = η›]
      rcases hlam with hlim | h0
      · -- η is limit: use the limit argument
        -- For each k, decompose enumBelow η k = α'_k + m_k
        have hne : η ≠ 0 := hlim.ne_bot
        have h_decomp : ∀ k, ∃ (α' : Ordinal.{0}) (m : ℕ),
            (Order.IsSuccLimit α' ∨ α' = 0) ∧
            enumBelow η k = α' + ↑m ∧
            α' + 2 * ↑m < η := by
          intro k
          obtain ⟨α', m, hα', hm⟩ := ordinal_limit_nat_decomposition (enumBelow η k)
          refine ⟨α', m, hα', hm, ?_⟩
          have h_enum_lt : enumBelow η k < η := enumBelow_lt η hne k
          have hα'_lt : α' < η := by
            calc α' ≤ α' + ↑m := le_self_add
              _ = enumBelow η k := hm.symm
              _ < η := h_enum_lt
          have : α' + 2 * ↑m = α' + ↑(2 * m) := by push_cast; ring_nf
          rw [this]
          exact limit_add_nat_lt η hlim hne α' hα'_lt (2 * m)
        choose α' m hα' hm hα'm using h_decomp
        -- Each MaxFun(enumBelow η k) ≤ MinFun(α'_k + 2*m_k) using the IH on smaller ordinals
        have h_red : ∀ k, ContinuouslyReduces (MaxFun (enumBelow η k))
            (MinFun (α' k + 2 * ↑(m k))) := by
          intro k
          rw [hm k]
          have hα'_lt_η : α' k < η := by
            calc α' k ≤ α' k + ↑(m k) := le_self_add
              _ = enumBelow η k := (hm k).symm
              _ < η := enumBelow_lt η hne k
          exact ih_η (α' k) hα'_lt_η (lt_trans hα'_lt_η hη) (hα' k) (m k)
        -- Get injection p with α'_k + 2*m_k ≤ cofinalSeq η (p k)
        obtain ⟨p, hp_inj, hp_bound⟩ := exists_injection_above_targets η hη hlim
          (fun k => α' k + 2 * ↑(m k)) (fun k => hα'm k)
        -- Each MaxFun(enumBelow η k) ≤ MinFun(cofinalSeq η (p k)) by monotonicity
        have h_red' : ∀ k, ContinuouslyReduces
            (Subtype.val : MaxDom (enumBelow η k) → ℕ → ℕ)
            (Subtype.val : MinDom (cofinalSeq η (p k)) → ℕ → ℕ) := by
          intro k
          exact (h_red k).trans (MinFun_monotone _ _ (by exact lt_trans (hα'm k) hη)
            (by exact lt_of_lt_of_le (cofinalSeq_lt η hlim hne (p k)) hη.le) (hp_bound k))
        -- Apply gluing_reduces_to_pgluing_via_injection
        have h_gl := gluing_reduces_to_pgluing_via_injection
          (fun k => MaxDom (enumBelow η k))
          (fun k => MinDom (cofinalSeq η k))
          p hp_inj h_red'
        -- Now rewrite MaxFun η and MinFun η using the limit unfoldings
        show ContinuouslyReduces (MaxFun η) (MinFun η)
        unfold MaxFun MinFun
        rw [MaxDom_limit η hlim hne, MinDom_limit η hlim hne]
        exact h_gl
      · -- η = 0
        subst h0; exact MaxFun_le_MinFun_zero
    | succ n ih =>
      -- η + (n+1) = Order.succ (η + n) and η + 2*(n+1) = Order.succ (Order.succ (η + 2n))
      have h1 : η + ↑(n + 1) = Order.succ (η + ↑n) := by
        rw [Nat.cast_succ, ← Ordinal.add_one_eq_succ, add_assoc]
      have h2 : η + 2 * ↑(n + 1) = Order.succ (Order.succ (η + 2 * ↑n)) := by
        simp only [Nat.cast_succ]
        rw [← Ordinal.add_one_eq_succ, ← Ordinal.add_one_eq_succ]
        rw [mul_add, mul_one, add_assoc, add_assoc]; norm_num
      rw [h1, h2]
      exact MaxFun_le_MinFun_succ (η + ↑n) (η + 2 * ↑n) ih

set_option maxHeartbeats 8000000 in
/- Tree argument: MaxFun(η) ≤ g for limit η with CBRank g = η.
PROVIDED SOLUTION
We are going to find a sequence '(s_n)_{n\in\N}' in $\N^{<\N}$ of finite sequences
pairwise incomparable for the prefix relation such that the sequence $(\CB(g\corestr{N_{s_n}}))_n$
is either constant equal to $\lambda$ or strictly below $\lambda$ and cofinal in $\lambda$.
Thanks to the induction hypothesis, an application of \cref{Gluingaslowerbound}
to the (pairwise disjoint) clopen sets $(N_{s_n})_n$ allows then to conclude.

We may want to define N_s = nbhd_fin s by adapting nbhd x n for a finite sequence s: Fin n → ℕ
with nbhd_fin s = {h : ∀ i ∈ Fin n s i = h i}. These form a basis of clopen sets
Notice that if t extends s (or s is an initial segment or prefix of t) for finite squences s: Fin n → ℕ and t: Fin m → ℕ, i.e. n≤ m and ∀ i ∈ Fin n s i = t i,
then \CB(g\corestr{N_t})=\lambda implies \CB(g\corestr{N_s})=\lambda.
Here g\corestr{N_t} is the restriction to the primage of nbhd_fin t by g
So $T=\set{s\in\N^{<\N}}[\CB(g\corestr{N_s})=\lambda]$ is non-empty and closed by initial segment,
notice that $T\neq\emptyset$ because it contains at least the empty sequence as nbhd ∅ is \N → ℕ and CB g =λ.
[T] is the body of the tree, the set {x:ℕ → ℕ : ∀ n the restriction x to n is in T}
If $[T]$ is infinite then an application of \cref{InfiniteEmbedOmega} allows to find the desired sequence,
so we can suppose that $[T]$ is finite.
Let $F$ be the set of $\sqsubset$-minimal elements of $\N^{<\N}\setminus T$.
Then ${\CB(g\corestr{N_s}): s\in F}$ is a subset of $\lambda$
and we claim that it is cofinal in $\lambda$, which allows us to find the desired sequence.
Towards a contradiction assume that for some $\beta<\lambda$ we have $\CB(g\corestr{N_s})<\beta$ for all $s\in F$.
Then, by \cref{CBbasics0}~\cref{CBbasicsfromJSL2},  $\CB_{\beta}(g)\cap g^{-1}(N_s)=\emptyset$ for all $s\in F$
and so $\CB_{\beta}(g)\subseteq g^{-1}([T])$.
But as $[T]$ is finite, we have $\CB_{\beta+1}(g)=\empty$ and so $\CB(g)\leq \beta+1$, a contradiction.
 -/
set_option maxHeartbeats 8000000 in
private lemma MaxFun_le_limit_rank (η : Ordinal.{0}) (hη : η < omega1)
    (hlam : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η) :
    ContinuouslyReduces (MaxFun η) g := by
  have hne : η ≠ 0 := hlam.ne_bot
  have h_decomp : ∀ n, ∃ (α' : Ordinal.{0}) (m : ℕ),
      (Order.IsSuccLimit α' ∨ α' = 0) ∧
      enumBelow η n = α' + ↑m ∧
      α' + 2 * ↑m < η := by
    intro n
    obtain ⟨α', m, hα', hm⟩ := ordinal_limit_nat_decomposition (enumBelow η n)
    refine ⟨α', m, hα', hm, ?_⟩
    have hα'_lt : α' < η := by
      calc α' ≤ α' + ↑m := le_self_add
        _ = enumBelow η n := hm.symm
        _ < η := enumBelow_lt η hne n
    have h_cast : (2 : Ordinal.{0}) * ↑m = ↑(2 * m) := by push_cast; ring_nf
    rw [h_cast]
    exact limit_add_nat_lt η hlam hne α' hα'_lt (2 * m)
  choose α' m hα' hm hδ using h_decomp
  obtain ⟨C, p, hp_inj, hC_clopen, hC_disj, hC_bound⟩ :=
    exists_disjoint_clopen_with_cofinal_ranks η hη hlam B g hgc hg hrank
      (fun n => α' n + 2 * ↑(m n)) (fun n => hδ n)
  have hred : ∀ n, ContinuouslyReduces
      (Subtype.val : MaxDom (enumBelow η n) → ℕ → ℕ)
      (gClopenFun B g (C (p n))) := by
    intro n
    have hα'_lt_ω1 : α' n < omega1 := by
      calc α' n ≤ α' n + ↑(m n) := le_self_add
        _ = enumBelow η n := (hm n).symm
        _ < η := enumBelow_lt η hne n
        _ < omega1 := hη
    have hmax_min := MaxFun_le_MinFun (α' n) hα'_lt_ω1 (hα' n) (m n)
    rw [hm n]
    have h_scat := gClopenFun_scattered B g hg (C (p n))
    have h_cont := gClopenFun_continuous B g hgc (C (p n))
    have h_cast : (2 : Ordinal.{0}) * ↑(m n) = ↑(2 * m n) := by push_cast; ring_nf
    have hmin_g : ContinuouslyReduces (MinFun (α' n + 2 * ↑(m n)))
        (gClopenFun B g (C (p n))) :=
      minFun_is_minimum (α' n + 2 * ↑(m n))
        (by rw [h_cast]; exact lt_trans (by rw [← h_cast]; exact hδ n) hη)
        (gClopenDom B g (C (p n)))
        (gClopenFun B g (C (p n)))
        h_cont h_scat
        (CBLevel_nonempty_below_rank _ h_scat _ (hC_bound n))
    exact hmax_min.trans hmin_g
  exact gluing_via_codomain_partition η hη hlam B g hgc C hC_clopen hC_disj p hp_inj hred

set_option maxHeartbeats 8000000 in
/-- **Theorem (JSLgeneralstructure). General Structure Theorem.** -/
theorem general_structure_theorem
    (A B : Set Baire)
    (f : A → Baire) (g : B → Baire)
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (hfc : Continuous f) (hgc : Continuous g)
    (η : Ordinal.{0})
    (hη : η < omega1)
    (hlam : Order.IsSuccLimit η ∨ η = 0) :
      ((CBRank g = η ∧ CBRank f ≤ CBRank g)
        → ContinuouslyReduces f g)
      ∧
      (∀ n : ℕ, (CBRank f = η + ↑n ∧ CBRank g ≥ η + 2 * ↑n + 1)
        → ContinuouslyReduces f g) := by
  constructor
  · -- Item 1
    intro ⟨hg_rank, hf_le⟩
    have hf_le_η : CBRank f ≤ η := hg_rank ▸ hf_le
    rcases hlam with hlam_limit | hlam_zero
    · -- η is limit
      have hf_max : ContinuouslyReduces f (MaxFun η) :=
        (maxFun_is_maximum' η hη).1 f hfc hf
          (fun β hβ => cblevel_empty_of_le f hf β (hf_le_η.trans hβ))
      exact hf_max.trans (MaxFun_le_limit_rank η hη hlam_limit B g hgc hg hg_rank)
    · -- η = 0
      subst hlam_zero
      have hfr : CBRank f = 0 := nonpos_iff_eq_zero.mp (hg_rank ▸ hf_le)
      have : IsEmpty ↥A :=
        isEmpty_of_CBLevel_zero_empty f (cblevel_empty_of_le f hf 0 hfr.le)
      exact continuouslyReduces_of_empty f g
  · -- Item 2
    intro n ⟨hf_rank, hg_ge⟩
    have hηn_lt : η + ↑n < omega1 := omega1_add_nat η hη n
    have hf_max : ContinuouslyReduces f (MaxFun (η + ↑n)) :=
      (maxFun_is_maximum' (η + ↑n) hηn_lt).1 f hfc hf
        (fun β hβ => cblevel_empty_of_le f hf β (hf_rank ▸ hβ))
    have hmax_min := MaxFun_le_MinFun η hη hlam n
    have h_cast : (↑(2 * n) : Ordinal.{0}) = 2 * ↑n := by push_cast; ring_nf
    have h2n_lt : η + ↑(2 * n) < omega1 := omega1_add_nat η hη (2 * n)
    have h2n_lt_rank : η + ↑(2 * n) < CBRank g := by
      rw [h_cast]; exact lt_of_lt_of_le (Order.lt_succ _) hg_ge
    have hmin_g : ContinuouslyReduces (MinFun (η + ↑(2 * n))) g :=
      minFun_is_minimum (η + ↑(2 * n)) h2n_lt B g hgc hg
        (CBLevel_nonempty_below_rank g hg (η + ↑(2 * n)) h2n_lt_rank)
    have hmax_min' : ContinuouslyReduces (MaxFun (η + ↑n)) (MinFun (η + ↑(2 * n))) := by
      rwa [h_cast]
    exact (hf_max.trans hmax_min').trans hmin_g

end
