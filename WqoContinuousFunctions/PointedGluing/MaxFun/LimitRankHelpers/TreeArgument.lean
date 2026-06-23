import WqoContinuousFunctions.ContinuousReducibility.Scattered.CBAnalysis
import WqoContinuousFunctions.ContinuousReducibility.Defs
import WqoContinuousFunctions.PointedGluing.MaxFun.LimitRankHelpers.Helpers
import WqoContinuousFunctions.PointedGluing.CBRank.SimpleHelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Tree Argument for Cofinal Ranks

The tree argument for producing disjoint clopen sets with cofinal CB-ranks,
used in the limit rank case of the General Structure Theorem.

## Main definitions

* `gRestr` — restriction of g to preimage of a set
* `cbRankRestr` — CB-rank of the restriction
* `TreeT` — the tree of finite sequences with full CB-rank

## Main results

* `exists_disjoint_clopen_with_cofinal_ranks` — the main tree argument result
-/


section TreeArgument


/-! ## §2  The tree T and its body [T] -/


variable {B : Set (ℕ → ℕ)} {g : B → ℕ → ℕ}
variable (η : Ordinal.{0})

/-- Restriction of `g` to the preimage of `S`. -/
def gRestr (S : Set (ℕ → ℕ)) : {x : B | g x ∈ S} → ℕ → ℕ :=
  fun x => g x.val

/-- CB-rank of `g` restricted to the preimage of the basic neighborhood `BaNbhd s`. -/
noncomputable def cbRankRestr (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) {n : ℕ} (s : Fin n → ℕ) : Ordinal.{0} :=
  CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val)

/-- The tree `T` of finite sequences `s` such that `CBRank(g|₁{BaNbhd s}) = η`. -/
def TreeT (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (η : Ordinal.{0}) :
    (Σ n : ℕ, Fin n → ℕ) → Prop :=
  fun ⟨_, s⟩ => cbRankRestr B g s = η


lemma CoRestr_BaNbhd_empty : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ := by
  simp [BaNbhd_empty]

/-- The empty sequence is in T: BaNbhd ∅ = univ, so gRestr univ = g, and CBRank g = η. -/
lemma TreeT_contains_empty (hg : ScatteredFun g) (hrank : CBRank g = η) :
    TreeT B g η ⟨0, Fin.elim0⟩ := by
  unfold TreeT cbRankRestr
  have hmem : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ :=
    CoRestr_BaNbhd_empty
  have hopen : IsOpen ({b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} : Set B) :=
    hmem ▸ isOpen_univ
  have hle : CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
      g x.val) ≤ CBRank g :=
    CBRank_open_restrict_le g hg _ hopen
  have hred : ContinuouslyReduces g (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) := by
    exact ⟨fun b => ⟨b, hmem ▸ Set.mem_univ b⟩, Continuous.subtype_mk continuous_id _,
          id, continuousOn_id, fun b => rfl⟩
  have hge : CBRank g ≤ CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) :=
    ContinuouslyReduces.rank_monotone hg (scattered_restrict g hg _) hred
  simp only []
  exact (le_antisymm hle hge).trans hrank


/-- T is closed under prefixes: if t ∈ T and s is a prefix of t, then s ∈ T. -/
lemma TreeT_prefix_closed (heta: η = CBRank g) {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) (ht : TreeT B g η ⟨m, t⟩)
    (hg : ScatteredFun g) (hgc : Continuous g) :
    TreeT B g η ⟨n, s⟩ := by
  simp only [TreeT, cbRankRestr] at *
  -- Let Vs := {b : B | g b ∈ BaNbhd s} and Vt := {b : B | g b ∈ BaNbhd t}.
  -- BaNbhd t ⊆ BaNbhd s, so Vt ⊆ Vs.
  set Vs : Set B := {b : B | g b ∈ BaNbhd s} with hVs_def
  set Vt : Set B := {b : B | g b ∈ BaNbhd t} with hVt_def
  -- Vt ⊆ Vs  (from BaNbhd_antitone)
  have hVtVs : Vt ⊆ Vs := by
    intro b hb
    simp only [hVt_def, hVs_def, Set.mem_setOf_eq] at *
    exact BaNbhd_antitone s t hpre hb
  -- Vs is open: preimage of BaNbhd s (which is open) under the continuous map g.
  have hVs_open : IsOpen Vs := by
    have : Vs = g ⁻¹' BaNbhd s := rfl
    rw [this]
    exact (BaNbhd_isOpen s).preimage hgc
  -- Vt is open (similarly).
  have hVt_open : IsOpen Vt := by
    have : Vt = g ⁻¹' BaNbhd t := rfl
    rw [this]
    exact (BaNbhd_isOpen t).preimage hgc
  -- The restriction g|Vs is scattered (restriction of a scattered function).
  have hgs_scat : ScatteredFun (fun x : Vs => g x.val) :=
    scattered_restrict g hg Vs
  -- The restriction g|Vt is scattered.
  have hgt_scat : ScatteredFun (fun x : Vt => g x.val) :=
    scattered_restrict g hg Vt
  -- Upper bound: CBRank (g|Vs) ≤ CBRank (g|Vt) via open restriction
  -- Vt is an open subset of Vs (since Vt ⊆ Vs and Vt is open in B,
  -- so it is open in the subspace Vs).
  -- We use CBRank_open_restrict_le applied to g|Vs and the open set Vt ∩ Vs = Vt.
  -- g|Vs restricted to Vt equals g|Vt.
  have hVt_open_in_Vs : IsOpen (Subtype.val ⁻¹' Vt : Set Vs) := by
    exact hVt_open.preimage continuous_subtype_val
  -- CBRank (g|Vt) ≤ CBRank (g|Vs)  [Vt is an open subset of Vs]
  have hred : ContinuouslyReduces (fun x : Vt => g x.val) (fun x : Vs => g x.val) :=
    ⟨fun x => ⟨x.val, hVtVs x.prop⟩,
    continuous_subtype_val.subtype_mk _,
    id, continuousOn_id,
    fun _ => rfl⟩
  have hle : CBRank (fun x : Vt => g x.val)  ≤ CBRank (fun x : Vs => g x.val) :=
    ContinuouslyReduces.rank_monotone hgt_scat hgs_scat hred  -- Conclude CBRank (g|Vs) = CBRank (g|Vt) = η.
  have hge : CBRank (fun x : Vs => g x.val) ≤ CBRank (fun x : Vt => g x.val) := by
    calc CBRank (fun x : Vs => g x.val)
        ≤ CBRank g := CBRank_open_restrict_le g hg Vs hVs_open
      _ = η        := heta.symm
      _ = CBRank (fun x : Vt => g x.val) := ht.symm
  exact le_antisymm hge hle |>.trans ht


/-- If s and t are incomparable (neither is a prefix of the other),
    their BaNbhds are disjoint. -/
lemma BaNbhd_incomparable_disjoint {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hst : ¬IsPrefix s t) (hts : ¬IsPrefix t s) :
    Disjoint (BaNbhd s) (BaNbhd t) := by
  simp only [IsPrefix] at hst hts
  push_neg at hst hts
  simp only [Set.disjoint_left, BaNbhd, Set.mem_setOf_eq]
  intro h hs ht
  rcases Nat.lt_or_ge n m with hnm | hnm
  · obtain ⟨i, hi⟩ := hst hnm.le
    exact hi ((hs i).symm.trans (ht ⟨i, i.isLt.trans_le hnm.le⟩))
  · obtain ⟨i, hi⟩ := hts hnm
    exact hi ((ht i).symm.trans (hs ⟨i, i.isLt.trans_le hnm⟩))


/-- Homeomorphism between `{b : B | g b ∈ C}` and `PreImage B g C`. -/
def PreImageEquiv (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    {b : B | g b ∈ C} ≃ₜ PreImage B g C where
  toFun := fun ⟨⟨x, hB⟩, hC⟩ => ⟨x, ⟨hB, hC⟩⟩
  invFun := fun ⟨x, hx⟩ => ⟨⟨x, hx.choose⟩, hx.choose_spec⟩
  left_inv := fun ⟨⟨x, hB⟩, hC⟩ => by simp
  right_inv := fun ⟨x, hx⟩ => by simp
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val.subtype_val _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

lemma CoRestrict_eq_comp (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    CoRestrict' B g C = (fun x : {b : B | g b ∈ C} => g x.val) ∘ (PreImageEquiv B g C).symm := by
  ext ⟨x, hx⟩
  simp [CoRestrict', PreImageEquiv]

lemma CoRestrict_CBRank_eq : ∀ (C : Set (ℕ → ℕ)), IsClopen C →
    CBRank (CoRestrict' B g C) = CBRank (fun x : {b : B | g b ∈ C} => g x.val) := by
  intro C _
  rw [CoRestrict_eq_comp]
  exact CBRank_comp_homeomorph _ _


/-- If all points in CBLevel g (succ β) map to a finite set under g, then
    CBLevel g (succ (succ β)) = ∅. -/
lemma CBLevel_succ_succ_empty_of_finite_image
    {B : Set (ℕ → ℕ)} {g : B → ℕ → ℕ} (hgc : Continuous g)
    (β : Ordinal.{0})
    (F : Set (ℕ → ℕ)) (hF : F.Finite)
    (hcontain : ∀ b : B, b ∈ CBLevel g (Order.succ β) → g b ∈ F) :
    CBLevel g (Order.succ (Order.succ β)) = ∅ := by
  -- By CBLevel_succ', CBLevel g (succ (succ β)) = CBLevel g (succ β) \ isolatedLocus g (CBLevel g (succ β)).
  have hcb_succ_succ : CBLevel g (Order.succ (Order.succ β)) = CBLevel g (Order.succ β) \ isolatedLocus g (CBLevel g (Order.succ β)) := by
    exact CBLevel_succ' g (Order.succ β)
  ext x; simp [hcb_succ_succ]
  intro hx
  -- Since F is finite, F \ {g x} is finite hence closed (by Set.Finite.isClosed in the T1 space ℕ → ℕ).
  have hF_closed : IsClosed (F \ {g x}) := by
    exact hF.subset (Set.diff_subset) |> Set.Finite.isClosed
  refine ⟨?_, ?_, ?_⟩
  exact hx
  exact { y : B | g y ∉ F \ { g x } }
  exact ⟨hF_closed.isOpen_compl.preimage hgc, by aesop, fun y hy => Classical.not_not.1 fun h => hy.1 <| by aesop⟩

/--
If CBRank ≤ β for a scattered function, then CBLevel at β is empty.
-/
lemma CBLevel_empty_of_le_rank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (β : Ordinal) (hle : CBRank f ≤ β) :
    CBLevel f β = ∅ := by
  -- Since f is scattered, CBLevel_eq_empty_at_rank gives CBLevel f (CBRank f) = ∅.
  have h_empty : CBLevel f (CBRank f) = ∅ := by
    exact CBLevel_eq_empty_at_rank f hf
  generalize_proofs at *; (
  exact Set.eq_empty_of_subset_empty (CBLevel_antitone f hle |> Set.Subset.trans <| h_empty.symm ▸ Set.Subset.rfl))

/--
If b ∈ an open set S ⊆ B and CBLevel of g restricted to S at α is empty,
    then b ∉ CBLevel g α.
-/
lemma not_mem_CBLevel_of_open_restrict_empty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (S : Set X) (hS : IsOpen S)
    (b : X) (hb : b ∈ S) (α : Ordinal)
    (hempty : CBLevel (f ∘ Subtype.val : S → Y) α = ∅) :
    b ∉ CBLevel f α := by
  by_contra h_contra
  -- Apply the CBLevel_open_restrict lemma to b and hb.
  have h_restrict : (⟨b, hb⟩ : S) ∈ CBLevel (f ∘ Subtype.val) α := by
    convert CBLevel_open_restrict f S hS α ⟨b, hb⟩ |>.2 h_contra
  exact hempty.subset h_restrict

/--
Discrete topology transfers through `Subtype.val`: if `S` is a discrete subset
of `↥A` (a subtype of `X`), then `Subtype.val '' S` is a discrete subset of `X`.
-/
lemma discreteTopology_image_val {X : Type*} [TopologicalSpace X]
    {A : Set X} (S : Set A) [DiscreteTopology S] :
    DiscreteTopology (Subtype.val '' S : Set X) := by
  rw [discreteTopology_subtype_iff] at *
  simp_all +decide [Filter.inf_principal_eq_bot, nhdsWithin]
  intro x hx hxS; specialize ‹∀ a : X, ∀ b : a ∈ A, ⟨a, b⟩ ∈ S → Sᶜ ∈ 𝓝 ⟨a, b⟩ ⊓ Filter.principal { ⟨a, b⟩ } ᶜ› x hx hxS; simp_all +decide [Filter.mem_inf_principal]
  rw [mem_nhds_subtype] at *
  rcases ‹_› with ⟨u, hu, hu'⟩ ; filter_upwards [hu] with y hy ; specialize hu' ; aesop


/-
this lemma is the crux of the General structure theorem
it is instrumental in showing that any scattered function
of limit CBRank η reduces (and hence is equivalent) to MaxFun η

The proof follows the one presented in the memoir.
Let `η<ω1`​ be a successor limit ordinal,
and let `g:B→ℕ` be a continuous scattered function
such that CBRank(g)=η.
Given a sequence of ordinals `δ_n<η`,
we wish to find a sequence of pairwise disjoint clopen sets
`Cn⊆ℕ` and an injective sequence of indices pn such that for each n,
the Cantor-Bendixson rank of g restricted to Cpn​​ is strictly greater than δn​.

We define a tree T of finite sequences `s∈ℕ^{<ℕ}`.
A sequence s is in T if the rank of g corestricted to the neighborhood BaNbhd(s)
is equal to the total rank η. Let the body of this tree, bodyT,
be the set of infinite sequences `x∈ℕ^\N`such that every prefix of `x` is in `T`.
We proceed by cases on the size of bodyT.
Case 1: bodyT is infinite

If the set of infinite branches is infinite,
we can find an infinite sequence of branches
that are distinct enough to allow us to pick
an infinite antichain of prefixes.
Specifically, because bodyT is a subset of the Baire space,
we can select a sequence of finite prefixes snsn​ such that
no si​ is a prefix of sj for i≠j.

Case 2: bodyT is finite

If bodyT is finite, the rank must be realized by the "frontier" of T.
We define a frontier node to be a sequence s such that s∉T, but its parent is in T.

First, we observe that for any β<η, there must exist a frontier node s
such that the rank of g corestricted to BaNbhd(s) is greater than β.
If this were not the case—that is, if all nodes outside T
whose parents are in T had rank at most β
—then the Cantor-Bendixson level of g at succ(β)
would be entirely contained within the finite set bodyT.
Since bodyT is finite, the subsequent level would
necessarily be empty, implying that CBRank(g)≤succ(succ(β))<η.
This contradicts the assumption that CBRank(g)=η.
-/
lemma exists_disjoint_clopen_with_cofinal_ranks
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η)
    (δ : ℕ → Ordinal.{0}) (hδ : ∀ n, δ n < η) :
    ∃ (C : ℕ → Set (ℕ → ℕ)) (p : ℕ → ℕ),
      Function.Injective p ∧
      (∀ n, IsClopen (C n)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ n, δ n < CBRank (CoRestrict' B g (C (p n))) := by
  -- Step 1: Build the tree T
  let T_prop : ∀ n : ℕ, (Fin n → ℕ) → Prop :=
    fun _ s => CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) = η
  set bodyT : Set (ℕ → ℕ) :=
    {x : ℕ → ℕ | ∀ n, T_prop n (fun i => x i)}
  by_cases hbody : bodyT.Infinite
  · -- Case A: bodyT infinite
    obtain ⟨seq, hseq_incompat, hseq_T⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                          ¬IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, T_prop (seq i).1 (seq i).2 := by
      obtain ⟨S, hS_inf, hS_disc⟩ :=
        haveI : Infinite bodyT := hbody.to_subtype
        exists_infinite_discreteTopology bodyT
      let S' : Set (ℕ → ℕ) := Subtype.val '' S
      have hS'_inf : S'.Infinite := hS_inf.image Subtype.val_injective.injOn
      have hS'_disc : DiscreteTopology ↥S' := @discreteTopology_image_val _ _ _ S hS_disc
      have hS'_sub : S' ⊆ bodyT := by
        rintro x ⟨⟨y, hy⟩, _, rfl⟩; exact hy
      haveI : Infinite S' := hS'_inf.to_subtype
      let f : ℕ → ↥S' := hS'_inf.natEmbedding S'
      have hf_inj : Injective f := (hS'_inf.natEmbedding S').injective
      obtain ⟨seq, hseq_ac, hseq_trunc⟩ :=
        infinite_baire_antichain_prefixes f hf_inj hS'_disc
      refine ⟨seq, hseq_ac, fun i => ?_⟩
      obtain ⟨m, hm⟩ := hseq_trunc i
      have hbody_m : (f m).val ∈ bodyT := hS'_sub (f m).prop
      show T_prop (seq i).1 (seq i).2
      have := hbody_m (seq i).1
      have heq : (seq i).2 = fun (j : Fin (seq i).1) => (f m).val (j : ℕ) := funext hm
      rw [heq]; exact this
    refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
            fun n => BaNbhd_isClopen _, ?_, ?_⟩
    · intro i j hij
      obtain ⟨hst, hts⟩ := hseq_incompat i j hij
      exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts
    · intro n
      simp only [id]
      rw [CoRestrict_CBRank_eq (BaNbhd (seq n).2) (BaNbhd_isClopen _)]
      rw [hseq_T n]
      exact hδ n
  · -- Case B: bodyT finite
    -- Helper: ∀ b, b ∈ CBLevel g (succ β) → g b ∈ bodyT
    -- (assuming all frontier nodes have rank ≤ β)
    have hcontain_aux : ∀ (β : Ordinal.{0}),
        (∀ (n : ℕ) (s : Fin (n+1) → ℕ),
          ¬T_prop (n+1) s → T_prop n (fun i : Fin n => s i.castSucc) →
          CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) ≤ β) →
        ∀ b : B, b ∈ CBLevel g (Order.succ β) → (g b) ∈ bodyT := by
      intro β hβ b hb
      by_contra hnot
      -- By definition of $bodyT$, there exists some $n$ such that $¬T_prop n (fun i => (g b) ↑i)$.
      obtain ⟨n, hn⟩ : ∃ n, ¬T_prop n (fun i => (g b) i) := by
        exact not_forall.mp fun h => hnot fun n => h n
      -- Let's take the minimal such n.
      obtain ⟨n₀, hn₀⟩ : ∃ n₀, ¬T_prop n₀ (fun i => (g b) i) ∧ ∀ m < n₀, T_prop m (fun i => (g b) i) := by
        exact ⟨Nat.find (⟨n, hn⟩ : ∃ n, ¬T_prop n fun i => g b ↑i), Nat.find_spec (⟨n, hn⟩ : ∃ n, ¬T_prop n fun i => g b ↑i), fun m mn => by aesop⟩
      -- Since $n₀$ is minimal, we have $T_prop (n₀ - 1) (fun i => (g b) i.castSucc)$.
      have hT_prop_prev : T_prop (n₀ - 1) (fun i => (g b) i.castSucc) := by
        rcases n₀ <;> simp_all +decide [Fin.castSucc]
        convert hrank using 1
        convert CBRank_comp_homeomorph _ _
        swap
        refine ⟨?_, ?_, ?_⟩
        refine ⟨fun x => ⟨x.val, ?_⟩, fun x => ⟨x, ?_⟩, ?_, ?_⟩ <;> simp +decide [BaNbhd]
        all_goals norm_num [Function.LeftInverse, Function.RightInverse]
        · exact continuous_subtype_val
        · fun_prop
      rcases n₀ <;> simp_all +decide
      · contrapose! hn₀
        convert hT_prop_prev using 1
      · have := hβ _ _ hn₀.1 (hn₀.2 _ le_rfl)
        apply not_mem_CBLevel_of_open_restrict_empty g {x : B | g x ∈ BaNbhd (fun i : Fin (Nat.succ ‹_›) => g b i)} (by
        exact hgc.isOpen_preimage _ (BaNbhd_isOpen _)) b (by
        exact mem_setOf.mpr (congrFun rfl)) (Order.succ β) (by
        apply CBLevel_empty_of_le_rank
        · exact scattered_restrict g hg {x | g x ∈ BaNbhd fun i => g b ↑i}
        · exact le_trans this (Order.le_succ _)) hb
    have hCofinal : ∀ β : Ordinal.{0}, β < η →
        ∃ (n : ℕ) (s : Fin (n+1) → ℕ), ¬T_prop (n+1) s ∧ T_prop n (fun i : Fin n => s i.castSucc) ∧
          β < CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) := by
      intro β hβ
      by_contra hall
      push_neg at hall
      have hcontain := hcontain_aux β hall
      have hempty : CBLevel g (Order.succ (Order.succ β)) = ∅ :=
        CBLevel_succ_succ_empty_of_finite_image hgc β bodyT
          (Set.not_infinite.mp hbody) hcontain
      exact absurd (hrank ▸ CBRank_le_of_CBLevel_empty g _ hempty)
        (not_le.mpr (hlim.succ_lt (hlim.succ_lt hβ)))
    -- Frontier nodes have rank < η
    have hfrontier_rank_lt : ∀ (n : ℕ) (s : Fin (n+1) → ℕ),
        ¬T_prop (n+1) s →
        CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) < η := by
      intro n s hs_prop
      have h_rank_le : CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) ≤ CBRank g := by
        apply CBRank_open_restrict_le
        · assumption
        · exact hgc.isOpen_preimage _ (BaNbhd_isOpen _)
      exact lt_of_le_of_ne (hrank ▸ h_rank_le) hs_prop
    -- Build sequence with strictly increasing ranks ensuring distinctness
    -- Step function: given β < η, get a node with rank in (β, η)
    have hstep : ∀ (β : Ordinal.{0}), β < η →
        ∃ (p : Σ n : ℕ, Fin n → ℕ),
          ¬T_prop p.1 p.2 ∧
          (∃ (m : ℕ) (heq : p.1 = m + 1),
            T_prop m (fun i : Fin m => p.2 (heq ▸ Fin.castSucc i))) ∧
          β < CBRank (fun x : {b : B | g b ∈ BaNbhd p.2} => g x.val) ∧
          CBRank (fun x : {b : B | g b ∈ BaNbhd p.2} => g x.val) < η := by
      intro β hβ
      obtain ⟨n, s, hnt, htp, hgt⟩ := hCofinal β hβ
      exact ⟨⟨n + 1, s⟩, hnt, ⟨n, rfl, htp⟩, hgt, hfrontier_rank_lt n s hnt⟩
    -- Build the sequence using Nat.rec
    let rankOf : (Σ n : ℕ, Fin n → ℕ) → Ordinal :=
      fun p => CBRank (fun x : {b : B | g b ∈ BaNbhd p.2} => g x.val)
    let build : ℕ → (Σ n : ℕ, Fin n → ℕ) × { r : Ordinal // r < η } := fun i =>
      Nat.rec
        (let p := (hstep (δ 0) (hδ 0)).choose
         (p, ⟨rankOf p, (hstep (δ 0) (hδ 0)).choose_spec.2.2.2⟩))
        (fun k prev =>
          let β := max (δ (k + 1)) prev.2.val
          let p := (hstep β (max_lt (hδ (k + 1)) prev.2.prop)).choose
          (p, ⟨rankOf p, (hstep β (max_lt (hδ (k + 1)) prev.2.prop)).choose_spec.2.2.2⟩))
        i
    -- Properties of the build function
    have hbuild_not : ∀ i, ¬T_prop (build i).1.1 (build i).1.2 := by
      intro i
      induction' i with i ih
      · exact Classical.choose_spec (hstep (δ 0) (hδ 0)) |>.1
      · exact Exists.choose_spec (hstep (Max.max (δ (i + 1)) (build i |>.2 |>.1)) (max_lt (hδ _) (build i |>.2 |>.2))) |>.1
    have hbuild_par : ∀ i, ∃ (m : ℕ) (heq : (build i).1.1 = m + 1),
        T_prop m (fun j : Fin m => (build i).1.2 (heq ▸ Fin.castSucc j)) := by
      intro i
      induction' i with i ih
      · exact Exists.choose_spec (hstep (δ 0) (hδ 0)) |>.2.1
      · exact (hstep _ (max_lt (hδ _) (build i |>.2.2)) |> Exists.choose_spec |> And.right |> And.left)
    have hbuild_cofinal : ∀ i, δ i < rankOf (build i).1 := by
      intro i
      induction' i with i ih
      · exact Classical.choose_spec (hstep (δ 0) (hδ 0)) |>.2.2.1
      · exact lt_of_le_of_lt (le_max_left _ _) (hstep _ (by
          exact max_lt (hδ _) (build i |>.2 |>.2)) |> Exists.choose_spec |> And.right |> And.right |> And.left)
    have hbuild_strict : ∀ i, rankOf (build i).1 < rankOf (build (i + 1)).1 := by
      intro i
      refine lt_of_le_of_lt ?_ (hstep (max (δ (i + 1)) (build i).2.val)
        (max_lt (hδ _) (build i |>.2 |>.2)) |> Exists.choose_spec |> And.right |> And.right |> And.left)
      cases i <;> simp +decide [build]
    -- Strictly increasing ranks implies strictly monotone
    have hbuild_strict_mono : StrictMono (fun i => rankOf (build i).1) :=
      strictMono_nat_of_lt_succ hbuild_strict
    -- Helper: if s is a prefix of t's parent (both frontier nodes), then s is in T
    have hprefix_in_T : ∀ (i j : ℕ),
        IsPrefix (build i).1.2 (build j).1.2 →
        (build i).1.1 < (build j).1.1 →
        T_prop (build i).1.1 (build i).1.2 := by
      intro i j ⟨hle, hagree⟩ hlt
      obtain ⟨mj, heqj, hparj⟩ := hbuild_par j
      -- (build i).1.1 < (build j).1.1 = mj + 1, so (build i).1.1 ≤ mj
      have hle_mj : (build i).1.1 ≤ mj := by omega
      -- Construct the prefix from (build i).1.2 to the parent of (build j).1
      -- (build j).1 has length mj+1, so its snd : Fin (mj+1) → ℕ
      -- We define the parent as the init of (build j).1.2
      set parent : Fin mj → ℕ := fun k => (build j).1.2 ⟨k.val, by omega⟩
      have hpre_parent : IsPrefix (build i).1.2 parent := by
        refine ⟨hle_mj, fun k => ?_⟩
        simp only [parent]
        rw [hagree k]
      -- parent and hparj's function agree pointwise (same Fin val)
      have hparj' : T_prop mj parent := by
        -- Both parent and the function in hparj apply (build j).1.2 to Fin elements
        -- with the same .val, so BaNbhd parent = BaNbhd (hparj's function)
        -- parent k and (heqj ▸ castSucc k) are Fin elements with the same .val
        have : parent = fun k : Fin mj => (build j).1.2 (heqj ▸ Fin.castSucc k) := by
          funext k; simp only [parent]
          have val_preserved : ∀ {a b : ℕ} (heq : a = b) (x : Fin a), (heq ▸ x : Fin b).val = x.val := by
            intros; subst_vars; rfl
          -- Both sides apply (build j).1.2 to a Fin with val = k.val
          have h1 : (⟨k.val, by omega⟩ : Fin (build j).1.1).val = (heqj ▸ Fin.castSucc k).val := by
            rw [val_preserved]; exact Fin.val_castSucc k
          exact congrArg (build j).1.2 (Fin.ext h1)
        rw [this]; exact hparj
      exact @TreeT_prefix_closed B g η hrank.symm _ _ _ _ hpre_parent hparj' hg hgc
    -- Incompatibility: distinct frontier nodes are incomparable
    obtain ⟨seq, hseq_incompat, hseq_cofinal⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                           ¬IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, δ i < CBRank (fun x : {b : B | g b ∈ BaNbhd (seq i).2} => g x.val) := by
      refine ⟨fun i => (build i).1, fun i j hij => ⟨?_, ?_⟩, hbuild_cofinal⟩
      · -- ¬IsPrefix (build i).1.2 (build j).1.2
        intro ⟨hle, hagree⟩
        by_cases heqlen : (build i).1.1 = (build j).1.1
        · -- Same length: prefix means equal, contradicting different ranks
          have heq_node : (build i).1 = (build j).1 := by
            -- Since the first components are equal and the second components are equal on the Fin type, the pairs are equal.
            apply Sigma.ext; exact heqlen; exact (by
            exact (Fin.heq_fun_iff heqlen).mpr hagree)
          have : rankOf (build i).1 = rankOf (build j).1 := by rw [heq_node]
          exact absurd this (ne_of_apply_ne id (hbuild_strict_mono.injective.ne hij))
        · -- Different length: shorter is prefix of parent (in T), contradicting ¬T_prop
          have hlt : (build i).1.1 < (build j).1.1 := lt_of_le_of_ne hle heqlen
          exact (hbuild_not i) (hprefix_in_T i j ⟨hle, hagree⟩ hlt)
      · -- ¬IsPrefix (build j).1.2 (build i).1.2 (symmetric case)
        intro ⟨hle, hagree⟩
        by_cases heqlen : (build j).1.1 = (build i).1.1
        · have heq_node : (build j).1 = (build i).1 := by
            -- Since the first components are equal and the second components are equal for all indices, the pairs themselves must be equal.
            apply Sigma.ext
            · -- Apply the hypothesis `heqlen` directly to conclude the proof.
              apply heqlen
            · exact (Fin.heq_fun_iff heqlen).mpr hagree
          have : rankOf (build j).1 = rankOf (build i).1 := by rw [heq_node]
          exact absurd this (ne_of_apply_ne id (hbuild_strict_mono.injective.ne (Ne.symm hij)))
        · have hlt : (build j).1.1 < (build i).1.1 := lt_of_le_of_ne hle heqlen
          exact (hbuild_not j) (hprefix_in_T j i ⟨hle, hagree⟩ hlt)
    -- Now take C n := BaNbhd (seq n).2 and p := id.
    refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
            fun n => BaNbhd_isClopen _, ?_, ?_⟩
    · intro i j hij
      obtain ⟨hst, hts⟩ := hseq_incompat i j hij
      exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts
    · intro n
      simp only [id]
      rw [CoRestrict_CBRank_eq (BaNbhd (seq n).2) (BaNbhd_isClopen _)]
      exact hseq_cofinal n

end TreeArgument
