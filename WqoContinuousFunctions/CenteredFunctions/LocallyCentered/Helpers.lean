import WqoContinuousFunctions.CenteredFunctions.CenteredAsPgluing
import ZeroDimensionalSpaces.Basics
import BQO.TwoBQO
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

universe u

/-!
# Helper lemmas for the successor case of Theorem 4.7

This file contains the technical machinery used in the proof of
`localCenterednessFromTwoBQO_scatFun` (Theorem 4.7), specifically the
successor-rank case. It is split from `CenteredFunctions/Theorems.lean`
to keep file sizes manageable.

## Contents

- `SimpleFun.comp_homeomorph`, `SimpleFun.top_level_scatFun` — basic lemmas on simple functions
- `ScatFun.cyl`, `ScatFun.cyl_isOpen`, `ScatFun.mem_cyl`, `ScatFun.cyl_subset_of_le` — cylinder neighbourhoods
- `locallyCentered_caseA`, `mem_CBLevel_of_cyl_rank` — the two cases in the induction
- `ScatFun.rayOn`, `ScatFun.rayOn_cbRank_lt`, `ScatFun.rayOn_reduces_mono` — restricted rays
  (the pure WQO/2-BQO combinatorics `IsRegularSeq.tail`, `WellQuasiOrdered.exists_forall_le_of_antitone`,
  `wqo_double_selection` now live in the `BQO` library)
- `rayShiftSeq`, `caseB_rho`, `caseB_U`, `caseB_U_isOpen`, `mem_caseB_U` — ray block sequence and case B neighbourhood
- `firstDiff`, `firstDiff_mem_raySet`, `firstDiff_eq_of_mem`, `firstDiff_eventuallyEq`, `firstDiff_tendsto_atTop` — first-difference index
- `raySigma0`, `rayFirstDiff_ge`, `raySigma0_block_mem`, `raySigma0_mem`, `raySigma0_func`, `raySigma0_continuous` — canonical reduction map into the gluing of rays
- `firstNonzero_eventuallyEq` — local constancy of `firstNonzero`
- `pgl_reduces_of_rays`, `ScatFun.reduces_pgl_rays` — constructive "rays as upper bound" (reusable; replaces the degenerate `pointedGluing_rays_upper_bound`)
- `caseB_upper`, `caseB_lower` — the two halves of the case B equivalence
- `caseB_pgl_equiv_exists` — existence of the regular sequence and neighbourhood in case B
- `locallyCentered_simple_caseB`, `locallyCentered_simple_eq_succ`, `locallyCentered_simple_le_succ` — case B conclusion
- `locallyCentered_succ_rank_scatFun` — the full successor step
-/

noncomputable section

/-- `SimpleFun` is invariant under precomposition by a homeomorphism. -/
lemma SimpleFun.comp_homeomorph {X Y : Type u} {Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y → Z) (hf : SimpleFun f) : SimpleFun (f ∘ e) := by
  obtain ⟨β, hne, hempty, y, hy⟩ := hf
  refine ⟨β, ?_, ?_, y, ?_⟩
  · rw [CBLevel_homeomorph]
    exact hne.preimage e.surjective
  · rw [CBLevel_homeomorph, hempty, Set.preimage_empty]
  · intro x hx
    rw [CBLevel_homeomorph] at hx
    exact hy (e x) hx

/-- For a simple `ScatFun` of CB-rank `α + 1`, the top nonempty CB-level is `α`,
the level `α + 1` is empty, and the function is constant on the top level. -/
lemma SimpleFun.top_level_scatFun (G : ScatFun) (hsimple : SimpleFun G.func)
    {α : Ordinal.{0}} (hrank : CBRank G.func = Order.succ α) :
    (CBLevel G.func α).Nonempty ∧ CBLevel G.func (Order.succ α) = ∅ ∧
      ∃ y, ∀ x ∈ CBLevel G.func α, G.func x = y := by
  obtain ⟨β, hne, hempty, y, hy⟩ := hsimple
  have hscat : ScatteredFun G.func := G.hScat
  have hrankβ : CBRank G.func = Order.succ β := by
    rw [CBRank_eq_sInf_empty G.func hscat]
    apply le_antisymm
    · exact csInf_le (OrderBot.bddBelow _) hempty
    · apply le_csInf ⟨Order.succ β, hempty⟩
      intro γ hγ
      by_contra hlt
      push_neg at hlt
      have hsub : CBLevel G.func β ⊆ CBLevel G.func γ :=
        CBLevel_antitone G.func (Order.lt_succ_iff.mp hlt)
      rw [hγ] at hsub
      exact hne.ne_empty (Set.subset_empty_iff.mp hsub)
  have hβα : β = α := Order.succ_eq_succ_iff.mp (hrankβ.symm.trans hrank)
  subst hβα
  exact ⟨hne, hempty, y, hy⟩

/-- Basic clopen cylinder neighbourhood of `x` of depth `n` inside a `ScatFun` domain:
the points whose underlying Baire stream agrees with `x` on the first `n` coordinates. -/
def ScatFun.cyl (G : ScatFun) (x : ↑G.domain) (n : ℕ) : Set ↑G.domain :=
  nbhd' G.domain x n

lemma ScatFun.cyl_isOpen (G : ScatFun) (x : ↑G.domain) (n : ℕ) :
    IsOpen (G.cyl x n) := (baire_nbhd'_isClopen G.domain x n).2

lemma ScatFun.mem_cyl (G : ScatFun) (x : ↑G.domain) (n : ℕ) : x ∈ G.cyl x n := by
  intro i _; rfl

/-- Deeper cylinders are contained in shallower ones. -/
lemma ScatFun.cyl_subset_of_le (G : ScatFun) (x : ↑G.domain) {m n : ℕ} (h : m ≤ n) :
    G.cyl x n ⊆ G.cyl x m := by
  intro a ha i hi
  exact ha i (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h))

/-- Case A: if some open neighbourhood `W` of `x` carries a restriction of CB-rank
strictly below `α + 1`, then `x` has a centered neighbourhood (by the inductive
hypothesis). -/
lemma locallyCentered_caseA
    (α : Ordinal.{0})
    (ih : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func)
    (G : ScatFun) (x : ↑G.domain) (W : Set ↑G.domain) (hW : IsOpen W) (hxW : x ∈ W)
    (hrank : CBRank (G.func ∘ (Subtype.val : ↥W → ↑G.domain)) < Order.succ α) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ IsCentered (G.func ∘ (Subtype.val : ↥U → ↑G.domain)) := by
  set R : ScatFun := G.restrict W with hR
  have hR_rank : CBRank R.func = CBRank (G.func ∘ (Subtype.val : ↥W → ↑G.domain)) := by
    rw [hR]
    show CBRank ((G.func ∘ Subtype.val) ∘ (G.restrictEquiv W)) = _
    exact CBRank_comp_homeomorph (G.restrictEquiv W) (G.func ∘ Subtype.val)
  have hR_lc : IsLocallyCentered R.func := ih _ (hR_rank ▸ hrank) R rfl
  have hW_lc : IsLocallyCentered (G.func ∘ (Subtype.val : ↥W → ↑G.domain)) := by
    have h := IsLocallyCentered_comp_homeomorph (G.restrictEquiv W)
      (G.func ∘ (Subtype.val : ↥W → ↑G.domain))
    rw [hR] at hR_lc
    exact h ▸ hR_lc
  exact isLocallyCentered_restrict_open G.func W hW hW_lc x hxW

/-
If every cylinder neighbourhood of `x` carries a restriction of CB-rank `≥ α + 1`
(equivalently `= α + 1`), then `x` lies in the top CB-level `CB_α(G)`.
-/
lemma mem_CBLevel_of_cyl_rank
    (G : ScatFun) (α : Ordinal.{0}) (_ : CBRank G.func = Order.succ α)
    (x : ↑G.domain)
    (hcyl : ∀ n, Order.succ α ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain))) :
    x ∈ CBLevel G.func α := by
  contrapose! hcyl
  -- By `baire_subspace_cylinder_mem_nhds`, there exists `m` with `G.cyl x m ⊆ (CBLevel G.func α)ᶜ`.
  obtain ⟨m, hm⟩ : ∃ m, G.cyl x m ⊆ (CBLevel G.func α)ᶜ := by
    have h_compl_open : IsOpen (CBLevel G.func α)ᶜ :=
      isOpen_compl_iff.mpr (CBLevel_isClosed _ _)
    exact baire_subspace_cylinder_mem_nhds x (CBLevel G.func α)ᶜ h_compl_open hcyl
  refine ⟨m, ?_⟩
  -- It suffices to show `CB_α` of the restriction to the cylinder is empty.
  rw [Order.lt_succ_iff]
  apply CBRank_le_of_CBLevel_empty
  -- A point of `CB_α` of the restriction would be a point of `CB_α(G)` inside the
  -- cylinder, contradicting that the cylinder avoids `CB_α(G)`.
  rw [Set.eq_empty_iff_forall_notMem]
  intro a ha
  exact hm a.2 ((CBLevel_open_restrict G.func (G.cyl x m) (G.cyl_isOpen x m) α a).mp ha)

-- Ray machinery (`ScatFun.rayOn`, `rayShiftSeq`, `firstDiff*`, `raySigma0*`,
-- `pgl_reduces_of_rays`, `reduces_pgl_rays`) and the monotonization skeleton
-- (`glWindow`, `exists_monotone_pgl_equiv`) moved upstream to
-- `CenteredFunctions/CenteredAsPgluing/Helpers.lean`.
/-
Each restricted ray of a simple function of rank `α + 1` has CB-rank `< α + 1`,
because the (unrestricted) rays have CB-rank `≤ α` (`ray_cb_le_alpha`) and restricting
to an open subset cannot increase the CB-rank.
-/
lemma ScatFun.rayOn_cbRank_lt (G : ScatFun) (α : Ordinal.{0}) (y : Baire)
    (hy : ∀ a ∈ CBLevel G.func α, G.func a = y)
    (S : Set ↑G.domain) (hS : IsOpen S) (i : ℕ) :
    CBRank (G.rayOn y S i).func < Order.succ α := by
  have h_cb : CBRank (G.rayOn y S i).func = CBRank (fun z : {a : ↑G.domain | a ∈ S ∧ G.func a ∈ RaySet Set.univ y i} => G.func z.val) := by
    convert CBRank_comp_homeomorph ( G.restrictEquiv ( S ∩ { a | G.func a ∈ RaySet Set.univ y i } ) ) _;
    ext; aesop;
  set Ray := {a : ↑G.domain | G.func a ∈ RaySet Set.univ y i}
  set r : Ray → Baire := fun z => G.func z.val;
  have h_ray_cb : CBRank r ≤ α := by
    apply ray_cb_le_alpha G.func G.hCont α y hy i;
  have h_open_subset : CBRank (fun z : {a : ↑G.domain | a ∈ S ∧ G.func a ∈ RaySet Set.univ y i} => G.func z.val) ≤ CBRank r := by
    convert CBRank_open_restrict_le r _ _ _;
    convert CBRank_comp_homeomorph _ _;
    rotate_left;
    rotate_left;
    exact scattered_restrict _ G.hScat _;
    exact { z : Ray | z.val ∈ S };
    exact hS.preimage ( continuous_subtype_val );
    rotate_left;
    refine ⟨ ?_, ?_, ?_ ⟩;
    refine ⟨ fun x => ⟨ ⟨ x.val, x.property.2 ⟩, x.property.1 ⟩, fun x => ⟨ x.val.val, x.property, x.val.property ⟩, ?_, ?_ ⟩ <;> simp +decide;
    all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
    · fun_prop;
    · fun_prop;
    · rfl;
  exact h_cb.symm ▸ lt_of_le_of_lt h_open_subset ( lt_of_le_of_lt h_ray_cb ( Order.lt_succ α ) )

/-
Restricting a ray to a smaller set yields a `ScatFun` that continuously reduces to
the ray restricted to a larger set (via the inclusion).
-/
lemma ScatFun.rayOn_reduces_mono (G : ScatFun) (y : Baire) {S S' : Set ↑G.domain}
    (hSS : S' ⊆ S) (i : ℕ) :
    ScatFun.Reduces (G.rayOn y S' i) (G.rayOn y S i) := by
  unfold ScatFun.Reduces;
  unfold ScatFun.rayOn; simp +decide [ ScatFun.restrict, ScatFun.restrictEquiv ] ;
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ x.val, x.property.1, hSS x.property.2.1, x.property.2.2 ⟩;
  · fun_prop;
  · refine ⟨ fun x => x, ?_, ?_ ⟩ <;> norm_num;
    exact continuousOn_id

/-- `LevelLT.reduces` is a preorder on `ScatFun.LevelLT β`, induced from the preorder
`ScatFun.Reduces` on the underlying `ScatFun`s. -/
instance ScatFun.LevelLT.reduces_isPreorder (β : Ordinal.{0}) :
    IsPreorder (ScatFun.LevelLT β) (ScatFun.LevelLT.reduces β) where
  refl F := ContinuouslyReduces.refl F.val.func
  trans _ _ _ hab hbc := ContinuouslyReduces.trans hab hbc

/-- The regular sequence of rays extracted in case B: the rays of `G` at `y`, restricted
to the cylinder `G.cyl x m`, shifted to start at index `j`. -/
noncomputable def caseB_rho (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ) :
    ℕ → ScatFun :=
  rayShiftSeq G y (G.cyl x m) j

/-- The neighbourhood of `x` extracted in case B: the cylinder `G.cyl x m` with the
finitely many low rays (indices `< j`) removed. -/
noncomputable def caseB_U (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ) :
    Set ↑G.domain :=
  G.cyl x m ∩ {a | ∀ i, i < j → G.func a ∉ RaySet Set.univ y i}

lemma caseB_U_isOpen (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ) :
    IsOpen (caseB_U G y x m j) := by
  refine IsOpen.inter ( G.cyl_isOpen x m ) ?_;
  convert isOpen_biInter_finset ( fun i _ => ?_ ) using 1;
  rotate_left;
  exact ℕ;
  exact Finset.range j;
  exact fun i => { a : G.domain | G.func a ∉ RaySet Set.univ y i };
  · refine isOpen_compl_iff.mpr ?_;
    simp +decide only [RaySet, mem_univ, ne_eq, true_and];
    refine IsClosed.inter ?_ ?_;
    · simp +decide only [isClosed_iff_clusterPt];
      intro a ha k hk; exact (by
      rw [ clusterPt_principal_iff ] at ha;
      contrapose! ha;
      refine ⟨ { b : G.domain | G.func b k ≠ y k }, ?_, ?_ ⟩;
      · exact IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq ( continuous_apply k |> Continuous.comp <| G.hCont ) continuous_const ) ha;
      · exact Set.eq_empty_of_forall_notMem fun b hb => hb.1 <| hb.2 k hk);
    · exact isClosed_compl_iff.mpr ( IsOpen.preimage ( show Continuous fun a : G.domain => G.func a i from ( continuous_apply i ).comp G.hCont ) ( isOpen_discrete { y i } ) );
  · aesop

lemma mem_caseB_U (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ)
    (hfx : G.func x = y) : x ∈ caseB_U G y x m j := by
  exact ⟨ G.mem_cyl x m, fun i hi => by simp +decide [ hfx, RaySet ] ⟩

/-
Upper bound: `G` restricted to `caseB_U` continuously reduces to the pointed gluing
of the ray sequence `caseB_rho`.  A direct instance of `pgl_reduces_of_rays` with
`S = caseB_U`, `T = G.cyl x m` (note `caseB_rho = rayShiftSeq G y (G.cyl x m) j`).
-/
lemma caseB_upper (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ) :
    ContinuouslyReduces
      (G.func ∘ (Subtype.val : ↥(caseB_U G y x m j) → ↑G.domain))
      (ScatFun.pgl (caseB_rho G y x m j)).func :=
  pgl_reduces_of_rays G y (caseB_U G y x m j) (G.cyl x m) j
    (fun _ ha => ha.1) (fun _ ha i hi => ha.2 i hi)

/-
Lower bound: the pointed gluing of the ray sequence `caseB_rho` continuously reduces
to `G` restricted to `caseB_U`, using the domination data from the WQO selection.
-/
lemma caseB_lower (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ)
    (hfx : G.func x = y)
    (hdom : ∀ n : ℕ, m < n → ∀ i : ℕ, ∃ i' : ℕ, j ≤ i' ∧
      ScatFun.Reduces (G.rayOn y (G.cyl x m) (i + j)) (G.rayOn y (G.cyl x n) i')) :
    ContinuouslyReduces
      (ScatFun.pgl (caseB_rho G y x m j)).func
      (G.func ∘ (Subtype.val : ↥(caseB_U G y x m j) → ↑G.domain)) := by
  convert ScatFun.pgl_reduces_of_local _ _ _ _ using 1;
  rotate_left;
  exact caseB_rho G y x m j;
  exact G.restrict ( caseB_U G y x m j );
  exact ( G.restrictEquiv ( caseB_U G y x m j ) ).symm ⟨ x, mem_caseB_U G y x m j hfx ⟩;
  · intro i V hV hxV;
    obtain ⟨ n, hn ⟩ := baire_subspace_cylinder_mem_nhds _ _ hV hxV;
    obtain ⟨ i', hi', h ⟩ := hdom ( n + m + 1 ) ( by linarith ) i;
    obtain ⟨ σ, hσ, τ, hτ, h ⟩ := h;
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
    use fun z => ⟨ σ z |>.1, by
      simp +decide only [ScatFun.rayOn, caseB_U, coe_setOf, mem_setOf_eq, Finset.mem_range, preimage_setOf_eq, Subtype.forall] at *;
      simp +decide only [ScatFun.restrict, coe_setOf, mem_setOf_eq, mem_inter_iff, comp_apply, forall_exists_index, forall_and_index] at *;
      simp +decide only [ScatFun.cyl] at *;
      simp +decide only [nbhd', RaySet, ne_eq, mem_setOf_eq, Finset.mem_range, mem_univ, true_and, forall_and_index, not_and, Decidable.not_not, exists_and_left] at *;
      grind ⟩
    all_goals generalize_proofs at *;
    exact τ;
    · fun_prop;
    · convert h using 1;
    · convert hτ using 1;
    · intro z; specialize hn; simp_all +decide [ Set.subset_def ] ;
      convert hn _ _ _ using 1;
      intro k hk; have := σ z |>.2.2; simp_all +decide [ ScatFun.rayOn ] ;
      exact this.1 k ( by simpa using by linarith );
    · simp +decide [ ScatFun.rayOn, ScatFun.restrict ] at *;
      simp +decide only [ScatFun.restrictEquiv, coe_setOf, mem_setOf_eq, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk] at *;
      simp +decide only [RaySet, ne_eq, mem_setOf_eq, mem_univ, true_and, forall_and_index] at *;
      rw [ mem_closure_iff_seq_limit ];
      simp +decide only [mem_range, Subtype.exists, hfx, tendsto_pi_nhds, nhds_discrete, Filter.tendsto_pure, Filter.eventually_atTop, ge_iff_le, not_exists, not_and, not_forall];
      intro x_1 hx_1
      use i';
      intro n; obtain ⟨ a, ha, ha' ⟩ := hx_1 n; use n; simp +decide;
      grind +splitImp;
  · unfold ScatFun.Reduces; simp +decide [ ScatFun.pgl, ScatFun.restrict ] ;
    grind +suggestions

/-- **Case B — the top point `x` is a center of its basin.**  Strengthening of `caseB_lower`:
the lower reduction `pgl ρ ≤ G|_{caseB_U}` (built by `pgl_reduces_of_local` anchored at `x`)
sends the gluing's distinguished point `zeroStream` to `x`.  Via `pgl_reduces_of_local_base`
(which exposes that) and `centerInvariance_equiv`, `x` is a center of `G|_{caseB_U}`.  The
reasoning is done at the `G.restrict caseB_U` level and transported back across `restrictEquiv`
with `IsCenterFor.comp_homeomorph`. -/
lemma caseB_x_isCenter (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ)
    (hfx : G.func x = y)
    (hreg : Preorder.IsRegularSeq ScatFun.Reduces (caseB_rho G y x m j))
    (hdom : ∀ n : ℕ, m < n → ∀ i : ℕ, ∃ i' : ℕ, j ≤ i' ∧
      ScatFun.Reduces (G.rayOn y (G.cyl x m) (i + j)) (G.rayOn y (G.cyl x n) i')) :
    IsCenterFor (G.func ∘ (Subtype.val : ↥(caseB_U G y x m j) → ↑G.domain))
      ⟨x, mem_caseB_U G y x m j hfx⟩ := by
  obtain ⟨σ', hσ', hbase, τ', hτ', heq'⟩ :=
    ScatFun.pgl_reduces_of_local_base (caseB_rho G y x m j) (G.restrict (caseB_U G y x m j))
      ((G.restrictEquiv (caseB_U G y x m j)).symm ⟨x, mem_caseB_U G y x m j hfx⟩) (by
        intro i V hV hxV
        obtain ⟨ n, hn ⟩ := baire_subspace_cylinder_mem_nhds _ _ hV hxV
        obtain ⟨ i', hi', h ⟩ := hdom ( n + m + 1 ) ( by linarith ) i
        obtain ⟨ σ, hσ, τ, hτ, h ⟩ := h
        refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
        use fun z => ⟨ σ z |>.1, by
          simp +decide only [ScatFun.rayOn, caseB_U, coe_setOf, mem_setOf_eq, Finset.mem_range, preimage_setOf_eq, Subtype.forall] at *
          simp +decide only [ScatFun.restrict, coe_setOf, mem_setOf_eq, mem_inter_iff, comp_apply, forall_exists_index, forall_and_index] at *
          simp +decide only [ScatFun.cyl] at *
          simp +decide only [nbhd', RaySet, ne_eq, mem_setOf_eq, Finset.mem_range, mem_univ, true_and, forall_and_index, not_and, Decidable.not_not, exists_and_left] at *
          grind ⟩
        all_goals generalize_proofs at *
        exact τ
        · fun_prop
        · convert h using 1
        · convert hτ using 1
        · intro z; specialize hn; simp_all +decide [ Set.subset_def ]
          convert hn _ _ _ using 1
          intro k hk; have := σ z |>.2.2; simp_all +decide [ ScatFun.rayOn ]
          exact this.1 k ( by simpa using by linarith )
        · simp +decide [ ScatFun.rayOn, ScatFun.restrict ] at *
          simp +decide only [ScatFun.restrictEquiv, coe_setOf, mem_setOf_eq, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk] at *
          simp +decide only [RaySet, ne_eq, mem_setOf_eq, mem_univ, true_and, forall_and_index] at *
          rw [ mem_closure_iff_seq_limit ]
          simp +decide only [mem_range, Subtype.exists, hfx, tendsto_pi_nhds, nhds_discrete, Filter.tendsto_pure, Filter.eventually_atTop, ge_iff_le, not_exists, not_and, not_forall]
          intro x_1 hx_1
          use i'
          intro nn; obtain ⟨ a, ha, ha' ⟩ := hx_1 nn; use nn; simp +decide
          grind +splitImp)
  have hupper : ContinuouslyReduces (G.restrict (caseB_U G y x m j)).func
      (ScatFun.pgl (caseB_rho G y x m j)).func :=
    (caseB_upper G y x m j).comp_homeomorph_left (G.restrictEquiv (caseB_U G y x m j))
  have hequiv : ContinuouslyEquiv (ScatFun.pgl (caseB_rho G y x m j)).func
      (G.restrict (caseB_U G y x m j)).func := ⟨⟨σ', hσ', τ', hτ', heq'⟩, hupper⟩
  have hc : IsCenterFor (G.restrict (caseB_U G y x m j)).func
      (σ' ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) :=
    centerInvariance_equiv (pgluingOfRegularIsCentered _ hreg) hequiv hσ' hτ' heq'
  rw [hbase] at hc
  have hc2 := (IsCenterFor.comp_homeomorph (G.restrictEquiv (caseB_U G y x m j))
    (G.func ∘ (Subtype.val : ↥(caseB_U G y x m j) → ↑G.domain))
    ((G.restrictEquiv (caseB_U G y x m j)).symm ⟨x, mem_caseB_U G y x m j hfx⟩)).mp hc
  rwa [Homeomorph.apply_symm_apply] at hc2

/-- **Case B kernel — the heart of Theorem 4.7's successor case.**  Under the case-B
hypotheses, `x` has an open neighbourhood `U` on which `G` is continuously equivalent
to the pointed gluing of a *regular* sequence `ρ` of `ScatFun`s.

The argument restricts the rays of `G` at `y` to deeper and deeper cylinders of `x`,
uses that `𝒞_{<α+1}` is WQO (from the 2-BQO hypothesis) to extract a regular sequence
`ρ` of rays, and shows the corresponding neighbourhood `U` of `x` satisfies
`G|_U ≡ pgl ρ`. -/
lemma caseB_pgl_equiv_exists
    (α : Ordinal.{0}) (_ : α < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ α)))
    (G : ScatFun) (_ : CBRank G.func = Order.succ α)
    (y : Baire) (hy : ∀ a ∈ CBLevel G.func α, G.func a = y)
    (_ : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func)
    (x : ↑G.domain) (hx_top : x ∈ CBLevel G.func α)
    (_ : ∀ n, Order.succ α ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain))) :
    ∃ (ρ : ℕ → ScatFun) (U : Set ↑G.domain),
      Preorder.IsRegularSeq ScatFun.Reduces ρ ∧ IsOpen U ∧ x ∈ U ∧
        ContinuouslyEquiv (G.func ∘ (Subtype.val : ↥U → ↑G.domain)) (ScatFun.pgl ρ).func := by
  have hfx : G.func x = y := hy x hx_top
  set s : ℕ → ℕ → ScatFun.LevelLT (Order.succ α) :=
    fun n i => ⟨G.rayOn y (G.cyl x n) i,
      G.rayOn_cbRank_lt α y hy (G.cyl x n) (G.cyl_isOpen x n) i⟩ with hs
  have hdec : ∀ m n i : ℕ, m ≤ n →
      ScatFun.LevelLT.reduces (Order.succ α) (s n i) (s m i) := by
    intro m n i hmn
    exact G.rayOn_reduces_mono y (G.cyl_subset_of_le x hmn) i
  obtain ⟨m, j, hreg, hdom⟩ := wqo_double_selection h2bqo s hdec
  refine ⟨caseB_rho G y x m j, caseB_U G y x m j, ?_, caseB_U_isOpen G y x m j,
    mem_caseB_U G y x m j hfx, ?_, ?_⟩
  · intro i
    exact hreg i
  · exact caseB_upper G y x m j
  · refine caseB_lower G y x m j hfx ?_
    intro n hn i
    obtain ⟨i', hi', hred⟩ := hdom n hn i
    exact ⟨i', hi', hred⟩

/-- **Case B — the heart of Theorem 4.7's successor case.**  `G` is simple of
rank `α + 1` with top level `CB_α(G)` on which `G` is constant `= y`, and `x` lies in
that top level (and every cylinder neighbourhood of `x` keeps rank `α + 1`).  Then `x`
has a centered neighbourhood.

We obtain from `caseB_pgl_equiv_exists` a regular sequence `ρ` and a neighbourhood `U`
of `x` with `G|_U ≡ pgl ρ`.  Since `ρ` is regular, `pgl ρ` is centered (at `0^ω`) by
`pgluingOfRegularIsCentered`, hence so is `G|_U` by `isCentered_of_equiv`. -/
lemma locallyCentered_simple_caseB
    (α : Ordinal.{0}) (hα : α < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ α)))
    (G : ScatFun) (hG_rank : CBRank G.func = Order.succ α)
    (y : Baire) (hy : ∀ a ∈ CBLevel G.func α, G.func a = y)
    (ih : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func)
    (x : ↑G.domain) (hx_top : x ∈ CBLevel G.func α)
    (hcyl : ∀ n, Order.succ α ≤
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain))) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ IsCentered (G.func ∘ (Subtype.val : ↥U → ↑G.domain)) := by
  obtain ⟨ρ, U, hρ_reg, hU_open, hxU, hequiv⟩ :=
    caseB_pgl_equiv_exists α hα h2bqo G hG_rank y hy ih x hx_top hcyl
  refine ⟨U, hU_open, hxU, ?_⟩
  exact isCentered_of_equiv
    ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, pgluingOfRegularIsCentered ρ hρ_reg⟩
    hequiv

/-- **Core successor case (simple, exact rank).**  A *simple* scattered function of
CB-rank exactly `α + 1` is locally centered, given the inductive hypothesis below
`α + 1` and the 2-BQO hypothesis at `α + 1`. -/
lemma locallyCentered_simple_eq_succ
    (α : Ordinal.{0}) (hα : α < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ α)))
    (G : ScatFun) (hG_simple : SimpleFun G.func)
    (hG_rank : CBRank G.func = Order.succ α)
    (ih : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func) :
    IsLocallyCentered G.func := by
  obtain ⟨_htop_ne, _htop_empty, y, hy⟩ := hG_simple.top_level_scatFun G hG_rank
  intro x
  by_cases hcase : ∃ n : ℕ,
      CBRank (G.func ∘ (Subtype.val : ↥(G.cyl x n) → ↑G.domain)) < Order.succ α
  · obtain ⟨n, hn⟩ := hcase
    exact locallyCentered_caseA α ih G x (G.cyl x n) (G.cyl_isOpen x n) (G.mem_cyl x n) hn
  · push_neg at hcase
    exact locallyCentered_simple_caseB α hα h2bqo G hG_rank y hy ih x
      (mem_CBLevel_of_cyl_rank G α hG_rank x hcase) hcase

/-- A *simple* scattered function whose CB-rank does not exceed `α + 1` is locally
centered. If its rank is strictly below `α + 1` this is immediate from the inductive
hypothesis; if it equals `α + 1` it is `locallyCentered_simple_eq_succ`. -/
lemma locallyCentered_simple_le_succ
    (α : Ordinal.{0}) (hα : α < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ α)))
    (G : ScatFun) (hG_simple : SimpleFun G.func)
    (hG_le : CBRank G.func ≤ Order.succ α)
    (ih : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func) :
    IsLocallyCentered G.func := by
  rcases lt_or_eq_of_le hG_le with hlt | heq
  · exact ih _ hlt G rfl
  · exact locallyCentered_simple_eq_succ α hα h2bqo G hG_simple heq ih

lemma locallyCentered_succ_rank_scatFun
    (α : Ordinal.{0}) (hα : α < omega1)
    (h2bqo : TwoBQO (ScatFun.LevelLT.reduces (Order.succ α)))
    (f : ScatFun)
    (hf_rank : CBRank f.func = Order.succ α)
    (ih : ∀ β < Order.succ α, ∀ (g : ScatFun), CBRank g.func = β → IsLocallyCentered g.func) :
    IsLocallyCentered f.func := by
  -- By the Decomposition Lemma, `f` is locally simple.
  intro x
  obtain ⟨U, hU_clopen, hxU, hsimple⟩ :=
    decomposition_lemma_baire f.domain f.func f.hScat x
  set W : Set ↑f.domain := {a | (a : Baire) ∈ U} with hW
  have hW_open : IsOpen W := hU_clopen.2.preimage continuous_subtype_val
  have hxW : x ∈ W := hxU
  set G : ScatFun := f.restrict W with hG
  have hG_simple : SimpleFun G.func :=
    hsimple.comp_homeomorph (f.restrictEquiv W) (f.func ∘ (Subtype.val : ↥W → ↑f.domain))
  have hG_le : CBRank G.func ≤ Order.succ α := by
    rw [hG]
    show CBRank ((f.func ∘ (Subtype.val : ↥W → ↑f.domain)) ∘ (f.restrictEquiv W)) ≤ _
    rw [CBRank_comp_homeomorph (f.restrictEquiv W) (f.func ∘ Subtype.val)]
    exact (CBRank_open_restrict_le f.func f.hScat W hW_open).trans hf_rank.le
  have hG_lc : IsLocallyCentered G.func :=
    locallyCentered_simple_le_succ α hα h2bqo G hG_simple hG_le ih
  have hW_lc : IsLocallyCentered (f.func ∘ (Subtype.val : ↥W → ↑f.domain)) := by
    have := (IsLocallyCentered_comp_homeomorph (f.restrictEquiv W)
      (f.func ∘ (Subtype.val : ↥W → ↑f.domain)))
    rw [hG] at hG_lc
    exact this ▸ hG_lc
  exact isLocallyCentered_restrict_open f.func W hW_open hW_lc x hxW

end
