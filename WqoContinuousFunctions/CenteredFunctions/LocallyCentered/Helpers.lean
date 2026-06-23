import WqoContinuousFunctions.CenteredFunctions.Theorems
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

/-- The `i`-th ray of a `ScatFun` `G` at base point `y`, intersected with a subset `S`
of the domain, packaged as a `ScatFun` via `G.restrict`. -/
noncomputable def ScatFun.rayOn (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (i : ℕ) :
    ScatFun :=
  G.restrict (S ∩ {a | G.func a ∈ RaySet Set.univ y i})

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
    refine' ⟨ _, _, _ ⟩;
    refine' ⟨ fun x => ⟨ ⟨ x.val, x.property.2 ⟩, x.property.1 ⟩, fun x => ⟨ x.val.val, x.property, x.val.property ⟩, _, _ ⟩ <;> simp +decide;
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
  refine' ⟨ _, _, _ ⟩;
  exact fun x => ⟨ x.val, x.property.1, hSS x.property.2.1, x.property.2.2 ⟩;
  · fun_prop;
  · refine' ⟨ fun x => x, _, _ ⟩ <;> norm_num;
    exact continuousOn_id

/-- `LevelLT.reduces` is a preorder on `ScatFun.LevelLT β`, induced from the preorder
`ScatFun.Reduces` on the underlying `ScatFun`s. -/
instance ScatFun.LevelLT.reduces_isPreorder (β : Ordinal.{0}) :
    IsPreorder (ScatFun.LevelLT β) (ScatFun.LevelLT.reduces β) where
  refl F := ContinuouslyReduces.refl F.val.func
  trans _ _ _ hab hbc := ContinuouslyReduces.trans hab hbc

/-- The rays of `G` at `y` on a set `T`, shifted to start at index `j` (block `i` is
the ray of index `i + j`).  This is the block sequence used in the canonical reduction
of a function into the pointed gluing of its rays. -/
noncomputable def rayShiftSeq (G : ScatFun) (y : Baire) (T : Set ↑G.domain) (j : ℕ) :
    ℕ → ScatFun :=
  fun i => G.rayOn y T (i + j)

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
  refine' IsOpen.inter ( G.cyl_isOpen x m ) _;
  convert isOpen_biInter_finset ( fun i _ => ?_ ) using 1;
  rotate_left;
  exact ℕ;
  exact Finset.range j;
  exact fun i => { a : G.domain | G.func a ∉ RaySet Set.univ y i };
  · refine' isOpen_compl_iff.mpr _;
    simp +decide [ RaySet ];
    refine' IsClosed.inter _ _;
    · simp +decide only [isClosed_iff_clusterPt];
      intro a ha k hk; exact (by
      rw [ clusterPt_principal_iff ] at ha;
      contrapose! ha;
      refine' ⟨ { b : G.domain | G.func b k ≠ y k }, _, _ ⟩;
      · exact IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq ( continuous_apply k |> Continuous.comp <| G.hCont ) continuous_const ) ha;
      · exact Set.eq_empty_of_forall_notMem fun b hb => hb.1 <| hb.2 k hk);
    · exact isClosed_compl_iff.mpr ( IsOpen.preimage ( show Continuous fun a : G.domain => G.func a i from ( continuous_apply i ).comp G.hCont ) ( isOpen_discrete { y i } ) );
  · aesop

lemma mem_caseB_U (G : ScatFun) (y : Baire) (x : ↑G.domain) (m j : ℕ)
    (hfx : G.func x = y) : x ∈ caseB_U G y x m j := by
  exact ⟨ G.mem_cyl x m, fun i hi => by simp +decide [ hfx, RaySet ] ⟩

/-- First coordinate where `v` differs from `y` (junk value `0` when `v = y`). -/
noncomputable def firstDiff (y v : Baire) : ℕ := sInf {k | v k ≠ y k}

/-
If `v ≠ y` then `v` lies in the ray of index `firstDiff y v` at `y`.
-/
lemma firstDiff_mem_raySet (y v : Baire) (h : v ≠ y) :
    v ∈ RaySet Set.univ y (firstDiff y v) := by
  refine' ⟨ Set.mem_univ _, _, _ ⟩;
  · exact fun k hk => Classical.not_not.1 fun hk' => hk.not_ge <| Nat.sInf_le hk';
  · exact Nat.sInf_mem ( Function.ne_iff.mp h )

/-
The ray index is determined by ray membership.
-/
lemma firstDiff_eq_of_mem (y v : Baire) (k : ℕ) (h : v ∈ RaySet Set.univ y k) :
    firstDiff y v = k := by
  obtain ⟨ hk₁, hk₂ ⟩ := h;
  exact le_antisymm ( Nat.sInf_le hk₂.2 ) ( le_csInf ⟨ k, hk₂.2 ⟩ fun n hn => le_of_not_gt fun h => hn <| hk₂.1 n h )

/-
`firstDiff y ·` is locally constant away from `y` (the codomain `ℕ` is discrete).
-/
lemma firstDiff_eventuallyEq (y v : Baire) (h : v ≠ y) :
    ∀ᶠ w in nhds v, firstDiff y w = firstDiff y v := by
  have hv_ray : v ∈ RaySet Set.univ y (firstDiff y v) := by
    exact firstDiff_mem_raySet y v h;
  set N := {w : Baire | ∀ k ≤ firstDiff y v, w k = v k} with hN_def;
  have hN_nhds : N ∈ nhds v := by
    rw [ nhds_pi ];
    simp +decide [ Filter.mem_pi, hN_def ];
    exact ⟨ Finset.Iic ( firstDiff y v ), Finset.finite_toSet _, fun k => { v k }, fun k => by simp +decide, fun w hw k hk => by simpa using hw k ( Finset.mem_Iic.mpr hk ) ⟩;
  filter_upwards [ hN_nhds ] with w hw;
  apply firstDiff_eq_of_mem y w (firstDiff y v);
  exact ⟨ Set.mem_univ _, fun k hk => by have := hw k hk.le; have := hv_ray.2.1 k hk; aesop, by have := hw ( firstDiff y v ) le_rfl; have := hv_ray.2.2; aesop ⟩

/-
If `v n → y` with all `v n ≠ y`, the ray indices tend to infinity.
-/
lemma firstDiff_tendsto_atTop {y : Baire} {v : ℕ → Baire}
    (h : Filter.Tendsto v Filter.atTop (nhds y)) (hne : ∀ n, v n ≠ y) :
    Filter.Tendsto (fun n => firstDiff y (v n)) Filter.atTop Filter.atTop := by
  rw [ Filter.tendsto_atTop_atTop ];
  intro M; have := h; rw [ tendsto_pi_nhds ] at this; simp_all +decide;
  choose N hN using this; use Finset.sup ( Finset.range M ) N; intro n hn; refine' le_csInf _ _ <;> norm_num at *; (
  exact Function.ne_iff.mp ( hne n ) |> Exists.imp fun k hk => by aesop;);
  exact fun k hk => not_lt.1 fun contra => hk <| hN k n <| hn k contra

/-- The underlying Baire map of the upper-bound reduction: a point of `caseB_U` whose
`G`-value is `y` goes to `0^ω`; otherwise it goes to the block `firstDiff y v - j`
embedding of the point. -/
noncomputable def raySigma0 (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (j : ℕ)
    (a : ↥S) : Baire :=
  if G.func a.val = y then zeroStream
  else prependZerosOne (firstDiff y (G.func a.val) - j) a.val.val

/-
Points of `S` (excluded from the low rays `< j`) whose value is not `y` lie in a ray of
index `≥ j`.
-/
lemma rayFirstDiff_ge (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (j : ℕ)
    (hlow : ∀ a ∈ S, ∀ i, i < j → G.func a ∉ RaySet Set.univ y i)
    (a : ↥S) (h : G.func a.val ≠ y) :
    j ≤ firstDiff y (G.func a.val) := by
  exact le_of_not_gt fun contra =>
    hlow a.val a.property _ contra (firstDiff_mem_raySet _ _ h)

/-- Membership of `a.val.val` in the block `firstDiff - j` of the shifted ray sequence:
the point lies in `T` (since `S ⊆ T`) and in the ray of its first-difference index. -/
lemma raySigma0_block_mem (G : ScatFun) (y : Baire) (S T : Set ↑G.domain) (j : ℕ)
    (hST : S ⊆ T)
    (hlow : ∀ a ∈ S, ∀ i, i < j → G.func a ∉ RaySet Set.univ y i)
    (a : ↥S) (hy : G.func a.val ≠ y) :
    a.val.val ∈ (rayShiftSeq G y T j (firstDiff y (G.func a.val) - j)).domain := by
  have hge : j ≤ firstDiff y (G.func a.val) := rayFirstDiff_ge G y S j hlow a hy
  refine ⟨a.val.property, hST a.property, ?_⟩
  show G.func a.val ∈ RaySet Set.univ y (firstDiff y (G.func a.val) - j + j)
  rw [Nat.sub_add_cancel hge]
  exact firstDiff_mem_raySet _ _ hy

lemma raySigma0_mem (G : ScatFun) (y : Baire) (S T : Set ↑G.domain) (j : ℕ)
    (hST : S ⊆ T)
    (hlow : ∀ a ∈ S, ∀ i, i < j → G.func a ∉ RaySet Set.univ y i)
    (a : ↥S) :
    raySigma0 G y S j a ∈ (ScatFun.pgl (rayShiftSeq G y T j)).domain := by
  rw [ScatFun.pgl_domain]
  unfold raySigma0
  split_ifs with hy
  · exact zeroStream_mem_pointedGluingSet _
  · exact prependZerosOne_mem_pointedGluingSet _ _ _
      (raySigma0_block_mem G y S T j hST hlow a hy)

lemma raySigma0_func (G : ScatFun) (y : Baire) (S T : Set ↑G.domain) (j : ℕ)
    (hST : S ⊆ T)
    (hlow : ∀ a ∈ S, ∀ i, i < j → G.func a ∉ RaySet Set.univ y i)
    (a : ↥S) :
    (ScatFun.pgl (rayShiftSeq G y T j)).func
        ⟨raySigma0 G y S j a, raySigma0_mem G y S T j hST hlow a⟩
      = if G.func a.val = y then zeroStream
        else prependZerosOne (firstDiff y (G.func a.val) - j) (G.func a.val) := by
  unfold raySigma0
  split_ifs with hy
  · exact ScatFun.pgl_func_zeroStream _ _
  · -- Block-`(firstDiff - j)` of `rayShiftSeq` acts as `G.func`; the block value equals
    -- `G.func a.val` (the restrict re-realization recovers the same point).
    have hge : j ≤ firstDiff y (G.func a.val) := rayFirstDiff_ge G y S j hlow a hy
    set k := firstDiff y (G.func a.val) - j with hk
    have hblk := ScatFun.pgl_func_block (rayShiftSeq G y T j) k
      ⟨a.val.val, raySigma0_block_mem G y S T j hST hlow a hy⟩
    simp only at hblk
    rw [hblk]
    congr 1

lemma raySigma0_continuous (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (j : ℕ) :
    Continuous (raySigma0 G y S j) := by
  apply sufficient_cond_continuity;
  any_goals exact { a : ↥S | G.func a.val ≠ y };
  · exact isOpen_compl_iff.mpr ( isClosed_eq ( G.hCont.comp continuous_subtype_val ) continuous_const );
  · intro a ha;
    have h_eventually_eq : ∀ᶠ b in nhds a, firstDiff y (G.func b.val) = firstDiff y (G.func a.val) := by
      have h_eventually_eq : Filter.Tendsto (fun b : ↥S => G.func b.val) (nhds a) (nhds (G.func a.val)) := by
        exact G.hCont.continuousAt.comp ( continuous_subtype_val.continuousAt );
      exact h_eventually_eq.eventually ( firstDiff_eventuallyEq y ( G.func a.val ) ha );
    refine' ContinuousWithinAt.congr_of_eventuallyEq _ _ _;
    use fun b => prependZerosOne ( firstDiff y ( G.func a.val ) - j ) b.val.val;
    · exact Continuous.continuousWithinAt ( continuous_prependZerosOne _ |> Continuous.comp <| continuous_subtype_val.comp <| continuous_subtype_val );
    · filter_upwards [ self_mem_nhdsWithin, h_eventually_eq.filter_mono inf_le_left ] with b hb₁ hb₂ ; unfold raySigma0 ; aesop;
    · unfold raySigma0; aesop;
  · exact continuousOn_const.congr fun a ha => if_pos <| by aesop;
  · intro x_1 a hx_1 ha hx_1_tendsto
    have h_tendsto_zero : Filter.Tendsto (fun n => firstDiff y (G.func (x_1 n).val) - j) Filter.atTop Filter.atTop := by
      have h_tendsto_zero : Filter.Tendsto (fun n => firstDiff y (G.func (x_1 n).val)) Filter.atTop Filter.atTop := by
        apply firstDiff_tendsto_atTop;
        · convert G.hCont.continuousAt.tendsto.comp ( continuous_subtype_val.continuousAt.tendsto.comp hx_1_tendsto ) using 1 ; aesop;
        · exact hx_1;
      exact Filter.tendsto_atTop_atTop.mpr fun n => by rcases Filter.eventually_atTop.mp ( h_tendsto_zero.eventually_ge_atTop ( n + j ) ) with ⟨ m, hm ⟩ ; exact ⟨ m, fun k hk => Nat.le_sub_of_add_le ( by linarith [ hm k hk ] ) ⟩ ;
    have h_tendsto_zero : Filter.Tendsto (fun n => prependZerosOne (firstDiff y (G.func (x_1 n).val) - j) (x_1 n).val.val) Filter.atTop (nhds zeroStream) := by
      apply prependZerosOne_tendsto_zeroStream h_tendsto_zero;
    convert h_tendsto_zero using 1;
    · exact funext fun n => if_neg ( hx_1 n );
    · unfold raySigma0; aesop;

/-
`firstNonzero` is locally constant away from `zeroStream`.
-/
lemma firstNonzero_eventuallyEq (w : Baire) (h : w ≠ zeroStream) :
    ∀ᶠ w' in nhds w, firstNonzero w' = firstNonzero w := by
  refine' Filter.eventually_of_mem ( _ ) _;
  exact { x : Baire | ∀ k ≤ firstNonzero w, x k = w k };
  · rw [ nhds_pi ];
    simp +decide [ Filter.mem_pi ];
    exact ⟨ Finset.Iic ( firstNonzero w ), Finset.finite_toSet _, fun k => { w k }, fun k => by simp +decide, fun x hx k hk => by simpa using hx k ( Finset.mem_Iic.mpr hk ) ⟩;
  · intro x hx; unfold firstNonzero; simp +decide;
    split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
    · grind +suggestions;
    · exact h ( funext ‹_› );
    · grind +suggestions

/-- **Canonical reduction into the gluing of rays.**  A `ScatFun` `G` restricted to a
set `S` continuously reduces to the pointed gluing of its rays at `y` taken on a
superset `T ⊇ S`, with the first `j` blocks dropped (these rays are assumed empty on
`S`, via `hlow`).  The reduction sends a point of value `y` to `0^ω`, and a point in
ray `k ≥ j` to block `k - j`.

This is the constructive "rays as upper bound" statement; the degenerate
`pointedGluing_rays_upper_bound` could not be used because its conclusion was purely
existential and its blocks were not the rays.  The parameters `T ⊇ S` (restriction
invariance) and `j` (shift / dropping of empty low blocks) make it reusable. -/
lemma pgl_reduces_of_rays (G : ScatFun) (y : Baire) (S T : Set ↑G.domain) (j : ℕ)
    (hST : S ⊆ T)
    (hlow : ∀ a ∈ S, ∀ i, i < j → G.func a ∉ RaySet Set.univ y i) :
    ContinuouslyReduces
      (G.func ∘ (Subtype.val : ↥S → ↑G.domain))
      (ScatFun.pgl (rayShiftSeq G y T j)).func := by
  use fun a => ⟨raySigma0 G y S j a, raySigma0_mem G y S T j hST hlow a⟩, (raySigma0_continuous G y S j).subtype_mk _;
  refine' ⟨ fun w => if w = zeroStream then y else stripZerosOne ( firstNonzero w ) w, _, _ ⟩ <;> norm_num +zetaDelta at *;
  · intro w hw; by_cases hw' : w = zeroStream <;> simp_all +decide [ ContinuousWithinAt ] ;
    · rw [ tendsto_pi_nhds ];
      intro k; rw [ nhdsWithin ] ; simp +decide [ Filter.Tendsto ] ;
      refine' Filter.mem_inf_principal.mpr _;
      refine' Filter.mem_of_superset ( _ ) _;
      exact { w' : Baire | ∀ i ≤ k, w' i = 0 };
      · rw [ nhds_pi ];
        simp +decide [ Filter.mem_pi, zeroStream ];
        exact ⟨ Finset.Iic k, Finset.finite_toSet _, fun _ => { 0 }, fun _ => by simp +decide, fun w hw => fun i hi => by simpa using hw i ( Finset.mem_Iic.mpr hi ) ⟩;
      · intro w' hw' hw''; obtain ⟨ a, rfl ⟩ := hw''; simp_all +decide [ raySigma0_func ] ;
        split_ifs at * <;> simp_all +decide [ prependZerosOne ];
        specialize hw' ( firstDiff y ( G.func a.val ) - j ) ; simp_all +decide [ Nat.sub_add_cancel ( rayFirstDiff_ge G y S j ( fun c hc => hlow c.val c.property hc ) a ‹_› ) ] ;
        have := firstDiff_mem_raySet y ( G.func a.val ) ‹_›; simp_all +decide [ RaySet ] ;
        rw [ firstNonzero_prependZerosOne ];
        rw [ stripZerosOne_prependZerosOne ] ; linarith [ this.1 k ( by linarith ) ] ;
    · refine' Filter.Tendsto.congr' _ _;
      use fun w' => stripZerosOne ( firstNonzero w ) w';
      · rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
        filter_upwards [ firstNonzero_eventuallyEq w hw', IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) hw' ] with x hx₁ hx₂ ; aesop;
      · refine' Continuous.continuousWithinAt _;
        exact continuous_pi fun _ => continuous_apply _;
  · intro a ha hb; split_ifs <;> simp_all +decide [ raySigma0_func ] ;
    · grind +suggestions;
    · grind +suggestions

/-- **Rays as upper bound (`ScatFun` form).**  Every `ScatFun` `G` continuously reduces
to the pointed gluing of *all* its rays at any base point `y`.  This is the constructive
replacement for the (degenerate, existential) `pointedGluing_rays_upper_bound`: the
blocks here are genuinely the rays `G.rayOn y univ i`, and the reduction is the canonical
one.  It is the `S = T = univ`, `j = 0` instance of `pgl_reduces_of_rays`. -/
lemma ScatFun.reduces_pgl_rays (G : ScatFun) (y : Baire) :
    ContinuouslyReduces G.func
      (ScatFun.pgl (fun i => G.rayOn y Set.univ i)).func := by
  have h := pgl_reduces_of_rays G y Set.univ Set.univ 0 (le_refl _)
    (fun a _ i hi => absurd hi (Nat.not_lt_zero i))
  -- `rayShiftSeq G y univ 0 = fun i => G.rayOn y univ (i + 0)` is defeq to `fun i => G.rayOn y univ i`,
  -- and the domain `↥(univ)` is homeomorphic to `↑G.domain`, removing the `∘ Subtype.val`.
  let e : (Set.univ : Set ↑G.domain) ≃ₜ ↑G.domain :=
    { toFun := Subtype.val, invFun := fun a => ⟨a, Set.mem_univ a⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      continuous_toFun := continuous_subtype_val,
      continuous_invFun := continuous_id.subtype_mk _ }
  have h2 := h.comp_homeomorph_left e.symm
  have heq : (G.func ∘ (Subtype.val : ↥(Set.univ : Set ↑G.domain) → ↑G.domain)) ∘ e.symm
      = G.func := rfl
  rwa [heq] at h2

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
    refine' ⟨ _, _, _, _, _, _, _ ⟩;
    use fun z => ⟨ σ z |>.1, by
      simp +decide [ caseB_U, ScatFun.rayOn ] at *;
      simp +decide [ ScatFun.restrict ] at *;
      simp +decide [ ScatFun.cyl ] at *;
      simp +decide [ nbhd', RaySet ] at *;
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
      simp +decide [ ScatFun.restrictEquiv ] at *;
      simp +decide [ RaySet ] at *;
      rw [ mem_closure_iff_seq_limit ];
      simp +decide [ hfx, tendsto_pi_nhds ];
      intro x_1 hx_1
      use i';
      intro n; obtain ⟨ a, ha, ha' ⟩ := hx_1 n; use n; simp +decide;
      grind +splitImp;
  · unfold ScatFun.Reduces; simp +decide [ ScatFun.pgl, ScatFun.restrict ] ;
    grind +suggestions

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
