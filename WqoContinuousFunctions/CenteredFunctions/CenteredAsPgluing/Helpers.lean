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

noncomputable section

/-!
# §4.1 — Rays of a function and the pointed-gluing-of-rays machinery (helpers)

Ray machinery (`ScatFun.rayOn`, `pgl_reduces_of_rays`, `reduces_pgl_rays`, …) and the
monotonization skeleton (`glWindow`, `exists_monotone_pgl_equiv`) underpinning Theorem 4.6
(CenteredAsPgluing).  Extracted from `LocallyCentered/Helpers.lean` so it is upstream of
`CenteredAsPgluing` and `finitenessOfCenteredFunctions`.
-/

/-- The `i`-th ray of a `ScatFun` `G` at base point `y`, intersected with a subset `S`
of the domain, packaged as a `ScatFun` via `G.restrict`. -/
noncomputable def ScatFun.rayOn (G : ScatFun) (y : Baire) (S : Set ↑G.domain) (i : ℕ) :
    ScatFun :=
  G.restrict (S ∩ {a | G.func a ∈ RaySet Set.univ y i})


/-- The rays of `G` at `y` on a set `T`, shifted to start at index `j` (block `i` is
the ray of index `i + j`).  This is the block sequence used in the canonical reduction
of a function into the pointed gluing of its rays. -/
noncomputable def rayShiftSeq (G : ScatFun) (y : Baire) (T : Set ↑G.domain) (j : ℕ) :
    ℕ → ScatFun :=
  fun i => G.rayOn y T (i + j)


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


/-!
## Monotonization of a `pgl`-regular ray sequence (forward direction of Theorem 4.6)

The remaining content of `monotone_pgluing_of_centered`: given the rays `R` of a centered
function, produce a `≤`-monotone sequence `g` with `pgl g ≡ pgl R`.  The construction
follows the provided solution (`4_centered_memo.tex`): deep, pairwise-disjoint finite
windows of rays, glued.

The pieces are stated here and wired together in `exists_monotone_pgl_equiv`; the four
genuinely-combinatorial facts — `rays_glRegular`, `exists_monotone_windows`,
`pgl_le_pgl_window_of_reg`, `pgl_le_pgl_of_monotone_cover` — are isolated below and are all
fully proved (via the shared `glWindow` helpers `glWindow_reduces_of_subset`,
`gl_glWindow_flatten`, `glWindow_redistribute`, and the rigidity bridge
`union_rays_reduces_glWindow`).
-/

/-- The **finite window gluing** of a ray sequence `R`: the plain gluing whose block `k` is
`R k` for `m ≤ k ≤ M` and empty otherwise.  Formal rendering of `gl_{i=m}^{M} R_i`. -/
def glWindow (R : ℕ → ScatFun) (m M : ℕ) : ScatFun :=
  ScatFun.gl (fun k => if m ≤ k ∧ k ≤ M then R k else ScatFun.empty)

/-
The block index `x.val 0` of a point in a window lies in `[m, M]`.
-/
lemma glWindow_val0_mem (R : ℕ → ScatFun) (m M : ℕ) (x : ↥(glWindow R m M).domain) :
    m ≤ x.val 0 ∧ x.val 0 ≤ M := by
  have h_k : ∃ k, x.val 0 = k ∧ unprepend x.val ∈ (if m ≤ k ∧ k ≤ M then R k else ScatFun.empty).domain := by
    convert GluingSet_inverse_short _ _;
  unfold ScatFun.empty at h_k; aesop;

/-
A window reduces into any larger window (`[m, M] ⊆ [m', M']`).
-/
lemma glWindow_reduces_of_subset (R : ℕ → ScatFun) {m M m' M' : ℕ}
    (hm : m' ≤ m) (hM : M ≤ M') :
    ScatFun.Reduces (glWindow R m M) (glWindow R m' M') := by
  refine' ⟨ _, _, _ ⟩;
  exact fun x => ⟨ x.val, by
    unfold glWindow at *; simp_all +decide [ ScatFun.gl ] ;
    obtain ⟨ k, hk ⟩ := x.2;
    rcases hk with ⟨ ⟨ i, rfl ⟩, hk ⟩ ; simp_all +decide [ GluingSet ] ;
    split_ifs at hk <;> simp_all +decide [ ScatFun.empty ];
    grind ⟩
  all_goals generalize_proofs at *;
  · fun_prop;
  · refine' ⟨ fun x => x, _, _ ⟩ <;> norm_num;
    · exact continuousOn_id;
    · unfold glWindow ScatFun.gl;
      unfold GluingSet GluingFunVal ScatFun.glBlock; simp +decide ;
      grind +suggestions

/-
**Flattening of disjoint sub-windows.**  If `kof : ℕ → ℕ` inverts the sub-window
assignment (`kof j = k` whenever `c k ≤ j ≤ d k`) and every nonempty sub-window
`[c k, d k]` is contained in `[q, Q]`, then the plain gluing of the sub-windows
`gl (fun k => glWindow R (c k) (d k))` reduces to the single window `glWindow R q Q`.
-/
lemma gl_glWindow_flatten (R : ℕ → ScatFun) (c d : ℕ → ℕ) (q Q : ℕ) (kof : ℕ → ℕ)
    (hcontain : ∀ k, c k ≤ d k → q ≤ c k ∧ d k ≤ Q)
    (hkof : ∀ k j, c k ≤ j → j ≤ d k → kof j = k) :
    ScatFun.Reduces (ScatFun.gl (fun k => glWindow R (c k) (d k))) (glWindow R q Q) := by
  refine' ⟨ _, _, _ ⟩;
  use fun x => ⟨fun i => if i = 0 then x.val 1 else x.val (i + 1), by
    obtain ⟨ k, hk ⟩ := x.2;
    obtain ⟨ ⟨ k, rfl ⟩, hk ⟩ := hk;
    obtain ⟨ y, hy, hy' ⟩ := hk;
    obtain ⟨ j, hj ⟩ := hy;
    obtain ⟨ ⟨ i, rfl ⟩, hi ⟩ := hj;
    obtain ⟨ z, hz, hz' ⟩ := hi;
    unfold glWindow; simp +decide [ ← hy', ← hz' ] ;
    unfold prepend at *; simp_all +decide [ GluingSet ] ;
    use i, z;
    split_ifs at * <;> simp_all +decide [ funext_iff, prepend ];
    · exact False.elim <| hz.elim;
    · grind⟩;
  · refine' Continuous.subtype_mk _ _;
    exact continuous_pi fun i => by split_ifs <;> [ exact continuous_apply 1 |> Continuous.comp <| continuous_subtype_val; exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val ] ;
  · refine' ⟨ fun y => _, _, _ ⟩;
    exact fun i => if i = 0 then kof ( y 0 ) else y ( i - 1 );
    · exact Continuous.continuousOn ( by continuity );
    · intro x
      simp [ScatFun.gl, glWindow];
      unfold GluingFunVal ScatFun.glBlock; simp +decide ;
      unfold unprepend; simp +decide [ prepend ] ;
      ext i; rcases i with ( _ | _ | i ) <;> simp +decide [ prepend ] ;
      · have := GluingSet_inverse_short ( fun k => ( glWindow R ( c k ) ( d k ) ).domain ) x;
        obtain ⟨ k, hk₁, hk₂ ⟩ := this; specialize hkof k ( x.val 1 ) ; simp_all +decide ;
        exact Eq.symm ( hkof ( by have := glWindow_val0_mem ( R := R ) ( m := c k ) ( d k ) ⟨ unprepend x.val, hk₂ ⟩ ; aesop ) ( by have := glWindow_val0_mem ( R := R ) ( m := c k ) ( d k ) ⟨ unprepend x.val, hk₂ ⟩ ; aesop ) );
      · split_ifs <;> simp_all +decide [ ScatFun.empty ];
        · grind;
        · grind +qlia

/-
**Disjoint sub-window allocation.**  Processing the indices `[m, M]` left to right
with a cursor starting at `q`, allocate to each ray `R k` (`k ∈ [m, M]`) its own
sub-window `[c k, d k]` obtained from `hreg`, so that the windows are pairwise disjoint,
contained in `[q, Q]`, and inverted by `kof`.  Outside `[m, M]` the block is empty so the
placeholder window may be empty (`d k < c k`).
-/
lemma exists_disjoint_subwindows (R : ℕ → ScatFun)
    (hreg : ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧ ScatFun.Reduces (R n) (glWindow R m M))
    (m M q : ℕ) :
    ∃ (c d kof : ℕ → ℕ) (Q : ℕ), q ≤ Q ∧
      (∀ k, ScatFun.Reduces (if m ≤ k ∧ k ≤ M then R k else ScatFun.empty)
        (glWindow R (c k) (d k))) ∧
      (∀ k, c k ≤ d k → q ≤ c k ∧ d k ≤ Q) ∧
      (∀ k j, c k ≤ j → j ≤ d k → kof j = k) := by
  by_contra h_contra;
  -- Define the cursor `cur` by `Nat.rec`: `cur 0 = q`, and
  -- `cur (k+1) = if (m ≤ k ∧ k ≤ M) then (Classical.choose (hreg (cur k) k)) + 1 else cur k`.
  set cur : ℕ → ℕ := fun k =>
    Nat.rec q (fun k cur_k =>
      if m ≤ k ∧ k ≤ M then (Classical.choose (hreg cur_k k)) + 1 else cur_k) k;
  refine' h_contra ⟨ fun k => if m ≤ k ∧ k ≤ M then cur k else 1, fun k => if m ≤ k ∧ k ≤ M then Classical.choose ( hreg ( cur k ) k ) else 0, fun j => if h : ∃ k, m ≤ k ∧ k ≤ M ∧ cur k ≤ j ∧ j ≤ Classical.choose ( hreg ( cur k ) k ) then h.choose else 0, cur ( M + 1 ), _, _, _, _ ⟩;
  · -- By definition of `cur`, we know that `cur k` is non-decreasing.
    have h_cur_mono : ∀ k, cur k ≤ cur (k + 1) := by
      grind;
    exact Nat.recOn ( M + 1 ) ( by rfl ) fun k hk => le_trans hk ( h_cur_mono k );
  · intro k; split_ifs <;> simp_all +decide [ ScatFun.empty_reduces ] ;
    exact Classical.choose_spec ( hreg ( cur k ) k ) |>.2;
  · intro k hk; by_cases hk' : m ≤ k ∧ k ≤ M <;> simp +decide [ hk' ] at hk ⊢;
    have h_cur_mono : ∀ k, cur k ≤ cur (k + 1) := by
      grind;
    refine' ⟨ _, _ ⟩;
    · exact Nat.recOn k ( by rfl ) fun k ih => le_trans ih ( h_cur_mono k );
    · refine' Nat.le_induction _ _ M hk'.2 <;> intros <;> simp_all +decide; all_goals grind;
  · intro k j hj₁ hj₂;
    by_cases hk : m ≤ k ∧ k ≤ M <;> simp +decide [ hk ] at hj₁ hj₂ ⊢;
    · split_ifs with h;
      · have h_unique : ∀ k' k'', m ≤ k' ∧ k' ≤ M ∧ m ≤ k'' ∧ k'' ≤ M → k' < k'' → choose (hreg (cur k') k') < cur k'' := by
          intros k' k'' hk' hk'';
          induction' hk'' with k'' hk'' ih; all_goals grind;
        grind;
      · exact False.elim <| h ⟨ k, hk.1, hk.2, hj₁, hj₂ ⟩;
    · linarith

/-- **Deep redistribution of a window.**  Using `glWindow`-regularity, a window
`glWindow R m M` reduces into a *deep* window `glWindow R q Q` (all of whose blocks have
index `≥ q`): each ray of `[m, M]` is pushed, via `hreg`, into its own disjoint
sub-window of `[q, Q]`. -/
lemma glWindow_redistribute (R : ℕ → ScatFun)
    (hreg : ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧ ScatFun.Reduces (R n) (glWindow R m M))
    (m M q : ℕ) :
    ∃ Q : ℕ, q ≤ Q ∧ ScatFun.Reduces (glWindow R m M) (glWindow R q Q) := by
  obtain ⟨c, d, kof, Q, hQ, hred, hcont, hkof⟩ := exists_disjoint_subwindows R hreg m M q
  exact ⟨Q, hQ, ContinuouslyReduces.trans
    (ScatFun.gl_reduces_of_pointwise _ (fun k => glWindow R (c k) (d k)) hred)
    (gl_glWindow_flatten R c d q Q kof hcont hkof)⟩

/-
The function of a `ScatFun.restrict` re-realizes the original point: its value at a
domain point `x` (whose underlying `Baire` value lies in `F.domain` via `h`) is
`F.func ⟨x.val, h⟩`.
-/
lemma restrict_func_eq (F : ScatFun) (S : Set ↑F.domain) (x : ↑(F.restrict S).domain)
    (h : x.val ∈ F.domain) :
    (F.restrict S).func x = F.func ⟨x.val, h⟩ := by
  convert congr_arg ( fun x : ↑F.domain => F.func x ) _ using 1
  generalize_proofs at *;
  exact Subtype.ext rfl

/-- The value of a ray's function re-realizes the original point. -/
lemma rayOn_func_eq (F : ScatFun) (y : Baire) (i : ℕ) (z : ↑(F.rayOn y Set.univ i).domain)
    (h : z.val ∈ F.domain) :
    (F.rayOn y Set.univ i).func z = F.func ⟨z.val, h⟩ :=
  restrict_func_eq F _ z h

/-
Value of a window's function on a block point `prepend i w` with `i ∈ [m, M]`:
it acts as `R i` on the payload, prefixed by the block tag `i`.
-/
lemma glWindow_func_prepend (R : ℕ → ScatFun) (m M i : ℕ) (hi : m ≤ i) (hi' : i ≤ M)
    (w : Baire) (hw : w ∈ (R i).domain)
    (hmem : prepend i w ∈ (glWindow R m M).domain) :
    (glWindow R m M).func ⟨prepend i w, hmem⟩ = prepend i ((R i).func ⟨w, hw⟩) := by
  convert GluingFunVal_prepend ( fun k => ( if m ≤ k ∧ k ≤ M then R k else ScatFun.empty ).domain ) ( fun _ => Set.univ ) ( ScatFun.glBlock fun k => if m ≤ k ∧ k ≤ M then R k else ScatFun.empty ) i ⟨ w, ?_ ⟩ hmem using 1;
  unfold ScatFun.glBlock; simp +decide [ * ] ;
  grind +splitImp;
  grind

/-- A block point `prepend i w` with `i ∈ [m, M]` and `w ∈ (R i).domain` lies in the
window's domain. -/
lemma mem_glWindow_prepend (R : ℕ → ScatFun) {m M i : ℕ} (hi : m ≤ i) (hi' : i ≤ M)
    {w : Baire} (hw : w ∈ (R i).domain) :
    prepend i w ∈ (glWindow R m M).domain := by
  apply mem_gluingSet_prepend
    (A := fun k => (if m ≤ k ∧ k ≤ M then R k else ScatFun.empty).domain)
  show w ∈ (if m ≤ i ∧ i ≤ M then R i else ScatFun.empty).domain
  rw [if_pos ⟨hi, hi'⟩]; exact hw

/-- **Union of rays reduces to its window gluing.**  The function `F` restricted to the
union of its rays of indices in `[m, M]` (at base point `y`) reduces to the finite window
gluing of those rays.  The rays are pairwise-disjoint clopen sets, so the union is their
disjoint gluing. -/
lemma union_rays_reduces_glWindow (F : ScatFun) (y : Baire) (m M : ℕ) :
    ContinuouslyReduces
      (fun (x : {a : ↑F.domain | ∃ i, m ≤ i ∧ i ≤ M ∧
          (∀ k, k < i → F.func a k = y k) ∧ F.func a i ≠ y i}) => F.func x.val)
      (glWindow (fun i => F.rayOn y Set.univ i) m M).func := by
  -- For a point `x` of the source, the unique ray index is `firstDiff y (F.func x.val)`,
  -- which lies in `[m, M]`; map `x` to that block of the window, carrying `x.val.val`.
  have hidx : ∀ (x : {a : ↑F.domain | ∃ i, m ≤ i ∧ i ≤ M ∧
        (∀ k, k < i → F.func a k = y k) ∧ F.func a i ≠ y i}),
      m ≤ firstDiff y (F.func x.val) ∧ firstDiff y (F.func x.val) ≤ M ∧ F.func x.val ≠ y := by
    intro x
    obtain ⟨i, hi₁, hi₂, hi₃, hi₄⟩ := x.2
    have hmem : F.func x.val ∈ RaySet Set.univ y i := ⟨Set.mem_univ _, hi₃, hi₄⟩
    have hfd : firstDiff y (F.func x.val) = i := firstDiff_eq_of_mem y _ i hmem
    exact ⟨hfd ▸ hi₁, hfd ▸ hi₂, fun h => hi₄ (by rw [h])⟩
  have hw : ∀ (x : {a : ↑F.domain | ∃ i, m ≤ i ∧ i ≤ M ∧
        (∀ k, k < i → F.func a k = y k) ∧ F.func a i ≠ y i}),
      x.val.val ∈ (F.rayOn y Set.univ (firstDiff y (F.func x.val))).domain := by
    intro x
    obtain ⟨_, _, hne⟩ := hidx x
    exact ⟨x.val.property, Set.mem_univ _, by
      have := firstDiff_mem_raySet y (F.func x.val) hne
      simpa using this⟩
  refine ⟨fun x => ⟨prepend (firstDiff y (F.func x.val)) x.val.val,
      mem_glWindow_prepend _ (hidx x).1 (hidx x).2.1 (hw x)⟩, ?_, fun w => unprepend w, ?_, ?_⟩
  · -- continuity of `σ`
    refine Continuous.subtype_mk ?_ _
    have hfd_cont : Continuous
        (fun x : {a : ↑F.domain | ∃ i, m ≤ i ∧ i ≤ M ∧
          (∀ k, k < i → F.func a k = y k) ∧ F.func a i ≠ y i} =>
          firstDiff y (F.func x.val)) := by
      refine continuous_iff_continuousAt.mpr fun a => ?_
      have hev : ∀ᶠ w in nhds (F.func a.val),
          firstDiff y w = firstDiff y (F.func a.val) :=
        firstDiff_eventuallyEq y (F.func a.val) (hidx a).2.2
      exact tendsto_nhds_of_eventually_eq
        (hev.filter_mono ((F.hCont.comp continuous_subtype_val).continuousAt))
    refine continuous_pi fun k => ?_
    rcases k with _ | k
    · simpa [prepend] using hfd_cont
    · simpa [prepend, unprepend] using
        (continuous_apply k).comp (continuous_subtype_val.comp continuous_subtype_val)
  · exact (continuous_unprepend).continuousOn
  · intro x
    obtain ⟨hm, hM, _⟩ := hidx x
    show F.func x.val = unprepend ((glWindow (fun i => F.rayOn y Set.univ i) m M).func _)
    rw [glWindow_func_prepend (fun i => F.rayOn y Set.univ i) m M
          (firstDiff y (F.func x.val)) hm hM x.val.val (hw x)
          (mem_glWindow_prepend _ hm hM (hw x)),
        unprepend_prepend, rayOn_func_eq F y _ ⟨x.val.val, hw x⟩ x.val.property]

/-
**Ray → window bridge (from rigidity).**  For the rays `R` of a centered `F` at its
cocenter, every ray reduces into a finite window of rays starting arbitrarily high:
`∀ m n, ∃ M ≥ m, R_n ≤ gl_{i=m}^{M} R_i`.  This is Item 3 of Proposition 4.4
(`rigidityOfCocenter_finiteGluing` at `F = G = F`), transported from rigidity's
union-of-rays form to the `glWindow` form.

TODO: derive from `rigidityOfCocenter_finiteGluing F F hF_cent hF_cent
(ContinuouslyEquiv.refl _)` plus a `union-of-rays ≡ glWindow` bridge.
-/
lemma rays_glRegular (F : ScatFun) (hF_cent : IsCentered F.func) :
    ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧
      ScatFun.Reduces (F.rayOn (cocenter F.func hF_cent) Set.univ n)
        (glWindow (fun i => F.rayOn (cocenter F.func hF_cent) Set.univ i) m M) := by
  intros m n
  obtain ⟨M, hmM, hrig⟩ := rigidityOfCocenter_finiteGluing F F hF_cent hF_cent (ContinuouslyEquiv.refl F.func) m n
  have hchain := hrig.trans (union_rays_reduces_glWindow F (cocenter F.func hF_cent) m M);
  refine' ⟨ M, hmM, _ ⟩;
  convert ContinuouslyReduces.comp_homeomorph_left hchain (Homeomorph.trans (F.restrictEquiv _) (Homeomorph.setCongr _)) using 1
  generalize_proofs at *;
  ext; simp [RaySet]

/-- **The deep, monotone window construction.**  From the `glWindow`-regularity of `R`,
build start/end points `a, b : ℕ → ℕ` of deep pairwise-disjoint windows `[a n, b n]` such
that each ray `R n` reduces into its window (covering) and consecutive windows are
`≤`-monotone.  This is the recursive core of the provided solution: choose
`a (n+1) > b n` (disjoint/deep), then `b (n+1)` large enough — via `hreg` — that every ray
`R i` of windows `≤ n` is dominated inside `[a (n+1), b (n+1)]`; monotonicity is then a
`gl`-flattening of the per-block reductions.

TODO: `Nat.rec` on the breakpoints + a `gl`-flattening lemma for the monotone step. -/
lemma exists_monotone_windows (R : ℕ → ScatFun)
    (hreg : ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧ ScatFun.Reduces (R n) (glWindow R m M)) :
    ∃ (a b : ℕ → ℕ),
      (∀ n, ScatFun.Reduces (R n) (glWindow R (a n) (b n))) ∧
      (∀ n, ScatFun.Reduces (glWindow R (a n) (b n))
        (glWindow R (a (n + 1)) (b (n + 1)))) := by
  -- Nested windows all starting at `0`, with right endpoint `b n = sup_{i ≤ n} Mb i`
  -- increasing.  Monotonicity is then mere window inclusion.
  choose Mb _hMb1 hMb2 using fun n => hreg 0 n
  refine ⟨fun _ => 0, fun n => (Finset.range (n + 1)).sup Mb, fun n => ?_, fun n => ?_⟩
  · exact ContinuouslyReduces.trans (hMb2 n)
      (glWindow_reduces_of_subset R (le_refl 0)
        (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n))))
  · exact glWindow_reduces_of_subset R (le_refl 0)
      (Finset.sup_mono (by intro x hx; simp only [Finset.mem_range] at *; omega))

/-
**`pgl` of windows ≤ `pgl R` (lower-bound direction).**  Each window block of
`pgl (fun n => glWindow R aₙ bₙ)` is a finite gluing of rays of `R`; `glWindow`-regularity
pushes those rays arbitrarily deep into `pgl R`, so `pgl (windows) ≤ pgl R` by the local
pointed-gluing criterion (`pgl_reduces_of_local`).

TODO: `pgl_reduces_of_local` at `0^ω`; per block use `hreg` to place the window deep, then
`gl_reduces_pgl_direct`.
-/
lemma pgl_le_pgl_window_of_reg (R : ℕ → ScatFun) (a b : ℕ → ℕ)
    (hreg : ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧ ScatFun.Reduces (R n) (glWindow R m M)) :
    ScatFun.Reduces (ScatFun.pgl (fun n => glWindow R (a n) (b n))) (ScatFun.pgl R) := by
  apply ScatFun.pgl_reduces_of_local (fun n => glWindow R (a n) (b n)) (ScatFun.pgl R) ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩
  intro n V hVopen hxV
  generalize_proofs at *;
  obtain ⟨q, hq⟩ := nbhd_basis' (ScatFun.pgl R).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hVopen hxV
  generalize_proofs at *;
  obtain ⟨Q, hqQ, hred1⟩ := glWindow_redistribute R hreg (a n) (b n) q
  generalize_proofs at *;
  obtain ⟨σ₁, hσ₁, τ₁, hτ₁, heq₁⟩ := hred1
  generalize_proofs at *;
  obtain ⟨σ₂, τ₂, hσ₂cont, hσ₂eq, hτ₂cont, hdeep, hone⟩ := ScatFun.gl_reduces_pgl_direct (fun k => if q ≤ k ∧ k ≤ Q then R k else ScatFun.empty) R id Function.injective_id (by
  intro k; by_cases hk : q ≤ k ∧ k ≤ Q <;> simp +decide [ hk ] ;
  exact Or.inr rfl)
  generalize_proofs at *;
  refine' ⟨ fun z => σ₂ ( σ₁ z ), fun w => τ₁ ( τ₂ w ), _, _, _, _, _ ⟩
  all_goals generalize_proofs at *;
  · exact hσ₂cont.comp hσ₁;
  · grind +locals;
  · refine' hτ₁.comp ( hτ₂cont.mono _ ) _;
    · exact Set.range_subset_iff.mpr fun x => ⟨ σ₁ x, rfl ⟩;
    · intro x hx; obtain ⟨ z, rfl ⟩ := hx; simp +decide [ ← hσ₂eq ] ;
      exact ⟨ _, z.2, rfl ⟩;
  · intro z
    generalize_proofs at *;
    refine' hq _;
    intro k hk; specialize hdeep ( σ₁ z ) k; simp_all +decide [ nbhd' ] ;
    exact hdeep ( by linarith [ glWindow_val0_mem R q Q ( σ₁ z ) ] );
  · have h_closure : closure (Set.range (fun z => (ScatFun.pgl R).func (σ₂ (σ₁ z)))) ⊆ ⋃ p ∈ Finset.Icc q Q, {w : Baire | w p = 1} := by
      refine' closure_minimal _ _;
      · rintro _ ⟨ z, rfl ⟩ ; specialize hone ( σ₁ z ) ; specialize hdeep ( σ₁ z ) ; simp_all +decide [ Finset.mem_Icc ] ;
        exact ⟨ _, glWindow_val0_mem R q Q ( σ₁ z ), hone ⟩;
      · exact isClosed_biUnion_finset fun _ _ => isClosed_eq ( continuous_apply _ ) continuous_const
    generalize_proofs at *;
    intro h; have := h_closure h; simp_all +decide [ Set.mem_iUnion ] ;
    obtain ⟨ i, hi, hi' ⟩ := this; have := ScatFun.pgl_func_zeroStream R; simp_all +decide [ zeroStream ] ;

/-- **`pgl R` ≤ `pgl g` for a monotone covering sequence (upper-bound direction).**  If `g`
is `≤`-monotone and each ray `R n` reduces into `g n`, then by monotonicity `R n` reduces
into `g m` for all `m ≥ n`; the rays are thus reducible by pieces to `g`, giving
`pgl R ≤ pgl g` by `pointedGluing_upper_bound`.

TODO: pieces `I_n = {n}`, reduction `R n ≤ g n`; feed `pointedGluing_upper_bound`. -/
lemma pgl_le_pgl_of_monotone_cover (R g : ℕ → ScatFun)
    (hmon : ∀ i j : ℕ, i ≤ j → ScatFun.Reduces (g i) (g j))
    (hcov : ∀ n, ScatFun.Reduces (R n) (g n)) :
    ScatFun.Reduces (ScatFun.pgl R) (ScatFun.pgl g) := by
  -- Cofinal covering: each `R i` reduces into `g j` for arbitrarily large `j`.
  have hcof : ∀ i m : ℕ, ∃ j, m ≤ j ∧ ScatFun.Reduces (R i) (g j) := fun i m =>
    ⟨max i m, le_max_right i m,
      ContinuouslyReduces.trans (hcov i) (hmon i (max i m) (le_max_left i m))⟩
  apply ScatFun.pgl_reduces_of_local
  intro i V hVopen hxV
  obtain ⟨m, hm⟩ := nbhd_basis' (ScatFun.pgl g).domain
    ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hVopen hxV
  obtain ⟨j, hjm, hj⟩ := hcof i m
  obtain ⟨σ', hσ', τ', hτ', h_eq⟩ := (ScatFun.reduces_iff _ _).1 hj
  refine ⟨fun z => ⟨prependZerosOne j (σ' z).val,
      prependZerosOne_mem_pointedGluingSet _ j _ (σ' z).prop⟩,
    fun w => τ' (stripZerosOne j w),
    ((continuous_prependZerosOne j).comp (continuous_subtype_val.comp hσ')).subtype_mk _,
    ?_, ?_, ?_, ?_⟩
  · intro z
    show (R i).func z = τ' (stripZerosOne j ((ScatFun.pgl g).func _))
    rw [ScatFun.pgl_func_block, stripZerosOne_prependZerosOne]
    exact h_eq z
  · refine hτ'.comp (continuous_stripZerosOne j).continuousOn ?_
    rintro _ ⟨z, rfl⟩
    dsimp only
    rw [ScatFun.pgl_func_block, stripZerosOne_prependZerosOne]
    exact ⟨z, rfl⟩
  · intro z
    refine hm ?_
    intro k hk
    have : prependZerosOne j (σ' z).val k = 0 :=
      prependZerosOne_head_eq_zero j _ k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjm)
    simpa [zeroStream] using this
  · rw [ScatFun.pgl_func_zeroStream]
    have hsub : Set.range (fun z => (ScatFun.pgl g).func
        (⟨prependZerosOne j (σ' z).val, prependZerosOne_mem_pointedGluingSet _ j _ (σ' z).prop⟩ :
          ↑(ScatFun.pgl g).domain)) ⊆ {w : Baire | w j = 1} := by
      rintro _ ⟨z, rfl⟩
      dsimp only
      rw [ScatFun.pgl_func_block]
      exact prependZerosOne_at_i j _
    intro hcl
    have : zeroStream ∈ {w : Baire | w j = 1} :=
      (IsClosed.closure_subset_iff (isClosed_eq (continuous_apply j) continuous_const)).2
        hsub hcl
    simp [zeroStream] at this

/-- **Monotonization (abstract), fully wired.**  A `glWindow`-regular sequence `R` admits a
`≤`-monotone sequence `g` with `pgl g ≡ pgl R`.  Combines the four facts above; this lemma
itself carries no `sorry`. -/
lemma exists_monotone_pgl_equiv (R : ℕ → ScatFun)
    (hreg : ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧ ScatFun.Reduces (R n) (glWindow R m M)) :
    ∃ (g : ℕ → ScatFun), IsMonotoneSeq g ∧
      ContinuouslyEquiv (ScatFun.pgl g).func (ScatFun.pgl R).func := by
  obtain ⟨a, b, hcov, hmon_step⟩ := exists_monotone_windows R hreg
  -- Iterate the one-step reduction to full monotonicity.
  have hg_mono : ∀ i j : ℕ, i ≤ j →
      ScatFun.Reduces (glWindow R (a i) (b i)) (glWindow R (a j) (b j)) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact ContinuouslyReduces.refl _
    | succ j _ ih => exact ContinuouslyReduces.trans ih (hmon_step j)
  exact ⟨fun n => glWindow R (a n) (b n), hg_mono,
    pgl_le_pgl_window_of_reg R a b hreg,
    pgl_le_pgl_of_monotone_cover R (fun n => glWindow R (a n) (b n)) hg_mono hcov⟩


end