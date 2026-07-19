import WqoContinuousFunctions.ScatFun.FiniteGluing
import WqoContinuousFunctions.ScatFun.RestrictReduces
import GeneralTopology.DiscreteSubspaces
import GeneralTopology.DisjointOpenNeighbourhoods
import Mathlib.Data.Nat.Nth

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# Intertwining reductions (memoir Lemma `Intertwinereductions`)

> Let `f : A → B` between metrizable spaces and `G ⊆ ℕ^ℕ` be finite. Suppose that for all
> `g ∈ G` there are infinitely many points `y ∈ B` such that for all neighbourhood `V` of `y`
> we have `g ≤ f ↾ V` (corestriction). Then `ω G ≤ f`.

Here everything is rendered at the `ScatFun` level.  The codomain space `B` is the Baire space
`ℕ → ℕ` (metrizable), the finite set `G` is a family `G : Fin n → ScatFun`, the corestriction
`f ↾ V` is `ScatFun.coRestrict f V`, and `ω G = ω (gl G)` is `ScatFun.omega (ScatFun.glFin G)`.

## Informal proof (memoir)

If `G` is empty then `ωG = ∅`, which reduces to anything.  Otherwise, for each `g ∈ G` let
`X_g = {y | ∀ V ∈ 𝓝 y, g ≤ f ↾ V}` (`IntertwineSet f g`); the hypothesis says each `X_g` is
infinite.  By `InfiniteEmbedOmegaStronger`
(`exists_pairwise_disjoint_infinite_discrete_subspaces`) we thin the `X_g` to pairwise disjoint
infinite `Y_g ⊆ X_g` with **discrete** union, giving an injective `(g, m) ↦ y^g_m` with discrete
image and `y^g_m ∈ X_g`.  Since `B` is metrizable and the image is discrete, there are pairwise
disjoint **open** `V^g_m ∋ y^g_m` (`exists_pairwise_disjoint_open_nhds`).  As `y^g_m ∈ X_g` and
`V^g_m` is a neighbourhood of `y^g_m`, we get `g ≤ f ↾ V^g_m`.  Then:

* `ωG ≤ gl_{(g,m)} g`              — ω-fold reindexing (`omega_glFin_reduces_reindex`),
* `gl_{(g,m)} g ≤ gl_{(g,m)} f ↾ V^g_m` — `Gluingcohomomorphism` (`gl_reduces_of_pointwise`),
* `gl_{(g,m)} f ↾ V^g_m ≤ f`        — gluing as a lower bound over pairwise-disjoint open sets
  (`gl_coRestrict_disjoint_open_reduces`, memoir `Gluingaslowerbound2`).

Composing the three gives `ωG ≤ f`.

## Status

Complete.  The three supporting lemmas `gl_coRestrict_disjoint_open_reduces`,
`exists_pairwise_disjoint_open_nhds`, and `omega_glFin_reduces_reindex` are all proved (the last
via the flattening lemma `gl_gl_flatten_reduces` and the support-form block embedding
`gl_reduces_of_blockEmbed_support`).  The upstream discrete-subspace input
`exists_pairwise_disjoint_infinite_discrete_subspaces` (in `GeneralTopology/DiscreteSubspaces.lean`) is
also now fully proved, so the whole `intertwine_reductions` chain is unconditional.
-/

namespace ScatFun

/-! ## Definitions -/

/-- **Corestriction** of `f` to a codomain set `V ⊆ Baire`: the restriction of `f` to the domain
piece `{z | f.func z ∈ V}`.  This is the `ScatFun` rendering of the memoir's `f ↾ V`
(`f\corestr{V}`).  Definitionally the same shape as `Fb` in `SimpleSuccessor/Prop411`. -/
def coRestrict (f : ScatFun) (V : Set Baire) : ScatFun :=
  f.restrict {z : ↑f.domain | f.func z ∈ V}

/-- **Corestriction is monotone** in the codomain set: if `V₀ ⊆ V` then `f ↾ V₀ ≤ f ↾ V`.
A direct corollary of `restrict_reduces_of_subset`, since `f ↾ V` restricts `f` to the domain
piece `{z | f.func z ∈ V}` and `V₀ ⊆ V` gives the inclusion of those pieces. -/
lemma coRestrict_reduces_of_subset (f : ScatFun) {V₀ V : Set Baire} (hsub : V₀ ⊆ V) :
    Reduces (coRestrict f V₀) (coRestrict f V) :=
  restrict_reduces_of_subset f (fun _ hz => hsub hz)

/-- **Domain-restrict-then-corestrict reduces into plain corestrict**: corestricting a further
domain-restriction `F.restrict D` to `V` reduces into corestricting `F` itself to `V` (points of
`F.restrict D` are, after all, just points of `F.domain` lying in `D`). Pure bookkeeping. -/
lemma coRestrict_restrict_reduces (F : ScatFun) (D : Set ↑F.domain) (V : Set Baire) :
    Reduces ((F.restrict D).coRestrict V) (F.coRestrict V) := by
  refine ⟨ fun x => ⟨ x.val, ?_ ⟩, ?_, fun x => x, continuousOn_id, ?_ ⟩
  · obtain ⟨h1, h2⟩ := x.2
    exact ⟨h1.choose, by simpa [ScatFun.restrict, ScatFun.coRestrict, ScatFun.restrictEquiv]
      using h2⟩
  · fun_prop
  · simp [ScatFun.restrict, ScatFun.coRestrict, ScatFun.restrictEquiv]

/-- **Bridge lemma.**  A subtype-level reduction of `g.func` into `f.func` corestricted to the
domain piece `{w | f.func w ∈ V}` upgrades to `Reduces g (coRestrict f V)`.  This is just
`ContinuouslyReduces.comp_homeomorph_right` applied with the homeomorphism `restrictEquiv`, since
`(coRestrict f V).func = (f.func ∘ Subtype.val) ∘ restrictEquiv f _` by definition of `restrict`. -/
lemma reduces_coRestrict_of_subtype (f g : ScatFun) (V : Set Baire)
    (h : ContinuouslyReduces g.func
      (f.func ∘ (Subtype.val : ↑{w : ↑f.domain | f.func w ∈ V} → ↑f.domain))) :
    Reduces g (coRestrict f V) :=
  h.comp_homeomorph_right (f.restrictEquiv {w | f.func w ∈ V})

/-- **ω copies** of a `ScatFun`: `ω h = gl_{i ∈ ω} h`, the plain gluing of the constant family.
This is the memoir's `ω h`. -/
def omega (h : ScatFun) : ScatFun :=
  gl (fun _ => h)

/-- `ω h` acts on the block-`n` point `(n)⌢z` by `(n)⌢(h z)` — the special case of
`gl_func_prepend` for the constant family `fun _ => h`.  (Isolated as an explicit lemma so
callers don't force the expensive definitional unfolding of `GluingFunVal`.) -/
lemma omega_func_prepend (h : ScatFun) (n : ℕ) (z : ↑h.domain) :
    (omega h).func ⟨prepend n z.val, mem_gluingSet_prepend z.prop⟩ = prepend n (h.func z) :=
  gl_func_prepend (fun _ => h) n z (mem_gluingSet_prepend z.prop)

/-- **Plain gluing of a finite family** `G : Fin n → ScatFun`.  Realised as the `ℕ`-indexed
plain gluing of `G` padded by the empty function past index `n` (the empty padding contributes
no points).  This is the memoir's `gl G` for a finite set `G`. -/
def glFin {n : ℕ} (G : Fin n → ScatFun) : ScatFun :=
  gl (fun k => if h : k < n then G ⟨k, h⟩ else empty)

/-- The set `X_g = {y ∈ B | ∀ neighbourhood V of y, g ≤ f ↾ V}` of the memoir. -/
def IntertwineSet (f g : ScatFun) : Set Baire :=
  {y : Baire | ∀ V ∈ 𝓝 y, Reduces g (f.coRestrict V)}

/-! ## A trivial helper: an empty-domain function reduces to anything -/

/-- A `ScatFun` with empty domain reduces (in the total `ContinuouslyReduces` sense) to any
`ScatFun`: both the forward map and the value-equation are vacuous, and the range of the composite
is empty so `ContinuousOn` is trivial.  Mirrors `empty_reduces`. -/
lemma reduces_of_isEmpty_domain {F G : ScatFun} (h : IsEmpty ↑F.domain) :
    Reduces F G := by
  refine ⟨fun x => (h.false x).elim,
    continuous_of_const (fun x => (h.false x).elim),
    id, continuousOn_id, fun x => (h.false x).elim⟩

/-! ## Supporting lemma 1 — gluing as a lower bound over pairwise-disjoint open sets

This is the memoir's corollary `Gluingaslowerbound2`: if `(U k)` are pairwise disjoint open
subsets of the codomain `Baire`, then `gl_k (f ↾ U k) ≤ f`.

INTENDED PROOF (memoir).  By the proposition `Gluingaslowerbound`.  Restricting each `U k` to the
union `W = ⋃ k, U k`, the `U k` become a **relative clopen partition** of `W` (each `U k` is open
in `B` hence open in `W`, and `W \ U k = ⋃_{j ≠ k} U j` is open, so `U k` is clopen in `W`).  Fix
for each `k` a reduction `(σ_k, τ_k)` of `f ↾ U k` into `f` (the identity corestriction reduction).
Set `σ : (k)⌢x ↦ σ_k x` and `τ : y ↦ (k)⌢τ_k y` for `y ∈ dom τ_k ⊆ U k`; these are well defined
and continuous because the `U k` (hence the `dom τ_k`) are pairwise disjoint
(`lem:ContUnion`), giving the required reduction `gl_k (f ↾ U k) ≤ f`.

In the `ScatFun` formalisation the cleanest route is to adapt `gl_corestrict_reduces`
(`SimpleSuccessor/Prop411`), which proves the analogous statement for a clopen partition
*covering* `Baire`.  The covering hypothesis is used only to define the inverse map `τ` everywhere;
here `τ` only needs to be defined (and continuous) on `im (f ∘ σ) ⊆ W`, where the disjoint opens
already form a relative clopen partition.  -/

theorem gl_coRestrict_disjoint_open_reduces (f : ScatFun) (U : ℕ → Set Baire)
    (hopen : ∀ k, IsOpen (U k)) (hdisj : Pairwise (Disjoint on U)) :
    Reduces (gl (fun k => f.coRestrict (U k))) f := by
  revert hdisj hopen;
  intro hopen hdisj
  set W := ⋃ k, U k with hW
  have hW_open : IsOpen W := by
    exact isOpen_iUnion hopen
  have hW_clopen : ∀ k, IsOpen (U k) ∧ IsOpen (W \ U k) := by
    intro k
    have hW_clopen_k : W \ U k = ⋃ j, ⋃ (_ : j ≠ k), U j := by
      simp +decide only [ne_eq, Set.ext_iff, mem_diff, mem_iUnion, exists_prop];
      exact fun x => ⟨ fun hx => by rcases Set.mem_iUnion.mp hx.1 with ⟨ i, hi ⟩ ; exact ⟨ i, by rintro rfl; exact hx.2 hi, hi ⟩, fun hx => by rcases hx with ⟨ i, hi, hi' ⟩ ; exact ⟨ Set.mem_iUnion.mpr ⟨ i, hi' ⟩, fun hx' => Set.disjoint_left.mp ( hdisj ( Ne.symm hi ) ) hx' hi' ⟩ ⟩
    generalize_proofs at *;
    exact ⟨ hopen k, hW_clopen_k.symm ▸ isOpen_iUnion fun j => isOpen_iUnion fun hj => hopen j ⟩;
  -- Define the inverse map τ.
  obtain ⟨τ, hτ_cont, hτ⟩ : ∃ τ : Baire → Baire, ContinuousOn τ W ∧ ∀ y ∈ W, ∀ k, y ∈ U k → τ y = prepend k y := by
    have h_cont : ∀ k, ContinuousOn (fun y => prepend k y) (U k) := by
      exact fun k => Continuous.continuousOn ( continuous_prepend k );
    have h_cont : ∀ y ∈ W, ∃ k, y ∈ U k ∧ ∀ j, y ∈ U j → j = k := by
      simp +zetaDelta only [mem_iUnion, forall_exists_index] at *;
      exact fun y k hk => ⟨ k, hk, fun j hj => Classical.not_not.1 fun h => Set.disjoint_left.1 ( hdisj h ) hj hk ⟩;
    choose! k hk₁ hk₂ using h_cont;
    have h_cont : ContinuousOn (fun y => prepend (k y) y) W := by
      intro y hy;
      have h_cont : ContinuousWithinAt (fun y => prepend (k y) y) (U (k y)) y := by
        have h_cont : ∀ z ∈ U (k y), k z = k y := by
          exact fun z hz => hk₂ z ( Set.mem_iUnion.mpr ⟨ k y, hz ⟩ ) _ hz ▸ rfl;
        exact ContinuousOn.continuousWithinAt ( by exact ContinuousOn.congr ( by solve_by_elim ) fun z hz => by rw [ h_cont z hz ] ) ( hk₁ y hy );
      refine' h_cont.mono_of_mem_nhdsWithin _;
      exact mem_nhdsWithin_of_mem_nhds ( hW_clopen ( k y ) |>.1.mem_nhds ( hk₁ y hy ) );
    exact ⟨ _, h_cont, fun y hy k hk => by rw [ hk₂ y hy k hk ] ⟩;
  refine ⟨ ?_, ?_, τ, hτ_cont.mono ?_, ?_ ⟩;
  use fun x => ⟨ unprepend x.val, by
    obtain ⟨ k, hk ⟩ := x.2; simp_all +decide [ ScatFun.coRestrict ] ;
    obtain ⟨ ⟨ y, rfl ⟩, hy ⟩ := hk; simp_all +decide [ ScatFun.restrict ] ;
    obtain ⟨ z, ⟨ hz₁, hz₂ ⟩, hz₃ ⟩ := hy; simp_all +decide [ ← hz₃ ] ;
    convert hz₁ using 1 ⟩
  all_goals generalize_proofs at *;
  · exact Continuous.subtype_mk ( continuous_unprepend.comp continuous_subtype_val ) _;
  · rintro _ ⟨ x, rfl ⟩;
    obtain ⟨ k, hk ⟩ := x.2;
    obtain ⟨ i, rfl ⟩ := hk.1;
    obtain ⟨ y, hy, hy' ⟩ := hk.2;
    exact Set.mem_iUnion.mpr ⟨ i, by simpa [ ← hy' ] using hy.2 ⟩;
  · intro x
    have hx : f.func ⟨unprepend x.val, by
      grind⟩ ∈ U (x.val 0) := by
      have := x.2;
      obtain ⟨ k, hk ⟩ := this;
      obtain ⟨ i, hi ⟩ := hk.1;
      subst hi;
      obtain ⟨ y, hy, hy' ⟩ := hk.2;
      convert hy.2 using 1;
      simp +decide only [gl_domain, ← hy', mem_setOf_eq];
      congr! 2
    generalize_proofs at *;
    rw [ hτ _ _ _ hx ];
    · rfl
    · exact Set.mem_iUnion.mpr ⟨ _, hx ⟩

/-! ## Supporting lemma 2 — discrete subspace ⇒ disjoint open neighbourhoods

Now lives in `GeneralTopology/DisjointOpenNeighbourhoods.lean` as `exists_pairwise_disjoint_open_nhds`
(proved there by the metric argument).

## Supporting lemma 3 — ω-fold reindexing of `ω (gl G)`

If `idx : ℕ → Fin n` hits every block index infinitely often, then `ω (gl G)` reduces to the
plain gluing `gl_j (G (idx j))`.

INTENDED PROOF.  `ω (gl G) = gl_i (gl_k (G k))` is a double gluing of `n · ω` blocks (each `G k`,
`ω`-many times).  Gluing is associative/reindexable: there is an injection from the `ℕ × Fin n`
block index set into `ℕ` matching blocks to equal blocks of `gl_j (G (idx j))` (possible exactly
because `idx` is "infinitely surjective"), so `gl_reduces_of_blockEmbed` / `gl_reindex` apply.
This is the same flavour of combinatorics as `Gl_mono` / `gl_reindex` in `Operations` and
`FiniteGluing`.  -/

/-! ## Infinite intertwining reduction (discrete thinning)

Used by `ScatFun/PreciseStructure/IntertwineMaxFunLimit.lean` (limit-case intertwining, item 2 of
`Intertwinereductionsforomegacentered`): given an injective `y : ℕ → Baire` witnessing
`y k ∈ IntertwineSet f (M k)` for each `k`, thin to an infinite index set `S` and glue the
corresponding coRestrictions to `f` over disjoint open neighbourhoods, padding the rest of the
family with `empty`. -/

/-- **Discrete thinning with disjoint open neighbourhoods.**  Any injective `y : ℕ → Baire` has an
infinite index set `S` and a pairwise-disjoint family of open sets `W` such that `y k ∈ W k` for
`k ∈ S`.  (Thin `range y` to an infinite discrete subset, then take pairwise disjoint open
neighbourhoods.) -/
lemma exists_infinite_disjoint_open_nhds (y : ℕ → Baire) (hinj : Function.Injective y) :
    ∃ (S : Set ℕ) (W : ℕ → Set Baire), S.Infinite ∧ (∀ k, IsOpen (W k)) ∧
      Pairwise (Disjoint on W) ∧ ∀ k ∈ S, y k ∈ W k := by
  classical
  obtain ⟨Y, hYsub, hYinf, hYdisc⟩ :=
    exists_infinite_discrete_subset (Set.infinite_range_of_injective hinj)
  set S : Set ℕ := y ⁻¹' Y with hS_def
  have himg : y '' S = Y := by
    rw [hS_def, Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hYsub]
  have hSinf : S.Infinite := Set.Infinite.of_image y (by rw [himg]; exact hYinf)
  set z : ↥S → Baire := fun i => y i.val with hz_def
  have hz_inj : Function.Injective z := fun a b h => Subtype.ext (hinj h)
  have hz_range : Set.range z ⊆ Y := by
    rintro _ ⟨i, rfl⟩; exact i.property
  have hz_disc : DiscreteTopology ↥(Set.range z) := DiscreteTopology.of_subset hYdisc hz_range
  obtain ⟨V, hVopen, hVmem, hVdisj⟩ := exists_pairwise_disjoint_open_nhds z hz_inj hz_disc
  set W : ℕ → Set Baire := fun k => if h : k ∈ S then V ⟨k, h⟩ else ∅ with hW_def
  refine ⟨S, W, hSinf, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ S
    · rw [hW_def]; simp only [dif_pos hk]; exact hVopen _
    · rw [hW_def]; simp only [dif_neg hk]; exact isOpen_empty
  · intro a b hab
    simp only [Function.onFun, hW_def]
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · simp only [dif_pos ha, dif_pos hb]
        exact hVdisj (fun h => hab (congrArg Subtype.val h))
      · simp only [dif_neg hb]; exact disjoint_bot_right
    · simp only [dif_neg ha]; exact disjoint_bot_left
  · intro k hk; rw [hW_def]; simp only [dif_pos hk]; exact hVmem ⟨k, hk⟩

/-- **Infinite intertwining reduction.**  Given an injective `y : ℕ → Baire` with `y k` in the
intertwine set of `M k` against `f`, there is a family `N` — equal to `M` on an infinite set of
indices and `empty` elsewhere — such that `gl N` reduces to `f`. -/
lemma intertwine_gl_subseq (f : ScatFun) (M : ℕ → ScatFun) (y : ℕ → Baire)
    (hinj : Function.Injective y) (hmem : ∀ k, y k ∈ IntertwineSet f (M k)) :
    ∃ N : ℕ → ScatFun, Reduces (gl N) f ∧
      {k | N k = M k}.Infinite ∧ (∀ k, N k = M k ∨ N k = empty) := by
  classical
  obtain ⟨S, W, hSinf, hWopen, hWdisj, hWnhds⟩ := exists_infinite_disjoint_open_nhds y hinj
  refine ⟨fun k => if k ∈ S then M k else empty, ?_, ?_, ?_⟩
  · refine (gl_reduces_of_pointwise _ (fun k => f.coRestrict (W k)) ?_).trans
      (gl_coRestrict_disjoint_open_reduces f W hWopen hWdisj)
    intro k
    by_cases hk : k ∈ S
    · rw [if_pos hk]
      exact hmem k (W k) ((hWopen k).mem_nhds (hWnhds k hk))
    · rw [if_neg hk]; exact empty_reduces _
  · refine hSinf.mono ?_
    intro k hk
    simp only [Set.mem_setOf_eq]
    rw [if_pos hk]
  · intro k
    by_cases hk : k ∈ S
    · exact Or.inl (if_pos hk)
    · exact Or.inr (if_neg hk)

/-
**Flattening a nested plain gluing.**  The double gluing `gl_i (gl_k (H i k))` reduces to
the single gluing of the flattened family `m ↦ H (Nat.unpair m).1 (Nat.unpair m).2`.  This is
the associativity of plain gluing: a nested point `(i)⌐(k)⌐a` is relabelled to the single-block
point `(Nat.pair i k)⌐a`, with the payload `a` unchanged.
-/
theorem gl_gl_flatten_reduces (H : ℕ → ℕ → ScatFun) :
    Reduces (gl (fun i => gl (fun k => H i k)))
      (gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2)) := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ prepend ( Nat.pair ( x.val 0 ) ( unprepend x.val 0 ) ) ( unprepend ( unprepend x.val ) ), mem_gluingSet_prepend ( show unprepend ( unprepend x.val ) ∈ ( H ( Nat.unpair ( Nat.pair ( x.val 0 ) ( unprepend x.val 0 ) ) |>.1 ) ( Nat.unpair ( Nat.pair ( x.val 0 ) ( unprepend x.val 0 ) ) |>.2 ) ).domain from by
                                                                                                                                      have h_unprepend : ∃ i, x.val 0 = i ∧ unprepend x.val ∈ (gl (fun k => H i k)).domain := by
                                                                                                                                        exact GluingSet_inverse_short (fun i => (gl fun k => H i k).domain) x
                                                                                                                                      obtain ⟨ i, hi, hi' ⟩ := h_unprepend;
                                                                                                                                      have := GluingSet_inverse_short ( fun k => ( H i k ).domain ) ⟨ unprepend x.val, hi' ⟩ ; aesop; ) ⟩;
  case refine_3 => exact fun y => prepend ( Nat.unpair ( y 0 ) |>.1 ) ( prepend ( Nat.unpair ( y 0 ) |>.2 ) ( unprepend y ) );
  · refine Continuous.subtype_mk ?_ ?_;
    have h_cont : Continuous (fun x : Baire => Nat.pair (x 0) (unprepend x 0)) := by
      have h_cont : Continuous (fun x : Baire => (x 0, unprepend x 0)) := by
        refine Continuous.prodMk ?_ ?_;
        · exact continuous_apply 0;
        · exact continuous_apply 0 |> Continuous.comp <| continuous_unprepend;
      exact Continuous.comp ( show Continuous fun x : ℕ × ℕ => Nat.pair x.1 x.2 from by continuity ) h_cont;
    have h_cont : Continuous (fun x : Baire => prepend (Nat.pair (x 0) (unprepend x 0)) (unprepend (unprepend x))) := by
      apply_rules [ continuous_pi, continuous_const ];
      intro i; exact (by
      rcases i with ( _ | i ) <;> simp +decide [ prepend ];
      · exact h_cont;
      · exact continuous_apply i |> Continuous.comp <| continuous_unprepend.comp continuous_unprepend);
    exact h_cont.comp continuous_subtype_val;
  · refine ⟨ ?_, ?_ ⟩;
    · refine Continuous.continuousOn ?_;
      obtain ⟨hfst, hsnd, htail⟩ :
          Continuous (fun y : Baire => (Nat.unpair (y 0)).1) ∧
          Continuous (fun y : Baire => (Nat.unpair (y 0)).2) ∧
          Continuous (fun y : Baire => unprepend y) :=
        ⟨by fun_prop (disch := solve_by_elim), by fun_prop, continuous_unprepend⟩
      have hprep : Continuous (fun p : ℕ × Baire => prepend p.1 p.2) := by
        convert continuous_prepend using 1;
        exact continuous_prod_of_discrete_left
      convert hprep.comp (Continuous.prodMk hfst (hprep.comp (Continuous.prodMk hsnd htail))) using 1;
    · intro x; simp +decide [ gl ] ;
      unfold GluingFunVal glBlock; simp +decide ;
      simp +decide only [prepend, ↓reduceIte, Nat.unpair_pair, ↓dreduceIte];
      grind +suggestions

/-
**Support reindexing of a plain gluing (identity payload).**  If a family `H` agrees with
`fun i => G (e i)` on a set `S` and has empty-domain blocks off `S`, and `e` is injective on `S`,
then `gl H` reduces to `gl G`.  This is `gl_reindex` restricted to the support `S`: the payload is
unchanged, only the block index is relabelled `i ↦ e i`, with the inverse recovering `i` from `e i`
via injectivity on `S` (off-`S` blocks never occur since their domain is empty).
-/
theorem gl_reindex_support (G H : ℕ → ScatFun) (e : ℕ → ℕ) (S : ℕ → Prop)
    (hS : Set.InjOn e {i | S i})
    (hH : ∀ i, S i → H i = G (e i))
    (hHempty : ∀ i, ¬ S i → IsEmpty ↑(H i).domain) :
    Reduces (gl H) (gl G) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ, ∀ i, S i → d (e i) = i := by
    have h_inv : ∀ m, (∃ i, S i ∧ e i = m) → ∃! i, S i ∧ e i = m := by
      exact fun m hm => by obtain ⟨ i, hi, rfl ⟩ := hm; exact ⟨ i, ⟨ hi, rfl ⟩, fun j hj => hS hj.1 hi hj.2 ⟩ ;
    choose! d hd₁ hd₂ using h_inv;
    exact ⟨ d, fun i hi => hd₂ _ ⟨ i, hi, rfl ⟩ _ ⟨ hi, rfl ⟩ ▸ rfl ⟩;
  refine ⟨ ?_, ?_, ?_ ⟩;
  use fun x => ⟨ prepend ( e ( x.val 0 ) ) ( unprepend x.val ), by
    have h_mem : unprepend x.val ∈ (H (x.val 0)).domain := by
      convert GluingSet_inverse_short ( fun i => ( H i ).domain ) x using 1;
      grind;
    by_cases hi : S ( x.val 0 ) <;> simp_all +decide [ mem_gluingSet_prepend ] ⟩
  all_goals generalize_proofs at *;
  · refine continuous_induced_rng.mpr ?_;
    refine continuous_pi fun i => ?_;
    induction' i with i ih;
    · convert continuous_of_discreteTopology.comp ( show Continuous fun x : ( gl H ).domain => x.val 0 from ?_ ) using 1;
      exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val;
    · convert continuous_apply ( i + 1 ) |> Continuous.comp <| continuous_subtype_val using 1;
  · refine ⟨ fun y => prepend ( d ( y 0 ) ) ( unprepend y ), ?_, ?_ ⟩
    all_goals generalize_proofs at *;
    · refine Continuous.continuousOn ?_;
      apply_rules [ continuous_pi, continuous_apply ];
      intro i; by_cases hi : i = 0 <;> simp +decide [ hi, prepend, unprepend ] ;
      · fun_prop;
      · exact continuous_apply _;
    · intro x
      simp only [gl, GluingFunVal, glBlock];
      by_cases hi : S ( x.val 0 ) <;> simp_all +decide [ prepend ];
      · simp +decide [ unprepend_prepend ];
        grind;
      · grind

/-- **Block-embedding reduction of plain gluings, support form.**  A strengthening of
`gl_reduces_of_blockEmbed`: the reindexing `e` only needs to be injective on, and the block
reductions only need to hold on, the *support* `{i | (F i).domain.Nonempty}`.  Blocks with empty
domain contribute nothing to `gl F`, so they impose no constraint. -/
theorem gl_reduces_of_blockEmbed_support (F G : ℕ → ScatFun) (e : ℕ → ℕ)
    (hinj : Set.InjOn e {i | (F i).domain.Nonempty})
    (hred : ∀ i, (F i).domain.Nonempty → Reduces (F i) (G (e i))) :
    Reduces (gl F) (gl G) := by
  classical
  set H : ℕ → ScatFun := fun i => if (F i).domain.Nonempty then G (e i) else empty with hHdef
  have hempty : ∀ i, ¬ (F i).domain.Nonempty → IsEmpty ↑(F i).domain := by
    intro i h
    exact Set.isEmpty_coe_sort.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  have hA : Reduces (gl F) (gl H) := by
    apply gl_reduces_of_pointwise
    intro i
    by_cases h : (F i).domain.Nonempty
    · simpa [hHdef, h] using hred i h
    · exact reduces_of_isEmpty_domain (hempty i h)
  have hB : Reduces (gl H) (gl G) :=
    gl_reindex_support G H e (fun i => (F i).domain.Nonempty) hinj
      (fun i h => by simp [hHdef, h]) (fun i h => by
        simp only [hHdef, if_neg h]
        exact Set.isEmpty_coe_sort.mpr rfl)
  exact hA.trans hB

/-
For `k < n`, infinitely many indices `jj` satisfy `idx jj = k` (as the fibre is unbounded by
`hidx`).
-/
lemma idx_fibre_infinite {n : ℕ} (idx : ℕ → Fin n)
    (hidx : ∀ (k : Fin n) (N : ℕ), ∃ j, N ≤ j ∧ idx j = k) (k : ℕ) (hk : k < n) :
    {jj | (idx jj : ℕ) = k}.Infinite := by
  exact Set.infinite_of_forall_exists_gt fun N => by obtain ⟨ j, hj₁, hj₂ ⟩ := hidx ⟨ k, hk ⟩ ( N + 1 ) ; exact ⟨ j, by aesop, by linarith ⟩ ;

/-- The single-gluing block-embedding step of `omega_glFin_reduces_reindex`, after flattening:
the gluing of the flattened padded family reduces to `gl (fun j => G (idx j))`. -/
lemma gl_pad_unpair_reduces {n : ℕ} (G : Fin n → ScatFun) (idx : ℕ → Fin n)
    (hidx : ∀ (k : Fin n) (N : ℕ), ∃ j, N ≤ j ∧ idx j = k) :
    Reduces
      (gl (fun m => if h : (Nat.unpair m).2 < n then G ⟨(Nat.unpair m).2, h⟩ else empty))
      (gl (fun j => G (idx j))) := by
  set F : ℕ → ScatFun :=
    fun m => if h : (Nat.unpair m).2 < n then G ⟨(Nat.unpair m).2, h⟩ else empty with hF
  have hsupp : ∀ m, (F m).domain.Nonempty → (Nat.unpair m).2 < n := by
    intro m hm
    by_contra h
    simp only [hF, dif_neg h] at hm
    exact absurd hm (by simp [empty])
  refine gl_reduces_of_blockEmbed_support F (fun j => G (idx j))
    (fun m => Nat.nth (fun jj => (idx jj : ℕ) = (Nat.unpair m).2) (Nat.unpair m).1) ?_ ?_
  · intro m hm m' hm' hee
    dsimp only at hee
    have hk : (Nat.unpair m).2 < n := hsupp m hm
    have hk' : (Nat.unpair m').2 < n := hsupp m' hm'
    have hmemk := Nat.nth_mem_of_infinite (idx_fibre_infinite idx hidx _ hk) (Nat.unpair m).1
    have hmemk' := Nat.nth_mem_of_infinite (idx_fibre_infinite idx hidx _ hk') (Nat.unpair m').1
    have hkk : (Nat.unpair m).2 = (Nat.unpair m').2 :=
      calc (Nat.unpair m).2
          = (idx (Nat.nth (fun jj => (idx jj : ℕ) = (Nat.unpair m).2) (Nat.unpair m).1) : ℕ) :=
            hmemk.symm
        _ = (idx (Nat.nth (fun jj => (idx jj : ℕ) = (Nat.unpair m').2) (Nat.unpair m').1) : ℕ) := by
            rw [hee]
        _ = (Nat.unpair m').2 := hmemk'
    have h1 : (Nat.unpair m).1 = (Nat.unpair m').1 := by
      apply Nat.nth_injective (idx_fibre_infinite idx hidx _ hk)
      rw [hee, hkk]
    have hu : Nat.unpair m = Nat.unpair m' := Prod.ext h1 hkk
    have := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) hu
    simpa [Nat.pair_unpair] using this
  · intro m hm
    have hk : (Nat.unpair m).2 < n := hsupp m hm
    have hmemk := Nat.nth_mem_of_infinite (idx_fibre_infinite idx hidx _ hk) (Nat.unpair m).1
    have hidxe :
        idx (Nat.nth (fun jj => (idx jj : ℕ) = (Nat.unpair m).2) (Nat.unpair m).1)
          = ⟨(Nat.unpair m).2, hk⟩ := Fin.ext hmemk
    simp only [hF, dif_pos hk, hidxe]
    exact ContinuouslyReduces.refl _

theorem omega_glFin_reduces_reindex {n : ℕ} (G : Fin n → ScatFun)
    (idx : ℕ → Fin n) (hidx : ∀ (k : Fin n) (N : ℕ), ∃ j, N ≤ j ∧ idx j = k) :
    Reduces (omega (glFin G)) (gl (fun j => G (idx j))) := by
  have hflat := gl_gl_flatten_reduces
    (fun (_ : ℕ) (k : ℕ) => (if h : k < n then G ⟨k, h⟩ else empty))
  exact hflat.trans (gl_pad_unpair_reduces G idx hidx)

/-! ## Routine helper lemmas for the main proof -/

/-
`omega (glFin G)` has empty domain when `G : Fin 0 → ScatFun`: both the inner finite
gluing and the outer ω-gluing are plain gluings of all-empty-domain blocks.
-/
lemma omega_glFin_zero_domain_isEmpty (G : Fin 0 → ScatFun) :
    IsEmpty ↑(omega (glFin G)).domain := by
      simp +decide only [omega, gl, glFin, not_lt_zero, ↓dreduceDIte, isEmpty_coe_sort];
      simp +decide [ GluingSet, empty ]

/-
Injectivity of the product enumeration `(k, j) ↦ natEmbedding (Y k) j` when the `Y k`
are pairwise disjoint: equal values lie in the same block (disjointness), and within a
block `natEmbedding` is injective.
-/
lemma yfun_injective {ι : Type*} {Y : ι → Set Baire}
    (hYinf : ∀ k, (Y k).Infinite) (hYdisj : Pairwise (Disjoint on Y)) :
    Function.Injective
      (fun p : ι × ℕ => (Set.Infinite.natEmbedding (Y p.1) (hYinf p.1) p.2 : ↑(Y p.1)).val) := by
  intro p q; have := @hYdisj p.1 q.1; by_cases h : p.1 = q.1 <;> simp_all +decide [ Set.disjoint_left ] ;
  · intro h_eq
    have h_eq' : p.2 = q.2 := by
      have h_eq' : Function.Injective (fun j : ℕ => (Set.Infinite.natEmbedding (Y p.1) (hYinf p.1) j).val) := by
        exact Subtype.val_injective.comp ( Set.Infinite.natEmbedding ( Y p.1 ) ( hYinf p.1 ) |>.injective );
      exact h_eq' ( by aesop )
    exact Prod.ext h h_eq';
  · grind +qlia

/-
`Fin (m+1) × ℕ` is countably infinite, so there is a bijection `ℕ ≃ Fin (m+1) × ℕ`.
-/
lemma nonempty_equiv_nat_finSucc_prod (m : ℕ) : Nonempty (ℕ ≃ Fin (m + 1) × ℕ) := by
  exact ( Cardinal.eq.1 <| by simp +decide )

/-
A bijection `e : ℕ ≃ Fin (m+1) × ℕ` hits every first-coordinate value `k` arbitrarily
late: for all `N` there is `j ≥ N` with `(e j).1 = k`.
-/
lemma exists_ge_fst_eq {m : ℕ} (e : ℕ ≃ Fin (m + 1) × ℕ) (k : Fin (m + 1)) (N : ℕ) :
    ∃ j, N ≤ j ∧ (e j).1 = k := by
      have h_unbounded : Set.Infinite {j | (e j).1 = k} := by
        exact Set.infinite_of_injective_forall_mem ( show Function.Injective ( fun n => e.symm ( k, n ) ) from fun a b h => by simpa using e.symm.injective h ) fun n => by simp +decide ;
      exact Exists.elim ( h_unbounded.exists_gt N ) fun x hx => ⟨ x, hx.2.le, hx.1 ⟩

/-! ## Main lemma -/

/-- **Lemma `Intertwinereductions` (`ScatFun` form).**

Let `f : ScatFun` and `G : Fin n → ScatFun`.  If for every block `G k` the set
`IntertwineSet f (G k) = {y | ∀ V ∈ 𝓝 y, G k ≤ f ↾ V}` is infinite, then `ω (gl G) ≤ f`.

The proof wires together the four ingredients listed in the file header. -/
theorem intertwine_reductions {n : ℕ} (f : ScatFun) (G : Fin n → ScatFun)
    (hG : ∀ k, (IntertwineSet f (G k)).Infinite) :
    Reduces (omega (glFin G)) f := by
  -- The empty case `G = ∅`: `ω (gl ∅)` has empty domain, hence reduces to anything.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    -- `glFin G = gl (fun _ => empty)` and `omega _ = gl (fun _ => glFin G)` both have empty domain
    -- (a plain gluing of all-empty-domain blocks is empty).
    exact reduces_of_isEmpty_domain (omega_glFin_zero_domain_isEmpty G)
  · -- Nonempty case.  Write `n = m + 1` so `InfiniteEmbedOmegaStronger` applies directly.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    -- Step 1.  Thin the `IntertwineSet`s to pairwise disjoint infinite `Y k` with discrete union.
    obtain ⟨Y, hYsub, hYinf, hYdisj, hYdisc⟩ :=
      exists_pairwise_disjoint_infinite_discrete_subspaces
        (fun k => IntertwineSet f (G k)) hG
    -- Step 2.  Enumerate each infinite `Y k` injectively, and assemble the product enumeration
    -- `yfun : Fin (m+1) × ℕ → Baire`, `(k, j) ↦ enum k j ∈ Y k`.
    set enum : Fin (m + 1) → ℕ → Baire :=
      fun k j => (Set.Infinite.natEmbedding (Y k) (hYinf k) j : ↥(Y k)).val with henum
    have henum_mem : ∀ k j, enum k j ∈ Y k :=
      fun k j => (Set.Infinite.natEmbedding (Y k) (hYinf k) j).property
    set yfun : Fin (m + 1) × ℕ → Baire := fun p => enum p.1 p.2 with hyfun
    -- `yfun` is injective: same block ⇒ `natEmbedding` injective; different blocks ⇒ `Y` disjoint.
    have hyfun_inj : Function.Injective yfun := by
      simpa only [hyfun, henum] using yfun_injective hYinf hYdisj
    -- `range yfun ⊆ ⋃ k, Y k`, and the latter is discrete, so `range yfun` is discrete.
    have hyfun_range_sub : Set.range yfun ⊆ ⋃ k, Y k := by
      rintro _ ⟨⟨k, j⟩, rfl⟩; exact Set.mem_iUnion.2 ⟨k, henum_mem k j⟩
    have hyfun_disc : DiscreteTopology ↥(Set.range yfun) :=
      DiscreteTopology.of_subset hYdisc hyfun_range_sub
    -- Step 3.  Pairwise disjoint open neighbourhoods of the discrete image.
    obtain ⟨Vfun, hVopen, hVmem, hVdisj⟩ :=
      exists_pairwise_disjoint_open_nhds yfun hyfun_inj hyfun_disc
    -- Step 4.  Reindex the product `Fin (m+1) × ℕ` by `ℕ` via a bijection `e`.
    obtain ⟨e⟩ : Nonempty (ℕ ≃ Fin (m + 1) × ℕ) := nonempty_equiv_nat_finSucc_prod m
    set W : ℕ → Set Baire := fun j => Vfun (e j) with hW
    have hWopen : ∀ j, IsOpen (W j) := fun j => hVopen (e j)
    have hWdisj : Pairwise (Disjoint on W) := by
      intro a b hab
      exact hVdisj (fun h => hab (e.injective h))
    -- Step 4a.  `gl_j (f ↾ W j) ≤ f`  (memoir `Gluingaslowerbound2`).
    have hLB : Reduces (gl (fun j => f.coRestrict (W j))) f :=
      gl_coRestrict_disjoint_open_reduces f W hWopen hWdisj
    -- Step 4b.  For each `j`, the block `G (e j).1` reduces to `f ↾ W j`.
    -- Indeed `yfun (e j) ∈ Y (e j).1 ⊆ IntertwineSet f (G (e j).1)` and `W j = Vfun (e j)` is an
    -- open neighbourhood of `yfun (e j)`, so the defining property of `IntertwineSet` applies.
    have hblock : ∀ j, Reduces (G (e j).1) (f.coRestrict (W j)) := by
      intro j
      have hy_in : yfun (e j) ∈ IntertwineSet f (G (e j).1) :=
        hYsub (e j).1 (by simpa [hyfun] using henum_mem (e j).1 (e j).2)
      have hWnhds : W j ∈ 𝓝 (yfun (e j)) :=
        (hWopen j).mem_nhds (by simpa [hW] using hVmem (e j))
      exact hy_in (W j) hWnhds
    -- Step 4c.  `gl_j (G (e j).1) ≤ gl_j (f ↾ W j)`  (Gluingcohomomorphism).
    have hCohom : Reduces (gl (fun j => G (e j).1)) (gl (fun j => f.coRestrict (W j))) :=
      gl_reduces_of_pointwise _ _ hblock
    -- Step 5.  `ω (gl G) ≤ gl_j (G (e j).1)`  (ω-fold reindexing).
    -- `idx j = (e j).1` hits every block index infinitely often because `e` is a bijection onto
    -- `Fin (m+1) × ℕ`, so each fibre `{j | (e j).1 = k}` is infinite.
    have hidx : ∀ (k : Fin (m + 1)) (N : ℕ), ∃ j, N ≤ j ∧ (e j).1 = k :=
      fun k N => exists_ge_fst_eq e k N
    have hOmega : Reduces (omega (glFin G)) (gl (fun j => G (e j).1)) :=
      omega_glFin_reduces_reindex G (fun j => (e j).1) hidx
    -- Compose the chain  ω(gl G) ≤ gl(G∘fst∘e) ≤ gl(f ↾ W) ≤ f.
    exact hOmega.trans (hCohom.trans hLB)

end ScatFun

end