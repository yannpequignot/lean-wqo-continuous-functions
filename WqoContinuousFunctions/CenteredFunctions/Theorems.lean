import WqoContinuousFunctions.CenteredFunctions.Defs
import WqoContinuousFunctions.CenteredFunctions.Helpers
import WqoContinuousFunctions.PointedGluing.UpperBound.Theorem
import WqoContinuousFunctions.ScatFun.Operations
import WqoContinuousFunctions.ScatFun.FiniteGluing
import WqoContinuousFunctions.PointedGluing.MinFun.Theorems
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Formalization of `4_centered_memo.tex` — Main Theorems

This file formalizes the main theorems from Chapter 4 (Centered Functions) of the
memoir on continuous reducibility between functions.

## Main results

### Section 1: Definition and characterization (§4.1)
* `pgluingOfRegularIsCentered` — Fact 4.1
* `centerInvariance_reduce` — Fact 4.2, Item 1
* `centerInvariance_equiv` — Fact 4.2, Item 2
* `centerInvariance_cover` — Fact 4.2, Item 3
* `scatteredHaveCocenter` — Proposition 4.3
* `scatteredCentered_isSimple` — Proposition 4.3, second part
* `rigidityOfCocenter_tau` — Proposition 4.4, Item 1
* `rigidityOfCocenter_separation` — Proposition 4.4, Item 2
* `rigidityOfCocenter_finiteGluing` — Proposition 4.4, Item 3
* `rigidityOfCocenter_reducibleByPieces` — Proposition 4.4, Item 4
* `residualCorestrictionOfCentered` — Corollary 4.5
  (Theorem 4.6 — `centeredAsPgluing_*` / `centered_equiv_pgl_rays` /
  `monotone_pgluing_of_centered` / `centeredAsPgluing_iff_monotone` / `centeredAsPgluing_CBrank`
  — now live in `CenteredFunctions/CenteredAsPgluing.lean`.)
* `limit_rank_equiv_maxFun` — `ConsequencesGeneralStructureThm`: every function of
  limit CB-rank `lam` is `≡ ℓ_lam` (used to feed Corollary 4.10).

### Corollary 4.10 (centeredSuccessor)
* The strict-inequality part (`k_{lam+1} < pgl ℓ_lam`) for `lam` a nonzero limit is proved in
  `ScatFun/PreciseStructure/Strictness.lean` (`pglMaxFun_not_le_minFunPlusOne_limit`, paired with
  the easy direction `minFun_le_pglMaxFun` in `Helpers.lean`).
* The dichotomy part of Corollary 4.10 (`centeredSuccessor`: a centered function of
  rank `lam + 1` is `≡ k_{lam+1}` or `≡ pgl ℓ_lam`) lives in
  `CenteredFunctions/Finiteness.lean` (it consumes Theorem 4.9), and is proved there
  for `lam` a nonzero limit.

## Located in other files
* Theorem 4.7 `localCenterednessFromTwoBQO_scatFun` → `CenteredFunctions/LocallyCentered/Theorem.lean`.
* Proposition 4.8 `finitegenerationAndPgluing_upper` / `_lower` → `ScatFun/FiniteGluing.lean`.
* Theorem 4.9 `finitenessOfCenteredFunctions` → `CenteredFunctions/Finiteness.lean`
  (helpers in `CenteredFunctions/FinitenessHelpers.lean`).

## §4.3 (not yet formalized)
Proposition 4.11 (`simpleIffCoincidenceOfCocenters`), Theorem 4.12
(`simpleFunctionsLambdaPlusOne`) and Corollary 4.13 (`finiteDegreeLambdaPlusOne`)
are not yet formalized; only the Proposition 4.11 helper scaffolding lives in
`CenteredFunctions/Helpers.lean`.
-/

noncomputable section

/-!
## Section 1: Definition and Characterization (§4.1)
-/

/-- **Fact 4.1 (Pgluingofregulariscentered).**
If `(f_i)_{i ∈ ℕ}` is a regular sequence in `𝒞`, then `0^ω` is a center for
`pgl_i f_i`.

*Proof sketch:* By Pgluingaslowerbound2, it suffices to show that for every clopen
neighborhood `U` of `0^ω` and every `n ∈ ℕ`, there exists a continuous reduction
`(σ, τ)` from `f_n` to the pointed gluing such that `im(σ) ⊆ U` and
`0^ω ∉ cl(im(f ∘ σ))`. By regularity, we can find `m` large enough such that
`N_{(0)^m} ⊆ U` and `f_n ≤ f_m`, giving the desired reduction. -/
theorem pgluingOfRegularIsCentered
    (F : ℕ → ScatFun)
    (hf_reg : Preorder.IsRegularSeq ScatFun.Reduces F) :
    IsCenterFor
      (ScatFun.pgl F).func
      ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ := by
  -- By `pgl_isCenterFor_of_local`, it suffices to give, for each block `i` and each
  -- neighbourhood `V ∋ 0^ω`, a reduction of `(F i).func` into `pgl F` landing in `V`
  -- with closure avoiding `0^ω`.  Regularity gives `j ≥ N` with `F i ≤ F j`; we redirect
  -- block `i` into block `j` (which for `j` large sits in `V`, with image in the clopen
  -- `{y | y j = 1}` avoiding `0^ω`).
  apply pgl_isCenterFor_of_local
  intro i V hV hzV
  obtain ⟨n, hn⟩ :=
    nbhd_basis' (ScatFun.pgl F).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hV hzV
  obtain ⟨j, hjn, hred⟩ := hf_reg.exists_ge i n
  obtain ⟨σ₀, hσ₀cont, τ₀, hτ₀cont, hστ₀⟩ := hred
  set σ : (F i).domain → ↥(ScatFun.pgl F).domain :=
    fun z => ⟨prependZerosOne j (σ₀ z).val,
      prependZerosOne_mem_pointedGluingSet _ j _ (σ₀ z).prop⟩ with hσ
  -- `pgl F` on `σ z` is the block-`j` embedding `(0)^j(1)·(F j).func (σ₀ z)`.
  have hfs : ∀ z, (ScatFun.pgl F).func (σ z) = prependZerosOne j ((F j).func (σ₀ z)) :=
    fun z => ScatFun.pgl_func_block F j (σ₀ z)
  refine ⟨σ, fun y => τ₀ (stripZerosOne j y), ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of σ
    exact Continuous.subtype_mk
      ((continuous_prependZerosOne j).comp (continuous_subtype_val.comp hσ₀cont)) _
  · -- reduction equation
    intro z
    show (F i).func z = τ₀ (stripZerosOne j ((ScatFun.pgl F).func (σ z)))
    rw [hfs z, stripZerosOne_prependZerosOne]
    exact hστ₀ z
  · -- continuity of τ on the relevant range
    apply hτ₀cont.comp (continuous_stripZerosOne j).continuousOn
    rintro _ ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    show ((F j).func ∘ σ₀) z = stripZerosOne j ((ScatFun.pgl F).func (σ z))
    rw [hfs z, stripZerosOne_prependZerosOne]
    rfl
  · -- image of σ lands in V
    intro z
    refine hn ?_
    intro k hk
    exact prependZerosOne_head_eq_zero j _ k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjn)
  · -- 0^ω is not in the closure of the image (it sits in the clopen {y | y j = 1})
    have hCcl : IsClosed {y : Baire | y j = 1} :=
      isClosed_singleton.preimage (continuous_apply j)
    have hsub : Set.range (fun z => (ScatFun.pgl F).func (σ z)) ⊆ {y : Baire | y j = 1} := by
      rintro _ ⟨z, rfl⟩
      simp only [Set.mem_setOf_eq, hfs z]
      exact prependZerosOne_at_i j _
    intro h
    have : zeroStream ∈ {y : Baire | y j = 1} := hCcl.closure_subset_iff.mpr hsub h
    simp [zeroStream] at this

/-
**Fact 4.2 (Centerinvariance) — Item 1.**
If `x` is a center for `f` and `(σ, τ)` continuously reduces `f` to `g`,
then for every neighborhood `U` of `σ(x)`, we have `f ≤ g|_U`.

*Proof:* By continuity of `σ`, `σ⁻¹(U)` is a neighborhood of `x`.
We have `f|_{σ⁻¹(U)} ≤ g|_U` via `(σ↾U, τ)` and `f ≤ f|_{σ⁻¹(U)}` since
`x` is a center for `f`, so `f ≤ g|_U` by transitivity.
-/
theorem centerInvariance_reduce
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    {σ : A → A'} (hσ : Continuous σ)
    {τ : B' → B} (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a)))
    {U : Set A'} (hU : IsOpen U) (hσx : σ x ∈ U) :
    ContinuouslyReduces f (g ∘ (Subtype.val : U → A')) := by
  have h_f_le_f_restrict : f ≤ f ∘ (Subtype.val : σ ⁻¹' U → A) := by
    exact hcenter _ (hU.preimage hσ) hσx
  have h_f_restrict_le_g_restrict : f ∘ (Subtype.val : σ ⁻¹' U → A) ≤ g ∘ (Subtype.val : U → A') := by
    refine ⟨fun a => ⟨σ a, a.2⟩, ?_, ?_⟩
    · fun_prop
    · refine ⟨τ, ?_, ?_⟩
      · refine hτ_cont.mono ?_
        rintro _ ⟨a, rfl⟩ ; exact ⟨a, rfl⟩
      · aesop
  exact ContinuouslyReduces.trans h_f_le_f_restrict h_f_restrict_le_g_restrict

/-
**Fact 4.2 (Centerinvariance) — Item 2.**
If `x` is a center for `f` and `f ≡ g` via `(σ, τ)`, then `σ(x)` is a center for `g`.

*Proof:* If `U` is a neighborhood of `σ(x)`, then by Item 1 `f ≤ g|_U`.
Since `g ≤ f` by equivalence, `g ≤ g|_U` by transitivity.
-/
theorem centerInvariance_equiv
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    (hequiv : ContinuouslyEquiv f g)
    {σ : A → A'} (hσ : Continuous σ)
    {τ : B' → B} (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a))) :
    IsCenterFor g (σ x) := by
  intro U hU hσU
  convert hequiv.2.trans (centerInvariance_reduce hcenter hσ hτ_cont hτ_eq hU hσU) using 1

/-
**Fact 4.2 (Centerinvariance) — Item 3.**
If `x` is a center for `f` and `(σ, τ)` reduces `f` to `g`, and `(A_i)_{i ∈ I}` is
an open covering of `dom(g)`, then there exists `i ∈ I` with `f ≤ g|_{A_i}`.

*Proof:* `σ(x) ∈ A_i` for some `i`, and since `A_i` is open, apply Item 1.
-/
theorem centerInvariance_cover
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    (hred : ContinuouslyReduces f g)
    {I : Type*} {C : I → Set A'} (hcover : ⋃ i, C i = univ)
    (hopen : ∀ i, IsOpen (C i)) :
    ∃ i, ContinuouslyReduces f (g ∘ (Subtype.val : C i → A')) := by
  have := hcover.symm.subset (Set.mem_univ (hred.choose x))
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
  exact ⟨i, centerInvariance_reduce hcenter (hred.choose_spec.1) (hred.choose_spec.2.choose_spec.1) (hred.choose_spec.2.choose_spec.2) (hopen i) hi⟩

/-- **Proposition 4.3 (scatteredhavecocenter).**
Suppose that `f : A → B` is centered with `A` metrizable and `B` Hausdorff.
Then `f` is scattered if and only if all centers have the same image by `f`.

Moreover when `f` is scattered, it is simple and any center of `f` is mapped to
its distinguished point.

*Proof sketch (⇒):* If `f` is scattered with rank `γ = α + 1`, by transfinite
induction, all centers belong to `CB_β(f)` for all `β < γ`. In particular, all centers
are in `CB_α(f)`, and since centers are `f|_{CB_α(f)}`-isolated, `f` is constant
on `CB_α(f)` — hence `f` is simple and all centers have the same image.

*Proof sketch (⇐ / contrapositive):* If two centers `x₀, x₁` map to different
values `f(x₀) ≠ f(x₁)`, then by induction both belong to every `CB_α(f)`,
so the perfect kernel is nonempty and `f` is not scattered.
Not formalized yet -/
theorem scatteredHaveCocenter
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf_scat: ScatteredFun f):
    ∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y := by
  -- Forward: scattered → all centers have same image
  -- By contrapositive: if two centers x, y have f(x) ≠ f(y),
  -- then f is not scattered (centers_different_images_not_scattered)
  intro x y hx hy
  by_contra h
  exact centers_different_images_not_scattered f x y hx hy h hf_scat


/--
**Proposition 4.3 — Second part.**
When `f` is scattered and centered, it is simple and any center maps to the
distinguished point.
-/
theorem scatteredCentered_isSimple
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f) :
    SimpleFun f := by
  -- The distinguished point is the cocenter; `centered_scattered_simple_structure`
  -- supplies the last nonempty CB-level on which `f` is constant.
  have hy : ∀ x, IsCenterFor f x → f x = cocenter f hf_cent := fun x hx =>
    scatteredHaveCocenter f hf_scat x hf_cent.choose hx hf_cent.choose_spec
  obtain ⟨α, _hrank, hne, hempty, hconst⟩ :=
    centered_scattered_simple_structure f hf_scat hf_cent (cocenter f hf_cent) hy
  exact ⟨α, hne, hempty, cocenter f hf_cent, hconst⟩

/-
**Proposition 4.4 (Rigidityofthecocenter) — Item 1.**
Let `f, g ∈ 𝒞` be centered with cocenters `y_f` and `y_g`.
If `f ≡ g` and `(σ, τ)` reduces `f` to `g`, then `τ(y_g) = y_f`.

*Proof:* Let `x` be a center for `f`. Since `f ≡ g`, `σ(x)` is a center for `g`
by Centerinvariance, so `g(σ(x)) = y_g`. Hence `τ(y_g) = τ(g(σ(x))) = f(x) = y_f`.
-/
theorem rigidityOfCocenter_tau
    {A B A' B' : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    [TopologicalSpace A'] [MetrizableSpace A']
    [TopologicalSpace B'] [T2Space B']
    {f : A → B} {g : A' → B'}
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    {σ : A → A'} {τ : B' → B}
    (hσ : Continuous σ)
    (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a))) :
    τ (cocenter g hg_cent) = cocenter f hf_cent := by
  -- The cocenter values are determined by scatteredness (`scatteredHaveCocenter`).
  have hy_f : ∀ x, IsCenterFor f x → f x = cocenter f hf_cent := fun x hx =>
    scatteredHaveCocenter f hf_scat x hf_cent.choose hx hf_cent.choose_spec
  have hy_g : ∀ x, IsCenterFor g x → g x = cocenter g hg_cent := fun x hx =>
    scatteredHaveCocenter g hg_scat x hg_cent.choose hx hg_cent.choose_spec
  rw [← hy_g _ (centerInvariance_equiv hf_cent.choose_spec hequiv hσ hτ_cont hτ_eq),
    ← hy_f _ hf_cent.choose_spec, hτ_eq]

/-
**Proposition 4.4 (Rigidityofthecocenter) — Item 2.**
For all `n ∈ ℕ`, `y_g ∉ cl(g ∘ σ(dom(Ray(f, y_f, n))))`.

*Proof:* Suppose not, then there is a sequence `(x_i) ⊆ dom(Ray(f, y_f, n))` with
`g(σ(x_i)) → y_g`, so `f(x_i) = τ(g(σ(x_i))) → τ(y_g) = y_f`. But by definition
of rays, `f(x_i) ∉ N_{y_f|_{n+1}}`, contradiction.
-/
theorem rigidityOfCocenter_separation
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {f g : A → ℕ → ℕ}
    (_hf_scat : ScatteredFun f) (_hg_scat : ScatteredFun g)
    (_hf_cent : IsCentered f) (_hg_cent : IsCentered g)
    (_hequiv : ContinuouslyEquiv f g)
    (σ : A → A) (τ : (ℕ → ℕ) → (ℕ → ℕ))
    (_hσ : Continuous σ) (hτ : ContinuousOn τ (Set.range (g ∘ σ)))
    (hred : ∀ a, f a = τ (g (σ a)))
    (y_f y_g : ℕ → ℕ)
    (_hy_f : ∀ x, IsCenterFor f x → f x = y_f)
    (_hy_g : ∀ x, IsCenterFor g x → g x = y_g)
    (hτ_yg : τ y_g = y_f) (hyg_mem : y_g ∈ Set.range (g ∘ σ)) :
    ∀ n : ℕ, y_g ∉ closure (Set.range
      (fun (x : {a : A | (∀ k, k < n → f a k = y_f k) ∧ f a n ≠ y_f n}) =>
        g (σ x.val))) := by
  intro n hn
  obtain ⟨x_i, hx_i⟩ : ∃ (x_i : ℕ → {a : A | (∀ k < n, f a k = y_f k) ∧ f a n ≠ y_f n}), Filter.Tendsto (fun i => g (σ (x_i i))) Filter.atTop (nhds y_g) := by
    rw [mem_closure_iff_seq_limit] at hn
    exact ⟨fun i => Classical.choose (hn.choose_spec.1 i), by simpa only [Classical.choose_spec (hn.choose_spec.1 _)] using hn.choose_spec.2⟩
  have h_contra : ∀ᶠ i in Filter.atTop, f (x_i i) n = y_f n := by
    have h_contra : Filter.Tendsto (fun i => f (x_i i)) Filter.atTop (nhds y_f) := by
      -- `τ` is continuous within `range (g ∘ σ)` at `y_g`, and the sequence stays in it.
      have hx' : Filter.Tendsto (fun i => g (σ (x_i i))) Filter.atTop
          (nhdsWithin y_g (Set.range (g ∘ σ))) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx_i
          (Filter.Eventually.of_forall (fun i => ⟨(x_i i : A), rfl⟩))
      have hcomp := Filter.Tendsto.comp (hτ _ hyg_mem) hx'
      rw [hτ_yg] at hcomp
      simpa only [Function.comp, hred] using hcomp
    rw [tendsto_pi_nhds] at h_contra
    simpa using h_contra n
  exact h_contra.exists.elim fun i hi => x_i i |>.2.2 hi

/-- **Continuity of a reduction at the cocenter.**
If `(σ, τ)` witnesses `F.func ≤ G.func` (both centered scattered) and a family `x i`
satisfies `G.func (σ (x i)) → y_g` (the cocenter of `G`), then `F.func (x i) → y_f`
(the cocenter of `F`).

This is the analytic heart of Proposition 4.4.  Although `τ` is only continuous on
`range (G.func ∘ σ)`, the cocenter `y_g = G.func (σ x_f)` *lies in* that range (where
`x_f` is a center of `F`, so `σ x_f` is a center of `G` by `centerInvariance_equiv` and
`G.func (σ x_f) = y_g` by `scatteredHaveCocenter`), and `τ y_g = y_f`.  So `τ` is
genuinely continuous at the limit point, and the conclusion follows by transporting the
convergence through `τ`. -/
lemma reduction_tendsto_cocenter {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MetrizableSpace B]
    {f : A → Baire} {g : B → Baire}
    (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    {σ : A → B} (hσ : Continuous σ)
    {τ : Baire → Baire} (hτ : ContinuousOn τ (Set.range (g ∘ σ)))
    (hred : ∀ a, f a = τ (g (σ a)))
    {ι : Type*} {l : Filter ι} {x : ι → A}
    (hx : Filter.Tendsto (fun i => g (σ (x i))) l (nhds (cocenter g hg_cent))) :
    Filter.Tendsto (fun i => f (x i)) l (nhds (cocenter f hf_cent)) := by
  set xf := hf_cent.choose with hxf_def
  have hxf : IsCenterFor f xf := hf_cent.choose_spec
  -- `σ x_f` is a center of `g`, so it is mapped to the cocenter `y_g`.
  have hcenterG : IsCenterFor g (σ xf) :=
    centerInvariance_equiv hxf hequiv hσ hτ hred
  have hyg_eq : g (σ xf) = cocenter g hg_cent :=
    scatteredHaveCocenter g hg_scat (σ xf) hg_cent.choose hcenterG hg_cent.choose_spec
  have hyg_mem : cocenter g hg_cent ∈ Set.range (g ∘ σ) := ⟨xf, hyg_eq⟩
  -- `τ y_g = y_f`.
  have hτyf : τ (cocenter g hg_cent) = cocenter f hf_cent := by
    rw [← hyg_eq, ← hred xf]
    rfl
  -- `τ` is continuous within the range at `y_g`, and the sequence stays in the range.
  have hwithin : ContinuousWithinAt τ (Set.range (g ∘ σ)) (cocenter g hg_cent) :=
    hτ _ hyg_mem
  have hx' : Filter.Tendsto (fun i => g (σ (x i))) l
      (nhdsWithin (cocenter g hg_cent) (Set.range (g ∘ σ))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx
      (Filter.Eventually.of_forall (fun i => ⟨x i, rfl⟩))
  have hcomp : Filter.Tendsto (fun i => τ (g (σ (x i)))) l
      (nhds (cocenter f hf_cent)) := by
    have := Filter.Tendsto.comp hwithin hx'
    rwa [hτyf] at this
  simpa only [hred] using hcomp

/-- **Center of an open restriction.**  If `x` is a center of `f` and `V` is an open
neighbourhood of `x`, then `⟨x, _⟩` is a center of the restriction `f|_V = f ∘ val`.

The witnessing reductions for `f ≤ f|_W'` (`W' ⊆ V` open around `x`) come from the
center property of `f` on the ambient nbhd `val '' W'`, transported across the open
embedding `val : V → A`. -/
lemma isCenterFor_restrict {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {x : A} (hx : IsCenterFor f x)
    {V : Set A} (hV : IsOpen V) (hxV : x ∈ V) :
    IsCenterFor (f ∘ (Subtype.val : V → A)) ⟨x, hxV⟩ := by
  intro W hW hxW
  -- `W' = val '' W ⊆ A` is open (open embedding) and contains `x`.
  set W' : Set A := Subtype.val '' W with hW'_def
  have hW'_open : IsOpen W' := hV.isOpenMap_subtype_val W hW
  have hxW' : x ∈ W' := ⟨⟨x, hxV⟩, hxW, rfl⟩
  obtain ⟨σ₀, hσ₀, τ₀, hτ₀, h₀⟩ := hx W' hW'_open hxW'
  -- Every point of `W'` lies in `V`, and (re-realised in `↥V`) lies in `W`.
  have hsubV : ∀ w' : ↥W', (w' : A) ∈ V := by
    rintro ⟨a, b, _, rfl⟩; exact b.2
  have hsubW : ∀ w' : ↥W', (⟨(w' : A), hsubV w'⟩ : ↥V) ∈ W := by
    rintro ⟨a, b, hbW, rfl⟩
    have : (⟨(b : A), hsubV ⟨(b : A), b, hbW, rfl⟩⟩ : ↥V) = b := Subtype.ext rfl
    rw [this]; exact hbW
  set φ : ↥W' → ↥W := fun w' => ⟨⟨(w' : A), hsubV w'⟩, hsubW w'⟩ with hφ
  have hφ_cont : Continuous φ :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  -- Reduce `f∘val_V ≤ (f∘val_V)|_W` via `(φ ∘ σ₀ ∘ val_V, τ₀)`.
  refine ⟨fun v => φ (σ₀ ((Subtype.val : V → A) v)), ?_, τ₀, ?_, ?_⟩
  · exact hφ_cont.comp (hσ₀.comp continuous_subtype_val)
  · refine hτ₀.mono ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨(v : A), rfl⟩
  · intro v
    exact h₀ (v : A)

/-- **Cylinder basis bound.**  If `y` is not in the closure of `S ⊆ Baire`, some finite
initial segment `[0, M)` already witnesses that every point of `S` differs from `y`.
(The complement of `closure S` is an open neighbourhood of `y`, hence contains a cylinder
`nbhd y M`, which is therefore disjoint from `S`.) -/
lemma exists_lt_disagree_of_notMem_closure {S : Set Baire} {y : Baire}
    (h : y ∉ closure S) : ∃ M : ℕ, ∀ z ∈ S, ∃ k < M, z k ≠ y k := by
  obtain ⟨M, hM⟩ := nbhd_basis y (closure S)ᶜ isClosed_closure.isOpen_compl h
  refine ⟨M, fun z hz => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hz_nbhd : z ∈ nbhd y M := by
    simp only [nbhd, Set.mem_setOf_eq]
    exact fun i hi => hcon i (Finset.mem_range.mp hi)
  exact hM hz_nbhd (subset_closure hz)

/-- **Separation for the pushed ray (the analytic core of Item 3).**
With `(σ, τ)` reducing `F.func ≤ G.func`, `x_f` a center of `F`, `V` an open nbhd of
`x_f`, and `(ρ, κ)` the center-reduction `F.func ≤ F.func|_V`, the cocenter `y_g` is not
in the closure of the image of the `n`-ray of `F` under `G.func ∘ σ ∘ ρ`.

*Proof:* a sequence converging to `y_g` would, by `reduction_tendsto_cocenter` applied to
`(σ, τ)`, force `F.func (val (ρ x_j)) → y_f`; since `y_f = cocenter (F.func|_V)`, a second
application of `reduction_tendsto_cocenter` to `(ρ, κ)` forces `F.func (x_j) → y_f`,
contradicting membership in the ray (where the `n`-th coordinate stays `≠ y_f n`). -/
lemma ray_separation
    (F G : ScatFun) (hF_cent : IsCentered F.func) (hG_cent : IsCentered G.func)
    (hequiv : ContinuouslyEquiv F.func G.func)
    {σ : ↑F.domain → ↑G.domain} (hσ : Continuous σ)
    {τ : Baire → Baire} (hτ : ContinuousOn τ (Set.range (G.func ∘ σ)))
    (hred : ∀ a, F.func a = τ (G.func (σ a)))
    {V : Set ↑F.domain} (hV : IsOpen V) {xf : ↑F.domain} (hxfV : xf ∈ V)
    (hxf : IsCenterFor F.func xf)
    {ρ : ↑F.domain → ↥V} (hρ : Continuous ρ)
    {κ : Baire → Baire} (hκ : ContinuousOn κ (Set.range ((F.func ∘ Subtype.val) ∘ ρ)))
    (hred_c : ∀ a, F.func a = κ (F.func (Subtype.val (ρ a)))) (n : ℕ) :
    cocenter G.func hG_cent ∉ closure (Set.range
      (fun (x : {a : ↑F.domain | (∀ k, k < n → F.func a k = cocenter F.func hF_cent k) ∧
          F.func a n ≠ cocenter F.func hF_cent n}) =>
        G.func (σ (Subtype.val (ρ x.val))))) := by
  -- The restricted function `F.func|_V`, bundled with scatteredness/centeredness/equiv.
  set gV : ↥V → Baire := F.func ∘ (Subtype.val : V → ↑F.domain) with hgV
  have hVscat : ScatteredFun gV := scattered_restrict F.func F.hScat V
  have hVcent : IsCentered gV := ⟨⟨xf, hxfV⟩, isCenterFor_restrict hxf hV hxfV⟩
  have hVequiv : ContinuouslyEquiv F.func gV :=
    ⟨⟨ρ, hρ, κ, hκ, hred_c⟩,
     ⟨Subtype.val, continuous_subtype_val, id, continuousOn_id, fun _ => rfl⟩⟩
  -- The cocenter of `F.func|_V` is the cocenter of `F.func`.
  have hxf_cocenter : F.func xf = cocenter F.func hF_cent :=
    scatteredHaveCocenter F.func F.hScat xf hF_cent.choose hxf hF_cent.choose_spec
  have hVcocenter : cocenter gV hVcent = cocenter F.func hF_cent := by
    have h := scatteredHaveCocenter gV hVscat hVcent.choose ⟨xf, hxfV⟩ hVcent.choose_spec
      (isCenterFor_restrict hxf hV hxfV)
    rw [show cocenter gV hVcent = gV hVcent.choose from rfl, h]
    exact hxf_cocenter
  -- Suppose the cocenter were in the closure; extract a sequence.
  intro hmem
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨u, hu_mem, hu_lim⟩ := hmem
  choose x_j hx_j using hu_mem
  have hlim1 : Filter.Tendsto (fun j => G.func (σ (Subtype.val (ρ (x_j j).val)))) Filter.atTop
      (nhds (cocenter G.func hG_cent)) := by simpa only [hx_j] using hu_lim
  -- First engine application: along `σ`, the pushed source converges to `y_f`.
  have hlim2 : Filter.Tendsto (fun j => F.func (Subtype.val (ρ (x_j j).val))) Filter.atTop
      (nhds (cocenter F.func hF_cent)) :=
    reduction_tendsto_cocenter G.hScat hF_cent hG_cent hequiv hσ hτ hred hlim1
  -- Second engine application: along `ρ` (the center-reduction), the source converges to `y_f`.
  have hlim3 : Filter.Tendsto (fun j => F.func ((x_j j).val)) Filter.atTop
      (nhds (cocenter F.func hF_cent)) := by
    have hx2 : Filter.Tendsto (fun j => gV (ρ ((x_j j).val))) Filter.atTop
        (nhds (cocenter gV hVcent)) := by rw [hVcocenter]; exact hlim2
    exact reduction_tendsto_cocenter hVscat hF_cent hVcent hVequiv hρ hκ hred_c hx2
  -- But the source stays in the `n`-ray, so its `n`-th coordinate never equals `y_f n`.
  rw [tendsto_pi_nhds] at hlim3
  have hev : ∀ᶠ j in Filter.atTop, F.func ((x_j j).val) n = cocenter F.func hF_cent n := by
    simpa using hlim3 n
  obtain ⟨j, hj⟩ := hev.exists
  exact (x_j j).2.2 hj

/-- **Proposition 4.4 (Rigidityofthecocenter) — Item 3.**
For all `m, n ∈ ℕ` there is `M ≥ m` such that
`Ray(f, y_f, n) ≤ ⊔_{i=m}^{M} Ray(g, y_g, i)`.

*Proof:* Use continuity of `g` to find `U ∋ σ(x)` open with `g(U) ⊆ N_{y_g|_m}`.
Since `σ(x)` is a center for `g`, find `(σ', τ')` reducing `f` to `g|_U`.
By the separation property, find `M > m` with `N_{y_g|_{M+1}}` disjoint from
the closure of `g ∘ σ'(dom(Ray(f, y_f, n)))`. -/
theorem rigidityOfCocenter_finiteGluing
    (F G : ScatFun)
    (hF_cent : IsCentered F.func) (hG_cent : IsCentered G.func)
    (hequiv : ContinuouslyEquiv F.func G.func) :
    ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧
      ContinuouslyReduces
        (fun (x : {a : ↑F.domain | (∀ k, k < n → F.func a k = cocenter F.func hF_cent k) ∧
            F.func a n ≠ cocenter F.func hF_cent n}) =>
          F.func x.val) -- the ray of F at n
        (fun (x : {a : ↑G.domain | ∃ i, m ≤ i ∧ i ≤ M ∧ -- the gluing of rays [m, M] of G
          (∀ k, k < i → G.func a k = cocenter G.func hG_cent k) ∧
          G.func a i ≠ cocenter G.func hG_cent i}) => G.func x.val) := by
  intro m n
  -- Step 1: a reduction `(σ, τ)` of `F.func ≤ G.func`; `σ x_f` is a center of `G` whose
  -- image is the cocenter `y_g`.
  obtain ⟨σ, hσ, τ, hτ, hred⟩ := hequiv.1
  have hxf : IsCenterFor F.func hF_cent.choose := hF_cent.choose_spec
  have hcenterG : IsCenterFor G.func (σ hF_cent.choose) :=
    centerInvariance_equiv hxf hequiv hσ hτ hred
  have hyg_eq : G.func (σ hF_cent.choose) = cocenter G.func hG_cent :=
    scatteredHaveCocenter G.func G.hScat _ hG_cent.choose hcenterG hG_cent.choose_spec
  -- Step 2: lower-bound neighbourhood `U ∋ σ x_f`; pull back to `V ∋ x_f`.
  obtain ⟨U, hU_open, hσxfU, hU⟩ :=
    cocenter_continuity_cylinder continuous_id (σ hF_cent.choose) (cocenter G.func hG_cent)
      G.hCont hcenterG hyg_eq m
  set V : Set ↑F.domain := σ ⁻¹' U with hV_def
  have hV_open : IsOpen V := hU_open.preimage hσ
  have hxfV : hF_cent.choose ∈ V := by simpa [hV_def, Set.mem_preimage] using hσxfU
  -- Step 3: the center-reduction `F.func ≤ F.func|_V`, witnessed by `(ρ, κ)`.
  obtain ⟨ρ, hρ, κ, hκ, hred_c⟩ := hxf V hV_open hxfV
  -- Step 4: separation — `y_g` avoids the closure of the pushed ray image.
  have hsep := ray_separation F G hF_cent hG_cent hequiv hσ hτ hred hV_open hxfV hxf hρ hκ
    hred_c n
  -- Step 5: a uniform bound `M₀` from the cylinder basis.
  obtain ⟨M₀, hM₀⟩ := exists_lt_disagree_of_notMem_closure hsep
  refine ⟨max m M₀, le_max_left _ _, ?_⟩
  -- Step 6: assemble the reduction `(x ↦ ⟨σ (val (ρ x.val)), _⟩, κ ∘ τ)`.
  -- Membership of each pushed source point in `⊔_{[m, max m M₀]} Ray_G`.
  have hmem : ∀ (x : {a : ↑F.domain | (∀ k, k < n → F.func a k = cocenter F.func hF_cent k) ∧
        F.func a n ≠ cocenter F.func hF_cent n}),
      σ (Subtype.val (ρ x.val)) ∈
        {a : ↑G.domain | ∃ i, m ≤ i ∧ i ≤ max m M₀ ∧
          (∀ k, k < i → G.func a k = cocenter G.func hG_cent k) ∧
          G.func a i ≠ cocenter G.func hG_cent i} := by
    intro x
    have hb_range : G.func (σ (Subtype.val (ρ x.val))) ∈ Set.range
        (fun (y : {a : ↑F.domain | (∀ k, k < n → F.func a k = cocenter F.func hF_cent k) ∧
            F.func a n ≠ cocenter F.func hF_cent n}) =>
          G.func (σ (Subtype.val (ρ y.val)))) := ⟨x, rfl⟩
    have hb_ne : G.func (σ (Subtype.val (ρ x.val))) ≠ cocenter G.func hG_cent :=
      fun h => hsep (h ▸ subset_closure hb_range)
    have hb_ex : ∃ k, G.func (σ (Subtype.val (ρ x.val))) k ≠ cocenter G.func hG_cent k :=
      Function.ne_iff.mp hb_ne
    have hb_in_U : σ (Subtype.val (ρ x.val)) ∈ U := (ρ x.val).2
    refine ⟨Nat.find hb_ex, ?_, ?_, ?_, Nat.find_spec hb_ex⟩
    · rw [Nat.le_find_iff]
      exact fun k hk => not_ne_iff.mpr (hU _ hb_in_U k hk)
    · obtain ⟨k₀, hk₀M, hk₀ne⟩ := hM₀ _ hb_range
      exact le_trans (Nat.find_le hk₀ne) (le_trans hk₀M.le (le_max_right m M₀))
    · exact fun k hk => not_ne_iff.mp (Nat.find_min hb_ex hk)
  refine ⟨fun x => ⟨σ (Subtype.val (ρ x.val)), hmem x⟩, ?_, κ ∘ τ, ?_, ?_⟩
  · exact Continuous.subtype_mk
      (hσ.comp (continuous_subtype_val.comp (hρ.comp continuous_subtype_val))) _
  · apply ContinuousOn.comp hκ
    · refine hτ.mono ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨Subtype.val (ρ x.val), rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨x.val, hred (Subtype.val (ρ x.val))⟩
  · intro x
    show F.func x.val = κ (τ (G.func (σ (Subtype.val (ρ x.val)))))
    rw [hred_c x.val]
    exact congrArg κ (hred (Subtype.val (ρ x.val)))

/--
**Proposition 4.4 (Rigidityofthecocenter) — Item 4.**
`(Ray(f, y_f, n))_{n ∈ ℕ}` is reducible by finite pieces to `(Ray(g, y_g, n))_{n ∈ ℕ}`.
This follows from a recursive application of Item 3.
-/
theorem rigidityOfCocenter_reducibleByPieces
    (F G : ScatFun)
    (hF_cent : IsCentered F.func) (hG_cent : IsCentered G.func)
    (hequiv : ContinuouslyEquiv F.func G.func) :
    ∃ (I : ℕ → Finset ℕ),
      (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
      ∀ n, ContinuouslyReduces
        (fun (x : {a : ↑F.domain | (∀ k, k < n → F.func a k = cocenter F.func hF_cent k) ∧
            F.func a n ≠ cocenter F.func hF_cent n}) =>
          F.func x.val)
        (fun (x : {a : ↑G.domain | ∃ i ∈ I n,
          (∀ k, k < i → G.func a k = cocenter G.func hG_cent k) ∧
            G.func a i ≠ cocenter G.func hG_cent i}) =>
          G.func x.val) := by
  by_contra h_contra
  have :=rigidityOfCocenter_finiteGluing F G hF_cent hG_cent hequiv
  choose M hM₁ hM₂ using this
  refine h_contra ⟨fun n => Finset.Icc (Nat.recOn n 0 fun n IH => M IH n + 1) (M (Nat.recOn n 0 fun n IH => M IH n + 1) n), ?_, ?_⟩
  · intro m n hmn
    cases lt_or_gt_of_ne hmn <;> simp +decide [*, Finset.disjoint_left]
    · intro a ha₁ ha₂ ha₃
      refine absurd ha₃ (not_le_of_gt ?_)
      refine' Nat.le_induction _ _ n ‹_› <;> intros <;> simp +decide [*]
      exact le_trans (by linarith) (hM₁ _ _)
    · refine fun a ha₁ ha₂ ha₃ => lt_of_lt_of_le ?_ ha₁
      refine' Nat.le_induction _ _ m ‹_› <;> intros <;> simp +decide [*]
      exact le_trans (by linarith) (hM₁ _ _)
  · intro n
    obtain ⟨σ, hσ, τ, hτ, h⟩ := hM₂ (Nat.recOn n 0 fun n IH => M IH n + 1) n
    refine ⟨?_, ?_, ?_⟩
    use fun x => ⟨σ x |>.1, by
      exact ⟨_, Finset.mem_Icc.mpr ⟨σ x |>.2.choose_spec.1, σ x |>.2.choose_spec.2.1⟩, σ x |>.2.choose_spec.2.2.1, σ x |>.2.choose_spec.2.2.2⟩⟩
    all_goals generalize_proofs at *
    · fun_prop
    · exact ⟨τ, hτ, h⟩

/-
**Corollary 4.5 (ResidualCorestrictionOfCentered).**
If `f ∈ 𝒞` and `f ≡ pgl G` for some finite `G ⊆ 𝒞`, then `f` is centered.
Moreover, for every open set `V ⊆ B` excluding its cocenter, `f↾V ≤ FinGl(G)`.

*Proof:* Since `f ≡ pgl G`, by Pgluingofregulariscentered, `g(0^ω) = 0^ω` is
the cocenter of `g`, so `f` is centered by Centerinvariance and `y = τ(0^ω)`
is the cocenter of `f`. By Rigidityofthecocenter, `(Ray(f, y, n))_n` is
reducible by finite pieces to `ω · ⊔G`. So for all `n`, `Ray(f, y, n) ≤ FinGl(G)`,
and if `V` excludes `y`, then `f↾V` is covered by finitely many rays.

Centeredness is preserved by continuous equivalence: if `g` is centered and
    `f ≡ g`, then `f` is centered.
-/
theorem isCentered_of_equiv
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g) : IsCentered f := by
  -- Since `g` is centered, there exists `x₀` with `IsCenterFor g x₀`. We claim `σ'(x₀)` is a center for `f`.
  obtain ⟨σ', hσ'_cont, τ', hτ'_cont, hτ'_eq⟩ := hequiv.2
  obtain ⟨x₀, hx₀⟩ := hg_cent
  use σ' x₀
  have := centerInvariance_equiv hx₀ hequiv.symm hσ'_cont hτ'_cont (fun x => hτ'_eq x ▸ rfl) ; aesop

theorem residualCorestrictionOfCentered
    (F : ScatFun)
    (g : ℕ → ScatFun)
    (hg_reg : Preorder.IsRegularSeq ScatFun.Reduces g)
    (hequiv : ContinuouslyEquiv F.func (ScatFun.pgl g).func) :
    IsCentered F.func := by
  convert isCentered_of_equiv _ hequiv using 1
  exact ⟨⟨_, zeroStream_mem_pointedGluingSet _⟩, pgluingOfRegularIsCentered g hg_reg⟩

-- **Theorem 4.6 (CenteredAsPgluing) — Item 1 (forward).**  Restated at the `ScatFun`
-- level as `centeredAsPgluing_forward` in `CenteredFunctions/LocallyCentered/Theorem.lean`,
-- where the constructive `ScatFun.reduces_pgl_rays` (the proper replacement for the old
-- degenerate `pointedGluing_rays_upper_bound`) is in scope.

-- §4.1 Theorem 4.6 (CenteredAsPgluing) — `centeredAsPgluing_forward/backward`,
-- `centered_equiv_pgl_rays`, `monotone_pgluing_of_centered`, `centeredAsPgluing_iff_monotone`,
-- `centeredAsPgluing_CBrank` (+ the ray machinery) — live in
-- `CenteredFunctions/CenteredAsPgluing.lean` (and its `.Helpers`).
-- The Theorem 4.9 helper lemmas → `CenteredFunctions/FinitenessHelpers.lean`;
-- `finitenessOfCenteredFunctions` itself → `CenteredFunctions/Finiteness.lean`.

open ScatFun in
/-- **Result 1 (limit-rank equivalence) — `ConsequencesGeneralStructureThm`.**
Every scattered continuous function of *limit* CB-rank `lam < ω₁` is continuously
equivalent to the maximum function `ℓ_lam` (`maxFun lam`).

This packages, at the `ScatFun` level, the consequence of the General Structure
Theorem (`general_structure_theorem`, item 1): at a limit rank there is a single
`≡`-class, represented by `ℓ_lam`.  Both reductions are instances of item 1 (with
the roles of the two functions swapped), using that `CBRank ℓ_lam = lam`
(`maxFun_cbRank_eq`). -/
theorem limit_rank_equiv_maxFun (F : ScatFun) (lam : Ordinal.{0})
    (hlam_lt : lam < omega1) (hlim : Order.IsSuccLimit lam)
    (hrank : CBRank F.func = lam) :
    ScatFun.Equiv F (ScatFun.maxFun lam hlam_lt) := by
  have hmaxrank : CBRank (ScatFun.maxFun lam hlam_lt).func = lam := by
    rw [ScatFun.maxFun_func]; exact maxFun_cbRank_eq lam hlam_lt
  have hmscat : ScatteredFun (ScatFun.maxFun lam hlam_lt).func :=
    (ScatFun.maxFun lam hlam_lt).hScat
  have hmcont : Continuous (ScatFun.maxFun lam hlam_lt).func :=
    (ScatFun.maxFun lam hlam_lt).hCont
  refine ⟨?_, ?_⟩
  · -- `F ≤ ℓ_lam`: item 1 with `g = ℓ_lam`.
    exact (general_structure_theorem F.domain (ScatFun.maxFun lam hlam_lt).domain
      F.func (ScatFun.maxFun lam hlam_lt).func F.hScat hmscat F.hCont hmcont
      lam hlam_lt (Or.inl hlim)).1 ⟨hmaxrank, le_of_eq (hrank.trans hmaxrank.symm)⟩
  · -- `ℓ_lam ≤ F`: `ℓ_lam` is a lower bound at limit rank (`MaxFun_le_limit_rank`),
    -- avoiding the verbose `general_structure_theorem` round-trip.
    exact MaxFun_le_limit_rank lam hlam_lt hlim F.domain F.func F.hCont F.hScat hrank


namespace ConseqMinFunAux

lemma ordinal_limit_add_nat (o : Ordinal.{0}) :
    ∃ (η : Ordinal.{0}) (k : ℕ), o = η + k ∧ (η = 0 ∨ Order.IsSuccLimit η) := by
  induction o using Ordinal.limitRecOn with
  | zero => exact ⟨0, 0, by simp, Or.inl rfl⟩
  | succ o ih =>
      obtain ⟨η, k, rfl, h⟩ := ih
      exact ⟨η, k + 1, by push_cast; rw [← add_assoc, Ordinal.add_one_eq_succ], h⟩
  | limit o hlim ih => exact ⟨o, 0, by simp, Or.inr hlim⟩


lemma cbRank_rayFun_pgl (s : ℕ → ScatFun) (n : ℕ) :
    CBRank (RayFun (ScatFun.pgl s).func zeroStream n) = CBRank (s n).func := by
  refine le_antisymm ?_ ?_;
  · -- By definition of `RayFun`, we know that `RayFun (ScatFun.pgl s).func zeroStream n` is continuously reducible to `(s n).func`.
    have h_ray_reduces : ContinuouslyReduces (RayFun (ScatFun.pgl s).func zeroStream n) (s n).func := by
      refine ⟨ ?_, ?_ ⟩;
      exact fun x => ⟨ stripZerosOne n x.val.val, by
        have := x.2.1; have := x.2.2; simp_all +decide [ ScatFun.pgl, PointedGluingFun ] ;
        split_ifs at this <;> simp_all +decide [ ScatFun.pglBlock ];
        have h_firstNonzero : firstNonzero x.val.val = n := by
          exact le_antisymm ( le_of_not_gt fun h => this <| by
            exact if_pos h ) ( le_of_not_gt fun h => by
            simp_all +decide [ prependZerosOne, zeroStream ];
            grind +splitImp )
        generalize_proofs at *; (
        grind) ⟩
      generalize_proofs at *; (
      refine ⟨ ?_, ?_ ⟩
      all_goals generalize_proofs at *;
      · exact Continuous.subtype_mk ( continuous_stripZerosOne n |> Continuous.comp <| continuous_subtype_val.comp continuous_subtype_val ) _;
      · refine ⟨ fun x => prependZerosOne n x, ?_, ?_ ⟩ <;> simp +decide [ RayFun ];
        · exact Continuous.continuousOn ( continuous_prependZerosOne n );
        · intro a ha hp hq
          have h_block : ∃ w : (s n).domain, a = prependZerosOne n w.val := by
            obtain ⟨ i, hi ⟩ := ha
            generalize_proofs at *; (
            simp_all +decide [ ScatFun.pgl_func_zeroStream ]);
            obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ‹_›
            generalize_proofs at *; (
            obtain ⟨ w, hw, rfl ⟩ := hi
            generalize_proofs at *; (
            have h_block : i = n := by
              have h_block : (ScatFun.pgl s).func ⟨prependZerosOne i w, by
                assumption⟩ = prependZerosOne i ((s i).func ⟨w, hw⟩) := by
                exact ScatFun.pgl_func_block s i ⟨ w, hw ⟩
              generalize_proofs at *; (
              by_cases hi : i < n <;> simp_all +decide [ prependZerosOne ];
              · specialize hp i hi ; simp_all +decide [ zeroStream ];
              · cases lt_or_eq_of_le hi <;> simp_all +decide [ zeroStream ])
            generalize_proofs at *; (
            exact ⟨ ⟨ w, by aesop ⟩, by aesop ⟩)))
          generalize_proofs at *; (
          obtain ⟨ w, rfl ⟩ := h_block; simp +decide [ ScatFun.pgl_func_block ] ;
          grind [stripZerosOne_prependZerosOne]))
    generalize_proofs at *; (
    apply_rules [ ContinuouslyReduces.rank_monotone ];
    · have h_ray_scattered : ScatteredFun (ScatFun.pgl s).func := by
        exact ScatFun.pgl _ |>.hScat
      generalize_proofs at *;
      exact scattered_restrict (ScatFun.pgl s).func h_ray_scattered
        {a | (∀ k < n, (ScatFun.pgl s).func a k = zeroStream k) ∧
          (ScatFun.pgl s).func a n ≠ zeroStream n};
    · exact ( s n ).hScat);
  · -- By definition of `RayFun`, we know that `(s n).func` is continuously reducible to `RayFun (ScatFun.pgl s).func zeroStream n`.
    have h_reducible : ContinuouslyReduces (s n).func (RayFun (ScatFun.pgl s).func zeroStream n) := by
      refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
      refine fun x => ⟨ ⟨ prependZerosOne n x.val, prependZerosOne_mem_pointedGluingSet _ n x.val x.prop ⟩, ?_, ?_ ⟩ <;> simp +decide [ ScatFun.pgl_func_block ];
      any_goals intro x; exact stripZerosOne n x;
      all_goals norm_num [ prependZerosOne, zeroStream ];
      any_goals intros; linarith;
      · refine Continuous.subtype_mk ?_ ?_;
        refine' Continuous.subtype_mk _ _;
        exact continuous_prependZerosOne n |> Continuous.comp <| continuous_subtype_val;
      · exact Continuous.continuousOn ( continuous_stripZerosOne n );
      · grind [ScatFun.pgl_func_block, stripZerosOne_prependZerosOne];
    apply_rules [ ContinuouslyReduces.rank_monotone ];
    · exact ( s n ).hScat;
    · have h_scattered : ScatteredFun (ScatFun.pgl s).func := by
        exact ScatFun.pgl _ |>.hScat;
      exact scattered_restrict (ScatFun.pgl s).func h_scattered
        {a | (∀ k < n, (ScatFun.pgl s).func a k = zeroStream k) ∧
          (ScatFun.pgl s).func a n ≠ zeroStream n}


theorem centeredAsPgluing_CBrank
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f)
    (y : ℕ → ℕ) (hy : ∀ x, IsCenterFor f x → f x = y) :
    CBRank f = Order.succ (⨆ n, CBRank (RayFun f y n)) := by
  -- `f` is simple: rank `α + 1`, with `f` constant `= y` on `CB_α`.
  obtain ⟨α, hrank, hne, _hempty, hsimple⟩ :=
    centered_scattered_simple_structure f hf_scat hf_cent y hy
  -- `RayFun f y n` has the same CB-rank as the `RaySet`-form ray used by the helpers
  -- (their domains coincide, since `f a ∈ B` always).
  have hray_eq : ∀ n, CBRank (RayFun f y n)
      = CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) := by
    intro n
    have hD : {a : A | (∀ k, k < n → f a k = y k) ∧ f a n ≠ y n}
            = {a : A | f a ∈ RaySet B y n} := by
      ext a; simp only [RaySet, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hfB a, h⟩, fun h => h.2⟩
    exact CBRank_comp_homeomorph (Homeomorph.setCongr hD)
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)
  -- The supremum of the ray CB-ranks is exactly `α` (`sup_ray_cb_eq_alpha`).
  have hsup : (⨆ n, CBRank (RayFun f y n)) = α := by
    rw [iSup_congr hray_eq]
    exact sup_ray_cb_eq_alpha f hfB hf hf_scat α hne y hsimple
      (fun n => CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val))
      (fun _ => rfl) (fun n => ray_cb_le_alpha f hf α y hsimple n)
  rw [hrank, hsup]

lemma cbRank_pgl_regular (s : ℕ → ScatFun)
    (hs : Preorder.IsRegularSeq ScatFun.Reduces s) :
    CBRank (ScatFun.pgl s).func = Order.succ (⨆ i, CBRank (s i).func) := by
  convert centeredAsPgluing_CBrank _ _ _ _ _ _ _;
  convert cbRank_rayFun_pgl s _ |> Eq.symm;
  exact Set.univ;
  · exact fun _ => Set.mem_univ _;
  · exact ( ScatFun.pgl s ).hCont;
  · exact ( ScatFun.pgl s ).hScat;
  · exact ⟨ _, pgluingOfRegularIsCentered s hs ⟩;
  · intro x hx;
    have := scatteredHaveCocenter ( ScatFun.pgl s ).func ( ScatFun.pgl s ).hScat x ⟨ zeroStream, zeroStream_mem_pointedGluingSet _ ⟩ hx ( pgluingOfRegularIsCentered s hs );
    exact this.trans ( ScatFun.pgl_func_zeroStream s _ )

lemma minFun_cbRank_via_pgl (α : Ordinal.{0}) (hα : α < omega1)
    (F : ℕ → ScatFun) (hreg : Preorder.IsRegularSeq ScatFun.Reduces F)
    (hblk : ∀ (i : ℕ) (a : ↥(F i).domain), (F i).func a = (a : ℕ → ℕ))
    (hdom : MinDom α = (ScatFun.pgl F).domain) :
    CBRank (ScatFun.minFun α hα).func = Order.succ (⨆ i, CBRank (F i).func) := by
  convert cbRank_pgl_regular F hreg using 1;
  -- By definition of minFun, we have that (ScatFun.minFun α hα).func = Subtype.val.
  have h_minFun_val : (ScatFun.minFun α hα).func = Subtype.val := rfl
  -- By definition of pgl, we have that (ScatFun.pgl F).func = Subtype.val.
  have h_pgl_val : (ScatFun.pgl F).func = Subtype.val := by
    convert scatFun_pgl_func_eq_val F hblk using 1;
    exact ⟨ fun h z => h ▸ rfl, fun h => funext h ⟩
  rw [h_minFun_val, h_pgl_val];
  convert CBRank_comp_homeomorph ( Homeomorph.setCongr hdom ) Subtype.val using 1


lemma iSup_succ_cofinalSeq (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) :
    (⨆ n, Order.succ (cofinalSeq lam n)) = lam := by
  refine le_antisymm ?_ ?_;
  · exact ciSup_le' fun n => Order.succ_le_of_lt ( cofinalSeq_lt lam hlim hne n );
  · refine le_of_forall_lt fun β hβ => ?_;
    obtain ⟨ n, hn ⟩ := cofinalSeq_eventually_ge lam hlam hlim hne β hβ;
    exact lt_of_le_of_lt hn ( lt_of_lt_of_le ( Order.lt_succ _ ) ( le_ciSup ( Ordinal.bddAbove_of_small _ ) _ ) )

/-! ### A monotone cofinal sequence

Used by `ScatFun/PreciseStructure/IntertwineMaxFunLimit.lean` (limit-case intertwining): the running
maximum of `cofinalSeq lam` is, unlike `cofinalSeq` itself, monotone, so any infinite index
subset of it is still cofinal in `lam`. -/

/-- A **monotone** cofinal sequence in a countable limit ordinal `lam`: the running maximum of
`cofinalSeq lam`. -/
noncomputable def monoCofinal (lam : Ordinal.{0}) (k : ℕ) : Ordinal.{0} :=
  (Finset.range (k + 1)).sup (cofinalSeq lam)

lemma monoCofinal_mono (lam : Ordinal.{0}) : Monotone (monoCofinal lam) := by
  exact fun a b hab => Finset.sup_mono <| Finset.range_mono <| by simpa;

lemma monoCofinal_lt (lam : Ordinal.{0}) (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) (k : ℕ) :
    monoCofinal lam k < lam := by
  have h_sup_lt : ∀ i ∈ Finset.range (k + 1), cofinalSeq lam i < lam := by
    exact fun i hi => cofinalSeq_lt lam hlim hne i;
  convert Finset.sup_lt_iff _ |>.2 h_sup_lt using 1;
  exact Ne.bot_lt' (Ne.symm hne)

lemma monoCofinal_iSup_succ (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) :
    (⨆ k, Order.succ (monoCofinal lam k)) = lam := by
  refine le_antisymm ?_ ?_;
  · exact Ordinal.iSup_le fun k => Order.succ_le_of_lt ( monoCofinal_lt lam hlim hne k );
  · -- By definition of `monoCofinal`, we know that `cofinalSeq lam k ≤ monoCofinal lam k`.
    have h_cofinal_le_monoCofinal : ∀ k, cofinalSeq lam k ≤ monoCofinal lam k := by
      intro k; exact Finset.le_sup ( f := cofinalSeq lam ) ( Finset.mem_range.mpr ( Nat.lt_succ_self k ) ) ;
    -- Since `lam` is a limit ordinal, we have `lam = ⨆ k, Order.succ (cofinalSeq lam k)`.
    have h_lam_eq_sup : lam = ⨆ k, Order.succ (cofinalSeq lam k) := by
      exact Eq.symm (iSup_succ_cofinalSeq lam hlam_lt hlim hne);
    exact h_lam_eq_sup.le.trans ( ciSup_mono ( Ordinal.bddAbove_of_small _ ) fun k => Order.succ_le_succ ( h_cofinal_le_monoCofinal k ) )

lemma iSup_succ_monoCofinal_comp (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) (e : ℕ → ℕ) (he : StrictMono e) :
    (⨆ j, Order.succ (monoCofinal lam (e j))) = lam := by
  refine le_antisymm ?_ ?_;
  · refine' ciSup_le fun j => _;
    exact hlim.succ_lt ( monoCofinal_lt lam hlim hne ( e j ) ) |> le_of_lt;
  · convert Ordinal.iSup_le _;
    convert monoCofinal_iSup_succ lam hlam_lt hlim hne |> Eq.symm;
    intro i;
    refine le_trans ?_ ( le_ciSup ?_ i );
    · exact Order.succ_le_succ ( monoCofinal_mono lam ( he.id_le i ) );
    · exact Ordinal.bddAbove_range fun j => Order.succ (monoCofinal lam (e j))

/-! ### A two-valued supremum lemma -/

/-- If `t` is monotone with `⨆ t = lam` and `w ≤ t` pointwise with `w = t` on an infinite set,
then `⨆ w = lam`. -/
lemma iSup_two_valued_infinite {t : ℕ → Ordinal.{0}} (hmono : Monotone t)
    {lam : Ordinal.{0}} (hsup : (⨆ k, t k) = lam)
    {w : ℕ → Ordinal.{0}} (hle : ∀ k, w k ≤ t k)
    {S : Set ℕ} (hS : S.Infinite) (hwS : ∀ k ∈ S, w k = t k) :
    (⨆ k, w k) = lam := by
  refine le_antisymm ?_ ?_;
  · exact hsup ▸ ciSup_mono ( Ordinal.bddAbove_range t ) hle;
  · rw [ ← hsup ];
    refine Ordinal.iSup_le fun k => ?_;
    obtain ⟨ m, hmS, hkm ⟩ := hS.exists_gt k;
    exact le_trans ( hmono hkm.le ) ( hwS m hmS ▸ Ordinal.le_iSup _ _ )

lemma minFun_cbRank_eq (α : Ordinal.{0}) (hα : α < omega1) :
    CBRank (ScatFun.minFun α hα).func = Order.succ α := by
  induction' α using Ordinal.limitRecOn with α ih;
  · have h_domain : (ScatFun.minFun 0 hα).domain = PointedGluingSet (fun _ => ∅) := by
      convert MinDom_zero;
    have := minFun_cbRank_via_pgl 0 hα ( fun _ => ScatFun.empty ) ( scatFun_const_isRegularSeq ScatFun.empty ) ( by
      exact fun i a => False.elim <| a.2.elim ) ( by
      exact h_domain ) ; simp_all +decide [ ScatFun.empty ] ;
    unfold CBRank; simp +decide [ CBLevel ] ;
    rw [ show { α : Ordinal.{0} | _ } = Set.univ from ?_ ] ; simp +decide;
    grind;
  · convert minFun_cbRank_via_pgl ( Order.succ α ) hα ( fun _ => ScatFun.minFun α ( lt_trans ( Order.lt_succ α ) hα ) ) _ _ _ using 1;
    · rw [ ciSup_const, ih ( lt_trans ( Order.lt_succ α ) hα ) ];
    · exact scatFun_const_isRegularSeq _;
    · aesop;
    · exact MinDom_succ α;
  · rename_i α hα ih;
    by_cases hne : α = 0;
    · aesop;
    · convert minFun_cbRank_via_pgl α hα ( fun n => ScatFun.minFun ( cofinalSeq α n ) ( lt_trans ( cofinalSeq_lt α ‹_› hne n ) hα ) ) ( minFun_cofinalSeq_isRegularSeq α hα ‹_› hne ) _ _ using 1;
      · rw [ iSup_congr fun n => ih _ ( cofinalSeq_lt α ‹_› hne n ) ( lt_trans ( cofinalSeq_lt α ‹_› hne n ) hα ) ];
        rw [ iSup_succ_cofinalSeq α hα ‹_› hne ];
      · aesop;
      · convert MinDom_limit α ‹_› hne using 1


lemma minFun_limit_equiv_pgl (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0) :
    ScatFun.Equiv (ScatFun.minFun lam hlam)
      (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n)
          (lt_trans (cofinalSeq_lt lam hlim hne n) hlam))) := by
  -- Apply MinDom_limit to rewrite the domain.
  have hdom : (ScatFun.minFun lam hlam).domain = (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n) (lt_trans (cofinalSeq_lt lam hlim hne n) hlam))).domain := by
    exact MinDom_limit lam hlim hne;
  refine ⟨ ?_, ?_ ⟩;
  · use fun x => ⟨ x, by
      exact hdom ▸ x.2 ⟩
    generalize_proofs at *;
    refine ⟨ ?_, ?_ ⟩;
    · fun_prop;
    · refine ⟨ fun x => x, ?_, ?_ ⟩ <;> norm_num;
      · exact continuousOn_id;
      · intro a ha; exact (by
        convert scatFun_pgl_func_eq_val _ _ _ |>.symm;
        · rfl;
        · aesop);
  · refine ⟨ ?_, ?_ ⟩;
    exact fun x => ⟨ x, hdom.symm ▸ x.2 ⟩;
    refine ⟨ ?_, ?_ ⟩;
    · fun_prop;
    · refine ⟨ fun x => x, ?_, ?_ ⟩ <;> norm_num;
      · exact continuousOn_id;
      · intro a ha; exact (by
        convert scatFun_pgl_func_eq_val _ _ _;
        exact fun i a => rfl)


lemma pgl_reduces_pgl (s t : ℕ → ScatFun)
    (h : ∀ (i j₀ : ℕ), ∃ j, j₀ ≤ j ∧ ScatFun.Reduces (s i) (t j)) :
    ScatFun.Reduces (ScatFun.pgl s) (ScatFun.pgl t) := by
  apply ScatFun.pgl_reduces_of_local;
  intro i V hVopen hxV
  obtain ⟨m, hm⟩ := nbhd_basis' (ScatFun.pgl t).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hVopen hxV
  obtain ⟨j, hjm, hj⟩ := h i m
  obtain ⟨σ', hσ', τ', hτ', h_eq⟩ := (ScatFun.reduces_iff (s i) (t j)).1 hj
  use fun z => ⟨prependZerosOne j (σ' z).val, prependZerosOne_mem_pointedGluingSet _ j _ (σ' z).prop⟩, fun w => τ' (stripZerosOne j w);
  refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact Continuous.subtype_mk ( continuous_prependZerosOne j |> Continuous.comp <| continuous_subtype_val.comp hσ' ) _;
  · intro z
    simp only [h_eq, ScatFun.pgl_domain, ScatFun.pgl_func_block];
    rw [ stripZerosOne_prependZerosOne ];
  · refine hτ'.comp ?_ ?_;
    · exact Continuous.continuousOn ( continuous_stripZerosOne j );
    · intro x hx; obtain ⟨ z, rfl ⟩ := hx; simp +decide [ ScatFun.pgl_func_block ] ;
      exact ⟨ z, z.2, by rw [ stripZerosOne_prependZerosOne ] ⟩;
  · intro z
    apply hm
    simp only [ScatFun.pgl_domain, nbhd', Finset.mem_range, mem_setOf_eq];
    exact fun k hk => prependZerosOne_head_eq_zero j _ k ( lt_of_lt_of_le hk hjm );
  · rw [ ScatFun.pgl_func_zeroStream ];
    rw [ mem_closure_iff ] ; norm_num;
    refine ⟨ { w : Baire | w j ≠ 1 }, ?_, ?_, ?_ ⟩ <;> norm_num [ Set.Nonempty ];
    · exact isOpen_ne.preimage ( continuous_apply j );
    · exact zero_ne_one;
    · intro x hx y hy H; have := congr_fun H j; simp +decide [ ScatFun.pgl_func_block, prependZerosOne_at_i ] at this; aesop;


lemma reduces_minFun_cofinal (lam : Ordinal.{0}) (hlam : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0)
    (F : ScatFun) (hF : CBRank F.func < lam) (j₀ : ℕ) :
    ∃ j, j₀ ≤ j ∧ ScatFun.Reduces F
      (ScatFun.minFun (cofinalSeq lam j)
        (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)) := by
  have h_exists : ∃ j, j₀ ≤ j ∧ F.Reduces (ScatFun.minFun (cofinalSeq lam j) (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)) := by
    have h_decomp := ordinal_limit_add_nat (CBRank F.func)
    obtain ⟨η, k, hηk, hη⟩ := h_decomp
    have hk : (η + 2 * k : Ordinal.{0}) < lam := by
      have h_b_lt_lam : ∀ (n : ℕ), η + n < lam := by
        intro n
        have hη_lt_lam : η < lam := by
          exact lt_of_le_of_lt le_self_add ( hηk ▸ hF )
        induction n with
        | zero => simpa using hη_lt_lam
        | succ n ih =>
            rw [Nat.cast_succ, ← add_assoc, Ordinal.add_one_eq_succ]
            exact hlim.succ_lt ih
      generalize_proofs at *;
      exact_mod_cast h_b_lt_lam ( 2 * k )
    generalize_proofs at *;
    -- Set `T := Order.succ ((Finset.range (j₀ + 1)).sup (fun i => cofinalSeq lam i) ⊔ (η + 2 * k))`.
    set T := Order.succ ((Finset.range (j₀ + 1)).sup (fun i => cofinalSeq lam i) ⊔ (η + 2 * k)) with hT_def
    generalize_proofs at *;
    -- Apply `cofinalSeq_eventually_ge` to get `j` with `T ≤ cofinalSeq lam j`.
    obtain ⟨j, hj⟩ : ∃ j, T ≤ cofinalSeq lam j := by
      apply cofinalSeq_eventually_ge lam hlam hlim hne T (by
      refine hlim.succ_lt ?_;
      induction' j₀ with j₀ ih <;> simp_all +decide [ Finset.range_add_one ];
      · exact cofinalSeq_lt lam hlim hne 0;
      · exact cofinalSeq_lt lam hlim hne _)
    generalize_proofs at *;
    refine ⟨ j, ?_, ?_ ⟩
    generalize_proofs at *;
    · contrapose! hj;
      exact lt_of_le_of_lt ( Finset.le_sup ( f := fun i => cofinalSeq lam i ) ( Finset.mem_range.mpr ( by linarith ) ) |> le_trans <| le_max_left _ _ ) ( Order.lt_succ _ );
    · have := general_structure_theorem F.domain (ScatFun.minFun (cofinalSeq lam j) (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)).domain F.func (ScatFun.minFun (cofinalSeq lam j) (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)).func F.hScat (ScatFun.minFun (cofinalSeq lam j) (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)).hScat F.hCont (ScatFun.minFun (cofinalSeq lam j) (lt_trans (cofinalSeq_lt lam hlim hne j) hlam)).hCont η (by
      exact lt_of_le_of_lt le_self_add ( hηk ▸ hF.trans_le hlam.le )) (by
      exact hη.symm)
      generalize_proofs at *;
      convert this.2 k ⟨ hηk, _ ⟩ using 1
      generalize_proofs at *;
      rw [ minFun_cbRank_eq ];
      exact Order.succ_le_succ ( le_trans ( le_max_right _ _ ) ( le_trans ( le_of_lt ( Order.lt_succ _ ) ) hj ) );
  exact h_exists


end ConseqMinFunAux

/-- **Result 2 (pgl below a limit) — `ConsequencesGeneralStructureThm`, item 1 (≤ half).**
For a *limit* ordinal `lam` and any sequence `(F n)` of scattered continuous functions in
`𝒞_{<lam}` (i.e. `CBRank (F n).func < lam`), the pointed gluing `pgl_n (F n)` reduces to the
minimum function `k_{lam+1}` (`minFun lam`).

This is the `≤` half of `ConsequencesGeneralStructureThm`, item 1.  Theorem 4.12
(`simpleFunctionsLambdaPlusOne`) consumes it to bound both `g` (Case A) and `g|_{C₁}`
(Case B) by `k_{lam+1}`, the rays involved all lying in `𝒞_{<lam}`.  (The `≡` refinement of
item 1, under regularity of `(CB(F n))` with supremum `lam`, follows by combining this with
`minFun_is_minimum`; it is not separately scaffolded as Theorem 4.12 only needs the `≤`
direction.  Item 2 — `pgl ℓ_lam ≤ f` when `CB f ≥ lam+2` — is likewise not used by 4.12.)

## Provided solution

Fix an increasing cofinal sequence `(α_n)` in `lam`.  Since `2·CB(F n) < lam`, there is an
increasing `(k_n)` with `2·CB(F n) ≤ α_{k_n}` for all `n`, so by the General Structure
Theorem (`general_structure_theorem`) `F n ≤ minFun (α_{k_n})`, and in turn
`pgl_n (F n) ≤ pgl_n minFun(α_{k_n}) ≤ minFun lam` by `Pgluingasupperbound`
(`pointedGluing_upper_bound`) together with the cofinal collapse
`pgl_n minFun(α_n) ≡ minFun lam` (`minFun_limit_equiv_pgl`). -/
theorem consequencesGeneralStructure_pgl_le_minFun
    (lam : Ordinal.{0}) (hlam_lt : lam < omega1)
    (hlim : Order.IsSuccLimit lam) (hne : lam ≠ 0)
    (F : ℕ → ScatFun) (hF : ∀ n, CBRank (F n).func < lam) :
    ScatFun.Reduces (ScatFun.pgl F) (ScatFun.minFun lam hlam_lt) := by
  have step1 : ScatFun.Reduces (ScatFun.pgl F)
      (ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n)
        (lt_trans (cofinalSeq_lt lam hlim hne n) hlam_lt))) := by
    apply ConseqMinFunAux.pgl_reduces_pgl
    intro i j₀
    exact ConseqMinFunAux.reduces_minFun_cofinal lam hlam_lt hlim hne (F i) (hF i) j₀
  exact ContinuouslyReduces.trans step1
    (ConseqMinFunAux.minFun_limit_equiv_pgl lam hlam_lt hlim hne).2

end
