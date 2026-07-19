import ZeroDimensionalSpaces.GenRedProp
import WqoContinuousFunctions.ContinuousReducibility.Defs
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

universe u

/-!
# CB Analysis — Scattered Functions and Cantor–Bendixson Theory

This file formalizes the Cantor–Bendixson derivative for functions, the CB-rank,
and the relationship between scattered functions and the perfect kernel.

## Main definitions

* `NowhereLocallyConstant` — a function is nowhere locally constant on a set
* `CBLevel` — the Cantor–Bendixson derivative levels CB_α(f)

## Main results

* `scattered_iff_empty_perfectKernel` — f is scattered ↔ f has empty perfect kernel
* `ContinuouslyReduces.scattered` — if f ≤ g and g is scattered, then f is scattered
* `ContinuouslyReduces.cb_monotone` — if (σ,τ) reduces f to g, then σ(CB_α(f)) ⊆ CB_α(g)
-/

section NowhereLocallyConstant

/-- A function `f : X → Y` is *nowhere locally constant* if it is not constant on any
nonempty open subset of its domain. -/
def NowhereLocallyConstant {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ x ∈ U, ∃ x' ∈ U, f x ≠ f x'

/-- A function is not scattered iff it admits a nonempty restriction that is nowhere
locally constant. -/
theorem not_scattered_iff_exists_nlc {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : ¬ ScatteredFun f ↔
    ∃ A : Set X, A.Nonempty ∧ NowhereLocallyConstant (f ∘ (Subtype.val : A → X)) := by
  constructor
  · intro hns
    simp only [ScatteredFun, not_forall] at hns
    push_neg at hns
    obtain ⟨S, hS, hnoU⟩ := hns
    refine ⟨S, hS, ?_⟩
    intro U hU ⟨x, hx⟩
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    have hne : (V ∩ S).Nonempty := ⟨x.val, hx, x.prop⟩
    obtain ⟨a, ⟨haV, haS⟩, b, ⟨hbV, hbS⟩, hab⟩ := hnoU V hV hne
    exact ⟨⟨a, haS⟩, haV, ⟨b, hbS⟩, hbV, hab⟩
  · rintro ⟨A, hA, hnlc⟩ hscat
    obtain ⟨U, hU, hUA, hconst⟩ := hscat A hA
    have hU' : IsOpen (Subtype.val ⁻¹' U : Set A) := hU.preimage continuous_subtype_val
    have hne : (Subtype.val ⁻¹' U : Set A).Nonempty := by
      obtain ⟨x, hxU, hxA⟩ := hUA
      exact ⟨⟨x, hxA⟩, hxU⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hnlc _ hU' hne
    exact hab (hconst a.val ⟨ha, a.prop⟩ b.val ⟨hb, b.prop⟩)

end NowhereLocallyConstant

section CBDerivative

/-!
## Cantor–Bendixson Derivative for Functions

The CB-derivative levels are defined transfinitely:
- CB₀(f) = dom f (= univ)
- CB_{α+1}(f) = CB_α(f) \ I(f, CB_α(f))
- CB_λ(f) = ⋂_{α<λ} CB_α(f) for λ limit
-/

/-- The set of `f`-isolated points in a set `A`: points where `f|_A` is locally constant. -/
def isolatedLocus {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (A : Set X) : Set X :=
  {x ∈ A | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ A, f y = f x}

theorem isolatedLocus_isOpen_in {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) :
    ∃ U : Set X, IsOpen U ∧ isolatedLocus f A = U ∩ A := by
  refine ⟨{x | ∃ V, IsOpen V ∧ x ∈ V ∧ ∃ c, ∀ y ∈ V ∩ A, f y = c}, ?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, hVo, hxV, c, hc⟩
    exact ⟨V, fun y hy => ⟨V, hVo, hy, c, hc⟩, hVo, hxV⟩
  · ext x
    simp only [isolatedLocus, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hxA, V, hV, hxV, hconst⟩
      exact ⟨⟨V, hV, hxV, f x, fun y hy => hconst y hy⟩, hxA⟩
    · rintro ⟨⟨V, hV, hxV, c, hconst⟩, hxA⟩
      refine ⟨hxA, V, hV, hxV, fun y hy => ?_⟩
      rw [hconst y hy, hconst x ⟨hxV, hxA⟩]

/-- The Cantor–Bendixson derivative levels `CB_α(f)`, defined by transfinite recursion
using `Ordinal.limitRecOn`. -/
noncomputable def CBLevel {X : Type u} {Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Ordinal.{u} → Set X :=
  fun α => Ordinal.limitRecOn α
    (univ : Set X)
    (fun β ih => ih \ isolatedLocus f ih)
    (fun β _ ih => ⋂ γ ∈ Iio β, ih γ (by exact Set.mem_Iio.mp ‹_›))

/--
CBLevel is invariant under homeomorphisms.
-/
lemma CBLevel_homeomorph {X Y : Type u} {Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : Y → Z) (β : Ordinal.{u}) :
    CBLevel (f ∘ e) β = e ⁻¹' (CBLevel f β) := by
  induction' β using Ordinal.limitRecOn with β ih <;> simp_all +decide [CBLevel]
  · congr! 1
    ext; simp +decide [isolatedLocus]
    intro hx
    constructor <;> rintro ⟨U, hU, hx, hU'⟩
    · exact ⟨e '' U, e.isOpen_image.mpr hU, Set.mem_image_of_mem _ hx, by simpa [Set.image_preimage_eq_inter_range] using hU'⟩
    · exact ⟨e ⁻¹' U, hU.preimage e.continuous, hx, fun y hy hy' => hU' _ hy hy'⟩
  · simp +decide [Set.preimage_iInter]

/-- CB₀(f) = univ. -/
theorem CBLevel_zero {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : CBLevel f 0 = univ := by
  simp [CBLevel, Ordinal.limitRecOn]

/--
The CB levels are decreasing: if `α ≤ β` then `CB_β(f) ⊆ CB_α(f)`.
-/
theorem CBLevel_antitone {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Antitone (CBLevel f) := by
  intro α β hαβ x hx
  induction' β using Ordinal.limitRecOn with β ih generalizing α x
  · aesop
  · cases hαβ.eq_or_lt <;> simp_all +decide [CBLevel]
  · cases hαβ.eq_or_lt <;> simp_all +decide [CBLevel]

/-!
## CB-Rank
-/

/-- The CB-rank of a  SCATTERED function can be defined by the supremum of ordinals `α` such that `CB_α(f)` is
nonempty. Returns `0` for functions where only `CB_0(f) = univ` is nonempty (when the
domain is empty). -/

-- noncomputable def CBRank_scat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
--     (f : X → Y) (_fs: ScatteredFun f) : Ordinal :=
--   sSup {α : Ordinal | (CBLevel f α).Nonempty}

/- In general we define the CB rank as the least ordinal such that the CB derivative stabilizes-/
noncomputable def CBRank {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Ordinal.{u} :=
  sInf {α : Ordinal.{u} | (CBLevel f α) = (CBLevel f (Order.succ α))}

lemma CBRank_comp_homeomorph {X Y : Type u} {Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y → Z) :
    CBRank (f ∘ e) = CBRank f := by
  unfold CBRank
  congr 1
  ext β
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
      CBLevel_homeomorph e f β, CBLevel_homeomorph e f (Order.succ β),
      Set.preimage_eq_preimage e.surjective]

/-!
## CB Level of open restrictions

For an open subset `S` of `X`, the CB levels of `f` restricted to `S` equal
the intersection of `S` with the CB levels of `f` on the ambient space.
-/

lemma scattered_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) :
    ScatteredFun (f ∘ Subtype.val : S → Y) := by
  intro T hT
  obtain ⟨U, hU_open, hU_nonempty⟩ := hf (Subtype.val '' T) (by
  exact hT.image _)
  refine ⟨Subtype.val ⁻¹' U, ?_, ?_, ?_⟩ <;> simp_all +decide [Set.Nonempty]
  · exact hU_open.preimage continuous_subtype_val
  · exact fun x hx hx' hx'' y hy hy' hy'' => hU_nonempty.2 x hx' hx hx'' y hy' hy hy''

end CBDerivative

section ScatteredIffEmptyKernel

/-- The perfect kernel of `f` in terms of CB levels: the intersection of all levels. -/
noncomputable def perfectKernelCB {X : Type u} {Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Set X :=
  ⋂ (α : Ordinal.{u}), CBLevel f α

/-- Helper: `CBLevel f (succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α)`. -/
theorem CBLevel_succ' {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (α : Ordinal) :
    CBLevel f (Order.succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α) := by
  simp [CBLevel, Ordinal.limitRecOn_succ]

/--
CBLevel at a limit ordinal is the intersection of all lower levels.
-/
lemma CBLevel_limit {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (lam : Ordinal) (hlam : Order.IsSuccLimit lam) :
    CBLevel f lam = ⋂ (γ : Ordinal) (_ : γ < lam), CBLevel f γ := by
  unfold CBLevel; aesop

/--
For an open subset `S ⊆ X`, `CBLevel (f ∘ Subtype.val : S → Y) β` equals
`Subtype.val ⁻¹' (CBLevel f β)` — i.e., a point `x : S` is in the CB level of the
restriction iff `x.val` is in the CB level of the full function.
-/
lemma CBLevel_open_restrict {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set X) (hS : IsOpen S) (β : Ordinal)
    (x : S) :
    x ∈ CBLevel (f ∘ Subtype.val : S → Y) β ↔ x.val ∈ CBLevel f β := by
  have h_ind : ∀ β : Ordinal, Subtype.val ⁻¹' CBLevel f β = CBLevel (fun (z : S) => f z.val) β := by
    intro β
    induction' β using Ordinal.limitRecOn with β ih
    · simp +decide [CBLevel]
    · simp +decide [CBLevel_succ', ih]
      simp +decide only [← ih, isolatedLocus, mem_inter_iff, and_imp, preimage_setOf_eq, mem_preimage, Subtype.forall]
      congr! 3
      constructor <;> rintro ⟨h₁, U, hU₁, hU₂, hU₃⟩
      · exact ⟨h₁, Subtype.val ⁻¹' U, hU₁.preimage continuous_subtype_val, hU₂, fun a ha ha' ha'' => hU₃ a ha' ha''⟩
      · obtain ⟨V, hV₁, hV₂⟩ := hU₁
        refine ⟨h₁, V ∩ S, hV₁.inter hS, ?_, ?_⟩ <;> aesop
    · simp_all +decide [Set.ext_iff, CBLevel_limit]
  exact Set.ext_iff.mp (h_ind β) x |>.symm

/--
For a clopen disjoint union, the CB rank is at most the supremum.
-/
lemma CBLevel_open_union_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

    (f : X → Y)
    (S : ℕ → Set X)
    (hS_open : ∀ n, IsOpen (S n))
    (hS_cover : ∀ x : X, ∃ n, x ∈ S n)
    (β : Ordinal)
    (hS_empty : ∀ n, CBLevel (f ∘ Subtype.val : S n → Y) β = ∅) :
    CBLevel f β = ∅ := by
  ext x
  obtain ⟨n, hn⟩ := hS_cover x
  specialize hS_empty n
  simp_all +decide [CBLevel_open_restrict, Set.ext_iff]

/-- If the perfect kernel is empty, then `f` is scattered. This is the backward direction
of Proposition 2.7. -/
theorem scattered_of_empty_perfectKernel {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : perfectKernelCB f = ∅) : ScatteredFun f := by
  by_contra hns
  rw [not_scattered_iff_exists_nlc] at hns
  obtain ⟨A, hA, hnlc⟩ := hns
  suffices hA_sub : ∀ α : Ordinal, A ⊆ CBLevel f α by
    exact hA.not_subset_empty (h ▸ fun x hx => mem_iInter.mpr (fun α => hA_sub α hx))
  intro α
  induction' α using Ordinal.limitRecOn with α ih _ hβ ih
  · intro x _; rw [CBLevel_zero]; exact mem_univ x
  · intro x hxA
    simp only [CBLevel, Ordinal.limitRecOn_succ]
    exact ⟨ih hxA, fun ⟨_, U, hU, hxU, hconst⟩ => by
      obtain ⟨a, ha, b, hb, hab⟩ := hnlc _ (hU.preimage continuous_subtype_val) ⟨⟨x, hxA⟩, hxU⟩
      exact hab ((hconst a.val ⟨ha, ih a.prop⟩).trans (hconst b.val ⟨hb, ih b.prop⟩).symm)⟩
  · intro x hxA
    unfold CBLevel
    rw [Ordinal.limitRecOn_limit _ _ _ _ hβ]
    exact mem_iInter₂.mpr (fun γ hγ => by exact ih γ (mem_Iio.mp hγ) hxA)

/-- If some CB-level of `f` is empty, then `f` is scattered (its perfect kernel,
contained in that level, is empty). -/
theorem scatteredFun_of_CBLevel_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (β : Ordinal) (h : CBLevel f β = ∅) : ScatteredFun f := by
  apply scattered_of_empty_perfectKernel f
  exact Set.eq_empty_of_forall_notMem fun x hx => by
    have := Set.mem_iInter.mp hx β; rw [h] at this; exact this

/--
If `f` is scattered and `S` is nonempty, then the isolated locus of `f` on `S`
is nonempty.
-/
lemma scattered_isolatedLocus_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : S.Nonempty) :
    (isolatedLocus f S).Nonempty := by
  rcases hf S hS with ⟨U, hU, hU'⟩
  exact ⟨hU'.1.choose, hU'.1.choose_spec.2, U, hU, hU'.1.choose_spec.1, fun x hx => hU'.2 _ ⟨hx.1, hx.2⟩ _ hU'.1.choose_spec⟩

/--
The CB levels never stabilize implies there's an injection from `Ordinal` into `X`.
Used to derive a contradiction when `X` is small enough.
-/
lemma CBLevel_strictAnti_of_ne {X : Type u} {Y : Type*}
    [TopologicalSpace X]
    (f : X → Y)
    (h : ∀ α : Ordinal.{u}, CBLevel f α ≠ CBLevel f (Order.succ α)) :
    ∃ g : Ordinal.{u} → X, Injective g := by
  have h_inj : ∀ α : Ordinal, ∃ x ∈ CBLevel f α, x ∉ CBLevel f (Order.succ α) := by
    intro α
    by_contra h_contra
    push_neg at h_contra
    have h_eq : CBLevel f α = CBLevel f (Order.succ α) := by
      exact Set.Subset.antisymm h_contra (CBLevel_antitone f (Order.le_succ α))
    exact h α h_eq
  choose g hg using h_inj
  refine ⟨g, fun α β hαβ => le_antisymm ?_ ?_⟩ <;> contrapose! hαβ
  · have h_g_alpha_in_CBLevel_beta : g α ∈ CBLevel f (Order.succ β) := by
      exact CBLevel_antitone f (Order.succ_le_of_lt hαβ) (hg α |>.1)
    exact fun h => hg β |>.2 (h ▸ h_g_alpha_in_CBLevel_beta)
  · intro h_eq
    have h_subset : CBLevel f β ⊆ CBLevel f (Order.succ α) := by
      apply CBLevel_antitone
      exact Order.succ_le_iff.mpr hαβ
    exact hg α |>.2 (h_eq ▸ h_subset (hg β |>.1))

/--
If `f` is scattered and `CBLevel f α` is nonempty, then `CBLevel f (succ α)` is
strictly smaller.
-/
lemma CBLevel_succ_ssubset_of_scattered {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (α : Ordinal)
    (hne : (CBLevel f α).Nonempty) :
    CBLevel f (Order.succ α) ⊂ CBLevel f α := by
  have h_eq : isolatedLocus f (CBLevel f α) ≠ ∅ := by
    exact Set.Nonempty.ne_empty (scattered_isolatedLocus_nonempty f hf _ hne)
  simp_all +decide [Set.ssubset_def, Set.subset_def]
  simp_all +decide [CBLevel_succ', Set.ext_iff]
  exact ⟨h_eq.choose, h_eq.choose_spec.1, fun _ => h_eq.choose_spec⟩

/--
Forward direction of Proposition 2.7, for an arbitrary topological space.
The CB levels are indexed by `Ordinal.{u}` (the domain's own universe), so a non-stabilizing
strictly-decreasing chain would give an injection `Ordinal.{u} ↪ X`, contradicting
`not_injective_of_ordinal` — whose smallness premise `Small.{u} X` is `small_self`. No size
hypothesis on `X` is needed.
-/
private lemma scattered_implies_empty_perfectKernel {X : Type u} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) : perfectKernelCB f = ∅ := by
  contrapose! hf with h
  intro h_scattered
  have h_contradiction : ∃ g : Ordinal.{u} → X, Function.Injective g := by
    apply CBLevel_strictAnti_of_ne
    intro α h_eq
    apply CBLevel_succ_ssubset_of_scattered f h_scattered α (by
    exact h.mono (Set.iInter_subset _ α)) |>.ne h_eq.symm
  exact not_injective_of_ordinal (h_contradiction.choose) h_contradiction.choose_spec

/-- **Proposition 2.7.** A function is scattered iff its perfect kernel is empty.

The forward direction requires showing the CB levels eventually stabilize (ordinal
arithmetic). The backward direction is fully proved above.

**Note on universes:** because `CBLevel`/`CBRank` are indexed by `Ordinal.{u}` (the universe of
the domain `X : Type u`), the stabilization argument's appeal to `not_injective_of_ordinal` is
discharged by `small_self : Small.{u} X`. Hence this holds for *arbitrary* topological spaces with
no size hypothesis. This is Proposition 2.11 in the memoir. -/
theorem scattered_iff_empty_perfectKernel {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : ScatteredFun f ↔ perfectKernelCB f = ∅ := by
  exact ⟨scattered_implies_empty_perfectKernel f, scattered_of_empty_perfectKernel f⟩

theorem CBRank_eq_sInf_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) :
    CBRank f = sInf {α : Ordinal | CBLevel f α = ∅} := by
  unfold CBRank
  suffices h : {α : Ordinal | CBLevel f α = CBLevel f (Order.succ α)} =
               {α : Ordinal | CBLevel f α = ∅} by
    rw [h]
  ext α
  simp only [Set.mem_setOf_eq]
  constructor
  · intro heq
    by_contra hne
    -- hne : ¬ CBLevel f α = ∅
    -- CBLevel_succ_ssubset_of_scattered needs (CBLevel f α).Nonempty
    have hne' : (CBLevel f α).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    exact (CBLevel_succ_ssubset_of_scattered f hf α hne').ne' heq
  · intro hempty
    have hsucc : CBLevel f (Order.succ α) = ∅ :=
      Set.eq_empty_of_subset_empty (hempty ▸ CBLevel_antitone f (Order.le_succ α))
    rw [hempty, hsucc]

end ScatteredIffEmptyKernel

section ReductionAndCB

lemma local_cb_derivative {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    (U: Set X) (hU: IsOpen U)
    (α : Ordinal):
    CBLevel (f ∘ (Subtype.val: U -> X)) α= (CBLevel f α) ∩ U := by
  induction' α using Ordinal.limitRecOn with α ih
  · simp +decide [CBLevel]
  · rw [CBLevel_succ', CBLevel_succ']
    simp +decide only [Set.ext_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right, mem_inter_iff, isolatedLocus, comp_apply, and_imp, Subtype.forall, sdiff_sep_self, not_exists, not_and, not_forall, mem_setOf_eq] at ih ⊢
    intro x
    constructor
    · rintro ⟨hx, hx', hx''⟩
      refine ⟨⟨ih x |>.1 ⟨hx, hx'⟩ |>.1, ?_⟩, hx⟩
      intro V hV hxV
      specialize hx'' (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) (by simpa)
      grind
    · intro hx
      refine ⟨hx.2, ih x |>.2 ⟨hx.1.1, hx.2⟩ |>.2, ?_⟩
      intro V hV hxV
      rcases hV with ⟨W, hW, rfl⟩
      rcases hx.1.2 (W ∩ U) (hW.inter hU) ⟨hxV, hx.2⟩ with ⟨y, hyW, hyU, hy⟩
      exact ⟨y, hyW.2, hyW.1, ih y |>.2 ⟨hyU, hyW.2⟩ |>.2, hy⟩
  · rename_i o ho ih
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simp_all +decide [CBLevel, Set.ext_iff]
      exact ⟨fun i hi => (ih i hi x |> Iff.mp) (hx i |> fun ⟨hx₁, hx₂⟩ => ⟨hx₁, hx₂ hi⟩) |>.1, hx o |> fun ⟨hx₁, hx₂⟩ => hx₁⟩
    · intro x hx
      simp_all +decide [CBLevel, Set.ext_iff]
      exact fun i hi => ih i hi x |>.2 ⟨hx.1 i hi, hx.2⟩ |>.2

lemma exit_ordinal_is_successor {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (x : X) (γ : Ordinal)
    (hx_out : x ∉ CBLevel f γ) :
    ∃ β : Ordinal, β < γ ∧ x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
  contrapose! hx_out
  induction' γ using Ordinal.limitRecOn with γ ih
  · exact CBLevel_zero f ▸ Set.mem_univ x
  · exact hx_out γ (Order.lt_succ γ) (ih fun β hβ => hx_out β (lt_trans hβ (Order.lt_succ γ)))
  · simp_all +decide [CBLevel]
    grind

lemma cbrank_restriction_le_of_empty_level {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (U : Set X) (hU : IsOpen U)
    (β : Ordinal)
    (hempty : CBLevel f (Order.succ β) ∩ U = ∅) :
    CBRank (f ∘ (Subtype.val : U → X)) ≤ Order.succ β := by
  apply csInf_le'
  ext x
  constructor <;> intro hx <;> contrapose! hempty
  · exact ⟨x, by simpa using local_cb_derivative U hU (Order.succ β) |>.subset ⟨x, hx, rfl⟩⟩
  · contrapose! hempty; simp_all +decide [CBLevel_succ']

lemma limit_locally_lower {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    (hf : ScatteredFun f)
    (lam : Ordinal)
    (hlam : lam = CBRank f)
    (hlim : Order.IsSuccLimit lam) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBRank (f ∘ (Subtype.val : U → X)) < lam := by
  intro x
  by_cases h_empty_level : (CBLevel f lam).Nonempty
  · have h_contradiction : ∀ α, CBLevel f α = CBLevel f (Order.succ α) → CBLevel f α = ∅ := by
      intro α hα
      by_contra h_nonempty
      have h_contradiction : CBLevel f (Order.succ α) ⊂ CBLevel f α := by
        apply CBLevel_succ_ssubset_of_scattered f hf α (Set.nonempty_iff_ne_empty.mpr h_nonempty)
      simp_all +decide [Set.ssubset_def]
    contrapose! h_contradiction
    exact ⟨lam, hlam ▸ csInf_mem (show { α : Ordinal | CBLevel f α = CBLevel f (Order.succ α) }.Nonempty from by exact Set.nonempty_iff_ne_empty.2 fun h => by simp_all +decide [CBRank]), h_empty_level⟩
  · simp_all +decide [Set.not_nonempty_iff_eq_empty]
    have h_contradiction : ∃ β, β < CBRank f ∧ x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
      apply exit_ordinal_is_successor
      aesop
    obtain ⟨β, hβ_lt, hβ_mem, hβ_not_mem⟩ := h_contradiction
    have h_iso_loc : x ∈ isolatedLocus f (CBLevel f β) := by
      simp_all +decide [CBLevel_succ']
    have h_neighborhood : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ := by
      obtain ⟨U, hU_open, hxU, hU_const⟩ := h_iso_loc.2
      refine ⟨U, hU_open, hxU, ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy_succ hyU
      rw [CBLevel_succ'] at hy_succ
      exact hy_succ.2 ⟨hy_succ.1, U, hU_open, hyU,
        fun z hz => (hU_const z hz).trans (hU_const y ⟨hyU, hy_succ.1⟩).symm⟩
    obtain ⟨U, hU_open, hxU, hU_empty⟩ := h_neighborhood
    have h_cbrank_le : CBRank (f ∘ (Subtype.val : U → X)) ≤ Order.succ β := by
      apply cbrank_restriction_le_of_empty_level U hU_open β hU_empty
    exact ⟨U, hU_open, hxU, lt_of_le_of_lt h_cbrank_le (hlim.succ_lt hβ_lt)⟩

/-!
## Proposition 2.9 (CBbasicsfromJSL)

1. If `f ≤ g` and `g` is scattered, then `f` is scattered.
2. If `(σ,τ)` continuously reduces `f` to `g`, then `σ(CB_α(f)) ⊆ CB_α(g)`.
-/

lemma ContinuouslyReduces.scattered_local {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (σ : X → X') (τ : Y' → Y) -- express continuously reduces f to g
    (hσ : Continuous σ) -- in full to talk about the witnesses
    (_hτ : ContinuousOn τ (Set.range (g ∘ σ)))
    (heq : ∀ x, f x = τ (g (σ x)))
    (A : Set X)
    (x : X) (hx :  x ∈ A)
    (hsx : (σ x) ∈ (isolatedLocus g (σ '' A)))
    : (x ∈ isolatedLocus f A) := by
  -- 1. Unpack the hypothesis hsx.
  -- hsx is of the form `(σ x ∈ σ '' A) ∧ (∃ U, ...)`
    obtain ⟨_h_in_image, U, hU_isOpen, h_sx_in_U, h_g_const⟩ := hsx; -- U open st g is locally constant on σ '' A ∩ A

    -- 2. Define the preimage set.
    let V : Set X := σ ⁻¹' U

    -- 3. Prove V is open and contains x.
    have hV_isOpen : IsOpen V := hU_isOpen.preimage hσ
    have h_x_in_V : x ∈ V := h_sx_in_U

    -- 4. Prove f is constant on V ∩ A.
    have h_f_const : ∀ y ∈ V ∩ A, f y = f x := by
    -- Introduce an arbitrary y and the hypothesis that it's in V ∩ A
      intro y hy

      -- Extract y ∈ V and y ∈ A
      have h_sy_in_U : σ y ∈ U := hy.1
      have h_y_in_A : y ∈ A := hy.2

      -- To use h_g_const, we need to show σ y ∈ σ '' A
      have h_sy_in_image : σ y ∈ σ '' A := mem_image_of_mem σ h_y_in_A

      -- Now we can apply our knowledge about g
      have h_g_eq : g (σ y) = g (σ x) := h_g_const (σ y) ⟨h_sy_in_U, h_sy_in_image⟩

      -- Finally, use the reduction identity to prove f y = f x
      rw [heq y, heq x, h_g_eq]

    -- 5. Construct the final proof object
    exact ⟨hx, V, hV_isOpen, h_x_in_V, h_f_const⟩

/-- If `f ≤ g` and `g` is scattered, then `f` is scattered.
uses the lemma ContinuouslyReduces.scattered_local
-/
theorem ContinuouslyReduces.scattered {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (hred : f ≤ g) (hg : ScatteredFun g) :
    ScatteredFun f := by
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred
    --obtain ⟨U, hUo, hyU, hU⟩ := hg
    intro S hS -- let S be a nonempty subset of X
    let A : Set X' := σ '' S -- let A be the image of S by σ
    have hA_nonempty :A.Nonempty := hS.image σ -- A is non empty
    -- now we use that g is scattered
    -- Step 1: Specialize the hypothesis to your set A
    have hg_A : ∃ U, IsOpen U ∧ (U ∩ A).Nonempty ∧ ∀ x ∈ U ∩ A, ∀ x' ∈ U ∩ A, g x = g x' := hg A hA_nonempty
    -- Step 2: Unpack the specialized hypothesis
    obtain ⟨U, hU_open, hU_nonempty, hg_const⟩ := hg_A
    -- let x be a point in A with σ x = y
    obtain ⟨y, hy_in_U, hy_in_image⟩ := hU_nonempty
    -- Replace 'rfl' stands for implicit reflexivity of equality in y=σx, henceforth σx
    obtain ⟨x, hx_in_S, rfl⟩ := hy_in_image
    -- This destroys 'hy_in_image', replaces 'y' with 'σ x',
    -- and updates 'hy_in_U' to mean 'σ x ∈ U'
    -- Since hy_in_image was destroyed, we quickly recreate the proof
    -- that σ x is in A.
    have h_sx_in_A : σ x ∈ A := Set.mem_image_of_mem σ hx_in_S
    have h_g_const_ : ∀ y ∈ U ∩ A, g y = g (σ x) := by
     intro z hz
     exact hg_const z hz (σ x) ⟨hy_in_U, h_sx_in_A⟩
    have hy_in_isolatedLocus : (σ x ∈ (isolatedLocus g A)) := by exact ⟨h_sx_in_A, U, hU_open, hy_in_U, h_g_const_⟩
    have hx_in_isolatedLocus : (x ∈ isolatedLocus f S) := by
      exact ContinuouslyReduces.scattered_local σ τ hσ hτ heq S x hx_in_S hy_in_isolatedLocus
    obtain ⟨x_in_S, V, hVopen, hx_in_V, h_const_VS⟩ := hx_in_isolatedLocus
    have h_VS_nonempty : (V ∩ S).Nonempty := by exact ⟨x, hx_in_V, x_in_S⟩
    --  h_const_VS states that all points are mapped to the image of x under f
    -- what the definition of scattered requires is that any two points have the same image under f
    have hf_const_adapted : ∀ z ∈ V ∩ S, ∀ z' ∈ V ∩ S, f z = f z' := by
      intro z hz z' hz'
      -- Since f z = f x and f z' = f x, we can rewrite both to be f x
      rw [h_const_VS z hz, h_const_VS z' hz']
    exact ⟨V, hVopen, h_VS_nonempty, hf_const_adapted⟩

lemma CoRestrict_scattered (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hg : ScatteredFun g) (C : Set (ℕ → ℕ)) :
    ScatteredFun (CoRestrict' B g C) := by
  have : ContinuouslyReduces (CoRestrict' B g C) g :=
    ⟨fun x => ⟨x.val, x.prop.choose⟩,
     Continuous.subtype_mk continuous_subtype_val _,
     id, continuousOn_id, fun x => rfl⟩
  exact this.scattered hg

/--
If `(σ,τ)` reduces `f` to `g`, then for all `α`, `σ(CB_α(f)) ⊆ CB_α(g)`.
-/
theorem ContinuouslyReduces.cb_monotone {X X' : Type u} {Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hσ : Continuous σ)
    (hred : ∀ x, f x = τ (g (σ x)))
    (α : Ordinal.{u}) :
    σ '' (CBLevel f α) ⊆ CBLevel g α := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  induction' α using Ordinal.limitRecOn with α ih generalizing y <;> simp_all +decide [CBLevel]
  contrapose! hy
  obtain ⟨U, hUo, hyU, hU⟩ := hy.2
  refine fun hy' => ⟨?_, ?_⟩
  · exact hy'
  · refine ⟨σ ⁻¹' U, hUo.preimage hσ, hyU, fun z hz => ?_⟩ ; aesop

/--
For a scattered function, if CBRank f = r, then CBLevel f r = ∅.
-/
lemma CBLevel_eq_empty_at_rank {X : Type u} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) :
    CBLevel f (CBRank f) = ∅ := by
  -- Let r = CBRank f.
  set r := CBRank f with hr
  by_cases hS : {α : Ordinal | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty
  · -- Since S is nonempty, we have r = csInf S ∈ S.
    have hr_mem : r ∈ {α : Ordinal | CBLevel f α = CBLevel f (Order.succ α)} := by
      exact csInf_mem hS
    contrapose! hr_mem
    have := CBLevel_succ_ssubset_of_scattered f hf r hr_mem
    exact fun h => this.ne h.symm
  · have h_inj : ∃ g : Ordinal.{u} → X, Function.Injective g := by
      apply CBLevel_strictAnti_of_ne
      exact fun α => fun h => hS ⟨α, h⟩
    exact False.elim (not_injective_of_ordinal h_inj.choose h_inj.choose_spec)

/--
CBRank of a restriction to an open set is bounded by CBRank of the full function,
    when both are scattered.
-/
lemma CBRank_open_restrict_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : IsOpen S) :
    CBRank (f ∘ Subtype.val : S → Y) ≤ CBRank f := by
  refine csInf_le ?_ ?_
  · exact ⟨0, fun α hα => zero_le α⟩
  · ext x
    rw [CBLevel_open_restrict, CBLevel_open_restrict]
    · have := CBLevel_eq_empty_at_rank f hf
      simp_all +decide [CBLevel]
    · exact hS
    · exact hS

theorem ContinuouslyReduces.rank_monotone {X X' : Type u} {Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (hred : ContinuouslyReduces f g) :
    CBRank f ≤ CBRank g := by
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred
  rw [CBRank_eq_sInf_empty _ hf, CBRank_eq_sInf_empty _ hg]
  apply csInf_le_csInf ⟨0, fun α _ => zero_le α⟩
  exact ⟨CBRank g, CBLevel_eq_empty_at_rank g hg⟩
  intro α hα
  simp only [Set.mem_setOf_eq] at hα ⊢
  have hmono := ContinuouslyReduces.cb_monotone hσ heq α
  exact Set.image_eq_empty.mp (Set.subset_empty_iff.mp (hmono.trans hα.subset))

/-- All CB levels of any function are closed sets.

Proof: By transfinite induction.
- Base: CB₀(f) = univ is closed.
- Successor: CB_{α+1}(f) = CB_α(f) \ isolatedLocus f (CB_α(f)).
  By `isolatedLocus_isOpen_in`, the isolated locus equals V ∩ CB_α(f) for some open V,
  so CB_{α+1}(f) = CB_α(f) ∩ Vᶜ = (closed) ∩ (closed) = closed.
- Limit: CB_λ(f) = ⋂_{α<λ} CB_α(f) = intersection of closed sets = closed. -/
lemma CBLevel_isClosed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal) : IsClosed (CBLevel f α) := by
  induction' α using Ordinal.limitRecOn with α ih lam hlam ih
  · -- CB₀(f) = univ
    simp [CBLevel_zero]
  · -- CB_{succ α}(f) = CB_α(f) \ (V ∩ CB_α(f)) = CB_α(f) ∩ Vᶜ for some open V
    rw [CBLevel_succ']
    obtain ⟨V, hV_open, hiso⟩ := isolatedLocus_isOpen_in f (CBLevel f α)
    rw [hiso]
    have h_eq : CBLevel f α \ (V ∩ CBLevel f α) = CBLevel f α ∩ Vᶜ := by
      ext x; simp [Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff]
    rw [h_eq]
    exact ih.inter hV_open.isClosed_compl
  · -- CB_λ(f) = ⋂_{α<λ} CB_α(f)
    rw [CBLevel_limit f lam hlam]
    exact isClosed_iInter (fun α => isClosed_iInter (fun hα => ih α hα))

/-- The CB-rank of a scattered function on a subspace of Baire space (or in fact any secound countable space) is
    a countable ordinal, i.e. strictly less than ω₁.

    Proof by contradiction. Assume CBRank f ≥ ω₁.
    The sets U_α = (CBLevel f α)ᶜ are open (since CB levels are closed) and
    strictly increasing. For each α < ω₁, pick x_α ∈ CBLevel f α \ CBLevel f (succ α).
    Then x_α ∈ U_{succ α} (open), so by second countability of A we can pick a
    countable basis element V_α ⊆ U_{succ α} containing x_α.
    The map α ↦ V_α is injective: if α < β then x_β ∈ CBLevel f (succ α) = U_{succ α}ᶜ,
    so x_β ∉ V_α, hence V_α ≠ V_β.
    This injects Iio ω₁ into the countable set countableBasis X — contradiction. -/
theorem CBRank_lt_omega1
    {X : Type} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X]
    {f : X → Y}
    (hf : ScatteredFun f) :
    CBRank f < omega1 := by
  -- Proof by contradiction: assume CBRank f ≥ ω₁
  by_contra h_not_lt
  push_neg at h_not_lt -- h_not_lt : omega1 ≤ CBRank f
  -- Step 1: For each α < ω₁, the level strictly drops:
  --         CBLevel f α \ CBLevel f (succ α) is nonempty.
  -- Since α < ω₁ ≤ CBRank f, the level CBLevel f α is nonempty (from CBRank_eq_sInf_empty)
  -- and CBLevel f α ≠ CBLevel f (succ α) (from α < CBRank f = sInf {...}).
  -- Then CBLevel_succ_ssubset_of_scattered gives the strict inclusion.
  have level_drop_nonempty : ∀ α : Ordinal, α < omega1 →
      (CBLevel f α \ CBLevel f (Order.succ α)).Nonempty := by
    intro α hα
    have hα_lt_rank : α < CBRank f := lt_of_lt_of_le hα h_not_lt
    -- CBLevel f α is nonempty: if it were empty it would be in sInf's set, giving rank ≤ α
    have hα_nonempty : (CBLevel f α).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hle : CBRank f ≤ α := by
        rw [CBRank_eq_sInf_empty f hf]
        exact csInf_le ⟨0, fun β _ => zero_le β⟩ h
      exact absurd hle (not_le.mpr hα_lt_rank)
    -- The level strictly decreases at α (since f is scattered and CBLevel f α ≠ ∅)
    have hsub := CBLevel_succ_ssubset_of_scattered f hf α hα_nonempty
    -- hsub : CBLevel f (succ α) ⊊ CBLevel f α, so the difference is nonempty
    obtain ⟨x, hxα, hxnot⟩ := Set.not_subset.mp hsub.2
    exact ⟨x, hxα, hxnot⟩
  -- Step 2: Choose x_α ∈ CBLevel f α \ CBLevel f (succ α) for each α < ω₁
  choose x hx using level_drop_nonempty
  -- hx α hα : x α hα ∈ CBLevel f α ∧ x α hα ∉ CBLevel f (succ α)
  -- Step 3: Each x_α lies in the open set (CBLevel f (succ α))ᶜ
  -- Step 4: By second countability, pick a basis element V_α ⊆ (CBLevel f (succ α))ᶜ
  --         with x_α ∈ V_α, for each α < ω₁
  have pick_basis : ∀ α (hα : α < omega1), ∃ V ∈ TopologicalSpace.countableBasis X,
      x α hα ∈ V ∧ V ⊆ (CBLevel f (Order.succ α))ᶜ :=
    fun α hα => (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open
      (hx α hα).2  -- x α hα ∉ CBLevel f (succ α), i.e. x α hα ∈ (CBLevel f (succ α))ᶜ
      (CBLevel_isClosed f (Order.succ α)).isOpen_compl
  choose V hV_mem hV_x hV_sub using pick_basis
  -- Step 5: The map α ↦ V_α is injective on Iio ω₁.
  -- Key: if α < β, then x_β ∈ CBLevel f β ⊆ CBLevel f (succ α), so x_β ∉ V_α.
  -- But x_β ∈ V_β, so V_α ≠ V_β.
  have V_inj : ∀ α (hα : α < omega1) β (hβ : β < omega1),
      V α hα = V β hβ → α = β := by
    intro α hα β hβ h_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with hlt | hlt
    · -- α < β: x_β ∈ CBLevel f (succ α) but V_β = V_α ⊆ (CBLevel f (succ α))ᶜ
      have hxβ_in : x β hβ ∈ CBLevel f (Order.succ α) :=
        CBLevel_antitone f (Order.succ_le_of_lt hlt) (hx β hβ).1
      exact absurd hxβ_in (hV_sub α hα (h_eq ▸ hV_x β hβ))
    · -- β < α: symmetric
      have hxα_in : x α hα ∈ CBLevel f (Order.succ β) :=
        CBLevel_antitone f (Order.succ_le_of_lt hlt) (hx α hα).1
      exact absurd hxα_in (hV_sub β hβ (h_eq.symm ▸ hV_x α hα))
  -- Step 6: The injection α ↦ V_α maps Iio ω₁ into the countable set countableBasis X,
  --         so Iio ω₁ is countable.
  have hIio_count : (Set.Iio omega1).Countable := by
    apply Set.MapsTo.countable_of_injOn
        (f := fun α : Ordinal => if h : α < omega1 then V α h else ∅)
        (t := TopologicalSpace.countableBasis X)
    · -- MapsTo: beta-reduce the lambda, then split the if
      intro α hα
      dsimp only
      split_ifs with h
      · exact hV_mem α h
      · exact absurd hα h
    · -- InjOn: beta-reduce in h_eq, then split both ifs
      intro α hα β hβ h_eq
      dsimp only at h_eq
      split_ifs at h_eq with ha hb
      · exact V_inj α ha β hb h_eq
      · exact absurd hβ hb
      · exact absurd hα ha
      · exact absurd hα ha
    · exact TopologicalSpace.countable_countableBasis X
  -- Step 7: But Iio ω₁ is NOT countable (ω₁ is the first uncountable ordinal).
  have hIio_uncount : ¬ (Set.Iio omega1).Countable := by
    intro hcount
    -- hcount : (Iio omega1).Countable, so Cardinal.mk ↑(Iio omega1) < aleph 1
    have h1 : Cardinal.mk ↑(Set.Iio omega1) < Cardinal.aleph 1 :=
      (Cardinal.countable_iff_lt_aleph_one _).mp hcount
    rw [Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one] at h1
    -- h1 : omega1.card < aleph 1, but omega1 = (aleph 1).ord so this gives omega1 < omega1
    exact absurd (Cardinal.lt_ord.mpr h1) (lt_irrefl omega1)
  exact hIio_uncount hIio_count

theorem Scattered_countable_rank
    {X : Type} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    [MetrizableSpace Y]
    (f : X → Y)
    (hf : ScatteredFun f) :
    CBRank f < omega1 := by
  -- A separable metrizable space is second countable: endow `X` with a compatible pseudometric
  -- (whose uniformity is countably generated) and apply `secondCountable_of_separable`.
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  exact CBRank_lt_omega1 hf

/-- **Theorem (Countable range).** A scattered continuous function
has countable range.

#PROVIDED SOLUTION
By Scattered_countable_rank the CB rank of f is countable,
so the CB level at that rank is empty.
The domain of f is the union of the sets C α = CBLevel f α \ CBLevel f (α+1) for α < CBRank f.
On each C α the function f has countable range. So the range of f is a countable union of countable sets.
-/
-- Helper: for a scattered function on a second-countable space (any universe),
-- the initial segment Iio (CBRank f) is countable.
-- Proof: inject Iio (CBRank f) into the countable topological basis.
private lemma Iio_CBRank_countable {X' : Type*} {Y' : Type*}
    [TopologicalSpace X'] [TopologicalSpace Y']
    [SecondCountableTopology X']
    (g : X' → Y') (hg : ScatteredFun g) :
    (Set.Iio (CBRank g)).Countable := by
  -- For each α < CBRank g, the level strictly drops.
  have level_drop_nonempty : ∀ α : Ordinal, α < CBRank g →
      (CBLevel g α \ CBLevel g (Order.succ α)).Nonempty := by
    intro α hα
    have hα_nonempty : (CBLevel g α).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have : CBRank g ≤ α := by
        rw [CBRank_eq_sInf_empty g hg]
        exact csInf_le ⟨0, fun β _ => zero_le β⟩ h
      exact absurd this (not_le.mpr hα)
    obtain ⟨x, hxα, hxnot⟩ :=
      Set.not_subset.mp (CBLevel_succ_ssubset_of_scattered g hg α hα_nonempty).2
    exact ⟨x, hxα, hxnot⟩
  -- For each α < CBRank g, choose x_α in the level difference.
  choose x hx using level_drop_nonempty
  -- For each α, pick a basis open V_α containing x_α and disjoint from CBLevel g (succ α).
  have pick_basis : ∀ α (hα : α < CBRank g), ∃ V ∈ countableBasis X',
      x α hα ∈ V ∧ V ⊆ (CBLevel g (Order.succ α))ᶜ :=
    fun α hα => (isBasis_countableBasis X').exists_subset_of_mem_open
      (hx α hα).2 (CBLevel_isClosed g (Order.succ α)).isOpen_compl
  choose V hV_mem hV_x hV_sub using pick_basis
  -- α ↦ V α is injective on Iio (CBRank g).
  have V_inj : ∀ α (hα : α < CBRank g) β (hβ : β < CBRank g),
      V α hα = V β hβ → α = β := by
    intro α hα β hβ h_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with hlt | hlt
    · exact absurd (CBLevel_antitone g (Order.succ_le_of_lt hlt) (hx β hβ).1)
        (hV_sub α hα (h_eq ▸ hV_x β hβ))
    · exact absurd (CBLevel_antitone g (Order.succ_le_of_lt hlt) (hx α hα).1)
        (hV_sub β hβ (h_eq.symm ▸ hV_x α hα))
  -- The injection into the countable basis gives countability.
  apply Set.MapsTo.countable_of_injOn
      (f := fun α : Ordinal => if h : α < CBRank g then V α h else ∅)
      (t := countableBasis X')
  · intro α hα; dsimp only; split_ifs with h
    · exact hV_mem α h
    · exact absurd hα h
  · intro α hα β hβ h_eq; dsimp only at h_eq; split_ifs at h_eq with ha hb
    · exact V_inj α ha β hb h_eq
    · exact absurd hβ hb
    · exact absurd hα ha
    · exact absurd hα ha
  · exact countable_countableBasis X'

theorem Scattered_countable_range
    {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    [MetrizableSpace Y]
    (f : X → Y)
    (hf : ScatteredFun f) :
    (Set.range f).Countable := by
  -- Derive second countable topology on X from separable + metrizable.
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have hsc : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  -- CBLevel at rank is empty.
  have hrank_empty : CBLevel f (CBRank f) = ∅ := CBLevel_eq_empty_at_rank f hf
  -- Iio (CBRank f) is countable.
  have hIio_count : (Set.Iio (CBRank f)).Countable := Iio_CBRank_countable f hf
  -- range f ⊆ ⋃ β < CBRank f, f '' (CBLevel f β \ CBLevel f (succ β)).
  have h_sub : Set.range f ⊆
      ⋃ β ∈ Set.Iio (CBRank f), f '' (CBLevel f β \ CBLevel f (Order.succ β)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hx_out : x ∉ CBLevel f (CBRank f) := by simp [hrank_empty]
    obtain ⟨β, hβ_lt, hβ_in, hβ_out⟩ := exit_ordinal_is_successor x (CBRank f) hx_out
    exact Set.mem_biUnion hβ_lt ⟨x, ⟨hβ_in, hβ_out⟩, rfl⟩
  -- The union is countable.
  apply Set.Countable.mono h_sub
  apply hIio_count.biUnion
  intro β _
  -- T = CBLevel f β \ CBLevel f (succ β) is a separable subspace.
  set T : Set X := CBLevel f β \ CBLevel f (Order.succ β) with hT_def
  have : SecondCountableTopology T := Subtype.secondCountableTopology T
  have : SeparableSpace T := SecondCountableTopology.to_separableSpace
  -- The fibers of (f ∘ Subtype.val : T → Y) are pairwise disjoint open sets in T.
  -- Since T is separable, f '' T is countable.
  apply Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y => (fun x : T => f x.val) ⁻¹' ({y} : Set Y))
  · -- Pairwise disjoint fibers.
    intro y₁ _ y₂ _ hne
    simp only [Function.onFun]
    apply Set.disjoint_left.mpr
    intro x hx1 hx2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  · -- Each fiber is open in T.
    intro y _
    rw [isOpen_iff_mem_nhds]
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    -- x.val ∈ T so x.val ∈ isolatedLocus f (CBLevel f β).
    have hx_iso : x.val ∈ isolatedLocus f (CBLevel f β) := by
      have h1 : x.val ∈ CBLevel f β := x.property.1
      have h2 : x.val ∉ CBLevel f (Order.succ β) := x.property.2
      simp only [CBLevel_succ', Set.mem_diff, not_and, Classical.not_not] at h2
      exact h2 h1
    obtain ⟨_, U, hU, hxU, hconst⟩ := hx_iso
    rw [mem_nhds_iff]
    exact ⟨Subtype.val ⁻¹' U,
      fun ⟨z, hz⟩ hzU => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (hconst z ⟨hzU, hz.1⟩).trans hx,
      hU.preimage continuous_subtype_val, hxU⟩
  · -- Each fiber is nonempty for y ∈ f '' T.
    intro y hy
    obtain ⟨x, hxT, rfl⟩ := hy
    exact ⟨⟨x, hxT⟩, by simp⟩

end ReductionAndCB
