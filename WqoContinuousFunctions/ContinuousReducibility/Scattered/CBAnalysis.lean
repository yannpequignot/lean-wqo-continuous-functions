import WqoContinuousFunctions.BaireSpace.GenRedProp
import WqoContinuousFunctions.ContinuousReducibility.Defs
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# CB Analysis — Scattered Functions and Cantor–Bendixson Theory

This file formalizes the Cantor–Bendixson derivative for functions, the CB-rank,
and the relationship between scattered functions and the perfect kernel.

## Main definitions

* `NowhereLocallyConstant` — a function is nowhere locally constant on a set
* `CBLevel` — the Cantor–Bendixson derivative levels CB_α(f)

## Main results

* `scattered_iff_empty_perfectKernel_general` — f is scattered ↔ f has empty perfect kernel
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

/-- The isolated locus is relatively open in `A`. -/
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
noncomputable def CBLevel {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Ordinal.{0} → Set X :=
  fun α => Ordinal.limitRecOn α
    (univ : Set X)
    (fun β ih => ih \ isolatedLocus f ih)
    (fun β _ ih => ⋂ γ ∈ Iio β, ih γ (by exact Set.mem_Iio.mp ‹_›))

/--
CBLevel is invariant under homeomorphisms.
-/
lemma CBLevel_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : Y → Z) (β : Ordinal.{0}) :
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


noncomputable def CBRank_scat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (_fs: ScatteredFun f) : Ordinal.{0} :=
  sSup {α : Ordinal.{0} | (CBLevel f α).Nonempty}

/- In general we define the CB rank as the least ordinal such that the CB derivative stabilizes-/
noncomputable def CBRank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | (CBLevel f α) = (CBLevel f (Order.succ α))}

/-!
## CB Level of open restrictions

For an open subset `S` of `X`, the CB levels of `f` restricted to `S` equal
the intersection of `S` with the CB levels of `f` on the ambient space.
-/

/--
For an open subset `S ⊆ X`, the isolated locus of `f|_S` on `S ∩ A` corresponds
to `S ∩ isolatedLocus f A`.
-/
lemma isolatedLocus_open_restrict {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set X) (hS : IsOpen S) (A : Set X)
    (_hSA : S ∩ CBLevel f 0 = S) -- trivially true, just for structure
    (x : S) (hxA : x.val ∈ A) :
    (x ∈ isolatedLocus (f ∘ Subtype.val : S → Y) (Subtype.val ⁻¹' A)) ↔
    (x.val ∈ isolatedLocus f A) := by
  constructor <;> intro h <;> rcases h with ⟨U, hU₁, hU₂, hU₃⟩ <;> simp_all +decide [isolatedLocus]
  · rcases hU₂ with ⟨U, hU₁, rfl⟩
    exact ⟨U ∩ S, hU₁.inter hS, ⟨hU₃.1, x.2⟩, fun y hy hyA => hU₃.2 y hy.2 hy.1 hyA⟩
  · exact ⟨Subtype.val ⁻¹' hU₁, hU₂.preimage continuous_subtype_val, hU₃.1, fun a ha ha' ha'' => hU₃.2 a ha' ha''⟩




/--
If `f` is scattered, then `f` restricted to any subset is also scattered.
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
noncomputable def perfectKernelCB {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Set X :=
  ⋂ (α : Ordinal.{0}), CBLevel f α

/-- Helper: `CBLevel f (succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α)`. -/
theorem CBLevel_succ' {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (α : Ordinal.{0}) :
    CBLevel f (Order.succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α) := by
  simp [CBLevel, Ordinal.limitRecOn_succ]

/--
CBLevel at a limit ordinal is the intersection of all lower levels.
-/
lemma CBLevel_limit {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam) :
    CBLevel f lam = ⋂ (γ : Ordinal.{0}) (_ : γ < lam), CBLevel f γ := by
  unfold CBLevel; aesop



/--
For an open subset `S ⊆ X`, `CBLevel (f ∘ Subtype.val : S → Y) β` equals
`Subtype.val ⁻¹' (CBLevel f β)` — i.e., a point `x : S` is in the CB level of the
restriction iff `x.val` is in the CB level of the full function.
-/
lemma CBLevel_open_restrict {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set X) (hS : IsOpen S) (β : Ordinal.{0})
    (x : S) :
    x ∈ CBLevel (f ∘ Subtype.val : S → Y) β ↔ x.val ∈ CBLevel f β := by
  have h_ind : ∀ β : Ordinal.{0}, Subtype.val ⁻¹' CBLevel f β = CBLevel (fun (z : S) => f z.val) β := by
    intro β
    induction' β using Ordinal.limitRecOn with β ih
    · simp +decide [CBLevel]
    · simp +decide [CBLevel_succ', ih]
      simp +decide [← ih, isolatedLocus]
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
    [Small.{0} X]
    (f : X → Y)
    (S : ℕ → Set X)
    (hS_open : ∀ n, IsOpen (S n))
    (hS_cover : ∀ x : X, ∃ n, x ∈ S n)
    (β : Ordinal.{0})
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
  suffices hA_sub : ∀ α : Ordinal.{0}, A ⊆ CBLevel f α by
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
The CB levels never stabilize implies there's an injection from `Ordinal.{0}` into `X`.
Used to derive a contradiction when `X` is small enough.
-/
lemma CBLevel_strictAnti_of_ne {X Y : Type*}
    [TopologicalSpace X]
    (f : X → Y)
    (h : ∀ α : Ordinal.{0}, CBLevel f α ≠ CBLevel f (Order.succ α)) :
    ∃ g : Ordinal.{0} → X, Injective g := by
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
    (f : X → Y) (hf : ScatteredFun f) (α : Ordinal.{0})
    (hne : (CBLevel f α).Nonempty) :
    CBLevel f (Order.succ α) ⊂ CBLevel f α := by
  have h_eq : isolatedLocus f (CBLevel f α) ≠ ∅ := by
    exact Set.Nonempty.ne_empty (scattered_isolatedLocus_nonempty f hf _ hne)
  simp_all +decide [Set.ssubset_def, Set.subset_def]
  simp_all +decide [CBLevel_succ', Set.ext_iff]
  exact ⟨h_eq.choose, h_eq.choose_spec.1, fun _ => h_eq.choose_spec⟩

/--
Forward direction of Proposition 2.7 when `X` is `Small.{0}` (in particular, `Type 0`).
The CB levels are indexed by `Ordinal.{0}`, so the stabilization argument uses
`not_injective_of_ordinal` which requires `Small.{0} X`.
-/
private lemma scattered_implies_empty_perfectKernel_small {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) : perfectKernelCB f = ∅ := by
  contrapose! hf with h
  intro h_scattered
  have h_contradiction : ∃ g : Ordinal.{0} → X, Function.Injective g := by
    apply CBLevel_strictAnti_of_ne
    intro α h_eq
    apply CBLevel_succ_ssubset_of_scattered f h_scattered α (by
    exact h.mono (Set.iInter_subset _ α)) |>.ne h_eq.symm
  exact not_injective_of_ordinal (h_contradiction.choose) h_contradiction.choose_spec

/-- **Proposition 2.7.** A function is scattered iff its perfect kernel is empty.

The forward direction requires showing the CB levels eventually stabilize (ordinal
arithmetic). The backward direction is fully proved above.

**Note on universes:** The proof of the forward direction uses `not_injective_of_ordinal`
which requires `Small.{0} X`. Since the CB levels are indexed by `Ordinal.{0}`, this
argument works when `X : Type 0` (or more generally when `Small.{0} X`). The theorem
is stated with `[Small.{0} X]` to reflect this constraint. -/
theorem scattered_iff_empty_perfectKernel_general {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) : ScatteredFun f ↔ perfectKernelCB f = ∅ := by
  exact ⟨scattered_implies_empty_perfectKernel_small f, scattered_of_empty_perfectKernel f⟩

theorem CBRank_eq_sInf_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    CBRank f = sInf {α : Ordinal.{0} | CBLevel f α = ∅} := by
  unfold CBRank
  suffices h : {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)} =
               {α : Ordinal.{0} | CBLevel f α = ∅} by
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
    (α : Ordinal.{0}):
    CBLevel (f ∘ (Subtype.val: U -> X)) α= (CBLevel f α) ∩ U := by
  induction' α using Ordinal.limitRecOn with α ih
  · simp +decide [CBLevel]
  · rw [CBLevel_succ', CBLevel_succ']
    simp +decide [Set.ext_iff, isolatedLocus] at ih ⊢
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

/-- The exit ordinal of x (min α s.t. x ∉ CBLevel f α) cannot be a limit ordinal. -/
lemma exit_ordinal_not_limit {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (x : X) (γ : Ordinal.{0})
    (hx_out : x ∉ CBLevel f γ)
    (hγ_limit : Order.IsSuccLimit γ) :
    ∃ δ : Ordinal.{0}, δ < γ ∧ x ∉ CBLevel f δ := by
  by_contra h
  push_neg at h
  apply hx_out
  simp [CBLevel, Ordinal.limitRecOn_limit _ _ _ _ hγ_limit]
  intro δ hδ
  exact h δ hδ

/--
The minimal exit ordinal of any point from the CB hierarchy is a successor.
-/
lemma exit_ordinal_is_successor {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (x : X) (γ : Ordinal.{0})
    (hx_out : x ∉ CBLevel f γ) :
    ∃ β : Ordinal.{0}, β < γ ∧ x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
  contrapose! hx_out
  induction' γ using Ordinal.limitRecOn with γ ih
  · exact CBLevel_zero f ▸ Set.mem_univ x
  · exact hx_out γ (Order.lt_succ γ) (ih fun β hβ => hx_out β (lt_trans hβ (Order.lt_succ γ)))
  · simp_all +decide [CBLevel]
    grind

/--
If x ∈ isolatedLocus f (CBLevel f β), then there exists open U with x ∈ U
    such that CBLevel f (succ β) ∩ U = ∅.
-/
lemma isolatedLocus_clears_succ_level {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (β : Ordinal.{0})
    (x : X)
    (hx : x ∈ isolatedLocus f (CBLevel f β)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ := by
  rcases hx with ⟨hx₁, ⟨U, hU₁, hx₂, hx₃⟩⟩
  refine ⟨U, hU₁, hx₂, Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_⟩
  simp_all +decide [CBLevel_succ']
  exact hy.1.2 ⟨hy.1.1, U, hU₁, hy.2, fun z hz => by aesop⟩

/--
If CBLevel f (succ β) ∩ U = ∅ for open U, then CBRank(f|_U) ≤ succ β,
    provided succ β < omega1.
-/
lemma cbrank_restriction_le_of_empty_level {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (U : Set X) (hU : IsOpen U)
    (β : Ordinal.{0})
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
    exact ⟨lam, hlam ▸ csInf_mem (show { α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α) }.Nonempty from by exact Set.nonempty_iff_ne_empty.2 fun h => by simp_all +decide [CBRank]), h_empty_level⟩
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
theorem ContinuouslyReduces.cb_monotone {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hσ : Continuous σ)
    (hred : ∀ x, f x = τ (g (σ x)))
    (α : Ordinal.{0}) :
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
lemma CBLevel_eq_empty_at_rank {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    CBLevel f (CBRank f) = ∅ := by
  -- Let r = CBRank f.
  set r := CBRank f with hr
  by_cases hS : {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty
  · -- Since S is nonempty, we have r = csInf S ∈ S.
    have hr_mem : r ∈ {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)} := by
      exact csInf_mem hS
    contrapose! hr_mem
    have := CBLevel_succ_ssubset_of_scattered f hf r hr_mem
    exact fun h => this.ne h.symm
  · have h_inj : ∃ g : Ordinal.{0} → X, Function.Injective g := by
      apply CBLevel_strictAnti_of_ne
      exact fun α => fun h => hS ⟨α, h⟩
    exact False.elim (not_injective_of_ordinal h_inj.choose h_inj.choose_spec)


/--
CBRank of a restriction to an open set is bounded by CBRank of the full function,
    when both are scattered.
-/
lemma CBRank_open_restrict_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Small.{0} X]
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

/--
If `f` is scattered with CB rank `r`, and `S` is open, then
    `CBLevel (f|_S) r = ∅`.
-/
lemma CBLevel_open_restrict_empty_at_rank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : IsOpen S) :
    CBLevel (f ∘ Subtype.val : S → Y) (CBRank f) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx; have := CBLevel_eq_empty_at_rank f hf; simp_all +decide [CBLevel_open_restrict]



theorem ContinuouslyReduces.rank_monotone {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    [Small.{0} X] [Small.{0} X']
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

/-- The CB-rank of a scattered function on a subspace of Baire space is
    a countable ordinal, i.e. strictly less than ω₁.

    Proof sketch: the complements of CB levels form a strictly increasing
    chain of open sets in A (a subspace of ℕ → ℕ, which is second countable).
    By regularity of ℵ₁ = Cardinal.aleph 1, no countable family can be
    cofinal in omega1, so the chain must stabilize before omega1.

    Key ingredients needed:
    - `CBLevel_isClosed` : CB levels are closed (by transfinite induction)
    - `Cardinal.isRegular_aleph_one` : aleph 1 is a regular cardinal
    - `TopologicalSpace.exists_countable_basis` : A has a countable basis
    TODO: complete this proof. -/
theorem CBRank_lt_omega1
    {A : Set (ℕ → ℕ)} {f : A → ℕ → ℕ}
    (hf : ScatteredFun f) :
    CBRank f < omega1 := by
  sorry

end ReductionAndCB


section ScatteredCharacterization

/-!
## Characterization of Scattered Functions

**Theorem (scatterediffemptykernel).** Suppose `X` is metrizable, `Y` is Hausdorff,
and `f : X → Y` is continuous. Then `f` is scattered if and only if it has empty
perfect kernel.
-/

/-- The *perfect kernel* of `f` is the largest closed subset of the domain on which `f`
is nowhere locally constant. It is defined as the intersection of all closed sets `S`
such that the locally constant locus of `f` restricted to `S` is empty (i.e., `f` is
nowhere locally constant on `S`). -/
def perfectKernel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Set X :=
  ⋂₀ {S : Set X | IsClosed S ∧ (locallyConstantLocus f)ᶜ ⊆ S}

/-- The perfect kernel equals the complement of the locally constant locus,
since the locally constant locus is open (hence its complement is the smallest
closed set containing itself). -/
lemma perfectKernel_eq_compl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : perfectKernel f = (locallyConstantLocus f)ᶜ := by
  unfold perfectKernel
  apply le_antisymm
  · exact Set.sInter_subset_of_mem ⟨(isOpen_locallyConstantLocus f).isClosed_compl, le_refl _⟩
  · exact Set.subset_sInter fun S hS => hS.2

/-- Backward direction: if every point is locally constant, then f is scattered. -/
lemma locallyConstantLocus_univ_imp_scattered {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : locallyConstantLocus f = Set.univ) : ScatteredFun f := by
  intro S hS
  obtain ⟨x, hx⟩ := hS
  have : x ∈ locallyConstantLocus f := h ▸ Set.mem_univ x
  obtain ⟨U, hU, hxU, hconst⟩ := this
  exact ⟨U, hU, ⟨x, hxU, hx⟩, fun y hy z hz => by rw [hconst y hy.1, hconst z hz.1]⟩

/-- Forward direction helper: if f is scattered, continuous, X metrizable, Y T₂,
then every point is locally constant.

Proof: Suppose y ∉ locallyConstantLocus f. Since X is metrizable (hence first countable),
choose z_n → y with f(z_n) ≠ f(y). Apply ScatteredFun to {y} ∪ {z_n}.
The open set U must eventually contain y (since z_n → y), giving f(z_n) = f(y)
for large n, contradiction. -/
lemma scattered_imp_locallyConstantLocus_univ {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hscat : ScatteredFun f) :
    locallyConstantLocus f = Set.univ := by
  sorry

/-- A continuous function from a metrizable domain to a Hausdorff codomain is scattered
if and only if its perfect kernel is empty. -/
theorem scatteredIffEmptyKernel {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) :
    ScatteredFun f ↔ perfectKernel f = ∅ := by
  rw [perfectKernel_eq_compl]
  constructor
  · intro h
    rw [scattered_imp_locallyConstantLocus_univ f hf h]
    simp
  · intro h
    have : locallyConstantLocus f = Set.univ := by
      rwa [Set.compl_empty_iff] at h
    exact locallyConstantLocus_univ_imp_scattered f this

end ScatteredCharacterization
