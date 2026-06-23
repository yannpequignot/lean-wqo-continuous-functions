import Mathlib.Tactic
import Mathlib.Topology.Basic
-- import WqoContinuousFunctions.PointedGluing.GeneralStructureHelpers.Helpers
import WqoContinuousFunctions.ContinuousReducibility.Gluing
import WqoContinuousFunctions.ContinuousReducibility.Scattered
import ZeroDimensionalSpaces.Basics
import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers
import WqoContinuousFunctions.PointedGluing.MaxFun.LimitRankHelpers.Helpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

/-!
# Clopen Restriction for MaxFun Limit Rank

This file defines `gClopenDom`/`gClopenFun` for restricting a function to the preimage
of a clopen set, and proves the key `gluing_via_codomain_partition` lemma.

## Main definitions

* `gClopenDom` — domain restriction to preimage of a set
* `gClopenFun` — restricted function on `gClopenDom`

## Main results

* `gClopenFun_continuous` — continuity of the restricted function
* `gClopenFun_scattered` — scatteredness of the restricted function
* `gluing_via_codomain_partition` — reduces MaxFun(η) to g via codomain partition
-/

noncomputable section



private lemma extract_B_map
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ))
    {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (CoRestrict' B g C)) :
    ∃ (σ : A → B) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
      Continuous σ ∧
      ContinuousOn τ (Set.range (g ∘ σ)) ∧
      (∀ x, g (σ x) ∈ C) ∧
      (∀ x : A, x.val = τ (g (σ x))) := by
  obtain ⟨σ₀, hσ₀_cont, τ₀, hτ₀_cont, hτ₀_eq⟩ := hred
  refine ⟨fun x => ⟨(σ₀ x).val, (σ₀ x).prop.choose⟩, τ₀, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp hσ₀_cont) _
  · convert hτ₀_cont using 1
  · exact fun x => (σ₀ x).prop.choose_spec
  · exact hτ₀_eq

/-- Each piece of the gluing reduces to g, via transitivity with gClopenFun → g. -/
private lemma piece_reduces_to_g
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (C : Set (ℕ → ℕ)) {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (CoRestrict' B g C)) :
    ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) g := by
  exact hred.trans ⟨fun x => ⟨x.val, x.prop.choose⟩,
    Continuous.subtype_mk continuous_subtype_val _,
    id, continuousOn_id, fun x => rfl⟩

/-- Membership: unprepend x.val ∈ A (x.val 0) for x ∈ GluingSet A. -/
private lemma gluingSet_unprepend_mem (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    unprepend x.val ∈ A (x.val 0) := by
  obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short A x
  exact hi ▸ hmem

/--
The block-wise σ on a GluingSet is continuous.
-/
private lemma gluingSet_blockwise_sigma_cont
    {B : Set (ℕ → ℕ)} (A : ℕ → Set (ℕ → ℕ))
    (σ_n : ∀ n, A n → B) (hσ_cont : ∀ n, Continuous (σ_n n)) :
    Continuous (fun x : GluingSet A => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  have h_block : IsOpen {y : GluingSet A | y.val 0 = x.val 0} := by
    convert isClopen_preimage_zero (x.val 0) |> IsClopen.isOpen |> IsOpen.preimage (continuous_subtype_val) using 1
  have h_cont_on_block : ContinuousOn (fun x : GluingSet A => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) {y : GluingSet A | y.val 0 = x.val 0} := by
    have h_cont_unprepend : Continuous (fun x : GluingSet A => unprepend x.val) := by
      exact continuous_unprepend.comp continuous_subtype_val
    have h_cont_on_block : ContinuousOn (fun x : {y : GluingSet A | y.val 0 = x.val 0} => σ_n (x.val.val 0) ⟨unprepend x.val.val, gluingSet_unprepend_mem A x.val⟩) Set.univ := by
      -- On the block the running first coordinate `z.val.val 0` is constant `= x.val 0`, so the
      -- block-wise map agrees with the fixed-index composite `σ_n (x.val 0) ∘ (z ↦ unprepend z)`,
      -- which is continuous.  The previous proof let `grind` build a congruence across the two
      -- indices; that crashed (`mkCongrProof` assertion violation).  Instead we transport along the
      -- index equality `z.2 : z.val.val 0 = x.val 0` with a `subst` over genuine index variables,
      -- where proof irrelevance closes the remaining membership-proof mismatch.
      refine Continuous.continuousOn (Continuous.congr
        ((hσ_cont (x.val 0)).comp (Continuous.subtype_mk
          (h_cont_unprepend.comp continuous_subtype_val)
          (fun z => by
            have hmem := gluingSet_unprepend_mem A z.val
            rwa [(z.2 : z.val.val 0 = x.val 0)] at hmem))) ?_)
      intro z
      have congr_index : ∀ {i j : ℕ} (_ : i = j) {v : ℕ → ℕ}
          (hi : v ∈ A i) (hj : v ∈ A j), σ_n i ⟨v, hi⟩ = σ_n j ⟨v, hj⟩ := by
        intro i j h v hi hj; subst h; rfl
      exact congr_index (z.2 : z.val.val 0 = x.val 0).symm _ _
    rw [continuousOn_iff_continuous_restrict] at *
    convert h_cont_on_block.comp (show Continuous fun y : { y : GluingSet A // y.val 0 = x.val 0 } => ⟨⟨y.val, by aesop⟩, by aesop⟩ from ?_) using 1
    fun_prop
  exact h_cont_on_block.continuousAt (h_block.mem_nhds <| by aesop)

/-- If each block of a GluingSet reduces to g with images in disjoint clopens C(p n),
    then the entire GluingSet reduces to g. -/
private lemma gluingSet_blockwise_reduces
    {B : Set (ℕ → ℕ)} (g : B → ℕ → ℕ) (_hgc : Continuous g)
    (A : ℕ → Set (ℕ → ℕ))
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (σ_n : ∀ n, A n → B) (τ_n : ∀ _n, (ℕ → ℕ) → (ℕ → ℕ))
    (hσ_cont : ∀ n, Continuous (σ_n n))
    (hτ_cont : ∀ n, ContinuousOn (τ_n n) (Set.range (g ∘ σ_n n)))
    (hg_mem : ∀ n (x : A n), g (σ_n n x) ∈ C (p n))
    (heq : ∀ n (x : A n), x.val = τ_n n (g (σ_n n x))) :
    ContinuouslyReduces (Subtype.val : GluingSet A → ℕ → ℕ) g := by
  set σ : GluingSet A → B := fun x => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩
  set τ : (ℕ → ℕ) → (ℕ → ℕ) := fun y =>
    if h : ∃ n, y ∈ C (p n) then prepend h.choose (τ_n h.choose y) else 0
  -- Helper: unique block determination by disjointness
  have huniq : ∀ z, ∀ i j, z ∈ C (p i) → z ∈ C (p j) → i = j := by
    intro z i j hi hj
    by_contra h
    exact Set.disjoint_left.mp (hC_disj _ _ (hp.ne h)) hi hj
  refine ⟨σ, gluingSet_blockwise_sigma_cont A σ_n hσ_cont, τ, ?_, ?_⟩
  -- ContinuousOn τ on range(g ∘ σ)
  · -- Use continuousOn_piecewise_clopen
    have hcover : ∀ z ∈ Set.range (g ∘ σ), ∃ i, z ∈ C (p i) := by
      rintro z ⟨x, rfl⟩
      exact ⟨x.val 0, hg_mem (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩⟩
    apply continuousOn_piecewise_clopen (S_i := fun n => C (p n))
        (τ_i := fun n y => prepend n (τ_n n y))
    -- cover
    · exact hcover
    -- clopen
    · intro n; exact hC_clopen (p n)
    -- agree
    · intro z _ i hi j hj; rw [huniq z i j hi hj]
    -- cont on each piece
    · intro n
      have hsubset : Set.range (g ∘ σ) ∩ C (p n) ⊆ Set.range (g ∘ σ_n n) := by
        rintro z ⟨⟨x, rfl⟩, hz_C⟩
        have hblock : x.val 0 = n :=
          huniq _ (x.val 0) n (hg_mem (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) hz_C
        exact ⟨⟨unprepend x.val, hblock ▸ gluingSet_unprepend_mem A x⟩,
              by simp only [comp_def]; exact congrArg g (by subst hblock; rfl)⟩
      exact (continuous_prepend n).continuousOn.comp
        ((hτ_cont n).mono hsubset) (fun _ _ => Set.mem_univ _)
    -- cover (duplicate)
    · exact hcover
    -- τ def
    · intro z hz n hn
      simp only [τ]
      have hexists : ∃ m, z ∈ C (p m) := ⟨n, hn⟩
      rw [dif_pos hexists]
      have hchoose : hexists.choose = n := huniq z _ n hexists.choose_spec hn
      rw [hchoose]
  -- equation: τ(g(σ(x))) = x.val
  · intro x
    -- σ x = σ_n (x.val 0) ⟨unprepend x.val, ...⟩
    -- g(σ x) ∈ C(p(x.val 0))
    set n₀ := x.val 0
    set a₀ : A n₀ := ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩
    have hval : g (σ_n n₀ a₀) ∈ C (p n₀) := hg_mem n₀ a₀
    -- τ picks block n₀ since g(σ x) ∈ C(p n₀)
    have hτ_eq : τ (g (σ x)) = prepend n₀ (τ_n n₀ (g (σ_n n₀ a₀))) := by
      show τ (g (σ_n n₀ a₀)) = _
      simp only [τ]
      rw [dif_pos (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n))]
      have hch : (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n)).choose = n₀ :=
        huniq _ _ _ (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n)).choose_spec hval
      simp only [hch]
    rw [hτ_eq, ← heq n₀ a₀]
    exact (prepend_unprepend x.val).symm

/-
This lemma is key to show that all Scattered Continuous
functions with same limit CBRank η are equivalent to MaxFun η.
It states that if for η_n is cofinal in η,
we can find disjoint clopen sets C_n
in the codomain of a continuous function g such that
MaxDom(η_n) reduces to g corestricted to C_n, then MaxFun(η) reduces to g.
-/
lemma gluing_via_codomain_partition
    (η : Ordinal.{0}) (_hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g)
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (hred : ∀ n, ContinuouslyReduces
        (Subtype.val : MaxDom (enumBelow η n) → ℕ → ℕ)
        (CoRestrict' B g (C (p n)))) :
    ContinuouslyReduces (MaxFun η) g := by
  -- Step 1: Extract block reductions via extract_B_map
  have hred' := fun n => extract_B_map B g (C (p n)) (hred n)
  choose σ_n τ_n hσ_cont hτ_cont hg_mem heq using hred'
  -- Step 2: MaxDom η = GluingSet(fun n => MaxDom(enumBelow η n))
  have hMaxDom : MaxDom η = GluingSet (fun n => MaxDom (enumBelow η n)) :=
    MaxDom_limit η hlim (Order.IsSuccLimit.ne_bot hlim)
  -- Step 3: Apply gluingSet_blockwise_reduces
  show ContinuouslyReduces (Subtype.val : MaxDom η → ℕ → ℕ) g
  rw [hMaxDom]
  exact gluingSet_blockwise_reduces g hgc _ C hC_clopen hC_disj p hp σ_n τ_n hσ_cont hτ_cont hg_mem heq

end
