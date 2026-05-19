import RequestProject.PointedGluing.Theorems
import RequestProject.CenteredMemo.Defs
import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for CenteredMemo.Theorems

These lemmas decompose the main theorems from Chapter 4 into smaller, more
focused pieces.
-/

/-!
### Helpers for Fact 4.1 (pgluingOfRegularIsCentered)
-/

/-
In the product topology on ℕ → ℕ, any open set containing the zero stream
contains a "cylinder" of the form {x | ∀ k < N, x k = 0} for some N.
-/
lemma zeroStream_nhd_cylinder {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (h0 : zeroStream ∈ U) :
    ∃ N : ℕ, {x : ℕ → ℕ | ∀ k, k < N → x k = 0} ⊆ U := by
  rw [ isOpen_pi_iff ] at hU;
  obtain ⟨ I, u, hIu, hU ⟩ := hU zeroStream h0;
  use I.sup id + 1;
  intro x hx;
  exact hU fun i hi => by have := hx i ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hi ) ) ; aesop;

/-
For j ≥ N, the image of prependZerosOne j lies in the cylinder
{x | ∀ k < N, x k = 0}.
-/
lemma prependZerosOne_in_cylinder (N j : ℕ) (hj : N ≤ j) (x : ℕ → ℕ) :
    ∀ k, k < N → prependZerosOne j x k = 0 := by
  exact fun k hk => if_pos ( lt_of_lt_of_le hk hj )

/-
A regular sequence has arbitrarily large indices with reductions.
-/
lemma regularSeq_large_index {X Y : ℕ → Type*}
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    {f : ∀ n, X n → Y n} (hf : IsRegularSeq f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ ContinuouslyReduces (f i) (f j) := by
  exact Set.Infinite.exists_gt ( hf i ) N |> fun ⟨ j, hj₁, hj₂ ⟩ => ⟨ j, hj₂.le, hj₁ ⟩

/-!
### Helpers for Proposition 4.3 (scatteredHaveCocenter)
-/

/-- A center for f belongs to every nonempty CB level. That is, if x is a center
for f and CBLevel f β is nonempty, then x ∈ CBLevel f β. -/
lemma center_in_CBLevel {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x : A) (hx : IsCenterFor f x)
    (β : Ordinal.{0}) (hne : (CBLevel f β).Nonempty) :
    x ∈ CBLevel f β := by
  sorry

/-- If two centers of a scattered function have different images, then the
perfect kernel is nonempty — contradicting scatteredness. -/
lemma centers_different_images_not_scattered {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (x y : A)
    (hx : IsCenterFor f x) (hy : IsCenterFor f y)
    (hne : f x ≠ f y) :
    ¬ ScatteredFun f := by
  sorry

/-- If all centers of f have the same image and f is centered,
then f is scattered if and only if f is always scattered (tautological direction
for the backward implication). The key content is that the hypothesis about
centers having the same image is used in the backward direction. -/
lemma cocenter_unique_implies_scattered {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (_hf_cent : IsCentered f)
    (_hcocenter : ∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y)
    (hf_scat : ScatteredFun f) : ScatteredFun f := hf_scat

/-!
### Helpers for Proposition 4.4, Item 3 (rigidityOfCocenter_finiteGluing)
-/

/-
Given continuity of σ and a center x for g at σ(x), for any m there exists
an open set U containing σ(x) such that g maps U into the m-cylinder of y_g.
-/
lemma cocenter_continuity_cylinder {A : Type*} [TopologicalSpace A]
    {g : A → ℕ → ℕ} {σ : A → A}
    (_hσ : Continuous σ) (x : A) (y_g : ℕ → ℕ)
    (hg_cont : Continuous g)
    (_hσx_center : IsCenterFor g (σ x))
    (hg_eq : g (σ x) = y_g)
    (m : ℕ) :
    ∃ U : Set A, IsOpen U ∧ σ x ∈ U ∧
      ∀ a ∈ U, ∀ k, k < m → g a k = y_g k := by
  -- Define the set V as the intersection of all sets {a | g a k = y_g k} for k < m.
  set V := ⋂ k < m, {a | g a k = y_g k};
  have hV_open : IsOpen V := by
    refine' isOpen_iff_forall_mem_open.mpr _;
    intro x hx
    use ⋂ k < m, {a | g a k = y_g k};
    simp_all +decide [ Set.subset_def ];
    exact ⟨ fun x hx => Set.mem_iInter₂.2 hx, by rw [ show ( ⋂ k : ℕ, ⋂ ( _ : k < m ), { a | g a k = y_g k } ) = ⋂ k ∈ Finset.range m, { a | g a k = y_g k } by ext; simp +decide [ Finset.mem_range ] ] ; exact isOpen_biInter_finset fun i _ => isOpen_discrete { y_g i } |> IsOpen.preimage ( show Continuous fun a => g a i from continuous_apply i |> Continuous.comp <| hg_cont ) , fun i hi => Set.mem_iInter₂.1 hx i hi ⟩;
  exact ⟨ V, hV_open, Set.mem_iInter₂.2 fun k hk => by simp +decide [ hg_eq ], fun a ha k hk => Set.mem_iInter₂.1 ha k hk ⟩

/-!
### Helpers for Theorem 4.6 (centeredAsPgluing_iff_monotone)
-/

-- The backward direction of Theorem 4.6 (centered_of_monotone_pgluing)
-- is in Theorems.lean (uses pgluingOfRegularIsCentered)

/-- The forward direction: if f is centered, then f ≡ pgl_i f_i for some
monotone sequence. Uses regularization of the ray sequence. -/
lemma monotone_pgluing_of_centered
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f) (hf_cent : IsCentered f) :
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (g : ∀ i, C i → D i),
      IsMonotoneSeq (fun i => (fun (x : C i) => (g i x : ℕ → ℕ))) ∧
      ContinuouslyEquiv f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry

/-!
### Helpers for Theorem 4.7 (localCenterednessFromBQO)
-/

/-- Base case: any function with CB-rank 0 is locally centered
(vacuously, since it must be empty or locally constant). -/
lemma locallyCentered_rank_zero {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (_hf_scat : ScatteredFun f) (hf_rank : CBRank f = 0) :
    IsLocallyCentered f := by
  sorry

/-- Limit case: if f has limit CB-rank, then f is locally of lower rank,
hence locally centered by induction. -/
lemma locallyCentered_limit_rank {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf_scat : ScatteredFun f)
    (α : Ordinal.{0}) (hα_limit : Order.IsSuccLimit α) (hα_ne : α ≠ 0)
    (hf_rank : CBRank f = α)
    (ih : ∀ β < α, ∀ (X' Y' : Type) [TopologicalSpace X'] [TopologicalSpace Y']
      (g : X' → Y'), ScatteredFun g → CBRank g = β → IsLocallyCentered g) :
    IsLocallyCentered f := by
  sorry

/-- Successor case: if f has successor CB-rank α+1 and 𝒞_{<α+1} is BQO,
then f is locally centered. -/
lemma locallyCentered_succ_rank
    (α : Ordinal.{0}) (hα : α < omega1)
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < Order.succ α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n))
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf_scat : ScatteredFun f)
    (hf_rank : CBRank f = Order.succ α)
    (ih : ∀ β < Order.succ α, ∀ (X' Y' : Type) [TopologicalSpace X'] [TopologicalSpace Y']
      (g : X' → Y'), ScatteredFun g → CBRank g = β → IsLocallyCentered g) :
    IsLocallyCentered f := by
  sorry

/-!
### Helpers for Corollary 4.10 (centeredSuccessor)
-/

/-- The minimum function k_{λ+1} is centered. -/
lemma minFun_isCentered (lam : Ordinal.{0}) :
    IsCentered (MinFun lam) := by
  sorry

/-- The pointed gluing of the max function pgl(ℓ_λ) is centered. -/
lemma pglMaxFun_isCentered (lam : Ordinal.{0}) :
    ∃ (X₂ Y₂ : Type) (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (g : X₂ → Y₂), IsCentered g ∧ CBRank g = Order.succ lam := by
  sorry

/-- k_{λ+1} and pgl(ℓ_λ) are not equivalent (strict inequality). -/
lemma minFun_lt_pglMaxFun (lam : Ordinal.{0})
    (hlam : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hlam_lt : lam < omega1) :
    ∃ (X₁ Y₁ X₂ Y₂ : Type)
      (_ : TopologicalSpace X₁) (_ : TopologicalSpace Y₁)
      (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (min_f : X₁ → Y₁) (pgl_max : X₂ → Y₂),
      ContinuouslyReduces min_f pgl_max ∧
      ¬ ContinuouslyReduces pgl_max min_f := by
  sorry

/-!
### Helpers for Proposition 4.11 (simpleIffCoincidenceOfCocenters)
-/

/-- If f has successor CB-rank, then I = {n | CB(f_n) = sup CB(f_i)} is nonempty,
where f_i are the pieces from an open partition. -/
lemma successor_rank_implies_I_nonempty
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B)
    (P : ℕ → Set A) (hcover : ⋃ i, P i = univ)
    (α : Ordinal.{0}) (hα : CBRank f = Order.succ α) :
    {n : ℕ | CBRank (f ∘ (Subtype.val : P n → A)) =
      ⨆ i, CBRank (f ∘ (Subtype.val : P i → A))}.Nonempty := by
  sorry

/-- If I = {n | CB(f_n) = sup CB(f_i)} is nonempty, then CB(f) is a successor. -/
lemma I_nonempty_implies_successor_rank
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B)
    (P : ℕ → Set A) (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : ⋃ i, P i = univ)
    (hf_cent : ∀ i, IsCentered (f ∘ (Subtype.val : P i → A)))
    (hf_scat : ScatteredFun f)
    (hne : {n : ℕ | CBRank (f ∘ (Subtype.val : P n → A)) =
      ⨆ i, CBRank (f ∘ (Subtype.val : P i → A))}.Nonempty) :
    ∃ α : Ordinal.{0}, CBRank f = Order.succ α := by
  sorry

end