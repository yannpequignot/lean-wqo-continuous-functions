import WqoContinuousFunctions.PointedGluing.MaxFun.Helpers

/-!
# `MinFun` helpers: the reduction map on a pointed-gluing block (Chapter 3)

A single plumbing lemma, `pgl_sigma_eq_on_block`: on the block
`{y | (∀ k < n, yₖ = 0) ∧ yₙ ≠ 0}` the branch-wise reduction map `σ` (defined by
`firstNonzero`/`stripZerosOne`) agrees with the known-continuous per-block map `σ_n n`. Used to
establish continuity of the reduction witnessing `MinFun` as a lower bound. Chapter 3
(`3_general_struct_memo.tex`).
-/

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

variable
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    {f : A → B}
    {C D : ℕ → Set (ℕ → ℕ)}
    {g : ∀ n, C n → D n}
    {x : A}
    {An : ℕ → Set A}

/-
On a specific block, σ agrees with a known-continuous function.
    For y in the block {y | (∀ k < n, y.val k = 0) ∧ y.val n ≠ 0},
    σ y = (σ_n n ⟨stripZerosOne n y.val, ...⟩).val.
-/
omit [TopologicalSpace A] [MetrizableSpace A] in
lemma pgl_sigma_eq_on_block
    (σ_n : ∀ n, C n → An n) (n : ℕ)
    (y : PointedGluingSet C)
    (hy : (∀ k, k < n → y.val k = 0) ∧ y.val n ≠ 0) :
    (fun z : PointedGluingSet C =>
      if h : z.val = zeroStream then x
      else (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val) y =
    (σ_n n ⟨stripZerosOne n y.val, strip_mem_of_block C y n hy⟩).val := by
  -- Since y is not zeroStream, the if condition is false, so we can simplify the expression.
  have h_if_false : ¬(y.val = zeroStream) := by
    exact fun h => hy.2 (h.symm ▸ rfl)
  -- Since firstNonzero y.val = n, we can substitute this into the expression.
  have h_firstNonzero : firstNonzero y.val = n := by
    exact firstNonzero_eq_of_block _ _ hy
  grind


end
