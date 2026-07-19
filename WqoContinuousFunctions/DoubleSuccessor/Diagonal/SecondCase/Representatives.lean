import WqoContinuousFunctions.DoubleSuccessor.Diagonal.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Diagonal theorem, second case — representatives (`6_double_successor_memo.tex:301-303`)

Finite representative sets for the second-case families: `𝒫'_M` (pieces with cocenter `y` and
rank `> λ+1`) is realised by a finite `M ⊆ 𝒞_{α+2}` (`diagonalTheorem_secondCase_representatives_M`),
and its refinement `D` (`diagonalTheorem_secondCase_representatives_D`). Same construction as the
first-case representatives, placing each piece in `𝒞_{α+2}` via
`centered_equiv_mem_Centered_le_doubleSucc`.
-/

/-- **Second-case representatives for `𝒫'_M`** (`6_double_successor_memo.tex:301-303`). The pieces
with cocenter `y` and rank `> λ+1` (the set `𝒫'_M`) admit a finite set of representatives
`M ⊆ 𝒞_{α+2}`. Same construction as `diagonalTheorem_firstCase_representatives`: `M` is the subset
of `𝒞_{α+2}` realised by such a piece, and `centered_equiv_mem_Centered_le_doubleSucc` places each
piece there (its rank lies strictly between `λ` and `α+2`). -/
theorem diagonalTheorem_secondCase_representatives_M
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire} :
    ∃ M : Finset ScatFun, M ⊆ ScatFun.Centered (α + 1 + 1) ∧
      (∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP = y →
        α.limitPart + 1 < CBRank (F.restrict P).func →
        ∃ g ∈ M, ScatFun.Equiv (F.restrict P) g) ∧
      (∀ g ∈ M, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = y ∧ α.limitPart + 1 < CBRank (F.restrict P).func ∧
          ScatFun.Equiv (F.restrict P) g) := by
  classical
  have hrank_le : ∀ P : Set ↑F.domain, CBRank (F.restrict P).func ≤ α + 1 + 1 := by
    intro P
    have h1 : (F.restrict P).Reduces (F.restrict Set.univ) :=
      restrict_reduces_of_subset F (Set.subset_univ P)
    have h2 : CBRank (F.restrict P).func ≤ CBRank (F.restrict Set.univ).func :=
      ContinuouslyReduces.rank_monotone (F.restrict P).hScat (F.restrict Set.univ).hScat h1
    have h3 : CBRank (F.restrict Set.univ).func = CBRank F.func := by
      rw [cbRank_restrict_eq]
      exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
    rw [h3, hFrank] at h2; exact h2
  refine ⟨(ScatFun.Centered (α + 1 + 1)).filter
      (fun g => ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = y ∧ α.limitPart + 1 < CBRank (F.restrict P).func ∧
          ScatFun.Equiv (F.restrict P) g),
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro P hP hPy hPrank
    obtain ⟨h, hhmem, hhequiv⟩ :=
      centered_equiv_mem_Centered_le_doubleSucc α hα hFG (F.restrict P)
        (lt_trans (lt_add_one α.limitPart) hPrank) (hrank_le P)
        (hA.centered P hP)
    exact ⟨h, Finset.mem_filter.mpr ⟨hhmem, P, hP, hPy, hPrank, hhequiv⟩, hhequiv⟩
  · intro g hg
    exact (Finset.mem_filter.mp hg).2

/-- **Second-case representatives for `𝒫_D`** (`6_double_successor_memo.tex:304`). The pieces with
cocenter `≠ y` (the set `𝒫_D`) admit a finite set of representatives `D ⊆ 𝒞_{α+2}`. Same
construction as `diagonalTheorem_firstCase_representatives` (dropping the rank-`α+2` witness, which
is not needed here); `hfine` (fineness) supplies the rank lower bound `> λ` for each piece. -/
theorem diagonalTheorem_secondCase_representatives_D
    (α : Ordinal.{0}) (hα : α < omega1)
    (hFG : ScatFun.FGBelow (α + 1 + 1))
    (F : ScatFun) (hFrank : CBRank F.func = α + 1 + 1)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part) {y : Baire}
    (hfine : ∀ P ∈ Part, α.limitPart < CBRank (F.restrict P).func) :
    ∃ D : Finset ScatFun, D ⊆ ScatFun.Centered (α + 1 + 1) ∧
      (∀ (P : Set ↑F.domain) (hP : P ∈ Part), hA.cocenterOf hP ≠ y →
        ∃ g ∈ D, ScatFun.Equiv (F.restrict P) g) ∧
      (∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g) := by
  classical
  have hrank_le : ∀ P : Set ↑F.domain, CBRank (F.restrict P).func ≤ α + 1 + 1 := by
    intro P
    have h1 : (F.restrict P).Reduces (F.restrict Set.univ) :=
      restrict_reduces_of_subset F (Set.subset_univ P)
    have h2 : CBRank (F.restrict P).func ≤ CBRank (F.restrict Set.univ).func :=
      ContinuouslyReduces.rank_monotone (F.restrict P).hScat (F.restrict Set.univ).hScat h1
    have h3 : CBRank (F.restrict Set.univ).func = CBRank F.func := by
      rw [cbRank_restrict_eq]
      exact CBRank_comp_homeomorph (Homeomorph.Set.univ (↑F.domain)) F.func
    rw [h3, hFrank] at h2; exact h2
  refine ⟨(ScatFun.Centered (α + 1 + 1)).filter
      (fun g => ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g),
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro P hP hPy
    obtain ⟨h, hhmem, hhequiv⟩ :=
      centered_equiv_mem_Centered_le_doubleSucc α hα hFG (F.restrict P)
        (hfine P hP) (hrank_le P) (hA.centered P hP)
    exact ⟨h, Finset.mem_filter.mpr ⟨hhmem, P, hP, hPy, hhequiv⟩, hhequiv⟩
  · intro g hg
    exact (Finset.mem_filter.mp hg).2


end
