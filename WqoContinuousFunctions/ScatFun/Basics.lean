import WqoContinuousFunctions.ScatFun.Defs

/-!
# `ScatFun` basics: disjoint unions and CB-rank of restrictions

Low-level `ScatFun`-bundled infrastructure used throughout the finite-generation development:
the disjoint-union predicate `ScatFun.IsDisjointUnion` (a countable clopen partition of the
domain, the blocks of `f = ⊔ᵢ fᵢ`), its `topRankIndex`, and the two CB-rank identities
`cbRank_restrict_eq` / `cbRank_eq_iSup_restrict` relating the rank of `F` to the ranks of its
canonical block restrictions.
-/

/-- **`ScatFun.IsDisjointUnion`** — the `ScatFun`-bundled form of `IsDisjointUnion`
(`ContinuousReducibility/Gluing/Defs.lean`).  `F.IsDisjointUnion A` says `(A i)` is a
countable clopen partition of `F.domain`; the blocks of `f = ⊔ᵢ fᵢ` are the canonical
restrictions `F.restrict (A i)`.  Unlike `ScatFun.gl`, this leaves `F`'s codomain untouched
on every block. -/
def ScatFun.IsDisjointUnion (F : ScatFun) (A : ℕ → Set ↑F.domain) : Prop :=
  (∀ i, IsClopen (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ ⋃ i, A i = Set.univ

/-- The **top-rank index set** `I = {n | CB(fₙ) = supᵢ CB(fᵢ)}` of a disjoint union. -/
def ScatFun.topRankIndex (F : ScatFun) (A : ℕ → Set ↑F.domain) : Set ℕ :=
  {n | CBRank (F.restrict (A n)).func = ⨆ i, CBRank (F.restrict (A i)).func}

/-- CB-rank of a block `F.restrict A` equals that of the plain restriction
`fun x : A => F.func x.val`: they differ only by the re-realization homeomorphism
`restrictEquiv`, and `CBRank` is invariant under precomposition with a homeomorphism. -/
lemma cbRank_restrict_eq (F : ScatFun) (A : Set ↑F.domain) :
    CBRank (F.restrict A).func = CBRank (fun x : ↥A => F.func x.val) := by
  show CBRank ((fun x : ↥A => F.func x.val) ∘ (F.restrictEquiv A)) = _
  exact CBRank_comp_homeomorph (F.restrictEquiv A) (fun x : ↥A => F.func x.val)

/-- **`CBrankofclopenunion`, `ScatFun`/disjoint-union form.**  The CB-rank of a disjoint
union is the supremum of the block CB-ranks.  This specialises the general open-cover
corollary `cb_rank_of_clopen_union` to the partition blocks `F.restrict (A i)`; the
index-prepending of `ScatFun.gl` never affected CB-rank, so no gluing-specific lemma is
needed. -/
lemma cbRank_eq_iSup_restrict (F : ScatFun) (A : ℕ → Set ↑F.domain)
    (hdu : F.IsDisjointUnion A) :
    CBRank F.func = ⨆ i, CBRank (F.restrict (A i)).func := by
  have hcover : ∀ x : ↑F.domain, ∃ n, x ∈ A n := by
    intro x
    have hx : x ∈ ⋃ i, A i := by rw [hdu.2.2]; exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  have hopen : ∀ i, IsOpen (A i) := fun i => (hdu.1 i).isOpen
  rw [cb_rank_of_clopen_union F.func F.hScat A hcover hopen]
  exact iSup_congr (fun i => (cbRank_restrict_eq F (A i)).symm)
