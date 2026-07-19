import WqoContinuousFunctions.ScatFun.Wedge.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

variable {n : ℕ}

/-! ## The Disjointification Lemma (memoir Lemma 5.6, `DisjointificationLemma`)

### Memoir statement (`5_precise_struct_memo.tex:209`)

Let `f : A → B` be continuous and `(fᵢ)_{i ≤ k+1}` in `𝓕(Baire)`.  Suppose there
are `y ∈ im f` and `(xᵢ)_{i ≤ k}` in `f⁻¹(y)` such that

1. for every `i ≤ k` and every open `U ∋ xᵢ` there is a reduction `(σ,τ)` of `fᵢ`
   to `f` with `im σ ⊆ U` and `y ∉ closure (im (f∘σ))`;
2. for every open `V ∋ y` there is a reduction `(σ,τ)` of `f_{k+1}` to `f` with
   `im (f∘σ) ⊆ V` and `y ∉ closure (im (f∘σ))`.

Then `⋁(f₀,…,f_k ∣ f_{k+1}) ≤ f`.

### `ScatFun` rendering

`f = G`, the verticals `f₀,…,f_k` are `v : Fin n → ScatFun` (`n = k+1`), and the
diagonal `f_{k+1}` is `d`.  Reductions are unfolded to the `ContinuouslyReduces`
witnesses `(σ, τ)` exactly as in `pgl_reduces_of_local`, with two additions over
that lemma:

* the per-vertical anchor `x i : ↥G.domain` with `G.func (x i) = y`, and
* the **separation** clause `y ∉ closure (range (fun z => G.func (σ z)))`, which
  is what makes the disjointification (and hence the well-definedness of the
  glued `τ`) possible.
-/

/--
**Separation / disjointification step** (memoir lines 236–237).

Given finitely many sets `S p` whose closures all avoid `y`, and an open `V ∋ y`,
there is a basic clopen neighbourhood `nbhd y N` contained in `V` and disjoint
from every `closure (S p)`.

In the main proof `S p` ranges over the finitely many images `range (f ∘ σ_p)`
produced at one stage of the induction (one per vertical `i ≤ k` plus the
diagonal), and the conclusion supplies the next shrunk neighbourhood `V_{n+1}`.

PROOF PLAN: `W := V ∩ ⋂ p, (closure (S p))ᶜ` is open (finite intersection of
opens) and contains `y` (each `closure (S p)` misses `y`).  Apply `nbhd_basis y W`
to get `N` with `nbhd y N ⊆ W`; both conclusions follow by intersecting.
-/
lemma wedge_lb_separation {ι : Type} [Fintype ι] (y : Baire)
    (V : Set Baire) (hV : IsOpen V) (hyV : y ∈ V)
    (S : ι → Set Baire) (hS : ∀ p, y ∉ closure (S p)) :
    ∃ N : ℕ, nbhd y N ⊆ V ∧ ∀ p, Disjoint (nbhd y N) (closure (S p)) := by
  -- By the basis property of nbhd y, there exists an N such that nbhd y N is contained in W.
  obtain ⟨N, hN⟩ : ∃ N, nbhd y N ⊆ V ∩ ⋂ p, (closure (S p))ᶜ := by
    apply nbhd_basis y _ (IsOpen.inter hV ( isOpen_iInter_of_finite fun p => isOpen_compl_iff.mpr (isClosed_closure) ) ) (by
    aesop);
  exact ⟨ N, fun x hx => hN hx |>.1, fun p => Set.disjoint_left.mpr fun x hx₁ hx₂ => hN hx₁ |>.2 |> Set.mem_iInter.mp |> fun h => h p hx₂ ⟩

/--
**Domain decomposition of the wedge.**  Every point `z` of the wedge domain is
exactly one of three shapes:
* a vertical base point `(k)⌢0^ω` for some `k < n`;
* a vertical block `(k)⌢(0)^l(1)⌢z'` for some `k < n`, level `l`, and `z' ∈ (v k).domain`;
* a diagonal point `(n+i)⌢t` for some `i` and `t ∈ d.domain`.
-/
lemma wedge_domain_cases (v : Fin n → ScatFun) (d : ScatFun)
    (z : ↥(wedge v d).domain) :
    (∃ (k : Fin n), z.val = prepend k.val zeroStream) ∨
    (∃ (k : Fin n) (l : ℕ) (z' : ↥(v k).domain),
        z.val = prepend k.val (prependZerosOne l z'.val)) ∨
    (∃ (i : ℕ) (t : ↥d.domain), z.val = prepend (n + i) t.val) := by
  obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( wedgeDomFamily v d k |> ScatFun.domain ) ) z;
  by_cases hk' : k < n;
  · have h_domain : (wedgeDomFamily v d k).domain = {zeroStream} ∪ ⋃ l, prependZerosOne l '' (v ⟨k, hk'⟩).domain := by
      exact congr_arg ScatFun.domain ( ScatFun.wedgeDomFamily_vertical v d ⟨ k, hk' ⟩ );
    simp_all +decide [ Set.ext_iff ];
    rcases hk.2 with ( h | ⟨ i, x, hx, hx' ⟩ );
    · exact Or.inl ⟨ ⟨ k, hk' ⟩, by simpa [ h ] using prepend_unprepend z.val ▸ by aesop ⟩;
    · refine Or.inr <| Or.inl ⟨ ⟨ k, hk' ⟩, i, x, hx, ?_ ⟩;
      convert prepend_unprepend z.val using 1;
      · exact Eq.symm (prepend_unprepend z.val)
      · convert prepend_unprepend z.val using 1;
        grind;
  · -- Set i := k - n so k = n + i (omega). Then `wedgeDomFamily v d k = d` by `wedgeDomFamily_diag`, so `unprepend z.val ∈ d.domain`, giving the third disjunct with t := ⟨unprepend z.val, _⟩ and z.val = prepend (n+i) t.val.
    obtain ⟨i, hi⟩ : ∃ i, k = n + i := by
      exact Nat.exists_eq_add_of_le <| le_of_not_gt hk'
    have h_unprepend : unprepend z.val ∈ d.domain := by
      unfold wedgeDomFamily at hk; aesop;
    use Or.inr (Or.inr ⟨i, ⟨unprepend z.val, h_unprepend⟩, by
      rw [ ← hi, ← hk.1, prepend_unprepend ]⟩)

/-- The `unprepend` of a wedge-domain point lands in the corresponding slot's domain. -/
lemma wedge_unprepend_mem (v : Fin n → ScatFun) (d : ScatFun)
    (z : ↥(wedge v d).domain) :
    unprepend z.val ∈ (wedgeDomFamily v d (z.val 0)).domain :=
  slab_unprepend_mem (wedgeDomFamily v d) (z.val 0) ⟨z, rfl⟩

/-- On a diagonal slot (`¬ z₀ < n`), `unprepend z` lands in `d.domain`. -/
lemma wedge_unprepend_mem_diag (v : Fin n → ScatFun) (d : ScatFun)
    (z : ↥(wedge v d).domain) (hk : ¬ z.val 0 < n) :
    unprepend z.val ∈ d.domain := by
  have h := wedge_unprepend_mem v d z
  rwa [wedgeDomFamily_diag v d (z.val 0) hk] at h

/-- On a vertical slot (`z₀ = k < n`), `unprepend z` lands in the pointed-gluing
set of the constant column `v k`. -/
lemma wedge_unprepend_mem_vert (v : Fin n → ScatFun) (d : ScatFun)
    (z : ↥(wedge v d).domain) (k : Fin n) (hk : z.val 0 = k.val) :
    unprepend z.val ∈ PointedGluingSet (fun _ : ℕ => (v k).domain) := by
  have h := wedge_unprepend_mem v d z
  rw [hk, wedgeDomFamily_vertical v d k] at h
  exact h

/-- On a vertical block (`z₀ = k < n`, `unprepend z ≠ 0^ω`), the stripped payload
lands in `(v k).domain`. -/
lemma wedge_strip_mem_vert (v : Fin n → ScatFun) (d : ScatFun)
    (z : ↥(wedge v d).domain) (k : Fin n) (hk : z.val 0 = k.val)
    (hne : unprepend z.val ≠ zeroStream) :
    stripZerosOne (firstNonzero (unprepend z.val)) (unprepend z.val) ∈ (v k).domain :=
  strip_mem_of_pointedGluingSet (fun _ : ℕ => (v k).domain)
    ⟨unprepend z.val, wedge_unprepend_mem_vert v d z k hk⟩ hne

/-! ## The reduction map `σ` and its continuity -/

/-- The reduction map `σ : (wedge v d).domain → G.domain` assembled from per-column
maps.  On a vertical slot (`z₀ = k < n`) it sends the base point `(k)⌢0^ω` to the
anchor `x k` and a block `(k)⌢(0)^l(1)⌢z'` to `σV k l z'`; on a diagonal slot
(`z₀ = n+i`) it sends `(n+i)⌢t` to `σD i t`. -/
noncomputable def wedgeSigma (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (z : ↥(wedge v d).domain) : ↥G.domain :=
  if hk : z.val 0 < n then
    if hz : unprepend z.val = zeroStream then x ⟨z.val 0, hk⟩
    else σV ⟨z.val 0, hk⟩ (firstNonzero (unprepend z.val))
      ⟨stripZerosOne (firstNonzero (unprepend z.val)) (unprepend z.val),
       wedge_strip_mem_vert v d z ⟨z.val 0, hk⟩ rfl hz⟩
  else
    σD (z.val 0 - n) ⟨unprepend z.val, wedge_unprepend_mem_diag v d z hk⟩

/-- The off-base part of the wedge domain: the complement of the `n` vertical base
points `(k)⌢0^ω`. -/
def wedgeOffBase (v : Fin n → ScatFun) (d : ScatFun) : Set ↥(wedge v d).domain :=
  {z | ¬ (z.val 0 < n ∧ unprepend z.val = zeroStream)}

/-- The columns partition the off-base domain: a vertical ray piece `(k, l)` (first
coordinate `k < n`, ray level `l`) or a diagonal piece `i` (first coordinate `n+i`). -/
def wedgePiece (v : Fin n → ScatFun) (d : ScatFun) :
    (Fin n × ℕ) ⊕ ℕ → Set ↥(wedge v d).domain :=
  fun p => match p with
    | Sum.inl (k, l) =>
        {z | z.val 0 = k.val ∧ firstNonzero (unprepend z.val) = l ∧
          unprepend z.val ≠ zeroStream}
    | Sum.inr i => {z | z.val 0 = n + i}

/--
The wedge pieces cover exactly the off-base domain.
-/
lemma wedgePiece_iUnion (v : Fin n → ScatFun) (d : ScatFun) :
    (⋃ p, wedgePiece v d p) = wedgeOffBase v d := by
  ext z
  simp only [wedge_domain, gl_domain, wedgePiece, ne_eq, mem_iUnion, Sum.exists, mem_setOf_eq, Prod.exists, exists_and_left, ↓existsAndEq, true_and, exists_and_right, wedgeOffBase, not_and];
  constructor <;> intro h;
  · grind;
  · by_cases h' : z.val 0 < n <;> simp_all +decide;
    · exact Or.inl ⟨ ⟨ z.val 0, h' ⟩, rfl ⟩;
    · exact Or.inr ⟨ z.val 0 - n, by rw [ Nat.add_sub_cancel' h' ] ⟩

/--
The wedge pieces form a relative clopen partition.
-/
lemma wedgePiece_relClopen (v : Fin n → ScatFun) (d : ScatFun) :
    IsRelativeClopenPartition (wedgePiece v d) := by
  refine ⟨ ?_, ?_ ⟩;
  · grind +locals;
  · intro p
    apply IsOpen.preimage (continuous_subtype_val) (by
    cases p <;> simp +decide [ *, wedgePiece ];
    · rename_i k;
      have h_clopen : IsClopen {z : ↥(wedge v d).domain | z.val 0 = k.1.val ∧ (∀ j < k.2, unprepend z.val j = 0) ∧ unprepend z.val k.2 ≠ 0} := by
        have h_clopen : IsClopen {z : ↥(wedge v d).domain | z.val 0 = k.1.val} ∧ IsClopen {z : ↥(wedge v d).domain | unprepend z.val k.2 ≠ 0} ∧ ∀ j < k.2, IsClopen {z : ↥(wedge v d).domain | unprepend z.val j = 0} := by
          refine ⟨ ?_, ?_, ?_ ⟩;
          · constructor;
            · exact isClosed_eq ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) continuous_const;
            · have h_cont : Continuous (fun z : ↥(wedge v d).domain => z.val 0) := by
                exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val;
              exact h_cont.isOpen_preimage { ( k.1 : ℕ ) } ( by simp +decide );
          · refine ⟨ ?_, ?_ ⟩;
            · exact isClosed_compl_iff.mpr ( isOpen_discrete { 0 } |> IsOpen.preimage ( show Continuous fun z : ↥ ( wedge v d ).domain => unprepend z.val k.2 from by
                                                                                          exact continuous_apply k.2 |> Continuous.comp <| continuous_unprepend.comp <| continuous_subtype_val ) );
            · exact isOpen_ne.preimage ( continuous_apply _ |> Continuous.comp <| continuous_unprepend.comp <| continuous_subtype_val );
          · intro j hj;
            have h_clopen : IsClopen {z : ℕ → ℕ | z j = 0} := by
              exact baire_fiber_isClopen j 0;
            convert h_clopen.preimage ( show Continuous fun z : ↥ ( ScatFun.wedge v d ).domain => unprepend z.val from ?_ ) using 1;
            exact continuous_unprepend.comp continuous_subtype_val;
        convert h_clopen.1.inter ( h_clopen.2.1.inter ( isClopen_biInter_finset fun j hj => h_clopen.2.2 j ( Finset.mem_range.mp hj ) ) ) using 1 ; aesop;
      convert h_clopen.isOpen using 1;
      ext; simp [firstNonzero];
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
      · exact fun _ => ⟨ fun h => ⟨ h.1.2, h.1.1 ⟩, fun h => ⟨ ⟨ h.2, h.1 ⟩, fun h' => h.2 <| h'.symm ▸ rfl ⟩ ⟩;
      · exact fun _ _ => funext ‹_›;
    · -- The function $z \mapsto z.val 0$ is continuous, and the set $\{n + val✝\}$ is open in the discrete topology.
      have h_cont : Continuous (fun z : ↥(wedge v d).domain => z.val 0) := by
        exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val;
      exact h_cont.isOpen_preimage { n + ‹_› } ( by simp +decide ))

/--
On each column piece, `σ` is continuous (per-piece reduction map composed with
continuous coordinate maps).
-/
lemma wedgeSigma_cont_piece (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (hσVc : ∀ k l, Continuous (σV k l))
    (hσDc : ∀ i, Continuous (σD i))
    (p : (Fin n × ℕ) ⊕ ℕ) :
    Continuous (fun z : ↥(wedgePiece v d p) => wedgeSigma G v d x σV σD z.val) := by
  cases p <;> simp +decide [ ScatFun.wedgeSigma ];
  · rename_i p
    obtain ⟨k, l⟩ := p
    generalize_proofs at *;
    refine' Continuous.congr _ _;
    use fun z => σV k l ⟨stripZerosOne l (unprepend z.val.val), by
      convert wedge_strip_mem_vert v d z.val k _ _ using 1 <;> norm_num [ z.2.1 ];
      · exact z.2.2.1.symm ▸ rfl;
      · exact z.2.2.2⟩
    all_goals generalize_proofs at *;
    · exact hσVc k l |> Continuous.comp <| Continuous.subtype_mk ( continuous_stripZerosOne l |> Continuous.comp <| continuous_unprepend.comp <| continuous_subtype_val.comp continuous_subtype_val ) _;
    · intro z; simp +decide [ wedgePiece ] at z ⊢;
      grind;
  · convert Continuous.congr ( hσDc _ |> Continuous.comp <| ( continuous_unprepend.comp ( continuous_subtype_val.comp continuous_subtype_val ) |> Continuous.subtype_mk <| _ ) ) _ using 1;
    exact ‹ℕ›;
    all_goals simp +decide [ wedgePiece ];
    exact fun a ha ha' => by simpa [ ha' ] using wedge_unprepend_mem_diag v d ⟨ a, ha ⟩ ( by simp [ ha' ] ) ;
    grind

/-- `σ` is continuous on the off-base domain. -/
lemma wedgeSigma_continuousOn_offBase (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (hσVc : ∀ k l, Continuous (σV k l))
    (hσDc : ∀ i, Continuous (σD i)) :
    ContinuousOn (wedgeSigma G v d x σV σD) (wedgeOffBase v d) := by
  rw [← wedgePiece_iUnion v d, continuousOn_iff_continuous_restrict]
  apply continuous_of_relativeClopenPartition_seq (wedgePiece_relClopen v d)
  intro p
  have heq : (Set.restrict (⋃ p, wedgePiece v d p) (wedgeSigma G v d x σV σD)) ∘
        Set.inclusion (Set.subset_iUnion (wedgePiece v d) p) =
      fun z : ↥(wedgePiece v d p) => wedgeSigma G v d x σV σD z.val := by
    ext z; simp [Set.restrict]
  rw [heq]
  exact wedgeSigma_cont_piece G v d x σV σD hσVc hσDc p

/--
`σ` is continuous on the base points (where it is locally constant).
-/
lemma wedgeSigma_continuousOn_base (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain) :
    ContinuousOn (wedgeSigma G v d x σV σD)
      {z : ↥(wedge v d).domain | z.val 0 < n ∧ unprepend z.val = zeroStream} := by
  intro z hz
  have h_slab : ∀ᶠ w in nhdsWithin z {z : ↥(wedge v d).domain | z.val 0 < n ∧ unprepend z.val = zeroStream}, w.val 0 = z.val 0 := by
    have h_slab : IsOpen {w : ℕ → ℕ | w 0 = z.val 0} := by
      rw [ isOpen_pi_iff ];
      exact fun f hf => ⟨ { 0 }, fun _ => { f 0 }, by aesop ⟩;
    exact Filter.mem_of_superset ( mem_nhdsWithin_of_mem_nhds ( h_slab.preimage continuous_subtype_val |> IsOpen.mem_nhds <| by aesop ) ) fun w hw => hw
  generalize_proofs at *; (
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds;
  filter_upwards [ h_slab, self_mem_nhdsWithin ] with w hw₁ hw₂;
  unfold ScatFun.wedgeSigma; aesop;)

/--
Sequential boundary condition: a sequence of off-base points converging to a
vertical base point `(k)⌢0^ω` has `σ`-images converging to the anchor `x k`.
-/
lemma wedgeSigma_seq (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (hVconv : ∀ k : Fin n, SetsConvergeTo (fun l => Set.range (σV k l)) (x k))
    (zs : ℕ → ↥(wedge v d).domain) (a : ↥(wedge v d).domain)
    (hzU : ∀ m, zs m ∈ wedgeOffBase v d)
    (haUc : a ∈ (wedgeOffBase v d)ᶜ)
    (htend : Filter.Tendsto zs Filter.atTop (nhds a)) :
    Filter.Tendsto (wedgeSigma G v d x σV σD ∘ zs) Filter.atTop
      (nhds (wedgeSigma G v d x σV σD a)) := by
  simp_all +decide [ Set.mem_compl_iff, wedgeOffBase ];
  -- First get the index `k` with `a.val 0 = k.val` and `wedgeSigma G v d x σV σD a = x k`.
  set k : Fin n := ⟨a.val 0, haUc.1⟩
  have hwa : wedgeSigma G v d x σV σD a = x k := by
    unfold ScatFun.wedgeSigma; aesop;
  -- We now need to show WedgeSigma zs → x k.
  suffices hlim : Filter.Tendsto (wedgeSigma G v d x σV σD ∘ zs) Filter.atTop (nhds (x k)) by rw [hwa]; exact hlim;
  -- Step 1: `zs m ∈ wedgeOffBase` with `m ≥ N₁` ensures `zs m` is in slab `k`.
  have hslab : ∃ N₁, ∀ m ≥ N₁, (zs m).val 0 = k.val := by
    have hslab : Filter.Tendsto (fun m => (zs m).val 0) Filter.atTop (nhds (a.val 0)) := by
      exact Filter.Tendsto.comp ( continuous_apply 0 |> Continuous.continuousAt ) ( continuous_subtype_val.continuousAt.tendsto.comp htend );
    aesop;
  -- Step 2: `zs m ∈ wedgeOffBase` with `m ≥ N₂` ensures `firstNonzero (unprepend (zs m).val) ≥ M`.
  have hfnz_tendsto : ∀ M, ∃ N₂, ∀ m ≥ N₂, M ≤ firstNonzero (unprepend (zs m).val) := by
    intro M
    obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ m ≥ N₂, ∀ i < M, (unprepend (zs m).val) i = 0 := by
      have hfnz_tendsto : Filter.Tendsto (fun m => unprepend (zs m).val) Filter.atTop (nhds (unprepend a.val)) := by
        exact continuous_unprepend.continuousAt.tendsto.comp ( continuous_subtype_val.continuousAt.tendsto.comp htend );
      simp_all +decide [ tendsto_pi_nhds ];
      choose! N hN using hfnz_tendsto; exact ⟨ Finset.sup ( Finset.range M ) N, fun m hm i hi => hN i m ( le_trans ( Finset.le_sup ( f := N ) ( Finset.mem_range.mpr hi ) ) hm ) ⟩ ;
    use N₂ + hslab.choose; intro m hm; specialize hN₂ m ( by linarith ) ; specialize hslab ; have := hslab.choose_spec m ( by linarith ) ; simp_all +decide [ firstNonzero ] ;
    grind +splitIndPred;
  refine tendsto_nhds.mpr ?_;
  intro s hs hxk
  obtain ⟨M, hM⟩ : ∃ M, ∀ l ≥ M, Set.range (σV k l) ⊆ s := by
    exact hVconv k s hs hxk;
  obtain ⟨ N₁, hN₁ ⟩ := hslab; obtain ⟨ N₂, hN₂ ⟩ := hfnz_tendsto M; filter_upwards [ Filter.Ici_mem_atTop N₁, Filter.Ici_mem_atTop N₂ ] with m hm₁ hm₂; simp_all +decide [ Set.range_subset_iff ] ;
  grind +locals

/-- **Continuity of the wedge reduction map `σ`.**  Off the `n` vertical base points
the map is continuous piecewise on the clopen first-coordinate slabs; at each base
point `(k)⌢0^ω` continuity follows from the convergence of the vertical column's
images to the anchor `x k`. -/
lemma wedgeSigma_continuous (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (x : Fin n → ↥G.domain)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (hσVc : ∀ k l, Continuous (σV k l))
    (hσDc : ∀ i, Continuous (σD i))
    (hVconv : ∀ k : Fin n, SetsConvergeTo (fun l => Set.range (σV k l)) (x k)) :
    Continuous (wedgeSigma G v d x σV σD) := by
  have h1 : IsClopen ({z : Baire | z 0 < n}) :=
    (isClopen_discrete {m : ℕ | m < n}).preimage (continuous_apply 0)
  have h2 : IsClosed ({z : Baire | unprepend z = zeroStream}) :=
    isClosed_eq continuous_unprepend continuous_const
  have hcl : IsClosed ({z : Baire | z 0 < n} ∩ {z : Baire | unprepend z = zeroStream}) :=
    h1.isClosed.inter h2
  refine sufficient_cond_continuity (wedgeSigma G v d x σV σD) (wedgeOffBase v d)
    ?_ (wedgeSigma_continuousOn_offBase G v d x σV σD hσVc hσDc) ?_ ?_
  · -- the off-base set is open
    have hopen : IsOpen ((Subtype.val : ↥(wedge v d).domain → Baire) ⁻¹'
        ({z : Baire | z 0 < n} ∩ {z : Baire | unprepend z = zeroStream})ᶜ) :=
      hcl.isOpen_compl.preimage continuous_subtype_val
    convert hopen using 2
  · -- continuity on the base points
    have hset : (wedgeOffBase v d)ᶜ =
        {z : ↥(wedge v d).domain | z.val 0 < n ∧ unprepend z.val = zeroStream} := by
      ext z; simp [wedgeOffBase]
    rw [hset]; exact wedgeSigma_continuousOn_base G v d x σV σD
  · intro zs a hzU haUc htend
    exact wedgeSigma_seq G v d x σV σD hVconv zs a hzU haUc htend

/-! ## The inverse map `τ` and the reduction -/

/-- Output ray level of a wedge column (vertical `(k,l)` ↦ `l`, diagonal `i` ↦ `i`). -/
def wedgeOutLvl : (Fin n × ℕ) ⊕ ℕ → ℕ
  | Sum.inl (_, l) => l
  | Sum.inr i => i

/-- Output column tag of a wedge column (vertical `(k,l)` ↦ `k`, diagonal `i` ↦ `n`). -/
def wedgeOutCol : (Fin n × ℕ) ⊕ ℕ → ℕ
  | Sum.inl (k, _) => k.val
  | Sum.inr _ => n

/-- The `G`-image of each column piece. -/
def wedgeImg (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain) : (Fin n × ℕ) ⊕ ℕ → Set Baire
  | Sum.inl (k, l) => Set.range (fun z => G.func (σV k l z))
  | Sum.inr i => Set.range (fun t => G.func (σD i t))

/-- The per-column inverse map. -/
def wedgeTpiece (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire) : (Fin n × ℕ) ⊕ ℕ → (Baire → Baire)
  | Sum.inl (k, l) => τV k l
  | Sum.inr i => τD i

/-- The assembled inverse map `τ : Baire → Baire`.  On a `G`-value `w` lying in the
image of column `p`, it outputs `(0)^{outLvl p}(1)(outCol p)⌢(τ_piece p w)`; off all
column images it is `0^ω`. -/
noncomputable def wedgeTau (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (w : Baire) : Baire :=
  if h : w ∈ ⋃ p, wedgeImg G v d σV σD p then
    let p := (Set.mem_iUnion.mp h).choose
    prependZerosOne (wedgeOutLvl p) (prepend (wedgeOutCol p) (wedgeTpiece τV τD p w))
  else zeroStream

/--
On a column image, `τ` is given by the explicit per-column formula.
-/
lemma wedgeTau_eq_on_img (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (hpart : IsRelativeClopenPartition (wedgeImg G v d σV σD))
    (p : (Fin n × ℕ) ⊕ ℕ) (w : Baire) (hw : w ∈ wedgeImg G v d σV σD p) :
    wedgeTau G v d σV σD τV τD w
      = prependZerosOne (wedgeOutLvl p)
          (prepend (wedgeOutCol p) (wedgeTpiece τV τD p w)) := by
  obtain ⟨q, hq⟩ : ∃ q, w ∈ G.wedgeImg v d σV σD q := by
    use p;
  obtain ⟨q', hq'⟩ : ∃ q', w ∈ G.wedgeImg v d σV σD q' ∧ ∀ q'', w ∈ G.wedgeImg v d σV σD q'' → q'' = q' := by
    exact ⟨ q, hq, fun q'' hq'' => Classical.not_not.1 fun h => Set.disjoint_left.mp ( hpart.1 q'' q h ) hq'' hq ⟩;
  unfold ScatFun.wedgeTau; simp +decide ;
  grind

/--
`τ` is continuous on the union of the column images.
-/
lemma wedgeTau_continuousOn_UI (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (hτVc : ∀ k l, ContinuousOn (τV k l) (Set.range (fun z => G.func (σV k l z))))
    (hτDc : ∀ i, ContinuousOn (τD i) (Set.range (fun t => G.func (σD i t))))
    (hpart : IsRelativeClopenPartition (wedgeImg G v d σV σD)) :
    ContinuousOn (wedgeTau G v d σV σD τV τD) (⋃ p, wedgeImg G v d σV σD p) := by
  have h_cont : ∀ p, ContinuousOn (fun z : ↥(ScatFun.wedgeImg G v d σV σD p) => ScatFun.wedgeTau G v d σV σD τV τD z.val) Set.univ := by
    intro p;
    refine' ContinuousOn.congr _ _;
    use fun z => prependZerosOne ( ScatFun.wedgeOutLvl p ) ( prepend ( ScatFun.wedgeOutCol p ) ( ScatFun.wedgeTpiece τV τD p z.val ) );
    · refine Continuous.continuousOn ?_;
      refine' Continuous.comp ( continuous_prependZerosOne _ ) ( Continuous.comp ( continuous_prepend _ ) _ );
      cases p <;> simp +decide [ wedgeTpiece ];
      · exact ContinuousOn.comp_continuous ( hτVc _ _ ) continuous_subtype_val fun x => x.2;
      · exact ContinuousOn.comp_continuous ( hτDc _ ) continuous_subtype_val fun x => x.2;
    · intro z hz; exact ScatFun.wedgeTau_eq_on_img G v d σV σD τV τD hpart p z.val z.2;
  convert continuous_of_relativeClopenPartition_seq hpart _;
  convert continuousOn_iff_continuous_restrict;
  intro p; specialize h_cont p; rw [ continuousOn_univ ] at h_cont; exact h_cont;

/--
The functional equation `(wedge v d).func = τ ∘ G.func ∘ σ`.
-/
lemma wedge_lb_funeq (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire)
    (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (hVeq : ∀ k l z, (v k).func z = τV k l (G.func (σV k l z)))
    (hDeq : ∀ i t, d.func t = τD i (G.func (σD i t)))
    (hsep : ∀ p, y ∉ closure (wedgeImg G v d σV σD p))
    (hpart : IsRelativeClopenPartition (wedgeImg G v d σV σD))
    (z : ↥(wedge v d).domain) :
    (wedge v d).func z
      = wedgeTau G v d σV σD τV τD (G.func (wedgeSigma G v d x σV σD z)) := by
  obtain ⟨k, hk⟩ | ⟨k, l, z', hk⟩ | ⟨i, t, hk⟩ := wedge_domain_cases v d z;
  · have hz : wedgeSigma G v d x σV σD z = x k := by
      unfold ScatFun.wedgeSigma;
      simp +decide only [wedge_domain, gl_domain, hk, unprepend_prepend, ↓reduceDIte];
      simp +decide [ prepend ];
    have hz : wedgeTau G v d σV σD τV τD y = zeroStream := by
      apply dif_neg;
      exact fun h => by obtain ⟨ p, hp ⟩ := Set.mem_iUnion.mp h; exact hsep p <| subset_closure hp;
    grind +suggestions;
  · convert ScatFun.wedgeTau_eq_on_img G v d σV σD τV τD hpart (Sum.inl (k, l)) (G.func (σV k l z')) _ using 1;
    · convert ScatFun.wedge_func_vertical_block v d k l z' _ using 1;
      exact congr_arg _ ( Subtype.ext hk );
      · convert ScatFun.wedgeTau_eq_on_img G v d σV σD τV τD hpart (Sum.inl (k, l)) (G.func (σV k l z')) _ using 1;
        · exact hVeq k l z' ▸ rfl;
        · exact Set.mem_range_self _;
      · exact hk ▸ z.2;
    · convert ScatFun.wedgeTau_eq_on_img G v d σV σD τV τD hpart (Sum.inl (k, l)) (G.func (σV k l z')) _ using 1;
      · unfold ScatFun.wedgeSigma;
        simp +decide only [wedge_domain, gl_domain, hk, prepend, ↓reduceIte, Fin.is_lt, ↓reduceDIte, Fin.eta];
        split_ifs <;> simp_all +decide [ unprepend_prepend, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne ];
        · rename_i h; have := congr_fun h l; simp +decide [ prependZerosOne ] at this;
          exact absurd this ( by rw [ show zeroStream l = 0 from by rfl ] ; norm_num );
        · congr!;
          exact hk.symm ▸ by simp +decide [ prepend ] ;
      · exact Set.mem_range_self _;
    · exact Set.mem_range_self _;
  · convert ScatFun.wedge_func_diagonal v d i t _ using 1;
    grind;
    · convert ScatFun.wedgeTau_eq_on_img G v d σV σD τV τD hpart (Sum.inr i) _ _ using 1;
      · convert congr_arg ( fun x => prependZerosOne i ( prepend n x ) ) ( hDeq i t ) using 1;
        unfold ScatFun.wedgeSigma; simp +decide [ hk ] ;
        simp +decide only [wedgeOutLvl, wedgeOutCol, wedgeTpiece, prepend, ↓reduceIte, add_lt_iff_neg_left, not_lt_zero, ↓reduceDIte, add_tsub_cancel_left];
        congr! 3;
      · unfold ScatFun.wedgeSigma ScatFun.wedgeImg; simp +decide [ hk ] ;
        unfold prepend; simp +decide ;
        grind;
    · grind

/--
`τ` is continuous on the range `G.func ∘ σ`.
-/
lemma wedgeTau_continuousOn_range (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire)
    (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (hτVc : ∀ k l, ContinuousOn (τV k l) (Set.range (fun z => G.func (σV k l z))))
    (hτDc : ∀ i, ContinuousOn (τD i) (Set.range (fun t => G.func (σD i t))))
    (hsep : ∀ p, y ∉ closure (wedgeImg G v d σV σD p))
    (hpart : IsRelativeClopenPartition (wedgeImg G v d σV σD)) :
    ContinuousOn (wedgeTau G v d σV σD τV τD)
      (Set.range (fun z => G.func (wedgeSigma G v d x σV σD z))) := by
  refine' ContinuousOn.mono ( _ ) ( Set.range_subset_iff.mpr _ );
  rotate_left;
  exact insert y (⋃ p, G.wedgeImg v d σV σD p);
  · intro z
    simp only [wedgeSigma, wedge_domain, gl_domain, mem_insert_iff, mem_iUnion, Sum.exists, Prod.exists];
    split_ifs <;> simp_all +decide [ ScatFun.wedgeImg ];
    · exact Or.inr <| Or.inl ⟨ _, _, _, _, rfl ⟩;
    · exact Or.inr <| Or.inr <| ⟨ _, _, _, rfl ⟩;
  · refine fun w hw => ?_;
    by_cases hw' : w = y;
    · refine tendsto_pi_nhds.mpr ?_;
      intro j
      have h_eventually_zero : ∀ᶠ w in nhdsWithin y (insert y (⋃ p, wedgeImg G v d σV σD p)), G.wedgeTau v d σV σD τV τD w j = 0 := by
        have h_eventually_zero : ∀ᶠ w in nhdsWithin y (insert y (⋃ p, wedgeImg G v d σV σD p)), ∀ p ∈ {p : (Fin n × ℕ) ⊕ ℕ | wedgeOutLvl p ≤ j}, w ∉ closure (wedgeImg G v d σV σD p) := by
          have h_eventually_zero : ∀ p ∈ {p : (Fin n × ℕ) ⊕ ℕ | wedgeOutLvl p ≤ j}, ∀ᶠ w in nhdsWithin y (insert y (⋃ p, wedgeImg G v d σV σD p)), w ∉ closure (wedgeImg G v d σV σD p) := by
            exact fun p hp => Filter.eventually_of_mem ( nhdsWithin_le_nhds <| IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_closure ) <| hsep p ) fun x hx => hx;
          have h_finite : Set.Finite {p : (Fin n × ℕ) ⊕ ℕ | wedgeOutLvl p ≤ j} := by
            refine Set.Finite.subset ( Set.toFinite ( Set.image ( fun p : Fin n × ℕ => Sum.inl p ) ( Set.univ ×ˢ Set.Iic j ) ∪ Set.image ( fun i : ℕ => Sum.inr i ) ( Set.Iic j ) ) ) ?_;
            rintro ( _ | _ ) <;> simp +decide [ wedgeOutLvl ];
          exact Filter.eventually_subset_of_finite h_finite h_eventually_zero;
        filter_upwards [ h_eventually_zero ] with w hw;
        by_cases hw'' : w ∈ ⋃ p, wedgeImg G v d σV σD p;
        · obtain ⟨ p, hp ⟩ := Set.mem_iUnion.mp hw'';
          rw [ wedgeTau_eq_on_img G v d σV σD τV τD hpart p w hp ];
          exact prependZerosOne_head_eq_zero _ _ _ ( lt_of_not_ge fun h => hw p h <| subset_closure hp );
        · unfold ScatFun.wedgeTau; aesop;
      rw [ hw' ];
      rw [ show G.wedgeTau v d σV σD τV τD y j = 0 from _ ];
      · exact tendsto_nhds_of_eventually_eq h_eventually_zero;
      · convert h_eventually_zero.self_of_nhdsWithin using 1;
        grind;
    · have h_cont : ContinuousWithinAt (G.wedgeTau v d σV σD τV τD) (⋃ p, G.wedgeImg v d σV σD p) w := by
        exact ContinuousOn.continuousWithinAt ( wedgeTau_continuousOn_UI G v d σV σD τV τD hτVc hτDc hpart ) ( by aesop );
      refine h_cont.mono_of_mem_nhdsWithin ?_
      rw [mem_nhdsWithin]
      refine ⟨{z | z ≠ y}, isOpen_ne, hw', ?_⟩
      rintro z ⟨hz1, rfl | hz2⟩
      · exact absurd rfl hz1
      · exact hz2

/-- **The wedge reduces to `G`, from a column reduction bundle (assembly).** -/
lemma wedge_lb_of_bundle (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire)
    (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
    (σD : ℕ → ↥d.domain → ↥G.domain)
    (τV : (k : Fin n) → ℕ → Baire → Baire)
    (τD : ℕ → Baire → Baire)
    (hσVc : ∀ k l, Continuous (σV k l))
    (hσDc : ∀ i, Continuous (σD i))
    (hτVc : ∀ k l, ContinuousOn (τV k l) (Set.range (fun z => G.func (σV k l z))))
    (hτDc : ∀ i, ContinuousOn (τD i) (Set.range (fun t => G.func (σD i t))))
    (hVeq : ∀ k l z, (v k).func z = τV k l (G.func (σV k l z)))
    (hDeq : ∀ i t, d.func t = τD i (G.func (σD i t)))
    (hVconv : ∀ k : Fin n, SetsConvergeTo (fun l => Set.range (σV k l)) (x k))
    (hsep : ∀ p, y ∉ closure (wedgeImg G v d σV σD p))
    (hpart : IsRelativeClopenPartition (wedgeImg G v d σV σD)) :
    Reduces (wedge v d) G := by
  refine ⟨wedgeSigma G v d x σV σD,
    wedgeSigma_continuous G v d x σV σD hσVc hσDc hVconv,
    wedgeTau G v d σV σD τV τD, ?_, ?_⟩
  · exact wedgeTau_continuousOn_range G v d y x hxy σV σD τV τD hτVc hτDc hsep hpart
  · intro z
    exact wedge_lb_funeq G v d y x hxy σV σD τV τD hVeq hDeq hsep hpart z

/--
A family `img` covered by pairwise-disjoint clopen shells `C` (with `img p ⊆ C p`)
is a relative clopen partition.
-/
lemma relClopen_of_clopen_shells {X : Type*} [TopologicalSpace X] {ι : Type*}
    (img C : ι → Set X)
    (hC : ∀ p, IsClopen (C p)) (hsub : ∀ p, img p ⊆ C p)
    (hdisj : ∀ p q, p ≠ q → Disjoint (C p) (C q)) :
    IsRelativeClopenPartition img := by
  refine ⟨ fun p q hpq => Disjoint.mono ( hsub p ) ( hsub q ) ( hdisj p q hpq ), ?_ ⟩;
  intro p;
  refine ⟨ C p, ( hC p ).2, ?_ ⟩;
  ext ⟨ x, hx ⟩ ; simp +decide [ Set.mem_iUnion ] at hx ⊢;
  exact ⟨ fun hx' => by obtain ⟨ q, hq ⟩ := hx; exact Classical.not_not.1 fun hq' => Set.disjoint_left.1 ( hdisj p q ( by aesop ) ) hx' ( hsub q hq ), fun hx' => hsub p hx' ⟩

/--
The nested-shell recursion: from images (parametrised by stage and shell level)
whose closures avoid `y`, build a decreasing sequence of basic clopen neighbourhoods
`nbhd y (Nseq m)` of `y` with the `(m+1)`-st disjoint from the `m`-th stage's image.
-/
lemma wedge_nested_shells (y : Baire) (S : ℕ → ℕ → Set Baire)
    (hS : ∀ m N, y ∉ closure (S m N)) :
    ∃ Nseq : ℕ → ℕ, Nseq 0 = 0 ∧
      Antitone (fun m => nbhd y (Nseq m)) ∧
      (∀ m, Disjoint (nbhd y (Nseq (m + 1))) (closure (S m (Nseq m)))) := by
  -- Define `Nseq` via `Nat.rec` (well-founded on the stage): `Nseq 0 := 0` and `Nseq (m+1) := (wedge_lb_separation y (nbhd y (Nseq m)) ((baire_nbhd_isClopen y (Nseq m)).isOpen) (hy_mem) (fun _ : Unit => S m (Nseq m)) (fun _ => hS m (Nseq m))).choose`, where `hy_mem : y ∈ nbhd y (Nseq m)` holds since `nbhd y N = {h | ∀ i ∈ Finset.range N, h i = y i}` and y agrees with itself.
  set Nseq : ℕ → ℕ := fun m => Nat.rec 0 (fun k ih => (wedge_lb_separation y (nbhd y ih) ((baire_nbhd_isClopen y ih).isOpen) (by
  exact fun _ _ => rfl) (fun _ : Unit => S k ih) (fun _ => hS k ih)).choose) m
  generalize_proofs at *;
  -- Show that the sequence `Nseq` satisfies the required properties.
  use Nseq
  generalize_proofs at *;
  refine' ⟨ rfl, antitone_nat_of_succ_le fun m => _, fun m => _ ⟩ <;> simp +decide [ Nseq ]; all_goals grind

/--
Per-column vertical reduction at codomain shell `nbhd y N` and domain shell
`nbhd' (x k) l`.
-/
lemma wedge_lb_colVert (G : ScatFun) (v : Fin n → ScatFun)
    (y : Baire) (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    (h_vert : ∀ (i : Fin n) (U : Set ↥G.domain), IsOpen U → x i ∈ U →
      ∃ (σ : (v i).domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, (v i).func z = τ (G.func (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        y ∉ closure (Set.range fun z => G.func (σ z)))
    (k : Fin n) (l N : ℕ) :
    ∃ (σ : ↥(v k).domain → ↥G.domain) (τ : Baire → Baire),
      Continuous σ ∧
      ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
      (∀ z, (v k).func z = τ (G.func (σ z))) ∧
      (∀ z, σ z ∈ nbhd' G.domain (x k) l) ∧
      (∀ z, G.func (σ z) ∈ nbhd y N) ∧
      y ∉ closure (Set.range fun z => G.func (σ z)) := by
  convert h_vert k ( nbhd' G.domain ( x k ) l ∩ G.func ⁻¹' ( nbhd y N ) ) ?_ ?_ using 1;
  · grind;
  · exact IsOpen.inter ( baire_nbhd'_isClopen _ _ _ |>.isOpen ) ( G.hCont.isOpen_preimage _ ( baire_nbhd_isClopen _ _ |>.isOpen ) );
  · unfold nbhd' nbhd; simp +decide [ hxy ] ;

/--
Per-column diagonal reduction at codomain shell `nbhd y N`.
-/
lemma wedge_lb_colDiag (G : ScatFun) (d : ScatFun)
    (y : Baire)
    (h_diag : ∀ (V : Set Baire), IsOpen V → y ∈ V →
      ∃ (σ : d.domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, d.func z = τ (G.func (σ z))) ∧
        (∀ z, G.func (σ z) ∈ V) ∧
        y ∉ closure (Set.range fun z => G.func (σ z)))
    (N : ℕ) :
    ∃ (σ : d.domain → ↥G.domain) (τ : Baire → Baire),
      Continuous σ ∧
      ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
      (∀ z, d.func z = τ (G.func (σ z))) ∧
      (∀ z, G.func (σ z) ∈ nbhd y N) ∧
      y ∉ closure (Set.range fun z => G.func (σ z)) := by
  apply h_diag;
  · exact baire_nbhd_isClopen y N |>.isOpen;
  · exact fun i hi => rfl

/--
**The inductive shell construction (Phase 1).**  From the local reduction
hypotheses, produce the column reduction bundle feeding `wedge_lb_of_bundle`.
-/
lemma wedge_lb_construction (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire)
    (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    (h_vert : ∀ (i : Fin n) (U : Set ↥G.domain), IsOpen U → x i ∈ U →
      ∃ (σ : (v i).domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, (v i).func z = τ (G.func (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        y ∉ closure (Set.range fun z => G.func (σ z)))
    (h_diag : ∀ (V : Set Baire), IsOpen V → y ∈ V →
      ∃ (σ : d.domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, d.func z = τ (G.func (σ z))) ∧
        (∀ z, G.func (σ z) ∈ V) ∧
        y ∉ closure (Set.range fun z => G.func (σ z))) :
    ∃ (σV : (k : Fin n) → ℕ → ↥(v k).domain → ↥G.domain)
      (σD : ℕ → ↥d.domain → ↥G.domain)
      (τV : (k : Fin n) → ℕ → Baire → Baire)
      (τD : ℕ → Baire → Baire),
      (∀ k l, Continuous (σV k l)) ∧
      (∀ i, Continuous (σD i)) ∧
      (∀ k l, ContinuousOn (τV k l) (Set.range (fun z => G.func (σV k l z)))) ∧
      (∀ i, ContinuousOn (τD i) (Set.range (fun t => G.func (σD i t)))) ∧
      (∀ k l z, (v k).func z = τV k l (G.func (σV k l z))) ∧
      (∀ i t, d.func t = τD i (G.func (σD i t))) ∧
      (∀ k : Fin n, SetsConvergeTo (fun l => Set.range (σV k l)) (x k)) ∧
      (∀ p, y ∉ closure (wedgeImg G v d σV σD p)) ∧
      IsRelativeClopenPartition (wedgeImg G v d σV σD) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ ≃ (Fin n × ℕ) ⊕ ℕ, True := by
    cases n <;> simp_all +decide;
  obtain ⟨Nseq, hNseq0, hNseq_anti, hNseq_disjoint⟩ := wedge_nested_shells y (fun m N => match e m with
    | Sum.inl (k, l) => Set.range (fun z => G.func (Classical.choose (wedge_lb_colVert G v y x hxy h_vert k l N) z))
    | Sum.inr i => Set.range (fun t => G.func (Classical.choose (wedge_lb_colDiag G d y h_diag N) t))) (fun m N => by
      cases h : e m <;> simp +decide [ h ];
      · exact Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert _ _ _ ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.right |> And.right;
      · exact Classical.choose_spec ( wedge_lb_colDiag G d y h_diag N ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.right);
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
  use fun k l z => Classical.choose ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) z;
  use fun i t => Classical.choose ( wedge_lb_colDiag G d y h_diag ( Nseq ( e.symm ( Sum.inr i ) ) ) ) t;
  use fun k l => Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) |> Classical.choose;
  use fun i => Classical.choose_spec ( wedge_lb_colDiag G d y h_diag ( Nseq ( e.symm ( Sum.inr i ) ) ) ) |> Classical.choose;
  · exact fun k l => Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) |> Classical.choose_spec |> And.left;
  · exact fun i => Classical.choose_spec ( wedge_lb_colDiag G d y h_diag ( Nseq ( e.symm ( Sum.inr i ) ) ) ) |> Classical.choose_spec |> And.left;
  · grind;
  · refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    · grind;
    · grind +qlia;
    · grind;
    · intro k W hW hxW;
      obtain ⟨ L, hL ⟩ := nbhd_basis' G.domain ( x k ) W hW hxW;
      use L;
      intro l hl z hz;
      obtain ⟨ w, rfl ⟩ := hz;
      exact hL <| Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) |> Classical.choose_spec |> fun h => h.2.2.2.1 w |> fun h' => by
        exact fun i hi => h' i ( Finset.mem_range.mpr ( lt_of_lt_of_le ( Finset.mem_range.mp hi ) hl ) );
    · refine ⟨ ?_, ?_ ⟩;
      · intro p;
        rcases p with ( ⟨ k, l ⟩ | i ) <;> simp +decide [ ScatFun.wedgeImg ];
        · exact Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.right |> And.right;
        · exact Classical.choose_spec ( wedge_lb_colDiag G d y h_diag ( Nseq ( e.symm ( Sum.inr i ) ) ) ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.right;
      · refine' relClopen_of_clopen_shells _ _ _ _ _;
        use fun p => nbhd y ( Nseq ( e.symm p ) ) \ nbhd y ( Nseq ( e.symm p + 1 ) );
        · exact fun p => IsClopen.diff ( baire_nbhd_isClopen _ _ ) ( baire_nbhd_isClopen _ _ );
        · intro p;
          refine Set.subset_diff.mpr ⟨ ?_, ?_ ⟩;
          · rcases p with ( ⟨ k, l ⟩ | i ) <;> simp +decide [ ScatFun.wedgeImg ];
            · exact Set.range_subset_iff.mpr fun z => Classical.choose_spec ( wedge_lb_colVert G v y x hxy h_vert k l ( Nseq ( e.symm ( Sum.inl ( k, l ) ) ) ) ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.right |> And.left |> fun h => h z;
            · exact Set.range_subset_iff.mpr fun t => Classical.choose_spec ( wedge_lb_colDiag G d y h_diag ( Nseq ( e.symm ( Sum.inr i ) ) ) ) |> Classical.choose_spec |> And.right |> And.right |> And.right |> And.left |> fun h => h t;
          · refine Disjoint.symm ( hNseq_disjoint ( e.symm p ) |> Disjoint.mono_right ?_ );
            cases p <;> simp +decide [ ScatFun.wedgeImg ]; all_goals exact subset_closure;
        · intro p q hpq
          by_cases h_cases : e.symm p < e.symm q;
          · refine Set.disjoint_left.mpr ?_;
            intro a ha hb;
            exact ha.2 ( hNseq_anti ( Nat.succ_le_of_lt h_cases ) hb.1 );
          · rw [ Set.disjoint_left ];
            simp +zetaDelta only [ne_eq, not_lt, mem_diff, not_and, Decidable.not_not, and_imp] at *;
            intro a ha₁ ha₂ ha₃;
            exact hNseq_anti ( Nat.succ_le_of_lt ( lt_of_le_of_ne h_cases ( Ne.symm ( by simpa [ Equiv.symm_apply_eq ] using hpq ) ) ) ) ha₁

/-- **The Disjointification Lemma — the wedge as a lower bound (memoir Lemma 5.6).**

If `G` admits, locally around anchors `x i ∈ G⁻¹(y)`, reductions of each vertical
`v i` whose images concentrate near `x i` and stay clear of `y` (`h_vert`), and
reductions of the diagonal `d` whose images concentrate near `y` yet still avoid
it in closure (`h_diag`), then the wedge `⋁(v ∣ d)` reduces to `G`.

This is the wedge counterpart of `pgl_reduces_of_local`, but it is *not* a
corollary of it: the columns of the wedge must be reduced into **disjoint** pieces
of `G` so that the inverse map `τ` is well defined, and producing those disjoint
pieces requires a fresh inductive neighbourhood construction.

### PROOF PLAN (memoir `5_precise_struct_memo.tex:224-263`)

Write `f := G.func`.  The construction mirrors `pointedGluing_lower_bound`
(`PointedGluing/LowerBoundLemma.lean`), generalised from one base point to the
wedge's `n` vertical columns + ω diagonal columns.

**Phase 0 — the piece index.**  The wedge's columns are indexed by
`P := (Fin n ⊕ Unit) × ℕ`: a vertical piece `(inl j, l)` is column `j < n` at ray
level `l` (output prefix `(0)^l(1)(j)⌢·`), and a diagonal piece `(inr (), i)` is
diagonal slot `n + i` (output prefix `(0)^i(1)(n)⌢·`).  Fix a bijection
`φ : P ≃ ℕ` (the memoir's `ι⁻¹`); piece `p` will be reduced into the `f`-shell
`V_{φ p} \ V_{φ p + 1}`.

**Phase 1 — inductive neighbourhood construction (lines 224–239).**  Build
simultaneously, by induction on the stage `m`:
  * open `V_m ⊆ B` with `V_0 = univ`, `V_{m+1} ⊆ V_m`, `y ∈ V_m`, and
    `SetsConvergeTo V y`;
  * open `U_{i,m} ⊆ ↥G.domain` with `U_{i,0} = univ`, `x i ∈ U_{i,m}`, and
    `SetsConvergeTo (U i) (x i)`;
  * at each stage, reductions of every column into `f ↾ (V_m \ V_{m+1})` (vertical
    `i` with `im σ ⊆ U_{i,m}`), obtained from `h_vert`/`h_diag` applied on `V_m`.
The keystone is `wedge_lb_separation`: conditions 1+2 give finitely many
reductions whose `f∘σ`-closures avoid `y`, so `V_{m+1} := nbhd y N` can be chosen
disjoint from all of them; continuity of `f` at each `x i` then shrinks `U_{i,m+1}`
into `U_{i,m} ∩ f⁻¹(V_{m+1})`.

  Recommended carve-out once the bundle is fixed:
  `wedge_lb_construction : … → ∃ (V U) (σⱽ τⱽ σᴰ τᴰ), [the properties above]`.

**Phase 2 — assemble `σ`** (lines 244–249, 257–260).  Define on the wedge domain
`gl (wedgeDomFamily v d)` by the three coordinate cases (cf. `wedge_func_*`):
  * `(j)⌢0^ω        ↦ x j`                       (vertical base point);
  * `(j)⌢(0)^l(1)⌢z ↦ σⱽ_{j,l} z`                (vertical block, via `φ`);
  * `(n+i)⌢z        ↦ σᴰ_i z`                    (diagonal column).
Continuity off the base points is `continuous_of_relativeClopenPartition_seq`
over the clopen first-coordinate slabs (as in `gl_reduces_of_pointwise`).
Continuity *at* each base point `(j)⌢0^ω` is `sufficient_cond_continuity`: a
sequence `(j)⌢(0)^{l_k}(1)⌢z_k → (j)⌢0^ω` forces `l_k → ∞`, whence
`σⱽ_{j,l_k} z_k ∈ U_{j,l_k} → x j` by `SetsConvergeTo (U j) (x j)`.

**Phase 3 — assemble `τ`** (lines 250–254, 262).  Set `τ y = 0^ω` and, for
`z ∈ V_m \ V_{m+1}` (well defined by Phase-1 disjointness, with `m = φ(column,
level)`), `τ z = (0)^{level}(1)(column)⌢ τ_{piece} z`.  This is the
disjoint-union-of-columns map; off `{y}` it is continuous by
`continuous_of_relativeClopenPartition_seq` over the shells.

**Phase 4 — continuity of `τ` at `y`** (line 262).  `sufficient_cond_continuity`
again: along any `z_k → y` with `z_k ≠ y`, the hosting stage `m_k → ∞` (because
`SetsConvergeTo V y`), so the output prefix length `level(m_k) → ∞` and
`τ z_k → 0^ω = τ y`.  This is the exact analogue of the
`firstNonzero → ∞ ⟹ prependZerosOne → 0^ω` argument in `pointedGluing_lower_bound`.

**Phase 5 — the functional equation.**  `(wedge v d).func = τ ∘ f ∘ σ`, checked
case-by-case against `wedge_func_vertical_base`, `wedge_func_vertical_block`,
`wedge_func_diagonal` and the per-piece reduction equations `(v i).func z = τⱽ …`
/ `d.func z = τᴰ …`.

The proof is assembled from `wedge_lb_construction` (the inductive shell
construction producing the disjoint column reduction bundle) and
`wedge_lb_of_bundle` (which builds `σ` = `wedgeSigma`, `τ` = `wedgeTau` and verifies
the reduction).

The hypothesis `hy : y ∈ Set.range G.func` is part of the requested statement but
turns out to be unnecessary (the anchors `x` together with `hxy` already exhibit
`y` as a value of `G.func` when `n > 0`, and the diagonal hypothesis carries the
relevant content otherwise); it is retained as stated. -/
theorem wedge_lower_bound (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire) (_hy : y ∈ Set.range G.func)
    (x : Fin n → ↥G.domain) (hxy : ∀ i, G.func (x i) = y)
    -- 1. each vertical reduces with image arbitrarily close to its anchor `x i`,
    --    while its `G`-image stays clear of `y`.
    (h_vert : ∀ (i : Fin n) (U : Set ↥G.domain), IsOpen U → x i ∈ U →
      ∃ (σ : (v i).domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, (v i).func z = τ (G.func (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        y ∉ closure (Set.range fun z => G.func (σ z)))
    -- 2. the diagonal reduces with `G`-image arbitrarily close to `y`,
    --    yet still avoiding `y` in closure.
    (h_diag : ∀ (V : Set Baire), IsOpen V → y ∈ V →
      ∃ (σ : d.domain → ↥G.domain) (τ : Baire → Baire),
        Continuous σ ∧
        ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
        (∀ z, d.func z = τ (G.func (σ z))) ∧
        (∀ z, G.func (σ z) ∈ V) ∧
        y ∉ closure (Set.range fun z => G.func (σ z))) :
    Reduces (wedge v d) G := by
  obtain ⟨σV, σD, τV, τD, hσVc, hσDc, hτVc, hτDc, hVeq, hDeq, hVconv, hsep, hpart⟩ :=
    wedge_lb_construction G v d y x hxy h_vert h_diag
  exact wedge_lb_of_bundle G v d y x hxy σV σD τV τD hσVc hσDc hτVc hτDc
    hVeq hDeq hVconv hsep hpart

end ScatFun

end
