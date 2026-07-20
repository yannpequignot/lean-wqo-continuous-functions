import WqoContinuousFunctions.DoubleSuccessor.Diagonal.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-! ### Helpers for the Disjointification clauses (`secondCase_wedge_vertical_clause` /
`secondCase_wedge_diag_clause`)

The diagonal clause assembles, per representative `g ∈ D`, a reduction of `g` into `F⇂V` with
values in pairwise disjoint clopen sets around pairwise distinct qualifying cocenters (supplied
by strong-solvability clause 2), then glues them into a single reduction of `glList D.toList`.
The general-purpose pieces are:

* `exists_disjoint_clopen_around` — pairwise disjoint basic clopen cylinders `nbhd (yₖ) N` at a
  common level around finitely many distinct points, inside a clopen `V₀` and avoiding `y`;
* `gl_restrict_reduces_into_of_disjoint_values` — the "un-gluing" step: a gluing of restrictions
  of `G` to blocks whose `G`-values lie in pairwise disjoint clopen sets `C k` reduces into `G`
  itself (`σ` = payload inclusion, `τ b = prepend (idx b) b` with `idx` decoded from the `C`s);
* `glList_reduces_into_of_disjoint_values` — blockwise reductions of the entries of a list into
  `G` with values in pairwise disjoint clopen sets glue to a reduction of the whole `glList`
  (route: `gl_reduces_of_pointwise` into the gluing of value-blocks of `G`, then the previous
  lemma);
* `secondCase_diag_piece_into_coRestrict` — a single representative `g ≤ F↾Q` with cocenter
  `y_Q ∈ C ⊆ V` reduces into `F⇂V` with values in `C`
  (`restrict_reduces_restrict_inter_of_cocenter_mem` + `reduces_block_into_coRestrict`);
* `secondCase_diag_exists_pieces` — strong-solvability clause 2 supplies, per entry of a list of
  diagonal representatives, qualifying pieces with pairwise *distinct* cocenters inside `V₀`
  (sequential choice, dodging the previously chosen cocenters via
  `exists_clopen_nbhd_disjoint_finite`).
-/

/-- **Pairwise disjoint clopen cylinders around distinct points.** Finitely many distinct points
`yk` of Baire space, none equal to `y`, all inside a clopen `V₀`, admit pairwise disjoint basic
clopen neighbourhoods inside `V₀` avoiding `y`: take `nbhd (yk k) N ∩ V₀` at a common level `N`
past every pairwise difference (cf. `exists_uniform_isolating_or_infinite_clopen`,
`ZeroDimensionalSpaces/IsolatingSequences.lean`). -/
lemma exists_disjoint_clopen_around {m : ℕ} (yk : Fin m → Baire)
    (hinj : Function.Injective yk) (y : Baire) (hne : ∀ k, yk k ≠ y)
    {V₀ : Set Baire} (hV₀ : IsClopen V₀) (hmem : ∀ k, yk k ∈ V₀) :
    ∃ C : Fin m → Set Baire, (∀ k, IsClopen (C k)) ∧ (∀ k, yk k ∈ C k) ∧
      (∀ k, C k ⊆ V₀) ∧ (∀ k, y ∉ C k) ∧
      ∀ k l, k ≠ l → Disjoint (C k) (C l) := by
  classical
  -- A coordinate separating each pair of distinct points, and each point from `y`.
  have hd : ∀ k l : Fin m, k ≠ l → ∃ i, yk k i ≠ yk l i :=
    fun k l hkl => Function.ne_iff.mp (hinj.ne hkl)
  have he : ∀ k, ∃ i, yk k i ≠ y i := fun k => Function.ne_iff.mp (hne k)
  choose! d hdspec using hd
  choose e hespec using he
  -- A common level `N` past every separating coordinate.
  obtain ⟨N, hdN, heN⟩ : ∃ N : ℕ, (∀ k l : Fin m, d k l < N) ∧ ∀ k : Fin m, e k < N := by
    refine ⟨(Finset.univ.sup (fun p : Fin m × Fin m => d p.1 p.2)) +
      (Finset.univ.sup e) + 1, fun k l => ?_, fun k => ?_⟩
    · exact Nat.lt_succ_of_le ((Finset.le_sup (f := fun p : Fin m × Fin m => d p.1 p.2)
        (Finset.mem_univ (k, l))).trans (Nat.le_add_right _ _))
    · exact Nat.lt_succ_of_le ((Finset.le_sup (f := e)
        (Finset.mem_univ k)).trans (Nat.le_add_left _ _))
  refine ⟨fun k => nbhd (yk k) N ∩ V₀, fun k => (baire_nbhd_isClopen _ N).inter hV₀,
    fun k => ⟨fun i _ => rfl, hmem k⟩, fun k => Set.inter_subset_right, ?_, ?_⟩
  · -- `y` is dodged: it differs from `yk k` at coordinate `e k < N`.
    intro k hy
    exact hespec k ((hy.1 (e k) (Finset.mem_range.mpr (heN k))).symm)
  · -- Distinct points get disjoint cylinders: they differ at `d k l < N`.
    intro k l hkl
    exact ((nbhd_disjoint_of_ne (hdN k l) (hdspec k l hkl)).mono
      Set.inter_subset_left Set.inter_subset_left)

/-
**Un-gluing into the ambient function.** If `B k ⊆ ↑G.domain` are blocks whose `G`-values lie
in pairwise disjoint clopen sets `C k`, then the gluing of the restrictions `G.restrict (B k)`
reduces into `G`: `σ` strips the block tag (payload inclusion `x ↦ unprepend x`), and
`τ b = prepend (idx b) b` re-attaches it, the index `idx b` being decodable from `b` since the
`C k` are pairwise disjoint (and clopen, so `τ` is continuous on the union). The `G`-value of
every image point stays in its block's `C`.
-/
lemma gl_restrict_reduces_into_of_disjoint_values (G : ScatFun) (B : ℕ → Set ↑G.domain)
    (C : ℕ → Set Baire) (hCcl : ∀ k, IsClopen (C k))
    (hCdisj : ∀ k l, k ≠ l → Disjoint (C k) (C l))
    (hBC : ∀ k, ∀ x ∈ B k, G.func x ∈ C k) :
    ∃ (σ : ↑(ScatFun.gl (fun k => G.restrict (B k))).domain → ↑G.domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun x => G.func (σ x)) ∧
      (∀ x, (ScatFun.gl (fun k => G.restrict (B k))).func x = τ (G.func (σ x))) ∧
      (∀ x, G.func (σ x) ∈ C (x.val 0)) := by
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
  use fun x => ⟨ unprepend x.val, by
    obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( G.restrict ( B k ) ).domain ) x;
    exact hk.2.1 ⟩
  all_goals generalize_proofs at *;
  use fun x => if h : ∃ k, x ∈ C k then prepend ( Classical.choose h ) x else x;
  · exact Continuous.subtype_mk ( continuous_unprepend.comp continuous_subtype_val ) _;
  · intro x hx
    generalize_proofs at *;
    obtain ⟨ y, rfl ⟩ := hx;
    refine ContinuousAt.continuousWithinAt ?_;
    refine' ContinuousAt.congr _ _;
    exact fun x => prepend ( y.val 0 ) x;
    · exact Continuous.continuousAt ( continuous_prepend _ );
    · filter_upwards [ IsOpen.mem_nhds ( hCcl ( y.val 0 ) |>.isOpen ) ( show G.func ⟨ unprepend y.val, by solve_by_elim ⟩ ∈ C ( y.val 0 ) from by
                                                                          have := GluingSet_inverse_short ( fun k => ( G.restrict ( B k ) ).domain ) y;
                                                                          unfold ScatFun.restrict at this; aesop; ) ] with x hx
      generalize_proofs at *;
      split_ifs with h;
      · have := Classical.choose_spec h;
        exact Classical.not_not.1 fun h' => Set.disjoint_left.mp ( hCdisj _ _ <| by tauto ) this hx;
      · exact False.elim <| h ⟨ _, hx ⟩;
  · intro x;
    obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( G.restrict ( B k ) ).domain ) x;
    have h_eq : (ScatFun.gl (fun k => G.restrict (B k))).func x = prepend k (G.func ⟨unprepend x.val, by
      grind +qlia⟩) := by
      all_goals generalize_proofs at *;
      convert ScatFun.gl_func_prepend ( fun k => G.restrict ( B k ) ) k ⟨ unprepend x.val, hk.2 ⟩ _ using 1;
      congr! 1;
      exact Subtype.ext ( by simp +decide [ ← hk.1, prepend_unprepend ] );
      grind [prepend_unprepend]
    generalize_proofs at *;
    have h_eq : G.func ⟨unprepend x.val, by
      assumption⟩ ∈ C k := by
      all_goals generalize_proofs at *;
      convert hBC k _ _;
      exact hk.2.choose_spec
    generalize_proofs at *;
    have h_eq : Classical.choose (show ∃ k, G.func ⟨unprepend x.val, by
                                    assumption⟩ ∈ C k from ⟨ k, h_eq ⟩) = k := by
                                    all_goals generalize_proofs at *;
                                    --exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( hCdisj _ _ h ) ( Classical.choose_spec pft ) h_eq
                                    exact Classical.not_not.1 fun h => Set.disjoint_left.mp ( hCdisj _ _ h ) ( Classical.choose_spec ‹∃ k, G.func ⟨ unprepend x.val, _ ⟩ ∈ C k› ) h_eq
    generalize_proofs at *;
    grind;
  · intro x;
    obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( G.restrict ( B k ) ).domain ) x;
    unfold ScatFun.restrict at hk; aesop;

/-- **Blockwise reductions with disjoint value-clopens glue.** If every entry `L[k]` of a list
reduces into `G` with all `G`-values in a clopen `C k`, the `C k` pairwise disjoint, then
`glList L` reduces into `G` with all values in `⋃_{k < L.length} C k`. Route: transport each
blockwise reduction into `G.restrict {x | G.func x ∈ C k}` (`gl_reduces_of_pointwise`), then
un-glue via `gl_restrict_reduces_into_of_disjoint_values`. -/
lemma glList_reduces_into_of_disjoint_values (L : List ScatFun) (G : ScatFun)
    (C : ℕ → Set Baire) (hCcl : ∀ k, IsClopen (C k))
    (hCdisj : ∀ k l, k ≠ l → Disjoint (C k) (C l))
    (hblocks : ∀ k, k < L.length →
      ∃ (σk : ↑(L.getD k ScatFun.empty).domain → ↑G.domain) (τk : Baire → Baire),
        Continuous σk ∧ ContinuousOn τk (Set.range fun z => G.func (σk z)) ∧
        (∀ z, (L.getD k ScatFun.empty).func z = τk (G.func (σk z))) ∧
        (∀ z, G.func (σk z) ∈ C k)) :
    ∃ (σ : ↑(ScatFun.glList L).domain → ↑G.domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun z => G.func (σ z)) ∧
      (∀ z, (ScatFun.glList L).func z = τ (G.func (σ z))) ∧
      (∀ z, G.func (σ z) ∈ ⋃ k ∈ Finset.range L.length, C k) := by
  -- Define `B : ℕ → Set ↑G.domain := fun k => if k < L.length then {x | G.func x ∈ C k} else ∅`.
  set B : ℕ → Set G.domain := fun k => if k < L.length then {x | G.func x ∈ C k} else ∅ with hB_def;
  obtain ⟨σ1, hσ1, τ1, hτ1, heq1⟩ : ∃ σ1 : (ScatFun.glList L).domain → (ScatFun.gl (fun k => G.restrict (B k))).domain, Continuous σ1 ∧ ∃ τ1 : Baire → Baire, ContinuousOn τ1 (Set.range ((ScatFun.gl (fun k => G.restrict (B k))).func ∘ σ1)) ∧ (∀ z, (ScatFun.glList L).func z = τ1 ((ScatFun.gl (fun k => G.restrict (B k))).func (σ1 z))) := by
    have hred : ∀ k, ScatFun.Reduces (L.getD k ScatFun.empty) (G.restrict (B k)) := by
      intro k
      by_cases hk : k < L.length
      · have hBk : B k = {x : ↑G.domain | G.func x ∈ C k} := by
          rw [hB_def]; simp only [hk, if_true]
        rw [hBk]
        obtain ⟨ σk, τk, hσk, hτk, h₁, h₂ ⟩ := hblocks k hk
        refine ScatFun.reduces_coRestrict_of_subtype G (L.getD k ScatFun.empty) (C k) ?_
        refine ⟨ fun z => ⟨ σk z, h₂ z ⟩, Continuous.subtype_mk hσk _, τk, ?_, fun z => h₁ z ⟩
        apply hτk.mono; rintro _ ⟨z, rfl⟩; exact ⟨z, rfl⟩
      · have hempty : L.getD k ScatFun.empty = ScatFun.empty := by
          rw [List.getD_eq_default]; omega
        rw [hempty]; exact ScatFun.empty_reduces _
    exact ScatFun.gl_reduces_of_pointwise (fun k => L.getD k ScatFun.empty) (fun k => G.restrict (B k)) hred;
  obtain ⟨σ2, τ2, hσ2, hτ2, heq2, hval2⟩ := gl_restrict_reduces_into_of_disjoint_values G B C hCcl hCdisj (by
    intro k x hx
    by_cases hk : k < L.length
    · rw [hB_def] at hx; simp only [hk, if_true, Set.mem_setOf_eq] at hx; exact hx
    · rw [hB_def] at hx; simp only [hk, if_false] at hx; exact absurd hx (Set.notMem_empty _));
  refine ⟨ fun z => σ2 ( σ1 z ), fun x => τ1 ( τ2 x ), hσ2.comp hσ1, ?_, ?_, ?_ ⟩;
  · refine hτ1.comp ( hτ2.mono ?_ ) ?_
    · exact Set.range_subset_iff.mpr fun z => ⟨ σ1 z, rfl ⟩
    · intro x hx; obtain ⟨ z, rfl ⟩ := hx
      exact ⟨ z, by simp only [Function.comp_apply]; exact heq2 (σ1 z) ⟩
  · intro z; rw [heq1 z, heq2 (σ1 z)]
  · intro z
    have h_index : (σ1 z).val 0 < L.length := by
      obtain ⟨ i, hi, hi' ⟩ := GluingSet_inverse_short ( fun k => ( G.restrict ( B k ) ).domain ) ( σ1 z )
      by_contra hcon
      push_neg at hcon
      rw [hi] at hcon
      have : B i = ∅ := by rw [hB_def]; simp only [if_neg (by omega : ¬ i < L.length)]
      simp only [ScatFun.restrict, this, Set.mem_setOf_eq] at hi'
      obtain ⟨h, hmem⟩ := hi'; exact absurd hmem (Set.notMem_empty _)
    exact Set.mem_iUnion₂.mpr ⟨(σ1 z).val 0, Finset.mem_range.mpr h_index, hval2 (σ1 z)⟩

/-
**A diagonal representative reduces into the corestriction with values near its qualifying
cocenter** (`6_double_successor_memo.tex:335-339`, single-`g` step). If `g ≤ F↾Q` for a piece
`Q ∈ 𝒫` whose cocenter lies in a clopen `C ⊆ V`, then `g` reduces into `F⇂V` with all values
in `C`: shrink `F↾Q` into `F↾(Q ∩ F⁻¹C)` around its cocenter
(`restrict_reduces_restrict_inter_of_cocenter_mem`), then transport into the corestriction
(`reduces_block_into_coRestrict`).
-/
lemma secondCase_diag_piece_into_coRestrict
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {Q : Set ↑F.domain} (hQ : Q ∈ Part) (g : ScatFun)
    (hgred : ScatFun.Reduces g (F.restrict Q))
    {C V : Set Baire} (hC : IsClopen C) (hCV : C ⊆ V)
    (hcoc : hA.cocenterOf hQ ∈ C) :
    ∃ (σ : ↑g.domain → ↑(F.coRestrict V).domain) (τ : Baire → Baire),
      Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict V).func (σ z)) ∧
      (∀ z, g.func z = τ ((F.coRestrict V).func (σ z))) ∧
      (∀ z, (F.coRestrict V).func (σ z) ∈ C) := by
  revert hgred;
  -- Apply the lemma `reduces_block_into_coRestrict` to obtain the required σ and τ.
  have h_reduces : g.Reduces (F.restrict Q) → g.Reduces (F.coRestrict C) := by
    intro hgred;
    obtain ⟨ σ, hσ, τ, hτ, h ⟩ := hgred;
    have h_restrict : ScatFun.Reduces (F.restrict Q) (F.restrict {w : ↑F.domain | w ∈ Q ∧ F.func w ∈ C}) := by
      apply restrict_reduces_restrict_inter_of_cocenter_mem;
      exact hC.isOpen;
      convert hcoc using 1;
    obtain ⟨ σ', hσ', τ', hτ', h' ⟩ := h_restrict;
    refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    use fun x => ⟨ σ' ( σ x ) |>.1, by
      simp +decide only [ScatFun.coRestrict];
      simp +decide only [ScatFun.restrict, mem_setOf_eq, coe_setOf];
      grind +splitIndPred ⟩
    all_goals generalize_proofs at *;
    fun_prop;
    use fun x => τ ( τ' x );
    · refine hτ.comp ?_ ?_;
      · refine hτ'.mono ?_;
        rintro _ ⟨ x, rfl ⟩ ; exact ⟨ σ x, rfl ⟩ ;
      · intro x hx;
        obtain ⟨ y, rfl ⟩ := hx;
        use y;
        convert h' ( σ y ) using 1;
    · intro x; specialize h x; specialize h' ( σ x ) ; aesop;
  intro hgred
  obtain ⟨σ, τ, hσ, hτ⟩ := h_reduces hgred;
  refine ⟨ fun z => ⟨ σ z, ?_ ⟩, hσ, ?_, ?_, ?_, ?_ ⟩;
  exact ⟨ σ z |>.2.1, hCV ( σ z |>.2.2 ) ⟩;
  · exact Continuous.subtype_mk ( continuous_subtype_val.comp τ ) _;
  · convert hτ.1 using 1;
  · aesop;
  · exact fun z => σ z |>.2.2

/-
**Qualifying pieces with pairwise distinct cocenters** (`6_double_successor_memo.tex:335-339`,
choice step). For every entry `l.get k` of a list of diagonal representatives (each realized by
some piece of cocenter `≠ y`), strong-solvability clause 2 supplies a piece `Q k ∈ 𝒫` with
cocenter `≠ y`, *inside* the prescribed clopen `V₀ ∋ y`, *pairwise distinct* across `k`
(sequential choice: each step dodges the finitely many previously chosen cocenters via
`exists_clopen_nbhd_disjoint_finite`), and `l.get k ≤ F↾(Q k)`.
-/
lemma secondCase_diag_exists_pieces
    (α : Ordinal.{0}) (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (l : List ScatFun)
    (hl : ∀ g ∈ l, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    {V₀ : Set Baire} (hV₀ : IsClopen V₀) (hyV₀ : y ∈ V₀) :
    ∃ (Q : Fin l.length → Set ↑F.domain) (hQ : ∀ k, Q k ∈ Part),
      Function.Injective (fun k => hA.cocenterOf (hQ k)) ∧
      (∀ k, hA.cocenterOf (hQ k) ≠ y) ∧
      (∀ k, hA.cocenterOf (hQ k) ∈ V₀) ∧
      (∀ k, ScatFun.Reduces (l.get k) (F.restrict (Q k))) := by
  revert l;
  -- By induction on the list l, we can construct the required family of pieces Q.
  intro l hl
  induction' l with g l ih;
  · simp +decide [ Function.Injective ];
  · obtain ⟨Q, hQ⟩ := ih (fun g hg => hl g (List.mem_cons_of_mem _ hg));
    obtain ⟨hQ, hQ_inj, hQ_ne_y, hQ_in_V₀, hQ_reduces⟩ := hQ
    obtain ⟨P, hP, hP_ne_y, hP_equiv⟩ := hl g (by simp);
    -- By strong-solvability clause 2, there exists a piece `Q' ∈ Part` with `hA.cocenterOf hQ' ≠ y`, `hA.cocenterOf hQ' ∈ V₀`, and `ScatFun.Reduces (F.restrict P) (F.restrict Q')`.
    obtain ⟨Q', hQ', hQ'_ne_y, hQ'_in_V₀, hQ'_reduces⟩ : ∃ Q' : Set ↑F.domain, ∃ hQ' : Q' ∈ Part, hA.cocenterOf hQ' ≠ y ∧ hA.cocenterOf hQ' ∈ V₀ ∧ ScatFun.Reduces (F.restrict P) (F.restrict Q') ∧ ∀ k : Fin l.length, hA.cocenterOf hQ' ≠ hA.cocenterOf (hQ k) := by
      have := hss.2.2;
      obtain ⟨V, hVcl, hyV, hV⟩ : ∃ V : Set Baire, IsClopen V ∧ y ∈ V ∧ Disjoint V (Set.range (fun k : Fin l.length => hA.cocenterOf (hQ k))) := by
        convert exists_clopen_nbhd_disjoint_finite ( Set.toFinite ( Set.range fun k : Fin l.length => hA.cocenterOf ( hQ k ) ) ) _ using 1;
        exact fun ⟨ k, hk ⟩ => hQ_ne_y k hk;
      obtain ⟨ Q', hQ', hQ'_ne_y, hQ'_in_V, hQ'_reduces ⟩ := this ( V ∩ V₀ ) ( hVcl.inter hV₀ ) ⟨ hyV, hyV₀ ⟩ |>.2 P hP hP_ne_y;
      exact ⟨ Q', hQ', hQ'_ne_y, hQ'_in_V.2, hQ'_reduces, fun k => fun hk => hV.le_bot ⟨ hQ'_in_V.1, hk ▸ Set.mem_range_self k ⟩ ⟩;
    refine ⟨ Fin.cons Q' Q, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ Fin.forall_fin_succ, * ];
    · intro i j hij;
      rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num at hij ⊢;
      · exact hQ'_reduces.2 ⟨ j, by linarith ⟩ hij;
      · exact hQ'_reduces.2 ⟨ i, by linarith ⟩ hij.symm;
      · exact congr_arg Fin.val ( hQ_inj hij );
    · exact ⟨ hP_equiv.2.trans hQ'_reduces.1, fun k => hQ_reduces k ⟩

/-- **Near-center reduction of `glList Mgi` into a centered `f0 ≡ pglFinset Mgi`.** The general-`g`
analogue of `maxFun_reduces_centered_near_center` (`DiagonalForLambdaPlusOne.lean:642`): with
`pglFinset Mgi = pgl (fun _ => glList Mgi.toList)` playing the role of `succMaxFun` and
`glList Mgi.toList` the role of `maxFun`, the same block-reduction/concentration argument yields,
for every open `V0` around a center `x0` (value the cocenter `y0`), a reduction `(σ, τ)` of
`glList Mgi.toList` into `f0` with `σ`-image inside `V0` and cocenter separation. -/
lemma pglFinset_reduces_glList_near_center (f0 : ScatFun) (Mgi : Finset ScatFun)
    (y0 : Baire) (hcent : IsCentered f0.func) (hy0 : cocenter f0.func hcent = y0)
    (h0 : ScatFun.Equiv f0 (ScatFun.pglFinset Mgi)) :
    ∃ x0 : ↑f0.domain, f0.func x0 = y0 ∧
      ∀ (V0 W : Set Baire), IsOpen V0 → (x0 : Baire) ∈ V0 → IsOpen W → y0 ∈ W →
        ∃ (σ : ↑(ScatFun.glList Mgi.toList).domain → ↑f0.domain) (τ : Baire → Baire),
          Continuous σ ∧ ContinuousOn τ (Set.range fun z => f0.func (σ z)) ∧
          (∀ z, (ScatFun.glList Mgi.toList).func z = τ (f0.func (σ z))) ∧
          (∀ z, ((σ z : ↑f0.domain) : Baire) ∈ V0) ∧
          (∀ z, f0.func (σ z) ∈ W) ∧
          y0 ∉ closure (Set.range fun z => f0.func (σ z)) := by
  classical
  set s : ℕ → ScatFun := fun _ => ScatFun.glList Mgi.toList with hs
  have hPdef : ScatFun.pglFinset Mgi = ScatFun.pgl s := rfl
  rw [hPdef] at h0
  obtain ⟨σ2, hσ2c, τ2, hτ2c, heq2⟩ := h0.2
  set z0 : ↑(ScatFun.pgl s).domain := ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ with hz0
  have hz0center : IsCenterFor (ScatFun.pgl s).func z0 :=
    ScatFun.pgl_isCenterFor_zeroStream_of_regular s (scatFun_const_isRegularSeq _)
  have hx0center : IsCenterFor f0.func (σ2 z0) :=
    centerInvariance_equiv hz0center ⟨h0.2, h0.1⟩ hσ2c hτ2c heq2
  have hx0val : f0.func (σ2 z0) = y0 := by
    rw [← hy0]
    exact scatteredHaveCocenter f0.func f0.hScat _ hcent.choose hx0center hcent.choose_spec
  have hpglcent : IsCentered (ScatFun.pgl s).func := isCentered_of_equiv hcent ⟨h0.2, h0.1⟩
  have hτ2y0 : τ2 y0 = zeroStream := by
    have key := rigidityOfCocenter_tau (ScatFun.pgl s).hScat f0.hScat hpglcent hcent
      ⟨h0.2, h0.1⟩ hσ2c hτ2c heq2
    rwa [hy0, ScatFun.cocenter_pgl_eq_zeroStream_of_regular s (scatFun_const_isRegularSeq _) hpglcent]
      at key
  refine ⟨σ2 z0, hx0val, ?_⟩
  intro V0 W hV0 hx0V0 hW hy0W
  -- Concentrate the block index `d` so the block-`d` reduction stays in `V0` and its `f0`-values in `W`.
  obtain ⟨d, hd⟩ : ∃ d, ∀ a : ↑(ScatFun.pgl s).domain,
      a ∈ nbhd' (ScatFun.pgl s).domain z0 d →
        (σ2 a : Baire) ∈ V0 ∧ f0.func (σ2 a) ∈ W := by
    have hcont1 : Continuous (fun a : ↑(ScatFun.pgl s).domain => (σ2 a : Baire)) :=
      continuous_subtype_val.comp hσ2c
    have hcont2 : Continuous (fun a : ↑(ScatFun.pgl s).domain => f0.func (σ2 a)) :=
      f0.hCont.comp hσ2c
    set U : Set ↑(ScatFun.pgl s).domain :=
      {a | (σ2 a : Baire) ∈ V0 ∧ f0.func (σ2 a) ∈ W} with hU
    have hUopen : IsOpen U :=
      (hcont1.isOpen_preimage _ hV0).inter (hcont2.isOpen_preimage _ hW)
    have hz0U : z0 ∈ U := ⟨hx0V0, by rw [hx0val]; exact hy0W⟩
    obtain ⟨d, hd⟩ := nbhd_basis' (ScatFun.pgl s).domain z0 U hUopen hz0U
    exact ⟨d, fun a ha => hd ha⟩
  obtain ⟨σB, τB, hσBc, hτBc, heqB, hσBval, hσBfunc⟩ := pgl_block_reduction_explicit s d
  have hmemnbhd : ∀ z : ↑(s d).domain, σB z ∈ nbhd' (ScatFun.pgl s).domain z0 d := by
    intro z i hi
    rw [hσBval z]
    exact prependZerosOne_head_eq_zero d _ i (Finset.mem_range.mp hi)
  refine ⟨fun z => σ2 (σB z), fun w => τB (τ2 w), hσ2c.comp hσBc, ?_, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.comp hτBc ?_ ?_
    · refine hτ2c.mono ?_
      rintro _ ⟨z, rfl⟩; exact ⟨σB z, rfl⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨z, heq2 (σB z)⟩
  · intro z
    show (s d).func z = τB (τ2 (f0.func (σ2 (σB z))))
    rw [← heq2 (σB z)]
    exact heqB z
  · intro z; exact (hd (σB z) (hmemnbhd z)).1
  · intro z; exact (hd (σB z) (hmemnbhd z)).2
  · intro hy0_closure
    obtain ⟨z_i, hz_i⟩ : ∃ z_i : ℕ → ↑(s d).domain,
        Filter.Tendsto (fun i => f0.func (σ2 (σB (z_i i)))) Filter.atTop (nhds y0) := by
      rw [mem_closure_iff_seq_limit] at hy0_closure
      obtain ⟨x, hx1, hx2⟩ := hy0_closure
      choose z hz using hx1
      exact ⟨z, hx2.congr fun n => hz n ▸ rfl⟩
    have hy0mem : y0 ∈ Set.range (fun a => f0.func (σ2 a)) := ⟨z0, hx0val⟩
    have hx' : Filter.Tendsto (fun i => f0.func (σ2 (σB (z_i i)))) Filter.atTop
        (nhdsWithin y0 (Set.range fun a => f0.func (σ2 a))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz_i
        (Filter.Eventually.of_forall (fun i => ⟨σB (z_i i), rfl⟩))
    have hcomp := (hτ2c.continuousWithinAt hy0mem).tendsto.comp hx'
    have h_contra : Filter.Tendsto (fun i => (ScatFun.pgl s).func (σB (z_i i))) Filter.atTop
        (nhds (τ2 y0)) := by
      simpa only [Function.comp_def, ← heq2] using hcomp
    have hcoord := (tendsto_pi_nhds.mp h_contra) d
    have hval1 : ∀ i, (ScatFun.pgl s).func (σB (z_i i)) d = 1 := by
      intro i; rw [hσBfunc (z_i i)]; exact prependZerosOne_at_i d _
    have hcoord2 : Filter.Tendsto (fun _ : ℕ => (1 : ℕ)) Filter.atTop (nhds ((τ2 y0) d)) :=
      hcoord.congr hval1
    have huniq := tendsto_nhds_unique tendsto_const_nhds hcoord2
    rw [hτ2y0] at huniq
    exact absurd huniq (by simp [zeroStream])

/-
**Vertical clause + anchor of `wedge_lower_bound` — single column.** The per-representative core
of `secondCase_wedge_vertical_clause`, phrased for one column `g ≡ pglFinset Mgi` realized by a piece
`F↾P ≡ g` of cocenter `y`. Mirrors `diagonal_wedge_vertical` (`DiagonalForLambdaPlusOne.lean:728`),
generalized from the single maximum `maxFun λ` to an arbitrary centered representative `g`.

Produces the anchor `x0 ∈ (F⇂V).domain` with `(F⇂V)(x0) = y` and, for every open `U ∋ x0`, a
reduction `(σ, τ)` of `glList Mgi` into `F⇂V` with image in `U` and `F`-image closure avoiding `y`.

**Proof strategy (leaf).**
1. **Anchor.** `F↾P` is centered (`hA.centered`) with cocenter `y` (`hPcoc`); a center `x_P`
   satisfies `(F↾P)(x_P) = y` (`scatteredHaveCocenter`). Its image in `(F⇂V).domain` — legitimate
   because `y ∈ V`, so `F(x_P) = y ∈ V` — is the anchor `x0` (value `y`).
2. **Vertical reduction.** For open `U ∋ x0`, `centerInvariance_reduce`
   (`CenteredFunctions/Theorems.lean:146`) at the center reduces `g` into `F↾(P ∩ U)` (image inside
   `U`); transport `g ≡ pglFinset Mgi` (`hgpgl`) and `glList Mgi ≤ pglFinset Mgi` to get a reduction
   of `glList Mgi`, then re-realize into `F⇂V` with `reduces_block_into_coRestrict`
   (`DiagonalForLambdaPlusOne.lean:166`).
3. **Separation.** `rigidityOfCocenter_separation` (`Theorems.lean:299`) gives
   `y ∉ closure (range (F⇂V ∘ σ))`, the cocenter-rigidity datum of the Disjointification Lemma.
-/
lemma secondCase_wedge_vertical_column
    (F : ScatFun) {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (g : ScatFun) (Mgi : Finset ScatFun)
    (hgpgl : ScatFun.Equiv g (ScatFun.pglFinset Mgi))
    {P : Set ↑F.domain} (hP : P ∈ Part)
    (hPcoc : hA.cocenterOf hP = y) (hPeq : ScatFun.Equiv (F.restrict P) g)
    (V : Set Baire) (hVcl : IsClopen V) (hyV : y ∈ V) :
    ∃ x0 : ↑(F.coRestrict V).domain, (F.coRestrict V).func x0 = y ∧
      ∀ (U : Set ↑(F.coRestrict V).domain), IsOpen U → x0 ∈ U →
        ∃ (σ : ↑(ScatFun.glList Mgi.toList).domain → ↑(F.coRestrict V).domain)
          (τ : Baire → Baire),
          Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict V).func (σ z)) ∧
          (∀ z, (ScatFun.glList Mgi.toList).func z = τ ((F.coRestrict V).func (σ z))) ∧
          (∀ z, σ z ∈ U) ∧
          y ∉ closure (Set.range fun z => (F.coRestrict V).func (σ z)) := by
  have := pglFinset_reduces_glList_near_center ( F.restrict P ) Mgi y ( hA.centered P hP ) hPcoc ( hPeq.trans hgpgl );
  obtain ⟨ x0, hx0 ⟩ := this;
  refine ⟨ ⟨ x0, ?_ ⟩, ?_, ?_ ⟩;
  exact ⟨ x0.2.1, by simpa [ ScatFun.restrict ] using hx0.1.symm ▸ hyV ⟩;
  · convert hx0.1 using 1;
  · intro U hU hx0U
    obtain ⟨V0, hV0_open, hV0_eq⟩ : ∃ V0 : Set Baire, IsOpen V0 ∧ U = Subtype.val ⁻¹' V0 := by
      obtain ⟨ V0, hV0_open, hV0_eq ⟩ := hU;
      exact ⟨ V0, hV0_open, hV0_eq.symm ⟩;
    obtain ⟨ σ, τ, hσ, hτ, hστ, hσV0, hσV, hσy ⟩ := hx0.2 V0 V hV0_open ( by simpa [ hV0_eq ] using hx0U ) hVcl.isOpen hyV;
    refine ⟨ fun z => ⟨ σ z, ?_ ⟩, τ, ?_, ?_, ?_, ?_, ?_ ⟩;
    exact ⟨ σ z |>.2.1, hσV z ⟩;
    · fun_prop;
    · convert hτ using 1;
    · convert hστ using 1;
    · exact fun z => hV0_eq.symm ▸ hσV0 z;
    · convert hσy using 1

/-- **Anchors + vertical clause of `wedge_lower_bound`** for the second case (part of obligation 3,
`6_double_successor_memo.tex:328-333`). For each column `i`, an anchor `x i ∈ (F⇂V).domain` with
value `y` (the image under `F⇂V` of a *center* of the representative piece `F↾Pᵢ ≡ gM i`), together
with — for every open `U' ∋ x i` — a reduction `(σ, τ)` of the vertical column `v i = glList (Mg i)`
into `F⇂V` whose image lies in `U'` and whose `F`-image closure avoids `y`.

**Proof (scaffold).** Assemble `secondCase_wedge_vertical_column` over the `Fin n` columns: from the
*realized* (rep→piece) hypothesis `hMreal`, pick per column `i` a piece `Pᵢ` realizing `gM i`
(cocenter `y`, `F↾Pᵢ ≡ gM i`), then `choose` the anchor and per-`U'` reduction from the column lemma.

`hMreal` (rep→piece) is the companion of the *cover* clause and is exposed directly by
`secondCase_blockData`; it is threaded here through `secondCase_wedge_le_coRestrict` from the
construction. The only remaining leaf is the per-column core `secondCase_wedge_vertical_column`. -/
lemma secondCase_wedge_vertical_clause
    (F : ScatFun)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire}
    {n : ℕ} (gM : Fin n → ScatFun) (Mg : Fin n → Finset ScatFun)
    (hgpgl : ∀ i, ScatFun.Equiv (gM i) (ScatFun.pglFinset (Mg i)))
    (hMreal : ∀ i, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (gM i))
    (V : Set Baire) (hVcl : IsClopen V) (hyV : y ∈ V) :
    ∃ x : Fin n → ↑(F.coRestrict V).domain, (∀ i, (F.coRestrict V).func (x i) = y) ∧
      ∀ (i : Fin n) (U : Set ↑(F.coRestrict V).domain), IsOpen U → x i ∈ U →
        ∃ (σ : ↑(ScatFun.glList (Mg i).toList).domain → ↑(F.coRestrict V).domain)
          (τ : Baire → Baire),
          Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict V).func (σ z)) ∧
          (∀ z, (ScatFun.glList (Mg i).toList).func z = τ ((F.coRestrict V).func (σ z))) ∧
          (∀ z, σ z ∈ U) ∧
          y ∉ closure (Set.range fun z => (F.coRestrict V).func (σ z)) := by
  classical
  choose P hP hPcoc hPeq using hMreal
  choose x0 hx0 hcol using fun i =>
    secondCase_wedge_vertical_column F hA (gM i) (Mg i) (hgpgl i) (hP i) (hPcoc i) (hPeq i) V hVcl hyV
  exact ⟨x0, hx0, fun i U hU hxU => hcol i U hU hxU⟩

/-- **Diagonal clause of `wedge_lower_bound`** for the second case (part of obligation 3,
`6_double_successor_memo.tex:335-339`). For every open `W ∋ y`, a reduction `(σ, τ)` of the diagonal
`glList D` into `F⇂V` whose `F`-image lies in `W` yet whose closure avoids `y`.

**Proof strategy** (the general analog of `diagonal_wedge_diag_clause`,
`DiagonalForLambdaPlusOne.lean:178`): it suffices to produce, per `g ∈ D`, a reduction of `g` into
`F⇂V` with image in `W` avoiding `y`, then assemble over `D` via `glList`. Fix `g ∈ D`: `hDreal`
gives `P ∈ 𝒫_D` with `F↾P ≡ g` and cocenter `y_P ≠ y`; strong solvability clause 2 (`hss.2`) places
such a `y_P` inside `W`. Pick a clopen `V' ⊆ W` around `y_P` avoiding `y`; `F↾P` centered with
cocenter `y_P` gives `g ≤ F⇂V'` (`reduces_coRestrict_cocenter_nbhd`-style), the closure avoiding
`y`. -/
lemma secondCase_wedge_diag_clause
    (α : Ordinal.{0}) (F : ScatFun)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    (D : Finset ScatFun)
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    (V : Set Baire) (hVcl : IsClopen V) (hyV : y ∈ V) :
    ∀ (W : Set Baire), IsOpen W → y ∈ W →
      ∃ (σ : ↑(ScatFun.glList D.toList).domain → ↑(F.coRestrict V).domain) (τ : Baire → Baire),
        Continuous σ ∧ ContinuousOn τ (Set.range fun z => (F.coRestrict V).func (σ z)) ∧
        (∀ z, (ScatFun.glList D.toList).func z = τ ((F.coRestrict V).func (σ z))) ∧
        (∀ z, (F.coRestrict V).func (σ z) ∈ W) ∧
        y ∉ closure (Set.range fun z => (F.coRestrict V).func (σ z)) := by
  classical
  intro W hWopen hyW
  set m := D.toList.length with hm_def
  -- A basic clopen `V₀ ∋ y` inside `V ∩ W`.
  obtain ⟨N₀, hN₀⟩ := nbhd_basis y (V ∩ W) (hVcl.isOpen.inter hWopen) ⟨hyV, hyW⟩
  set V₀ : Set Baire := nbhd y N₀ with hV₀_def
  have hV₀cl : IsClopen V₀ := baire_nbhd_isClopen y N₀
  have hyV₀ : y ∈ V₀ := fun i _ => rfl
  -- Qualifying pieces with pairwise distinct cocenters inside `V₀` (clause 2 + choice).
  obtain ⟨Q, hQ, hinj, hne, hmem, hred⟩ := secondCase_diag_exists_pieces α F hA hss D.toList
    (fun g hg => hDreal g (Finset.mem_toList.mp hg)) hV₀cl hyV₀
  -- Pairwise disjoint clopen cylinders around the cocenters, inside `V₀`, avoiding `y`.
  obtain ⟨C, hCcl, hCmem, hCsub, hCy, hCdisj⟩ :=
    exists_disjoint_clopen_around (fun k => hA.cocenterOf (hQ k)) hinj y hne hV₀cl hmem
  -- Pad the disjoint clopen family to an `ℕ`-indexed one.
  set Cpad : ℕ → Set Baire := fun k => if h : k < m then C ⟨k, h⟩ else ∅ with hCpad_def
  have hCpadcl : ∀ k, IsClopen (Cpad k) := by
    intro k; simp only [hCpad_def]; split
    · exact hCcl _
    · exact isClopen_empty
  have hCpaddisj : ∀ k l, k ≠ l → Disjoint (Cpad k) (Cpad l) := by
    intro k l hkl
    simp only [hCpad_def]
    split <;> split
    · exact hCdisj _ _ (fun h => hkl (congrArg Fin.val h))
    · exact Set.disjoint_empty _
    · exact (Set.disjoint_empty _).symm
    · exact Set.disjoint_empty _
  have hCpadsub : ∀ k, Cpad k ⊆ V₀ := by
    intro k; simp only [hCpad_def]; split
    · exact hCsub _
    · exact Set.empty_subset _
  have hCpady : ∀ k, y ∉ Cpad k := by
    intro k; simp only [hCpad_def]; split
    · exact hCy _
    · exact Set.notMem_empty y
  -- Per-block reductions into `F⇂V` with values in `Cpad k`.
  have hblocks : ∀ k, k < D.toList.length →
      ∃ (σk : ↑(D.toList.getD k ScatFun.empty).domain → ↑(F.coRestrict V).domain)
        (τk : Baire → Baire),
        Continuous σk ∧
        ContinuousOn τk (Set.range fun z => (F.coRestrict V).func (σk z)) ∧
        (∀ z, (D.toList.getD k ScatFun.empty).func z = τk ((F.coRestrict V).func (σk z))) ∧
        (∀ z, (F.coRestrict V).func (σk z) ∈ Cpad k) := by
    intro k hk
    have hgetD : D.toList.getD k ScatFun.empty = D.toList.get ⟨k, hk⟩ := by
      rw [List.getD_eq_getElem _ _ hk]; rfl
    have hCk : Cpad k = C ⟨k, hk⟩ := dif_pos hk
    rw [hgetD, hCk]
    exact secondCase_diag_piece_into_coRestrict F hA (hQ ⟨k, hk⟩) _ (hred ⟨k, hk⟩)
      (hCcl ⟨k, hk⟩) (fun b hb => ((hN₀ (hCsub ⟨k, hk⟩ hb)).1 : b ∈ V)) (hCmem ⟨k, hk⟩)
  -- Glue the blocks.
  obtain ⟨σ, τ, hσc, hτc, heq, hval⟩ := glList_reduces_into_of_disjoint_values D.toList
    (F.coRestrict V) Cpad hCpadcl hCpaddisj hblocks
  -- The union of the (finitely many, occupied) value-blocks: clopen, inside `W`, avoiding `y`.
  set T : Set Baire := ⋃ k ∈ Finset.range D.toList.length, Cpad k with hT_def
  have hTcl : IsClopen T := isClopen_biUnion_finset (fun k _ => hCpadcl k)
  have hTW : T ⊆ W := by
    intro b hb
    obtain ⟨k, -, hbk⟩ := Set.mem_iUnion₂.mp hb
    exact (hN₀ (hCpadsub k hbk)).2
  have hTy : y ∉ T := by
    intro hy
    obtain ⟨k, -, hyk⟩ := Set.mem_iUnion₂.mp hy
    exact hCpady k hyk
  refine ⟨σ, τ, hσc, hτc, heq, fun z => hTW (hval z), fun hy => hTy ?_⟩
  exact closure_minimal (Set.range_subset_iff.mpr hval) hTcl.isClosed hy

/-- **The Disjointification-Lemma obligation of the second case**, isolated
(`6_double_successor_memo.tex:321-342`). For any clopen neighbourhood `V ∋ y` (in the construction
`V = U ∩ Wᶜ`), the diagonal wedge `⋀(v ∣ gl D)` reduces into `F⇂V`. This is the wiring of
`ScatFun.wedge_lower_bound` (Disjointification Lemma, proved) against the two clauses
`secondCase_wedge_vertical_clause` / `secondCase_wedge_diag_clause`; the anchor for the `_hy`
premise is column `0` (available since `hpos : 0 < n` in the second case). -/
lemma secondCase_wedge_le_coRestrict
    (α : Ordinal.{0}) (F : ScatFun)
    {Part : Set (Set ↑F.domain)} (hA : F.IsCPartition Part)
    {y : Baire} (hss : hA.IsStronglySolvableAt α.limitPart y)
    {n : ℕ} (hpos : 0 < n) (gM : Fin n → ScatFun) (Mg : Fin n → Finset ScatFun)
    (D : Finset ScatFun)
    (hgpgl : ∀ i, ScatFun.Equiv (gM i) (ScatFun.pglFinset (Mg i)))
    (hMreal : ∀ i, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP = y ∧ ScatFun.Equiv (F.restrict P) (gM i))
    (hDreal : ∀ g ∈ D, ∃ (P : Set ↑F.domain) (hP : P ∈ Part),
        hA.cocenterOf hP ≠ y ∧ ScatFun.Equiv (F.restrict P) g)
    (V : Set Baire) (hVcl : IsClopen V) (hyV : y ∈ V) :
    ScatFun.Reduces
      (ScatFun.wedge (fun i => ScatFun.glList (Mg i).toList) (ScatFun.glList D.toList))
      (F.coRestrict V) := by
  obtain ⟨x, hxy, hvert⟩ :=
    secondCase_wedge_vertical_clause F hA gM Mg hgpgl hMreal V hVcl hyV
  exact ScatFun.wedge_lower_bound (F.coRestrict V) (fun i => ScatFun.glList (Mg i).toList)
    (ScatFun.glList D.toList) y ⟨x ⟨0, hpos⟩, hxy _⟩ x hxy
    (fun i U hU hxU => hvert i U hU hxU)
    (secondCase_wedge_diag_clause α F hA hss D hDreal V hVcl hyV)


end