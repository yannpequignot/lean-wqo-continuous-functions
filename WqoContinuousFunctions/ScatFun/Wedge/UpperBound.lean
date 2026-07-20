import WqoContinuousFunctions.ScatFun.Wedge.Defs
import WqoContinuousFunctions.ScatFun.FiniteGluing
import WqoContinuousFunctions.CenteredFunctions.CenteredAsPgluing.Helpers
import WqoContinuousFunctions.PointedGluing.ClopenPartitionReduces

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

namespace ScatFun

variable {n : ℕ}

/-! ## Helper lemmas towards `wedge_upper_bound` -/

/-- `repSeq` of a one-element family is the constant family. -/
lemma repSeq_const_one (w : ScatFun) :
    repSeq (![w] : Fin 1 → ScatFun) = fun _ => w := by
  ext; simp [repSeq, Nat.mod_one]

/-- A finite gluing of `m` copies of `w` is a member of `FinGl ![w]`. -/
lemma glList_replicate_mem_finGl (w : ScatFun) (m : ℕ) :
    glList (List.replicate m w) ∈ FinGl (![w] : Fin 1 → ScatFun) := by
  use fun _ => m
  simp only [Gl, glList]
  unfold copiesSeq copiesList
  simp +decide only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_fin_one, List.finRange, zero_add, List.ofFn_succ, Fin.isValue, Fin.cast_eq_self, List.ofFn_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_eq_getElem?_getD, and_self]
  constructor
  exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩

/-- **Vertical block reduces to the pointed-gluing column.**  If every ray of `G` on the
vertical block `A i` (at base point `y`) reduces to finitely many copies of `v i`, then the
restriction of `G` to `A i` reduces to the constant pointed gluing `pgl (fun _ => v i)`
(the `i`-th vertical column of the wedge). -/
lemma vertical_block_reduces_pgl (G : ScatFun) (v : Fin n → ScatFun) (y : Baire)
    (S : Set ↑G.domain) (i : ℕ) (hi : i < n)
    (h_vertical : ∀ (j : ℕ),
      ∃ m, Reduces (G.rayOn y S j) (glList (List.replicate m (v ⟨i, hi⟩)))) :
    Reduces (G.restrict S) (pgl (fun _ : ℕ => v ⟨i, hi⟩)) := by
  have hrays : ContinuouslyReduces (G.func ∘ (Subtype.val : ↥S → ↑G.domain))
      (pgl (rayShiftSeq G y S 0)).func :=
    pgl_reduces_of_rays G y S S 0 (le_refl _) (fun a _ i hi => absurd hi (Nat.not_lt_zero i))
  have h1 : Reduces (G.restrict S) (pgl (rayShiftSeq G y S 0)) :=
    hrays.comp_homeomorph_left (G.restrictEquiv S)
  have h2 : Reduces (pgl (rayShiftSeq G y S 0))
      (pgl (repSeq (![v ⟨i, hi⟩] : Fin 1 → ScatFun))) := by
    apply finitegenerationAndPgluing_upper
    intro k
    obtain ⟨m, hm⟩ := h_vertical k
    exact ⟨glList (List.replicate m (v ⟨i, hi⟩)), glList_replicate_mem_finGl _ _, hm⟩
  rw [repSeq_const_one] at h2
  exact h1.trans h2

/-- **Rays as upper bound, based form.**  The canonical reduction of `G` (restricted to `S`,
seen as `G.func ∘ val`) into the pointed gluing of its rays, with `τ zeroStream = y`. -/
lemma pgl_reduces_of_rays_based (G : ScatFun) (y : Baire) (S : Set ↑G.domain) :
    ∃ (σ : ↥S → ↑(pgl (rayShiftSeq G y S 0)).domain) (τ : Baire → Baire),
      Continuous σ ∧
      ContinuousOn τ (Set.range (fun a => (pgl (rayShiftSeq G y S 0)).func (σ a))) ∧
      (∀ a : ↥S, G.func a.val = τ ((pgl (rayShiftSeq G y S 0)).func (σ a))) ∧
      τ zeroStream = y ∧
      Filter.Tendsto τ
        (nhdsWithin zeroStream (Set.range (fun a => (pgl (rayShiftSeq G y S 0)).func (σ a))))
        (nhds y) := by
  refine ⟨fun a => ⟨raySigma0 G y S 0 a,
      raySigma0_mem G y S S 0 (le_refl _) (fun a _ i hi => absurd hi (Nat.not_lt_zero i)) a⟩,
    fun w => if w = zeroStream then y else stripZerosOne (firstNonzero w) w,
    (raySigma0_continuous G y S 0).subtype_mk _, ?_, ?_, if_pos rfl, ?_⟩
  · intro w hw; by_cases hw' : w = zeroStream <;> simp_all +decide [ ContinuousWithinAt ] ;
    · rw [ tendsto_pi_nhds ];
      intro k; rw [ nhdsWithin ] ; simp +decide [ Filter.Tendsto ] ;
      refine Filter.mem_inf_principal.mpr ?_;
      refine' Filter.mem_of_superset ( _ ) _;
      exact { w' : Baire | ∀ i ≤ k, w' i = 0 };
      · rw [ nhds_pi ];
        simp +decide only [zeroStream, nhds_discrete, Filter.pure_zero, Filter.mem_pi, Filter.mem_zero];
        exact ⟨ Finset.Iic k, Finset.finite_toSet _, fun _ => { 0 }, fun _ => by simp +decide, fun w hw => fun i hi => by simpa using hw i ( Finset.mem_Iic.mpr hi ) ⟩;
      · intro w' hw' hw''; obtain ⟨ a, rfl ⟩ := hw''; simp_all +decide [ raySigma0_func ] ;
        split_ifs at * <;> simp_all +decide [ prependZerosOne ];
        specialize hw' ( firstDiff y ( G.func a.val ) - 0 ) ; simp_all +decide ;
        have := firstDiff_mem_raySet y ( G.func a.val ) ‹_›; simp_all +decide [ RaySet ] ;
        rw [ firstNonzero_prependZerosOne ];
        rw [ stripZerosOne_prependZerosOne ] ; linarith [ this.1 k ( by linarith ) ] ;
    · refine' Filter.Tendsto.congr' _ _;
      use fun w' => stripZerosOne ( firstNonzero w ) w';
      · rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
        filter_upwards [ firstNonzero_eventuallyEq w hw', IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) hw' ] with x hx₁ hx₂ ; aesop;
      · refine' Continuous.continuousWithinAt _;
        exact continuous_pi fun _ => continuous_apply _;
  · intro a; dsimp only; split_ifs with hh <;> simp_all +decide [ raySigma0_func ]
    · grind [prependZerosOne_ne_zeroStream]
    · grind [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
  · rw [ tendsto_pi_nhds ];
    intro k; rw [ nhdsWithin ] ; simp +decide [ Filter.Tendsto ] ;
    refine Filter.mem_inf_principal.mpr ?_;
    refine' Filter.mem_of_superset ( _ ) _;
    exact { w' : Baire | ∀ i ≤ k, w' i = 0 };
    · rw [ nhds_pi ];
      simp +decide only [zeroStream, nhds_discrete, Filter.pure_zero, Filter.mem_pi, Filter.mem_zero];
      exact ⟨ Finset.Iic k, Finset.finite_toSet _, fun _ => { 0 }, fun _ => by simp +decide, fun w hw => fun i hi => by simpa using hw i ( Finset.mem_Iic.mpr hi ) ⟩;
    · intro w' hw' hw''; obtain ⟨ a, rfl ⟩ := hw''; simp_all +decide [ raySigma0_func ] ;
      split_ifs at * <;> simp_all +decide [ prependZerosOne ];
      · specialize hw' ( firstDiff y ( G.func a.val ) - 0 ) ; simp_all +decide ;
        have := firstDiff_mem_raySet y ( G.func a.val ) ‹_›; simp_all +decide [ RaySet ] ;
        rw [ firstNonzero_prependZerosOne ];
        rw [ stripZerosOne_prependZerosOne ] ; linarith [ this.1 k ( by linarith ) ]

/-
**Finite generation upper bound into a constant column, based form.**  If every `f j`
reduces to finitely many copies of `w`, then `pgl f` reduces to the constant pointed gluing
`pgl (fun _ => w)`, via a reduction whose `τ` fixes the base point (`τ zeroStream = zeroStream`)
and tends to the base point near it.
-/
lemma pgl_const_upper_based (w : ScatFun) (f : ℕ → ScatFun)
    (hf : ∀ j, ∃ m, Reduces (f j) (glList (List.replicate m w))) :
    ∃ (σ : ↑(pgl f).domain → ↑(pgl (fun _ : ℕ => w)).domain) (τ : Baire → Baire),
      Continuous σ ∧
      ContinuousOn τ (Set.range (fun z => (pgl (fun _ : ℕ => w)).func (σ z))) ∧
      (∀ z, (pgl f).func z = τ ((pgl (fun _ : ℕ => w)).func (σ z))) ∧
      τ zeroStream = zeroStream ∧
      Filter.Tendsto τ
        (nhdsWithin zeroStream (Set.range (fun z => (pgl (fun _ : ℕ => w)).func (σ z))))
        (nhds zeroStream) := by
  have hrep : repSeq (![w] : Fin 1 → ScatFun) = fun _ => w := repSeq_const_one w
  rw [show (fun _ : ℕ => w) = repSeq (![w] : Fin 1 → ScatFun) from hrep.symm]
  obtain ⟨σ, hσ, hσ0, τ, hτ, heq⟩ := pgl_reduces_of_local_base f
    (pgl (repSeq (![w] : Fin 1 → ScatFun)))
    ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩
    (by
      intro i V hVopen hxV
      obtain ⟨m, hm⟩ := hf i
      have hgl : Reduces (f i) (gl (copiesSeq (![w] : Fin 1 → ScatFun) (fun _ => m))) := by
        convert hm using 2
        unfold copiesSeq glList copiesList
        simp +decide [ List.finRange ]
      exact pgl_repSeq_local (![w] : Fin 1 → ScatFun) (by norm_num) f i (fun _ => m) hgl V hVopen hxV)
  have hτ0 : τ zeroStream = zeroStream := by
    have := heq ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩
    rw [pgl_func_zeroStream, hσ0, pgl_func_zeroStream] at this
    exact this.symm
  refine ⟨σ, τ, hσ, hτ, heq, hτ0, ?_⟩
  have hmem : zeroStream ∈ Set.range (fun z => (pgl (repSeq (![w] : Fin 1 → ScatFun))).func (σ z)) := by
    refine ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, ?_⟩
    show (pgl (repSeq (![w] : Fin 1 → ScatFun))).func (σ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩) = zeroStream
    rw [hσ0, pgl_func_zeroStream]
  have hcwa := hτ.continuousWithinAt hmem
  rw [ContinuousWithinAt, hτ0] at hcwa
  exact hcwa

/-- **Based vertical reduction.**  As `vertical_block_reduces_pgl`, but exposing the reduction
witness with the *based* property `τ zeroStream = y`: the column reduction sends the
pointed-gluing base point back to `y`. -/
lemma vertical_block_reduces_pgl_based (G : ScatFun) (v : Fin n → ScatFun) (y : Baire)
    (S : Set ↑G.domain) (i : ℕ) (hi : i < n)
    (h_vertical : ∀ (j : ℕ),
      ∃ m, Reduces (G.rayOn y S j) (glList (List.replicate m (v ⟨i, hi⟩)))) :
    ∃ (σ : ↑(G.restrict S).domain → ↑(pgl (fun _ : ℕ => v ⟨i, hi⟩)).domain) (τ : Baire → Baire),
      Continuous σ ∧
      ContinuousOn τ (Set.range (fun z => (pgl (fun _ : ℕ => v ⟨i, hi⟩)).func (σ z))) ∧
      (∀ z, (G.restrict S).func z = τ ((pgl (fun _ : ℕ => v ⟨i, hi⟩)).func (σ z))) ∧
      τ zeroStream = y ∧
      Filter.Tendsto τ
        (nhdsWithin zeroStream
          (Set.range (fun z => (pgl (fun _ : ℕ => v ⟨i, hi⟩)).func (σ z))))
        (nhds y) := by
  obtain ⟨σ₁, τ₁, hσ₁, hτ₁, heq₁, hτ₁0, htend₁⟩ := pgl_reduces_of_rays_based G y S
  obtain ⟨σ₂, τ₂, hσ₂, hτ₂, heq₂, hτ₂0, htend₂⟩ :=
    pgl_const_upper_based (v ⟨i, hi⟩) (rayShiftSeq G y S 0) (fun j => h_vertical j)
  refine ⟨fun z => σ₂ (σ₁ ((G.restrictEquiv S) z)), τ₁ ∘ τ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hσ₂.comp (hσ₁.comp (G.restrictEquiv S).continuous)
  · refine ContinuousOn.comp hτ₁ (hτ₂.mono ?_) ?_
    · rintro _ ⟨z, rfl⟩; exact ⟨σ₁ ((G.restrictEquiv S) z), rfl⟩
    · rintro _ ⟨z, rfl⟩
      rw [← heq₂ (σ₁ ((G.restrictEquiv S) z))]
      exact ⟨(G.restrictEquiv S) z, rfl⟩
  · intro z
    show (G.func ∘ (Subtype.val : ↥S → ↑G.domain)) ((G.restrictEquiv S) z) = _
    rw [Function.comp_apply, heq₁ ((G.restrictEquiv S) z), heq₂]; rfl
  · show τ₁ (τ₂ zeroStream) = y
    rw [hτ₂0, hτ₁0]
  · refine htend₁.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨htend₂.mono_left (nhdsWithin_mono _ ?_), ?_⟩
    · rintro _ ⟨z, rfl⟩; exact ⟨σ₁ ((G.restrictEquiv S) z), rfl⟩
    · filter_upwards [self_mem_nhdsWithin] with w hw
      obtain ⟨z, rfl⟩ := hw
      rw [← heq₂ (σ₁ ((G.restrictEquiv S) z))]
      exact ⟨(G.restrictEquiv S) z, rfl⟩

/-! ## The retag left-inverse `wUntag` -/

/-- Left inverse of `retag n` on the range of `gl (wedgeDomFamily …)`.  Given a wedge value
`w = (0)^l (1)(c)⌢z`, recovers the underlying glued value `prepend slot payload`:
the vertical columns (`c < n`) recover `prepend c (prependZerosOne l z)` and the diagonal
column (`c = n`) recovers `prepend (n + l) z`. -/
def wUntag (n : ℕ) (w : Baire) : Baire :=
  let l := firstNonzero w
  let tail := stripZerosOne l w
  let c := tail 0
  let z := unprepend tail
  if c < n then prepend c (prependZerosOne l z) else prepend (n + l) z

/-- `wUntag` undoes the retag of a vertical block value `(0)^l(1)(j)⌢z` (`j < n`). -/
lemma wUntag_retag_vertical (n j l : ℕ) (hj : j < n) (z : Baire) :
    wUntag n (prependZerosOne l (prepend j z)) = prepend j (prependZerosOne l z) := by
  unfold wUntag
  simp only
  rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
  rw [show (prepend j z) 0 = j from by simp [prepend], if_pos hj, unprepend_prepend]

/-- `wUntag` undoes the retag of a diagonal value `(0)^l(1)(n)⌢z`. -/
lemma wUntag_retag_diagonal (n l : ℕ) (z : Baire) :
    wUntag n (prependZerosOne l (prepend n z)) = prepend (n + l) z := by
  unfold wUntag
  simp only
  rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
  rw [show (prepend n z) 0 = n from by simp [prepend], if_neg (lt_irrefl n), unprepend_prepend]

/-! ## The explicit reduction `(wSigma, wTau)` -/

/-- The `σ`-map of the wedge reduction: on the block `P i` send `x` to slot `i` of the glued
wedge domain, carrying the block reduction `σb i`. -/
def wSigma (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (P : ℕ → Set ↑G.domain) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (x : ↑G.domain) : ↑(gl (wedgeDomFamily v d)).domain :=
  ⟨prepend (partitionIndex P hP_cover x)
      (σb (partitionIndex P hP_cover x)
        ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩).val,
    mem_gluingSet_prepend (σb (partitionIndex P hP_cover x)
        ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩).2⟩

/-- The `τ`-map of the wedge reduction: send the base point to `y`, otherwise invert the
retag (`wUntag`) and apply the relevant block reduction `τb`. -/
def wTau (n : ℕ) (y : Baire) (τb : ℕ → Baire → Baire) (w : Baire) : Baire :=
  if w = zeroStream then y else τb ((wUntag n w) 0) (unprepend (wUntag n w))

/-
**Continuity of `wSigma`.**
-/
lemma wSigma_continuous (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (P : ℕ → Set ↑G.domain) (hP_clopen : ∀ i, IsClopen (P i))
    (hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (hσb : ∀ i, Continuous (σb i)) :
    Continuous (wSigma G v d P hP_cover σb) := by
  constructor;
  intro s hs; rw [ isOpen_iff_mem_nhds ] ; intro x hx; simp_all +decide [ Set.preimage ] ;
  obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( hP_cover.symm ▸ Set.mem_univ x ) ; simp_all +decide [ Set.disjoint_left, ScatFun.wSigma ] ;
  -- Since $P i$ is clopen, the set $\{x \in P i \mid \sigmab i x \in s\}$ is open in $P i$.
  have h_open_in_Pi : IsOpen {x : ↥(G.restrict (P i)).domain | ⟨prepend i (σb i x).val, mem_gluingSet_prepend (σb i x).2⟩ ∈ s} := by
    convert hs.preimage _ using 1;
    exact Continuous.subtype_mk ( continuous_prepend i |> Continuous.comp <| continuous_subtype_val.comp <| hσb i ) _;
  obtain ⟨ t, ht₁, ht₂ ⟩ := h_open_in_Pi; simp_all +decide [ Set.preimage ] ;
  refine Filter.mem_of_superset ( Filter.inter_mem ( IsOpen.mem_nhds ( hP_clopen i |>.isOpen ) hi ) ( IsOpen.mem_nhds ( ht₁.preimage <| continuous_subtype_val ) <| show ( x : Baire ) ∈ t from ?_ ) ) ?_;
  · replace ht₂ := Set.ext_iff.mp ht₂ ⟨ x, ⟨ x.2, hi ⟩ ⟩ ; simp_all +decide ;
    grind +extAll;
  · intro x hx; specialize ht₂; replace ht₂ := Set.ext_iff.mp ht₂ ⟨ x, ⟨ x.2, hx.1 ⟩ ⟩ ; simp_all +decide ;
    grind

/-
**The reduction equation** for `(wSigma, wTau)`.
-/
lemma wedge_slot_eq (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun) (y : Baire)
    (P : ℕ → Set ↑G.domain) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (τb : ℕ → Baire → Baire)
    (heqb : ∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z)))
    (hbase : ∀ i, i < n → τb i zeroStream = y)
    (x : ↑G.domain) :
    G.func x = wTau n y τb ((wedge v d).func (wSigma G v d P hP_cover σb x)) := by
  -- By definition of `wSigma` and `wTau`, we can split into cases based on whether `i < n` or `i ≥ n`.
  set i := partitionIndex P hP_cover x with hi_def
  by_cases h : i < n;
  · have h_val : (wedgeDomFamily v d i).func (σb i ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩) ∈ PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)) := by
      have h_val : (wedgeDomFamily v d i) = pgl (fun _ => v ⟨i, h⟩) := by
        exact ScatFun.wedgeDomFamily_vertical v d ⟨ i, h ⟩;
      grind [pgl_func_mem];
    cases' h_val with h_val h_val;
    · have h_eq : G.func x = τb i zeroStream := by
        grind [restrict_func_eq];
      have h_eq : (wedge v d).func (wSigma G v d P hP_cover σb x) = retag n (prepend i zeroStream) := by
        convert congr_arg ( fun z => retag n z ) ( gl_func_prepend ( wedgeDomFamily v d ) i ( σb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ ) _ ) using 1;
        rw [ Set.mem_singleton_iff.mp h_val ];
      rw [ h_eq, retag_vertical_base ];
      · unfold wTau; aesop;
      · exact h;
    · obtain ⟨l, z, hz⟩ : ∃ l z, (wedgeDomFamily v d i).func (σb i ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩) = prependZerosOne l z := by
        simp +zetaDelta only [Subtype.forall, image_univ, mem_iUnion, mem_range] at *;
        tauto;
      -- By definition of `wSigma`, we have:
      have h_wSigma : (wedge v d).func (wSigma G v d P hP_cover σb x) = retag n (prepend i (prependZerosOne l z)) := by
        convert congr_arg ( fun x => retag n x ) ( gl_func_prepend ( wedgeDomFamily v d ) i ( σb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ ) _ ) using 1;
        rw [ hz ];
      rw [ h_wSigma, retag_vertical_block ];
      · convert heqb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ using 1;
        rw [ hz, wTau ];
        rw [ wUntag_retag_vertical ] <;> norm_num [ h ];
        split_ifs <;> simp_all +decide [ prepend ];
        · grind [prependZerosOne_ne_zeroStream];
        · exact congr_arg _ ( by rw [ unprepend_prepend ] );
      · exact h;
  · have h_val : (wedge v d).func (wSigma G v d P hP_cover σb x) = prependZerosOne (i - n) (prepend n ((wedgeDomFamily v d i).func (σb i ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩))) := by
      convert ScatFun.retag_diagonal n ( i - n ) ( ( ScatFun.wedgeDomFamily v d i ).func ( σb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ ) ) using 1;
      rw [ Nat.add_sub_of_le ( le_of_not_gt h ) ];
      convert congr_arg ( fun z => retag n z ) ( gl_func_prepend ( wedgeDomFamily v d ) i ( σb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ ) _ ) using 1;
    rw [ h_val, wTau ];
    rw [ if_neg ];
    · rw [ wUntag_retag_diagonal ];
      rw [ Nat.add_sub_of_le ( le_of_not_gt h ) ];
      convert heqb i ⟨ x.val, ⟨ x.2, partitionIndex_mem P hP_cover x ⟩ ⟩ using 1;
    · intro H; have := congr_fun H ( i - n ) ; simp +decide [ prependZerosOne ] at this;
      exact absurd this ( by erw [ show zeroStream ( i - n ) = 0 from by rfl ] ; norm_num )

/-- A sequence in Baire converging to `zeroStream` with all terms nonzero has
`firstNonzero` tending to infinity. -/
lemma firstNonzero_tendsto_atTop (x : ℕ → Baire) (hne : ∀ m, x m ≠ zeroStream)
    (hlim : Filter.Tendsto x Filter.atTop (nhds zeroStream)) :
    Filter.Tendsto (fun m => firstNonzero (x m)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  have hev : ∀ᶠ m in Filter.atTop, ∀ k < M, x m k = 0 := by
    rw [tendsto_pi_nhds] at hlim
    have hk : ∀ k, ∀ᶠ m in Filter.atTop, x m k = 0 := by
      intro k
      have := (hlim k).eventually (show ({(0:ℕ)} : Set ℕ) ∈ nhds (zeroStream k) by simp [zeroStream])
      simpa using this
    have hfin : (∀ᶠ m in Filter.atTop, ∀ k ∈ Finset.range M, x m k = 0) := by
      rw [Filter.eventually_all_finset]
      intro k _; exact hk k
    filter_upwards [hfin] with m hm k hk' using hm k (Finset.mem_range.mpr hk')
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  exact ⟨N, fun m hm => by
    by_contra h
    push_neg at h
    exact (firstNonzero_val_ne (hne m)) (hN m hm (firstNonzero (x m)) h)⟩

/-- The retag left-inverse `wUntag` recovers, from a non-base-point value of the reduction,
the glued slot point `prepend i val` (with `i` the partition slot and `val` the block value). -/
lemma wUntag_wedge_wSigma (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (P : ℕ → Set ↑G.domain) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (x : ↑G.domain)
    (hne : (wedge v d).func (wSigma G v d P hP_cover σb x) ≠ zeroStream) :
    wUntag n ((wedge v d).func (wSigma G v d P hP_cover σb x))
      = prepend (partitionIndex P hP_cover x)
          ((wedgeDomFamily v d (partitionIndex P hP_cover x)).func
            (σb (partitionIndex P hP_cover x)
              ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩)) := by
  set i := partitionIndex P hP_cover x with hi
  set val := (wedgeDomFamily v d i).func
    (σb i ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩) with hval
  have hgl : (wedge v d).func (wSigma G v d P hP_cover σb x) = retag n (prepend i val) := by
    convert congr_arg (fun z => retag n z) (gl_func_prepend (wedgeDomFamily v d) i
      (σb i ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩) _) using 1
  by_cases h : i < n
  · have hmem : val ∈ PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)) := by
      have heq : wedgeDomFamily v d i = pgl (fun _ => v ⟨i, h⟩) := wedgeDomFamily_vertical v d ⟨i, h⟩
      rw [hval]; rw [scatFun_func_cast heq]; exact pgl_func_mem _ _
    rcases hmem with h0 | hblk
    · rw [Set.mem_singleton_iff] at h0
      exfalso; apply hne; rw [hgl, h0, retag_vertical_base n i h]
    · rw [Set.mem_iUnion] at hblk
      obtain ⟨l, z, -, hz⟩ := hblk
      rw [hgl, ← hz, retag_vertical_block n i l h z, wUntag_retag_vertical n i l h z, hz]
  · rw [hgl, show i = n + (i - n) from by omega, retag_diagonal n (i - n) val,
      wUntag_retag_diagonal n (i - n) val]
    congr 1; omega

/-- `wUntag n` is continuous away from the base point `zeroStream`. -/
lemma wUntag_continuousOn : ContinuousOn (wUntag n) {w : Baire | w ≠ zeroStream} := by
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  refine ContinuousAt.continuousWithinAt ?_
  have hl : ∀ᶠ w' in nhds w, firstNonzero w' = firstNonzero w := firstNonzero_eventuallyEq w hw
  set l₀ := firstNonzero w with hl0
  set c₀ := (stripZerosOne l₀ w) 0 with hc0
  have hccont : Continuous (fun w' : Baire => (stripZerosOne l₀ w') 0) :=
    (continuous_apply 0).comp (continuous_stripZerosOne l₀)
  have hc : ∀ᶠ w' in nhds w, (stripZerosOne l₀ w') 0 = c₀ :=
    hccont.continuousAt.preimage_mem_nhds ((isOpen_discrete {c₀}).mem_nhds rfl)
  by_cases hcn : c₀ < n
  · apply ContinuousAt.congr
      (f := fun w' => prepend c₀ (prependZerosOne l₀ (unprepend (stripZerosOne l₀ w'))))
    · exact ((continuous_prepend c₀).comp ((continuous_prependZerosOne l₀).comp
        (continuous_unprepend.comp (continuous_stripZerosOne l₀)))).continuousAt
    · filter_upwards [hl, hc] with w' hl' hc'
      unfold wUntag; simp only [hl', hc', hcn, if_pos]
  · apply ContinuousAt.congr
      (f := fun w' => prepend (n + l₀) (unprepend (stripZerosOne l₀ w')))
    · exact ((continuous_prepend (n + l₀)).comp
        (continuous_unprepend.comp (continuous_stripZerosOne l₀))).continuousAt
    · filter_upwards [hl, hc] with w' hl' hc'
      unfold wUntag; simp only [hl', hc', hcn, if_neg, not_false_iff]

/-- **Continuity of `wTau` away from the base point.** -/
lemma wTau_continuousOn_nonzero (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun) (y : Baire)
    (P : ℕ → Set ↑G.domain) (_hP_clopen : ∀ i, IsClopen (P i))
    (_hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (_hσb : ∀ i, Continuous (σb i))
    (τb : ℕ → Baire → Baire)
    (hτb : ∀ i, ContinuousOn (τb i) (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z))))
    (_heqb : ∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z))) :
    ContinuousOn (wTau n y τb)
      (Set.range (fun x => (wedge v d).func (wSigma G v d P hP_cover σb x))
        ∩ {w | w ≠ zeroStream}) := by
  set R := Set.range (fun x => (wedge v d).func (wSigma G v d P hP_cover σb x)) with hR
  -- `g w = τb ((wUntag w) 0) (unprepend (wUntag w))` is continuous on `R ∩ {≠ 0}`
  have hT : ContinuousOn (fun u => τb (u 0) (unprepend u))
      (wUntag n '' (R ∩ {w | w ≠ zeroStream})) := by
    refine continuousOn_piecewise_clopen (fun i u => τb i (unprepend u))
      (fun i => {u : Baire | u 0 = i}) (fun z _ => ⟨z 0, rfl⟩)
      (fun i => isClopen_preimage_zero i) ?_ ?_ (fun z _ => ⟨z 0, rfl⟩)
      (fun u => τb (u 0) (unprepend u)) ?_
    · intro z _ i hi j hj
      simp only [Set.mem_setOf_eq] at hi hj; dsimp only; rw [show i = j from hi.symm.trans hj]
    · intro i
      refine (hτb i).comp continuous_unprepend.continuousOn ?_
      rintro u ⟨⟨w', hw', rfl⟩, hu0⟩
      simp only [Set.mem_setOf_eq] at hu0
      obtain ⟨x, rfl⟩ := hw'.1
      have hne : (wedge v d).func (wSigma G v d P hP_cover σb x) ≠ zeroStream := hw'.2
      rw [wUntag_wedge_wSigma G v d P hP_cover σb x hne] at hu0 ⊢
      simp only [prepend] at hu0
      rw [unprepend_prepend]
      rw [← hu0]
      exact ⟨⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩, rfl⟩
    · intro z _ i hi
      simp only [Set.mem_setOf_eq] at hi; dsimp only; rw [hi]
  have hg : ContinuousOn (fun w => τb ((wUntag n w) 0) (unprepend (wUntag n w)))
      (R ∩ {w | w ≠ zeroStream}) :=
    hT.comp (wUntag_continuousOn.mono (Set.inter_subset_right)) (Set.mapsTo_image _ _)
  refine hg.congr ?_
  rintro w ⟨-, hwne⟩
  simp only [Set.mem_setOf_eq] at hwne
  show wTau n y τb w = _
  unfold wTau; rw [if_neg hwne]

/-- Any neighbourhood of `zeroStream` contains a basic depth-neighbourhood. -/
lemma basic_nbhd_of_zeroStream (V : Set Baire) (hV : V ∈ nhds (zeroStream : Baire)) :
    ∃ M : ℕ, {w : Baire | ∀ k < M, w k = 0} ⊆ V := by
  rw [nhds_pi] at hV
  obtain ⟨I, hI, t, ht, htsub⟩ := Filter.mem_pi.mp hV
  refine ⟨(hI.toFinset.sup id) + 1, fun w hw => htsub ?_⟩
  intro i hi
  have hi' : i ≤ hI.toFinset.sup id := Finset.le_sup (f := id) (by simpa using hi)
  have hwi : w i = 0 := hw i (by omega)
  rw [hwi]; exact mem_of_mem_nhds (ht i)

/-- The reduction value is the retag of the slot point `prepend i val` (always). -/
lemma wedge_wSigma_eq_retag (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (P : ℕ → Set ↑G.domain) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (x : ↑G.domain) :
    (wedge v d).func (wSigma G v d P hP_cover σb x)
      = retag n (prepend (partitionIndex P hP_cover x)
          ((wedgeDomFamily v d (partitionIndex P hP_cover x)).func
            (σb (partitionIndex P hP_cover x)
              ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩))) := by
  convert congr_arg (fun z => retag n z) (gl_func_prepend (wedgeDomFamily v d)
    (partitionIndex P hP_cover x)
    (σb (partitionIndex P hP_cover x) ⟨x.val, ⟨x.2, partitionIndex_mem P hP_cover x⟩⟩) _) using 1

/-- **The reduction images tend to `y` along sequences approaching the base point.** -/
lemma wTau_seq_tendsto (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun) (y : Baire)
    (P : ℕ → Set ↑G.domain) (_hP_clopen : ∀ i, IsClopen (P i))
    (_hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (_hσb : ∀ i, Continuous (σb i))
    (τb : ℕ → Baire → Baire)
    (_hτb : ∀ i, ContinuousOn (τb i) (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z))))
    (heqb : ∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z)))
    (hbase : ∀ i, i < n → τb i zeroStream = y)
    (hconv : ∀ U : Set Baire, IsOpen U → y ∈ U → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      Set.range (fun z => (G.restrict (P i)).func z) ⊆ U)
    (hbase_cont : ∀ i, i < n → Filter.Tendsto (τb i)
      (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) (nhds y))
    (x : ℕ → Baire)
    (hx_mem : ∀ m, x m ∈ Set.range (fun x => (wedge v d).func (wSigma G v d P hP_cover σb x)))
    (hx_ne : ∀ m, x m ≠ zeroStream)
    (hx_lim : Filter.Tendsto x Filter.atTop (nhds zeroStream)) :
    Filter.Tendsto (fun m => wTau n y τb (x m)) Filter.atTop (nhds y) := by
  rw [tendsto_nhds]
  intro U hU hyU
  choose f hf using hx_mem
  set ii := fun m => partitionIndex P hP_cover (f m) with hii
  set valf := fun m => (wedgeDomFamily v d (ii m)).func
    (σb (ii m) ⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩) with hvalf
  have hwT : ∀ m, wTau n y τb (x m) = G.func (f m) := fun m => by
    rw [← hf m, ← wedge_slot_eq G v d y P hP_cover σb τb heqb hbase (f m)]
  have hret : ∀ m, x m = retag n (prepend (ii m) (valf m)) := fun m => by
    rw [← hf m]; exact wedge_wSigma_eq_retag G v d P hP_cover σb (f m)
  obtain ⟨Nd, hNd⟩ := hconv U hU hyU
  have hMc : ∀ c, c < n → ∃ Mc : ℕ, ∀ val : Baire, (∀ k < Mc, val k = 0) →
      val ∈ Set.range (fun z => (wedgeDomFamily v d c).func (σb c z)) → τb c val ∈ U := by
    intro c hc
    have hmem : {val | τb c val ∈ U} ∈
        nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d c).func (σb c z))) :=
      (hbase_cont c hc) (hU.mem_nhds hyU)
    rw [mem_nhdsWithin] at hmem
    obtain ⟨V, hVopen, hzV, hVsub⟩ := hmem
    obtain ⟨Mc, hMcsub⟩ := basic_nbhd_of_zeroStream V (hVopen.mem_nhds hzV)
    exact ⟨Mc, fun val hval hvalrange => hVsub ⟨hMcsub hval, hvalrange⟩⟩
  choose Mc hMcspec using hMc
  set M := max Nd ((Finset.univ : Finset (Fin n)).sup (fun c => Mc c.val c.isLt)) + 1 with hM
  have hfn : Filter.Tendsto (fun m => firstNonzero (x m)) Filter.atTop Filter.atTop :=
    firstNonzero_tendsto_atTop x hx_ne hx_lim
  filter_upwards [hfn.eventually_ge_atTop M] with m hm
  simp only [Set.mem_preimage]
  rw [hwT m]
  by_cases hcm : ii m < n
  · -- vertical
    have hval_pgs : valf m ∈ PointedGluingSet (fun _ : ℕ => (Set.univ : Set Baire)) := by
      have heq : wedgeDomFamily v d (ii m) = pgl (fun _ => v ⟨ii m, hcm⟩) :=
        wedgeDomFamily_vertical v d ⟨ii m, hcm⟩
      rw [hvalf]; simp only; rw [scatFun_func_cast heq]; exact pgl_func_mem _ _
    have hvalne : valf m ≠ zeroStream := by
      intro h0
      apply hx_ne m
      rw [hret m, h0, retag_vertical_base n (ii m) hcm]
    -- firstNonzero (valf m) = firstNonzero (x m)
    obtain ⟨l, z, hz⟩ : ∃ l z, valf m = prependZerosOne l z := by
      rcases hval_pgs with h0 | hblk
      · exact absurd (Set.mem_singleton_iff.mp h0) hvalne
      · rw [Set.mem_iUnion] at hblk
        obtain ⟨l, hl⟩ := hblk
        obtain ⟨z, -, hzeq⟩ := hl
        exact ⟨l, z, hzeq.symm⟩
    have hfnval : firstNonzero (valf m) = firstNonzero (x m) := by
      rw [hret m, hz, retag_vertical_block n (ii m) l hcm z, firstNonzero_prependZerosOne,
        firstNonzero_prependZerosOne]
    have hvalf_zero : ∀ k < Mc (ii m) hcm, valf m k = 0 := by
      intro k hk
      apply firstNonzero_zero hvalne
      have : Mc (ii m) hcm ≤ firstNonzero (x m) := by
        have hle : Mc (ii m) hcm
            ≤ (Finset.univ : Finset (Fin n)).sup (fun c : Fin n => Mc c.val c.isLt) :=
          Finset.le_sup (f := fun c : Fin n => Mc c.val c.isLt) (Finset.mem_univ ⟨ii m, hcm⟩)
        omega
      rw [hfnval]; omega
    have hwval : G.func (f m) = τb (ii m) (valf m) := by
      have hh := heqb (ii m) ⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩
      rw [restrict_func_eq G (P (ii m))
        ⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩ (f m).2] at hh
      exact hh
    rw [hwval]
    exact hMcspec (ii m) hcm (valf m) hvalf_zero
      ⟨⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩, rfl⟩
  · -- diagonal
    have hxm : x m = prependZerosOne (ii m - n) (prepend n (valf m)) := by
      rw [hret m, show prepend (ii m) (valf m) = prepend (n + (ii m - n)) (valf m) from by
        congr 1; omega, retag_diagonal]
    have hfndiag : firstNonzero (x m) = ii m - n := by
      rw [hxm, firstNonzero_prependZerosOne]
    have hii_ge : Nd ≤ ii m := by omega
    have hmem : G.func (f m) ∈ Set.range (fun z => (G.restrict (P (ii m))).func z) :=
      ⟨⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩,
        restrict_func_eq G (P (ii m))
          ⟨(f m).val, ⟨(f m).2, partitionIndex_mem P hP_cover (f m)⟩⟩ (f m).2⟩
    exact hNd (ii m) hii_ge hmem

/-- **Continuity of `wTau` on the range of the reduction.** -/
lemma wTau_continuousOn (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun) (y : Baire)
    (P : ℕ → Set ↑G.domain) (hP_clopen : ∀ i, IsClopen (P i))
    (hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (hσb : ∀ i, Continuous (σb i))
    (τb : ℕ → Baire → Baire)
    (hτb : ∀ i, ContinuousOn (τb i) (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z))))
    (heqb : ∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z)))
    (hbase : ∀ i, i < n → τb i zeroStream = y)
    (hconv : ∀ U : Set Baire, IsOpen U → y ∈ U → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      Set.range (fun z => (G.restrict (P i)).func z) ⊆ U)
    (hbase_cont : ∀ i, i < n → Filter.Tendsto (τb i)
      (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) (nhds y)) :
    ContinuousOn (wTau n y τb)
      (Set.range (fun x => (wedge v d).func (wSigma G v d P hP_cover σb x))) := by
  set R := Set.range (fun x => (wedge v d).func (wSigma G v d P hP_cover σb x)) with hR
  have hg0 : ∀ w ∈ R, w = zeroStream → wTau n y τb w = y := by
    rintro w - rfl; exact if_pos rfl
  rw [continuousOn_iff_continuous_restrict]
  apply sufficient_cond_continuity (R.restrict (wTau n y τb)) {w : ↥R | (w : Baire) ≠ zeroStream}
  · exact isOpen_induced (isOpen_ne.preimage continuous_id)
  · have hnz := wTau_continuousOn_nonzero G v d y P hP_clopen hP_disj hP_cover σb hσb τb hτb heqb
    refine (hnz.comp continuous_subtype_val.continuousOn ?_)
    rintro w hw; exact ⟨w.2, hw⟩
  · apply continuousOn_const.congr
    rintro w hw
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hw
    show wTau n y τb w.val = y
    exact hg0 w.val w.2 hw
  · intro x a hxU haU hlim
    have ha0 : (a : Baire) = zeroStream := by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at haU; exact haU
    have hfa : (R.restrict (wTau n y τb)) a = y := by
      show wTau n y τb a.val = y; exact hg0 a.val a.2 ha0
    rw [hfa]
    have hxlim : Filter.Tendsto (fun m => (x m : Baire)) Filter.atTop (nhds zeroStream) := by
      rw [← ha0]; exact (continuous_subtype_val.tendsto a).comp hlim
    exact wTau_seq_tendsto G v d y P hP_clopen hP_disj hP_cover σb hσb τb hτb heqb hbase hconv
      hbase_cont (fun m => (x m).val) (fun m => (x m).2) (fun m => hxU m) hxlim

/-- **Core assembly.**  `G` reduces to `wedge v d` given a clopen partition `(P i)` of `G`
together with, for each slot `i`, a reduction `(σb i, τb i)` of the block `G.restrict (P i)`
into the `i`-th slot `wedgeDomFamily v d i` of the wedge family; vertical slots (`i < n`)
must be "based" (their `τb` fixes the base point to `y`) and the diagonal blocks' images must
converge to `y` (`hconv`). -/
lemma reduces_wedge_of_slot_partition (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire) (P : ℕ → Set ↑G.domain) (hP_clopen : ∀ i, IsClopen (P i))
    (hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hP_cover : ⋃ i, P i = Set.univ)
    (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
    (hσb : ∀ i, Continuous (σb i))
    (τb : ℕ → Baire → Baire)
    (hτb : ∀ i, ContinuousOn (τb i) (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z))))
    (heqb : ∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z)))
    (hbase : ∀ i, i < n → τb i zeroStream = y)
    (hconv : ∀ U : Set Baire, IsOpen U → y ∈ U → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      Set.range (fun z => (G.restrict (P i)).func z) ⊆ U)
    (hbase_cont : ∀ i, i < n → Filter.Tendsto (τb i)
      (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) (nhds y)) :
    Reduces G (wedge v d) :=
  ⟨wSigma G v d P hP_cover σb,
   wSigma_continuous G v d P hP_clopen hP_disj hP_cover σb hσb,
   wTau n y τb,
   wTau_continuousOn G v d y P hP_clopen hP_disj hP_cover σb hσb τb hτb heqb hbase hconv hbase_cont,
   wedge_slot_eq G v d y P hP_cover σb τb heqb hbase⟩

/-! ## Construction of the refined slot partition -/

/-
**Splitting an abstract reduction to `m` copies of `d`.**  If `H` reduces to `m` glued
copies of `d`, then `↑H.domain` has a clopen partition `(P k)` with each block reducing to a
single `d`, and the blocks beyond index `m` are empty.
-/
lemma reduces_replicate_split (H d : ScatFun) (m : ℕ)
    (hred : Reduces H (glList (List.replicate m d))) :
    ∃ P : ℕ → Set ↑H.domain,
      (∀ k, IsClopen (P k)) ∧
      (∀ k l, k ≠ l → Disjoint (P k) (P l)) ∧
      (⋃ k, P k = Set.univ) ∧
      (∀ k, Reduces (H.restrict (P k)) d) ∧
      (∀ k, m ≤ k → P k = ∅) := by
  refine ⟨ fun k => if k < m then { x | ( hred.choose x |> Subtype.val |> fun y => y 0 = k ) } else ∅, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp +decide [ IsClopen ];
  · have h_cont : Continuous (fun x : H.domain => (hred.choose x).val 0) := by
      exact continuous_apply 0 |> Continuous.comp <| continuous_subtype_val.comp hred.choose_spec.1;
    have h_cont : ∀ k, IsClopen {x : H.domain | (hred.choose x).val 0 = k} := by
      intro k; exact (by
      exact ⟨ isClosed_eq h_cont continuous_const, isOpen_iff_mem_nhds.mpr fun x hx => by filter_upwards [ h_cont.continuousAt.eventually ( isOpen_discrete { k } |> IsOpen.mem_nhds <| by aesop ) ] with y hy; aesop ⟩);
    intro k; split_ifs <;> simp_all +decide [ IsClopen ] ;
  · intro k l hkl; split_ifs <;> simp_all +decide [ Set.disjoint_left ] ;
  · ext x; simp [Set.mem_iUnion];
    have h_mem : (hred.choose x).val ∈ (glList (List.replicate m d)).domain := by
      exact hred.choose x |>.2;
    obtain ⟨ k, hk ⟩ := h_mem;
    rcases hk.1 with ⟨ i, rfl ⟩ ; simp +decide  at hk ⊢;
    by_cases hi : i < m <;> simp_all +decide ;
    · obtain ⟨ y, hy, hy' ⟩ := hk; rw [ ← hy' ] ; simp +decide [ prepend ] ; linarith;
    · exact absurd hk.choose_spec.1 ( by simp +decide [ ScatFun.empty ] );
  · intro k;
    by_cases hk : k < m <;> simp +decide [ hk ];
    · -- Define $\sigma'$ and $\tau'$ for the reduction.
      set σ' : {x : H.domain | (hred.choose x).val 0 = k} → d.domain := fun w => ⟨unprepend (hred.choose w).val, by
        convert GluingSet_inverse_short _ _;
        rotate_left;
        exact fun i => ( List.replicate m d ).getD i ScatFun.empty |> ScatFun.domain;
        exact hred.choose w;
        aesop⟩
      generalize_proofs at *;
      set τ' : Baire → Baire := fun b => hred.choose_spec.2.choose (prepend k b);
      have h_cont : Continuous σ' ∧ ContinuousOn τ' (Set.range (fun z => d.func (σ' z))) := by
        refine ⟨ ?_, ?_ ⟩;
        · refine' Continuous.subtype_mk _ _;
          exact continuous_unprepend.comp ( continuous_subtype_val.comp ( hred.choose_spec.1.comp continuous_subtype_val ) );
        · have h_cont : ContinuousOn (fun z => hred.choose_spec.2.choose z) (Set.range (fun z => (glList (List.replicate m d)).func (hred.choose z))) := by
            exact hred.choose_spec.2.choose_spec.1.mono ( Set.range_subset_iff.mpr fun x => Set.mem_range_self _ )
          generalize_proofs at *;
          refine h_cont.comp ( Continuous.continuousOn ?_ ) ?_;
          · exact continuous_prepend k;
          · simp +decide [ glList ];
            grind [gl_func_apply];
      have h_eq : ∀ w : {x : H.domain | (hred.choose x).val 0 = k}, H.func w.val = τ' (d.func (σ' w)) := by
        intro w
        have h_eq : (glList (List.replicate m d)).func (hred.choose w) = prepend k (d.func (σ' w)) := by
          convert gl_func_prepend _ _ _ _ using 1;
          rotate_left;
          rotate_left;
          exact fun i => List.getD ( List.replicate m d ) i empty;
          exact k;
          exact ⟨ unprepend ( hred.choose w ).val, by
            grind ⟩
          all_goals generalize_proofs at *;
          · exact mem_gluingSet_prepend ‹_›;
          · convert rfl using 2;
            ext; simp [prepend, unprepend];
            grind;
          · grind +splitImp;
        grind;
      have h_cont : Reduces (H.restrict {x : H.domain | (hred.choose x).val 0 = k}) d := by
        have h_cont : ContinuouslyReduces (H.func ∘ (Subtype.val : {x : H.domain | (hred.choose x).val 0 = k} → H.domain)) d.func := by
          use σ', h_cont.1, τ', h_cont.2, h_eq
        convert h_cont.comp_homeomorph_left ( H.restrictEquiv { x : H.domain | ( hred.choose x ).val 0 = k } ) using 1;
      exact h_cont;
    · refine ⟨ ?_, ?_, ?_, ?_ ⟩;
      exact fun x => False.elim <| x.2.2;
      exact continuous_of_const fun x y => by tauto;
      exact fun _ => 0;
      exact ⟨ continuousOn_const, fun x => False.elim <| x.2.2 ⟩;
  · exact fun k hk₁ hk₂ => False.elim <| hk₂.not_ge hk₁

/-
**Transporting a clopen partition across `restrict`.**  A clopen partition `(P k)` of the
re-realized domain `↑(G.restrict S).domain` (with `S` clopen) transports to a clopen partition
`(Q k)` of `S` inside `↑G.domain`, with each `G.restrict (Q k)` reducing to the corresponding
realized block, and empty blocks staying empty.
-/
lemma clopen_partition_restrict_transport (G : ScatFun) (S : Set ↑G.domain) (hS : IsClopen S)
    (P : ℕ → Set ↑(G.restrict S).domain) (hP_clopen : ∀ k, IsClopen (P k))
    (hP_disj : ∀ k l, k ≠ l → Disjoint (P k) (P l)) (hP_cover : ⋃ k, P k = Set.univ) :
    ∃ Q : ℕ → Set ↑G.domain,
      (∀ k, Q k ⊆ S) ∧ (∀ k, IsClopen (Q k)) ∧
      (∀ k l, k ≠ l → Disjoint (Q k) (Q l)) ∧ (⋃ k, Q k = S) ∧
      (∀ k, Reduces (G.restrict (Q k)) ((G.restrict S).restrict (P k))) ∧
      (∀ k, P k = ∅ → Q k = ∅) := by
  refine ⟨ fun k => { w : G.domain | ∃ h : w ∈ S, ⟨ w.val, ⟨ w.2, h ⟩ ⟩ ∈ P k }, ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact fun k w hw => hw.choose;
  · intro k;
    constructor;
    · refine isClosed_of_closure_subset ?_;
      intro w hw;
      rw [ mem_closure_iff_nhds ] at hw;
      contrapose! hw;
      by_cases hwS : w ∈ S <;> simp_all +decide [ IsClopen ];
      · have := hP_clopen k |>.1.isOpen_compl.mem_nhds hw;
        rw [ mem_nhds_subtype ] at this;
        obtain ⟨ u, hu, hu' ⟩ := this; use Subtype.val ⁻¹' u; simp_all +decide [ Set.ext_iff ] ;
        exact ⟨ by exact ContinuousAt.preimage_mem_nhds ( continuous_subtype_val.continuousAt ) hu, fun a b c d => hu' <| by aesop ⟩;
      · exact ⟨ Sᶜ, hS.1.isOpen_compl.mem_nhds hwS, by ext; aesop ⟩;
    · refine isOpen_iff_forall_mem_open.mpr ?_;
      intro x hx
      obtain ⟨hxS, hxP⟩ := hx
      obtain ⟨U, hU_open, hxU, hUP⟩ : ∃ U : Set ↑(G.restrict S).domain, IsOpen U ∧ ⟨x.val, ⟨x.2, hxS⟩⟩ ∈ U ∧ U ⊆ P k := by
        exact ⟨ _, hP_clopen k |>.2, hxP, Set.Subset.refl _ ⟩;
      refine ⟨ { w : G.domain | ∃ h : w ∈ S, ⟨ w.val, ⟨ w.2, h ⟩ ⟩ ∈ U }, ?_, ?_, ?_ ⟩;
      · exact fun w hw => ⟨ hw.choose, hUP hw.choose_spec ⟩;
      · obtain ⟨ V, hV_open, hVU ⟩ := hU_open;
        convert hS.2.inter ( hV_open.preimage ( show Continuous ( fun w : G.domain => w.val ) from continuous_subtype_val ) ) using 1 ; ext ; aesop;
      · exact ⟨ hxS, hxU ⟩;
  · intro k l hkl; specialize hP_disj k l hkl; rw [ Set.disjoint_left ] at *; aesop;
  · simp_all +decide [ Set.ext_iff ];
    intro a ha; specialize hP_cover a; aesop;
  · refine ⟨ fun k => ?_, fun k hk => ?_ ⟩;
    · refine ⟨ ?_, ?_, ?_ ⟩;
      refine fun x => ⟨ x.val, ?_ ⟩;
      exact ⟨ ⟨ x.2.1, x.2.2.choose ⟩, x.2.2.choose_spec ⟩;
      · fun_prop;
      · refine ⟨ id, continuousOn_id, ?_ ⟩ ; aesop;
    · grind +splitIndPred

/-- **Splitting a diagonal block.**  A clopen block `S` of `G` that reduces to `m` glued
copies of `d` refines into a clopen partition `(Q k)` of `S` (as subsets of `↑G.domain`),
where each piece reduces to a single `d`, and pieces beyond index `m` are empty. -/
lemma diag_block_split (G d : ScatFun) (S : Set ↑G.domain) (hS : IsClopen S) (m : ℕ)
    (hred : Reduces (G.restrict S) (glList (List.replicate m d))) :
    ∃ Q : ℕ → Set ↑G.domain,
      (∀ k, Q k ⊆ S) ∧ (∀ k, IsClopen (Q k)) ∧
      (∀ k l, k ≠ l → Disjoint (Q k) (Q l)) ∧
      ((⋃ k, Q k) = S) ∧
      (∀ k, Reduces (G.restrict (Q k)) d) ∧
      (∀ k, m ≤ k → Q k = ∅) := by
  obtain ⟨P, hP_clopen, hP_disj, hP_cover, hP_red, hP_empty⟩ :=
    reduces_replicate_split (G.restrict S) d m hred
  obtain ⟨Q, hQ_sub, hQ_clopen, hQ_disj, hQ_cover, hQ_red, hQ_empty⟩ :=
    clopen_partition_restrict_transport G S hS P hP_clopen hP_disj hP_cover
  refine ⟨Q, hQ_sub, hQ_clopen, hQ_disj, hQ_cover, ?_, ?_⟩
  · exact fun k => (hQ_red k).trans (hP_red k)
  · exact fun k hk => hQ_empty k (hP_empty k hk)

/-
**Repacking the diagonal region.**  Given a clopen partition `(B t)` whose blocks each
reduce to finitely many copies of `d` and whose images converge to `y`, there is a clopen
partition `(Q s)` of the same region into single-`d` slots whose images still converge to
`y` (deep slots come from deep blocks).
-/
set_option maxHeartbeats 600000 in
lemma diag_region_partition (G d : ScatFun) (y : Baire) (B : ℕ → Set ↑G.domain)
    (hB_clopen : ∀ t, IsClopen (B t))
    (hB_disj : ∀ s t, s ≠ t → Disjoint (B s) (B t))
    (hB_red : ∀ t, ∃ m, Reduces (G.restrict (B t)) (glList (List.replicate m d)))
    (hB_conv : SetsConvergeTo (fun t => Set.range (G.restrict (B t)).func) y) :
    ∃ Q : ℕ → Set ↑G.domain,
      (∀ s, IsClopen (Q s)) ∧
      (∀ s t, s ≠ t → Disjoint (Q s) (Q t)) ∧
      ((⋃ s, Q s) = ⋃ t, B t) ∧
      (∀ s, Q s ⊆ ⋃ t, B t) ∧
      (∀ s, Reduces (G.restrict (Q s)) d) ∧
      SetsConvergeTo (fun s => Set.range (G.restrict (Q s)).func) y := by
  obtain ⟨Qt, hQt⟩ : ∃ Qt : ℕ → ℕ → Set ↑G.domain, (∀ t k, Qt t k ⊆ B t) ∧ (∀ t k, IsClopen (Qt t k)) ∧ (∀ t k l, k ≠ l → Disjoint (Qt t k) (Qt t l)) ∧ (∀ t, ⋃ k, Qt t k = B t) ∧ (∀ t k, Reduces (G.restrict (Qt t k)) d) ∧ (∀ t k, (hB_red t).choose ≤ k → Qt t k = ∅) := by
    have := fun t => diag_block_split G d (B t) (hB_clopen t) (hB_red t).choose (hB_red t).choose_spec;
    exact ⟨ fun t => Classical.choose ( this t ), fun t k => Classical.choose_spec ( this t ) |>.1 k, fun t k => Classical.choose_spec ( this t ) |>.2.1 k, fun t k l hkl => Classical.choose_spec ( this t ) |>.2.2.1 k l hkl, fun t => Classical.choose_spec ( this t ) |>.2.2.2.1, fun t k => Classical.choose_spec ( this t ) |>.2.2.2.2.1 k, fun t k hk => Classical.choose_spec ( this t ) |>.2.2.2.2.2 k hk ⟩;
  refine ⟨ fun s => if h : ∃ t, ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) ≤ s ∧ s < ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) + ( hB_red t ).choose then Qt h.choose ( s - ( Finset.range h.choose ).sum ( fun t => ( hB_red t ).choose ) ) else ∅, ?_, ?_, ?_, ?_, ?_ ⟩;
  · intro s; by_cases hs : ∃ t, ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) ≤ s ∧ s < ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) + ( hB_red t ).choose <;> simp +decide [ hs, hQt.2.1 ] ;
    exact isClopen_empty;
  · intro s t hst; by_cases hs : ∃ t_1, ∑ t ∈ Finset.range t_1, ( hB_red t ).choose ≤ s ∧ s < ∑ t ∈ Finset.range t_1, ( hB_red t ).choose + ( hB_red t_1 ).choose <;> by_cases ht : ∃ t_1, ∑ t ∈ Finset.range t_1, ( hB_red t ).choose ≤ t ∧ t < ∑ t ∈ Finset.range t_1, ( hB_red t ).choose + ( hB_red t_1 ).choose <;> simp +decide [ hs, ht ] ;
    by_cases h : hs.choose = ht.choose;
    · grind +qlia;
    · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => Set.disjoint_left.mp ( hB_disj _ _ h ) ( hQt.1 _ _ hx₁ ) ( hQt.1 _ _ hx₂ );
  · ext x; simp [Set.mem_iUnion];
    constructor <;> rintro ⟨ t, ht ⟩;
    · split_ifs at ht <;> [ exact ⟨ _, hQt.1 _ _ ht ⟩ ; exact False.elim <| by simp_all +decide ];
    · obtain ⟨ k, hk ⟩ := Set.mem_iUnion.mp ( hQt.2.2.2.1 t ▸ ht );
      use (Finset.range t).sum (fun t => (hB_red t).choose) + k;
      split_ifs with h;
      · by_cases h_cases : h.choose = t;
        · simp_all +decide ;
        · cases lt_or_gt_of_ne h_cases <;> simp_all +decide;
          · have h_sum_le : ∑ t ∈ Finset.range t, (hB_red t).choose ≥ ∑ t ∈ Finset.range (h.choose + 1), (hB_red t).choose := by
              exact Finset.sum_le_sum_of_subset ( Finset.range_mono ( by linarith ) );
            simp_all +decide [ Finset.sum_range_succ ];
            grind +splitImp;
          · have h_sum_ge : ∑ t ∈ Finset.range h.choose, (hB_red t).choose ≥ ∑ t ∈ Finset.range (t + 1), (hB_red t).choose := by
              exact Finset.sum_le_sum_of_subset ( Finset.range_mono ( by linarith ) );
            simp_all +decide [ Finset.sum_range_succ ];
            grind;
      · grind;
  · intro s; by_cases h : ∃ t, ∑ t ∈ Finset.range t, ( hB_red t ).choose ≤ s ∧ s < ∑ t ∈ Finset.range t, ( hB_red t ).choose + ( hB_red t ).choose <;> simp +decide [ h ] ;
    exact Set.Subset.trans ( hQt.1 _ _ ) ( Set.subset_iUnion _ _ );
  · refine ⟨ ?_, ?_ ⟩;
    · intro s;
      by_cases h : ∃ t, ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) ≤ s ∧ s < ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) + ( hB_red t ).choose <;> simp +decide [ h ];
      · exact hQt.2.2.2.2.1 _ _;
      · unfold Reduces; simp +decide [ ScatFun.restrict ] ;
        grind [ContinuouslyReduces.comp_homeomorph_left, continuouslyReduces_of_empty];
    · intro U hU hyU; rcases hB_conv U hU hyU with ⟨ N, hN ⟩ ; use ( Finset.range N ).sum ( fun t => ( hB_red t ).choose ) ; intro s hs; by_cases hs' : ∃ t, ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) ≤ s ∧ s < ( Finset.range t ).sum ( fun t => ( hB_red t ).choose ) + ( hB_red t ).choose <;> simp_all +decide ;
      · have h_t_ge_N : N ≤ hs'.choose := by
          contrapose! hs;
          refine lt_of_lt_of_le hs'.choose_spec.2 ?_;
          rw [ ← Finset.sum_range_succ ];
          exact Finset.sum_le_sum_of_subset ( Finset.range_mono ( Nat.succ_le_of_lt hs ) );
        convert hN _ h_t_ge_N |> Set.Subset.trans _ using 1;
        simp_all +decide [ Set.range_subset_iff ];
        intro a ha; use a; simp_all +decide [ ScatFun.restrict ] ;
        split_ifs ; simp_all +decide [ ScatFun.restrictEquiv ];
        · exact ⟨ ha.1, hQt.1 _ _ ha.2 ⟩;
        · exact False.elim <| ‹¬∃ t, ∑ t ∈ Finset.range t, _ ≤ s ∧ s < ∑ t ∈ Finset.range t, _ + _› hs';
      · split_ifs <;> simp_all +decide [ Set.subset_def ];
        · grind;
        · split_ifs <;> simp_all +decide [ Set.ext_iff ];
          · grind;
          · simp +decide [ ScatFun.restrict ]

/-
From the hypotheses of `wedge_upper_bound`, build the refined clopen partition `(P i)`
into slots of the wedge family, with block reductions and the based / convergence
conditions.
-/
set_option maxHeartbeats 1400000 in
lemma wedge_refined_partition (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire) (A : ℕ → Set ↑G.domain) (h_disj : G.IsDisjointUnion A)
    (h_vertical : ∀ (i : ℕ) (hi : i < n) (j : ℕ),
      ∃ m, Reduces (G.rayOn y (A i) j) (glList (List.replicate m (v ⟨i, hi⟩))))
    (h_diag : ∀ i, n ≤ i → ∃ m, Reduces (G.restrict (A i)) (glList (List.replicate m d)))
    (h_ranges : SetsConvergeTo (fun i => Set.range (G.restrict (A i)).func) y) :
    ∃ (P : ℕ → Set ↑G.domain)
      (σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain)
      (τb : ℕ → Baire → Baire),
      (∀ i, IsClopen (P i)) ∧ (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i = Set.univ) ∧ (∀ i, Continuous (σb i)) ∧
      (∀ i, ContinuousOn (τb i)
        (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) ∧
      (∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z))) ∧
      (∀ i, i < n → τb i zeroStream = y) ∧
      (∀ U : Set Baire, IsOpen U → y ∈ U → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
        Set.range (fun z => (G.restrict (P i)).func z) ⊆ U) ∧
      (∀ i, i < n → Filter.Tendsto (τb i)
        (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z))))
        (nhds y)) := by
  have := h_disj.2.2;
  -- Apply the diagonal region partition lemma to obtain the partition Qd.
  obtain ⟨Qd, hQd_clopen, hQd_disj, hQd_cover, hQd_red, hQd_conv⟩ := diag_region_partition G d y (fun t => A (n + t)) (fun t => h_disj.1 (n + t)) (fun s t hst => h_disj.2.1 (n + s) (n + t) (by simpa using hst)) (fun t => h_diag (n + t) (by linarith)) (by
  exact fun U hU hy => by rcases h_ranges U hU hy with ⟨ N, hN ⟩ ; exact ⟨ N, fun t ht => hN _ ( by linarith ) ⟩ ;);
  -- Define the partition P as the union of A i for i < n and Qd (i - n) for i ≥ n.
  set P : ℕ → Set ↑G.domain := fun i => if i < n then A i else Qd (i - n);
  -- Define the functions σb and τb for each i.
  obtain ⟨σb, τb, hσb, hτb⟩ : ∃ σb : ∀ i, ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain, ∃ τb : ℕ → Baire → Baire, (∀ i, Continuous (σb i)) ∧ (∀ i, ContinuousOn (τb i) (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) ∧ (∀ i z, (G.restrict (P i)).func z = τb i ((wedgeDomFamily v d i).func (σb i z))) ∧ (∀ i, i < n → τb i zeroStream = y) ∧ (∀ i, i < n → Filter.Tendsto (τb i) (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb i z)))) (nhds y)) := by
    have h_vertical_block : ∀ i (hi : i < n), ∃ σb : ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain, ∃ τb : Baire → Baire, Continuous σb ∧ ContinuousOn τb (Set.range (fun z => (wedgeDomFamily v d i).func (σb z))) ∧ (∀ z, (G.restrict (P i)).func z = τb ((wedgeDomFamily v d i).func (σb z))) ∧ τb zeroStream = y ∧ Filter.Tendsto τb (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v d i).func (σb z)))) (nhds y) := by
      intro i hi;
      convert vertical_block_reduces_pgl_based G v y (P i) i hi _ using 1;
      · rw [ wedgeDomFamily_vertical v d ⟨ i, hi ⟩ ];
      · aesop;
    have h_diag_block : ∀ i (hi : ¬i < n), ∃ σb : ↑(G.restrict (P i)).domain → ↑(wedgeDomFamily v d i).domain, ∃ τb : Baire → Baire, Continuous σb ∧ ContinuousOn τb (Set.range (fun z => (wedgeDomFamily v d i).func (σb z))) ∧ (∀ z, (G.restrict (P i)).func z = τb ((wedgeDomFamily v d i).func (σb z))) := by
      intro i hi
      have h_red : Reduces (G.restrict (P i)) d := by
        grind;
      obtain ⟨ σb, τb, hσb, hτb ⟩ := h_red;
      use fun z => ⟨σb z, by
        rw [ wedgeDomFamily_diag ];
        · exact σb z |>.2;
        · exact hi⟩, fun z => hσb z
      generalize_proofs at *;
      refine ⟨ ?_, ?_, ?_ ⟩;
      · exact Continuous.subtype_mk ( continuous_subtype_val.comp τb ) _;
      · convert hτb.1 using 1;
        ext; simp;
        grind [wedgeDomFamily_diag];
      · grind [wedgeDomFamily_diag];
    choose! σb τb hσb hτb hσbτb using h_vertical_block;
    choose! σb' τb' hσb' hτb' hσbτb' using h_diag_block;
    use fun i => if hi : i < n then σb i hi else σb' i hi, fun i => if hi : i < n then τb i else τb' i;
    refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    · intro i; split_ifs <;> [ exact hσb i ‹_›; exact hσb' i ‹_› ] ;
    · intro i; by_cases hi : i < n <;> simp +decide [ hi, hτb, hτb' ] ;
    · grind;
    · exact fun i hi => by simpa [ hi ] using hσbτb i hi |>.2.1;
    · exact fun i hi => by simpa [ hi ] using hσbτb i hi |>.2.2;
  refine ⟨ P, σb, τb, ?_, ?_, ?_, hσb, hτb.1, hτb.2.1, hτb.2.2.1, ?_, hτb.2.2.2 ⟩;
  · intro i; by_cases hi : i < n <;> simp +decide [ *, IsClopen ] ;
    · exact h_disj.1 i |> fun h => by aesop;
    · simp +zetaDelta at *;
      rw [ if_neg ( not_lt_of_ge hi ) ] ; exact ⟨ hQd_clopen _ |>.1, hQd_clopen _ |>.2 ⟩ ;
  · intro i j hij; by_cases hi : i < n <;> by_cases hj : j < n <;> simp +decide [ *, Set.disjoint_left ] ;
    · simp +zetaDelta at *;
      simp +decide only [hi, ↓reduceIte, hj];
      exact fun a ha ha' ha'' => Set.disjoint_left.mp ( h_disj.2.1 i j hij ) ha' ha'';
    · simp +zetaDelta at *;
      intro a ha ha' ha''; split_ifs at ha' ha'' ; simp_all +decide [ Set.disjoint_left ] ;
      · linarith;
      · have := hQd_red ( j - n ) ha''; simp_all +decide [ Set.ext_iff ] ;
        obtain ⟨ k, hk ⟩ := this; have := h_disj.2.1 i ( n + k ) ( by linarith ) ; simp_all +decide [ Set.disjoint_left ] ;
    · simp +zetaDelta at *;
      split_ifs <;> simp_all +decide [ Set.disjoint_left ];
      · linarith;
      · intro a ha ha' ha''; specialize hQd_red ( i - n ) ha'; simp_all +decide ;
        obtain ⟨ k, hk ⟩ := hQd_red; have := h_disj.2.1 j ( n + k ) ( by linarith ) ; simp_all +decide [ Set.disjoint_left ] ;
    · simp +zetaDelta at *;
      split_ifs <;> simp_all +decide [ Set.disjoint_left ];
      · linarith;
      · linarith;
      · linarith;
      · exact hQd_disj _ _ ( by omega );
  · ext x; simp [P];
    by_cases hx : x ∈ ⋃ t, A (n + t);
    · obtain ⟨ s, hs ⟩ := Set.mem_iUnion.mp ( hQd_cover.symm ▸ hx ) ; use n + s; simp +decide [ hs ] ;
    · obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp ( this.symm ▸ Set.mem_univ x );
      exact ⟨ i, by rw [ if_pos ( Nat.lt_of_not_ge fun hi' => hx <| Set.mem_iUnion.mpr ⟨ i - n, by simpa [ Nat.add_sub_of_le hi' ] using hi ⟩ ) ] ; exact hi ⟩;
  · intro U hU hyU
    obtain ⟨N, hN⟩ := h_ranges U hU hyU
    obtain ⟨N', hN'⟩ := hQd_conv.2 U hU hyU
    use n + N' + N
    intro i hi
    by_cases hi' : i < n + N' + N
    generalize_proofs at *; (
    linarith);
    grind

/-! ## Proposition 5.4 (`Wedgeasupperbound`) -/

theorem wedge_upper_bound (G : ScatFun) (v : Fin n → ScatFun) (d : ScatFun)
    (y : Baire) (A : ℕ → Set ↑G.domain) (h_disj : G.IsDisjointUnion A)
    -- 1. rays of the vertical blocks reduce to finitely many copies of `v i`
    (h_vertical : ∀ (i : ℕ) (hi : i < n) (j : ℕ),
      ∃ m, Reduces (G.rayOn y (A i) j) (glList (List.replicate m (v ⟨i, hi⟩))))
    -- 2. each diagonal block reduces to finitely many copies of `d`
    (h_diag : ∀ i, n ≤ i → ∃ m, Reduces (G.restrict (A i)) (glList (List.replicate m d)))
    -- 3. the images `G(A i)` converge to `y`
    (h_ranges : SetsConvergeTo (fun i => Set.range (G.restrict (A i)).func) y) :
    Reduces G (wedge v d) := by
  obtain ⟨P, σb, τb, hP_clopen, hP_disj, hP_cover, hσb, hτb, heqb, hbase, hconv, hbase_cont⟩ :=
    wedge_refined_partition G v d y A h_disj h_vertical h_diag h_ranges
  exact reduces_wedge_of_slot_partition G v d y P hP_clopen hP_disj hP_cover σb hσb τb
    hτb heqb hbase hconv hbase_cont

end ScatFun
