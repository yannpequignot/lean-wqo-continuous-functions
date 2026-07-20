import WqoContinuousFunctions.ScatFun.Operations.Gl
import WqoContinuousFunctions.ScatFun.Operations.Pgl
import WqoContinuousFunctions.ContinuousReducibility.Gluing.UpperBound

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Reduction lemmas for the plain gluing `gl` (and `gl ↪ pgl`)

Split out of the former monolithic `ScatFun/Operations.lean`.  These are the reduction
combinators for the plain gluing `gl` (`ScatFun/Gl.lean`), plus the deep embedding of a plain
gluing into a pointed gluing `pgl` (`ScatFun/Pgl.lean`).

* `ScatFun.gl_reduces_of_pointwise` — blockwise `≤` lifts to `gl F ≤ gl G`
* `ScatFun.gl_reindex` / `gl_reduces_of_blockEmbed` — reindexing / block-embedding criteria
* `ScatFun.gl_reduces_pgl_direct` — `gl C ≤ pgl D` under an injective block matching
-/

namespace ScatFun

/-- **Pasting the per-block `σ`-maps of a gluing reduction.**  Given continuous
block maps `k i : A i → A' i`, there is a continuous map on `GluingSet A` sending
the block-`i` point `(i)⌐a` to `(i)⌐(k i a)`.  (Here it is realised directly as the
gluing of the block maps, whose continuity is `gluingFunVal_preserves_continuity`.) -/
lemma gluedSigma_continuous {A A' : ℕ → Set Baire}
    (k : ∀ i, ↑(A i) → ↑(A' i)) (hk : ∀ i, Continuous (k i)) :
    ∃ s : ↑(GluingSet A) → ↑(GluingSet A'), Continuous s ∧
      ∀ (i : ℕ) (a : ↑(A i)),
        s ⟨prepend i a.val, mem_gluingSet_prepend a.prop⟩
          = ⟨prepend i (k i a).val, mem_gluingSet_prepend (k i a).prop⟩ := by
  refine ⟨fun x => ⟨GluingFunVal A A' k x, ?_⟩, ?_, ?_⟩
  · unfold GluingFunVal; grind [mem_gluingSet_prepend]
  · exact (gluingFunVal_preserves_continuity A A' k hk).subtype_mk _
  · intro i a; unfold GluingFunVal; aesop

/-- **Pasting the per-block `τ`-maps of a gluing reduction.**  If, on each block
`S ∩ {z | z 0 = i}`, the map `z ↦ (i)⌐(k i (unprepend z))` is continuous, then the
blockwise map `y ↦ (y 0)⌐(k (y 0) (unprepend y))` is continuous on `S`.  (Proved by
`continuousOn_piecewise_clopen`.) -/
lemma gluedTau_continuousOn (S : Set Baire) (k : ℕ → Baire → Baire)
    (hk : ∀ i, ContinuousOn (fun z => prepend i (k i (unprepend z))) (S ∩ {z | z 0 = i})) :
    ContinuousOn (fun y => prepend (y 0) (k (y 0) (unprepend y))) S := by
  apply continuousOn_piecewise_clopen
  rotate_left
  rotate_left
  rotate_left
  · convert hk using 1
  · exact fun z hz => ⟨_, rfl⟩
  · aesop
  · exact fun z hz => ⟨z 0, rfl⟩
  · exact fun i => isClopen_preimage_zero i
  · aesop

/-- **Pointwise reduction of plain gluings.**  If block `i` of `F` continuously
reduces to block `i` of `G` for every `i`, then `gl F` reduces to `gl G`.

The reduction keeps the block index fixed: on the (relatively clopen) block
`{x | x.val 0 = i}`, the glued map is `prepend i ∘ (F i).func ∘ unprepend`, which
reduces blockwise to `(G i).func` via the given reductions, pasted together with
`continuous_pasting_on_clopen` / `continuousOn_piecewise_clopen`.
-/
theorem gl_reduces_of_pointwise (F G : ℕ → ScatFun)
    (hred : ∀ i, Reduces (F i) (G i)) :
    Reduces (gl F) (gl G) := by
  choose σ hσ τ hτ h_eq using hred;
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact fun x => ⟨ prepend ( x.val 0 ) ( σ ( x.val 0 ) ⟨ unprepend x.val, by
    have := GluingSet_inverse_short ( fun i => ( F i ).domain ) x;
    grind ⟩ ).val, by
    all_goals generalize_proofs at *;
    exact mem_gluingSet_prepend ( σ _ ⟨ _, ‹_› ⟩ ).2 ⟩
  all_goals generalize_proofs at *;
  · convert ScatFun.gluedSigma_continuous ( fun i => σ i ) hσ |> Classical.choose_spec |> And.left using 1;
    grind [prepend_unprepend];
  · refine ⟨ fun y => prepend ( y 0 ) ( τ ( y 0 ) ( unprepend y ) ), ?_, ?_ ⟩;
    · refine gluedTau_continuousOn ?_ ?_ ?_;
      intro i;
      refine' ContinuousOn.comp ( continuous_prepend i |> Continuous.continuousOn ) _ _;
      exact Set.range ( τ i );
      · refine ContinuousOn.comp ( hτ i ) ?_ ?_;
        · exact Continuous.continuousOn ( continuous_unprepend );
        · intro z hz;
          obtain ⟨ x, rfl ⟩ := hz.1;
          have := x.2;
          obtain ⟨ j, hj ⟩ := this;
          unfold prepend at *; aesop;
      · exact fun x hx => Set.mem_range_self _;
    · intro x
      simp only [gl, GluingFunVal_prepend];
      unfold GluingFunVal glBlock; aesop;

/-- **Reindexing a plain gluing by an injective map.**  For an injective
`e : ℕ → ℕ`, gluing the reindexed family `fun i => G (e i)` reduces to gluing
`G`: block `i` (first coordinate `i`) is relabelled to block `e i` (first
coordinate `e i`), keeping the payload; the inverse `τ` uses `Function.invFun e`,
which is a left inverse of `e` by injectivity. -/
theorem gl_reindex (G : ℕ → ScatFun) (e : ℕ → ℕ) (he : Function.Injective e) :
    Reduces (gl (fun i => G (e i))) (gl G) := by
  refine ⟨fun x => ⟨prepend (e (x.val 0)) (unprepend x.val), mem_gluingSet_prepend ?_⟩,
    ?_, fun y => prepend (Function.invFun e (y 0)) (unprepend y), ?_, ?_⟩
  · obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short (fun i => (G (e i)).domain) x
    rw [hi]; exact hmem
  · refine Continuous.subtype_mk ?_ _
    have hidx : Continuous (fun x : ↑(GluingSet (fun i => (G (e i)).domain)) => e (x.val 0)) :=
      continuous_of_discreteTopology.comp ((continuous_apply 0).comp continuous_subtype_val)
    refine continuous_pi fun i => ?_
    rcases i with _ | i
    · simpa [prepend] using hidx
    · simpa [prepend, unprepend] using (continuous_apply (i + 1)).comp continuous_subtype_val
  · refine Continuous.continuousOn ?_
    have hinv : Continuous (Function.invFun e) := continuous_of_discreteTopology
    have hidx : Continuous (fun y : Baire => Function.invFun e (y 0)) :=
      hinv.comp (continuous_apply 0)
    refine continuous_pi fun i => ?_
    rcases i with _ | i
    · simpa [prepend] using hidx
    · simpa [prepend, unprepend] using continuous_apply (i + 1)
  · intro x
    obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short (fun i => (G (e i)).domain) x
    have hmem' : unprepend x.val ∈ (G (e i)).domain := hmem
    have hxval : x.val = prepend i (unprepend x.val) := by rw [← hi, prepend_unprepend]
    have hlhs : GluingFunVal (fun i => (G (e i)).domain) (fun _ => Set.univ)
        (glBlock (fun i => G (e i))) x = prepend i ((G (e i)).func ⟨unprepend x.val, hmem'⟩) := by
      conv_lhs => rw [show x = ⟨prepend i (unprepend x.val), by rw [← hxval]; exact x.2⟩
        from Subtype.ext hxval]
      rw [GluingFunVal_prepend (fun i => (G (e i)).domain) (fun _ => Set.univ)
        (glBlock (fun i => G (e i))) i ⟨unprepend x.val, hmem'⟩]
      rfl
    have hsig : ∀ (h : prepend (e i) (unprepend x.val) ∈
        GluingSet (fun j => (G j).domain)),
        (gl G).func ⟨prepend (e i) (unprepend x.val), h⟩
          = prepend (e i) ((G (e i)).func ⟨unprepend x.val, hmem'⟩) := by
      intro h
      rw [show (⟨prepend (e i) (unprepend x.val), h⟩ : ↑(GluingSet (fun j => (G j).domain)))
        = ⟨prepend (e i) (⟨unprepend x.val, hmem'⟩ : ↑((G (e i)).domain)).val,
          mem_gluingSet_prepend hmem'⟩ from rfl]
      exact GluingFunVal_prepend (fun j => (G j).domain) (fun _ => Set.univ)
        (glBlock G) (e i) ⟨unprepend x.val, hmem'⟩ (mem_gluingSet_prepend hmem')
    show GluingFunVal _ _ (glBlock (fun i => G (e i))) x
      = prepend (Function.invFun e (((gl G).func _) 0)) (unprepend ((gl G).func _))
    simp only [hi]
    rw [hlhs, hsig, show (prepend (e i) ((G (e i)).func ⟨unprepend x.val, hmem'⟩)) 0 = e i from
      by simp [prepend], Function.leftInverse_invFun he i, unprepend_prepend]

/-- **General block-embedding criterion for plain gluings.**

If there is an injective reindexing `e : ℕ → ℕ` such that block `i` of `F`
continuously reduces to block `e i` of `G`, then the plain gluing `gl F`
continuously reduces to `gl G`.

This is the single reusable geometric input behind `Gl_mono`. -/
theorem gl_reduces_of_blockEmbed (F G : ℕ → ScatFun) (e : ℕ → ℕ)
    (he : Function.Injective e) (hred : ∀ i, Reduces (F i) (G (e i))) :
    Reduces (gl F) (gl G) :=
  (gl_reduces_of_pointwise F (fun i => G (e i)) hred).trans (gl_reindex G e he)

/-
**Joint continuity of the inverse block map** `(d, y) ↦ (invFun e d)⌢(stripZerosOne d y)`.
Again the depth `d` lives in discrete `ℕ`.
-/
lemma continuous_invFunPrependStrip_uncurry (e : ℕ → ℕ) :
    Continuous (fun p : ℕ × Baire =>
      prepend (Function.invFun e p.1) (stripZerosOne p.1 p.2)) := by
  refine continuous_iff_continuousAt.mpr ?_;
  intro p;
  refine ContinuousAt.congr (f := fun q => prepend ( invFun e p.1 ) ( stripZerosOne p.1 q.2 )) ?_ ?_;
  · refine' Continuous.continuousAt _;
    exact continuous_prepend ( invFun e p.1 ) |> Continuous.comp <| continuous_stripZerosOne ( p.1 ) |> Continuous.comp <| continuous_snd;
  · filter_upwards [ IsOpen.mem_nhds ( isOpen_discrete { p.1 } |> IsOpen.preimage continuous_fst ) ( Set.mem_singleton p.1 ) ] with q hq using by aesop;

/-
**A plain gluing reduces, deeply, into a pointed gluing.**

Assume an injective reindexing `e` such that each block `C k` is *equal* to block
`D (e k)` or has empty domain.  Then `gl C` reduces to `pgl D`, sending the block-`k`
point `(k)⌢w` of `gl C` to the pointed-gluing block point `(0)^{e k}(1)·w`.  Because
the block maps are identities, the reduction is `σ x = (0)^{e (x.val 0)}(1)·(unprepend x)`
and `τ y = (invFun e (firstNonzero y))⌢(stripZerosOne (firstNonzero y) y)`.
We expose the canonical `σ` together with two pieces of geometric control used by the
`pgl`-lower-bound machinery: every value `σ x` starts with `e (x.val 0)` zeros
(`deep`), and its `pgl D`-image carries a `1` at coordinate `e (x.val 0)` (so the image
stays away from the base point `0^ω`).
-/
lemma gl_reduces_pgl_direct (C D : ℕ → ScatFun) (e : ℕ → ℕ) (he : Function.Injective e)
    (hCD : ∀ k, C k = D (e k) ∨ IsEmpty ↑(C k).domain) :
    ∃ (σ : ↑(gl C).domain → ↑(pgl D).domain) (τ : Baire → Baire),
      Continuous σ ∧
      (∀ x, (gl C).func x = τ ((pgl D).func (σ x))) ∧
      ContinuousOn τ (Set.range (fun x => (pgl D).func (σ x))) ∧
      (∀ x (l : ℕ), l < e (x.val 0) → (σ x).val l = 0) ∧
      (∀ x, ((pgl D).func (σ x)) (e (x.val 0)) = 1) := by
  refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩;
  use fun x => ⟨ prependZerosOne ( e ( x.val 0 ) ) ( unprepend x.val ), by
    obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
    cases hCD k <;> simp_all +decide [ prependZerosOne_mem_pointedGluingSet ] ⟩
  all_goals generalize_proofs at *;
  use fun y => prepend ( Function.invFun e ( firstNonzero y ) ) ( stripZerosOne ( firstNonzero y ) y );
  · refine Continuous.subtype_mk ?_ ?_;
    convert continuous_prependZerosOne_uncurry.comp ( Continuous.prodMk ( continuous_of_discreteTopology.comp ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ) ( continuous_unprepend.comp continuous_subtype_val ) ) using 1;
  · intro x
    generalize_proofs at *;
    have h_eq : (gl C).func x = prepend (x.val 0) ((C (x.val 0)).func ⟨unprepend x.val, by
      have := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
      grind⟩) := by
      rfl
    generalize_proofs at *;
    have h_eq : (pgl D).func ⟨prependZerosOne (e (x.val 0)) (unprepend x.val), by
      assumption⟩ = prependZerosOne (e (x.val 0)) ((D (e (x.val 0))).func ⟨unprepend x.val, by
      cases hCD ( x.val 0 ) <;> simp_all +decide [ ScatFun.gl ]; all_goals grind⟩) := by
      all_goals generalize_proofs at *;
      convert ScatFun.pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by assumption ⟩ using 1
    generalize_proofs at *;
    cases hCD ( x.val 0 ) <;> simp_all +decide;
    · rw [ firstNonzero_prependZerosOne ];
      rw [ Function.leftInverse_invFun he ];
      rw [ stripZerosOne_prependZerosOne ];
      grind;
    · grind;
  · refine' ContinuousOn.mono _ _;
    exact { y : Baire | y ≠ zeroStream };
    · convert continuous_invFunPrependStrip_uncurry e |> Continuous.comp_continuousOn <| ContinuousOn.prodMk ( firstNonzero_continuousOn _ ) continuousOn_id using 1;
      exact fun y hy => hy;
    · intro y hy
      obtain ⟨x, hx⟩ := hy
      subst hx;
      simp only [Set.mem_setOf_eq];
      have := pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by
        obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
        cases hCD k <;> aesop ⟩
      generalize_proofs at *;
      intro h; have := congr_fun h ( e ( x.val 0 ) ) ; simp_all +decide [ prependZerosOne_at_i ] ;
      replace this := congr_fun this ( e ( x.val 0 ) ) ; simp_all +decide [ zeroStream, prependZerosOne ] ;
  · unfold prependZerosOne; aesop;
  · intro x;
    convert pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, _ ⟩ using 1;
    all_goals generalize_proofs at *;
    · constructor <;> intro h <;> simp_all +decide [ funext_iff, prependZerosOne ];
      convert pgl_func_block D ( e ( x.val 0 ) ) ⟨ unprepend x.val, by assumption ⟩ using 1;
      exact ⟨ fun h => funext fun n => by simpa using h n, fun h => fun n => by simpa using congr_fun h n ⟩;
    · obtain ⟨ k, hk ⟩ := GluingSet_inverse_short ( fun k => ( C k ).domain ) x;
      cases hCD k <;> aesop

end ScatFun

end
