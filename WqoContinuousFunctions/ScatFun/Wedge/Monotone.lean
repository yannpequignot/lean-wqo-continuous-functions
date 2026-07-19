import WqoContinuousFunctions.ScatFun.Wedge.UpperBound
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.LevelsFinitelyGenerated

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Monotonicity of `wedge`

`wedge` (`ScatFun/Wedge/Defs.lean`) is monotone (and hence a congruence for `Equiv`) under
pointwise reduction of the vertical family and the diagonal, unconditionally (no positivity
assumption on the number of vertical slots is needed). Shared between the `λ = 1` and `λ`
non-zero-limit cases of `FGatsuccessoroflimit` (`ScatFun/LevelsFinitelyGenerated/{Two,
LambdaPlusOne}.lean`), which both instantiate it rather than re-proving it.
-/

namespace ScatFun

/-- Per-slot based block reductions for the wedge monotonicity proof. -/
lemma wedge_slot_based_reductions {n : ℕ} {v v' : Fin n → ScatFun} {d d' : ScatFun}
    (hv : ∀ i, Reduces (v i) (v' i)) (hd : Reduces d d') :
    ∀ i, ∃ (σ : ↑(wedgeDomFamily v d i).domain → ↑(wedgeDomFamily v' d' i).domain)
      (τ : Baire → Baire), Continuous σ ∧
      ContinuousOn τ (Set.range (fun z => (wedgeDomFamily v' d' i).func (σ z))) ∧
      (∀ z, (wedgeDomFamily v d i).func z = τ ((wedgeDomFamily v' d' i).func (σ z))) ∧
      (i < n → τ zeroStream = zeroStream) ∧
      (i < n → Filter.Tendsto τ
        (nhdsWithin zeroStream (Set.range (fun z => (wedgeDomFamily v' d' i).func (σ z))))
        (nhds zeroStream)) := by
  intro i
  by_cases h : i < n
  · rw [wedgeDomFamily_vertical v d ⟨i, h⟩, wedgeDomFamily_vertical v' d' ⟨i, h⟩]
    obtain ⟨σ, τ, hσ, hτ, heq, hτ0, htend⟩ :=
      pgl_const_upper_based (v' ⟨i, h⟩) (fun _ => v ⟨i, h⟩)
        (fun _ => ⟨1, by simpa using (hv ⟨i, h⟩).trans (glList_single_equiv (v' ⟨i, h⟩)).1⟩)
    exact ⟨σ, τ, hσ, hτ, heq, fun _ => hτ0, fun _ => htend⟩
  · rw [wedgeDomFamily_diag v d i h, wedgeDomFamily_diag v' d' i h]
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := hd
    exact ⟨σ, τ, hσ, hτ, heq, fun hh => absurd hh h, fun hh => absurd hh h⟩

/-- `retag n` is continuous on the range of the glued map `gl (wedgeDomFamily v d)` (extracted
from the proof of `wedge_func_continuous`). -/
lemma retag_continuousOn_range {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) :
    ContinuousOn (retag n) (Set.range (gl (wedgeDomFamily v d)).func) := by
  refine continuousOn_piecewise_clopen
    (S := Set.range (gl (wedgeDomFamily v d)).func)
    (fun k w => if k < n then
        (if unprepend w = zeroStream then zeroStream
         else prependZerosOne (firstNonzero (unprepend w))
                (prepend k (stripZerosOne (firstNonzero (unprepend w)) (unprepend w))))
      else prependZerosOne (k - n) (prepend n (unprepend w)))
    (fun k => {w | w 0 = k})
    (fun z _ => ⟨z 0, rfl⟩)
    (fun k => isClopen_preimage_zero k)
    (fun z _ i hi j hj => ?_)
    ?_
    (fun z _ => ⟨z 0, rfl⟩)
    (retag n)
    ?_
  · simp only [Set.mem_setOf_eq] at hi hj
    subst hi; subst hj; rfl
  · intro k
    by_cases hk : k < n
    · simp only [hk, if_true]
      exact retag_continuousOn_vertical_slab v d k hk
    · simp only [hk, if_false]
      exact ((continuous_prependZerosOne _).comp
        ((continuous_prepend _).comp continuous_unprepend)).continuousOn
  · intro z _ i hi
    simp only [Set.mem_setOf_eq] at hi
    subst hi; rfl

/-- **Monotonicity of `wedge`.** If each vertical `v i` reduces to `v' i` and the diagonal `d`
reduces to `d'`, then `wedge v d` reduces to `wedge v' d'`. -/
lemma wedge_reduces_of_reduces {n : ℕ} {v v' : Fin n → ScatFun} {d d' : ScatFun}
    (hv : ∀ i, Reduces (v i) (v' i)) (hd : Reduces d d') :
    Reduces (wedge v d) (wedge v' d') := by
  classical
  choose σ' τ' hσ' hτ' heq' hτ0' htend' using wedge_slot_based_reductions hv hd
  set G : ScatFun := wedge v d with hG
  set P : ℕ → Set ↑G.domain := fun i => {x | (x : Baire) 0 = i} with hP
  have hfunc : ∀ (i : ℕ) (z : ↑(G.restrict (P i)).domain)
      (hpay : unprepend z.val ∈ (wedgeDomFamily v d i).domain),
      (G.restrict (P i)).func z
        = retag n (prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩)) := by
    intro i z hpay
    obtain ⟨hmem, hPi⟩ := z.2
    have hz0 : z.val 0 = i := hPi
    have hval : z.val = prepend i (unprepend z.val) := by
      conv_lhs => rw [← prepend_unprepend z.val]
      rw [hz0]
    have hmem2 : prepend i (unprepend z.val) ∈ (gl (wedgeDomFamily v d)).domain :=
      mem_gluingSet_prepend hpay
    show retag n ((gl (wedgeDomFamily v d)).func ⟨z.val, hmem⟩) = _
    rw [show (⟨z.val, hmem⟩ : ↑(gl (wedgeDomFamily v d)).domain)
        = ⟨prepend i (unprepend z.val), hmem2⟩ from Subtype.ext hval]
    rw [gl_func_prepend (wedgeDomFamily v d) i ⟨unprepend z.val, hpay⟩ hmem2]
  refine reduces_wedge_of_slot_partition G v' d' zeroStream P ?_ ?_ ?_
    (fun i z => σ' i ⟨unprepend z.val, ?_⟩) ?_ (fun i W => retag n (prepend i (τ' i W)))
    ?_ ?_ ?_ ?_ ?_
  · -- clopen
    intro i
    exact (isClopen_preimage_zero i).preimage continuous_subtype_val
  · -- disjoint
    intro i j hij
    rw [Set.disjoint_left]
    rintro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  · -- cover
    rw [Set.eq_univ_iff_forall]
    intro x
    exact Set.mem_iUnion.mpr ⟨x.val 0, rfl⟩
  · -- payload membership
    obtain ⟨hmem, hPi⟩ := z.2
    exact slab_unprepend_mem (wedgeDomFamily v d) i ⟨⟨z.val, hmem⟩, hPi⟩
  · -- hσb
    intro i
    exact (hσ' i).comp ((continuous_unprepend.comp continuous_subtype_val).subtype_mk _)
  · -- hτb
    intro i
    refine (retag_continuousOn_range v d).comp
      ((continuous_prepend i).comp_continuousOn ((hτ' i).mono ?_)) ?_
    · rintro _ ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    rintro _ ⟨z, rfl⟩
    obtain ⟨hmem, hPi⟩ := z.2
    have hpay : unprepend z.val ∈ (wedgeDomFamily v d i).domain :=
      slab_unprepend_mem (wedgeDomFamily v d) i ⟨⟨z.val, hmem⟩, hPi⟩
    refine ⟨⟨prepend i (unprepend z.val), mem_gluingSet_prepend hpay⟩, ?_⟩
    rw [gl_func_prepend (wedgeDomFamily v d) i ⟨unprepend z.val, hpay⟩
      (mem_gluingSet_prepend hpay)]
    show prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩)
        = prepend i (τ' i _)
    congr 1
    exact heq' i ⟨unprepend z.val, hpay⟩
  · -- heqb
    intro i z
    obtain ⟨hmem, hPi⟩ := z.2
    have hz0 : z.val 0 = i := hPi
    have hpay : unprepend z.val ∈ (wedgeDomFamily v d i).domain :=
      slab_unprepend_mem (wedgeDomFamily v d) i ⟨⟨z.val, hmem⟩, hPi⟩
    have hval : z.val = prepend i (unprepend z.val) := by
      conv_lhs => rw [← prepend_unprepend z.val]
      rw [hz0]
    have hmem2 : prepend i (unprepend z.val) ∈ (gl (wedgeDomFamily v d)).domain :=
      mem_gluingSet_prepend hpay
    have hgl : (gl (wedgeDomFamily v d)).func ⟨z.val, hmem⟩
        = prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩) := by
      rw [show (⟨z.val, hmem⟩ : ↑(gl (wedgeDomFamily v d)).domain)
          = ⟨prepend i (unprepend z.val), hmem2⟩ from Subtype.ext hval]
      exact gl_func_prepend (wedgeDomFamily v d) i ⟨unprepend z.val, hpay⟩ hmem2
    calc (G.restrict (P i)).func z
        = retag n ((gl (wedgeDomFamily v d)).func ⟨z.val, hmem⟩) := rfl
      _ = retag n (prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩)) := by
          rw [hgl]
      _ = retag n (prepend i (τ' i ((wedgeDomFamily v' d' i).func
            (σ' i ⟨unprepend z.val, hpay⟩)))) := by rw [heq']
  · -- hbase
    intro i hi
    show retag n (prepend i (τ' i zeroStream)) = zeroStream
    rw [hτ0' i hi]
    exact retag_vertical_base n i hi
  · -- hconv
    intro U hUopen hU0
    obtain ⟨m, hm⟩ := baire_cylinder_mem_nhds zeroStream U hUopen hU0
    refine ⟨n + m, fun i hi => ?_⟩
    have hin : n ≤ i := le_trans (Nat.le_add_right n m) hi
    rintro w ⟨z, rfl⟩
    obtain ⟨hmem, hPi⟩ := z.2
    have hz0 : z.val 0 = i := hPi
    have hpay : unprepend z.val ∈ (wedgeDomFamily v d i).domain :=
      slab_unprepend_mem (wedgeDomFamily v d) i ⟨⟨z.val, hmem⟩, hPi⟩
    apply hm
    intro k hk
    simp only [Finset.mem_range] at hk
    show (G.restrict (P i)).func z k = zeroStream k
    rw [hfunc i z hpay]
    rw [show prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩)
        = prepend (n + (i - n)) ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩) from by
          rw [Nat.add_sub_cancel' hin], retag_diagonal]
    rw [prependZerosOne_head_eq_zero (i - n) _ k (by omega)]
    rfl
  · -- hbase_cont
    intro i hi
    have hz0mem : zeroStream ∈ (wedgeDomFamily v d i).domain := by
      rw [wedgeDomFamily_vertical v d ⟨i, hi⟩]
      exact zeroStream_mem_pointedGluingSet _
    have hval0 : (wedgeDomFamily v d i).func ⟨zeroStream, hz0mem⟩ = zeroStream := by
      rw [scatFun_func_cast (wedgeDomFamily_vertical v d ⟨i, hi⟩) ⟨zeroStream, hz0mem⟩]
      exact pgl_func_zeroStream _ _
    have hbase_mem : prepend i zeroStream ∈ Set.range (gl (wedgeDomFamily v d)).func := by
      refine ⟨⟨prepend i zeroStream, mem_gluingSet_prepend hz0mem⟩, ?_⟩
      rw [gl_func_prepend (wedgeDomFamily v d) i ⟨zeroStream, hz0mem⟩
        (mem_gluingSet_prepend hz0mem), hval0]
    have hretag : Filter.Tendsto (retag n)
        (𝓝[Set.range (gl (wedgeDomFamily v d)).func] (prepend i zeroStream)) (𝓝 zeroStream) := by
      have hcw := (retag_continuousOn_range v d).continuousWithinAt hbase_mem
      rw [ContinuousWithinAt, retag_vertical_base n i hi] at hcw
      exact hcw
    refine hretag.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · apply ((continuous_prepend i).tendsto zeroStream).comp
      apply (htend' i hi).mono_left
      apply nhdsWithin_mono
      rintro x ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · filter_upwards [self_mem_nhdsWithin] with W hW
      obtain ⟨z, rfl⟩ := hW
      obtain ⟨hmem, hPi⟩ := z.2
      have hpay : unprepend z.val ∈ (wedgeDomFamily v d i).domain :=
        slab_unprepend_mem (wedgeDomFamily v d) i ⟨⟨z.val, hmem⟩, hPi⟩
      refine ⟨⟨prepend i (unprepend z.val), mem_gluingSet_prepend hpay⟩, ?_⟩
      rw [gl_func_prepend (wedgeDomFamily v d) i ⟨unprepend z.val, hpay⟩
        (mem_gluingSet_prepend hpay)]
      show prepend i ((wedgeDomFamily v d i).func ⟨unprepend z.val, hpay⟩)
          = prepend i (τ' i _)
      congr 1
      exact heq' i ⟨unprepend z.val, hpay⟩

/-- **Congruence of `wedge` under continuous equivalence.** -/
lemma wedge_congr_equiv {n : ℕ} {v v' : Fin n → ScatFun} {d d' : ScatFun}
    (hv : ∀ i, Equiv (v i) (v' i)) (hd : Equiv d d') :
    Equiv (wedge v d) (wedge v' d') :=
  ⟨wedge_reduces_of_reduces (fun i => (hv i).1) hd.1,
    wedge_reduces_of_reduces (fun i => (hv i).2) hd.2⟩

end ScatFun

end
