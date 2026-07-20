import WqoContinuousFunctions.ScatFun.Generators.Defs
import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessorOfLimit
import WqoContinuousFunctions.ScatFun.PreciseStructure.DiagonalForLambdaPlusOne

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Generic `glList`/`gl` gluing toolkit

Lam-agnostic `ScatFun` list-gluing/flattening/permutation lemmas, split out of
`ScatFun/LevelsFinitelyGenerated/LambdaPlusOne.lean` (where they had accumulated without ever
mentioning `lam`) so that both `Two.lean` (`λ = 1` case) and `LambdaPlusOne.lean` (`λ` non-zero-limit
case) of `FGatsuccessoroflimit` (`5_precise_struct_memo.tex:378`) can share them instead of
duplicating (`Two.lean`'s former `finGl_two_of_equiv` was one such duplicate of
`finGl_single_of_equiv`).

Also holds the single-generator `FinGl`/`Gl`/`glList` toolkit (`empty_mem_FinGl`,
`gl_reduces_single`, `glList_single_equiv`, `glFin_single_equiv`, `Gl_eq_glList_copiesList`,
`copiesList_indicator_mult`, `Finset.exists_toFinFun_eq`), moved here from
`LevelsFinitelyGenerated.lean` once that file's level-`0`/`1`/limit results turned out to need
the same lam-agnostic lemmas as `Two.lean`/`LambdaPlusOne.lean`.
-/

namespace ScatFun

/-- A `ScatFun` with empty domain lies in `FinGl B` for *any* finite family `B` (witnessed by
the zero-multiplicity tuple: `Gl B (fun _ => 0)` glues zero copies of everything, hence also
has empty domain). -/
lemma empty_mem_FinGl {n : ℕ} (B : Fin n → ScatFun) {F : ScatFun} (hF : IsEmpty ↥F.domain) :
    F ∈ FinGl B := by
  have hGl_empty : IsEmpty ↥(Gl B (fun _ => 0)).domain := by
    rw [Set.isEmpty_coe_sort]
    simp [Gl, copiesSeq, copiesList, gl_domain, GluingSet, empty]
  exact ⟨fun _ => 0, reduces_of_isEmpty_domain hGl_empty, reduces_of_isEmpty_domain hF⟩

/-- If every block of `F` except block `i` is `ScatFun.empty`, then `gl F` reduces to `F i`.
The reverse direction of `reduces_block_gl`, using the emptiness of the other blocks to
recover the block-`i` point (and the ray `unprepend`/`prepend i`) from an arbitrary point of
`(gl F).domain`. -/
lemma gl_reduces_single (F : ℕ → ScatFun) (i : ℕ) (hempty : ∀ j, j ≠ i → F j = empty) :
    Reduces (gl F) (F i) := by
  have hmem : ∀ x : ↥(gl F).domain, x.val 0 = i ∧ unprepend x.val ∈ (F i).domain := by
    intro x
    have hx' : x.val ∈ GluingSet (fun k => (F k).domain) := x.prop
    obtain ⟨j, hj0, hjmem⟩ := GluingSet_inverse_short (fun k => (F k).domain) ⟨x.val, hx'⟩
    rcases eq_or_ne j i with hji | hji
    · exact ⟨hji ▸ hj0, hji ▸ hjmem⟩
    · exact absurd hjmem (hempty j hji ▸ Set.notMem_empty _)
  refine ⟨fun x => ⟨unprepend x.val, (hmem x).2⟩,
    (continuous_unprepend.comp continuous_subtype_val).subtype_mk _,
    prepend i, (continuous_prepend i).continuousOn, fun x => ?_⟩
  have hx0 : x.val 0 = i := (hmem x).1
  have hxeq : prepend i (unprepend x.val) = x.val := by rw [← hx0]; exact prepend_unprepend x.val
  have hxmem : prepend i (unprepend x.val) ∈ (gl F).domain := by rw [hxeq]; exact x.prop
  have hgl := gl_func_prepend F i ⟨unprepend x.val, (hmem x).2⟩ hxmem
  have hxx : (⟨prepend i (unprepend x.val), hxmem⟩ : ↥(gl F).domain) = x := Subtype.ext hxeq
  rw [hxx] at hgl
  show (gl F).func x = prepend i ((F i).func ⟨unprepend x.val, (hmem x).2⟩)
  exact hgl

/-- A single-block family reduces both ways with its block: `w ≡ glList [w]`. -/
lemma glList_single_equiv (w : ScatFun) : Equiv w (glList [w]) := by
  have hempty : ∀ j, j ≠ 0 → (fun k => ([w] : List ScatFun).getD k empty) j = empty := by
    intro j hj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [List.getD]
  refine ⟨reduces_block_gl (fun k => [w].getD k empty) 0, ?_⟩
  have := gl_reduces_single (fun k => [w].getD k empty) 0 hempty
  simpa [glList] using this

/-- A single-block finite family reduces both ways with its block: `glFin (fun _ => w) ≡ w`. -/
lemma glFin_single_equiv (w : ScatFun) : Equiv (glFin (fun _ : Fin 1 => w)) w := by
  have hglFin : glFin (fun _ : Fin 1 => w) = glList [w] := by
    unfold glFin glList; congr with k; aesop
  rw [hglFin]
  exact (glList_single_equiv w).symm

/-! ## Infrastructure for single-generator `FinGl`-membership transfers

The key realisation avoiding a general "`FinGl` under reindexing/permutation" lemma: `Gl B t`
is *definitionally* `glList (copiesList B t)` (both unfold to the same `gl`-of-a-padded-list),
so `FinGl`-membership witnesses can be built directly from `copiesList` facts, without ever
pinning down the exact order of `S.toList` for a `Finset` `S` — we only need `w`'s *index*
(`Finset.exists_toFinFun_eq`), not the whole enumeration. -/

/-- `Gl B t` unfolds to `glList` of the same list `copiesList B t`: both are `gl` of that
list's `getD`-padding. -/
lemma Gl_eq_glList_copiesList {n : ℕ} (B : Fin n → ScatFun) (t : Fin n → ℕ) :
    Gl B t = glList (copiesList B t) := rfl

/-- Generalisation of `copiesList_indicator` (`CenteredFunctions/FinitenessHelpers.lean:347`)
from multiplicity `1` to an arbitrary multiplicity `N`: only block `i` contributes, `N` copies
of it. -/
lemma copiesList_indicator_mult {m : ℕ} (B : Fin m → ScatFun) (i : Fin m) (N : ℕ) :
    copiesList B (fun j => if j = i then N else 0) = List.replicate N (B i) := by
  have key : ∀ (l : List (Fin m)), l.Nodup →
      (l.flatMap (fun j => List.replicate (if j = i then N else 0) (B j)))
        = (if i ∈ l then List.replicate N (B i) else []) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, ih (List.Nodup.of_cons hl)]
      rcases eq_or_ne a i with rfl | ha
      · have hi : a ∉ l := (List.nodup_cons.mp hl).1
        simp [hi]
      · simp [List.mem_cons, ha, Ne.symm ha]
  simp only [copiesList]
  rw [key (List.finRange m) (List.nodup_finRange m)]
  simp [List.mem_finRange]

/-- `Finset.toFinFun` hits every element of `S` at some index — the only fact needed about its
enumeration (its *order* is never pinned down). -/
lemma _root_.Finset.exists_toFinFun_eq {α : Type*} (S : Finset α) {w : α} (hw : w ∈ S) :
    ∃ i : Fin S.card, S.toFinFun i = w := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hw)
  refine ⟨n.cast S.length_toList, ?_⟩
  show S.toList.get ((n.cast S.length_toList).cast S.length_toList.symm) = w
  simpa using hn

/-- **Single-generator `FinGl` transfer.** If `F` is continuously equivalent to some `w ∈ S`,
then `F ∈ FinGl S.toFinFun`. -/
lemma finGl_single_of_equiv {S : Finset ScatFun} {F w : ScatFun}
    (hw : w ∈ S) (hEq : Equiv F w) : F ∈ FinGl S.toFinFun := by
  obtain ⟨i, hi⟩ := S.exists_toFinFun_eq hw
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · rw [Gl_eq_glList_copiesList, copiesList_indicator_mult, hi, List.replicate_one]
    exact (glList_single_equiv w).2.trans hEq.2
  · rw [Gl_eq_glList_copiesList, copiesList_indicator_mult, hi, List.replicate_one]
    exact hEq.1.trans (glList_single_equiv w).1

/-
**Plain gluing of a list is invariant, up to `Equiv`, under permutations of the list.**
A permutation of the block list gives an order-independent gluing: block `i` of `glList L`
is `L.getD i empty`, and a permutation matches these blocks up bijectively (padding the tails
with `empty`, which reduces to anything), so `gl_reduces_of_blockEmbed` applies in both
directions.
-/
lemma glList_perm_equiv {L L' : List ScatFun} (h : L.Perm L') :
    Equiv (glList L) (glList L') := by
  revert h;
  intro hL;
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin L.length ≃ Fin L'.length, ∀ i, L.get i = L'.get (σ i) := by
    have h_perm : ∀ (L L' : List ScatFun), L.Perm L' → ∃ σ : Fin L.length ≃ Fin L'.length, ∀ i, L.get i = L'.get (σ i) := by
      intro L L' hL; induction' hL with L L' hL ih; aesop;
      · obtain ⟨ σ, hσ ⟩ := ‹∃ σ : Fin L'.length ≃ Fin hL.length, ∀ i, L'.get i = hL.get ( σ i ) ›; use Equiv.ofBijective ( Fin.cons 0 ( Fin.succ ∘ σ ) ) ⟨ by
          simp +decide only [Injective, List.length_cons, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, comp_apply, imp_self, true_and, Fin.succ_ne_zero, Fin.succ_inj, EmbeddingLike.apply_eq_iff_eq, implies_true, and_self, and_true];
          exact fun i hi => absurd hi ( ne_of_lt ( Fin.succ_pos _ ) ), by
          intro x; induction x using Fin.inductionOn <;> simp +decide [ *, Fin.cons ] ;
          · exact ⟨ 0, rfl ⟩;
          · exact ⟨ Fin.succ ( σ.symm ‹_› ), by simp +decide [ Fin.cases ] ⟩ ⟩ ; simp +decide [ Fin.forall_fin_succ ] ;
        exact hσ;
      · refine ⟨ Equiv.swap ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩, fun i => ?_ ⟩ ; rcases i with ⟨ _ | _ | i, hi ⟩ <;> simp +decide [ Fin.ext_iff, Equiv.swap_apply_def ] at hi ⊢;
      · rename_i h₁ h₂ h₃ h₄;
        obtain ⟨ σ₁, hσ₁ ⟩ := h₃
        obtain ⟨ σ₂, hσ₂ ⟩ := h₄
        use σ₁.trans σ₂
        intro i
        simp only [List.get_eq_getElem, Equiv.trans_apply];
        grind +qlia;
    exact h_perm L L' hL |> fun ⟨ σ, hσ ⟩ => ⟨ σ.trans ( Equiv.cast ( by simp +decide ) ), fun i => by simpa using hσ i ⟩;
  constructor;
  · convert gl_reduces_of_blockEmbed ( fun k => if hk : k < L.length then L.get ⟨ k, hk ⟩ else ScatFun.empty ) ( fun k => if hk : k < L'.length then L'.get ⟨ k, hk ⟩ else ScatFun.empty ) ( fun k => if hk : k < L.length then σ ⟨ k, hk ⟩ else L'.length + k ) _ _ using 1;
    · unfold glList;
      grind +qlia;
    · exact congr_arg _ ( funext fun k => by aesop );
    · intro a b; by_cases ha : a < L.length <;> by_cases hb : b < L.length <;> simp +decide [ ha, hb ] ;
      · exact fun h => by simpa [ Fin.ext_iff ] using σ.injective ( Fin.ext h ) ;
      · exact fun h => absurd h ( by linarith [ Fin.is_lt ( σ ⟨ a, ha ⟩ ) ] );
      · grind +splitImp;
    · intro i; by_cases hi : i < L.length <;> simp +decide [ hi ] ;
      · constructor;
        swap;
        exact fun x => ⟨ x, by
          grind ⟩
        generalize_proofs at *;
        refine ⟨ ?_, ?_ ⟩;
        · fun_prop;
        · refine ⟨ ?_, ?_, ?_ ⟩;
          exact fun x => x;
          · exact continuousOn_id;
          · exact fun x => scatFun_func_cast (hσ ⟨i, hi⟩) x;
      · grind [empty_reduces];
  · apply gl_reduces_of_blockEmbed;
    rotate_right;
    use fun i => if hi : i < L'.length then σ.symm ⟨ i, hi ⟩ else i + L.length;
    · intro i j hij; simp_all +decide ;
      grind +qlia;
    · intro i; split_ifs <;> simp_all +decide ;
      · constructor;
        exact ⟨ continuous_id, fun x => x, continuousOn_id, fun x => rfl ⟩;
      · constructor;
        exact ⟨ continuous_id, fun _ => 0, continuousOn_const, fun x => by cases x; tauto ⟩

/-
**A finite gluing of generators lies in `FinGl` of the generator set.**  If every block of
the list `L` belongs to the finset `S`, then `glList L ∈ FinGl S.toFinFun`: group the blocks of
`L` by which element of `S` they equal (multiplicities `t i := L.count (S.toFinFun i)`); the
grouped list `copiesList S.toFinFun t` is a permutation of `L` (every element of `L` is some
`S.toFinFun i` since `S.toFinFun` enumerates `S`), so `glList L ≡ glList (copiesList S.toFinFun t)
= Gl S.toFinFun t` by `glList_perm_equiv` and `Gl_eq_glList_copiesList`.
-/
lemma finGl_glList_of_forall_mem {S : Finset ScatFun} {L : List ScatFun}
    (hL : ∀ w ∈ L, w ∈ S) : glList L ∈ FinGl S.toFinFun := by
  -- By definition of $copiesList$, we can choose $t i := L.count (S.toFinFun i)$.
  set t : Fin S.card → ℕ := fun i => List.count (S.toFinFun i) L with ht_def
  have hties : copiesList S.toFinFun t ≈ L := by
    refine List.Perm.symm ( List.perm_iff_count.mpr ?_ );
    intro a; by_cases ha : a ∈ L <;> simp_all +decide [ List.count ] ;
    · -- Since `a` is in `L` and `L` is a list of elements from `S`, there exists a unique `i` such that `S.toFinFun i = a`.
      obtain ⟨i, hi⟩ : ∃ i : Fin S.card, S.toFinFun i = a := by
        exact Finset.exists_toFinFun_eq S (hL a ha);
      simp +decide only [← hi, copiesList];
      simp +decide only [List.countP_flatMap];
      rw [ List.sum_map_eq_nsmul_single i ] <;> simp +decide [ List.countP_eq_length_filter ];
      exact fun j hj₁ hj₂ hj₃ => hj₁ <| Fin.ext <| by have := List.nodup_iff_injective_get.mp ( Finset.nodup_toList S ) hj₃; aesop;
    · rw [ List.countP_eq_zero.mpr, List.countP_eq_zero.mpr ] <;> simp_all +decide ;
      · intro x hx; contrapose! ha; simp_all +decide [ copiesList ] ;
        grind;
      · exact fun x hx => by rintro rfl; exact ha hx;
  exact ⟨ t, by
    convert ScatFun.glList_perm_equiv hties using 1 ⟩

/-- **`FinGl` transfer from an equivalence to a finite gluing of generators.** -/
lemma finGl_of_equiv_glList {S : Finset ScatFun} {F : ScatFun} {L : List ScatFun}
    (hL : ∀ w ∈ L, w ∈ S) (hEq : Equiv F (glList L)) : F ∈ FinGl S.toFinFun := by
  obtain ⟨t, h1, h2⟩ := finGl_glList_of_forall_mem hL
  exact ⟨t, h1.trans hEq.2, hEq.1.trans h2⟩

/-- The binary gluing `f ⊕ g` is (equivalent to, in fact equal to) the list gluing `glList [f, g]`. -/
lemma finGl_glBin_equiv_glList (f g : ScatFun) : Equiv (f ⊕ g) (glList [f, g]) := by
  have hcl : copiesList ![f, g] ![1, 1] = [f, g] := by
    simp [copiesList, List.finRange_succ, List.finRange_zero]
  have : (f ⊕ g) = glList [f, g] := by
    show Gl ![f, g] ![1, 1] = glList [f, g]
    rw [Gl_eq_glList_copiesList, hcl]
  rw [this]; exact ⟨ContinuouslyReduces.refl _, ContinuouslyReduces.refl _⟩

/-- `omega` is monotone under `Reduces`. -/
lemma omega_reduces_of_reduces {a b : ScatFun} (h : Reduces a b) :
    Reduces (omega a) (omega b) :=
  gl_reduces_of_pointwise (fun _ => a) (fun _ => b) (fun _ => h)

/-- If `IntertwineSet F w` is infinite, then `omega w` reduces to `F`. -/
lemma omega_reduces_of_intertwineSet_infinite (F w : ScatFun)
    (h : (IntertwineSet F w).Infinite) : Reduces (omega w) F := by
  have hbase : Reduces (omega (glFin (fun _ : Fin 1 => w))) F :=
    intertwine_reductions F (fun _ : Fin 1 => w) (fun _ => h)
  have hEq : Equiv (omega w) (omega (glFin (fun _ : Fin 1 => w))) :=
    ⟨omega_reduces_of_reduces (glFin_single_equiv w).2,
     omega_reduces_of_reduces (glFin_single_equiv w).1⟩
  exact hEq.1.trans hbase

/-
**Isolating clopen assignment for a nonempty finite set of Baire points.**  There is a
continuous `assign : Baire → ℕ` taking values `< S.card`, injective on `S`, and hitting every
value `< S.card` on `S`.  The blocks `assign⁻¹{i}` then form a clopen partition of `Baire` in
which each point of `S` lies in its own block.  Constructed from a finite prefix length that
distinguishes all points of `S` (points of `Baire` are separated by cylinders), assigning `x`
the index of the unique `s ∈ S` sharing that prefix, or `0` otherwise.
-/
lemma exists_isolating_assign (S : Finset Baire) (hS : S.Nonempty) :
    ∃ assign : Baire → ℕ, Continuous assign ∧ (∀ x, assign x < S.card) ∧
      Set.InjOn assign (↑S : Set Baire) ∧ (∀ i, i < S.card → ∃ s ∈ S, assign s = i) := by
  -- By definition of `Finset.card`, there exists a bijection between `S` and `Fin S.card`.
  obtain ⟨bij, hbij⟩ : ∃ bij : S ≃ Fin S.card, True := by
    exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
  -- Let's choose a separating prefix length `N` for `S`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ i < N, s i ≠ t i := by
    have h_sep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ i, s i ≠ t i := by
      exact fun s hs t ht hst => Function.ne_iff.mp hst;
    choose! N hN using h_sep;
    exact ⟨ Finset.sup ( S ×ˢ S ) ( fun p => N p.1 p.2 ) + 1, fun s hs t ht hst => ⟨ N s t, Nat.lt_succ_of_le ( Finset.le_sup ( f := fun p => N p.1 p.2 ) ( Finset.mk_mem_product hs ht ) ), hN s hs t ht hst ⟩ ⟩;
  refine ⟨ fun x => if hx : ∃ s ∈ S, ∀ i < N, s i = x i then bij ⟨ hx.choose, hx.choose_spec.1 ⟩ |> Fin.val else 0, ?_, ?_, ?_, ?_ ⟩;
  · refine continuous_iff_continuousAt.mpr ?_;
    intro x;
    by_cases hx : ∃ s ∈ S, ∀ i < N, s i = x i;
    · refine tendsto_const_nhds.congr' ?_;
      filter_upwards [ IsOpen.mem_nhds ( show IsOpen { y : Baire | ∀ i < N, y i = x i } from by
                                          rw [ isOpen_pi_iff ];
                                          intro f hf; use Finset.range N; use fun i => { y : ℕ | y = x i } ; aesop; ) ( show x ∈ { y : Baire | ∀ i < N, y i = x i } from fun i hi => rfl ) ] with y hy;
      split_ifs <;> simp_all +decide [ funext_iff ];
    · refine tendsto_const_nhds.congr' ?_;
      rw [ Filter.EventuallyEq, eventually_nhds_iff ];
      refine ⟨ { y : Baire | ∀ i < N, y i = x i }, ?_, ?_, ?_ ⟩ <;> norm_num;
      · grind;
      · rw [ isOpen_pi_iff ];
        intro f hf; use Finset.range N; use fun i => { y : ℕ | y = x i } ; aesop;
  · aesop;
  · intro s hs t ht h_eq;
    contrapose! h_eq;
    split_ifs <;> simp_all +decide ;
    · intro h; have := bij.injective ( Fin.ext h ) ; simp_all +decide ;
      exact absurd ( hN _ hs _ ht h_eq ) ( by rintro ⟨ i, hi, hi' ⟩ ; have := ‹∃ s_1 ∈ S, ∀ i < N, s_1 i = s i›.choose_spec.2 i hi; have := ‹∃ s ∈ S, ∀ i < N, s i = t i›.choose_spec.2 i hi; aesop );
    · rename_i h₁ h₂;
      exact absurd ( h₂ t ht ) ( by rintro ⟨ i, hi, hi' ⟩ ; exact hi' rfl );
    · rename_i h₁ h₂;
      exact absurd ( h₂ s hs ) ( by tauto );
    · exact absurd ( ‹∀ x ∈ S, ∃ x_1 < N, ¬x x_1 = s x_1› s hs ) ( by tauto );
  · intro i hi; use bij.symm ⟨ i, hi ⟩; simp +decide ;
    split_ifs with hx;
    · have := hx.choose_spec.2;
      contrapose! hN;
      exact ⟨ hx.choose, hx.choose_spec.1, bij.symm ⟨ i, hi ⟩, by simp, by aesop, this ⟩;
    · exact False.elim <| hx ⟨ _, bij.symm ⟨ i, hi ⟩ |>.2, fun j hj => rfl ⟩

/-
**Reverse of `gl_gl_flatten_reduces`.**  The single gluing of the flattened family reduces
back to the nested double gluing: a flat block `m = Nat.pair i k` carrying payload `a` maps to
the nested point `(i)⌐(k)⌐a`.
-/
lemma gl_flat_reduces_gl_gl (H : ℕ → ℕ → ScatFun) :
    Reduces (gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2))
      (gl (fun i => gl (fun k => H i k))) := by
  -- Define σ and τ to construct the reduction.
  set σ : ↑(gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2)).domain → ↑(gl (fun i => gl (fun k => H i k))).domain := fun x =>
    ⟨prepend (Nat.unpair (x.val 0)).1 (prepend (Nat.unpair (x.val 0)).2 (unprepend x.val)), by
      obtain ⟨ i, hi ⟩ := x.2;
      obtain ⟨ j, rfl ⟩ := hi.1;
      obtain ⟨ y, hy, hy' ⟩ := hi.2;
      simp +decide only [gl_domain, ← hy', unprepend_prepend];
      grind [mem_gluingSet_prepend]⟩
  generalize_proofs at *;
  set τ : Baire → Baire := fun y => prepend (Nat.pair (y 0) (unprepend y 0)) (unprepend (unprepend y));
  refine ⟨ σ, ?_, τ, ?_, ?_ ⟩;
  · refine Continuous.subtype_mk ?_ ?_;
    -- The function σ is continuous because it is a composition of continuous functions.
    have h_cont_sigma : Continuous (fun x : Baire => prepend (Nat.unpair (x 0)).1 (prepend (Nat.unpair (x 0)).2 (unprepend x))) := by
      apply_rules [ continuous_pi, continuous_apply, continuous_const ];
      intro i; rcases i with ( _ | i ) <;> simp +decide [ prepend, unprepend ] ;
      · fun_prop (disch := solve_by_elim);
      · fun_prop (disch := solve_by_elim)
    generalize_proofs at *;
    exact h_cont_sigma.comp continuous_subtype_val;
  · refine Continuous.continuousOn ?_;
    refine continuous_pi fun n => ?_;
    rcases n with ( _ | n ) <;> simp +decide [ τ, prepend, unprepend ];
    · fun_prop;
    · exact continuous_apply _;
  · intro x
    simp only [gl_domain, τ, σ];
    unfold ScatFun.gl;
    unfold GluingFunVal;
    simp +decide only [glBlock, Lean.Elab.WF.paramLet, unprepend_prepend];
    simp +decide [ prepend, unprepend ]

/-- **Equivalence form of nested-gluing flattening.** -/
lemma gl_gl_flatten_equiv (H : ℕ → ℕ → ScatFun) :
    Equiv (gl (fun i => gl (fun k => H i k)))
      (gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2)) :=
  ⟨gl_gl_flatten_reduces H, gl_flat_reduces_gl_gl H⟩

/-
The binary gluing `glBin` respects `Equiv` in both arguments.
-/
lemma glBin_congr {a a' b b' : ScatFun} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (glBin a b) (glBin a' b') := by
  -- Since `Equiv` is symmetric and transitive, we can apply these properties to get `b.Equiv c`.
  have h_equiv_bc : b.Equiv b' := by
    exact hb
  have h_equiv_ac : a.Equiv a' := by
    exact ha;
  apply And.intro;
  · apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp_all +decide [ ScatFun.copiesSeq ] ;
    · exact h_equiv_ac.1;
    · exact h_equiv_bc.1;
    · simp only [copiesList, List.finRange_succ, List.finRange_zero]
      exact empty_reduces _
  · apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp_all +decide [ copiesSeq ] ;
    · exact h_equiv_ac.2;
    · exact h_equiv_bc.2;
    · simp only [copiesList, List.finRange_succ, List.finRange_zero]
      exact empty_reduces _

/-
The binary gluing of two list-gluings, as a nested double gluing of the two block-families.
-/
lemma glBin_glList_equiv_gl_gl (L1 L2 : List ScatFun) :
    Equiv (glBin (glList L1) (glList L2))
      (gl (fun i => gl (fun k =>
        if i = 0 then L1.getD k empty else if i = 1 then L2.getD k empty else empty))) := by
  constructor <;> (apply ScatFun.gl_reduces_of_pointwise; intro i; rcases i with ( _ | _ | i ) <;> simp_all +decide [ScatFun.copiesSeq] ;);
  all_goals try exact ScatFun.Equiv.refl _ |>.1;
  · convert ScatFun.empty_reduces _ using 1;
  · exact gl_reduces_single (fun k => empty) i fun j => congrFun rfl

/-
The flattened double gluing of the two block-families is the list-gluing of the concatenation.
-/
lemma gl_flat_equiv_glList_append (L1 L2 : List ScatFun) :
    Equiv (gl (fun m => (if (Nat.unpair m).1 = 0 then L1.getD (Nat.unpair m).2 empty
        else if (Nat.unpair m).1 = 1 then L2.getD (Nat.unpair m).2 empty else empty)))
      (glList (L1 ++ L2)) := by
  constructor;
  · apply ScatFun.gl_reduces_of_blockEmbed_support;
    case e => exact fun i => if ( Nat.unpair i ).1 = 0 then ( Nat.unpair i ).2 else L1.length + ( Nat.unpair i ).2;
    · intro i hi j hj hij;
      by_cases hi0 : (Nat.unpair i).1 = 0 <;> by_cases hj0 : (Nat.unpair j).1 = 0 <;> simp_all +decide ;
      · rw [ ← Nat.pair_unpair i, ← Nat.pair_unpair j, hi0, hj0, hij ];
      · exact False.elim <| hi.elim fun x hx => by simp_all +decide [ empty ] ;
      · contrapose! hj;
        rw [ List.getElem?_eq_none ] <;> norm_num; all_goals grind;
      · cases h : ( Nat.unpair i ).1 <;> cases h' : ( Nat.unpair j ).1 <;> simp_all +decide ;
        split_ifs at hi hj <;> simp_all +decide [ ScatFun.empty ];
        rw [ ← Nat.pair_unpair i, ← Nat.pair_unpair j, h, h', hij ];
    · intro i hi; split_ifs <;> simp_all +decide [ List.getElem?_append ] ;
      · by_cases h : ( Nat.unpair i ).2 < L1.length <;> simp_all +decide ;
        · exact ScatFun.Equiv.refl _ |>.1;
        · exact False.elim <| hi.elim fun x hx => by simp_all +decide [ empty ] ;
      · exact ScatFun.Equiv.refl _ |>.1;
      · exact False.elim <| hi.elim fun x hx => by simp_all +decide [ empty ] ;
  · apply ScatFun.gl_reduces_of_blockEmbed_support;
    case e => exact fun i => Nat.pair ( if i < L1.length then 0 else 1 ) ( if i < L1.length then i else i - L1.length );
    · intro i hi j hj hij; simp_all +decide [ Nat.pair_eq_pair ] ;
      grind;
    · intro i hi; split_ifs <;> simp_all +decide [ Nat.unpair_pair ] ;
      · convert ScatFun.empty_reduces using 1;
        constructor <;> intro h <;> simp_all +decide [ List.getElem?_append ];
        · exact fun G => empty_reduces G;
        · exact ScatFun.Equiv.refl _ |>.1;
      · rw [ List.getElem?_append ];
        rw [ if_neg ( by linarith ) ] ; exact ScatFun.Equiv.refl _ |> fun h => h.1

/-- **The list-gluing of a concatenation is the binary gluing of the two list-gluings.** -/
lemma glList_append_equiv (L1 L2 : List ScatFun) :
    Equiv (glList (L1 ++ L2)) (glBin (glList L1) (glList L2)) :=
  Equiv.symm (Equiv.trans (glBin_glList_equiv_gl_gl L1 L2)
    (Equiv.trans
      (gl_gl_flatten_equiv (fun i k =>
        if i = 0 then L1.getD k empty else if i = 1 then L2.getD k empty else empty))
      (gl_flat_equiv_glList_append L1 L2)))

/-
**From `FinGl` membership to an equivalent gluing of generators.**  If `a ∈ FinGl S.toFinFun`
then `a` is continuously equivalent to `glList L` for some list `L` of elements of `S`.
-/
lemma exists_glList_of_finGl {S : Finset ScatFun} {a : ScatFun}
    (ha : a ∈ FinGl S.toFinFun) : ∃ L : List ScatFun, (∀ w ∈ L, w ∈ S) ∧ Equiv a (glList L) := by
  obtain ⟨ t, ht ⟩ := ha;
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact List.flatMap ( fun i => List.replicate ( t i ) ( S.toFinFun i ) ) ( List.finRange S.card );
  · simp +contextual [ List.mem_flatMap, List.mem_replicate ];
    exact fun w x hx hw => Finset.mem_toList.mp ( List.getElem_mem _ );
  · convert ht.symm using 1

/-- **`FinGl S` is closed under binary gluing.** -/
lemma finGl_glBin_mem {S : Finset ScatFun} {a b : ScatFun}
    (ha : a ∈ FinGl S.toFinFun) (hb : b ∈ FinGl S.toFinFun) :
    (a ⊕ b) ∈ FinGl S.toFinFun := by
  obtain ⟨La, hLa, haE⟩ := exists_glList_of_finGl ha
  obtain ⟨Lb, hLb, hbE⟩ := exists_glList_of_finGl hb
  refine finGl_of_equiv_glList (L := La ++ Lb) ?_ ?_
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hLa w h
    · exact hLb w h
  · exact (glBin_congr haE hbE).trans (glList_append_equiv La Lb).symm

/-
**`FinGl S` is closed under `glList` of `FinGl S` members.**  If every entry of the list `L`
lies in `FinGl S.toFinFun`, then so does `glList L`.  (Induction on `L`, using `finGl_glBin_mem`
for the cons step and `empty_mem_FinGl` for the base case.)
-/
lemma finGl_glList_of_forall_finGl {S : Finset ScatFun} {L : List ScatFun}
    (hL : ∀ w ∈ L, w ∈ FinGl S.toFinFun) : glList L ∈ FinGl S.toFinFun := by
  induction' L with w L ih;
  · apply empty_mem_FinGl;
    simp only [glList, List.getD_eq_getElem?_getD, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, gl_domain, isEmpty_coe_sort];
    unfold GluingSet; aesop;
  · have h_equiv : Equiv (glList (w :: L)) (w ⊕ glList L) := by
      have h_equiv : Equiv (glList ([w] ++ L)) (glBin (glList [w]) (glList L)) :=
        glList_append_equiv [w] L
      convert Equiv.trans h_equiv _ using 1;
      exact Equiv.trans ( Equiv.symm ( glBin_congr ( glList_single_equiv w ) ( Equiv.refl _ ) ) ) ( Equiv.refl _ );
    have h_bin : (w ⊕ glList L) ∈ FinGl S.toFinFun := by
      apply finGl_glBin_mem; exact hL w (by simp); exact ih (fun w hw => hL w (by simp [hw]));
    apply finGl_closed_equiv; assumption;
    exact h_equiv.symm

/-- **Flattening a list of block-lists.**  Gluing the list `Ls.map glList` of per-block gluings
is equivalent to gluing the flattened block-list `Ls.flatten`. -/
lemma glList_map_glList_flatten (Ls : List (List ScatFun)) :
    Equiv (glList (Ls.map glList)) (glList Ls.flatten) := by
  induction Ls with
  | nil => exact Equiv.refl _
  | cons L rest ih =>
    have hmap : (L :: rest).map glList = [glList L] ++ rest.map glList := rfl
    have hflat : (L :: rest).flatten = L ++ rest.flatten := rfl
    have e1 : Equiv (glList ((L :: rest).map glList))
        (glBin (glList L) (glList (rest.map glList))) := by
      rw [hmap]
      exact Equiv.trans (glList_append_equiv [glList L] (rest.map glList))
        (glBin_congr (Equiv.symm (glList_single_equiv (glList L))) (Equiv.refl _))
    have e2 : Equiv (glList ((L :: rest).flatten)) (glBin (glList L) (glList rest.flatten)) := by
      rw [hflat]; exact glList_append_equiv L rest.flatten
    exact Equiv.trans e1 (Equiv.trans (glBin_congr (Equiv.refl _) ih) (Equiv.symm e2))

/-- **Flattening a finitely-supported family of list-gluings into a single list-gluing.**
`gl` of the family `i ↦ glList (Lf i)` (padded with `empty` past `m`) is equivalent to the
`glList` of the concatenated list `⊕ᵢ Lf i`, by associativity of plain gluing. -/
lemma gl_dite_glList_flatten_equiv (m : ℕ) (Lf : Fin m → List ScatFun) :
    Equiv (gl (fun i => if h : i < m then glList (Lf ⟨i, h⟩) else empty))
      (glList ((List.finRange m).flatMap (fun i => Lf i))) := by
  have hLHS : (gl (fun i => if h : i < m then glList (Lf ⟨i, h⟩) else empty))
      = glList ((List.ofFn Lf).map glList) := by
    show gl _ = gl (fun k => ((List.ofFn Lf).map glList).getD k empty)
    congr 1; funext i
    by_cases h : i < m
    · rw [dif_pos h]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn]
      simp [h]
    · rw [dif_neg h]
      rw [List.getD_eq_default]
      simp only [List.length_map, List.length_ofFn]; omega
  have hRHS : ((List.finRange m).flatMap (fun i => Lf i)) = (List.ofFn Lf).flatten := by
    rw [List.ofFn_eq_map]; rfl
  rw [hLHS, hRHS]
  exact glList_map_glList_flatten (List.ofFn Lf)

/-
**CB-levels of a codomain-corestriction, as a homeomorphic image.**  `(coRestrict F C).func`
is `(F.func ∘ val_S) ∘ (F.restrictEquiv S)` for `S = {z | F.func z ∈ C}`, so its `β`-th CB-level
is the `restrictEquiv`-symm image of the `β`-th CB-level of `F.func ∘ val_S`.
-/
lemma coRestrict_CBLevel_symm (F : ScatFun) (C : Set Baire) (β : Ordinal.{0}) :
    CBLevel (coRestrict F C).func β
      = (F.restrictEquiv {z : ↑F.domain | F.func z ∈ C}).symm ''
        CBLevel (F.func ∘ (Subtype.val : ↑{z : ↑F.domain | F.func z ∈ C} → ↑F.domain)) β := by
  -- By definition of coRestrict, its domain is the set of elements in F's domain where F's value is in C.
  have h_domain : (F.coRestrict C).domain = {z : F.domain | F.func z ∈ C} := by
    -- The domain of the corestriction is the set of elements in the original domain that map to elements in C.
    simp only [coRestrict];
    simp +decide [ ScatFun.restrict, Set.ext_iff ];
  convert CBLevel_homeomorph ( F.restrictEquiv { z : F.domain | F.func z ∈ C } ) ( ( F.func ∘ Subtype.val ) ) β |> Eq.symm using 1;
  · convert CBLevel_homeomorph ( F.restrictEquiv { z : F.domain | F.func z ∈ C } ) ( ( F.func ∘ Subtype.val ) ) β using 1;
  · convert CBLevel_homeomorph ( F.restrictEquiv { z : F.domain | F.func z ∈ C } ) ( F.func ∘ Subtype.val ) β |> Eq.symm using 1;
    ext; simp [Homeomorph.image_symm]

/-
**CB-rank and top-level value of an isolating codomain-corestriction.**  If `C` is clopen,
`s ∈ C` is attained at the top level `λ` of `F` (rank `λ+1`), and `s` is the *only* top-level
value of `F` landing in `C`, then `coRestrict F C` again has rank `λ+1` and is constant `= s` on
its own top level.
-/
lemma coRestrict_isolated_rank_const (lam : Ordinal.{0})
    (F : ScatFun) (hFrank : CBRank F.func = lam + 1)
    (C : Set Baire) (hC : IsClopen C) (s : Baire) (hsC : s ∈ C)
    (htop : ∃ x, x ∈ CBLevel F.func lam ∧ F.func x = s)
    (hother : ∀ x, x ∈ CBLevel F.func lam → F.func x ∈ C → F.func x = s) :
    CBRank (coRestrict F C).func = lam + 1 ∧
      ∀ x ∈ CBLevel (coRestrict F C).func lam, (coRestrict F C).func x = s := by
  refine ⟨ le_antisymm ?_ ?_, ?_ ⟩;
  · refine' CBRank_le_of_CBLevel_empty _ _ _;
    have h_empty : CBLevel (F.func ∘ (Subtype.val : ↑{z : ↑F.domain | F.func z ∈ C} → ↑F.domain)) (lam + 1) = ∅ := by
      have h_empty : CBLevel F.func (lam + 1) = ∅ := by
        exact hFrank ▸ CBLevel_eq_empty_at_rank F.func F.hScat;
      have h_empty : Subtype.val '' CBLevel (F.func ∘ (Subtype.val : ↑{z : ↑F.domain | F.func z ∈ C} → ↑F.domain)) (lam + 1) = CBLevel F.func (lam + 1) ∩ {z : ↑F.domain | F.func z ∈ C} := by
        apply local_cb_derivative;
        exact F.hCont.isOpen_preimage _ hC.2;
      aesop;
    rw [ ScatFun.coRestrict_CBLevel_symm ];
    aesop;
  · refine le_of_not_gt fun h => ?_;
    obtain ⟨x, hx⟩ : ∃ x ∈ CBLevel F.func lam, F.func x = s := htop
    obtain ⟨hxS, hxlev⟩ : x ∈ {z : ↑F.domain | F.func z ∈ C} ∧ x ∈ CBLevel F.func lam := by
      aesop;
    have h_image : (F.restrictEquiv {z : ↑F.domain | F.func z ∈ C}).symm ⟨x, hxS⟩ ∈ CBLevel (F.coRestrict C).func lam := by
      rw [ coRestrict_CBLevel_symm ];
      have h_image : Subtype.val '' CBLevel (F.func ∘ (Subtype.val : ↑{z : ↑F.domain | F.func z ∈ C} → ↑F.domain)) lam = CBLevel F.func lam ∩ {z : ↑F.domain | F.func z ∈ C} := by
        apply local_cb_derivative;
        exact F.hCont.isOpen_preimage _ hC.2;
      exact h_image.symm.subset ⟨ hxlev, hxS ⟩ |> fun ⟨ y, hy, hy' ⟩ => by aesop;
    have h_image : CBLevel (F.coRestrict C).func lam ⊆ CBLevel (F.coRestrict C).func (CBRank (F.coRestrict C).func) := by
      exact CBLevel_antitone _ ( by aesop );
    have := CBLevel_eq_empty_at_rank ( F.coRestrict C ).func ( F.coRestrict C ).hScat; simp_all +decide [ Set.subset_def ] ;
    exact h_image _ _ ‹_›;
  · intro x hx;
    obtain ⟨ z, hzS, rfl ⟩ := (ScatFun.coRestrict_CBLevel_symm F C lam).subset hx;
    have hz_level : z.val ∈ CBLevel F.func lam := by
      have hz_level : Subtype.val '' CBLevel (F.func ∘ (Subtype.val : ↑{z | F.func z ∈ C} → ↑F.domain)) lam = CBLevel F.func lam ∩ {z | F.func z ∈ C} := by
        apply local_cb_derivative;
        exact hC.2.preimage F.hCont;
      exact hz_level.subset ( Set.mem_image_of_mem _ hzS ) |>.1;
    convert hother _ hz_level z.2 using 1

/-- **General regrouping lemma.**  If `(Q k)` is a countable clopen partition of a space `X`
(pairwise disjoint, covering), then for any index map `t : ℕ → ℕ` and any target `n`, the
sub-union of the pieces sent to `n` is again clopen.  (Open because it is a union of open sets;
closed because its complement is the union of the *other* clopen pieces, which is open since the
`Q k` cover `X`.)  Moved here (from `LambdaPlusOne.lean`) since it's needed again, lam-agnostically,
by `ScatFun.IsDisjointUnion.regroup` below. -/
lemma clopen_regroup {X : Type*} [TopologicalSpace X] (Q : ℕ → Set X)
    (hcl : ∀ k, IsClopen (Q k)) (hdis : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hcov : ⋃ k, Q k = Set.univ)
    (t : ℕ → ℕ) (n : ℕ) :
    IsClopen (⋃ k ∈ {k | t k = n}, Q k) := by
  refine ⟨?_, isOpen_biUnion (fun k _ => (hcl k).isOpen)⟩
  rw [← isOpen_compl_iff]
  have hcompl : (⋃ k ∈ {k | t k = n}, Q k)ᶜ = ⋃ k ∈ {k | t k ≠ n}, Q k := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_exists,
      not_and]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
      exact ⟨k, fun hkn => hx k hkn hk, hk⟩
    · rintro ⟨k, hkn, hk⟩ k' hk'n hk'
      exact absurd (Set.disjoint_left.mp (hdis k' k (fun h => hkn (h ▸ hk'n))) hk' hk) not_false
  rw [hcompl]
  exact isOpen_biUnion (fun k _ => (hcl k).isOpen)

/-- **Regrouping a disjoint union along an index map.**  If `A` is a disjoint union for `F` and
`t : ℕ → ℕ` sends each block-index to a new one, then re-collecting the blocks by their `t`-image
is again a disjoint union for `F` (the "coarsened" partition indexed by the image). Used to
regroup the fine per-block partition `A` into the coarser per-`P'`-class partition
`A' i = ⋃ n ∈ P' i, A n` at `case_N1_finite_nonempty_subcase_b`. -/
lemma IsDisjointUnion.regroup (F : ScatFun) (A : ℕ → Set ↑F.domain) (hdu : F.IsDisjointUnion A)
    (t : ℕ → ℕ) :
    F.IsDisjointUnion (fun i => ⋃ k ∈ {k | t k = i}, A k) := by
  refine ⟨fun i => clopen_regroup A hdu.1 hdu.2.1 hdu.2.2 t i, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro x hx hx'
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨k', hk', hxk'⟩ := Set.mem_iUnion₂.mp hx'
    simp only [Set.mem_setOf_eq] at hk hk'
    have hkk' : k ≠ k' := fun h => hij (by rw [← hk, ← hk', h])
    exact (Set.disjoint_left.mp (hdu.2.1 k k' hkk') hxk) hxk'
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ k, A k := by rw [hdu.2.2]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨t k, Set.mem_biUnion rfl hk⟩

end ScatFun

end
