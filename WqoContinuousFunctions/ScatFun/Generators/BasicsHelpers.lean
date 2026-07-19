import WqoContinuousFunctions.ScatFun.Generators.Defs
import WqoContinuousFunctions.ScatFun.LevelsFinitelyGenerated.Two
import WqoContinuousFunctions.ScatFun.Wedge.UpperBound
import WqoContinuousFunctions.ScatFun.Wedge.LowerBound
import WqoContinuousFunctions.ScatFun.Wedge.Monotone
import WqoContinuousFunctions.CenteredFunctions.Finiteness
import WqoContinuousFunctions.ScatFun.PreciseStructure.IntertwineOmegaCentered

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Infrastructure lemmas for `Generators/Basics.lean`

Reusable combinatorial facts about `omega`, `gl`, `glList` and `wedge` used to discharge the
three basic facts on generators (items 4–6 of the memoir's `BasicsOnGenerators`).
-/

namespace ScatFun

/-
**`ω` is idempotent** up to continuous equivalence: `ω (ω c) ≡ ω c`.  `ω (ω c)` is a gluing
of gluings of `c`; flattening the double index `ℕ × ℕ ≃ ℕ` (`gl_gl_flatten_equiv`) turns it into
a single gluing of `c`, i.e. `ω c`.
-/
lemma omega_omega_equiv (c : ScatFun) : Equiv (omega (omega c)) (omega c) := by
  -- To prove `ScatFun.Equiv (ScatFun.omega (ScatFun.omega c)) (ScatFun.omega c)`,
  -- unfold the definitions `omega := gl (fun _ => _)` and use `gl_gl_flatten_equiv`
  -- to reindex `ℕ × ℕ` as `ℕ`.
  unfold ScatFun.omega
  exact gl_gl_flatten_equiv (fun _ _ => c)

/-
A member of a list reduces into its list-gluing: `w ∈ L → Reduces w (glList L)`.  `w` is one
of the blocks `L.getD i empty` of `glList L = gl (fun k => L.getD k empty)`, and a block reduces
into its gluing (`reduces_block_gl`).
-/
lemma mem_reduces_glList {w : ScatFun} {L : List ScatFun} (h : w ∈ L) :
    Reduces w (glList L) := by
  rw [ List.mem_iff_get ] at h;
  obtain ⟨ n, rfl ⟩ := h;
  convert ScatFun.reduces_block_gl ( fun k => L.getD k empty ) n using 1;
  simp +zetaDelta at *

/-- If every block of a plain gluing reduces to `g`, the whole gluing reduces to `ω g`.
Pointwise reduction `gl F → gl (fun _ => g) = ω g` via `gl_reduces_of_pointwise`. -/
lemma gl_reduces_omega_of_forall {F : ℕ → ScatFun} {g : ScatFun}
    (h : ∀ i, Reduces (F i) g) : Reduces (gl F) (omega g) :=
  gl_reduces_of_pointwise F (fun _ => g) h

/-
If every block of a list reduces to `g`, its list-gluing reduces to `ω g`.  Blocks past the
length of `L` are `empty`, which reduces to anything.
-/
lemma glList_reduces_omega_of_forall {L : List ScatFun} {g : ScatFun}
    (h : ∀ w ∈ L, Reduces w g) : Reduces (glList L) (omega g) := by
  convert gl_reduces_omega_of_forall _;
  intro i; by_cases hi : i < L.length <;> simp_all +decide ;
  exact empty_reduces g

/-- **The wedge reduces to the plain gluing of its domain family.**  `wedge v d` is `retag n`
post-composed onto `(gl (wedgeDomFamily v d)).func`, and `retag n` is continuous on the range
(`retag_continuousOn_range`), so `wedge v d ≤ gl (wedgeDomFamily v d)` via `σ = id`,
`τ = retag n`.  (The reverse fails: `retag` merges the vertical base points.) -/
lemma wedge_reduces_gl_wedgeDomFamily {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) :
    Reduces (wedge v d) (gl (wedgeDomFamily v d)) := by
  refine' ⟨id, continuous_id, retag n, _, fun x => rfl⟩
  simpa using retag_continuousOn_range v d

/-- **The diagonal column reduces into the wedge.**  `ω d` continuously reduces to `wedge v d`.
Each diagonal slot `n + k` of `gl (wedgeDomFamily v d)` is `d`; the map `σ (k)⌢z := prepend (n+k) z`
lands in a diagonal slab, `wedge`'s value is `retag`-of-the-diagonal-value, inverted by
`τ := (unprepend ∘ wUntag n)` (`wUntag_retag_diagonal`). -/
lemma omega_diag_reduces_wedge {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) :
    Reduces (omega d) (wedge v d) := by
  have hd : ∀ x : ↥(omega d).domain, unprepend x.val ∈ d.domain := by
    intro x
    obtain ⟨j, hj0, hjmem⟩ := GluingSet_inverse_short (fun _ => d.domain) x
    simpa using hjmem
  have hmem : ∀ x : ↥(omega d).domain,
      prepend (n + x.val 0) (unprepend x.val) ∈ (wedge v d).domain := by
    intro x
    have h1 : unprepend x.val ∈ (wedgeDomFamily v d (n + x.val 0)).domain := by
      rw [wedgeDomFamily_diag v d (n + x.val 0) (by omega)]; exact hd x
    exact mem_gluingSet_prepend h1
  -- The recovery map `τ = G ∘ wUntag n`.
  set G : Baire → Baire := fun u => prepend (u 0 - n) (unprepend u) with hG
  have hGcont : Continuous G := by
    refine continuous_pi (fun j => ?_)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h0 : (fun u : Baire => G u 0) = fun u => u 0 - n := by
        funext u; simp [hG, prepend]
      rw [h0]
      exact (continuous_of_discreteTopology (f := fun m : ℕ => m - n)).comp (continuous_apply 0)
    · have hj0 : j ≠ 0 := hj.ne'
      have hidx : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
      have hjj : (fun u : Baire => G u j) = fun u => u j := by
        funext u; simp only [hG, prepend, unprepend, if_neg hj0, hidx]
      rw [hjj]; exact continuous_apply j
  -- The value of the wedge on the image of `σ`.
  have hval : ∀ x : ↥(omega d).domain,
      (wedge v d).func ⟨prepend (n + x.val 0) (unprepend x.val), hmem x⟩
        = prependZerosOne (x.val 0) (prepend n (d.func ⟨unprepend x.val, hd x⟩)) :=
    fun x => wedge_func_diagonal v d (x.val 0) ⟨unprepend x.val, hd x⟩ (hmem x)
  have hne : Set.range ((wedge v d).func ∘
      fun x : ↥(omega d).domain => (⟨prepend (n + x.val 0) (unprepend x.val), hmem x⟩ :
        ↥(wedge v d).domain)) ⊆ {w : Baire | w ≠ zeroStream} := by
    rintro _ ⟨x, rfl⟩
    simp only [Function.comp_apply, hval x, Set.mem_setOf_eq]
    intro hcontra
    have := congr_fun hcontra (x.val 0)
    simp [prependZerosOne, zeroStream] at this
  refine ⟨fun x => ⟨prepend (n + x.val 0) (unprepend x.val), hmem x⟩, ?_,
    G ∘ wUntag n, ?_, ?_⟩
  · -- continuity of `σ`
    refine Continuous.subtype_mk (continuous_pi (fun j => ?_)) _
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h0 : (fun x : ↥(omega d).domain => prepend (n + x.val 0) (unprepend x.val) 0)
          = fun x => n + x.val 0 := by funext x; simp [prepend]
      rw [h0]
      exact (continuous_of_discreteTopology (f := fun m : ℕ => n + m)).comp
        ((continuous_apply 0).comp continuous_subtype_val)
    · have hj0 : j ≠ 0 := hj.ne'
      have hidx : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
      have hjj : (fun x : ↥(omega d).domain => prepend (n + x.val 0) (unprepend x.val) j)
          = fun x => x.val j := by
        funext x; simp only [prepend, unprepend, if_neg hj0, hidx]
      rw [hjj]; exact (continuous_apply j).comp continuous_subtype_val
  · -- continuity of `τ = G ∘ wUntag n` on the range
    exact hGcont.comp_continuousOn (wUntag_continuousOn.mono hne)
  · -- the reduction equation
    intro x
    show (omega d).func x = (G ∘ wUntag n) ((wedge v d).func _)
    simp only [Function.comp_apply, hval x,
      wUntag_retag_diagonal n (x.val 0) (d.func ⟨unprepend x.val, hd x⟩)]
    have hox : (omega d).func x
        = prepend (x.val 0) (d.func ⟨unprepend x.val, hd x⟩) := by
      have h := omega_func_prepend d (x.val 0) ⟨unprepend x.val, hd x⟩
      have hx : x = ⟨prepend (x.val 0) (unprepend x.val), mem_gluingSet_prepend (hd x)⟩ :=
        Subtype.ext (prepend_unprepend x.val).symm
      rw [hx]; exact h
    rw [hox, hG]
    have h0 : (prepend (n + x.val 0) (d.func ⟨unprepend x.val, hd x⟩)) 0 = n + x.val 0 := by
      simp [prepend]
    simp only [h0, Nat.add_sub_cancel_left, unprepend_prepend]

/-- **A vertical column reduces into the wedge.**  The `j`-th vertical column
`pgl (fun _ => v j)` continuously reduces to `wedge v d`: it is exactly slot `j` of the wedge
domain, on which the wedge acts by `retag n ∘ prepend j`, injective on pointed-gluing values.

Proof via `pgl_reduces_of_local` (which handles continuity at the pointed-gluing base internally):
to reduce the column into `wedge v d`, place each column block, at pgl-depth `M`, into slot `j`
(`z ↦ prepend j (prependZerosOne M z)`); the wedge value there is `(0)^M (1)(j)⌢((v j).func z)`,
from which `(v j).func z` is recovered by `unprepend ∘ stripZerosOne M`.  Choosing `M` large (via
`nbhd_basis'`) keeps the images inside any prescribed neighbourhood of the base point
`x = (j)⌢0^ω`, and every image has coordinate `M` equal to `1`, so `0^ω = (wedge v d).func x` is
not in their closure. -/
lemma column_reduces_wedge {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) (j : Fin n) :
    Reduces (pgl (fun _ : ℕ => v j)) (wedge v d) := by
  -- The slot-`j` base point, which the wedge sends to `0^ω`.
  have hxmem : prepend j.val zeroStream ∈ (wedge v d).domain := by
    apply mem_gluingSet_prepend (i := j.val)
    rw [wedgeDomFamily_vertical v d j]
    exact zeroStream_mem_pointedGluingSet _
  refine pgl_reduces_of_local (fun _ : ℕ => v j) (wedge v d)
    ⟨prepend j.val zeroStream, hxmem⟩ ?_
  intro i V hVopen hxV
  -- A depth `M` with the `M`-cylinder around the base point inside `V`.
  obtain ⟨M, hMV⟩ :=
    nbhd_basis' (wedge v d).domain ⟨prepend j.val zeroStream, hxmem⟩ V hVopen hxV
  -- Block membership in slot `j` at depth `M`.
  have hblk : ∀ z : ↥(v j).domain,
      prepend j.val (prependZerosOne M z.val) ∈ (wedge v d).domain := by
    intro z
    apply mem_gluingSet_prepend (i := j.val)
    rw [wedgeDomFamily_vertical v d j]
    exact prependZerosOne_mem_pointedGluingSet (fun _ => (v j).domain) M z.val z.2
  refine ⟨fun z => ⟨prepend j.val (prependZerosOne M z.val), hblk z⟩,
    fun w => unprepend (stripZerosOne M w), ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `σ`
    exact ((continuous_prepend j.val).comp
      ((continuous_prependZerosOne M).comp continuous_subtype_val)).subtype_mk _
  · -- the reduction equation
    intro z
    show (v j).func z
        = unprepend (stripZerosOne M ((wedge v d).func
            ⟨prepend j.val (prependZerosOne M z.val), hblk z⟩))
    rw [wedge_func_vertical_block v d j M z (hblk z), stripZerosOne_prependZerosOne,
      unprepend_prepend]
  · -- continuity of `τ` on the range
    exact (continuous_unprepend.comp (continuous_stripZerosOne M)).continuousOn
  · -- images stay in `V`
    intro z
    apply hMV
    intro c hc
    rw [Finset.mem_range] at hc
    show prepend j.val (prependZerosOne M z.val) c = prepend j.val zeroStream c
    by_cases hc0 : c = 0
    · subst hc0; rfl
    · simp only [prepend, if_neg hc0]
      show prependZerosOne M z.val (c - 1) = 0
      exact prependZerosOne_head_eq_zero M z.val (c - 1) (by omega)
  · -- `0^ω = (wedge v d).func x` is not in the closure of the images
    have hsub : Set.range (fun z : ↥(v j).domain =>
        (wedge v d).func ⟨prepend j.val (prependZerosOne M z.val), hblk z⟩)
          ⊆ {w : Baire | w M = 1} := by
      rintro _ ⟨z, rfl⟩
      show (wedge v d).func _ M = 1
      rw [wedge_func_vertical_block v d j M z (hblk z)]
      exact prependZerosOne_at_i M _
    have hclosed : IsClosed {w : Baire | w M = 1} :=
      isClosed_eq (continuous_apply M) continuous_const
    rw [wedge_func_vertical_base v d j hxmem]
    intro hmem
    have : zeroStream ∈ {w : Baire | w M = 1} := hclosed.closure_subset_iff.mpr hsub hmem
    simp [zeroStream] at this

/-
**The gluing of the wedge domain family reduces to the gluing of its columns.**  Pure
gluing combinatorics (no `retag`): `gl (wedgeDomFamily v d)` has slots `i < n` equal to the
columns `pgl (fun _ => v i)` and slots `≥ n` equal to `d`; regrouping the columns into the first
factor `glList (List.ofFn columns)` and the `ω`-many diagonals into `ω d` gives the bound.
-/
lemma gl_wedgeDomFamily_reduces_glBin_columns {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) :
    Reduces (gl (wedgeDomFamily v d))
      (glBin (glList (List.ofFn (fun i => pgl (fun _ => v i)))) (omega d)) := by
  -- Let `cols k := (List.ofFn (fun i : Fin n => pgl (fun _ => v i))).getD k empty`, so `A := glList (List.ofFn (fun i => pgl (fun _ => v i))) = gl cols`, and `B := omega d = gl (fun _ => d)`.
  set cols : ℕ → ScatFun := fun k => (List.ofFn (fun i : Fin n => pgl (fun _ => v i))).getD k ScatFun.empty
  set A : ScatFun := gl cols
  set B : ScatFun := omega d;
  -- By `finGl_glBin_equiv_glList A B : Equiv (A ⊕ B) (glList [A,B])`, we have `Reduces (glBin A B) (gl (wedgeDomFamily v d))`.
  have h_equiv : Equiv (A ⊕ B) (glList [A, B]) :=
    finGl_glBin_equiv_glList A B
  -- By `gl_reduces_of_blockEmbed` with reindexing `e i := if i < n then Nat.pair 0 i else Nat.pair 1 (i - n)`, we have `Reduces (gl (wedgeDomFamily v d)) (gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2))`.
  have h_blockEmbed : Reduces (gl (wedgeDomFamily v d)) (gl (fun m => (if (Nat.unpair m).1 = 0 then cols (Nat.unpair m).2 else if (Nat.unpair m).1 = 1 then d else ScatFun.empty))) := by
    apply gl_reduces_of_blockEmbed (wedgeDomFamily v d) (fun m => if (Nat.unpair m).1 = 0 then cols (Nat.unpair m).2 else if (Nat.unpair m).1 = 1 then d else ScatFun.empty) (fun i => if i < n then Nat.pair 0 i else Nat.pair 1 (i - n)) (by
    intro i j; simp +decide;
    split_ifs <;> simp +decide;
    omega) (by
    intro i; by_cases hi : i < n <;> simp +decide [ hi ] ;
    · simp +decide [ cols, hi ];
      exact wedgeDomFamily_vertical v d ⟨ i, hi ⟩ ▸ ContinuouslyReduces.refl _;
    · convert wedgeDomFamily_diag v d ( i - n ) using 1;
      simp +decide only [wedgeDomFamily, hi, ↓reduceDIte, not_lt, dite_eq_right_iff];
      exact iff_of_true ( ContinuouslyReduces.refl _ ) ( by intros; omega ));
  -- By `gl_flat_reduces_gl_gl`, we have `Reduces (gl (fun m => H (Nat.unpair m).1 (Nat.unpair m).2)) (gl (fun i => gl (H i)))`.
  have h_flat_reduces_gl_gl : Reduces (gl (fun m => (if (Nat.unpair m).1 = 0 then cols (Nat.unpair m).2 else if (Nat.unpair m).1 = 1 then d else ScatFun.empty))) (gl (fun i => gl (fun k => (if i = 0 then cols k else if i = 1 then d else ScatFun.empty)))) := by
    convert ScatFun.gl_flat_reduces_gl_gl _ using 1;
    convert rfl;
  -- By `gl_reduces_of_pointwise`, we have `Reduces (gl (fun i => gl (H i))) (glBin A B)`.
  have h_pointwise : Reduces (gl (fun i => gl (fun k => (if i = 0 then cols k else if i = 1 then d else ScatFun.empty)))) (glBin A B) := by
    apply gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ copiesSeq ] ;
    · convert ContinuouslyReduces.refl _;
    · convert ContinuouslyReduces.refl _ using 1;
    · exact gl_reduces_single (fun k => empty) n fun j => congrFun rfl;
  convert h_blockEmbed.trans ( h_flat_reduces_gl_gl.trans ( h_pointwise.trans h_equiv.1 ) ) using 1

/-- **The wedge is bounded above by the gluing of its columns.**  `wedge v d` reduces to the
binary gluing of the finite gluing of its vertical columns and `ω d`. -/
lemma wedge_reduces_glBin_columns {n : ℕ} (v : Fin n → ScatFun) (d : ScatFun) :
    Reduces (wedge v d)
      (glBin (glList (List.ofFn (fun i => pgl (fun _ => v i)))) (omega d)) :=
  (wedge_reduces_gl_wedgeDomFamily v d).trans (gl_wedgeDomFamily_reduces_glBin_columns v d)

/-! ## Generic `gl`/`omega`/`glList`/`pglFinset` algebra

Moved here from `Generators/Basics.lean`: pure gluing-combinator facts with no reference to
`Centered`/`Generators`, so they belong with the rest of this file's reusable infrastructure
rather than in the file whose specific job is the `Centered`-transport argument. -/

/-- A plain gluing of all-`empty` blocks is equivalent to `empty`. -/
lemma gl_equiv_empty_of_forall_empty {h : ℕ → ScatFun} (hh : ∀ k, h k = empty) :
    Equiv (gl h) empty := by
  have h_domain_empty : IsEmpty (gl h).domain := by
    constructor;
    rintro ⟨ x, hx ⟩;
    cases hx;
    simp_all +decide [ empty ];
    aesop;
  exact ⟨reduces_of_isEmpty_domain h_domain_empty, empty_reduces (gl h)⟩

/-
**`ω` distributes over a binary gluing.**  `ω (a ⊕ b) ≡ (ω a) ⊕ (ω b)`.  (Regroup the
`ω`-many copies of `a ⊕ b` by which of the two slots each block occupies.)
-/
lemma omega_glBin_equiv (a b : ScatFun) :
    Equiv (omega (a ⊕ b)) ((omega a) ⊕ (omega b)) := by
  have h_equiv : Equiv (gl (fun _ => glBin a b)) (gl (fun m => if m.unpair.2 = 0 then a else if m.unpair.2 = 1 then b else empty)) ∧ Equiv (gl (fun _ => a) ⊕ gl (fun _ => b)) (gl (fun m => if m.unpair.1 = 0 then a else if m.unpair.1 = 1 then b else empty)) := by
    constructor;
    · have h_equiv : Equiv (gl (fun _ => glList [a, b])) (gl (fun m => if m.unpair.2 = 0 then a else if m.unpair.2 = 1 then b else empty)) := by
        convert ScatFun.gl_gl_flatten_equiv _ using 1;
        grind;
      convert h_equiv using 1;
    · apply Equiv.trans;
      apply finGl_glBin_equiv_glList;
      convert gl_gl_flatten_equiv _ using 1;
      rotate_right;
      exact fun i k => if i = 0 then a else if i = 1 then b else empty;
      · unfold glList;
        congr! 2;
        rename_i k; rcases k with ( _ | _ | k ) <;> simp +decide ;
        unfold empty;
        congr! 1;
        · simp +decide [ GluingSet ];
        · congr! 1; all_goals grind;
      · rfl;
  convert h_equiv.1.trans _ |> Equiv.trans <| h_equiv.2.symm using 1;
  refine ⟨ ?_, ?_ ⟩;
  · convert ScatFun.gl_reindex _ _ _ using 1;
    rotate_left;
    exact fun m => Nat.pair ( Nat.unpair m |>.2 ) ( Nat.unpair m |>.1 );
    · intro m n hmn;
      exact Nat.pair_unpair m ▸ Nat.pair_unpair n ▸ by aesop;
    · simp +decide [ Nat.unpair_pair ];
  · convert ScatFun.gl_reindex _ _ _ using 1;
    rotate_left;
    exact fun m => Nat.pair ( Nat.unpair m |>.2 ) ( Nat.unpair m |>.1 );
    · exact fun m n h => by simpa using congr_arg ( fun m => Nat.unpair m |>.2.pair ( Nat.unpair m |>.1 ) ) h;
    · simp +decide [ Nat.unpair_pair ]

/-- **`ω` distributes over a finite gluing.**  `ω (glList L)` is continuously equivalent to the
finite gluing of the `ω`-images of the blocks of `L`.  (Regroup the `ω`-many copies of
`a_1 ⊕ … ⊕ a_p` by block index: the copies of block `i` form `ω a_i`.) -/
lemma omega_glList_equiv_glList_omega (L : List ScatFun) :
    Equiv (omega (glList L)) (glList (L.map omega)) := by
  induction L with
  | nil =>
    have hnil : Equiv (glList ([] : List ScatFun)) empty :=
      gl_equiv_empty_of_forall_empty (fun _ => rfl)
    have homeg : Equiv (omega empty) empty :=
      gl_equiv_empty_of_forall_empty (fun _ => rfl)
    simpa using ((omega_equiv_congr hnil).trans homeg).trans hnil.symm
  | cons a L' ih =>
    have e1 : Equiv (glList (a :: L')) (a ⊕ glList L') := by
      simpa using
        (glList_append_equiv [a] L').trans
          (glBin_congr (glList_single_equiv a).symm (Equiv.refl _))
    have step : Equiv (omega (glList (a :: L'))) ((omega a) ⊕ glList (L'.map omega)) :=
      (omega_equiv_congr e1).trans
        ((omega_glBin_equiv a (glList L')).trans
          (glBin_congr (Equiv.refl (omega a)) ih))
    have e2 : Equiv ((omega a) ⊕ glList (L'.map omega)) (glList (omega a :: L'.map omega)) := by
      simpa using
        (glBin_congr (glList_single_equiv (omega a)) (Equiv.refl (glList (L'.map omega)))).trans
          (glList_append_equiv [omega a] (L'.map omega)).symm
    simpa using step.trans e2

/-
**Binary gluing of two column-gluings as a nested gluing.**  The infinite-family analogue of
`glBin_glList_equiv_gl_gl`: `(gl A) ⊕ (gl B)` is equivalent to the nested gluing whose `0`-th
column is `A`, whose `1`-st column is `B`, and whose remaining columns are empty.
-/
lemma glBin_gl_equiv_gl_gl (A B : ℕ → ScatFun) :
    Equiv (glBin (gl A) (gl B))
      (gl (fun i => gl (fun k => if i = 0 then A k else if i = 1 then B k else empty))) := by
  constructor;
  · apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ copiesSeq ] ;
    · convert ScatFun.Equiv.refl _ |>.1 using 1;
    · convert ScatFun.Equiv.refl _ |>.1 using 1;
    · convert ScatFun.empty_reduces _ using 1;
  · apply ScatFun.gl_reduces_of_pointwise;
    intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ ScatFun.copiesSeq ] ;
    · convert ScatFun.Equiv.refl _ |>.1 using 1;
    · convert ScatFun.Equiv.refl _ |>.1 using 1;
    · exact gl_reduces_single (fun _ => empty) i (fun j => congrFun rfl)

/-- **Splitting a plain gluing along a predicate.**  `gl h` is equivalent to the binary gluing of
its `p`-indicator sub-gluing and its complementary sub-gluing. -/
lemma gl_split_predicate (p : ℕ → Prop) (h : ℕ → ScatFun) :
    Equiv (gl h)
      ((gl (fun k => if p k then h k else empty)) ⊕
        (gl (fun k => if p k then empty else h k))) := by
  classical
  set A : ℕ → ScatFun := fun k => if p k then h k else empty with hA
  set B : ℕ → ScatFun := fun k => if p k then empty else h k with hB
  set Φ : ℕ → ScatFun :=
    fun m => if (Nat.unpair m).1 = 0 then A (Nat.unpair m).2
      else if (Nat.unpair m).1 = 1 then B (Nat.unpair m).2 else empty with hΦ
  have hRHS : Equiv (glBin (gl A) (gl B)) (gl Φ) :=
    (glBin_gl_equiv_gl_gl A B).trans
      (gl_gl_flatten_equiv (fun i k => if i = 0 then A k else if i = 1 then B k else empty))
  have hval1 : ∀ k, Φ (Nat.pair (if p k then 0 else 1) k) = h k := by
    intro k
    by_cases hpk : p k <;> simp [hΦ, hA, hB, Nat.unpair_pair, hpk]
  have hfwd : Reduces (gl h) (gl Φ) := by
    refine gl_reduces_of_blockEmbed_support h Φ (fun k => Nat.pair (if p k then 0 else 1) k) ?_ ?_
    · intro k1 _ k2 _ hk
      have := congrArg (fun m => (Nat.unpair m).2) hk
      simpa [Nat.unpair_pair] using this
    · intro k _
      rw [hval1 k]
      exact (Equiv.refl (h k)).1
  have hclass : ∀ m, (Φ m).domain.Nonempty →
      (Nat.unpair m).1 = (if p (Nat.unpair m).2 then 0 else 1) ∧ Φ m = h (Nat.unpair m).2 := by
    intro m hm
    by_cases h0 : (Nat.unpair m).1 = 0
    · by_cases hpk : p (Nat.unpair m).2
      · exact ⟨by simp [h0, hpk], by simp [hΦ, hA, h0, hpk]⟩
      · exfalso; simp [hΦ, hA, h0, hpk, empty] at hm
    · by_cases h1 : (Nat.unpair m).1 = 1
      · by_cases hpk : p (Nat.unpair m).2
        · exfalso; simp [hΦ, hB, h1, hpk, empty] at hm
        · exact ⟨by simp [h1, hpk], by simp [hΦ, hB, h1, hpk]⟩
      · exfalso; simp [hΦ, h0, h1, empty] at hm
  have hbwd : Reduces (gl Φ) (gl h) := by
    refine gl_reduces_of_blockEmbed_support Φ h (fun m => (Nat.unpair m).2) ?_ ?_
    · intro m1 hm1 m2 hm2 hk
      obtain ⟨he1, _⟩ := hclass m1 hm1
      obtain ⟨he2, _⟩ := hclass m2 hm2
      have hk2 : (Nat.unpair m1).2 = (Nat.unpair m2).2 := hk
      have hk1 : (Nat.unpair m1).1 = (Nat.unpair m2).1 := by rw [he1, he2, hk2]
      calc m1 = Nat.pair (Nat.unpair m1).1 (Nat.unpair m1).2 := (Nat.pair_unpair m1).symm
        _ = Nat.pair (Nat.unpair m2).1 (Nat.unpair m2).2 := by rw [hk1, hk2]
        _ = m2 := Nat.pair_unpair m2
    · intro m hm
      obtain ⟨_, hval⟩ := hclass m hm
      rw [hval]
      exact (Equiv.refl (h (Nat.unpair m).2)).1
  exact (show Equiv (gl h) (gl Φ) from ⟨hfwd, hbwd⟩).trans hRHS.symm

/-
**An indicator gluing over an infinite index set collapses to `ω`.**  If `{k | p k}` is
infinite, the gluing that is `s` on `p` and `empty` off `p` is equivalent to `ω s`.
-/
lemma gl_indicator_infinite_equiv_omega (s : ScatFun) (p : ℕ → Prop)
    (hinf : {k | p k}.Infinite) :
    Equiv (gl (fun k => if p k then s else empty)) (omega s) := by
  obtain ⟨e, he_inj, he_mem⟩ : ∃ e : ℕ → ℕ, Function.Injective e ∧ ∀ j, p (e j) := by
    exact ⟨ fun j => Nat.nth ( fun k => p k ) j, Nat.nth_injective hinf, fun j => Nat.nth_mem_of_infinite hinf _ ⟩;
  refine ⟨ ?_, ?_ ⟩;
  · apply gl_reduces_of_pointwise;
    intro i; by_cases hi : p i <;> simp +decide [ hi ] ;
    · constructor;
      exact ⟨ continuous_id, id, continuousOn_id, fun x => rfl ⟩;
    · exact empty_reduces s;
  · convert ScatFun.gl_reindex ( fun k => if p k then s else empty ) e he_inj using 1;
    aesop

/-- **Blockwise monotonicity of `glList` on equal-length `List.ofFn` lists.**  If `f i ≤ g i`
for every `i : Fin n`, then `glList (List.ofFn f) ≤ glList (List.ofFn g)`.  A plain index-`id`
block embed: repeats among the `g i` are irrelevant since the two lists are aligned slot for
slot (this replaces the earlier, unsound "absorbing collapse" — reducing repeated targets onto a
single de-duplicated block would require the false `ω x ≤ x`; here no collapse happens). -/
lemma glList_reduces_glList_ofFn {n : ℕ} (f g : Fin n → ScatFun)
    (h : ∀ i, Reduces (f i) (g i)) :
    Reduces (glList (List.ofFn f)) (glList (List.ofFn g)) := by
  show Reduces (gl (fun k => (List.ofFn f).getD k empty))
    (gl (fun k => (List.ofFn g).getD k empty))
  refine gl_reduces_of_pointwise _ _ (fun k => ?_)
  by_cases hk : k < n
  · have hf : (List.ofFn f).getD k empty = f ⟨k, hk⟩ := by
      rw [List.getD_eq_getElem, List.getElem_ofFn]; simpa using hk
    have hg : (List.ofFn g).getD k empty = g ⟨k, hk⟩ := by
      rw [List.getD_eq_getElem, List.getElem_ofFn]; simpa using hk
    rw [hf, hg]; exact h ⟨k, hk⟩
  · have hf : (List.ofFn f).getD k empty = empty := by
      rw [List.getD_eq_default]; simpa using hk
    have hg : (List.ofFn g).getD k empty = empty := by
      rw [List.getD_eq_default]; simpa using hk
    rw [hf, hg]; exact ContinuouslyReduces.refl _

/-
**`pglFinset` as an honest `pgl` with `ω` copies of every block.**  For a nonempty `F`,
the pointed gluing `pglFinset F = pgl (fun _ => glList F.toList)` is continuously equivalent to
`pgl (repSeq F.toFinFun)`, which lists every block of `F` infinitely often.  Both directions are
`finitegenerationAndPgluing_upper`/`_lower`.
-/
lemma pglFinset_equiv_pgl_repSeq (F : Finset ScatFun) :
    Equiv (pglFinset F) (pgl (repSeq F.toFinFun)) := by
  have h_upper : Reduces (pglFinset F) (pgl (repSeq F.toFinFun)) := by
    apply ScatFun.finitegenerationAndPgluing_upper F.toFinFun (fun _ => glList F.toList);
    intro i;
    have h_glList_in_FinGl : glList F.toList ∈ FinGl F.toFinFun := by
      have h_glb : glList F.toList = Gl F.toFinFun (fun _ => 1) := by
        unfold Gl;
        unfold copiesSeq;
        unfold copiesList; simp +decide [ List.flatMap ] ;
        have h_glb : List.map (fun i => F.toFinFun i) (List.finRange F.card) = F.toList := by
          refine List.ext_get ?_ ?_ <;> aesop;
        rw [ ← h_glb ];
        congr;
        induction ( List.finRange F.card ) <;> aesop
      use fun _ => 1;
      exact ⟨ h_glb ▸ ContinuouslyReduces.refl _, h_glb ▸ ContinuouslyReduces.refl _ ⟩;
    exact ⟨ _, h_glList_in_FinGl, ContinuouslyReduces.refl _ ⟩
  have h_lower : Reduces (pgl (repSeq F.toFinFun)) (pglFinset F) := by
    apply ScatFun.finitegenerationAndPgluing_lower;
    intro k i
    use i
    simp only [le_refl, true_and];
    convert ScatFun.mem_reduces_glList _;
    exact Finset.mem_toList.mpr ( Finset.mem_coe.mpr ( Finset.mem_coe.mpr ( Finset.mem_toList.mp ( List.getElem_mem _ ) ) ) )
  exact ⟨h_upper, h_lower⟩

/-
**Finite-generation transport of a pointed gluing.**  If every generator `g ∈ F` reduces to a
finite gluing of blocks of `F'`, and every block `x ∈ F'` reduces to some generator `g ∈ F`, then
`pglFinset F ≡ pglFinset F'`.  (Both sets are nonempty.)  This is the pointed-gluing transport
underlying the memoir's "replace each generator by its centered pieces" step; the `ω`-copy slack
of `pgl` lets the finitely-many pieces of each `g` be routed into distinct deep slots.
-/
lemma pglFinset_equiv_of_finGl {F F' : Finset ScatFun} (hF : F.Nonempty) (hF' : F'.Nonempty)
    (hfwd : ∀ g ∈ F, ∃ w ∈ FinGl F'.toFinFun, Reduces g w)
    (hrev : ∀ x ∈ F', ∃ g ∈ F, Reduces x g) :
    Equiv (pglFinset F) (pglFinset F') := by
  have hF'_nonempty : F'.Nonempty := by
    assumption
  have hF_nonempty : F.Nonempty := by
    assumption
  have h_repSeq_equiv : ScatFun.Equiv (ScatFun.pgl (ScatFun.repSeq F.toFinFun)) (ScatFun.pgl (ScatFun.repSeq F'.toFinFun)) := by
    apply And.intro;
    · apply ScatFun.finitegenerationAndPgluing_upper F'.toFinFun (ScatFun.repSeq F.toFinFun);
      intro i
      obtain ⟨g, hg⟩ : ∃ g ∈ F, ScatFun.repSeq F.toFinFun i = g := by
        unfold ScatFun.repSeq; simp +decide [ hF_nonempty ] ;
        exact Finset.mem_toList.mp ( List.getElem_mem _ )
      generalize_proofs at *;
      aesop;
    · apply ScatFun.finitegenerationAndPgluing_lower F'.toFinFun (ScatFun.repSeq F.toFinFun);
      intro k i; obtain ⟨ g, hg₁, hg₂ ⟩ := hrev ( F'.toFinFun k ) ( by
        exact Finset.mem_toList.mp ( List.getElem_mem _ ) ) ; (
      obtain ⟨ j, hj ⟩ := Finset.mem_image.mp ( show g ∈ Finset.image ( fun x : Fin F.card => F.toFinFun x ) Finset.univ from by
                                                  simp +decide only [Finset.mem_image, Finset.mem_univ, true_and];
                                                  have h_mem : g ∈ F.toList := by
                                                    exact Finset.mem_toList.mpr hg₁;
                                                  obtain ⟨ a, ha ⟩ := List.mem_iff_get.mp h_mem; use ⟨ a, by
                                                    simpa using a.2 ⟩ ; aesop; ) ; use j.val + i * F.card; simp_all +decide ;
      unfold repSeq; simp +decide [ *, Nat.mod_eq_of_lt ] ;
      nlinarith [ Fin.is_lt j, show F.card > 0 from Finset.card_pos.mpr hF_nonempty ]);
  have h_pgl_equiv : ScatFun.Equiv (ScatFun.pglFinset F) (ScatFun.pglFinset F') := by
    convert ScatFun.Equiv.trans ( ScatFun.pglFinset_equiv_pgl_repSeq F ) ( ScatFun.Equiv.trans h_repSeq_equiv ( ScatFun.pglFinset_equiv_pgl_repSeq F' |> ScatFun.Equiv.symm ) ) using 1
  exact h_pgl_equiv

/-
A finite gluing of blocks drawn from `F'` lies in `FinGl F'.toFinFun` (with multiplicities).
-/
lemma glList_mem_FinGl_of_subset (l : List ScatFun) (F' : Finset ScatFun)
    (h : ∀ x ∈ l, x ∈ F') : glList l ∈ FinGl F'.toFinFun :=
  finGl_glList_of_forall_mem h

end ScatFun

end