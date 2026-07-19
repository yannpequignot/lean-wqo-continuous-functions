import Mathlib.Data.List.GetD
import BQO.TwoBQO
import WqoContinuousFunctions.ScatFun.Operations

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

noncomputable section

/-!
# Finite gluings from a finite set of `ScatFun`s and their 2-BQO

Fix a finite sequence `B : Fin n → ScatFun` of scattered continuous functions.
For a tuple of multiplicities `t : Fin n → ℕ` we form the **finite gluing**
`Gl B t`, which glues `t i` copies of `B i` (for `i < n`).  The class

  `FinGl B := { f | f ≡ Gl B t for some t }`

is the set of `ScatFun`s equivalent to such a finite gluing.

## Main result

* `FinGl.isTwoBQO` — `ScatFun.Reduces` is a **2-BQO** on `FinGl B`.

## Proof strategy (matching the informal argument)

The argument is purely order-theoretic and is isolated in
`TwoBQO.monotone_image_equiv` (in `BQO/TwoBQO.lean`):

* `ℕⁿ` with the product order is 2-BQO — `TwoBQO.prodN`.
* `Gl B` is **monotone**: `t ≤ s` (pointwise) ⟹ `Gl B t ≤ Gl B s`
  (`Gl_mono` below).  Informally: if `t i ≤ s i` for every block, then the
  copies making up `Gl B t` form a sub-collection of those making up
  `Gl B s`, so the gluing on the left reduces (block-by-block, by the identity)
  into the gluing on the right.
* Any bad pair-sequence `φ` in `FinGl B` chooses, for each `k < l`, a tuple
  `t(k,l)` with `φ(k,l) ≡ Gl B t(k,l)`.  Since `ℕⁿ` is 2-BQO there are
  `k < l < m` with `t(k,l) ≤ t(l,m)`, hence `Gl B t(k,l) ≤ Gl B t(l,m)`, hence
  `φ(k,l) ≤ φ(l,m)` — contradicting badness.

The third bullet is exactly `comap` (pick the witness `t`) followed by `mono`
(chain through the equivalence and monotonicity), packaged once and for all in
`TwoBQO.monotone_image_equiv`.

## Implementation note — `Gl B t` is the plain gluing `ScatFun.gl`

`Gl B t` is the **plain** bundled gluing `ScatFun.gl` of the `ℕ`-indexed family
that lists `t i` copies of each `B i` and pads the (infinite) tail with the
trivial empty function `ScatFun.empty`.  The empty padding contributes no points
(`(i)⌢∅ = ∅`), so the domain of `Gl B t` is exactly the finite gluing
`⊔ᵢ (tᵢ copies of (B i).domain)` — matching the memoir's finite gluing with no
spurious base point.

`ScatFun.gl` inherits scatteredness/continuity from the plain-gluing
preservation lemmas (Fact 2.16: `gluingFun_scattered`,
`gluingFunVal_preserves_continuity`).
-/

namespace ScatFun


variable {n : ℕ} (B : Fin n → ScatFun) (t s : Fin n → ℕ)

/-- The list that spells out the blocks of the finite gluing: for each `i` in
order, `t i` copies of `B i`. -/
def copiesList : List ScatFun :=
  (List.finRange n).flatMap (fun i => List.replicate (t i) (B i))

/-- The `ℕ`-indexed family feeding `gl`: the `copiesList`, with the infinite
tail padded by `ScatFun.empty`. -/
def copiesSeq : ℕ → ScatFun :=
  fun k => (copiesList B t).getD k ScatFun.empty

/-- **Finite gluing** of `t i` copies of `B i` (`i < n`), as a `ScatFun`.

Realised as the plain gluing (`gl`) of `copiesSeq B t`; see the file-level
implementation note. -/
def Gl : ScatFun := gl (copiesSeq B t)


/-
**Monotonicity of `Gl B` in the multiplicities.**  If `t i ≤ s i` for every
block `i`, then `Gl B t` continuously reduces to `Gl B s`.

This is the single geometric input to the 2-BQO theorem.  Informally: `t ≤ s`
makes `copiesList B t` a sublist of `copiesList B s` (each `replicate (t i)`
block embeds into `replicate (s i)`), and a gluing reduces into any gluing whose
block family contains its blocks — block-by-block via the identity reduction
`B i ≤ B i`, packaged in `gl_reduces_of_blockEmbed`.
-/
theorem Gl_mono (h : ∀ i, t i ≤ s i) : Reduces (Gl B t) (Gl B s) := by
  obtain ⟨f, hf⟩ : ∃ f : Fin (List.length (List.flatMap (fun i => List.replicate (t i) (B i)) (List.finRange n))) ↪o Fin (List.length (List.flatMap (fun i => List.replicate (s i) (B i)) (List.finRange n))), ∀ ix, (List.flatMap (fun i => List.replicate (t i) (B i)) (List.finRange n)).get ix = (List.flatMap (fun i => List.replicate (s i) (B i)) (List.finRange n)).get (f ix) := by
    convert List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp _;
    convert List.Sublist.flatMap_right ( List.finRange n ) _;
    grind;
  convert gl_reduces_of_blockEmbed ( copiesSeq B t ) ( copiesSeq B s ) ( fun i => if hi : i < List.length ( List.flatMap ( fun i => List.replicate ( t i ) ( B i ) ) ( List.finRange n ) ) then ( f ⟨ i, hi ⟩ : ℕ ) else List.length ( List.flatMap ( fun i => List.replicate ( s i ) ( B i ) ) ( List.finRange n ) ) + ( i - List.length ( List.flatMap ( fun i => List.replicate ( t i ) ( B i ) ) ( List.finRange n ) ) ) ) ?_ ?_ using 1;
  · intro a b; simp +decide at *;
    split_ifs <;> simp_all +decide [ Fin.val_injective.eq_iff ];
    · intro h; have := f ⟨ a, by
        grind +locals ⟩ |>.2; simp_all +decide [ List.length_flatMap ] ;
    · intro h;
      contrapose! h;
      exact ne_of_gt ( lt_add_of_lt_of_nonneg ( Nat.lt_of_lt_of_le ( Fin.is_lt _ ) ( by simp ) ) ( Nat.zero_le _ ) );
    · omega;
  · intro i; by_cases hi : i < List.length ( List.flatMap ( fun i => List.replicate ( t i ) ( B i ) ) ( List.finRange n ) ) <;> simp +decide [ *, copiesSeq ] ;
    · convert ContinuouslyReduces.refl _ using 1;
      any_goals exact fun _ => 0;
      any_goals exact ℕ;
      any_goals try infer_instance;
      simp +decide only [copiesList];
      split_ifs <;> simp_all +decide;
      grind +suggestions;
    · convert empty_reduces _ using 1;
      grind +locals

/-- **Binary finite gluing** (memoir `\glbin`, e.g. `k_{λ+1} \gl ℓ_λ`): one copy each of `f`
and `g`. `abbrev` so that it stays reducible, letting `f ⊕ g` unfold transparently to
`Gl ![f, g] ![1, 1]` wherever the latter is expected (e.g. in existing proofs). -/
abbrev glBin (f g : ScatFun) : ScatFun := Gl ![f, g] ![1, 1]

@[inherit_doc] scoped infixl:65 " ⊕ " => ScatFun.glBin

/-- The class of `ScatFun`s **continuously equivalent to a finite gluing** from
`B`.  The membership predicate is phrased as a two-sided reduction so that it is
definitionally the subtype predicate of `TwoBQO.monotone_image_equiv`. -/
def FinGl : Set ScatFun :=
  fun f => ∃ t : Fin n → ℕ, Reduces (Gl B t) f ∧ Reduces f (Gl B t)

/-- **2-BQO of finite gluings.**  `ScatFun.Reduces` is a 2-BQO on `FinGl B`.

The proof is `TwoBQO.monotone_image_equiv` instantiated with the 2-BQO product
order on `ℕⁿ` (`TwoBQO.prodN`), the monotone map `Gl B` (`Gl_mono`), and the
preorder `ScatFun.Reduces`.  The subtype predicate produced by that lemma is
*definitionally* membership in `FinGl B`. -/
theorem FinGl.isTwoBQO :
    TwoBQO (fun a b : {f : ScatFun // f ∈ FinGl B} => Reduces a.val b.val) :=
  TwoBQO.monotone_image_equiv (TwoBQO.prodN n) (Gl B) (fun t s h => Gl_mono B t s h)

/-! ## Finite generation and pointed gluing (Prop. `FinitegenerationandPgluing`)

We relate the **pointed** gluing `pgl` with finite generation via `FinGl`.  The
finite set `F` of the memoir is rendered as `B : Fin n → ScatFun`, and the
pointed gluing `⊔ F` as `pgl (repSeq B)`, where `repSeq B` lists every generator
block infinitely often (period `n`). -/

/-- The finite family `B` enumerated with each block appearing **infinitely often**
(period `n`).  For `n = 0` it is the constant empty family.  This is the faithful
rendering of the memoir's `⊔ F` as an honest `pgl`: it has `ω` copies of every
block, which is what makes `⊔ F` both an *upper bound* of an arbitrary pointed
gluing and the target of the lower bound. -/
def repSeq : ℕ → ScatFun :=
  fun k => if h : 0 < n then B ⟨k % n, Nat.mod_lt k h⟩ else empty

/-! **Proposition `FinitegenerationandPgluing` (1) — upper bound.**


The memoir's `Pgl(F)` denotes the pointed gluing with **`ω` copies of each block**
(`gl F`), faithfully rendered as
`pgl (repSeq B)`.  The statement is therefore
`Reduces (pgl f) (pgl (repSeq B))` (under `hf : ∀ i, ∃ g ∈ FinGl B, Reduces (f i) g`).
Its proof is the memoir's "reduction by pieces" argument: each `f i ≤ gl (copiesSeq B t_i)`
embeds block-by-block into arbitrarily deep slots of `pgl (repSeq B)` (which has `ω`
copies of every block).  This is proved below as
`finitegenerationAndPgluing_upper`, building on the func-level
`gl_reduces_pgl_direct` ("a plain gluing reduces deep into a pointed gluing") and
the `copiesList`-index / `repSeq`-slot combinatorics `copiesSeq_eq_B`,
`gl_copiesSeq_block_lt`, `exists_deep_reindex`. -/


/-
Every block of the finite-gluing list `copiesList B t` is one of the
generators `B i`.
-/
lemma copiesSeq_eq_B (k : ℕ) (hk : k < (copiesList B t).length) :
    ∃ i : Fin n, copiesSeq B t k = B i := by
  convert Set.mem_setOf_eq.mp ( List.getElem_mem _ ) |> fun h => ?_;
  rotate_left;
  exact ScatFun;
  exact copiesList B t;
  exact k;
  grind +revert;
  have := List.mem_flatMap.mp h; obtain ⟨ i, hi, hi' ⟩ := this; use i;
  convert List.eq_of_mem_replicate hi';
  exact List.getD_eq_getElem _ _ hk

/-
Past the list length the gluing list is `empty` (empty domain), so any point of
`gl (copiesSeq B t)` lies in a block index `< (copiesList B t).length`.
-/
lemma gl_copiesSeq_block_lt (x : ↑(gl (copiesSeq B t)).domain) :
    x.val 0 < (copiesList B t).length := by
  have := GluingSet_inverse_short ( fun k => ( copiesSeq B t k ).domain ) x;
  obtain ⟨ i, hi, hi' ⟩ := this; simp_all +decide [ copiesSeq ] ;
  contrapose! hi'; aesop;

/-
**A deep injective reindexing of the finite-gluing blocks into `repSeq B`.**

For `0 < n` and any depth `m`, there is an injective `e : ℕ → ℕ` with `e k ≥ m` for
all `k`, such that every block `copiesSeq B t k` reduces to `repSeq B (e k)`.
(Concretely one may take `e k = (m + k) * n + (residue of block k)`.)
-/
lemma exists_deep_reindex (hn : 0 < n) (m : ℕ) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧ (∀ k, m ≤ e k) ∧
      ∀ k, copiesSeq B t k = repSeq B (e k) ∨ IsEmpty ↑(copiesSeq B t k).domain := by
  -- Define `j : ℕ → Fin n` such that `j k = ⟨0, hn⟩` if `k ≥ (copiesList B t).length` and `j k` is chosen such that `copiesSeq B t k = B (j k)` otherwise.
  obtain ⟨j, hj⟩ : ∃ j : ℕ → Fin n, ∀ k, copiesSeq B t k = B (j k) ∨ (copiesList B t).length ≤ k := by
    have hj : ∀ k, (∃ jk : Fin n, copiesSeq B t k = B jk) ∨ (copiesList B t).length ≤ k := by
      intro k; exact Classical.or_iff_not_imp_right.2 fun hk => copiesSeq_eq_B B t k (Nat.lt_of_not_ge hk);
    exact ⟨ fun k => Classical.choose ( hj k |> Or.rec ( fun ⟨ jk, hj ⟩ => ⟨ jk, Or.inl hj ⟩ ) fun hk => ⟨ ⟨ 0, hn ⟩, Or.inr hk ⟩ ), fun k => Classical.choose_spec ( hj k |> Or.rec ( fun ⟨ jk, hj ⟩ => ⟨ jk, Or.inl hj ⟩ ) fun hk => ⟨ ⟨ 0, hn ⟩, Or.inr hk ⟩ ) ⟩;
  refine ⟨ fun k => ( m + k ) * n + ( j k : ℕ ), ?_, ?_, ?_ ⟩;
  · exact fun a b h => by nlinarith [ Fin.is_lt ( j a ), Fin.is_lt ( j b ) ] ;
  · exact fun k => by nlinarith [ Fin.is_lt ( j k ) ] ;
  · intro k; specialize hj k; unfold repSeq; simp +decide [ hn, Nat.mod_eq_of_lt ] ;
    unfold copiesSeq; aesop;

/-
**Local reduction of a single block into `pgl (repSeq B)`.**  Given a block
`F i` that reduces to a finite gluing `gl (copiesSeq B mult)`, and an open
neighbourhood `V` of the base point `0^ω` of `pgl (repSeq B)`, there is a reduction of
`F i` into `pgl (repSeq B)` whose image lies in `V` and whose `pgl (repSeq B)`-image
has `0^ω` outside its closure.  This is exactly the per-block datum required by
`pgl_reduces_of_local`.
-/
lemma pgl_repSeq_local (hn : 0 < n) (F : ℕ → ScatFun) (i : ℕ)
    (mult : Fin n → ℕ) (hR : Reduces (F i) (gl (copiesSeq B mult)))
    (V : Set ↑(pgl (repSeq B)).domain) (hVopen : IsOpen V)
    (hxV : (⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ :
        ↑(pgl (repSeq B)).domain) ∈ V) :
    ∃ (σ : ↑(F i).domain → ↑(pgl (repSeq B)).domain) (τ : Baire → Baire),
      Continuous σ ∧
      (∀ z, (F i).func z = τ ((pgl (repSeq B)).func (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => (pgl (repSeq B)).func (σ z))) ∧
      (∀ z, σ z ∈ V) ∧
      (pgl (repSeq B)).func ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ∉
        closure (Set.range (fun z => (pgl (repSeq B)).func (σ z))) := by
  obtain ⟨m, hm⟩ := nbhd_basis' (pgl (repSeq B)).domain ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hVopen hxV
  obtain ⟨e, he_inj, he_ge, he_disj⟩ := exists_deep_reindex B mult hn m
  obtain ⟨σC, τC, hσC_cont, hσC_eq, hτC_cont, hσC_deep, hσC_one⟩ := gl_reduces_pgl_direct (copiesSeq B mult) (repSeq B) e he_inj he_disj;
  obtain ⟨σ1, hσ1_cont, τ1, hτ1_cont, hσ1_eq⟩ := hR;
  refine ⟨ fun z => σC ( σ1 z ), τ1 ∘ τC, ?_, ?_, ?_, ?_, ?_ ⟩;
  · exact hσC_cont.comp hσ1_cont;
  · grind;
  · apply_rules [ ContinuousOn.comp, hτ1_cont, hτC_cont ];
    · exact continuousOn_id;
    · exact fun x hx => by obtain ⟨ z, rfl ⟩ := hx; exact ⟨ σ1 z, rfl ⟩ ;
    · intro x hx; obtain ⟨ z, rfl ⟩ := hx; simp +decide [ hσC_eq ] ;
  · intro z
    apply hm;
    intro l hl;
    exact hσC_deep _ _ ( lt_of_lt_of_le ( Finset.mem_range.mp hl ) ( he_ge _ ) );
  · -- Let `Cl := ⋃ k ∈ Finset.range L, {y : Baire | y (e k) = 1}`.
    set L := (copiesList B mult).length
    set Cl := ⋃ k ∈ Finset.range L, {y : Baire | y (e k) = 1};
    -- Show that `R ⊆ Cl`.
    have hR_subset_Cl : Set.range (fun z => (pgl (repSeq B)).func (σC (σ1 z))) ⊆ Cl := by
      rintro _ ⟨ z, rfl ⟩;
      exact Set.mem_iUnion₂.mpr ⟨ _, Finset.mem_range.mpr ( gl_copiesSeq_block_lt B mult ( σ1 z ) ), hσC_one _ ⟩;
    -- Show that `Cl` is closed.
    have hCl_closed : IsClosed Cl := by
      exact isClosed_biUnion_finset fun k hk => isClosed_eq ( continuous_apply _ ) continuous_const;
    -- Show that `zeroStream ∉ Cl`.
    have h_zeroStream_not_in_Cl : zeroStream ∉ Cl := by
      simp [Cl, zeroStream];
    rw [ pgl_func_zeroStream ];
    exact fun h => h_zeroStream_not_in_Cl <| hCl_closed.closure_subset_iff.mpr hR_subset_Cl h

/-
The `n = 0` degenerate case of `finitegenerationAndPgluing_upper`: with no
generators every `f i` (and hence `pgl f`) and `pgl (repSeq B)` collapse to the
one-point space `{0^ω}`, and the reduction is the identity.
-/
lemma finitegenerationAndPgluing_upper_zero (hn : n = 0) (f : ℕ → ScatFun)
    (hf : ∀ i, ∃ g ∈ FinGl B, Reduces (f i) g) :
    Reduces (pgl f) (pgl (repSeq B)) := by
  subst hn
  generalize_proofs at *;
  have h_empty : ∀ i, (f i).domain = ∅ := by
    intro i
    obtain ⟨g, hg₁, hg₂⟩ := hf i
    generalize_proofs at *;
    obtain ⟨ t, ht₁, ht₂ ⟩ := hg₁
    generalize_proofs at *;
    have h_empty : (Gl B t).domain = ∅ := by
      unfold Gl; simp +decide [ GluingSet ] ;
      grind +qlia
    generalize_proofs at *;
    obtain ⟨ σ, hσ₁, hσ₂ ⟩ := hg₂
    generalize_proofs at *;
    have h_empty : ∀ x : (f i).domain, False := by
      intro x
      obtain ⟨ y, hy ⟩ := ht₂
      generalize_proofs at *;
      exact h_empty.subset ( y ( σ x ) |>.2 )
    generalize_proofs at *;
    exact Set.eq_empty_of_forall_notMem (fun x hx => h_empty ⟨x, hx⟩)
  generalize_proofs at *;
  refine ⟨ fun x => ⟨ zeroStream, ?_ ⟩, ?_, ?_, ?_ ⟩ <;> norm_num [ pgl, h_empty ];
  exact Or.inl rfl
  exact continuous_const
  exact fun _ => zeroStream
  exact ⟨ continuousOn_const, fun a ha => by
    convert pgl_func_zeroStream f _ using 1
    generalize_proofs at *;
    · cases ha <;> aesop;
    · exact zeroStream_mem_pointedGluingSet _ ⟩

/-- **Proposition `FinitegenerationandPgluing` (1) — upper bound.**

If each `f i` reduces to a member of `FinGl B` (an element continuously equivalent to a
finite gluing of the generators `B`), then the pointed gluing `pgl f` reduces to the
pointed gluing `pgl (repSeq B)` with `ω` copies of every generator block — the faithful
rendering of the memoir's `⊔ F`. -/
theorem finitegenerationAndPgluing_upper (f : ℕ → ScatFun)
    (hf : ∀ i, ∃ g ∈ FinGl B, Reduces (f i) g) :
    Reduces (pgl f) (pgl (repSeq B)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact finitegenerationAndPgluing_upper_zero B hn f hf
  · refine pgl_reduces_of_local _ _ ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ ?_
    intro i V hVopen hxV
    obtain ⟨g, ⟨mult, _, hg2⟩, hfg⟩ := hf i
    have hR : Reduces (f i) (gl (copiesSeq B mult)) := hfg.trans hg2
    exact pgl_repSeq_local B hn f i mult hR V hVopen hxV

/-- **Proposition `FinitegenerationandPgluing` (2) — lower bound.**

If every element of `F` reduces, *cofinally*, into the sequence `f` — i.e. for
each block `B k` and each threshold `i` there is `j ≥ i` with `B k ≤ f j` — then
the pointed gluing of **ω copies of the gluing ** of `F` reduces to the pointed gluing of the sequence:
`pgl (F) ≤ pglᵢ fᵢ`.


PROVIDED SOLUTION
We build a reduction by pieces and then use PointedGluing_upper_bound.
Given $n\in\N$, suppose that we have built a family `(I_m)_{m<n}`of pairwise disjoint finite subsets of $\N$ such that for all `m<n` we have `\gl F\leq\gl_{i\in I_m}f_i`.
Set $`=\max(\bigcup_{m<n}I_m)+1` and use the hypothesis to fix an injective function `\iota:F\rao[j,\infty)` such that for all `g\in F` we have `g\leq f_{\iota(g)}`.
Setting `I_n=\iota(F)`, which is finite since $F$ is, yields the desired reduction by pieces.
 -/
theorem finitegenerationAndPgluing_lower (f : ℕ → ScatFun)
    (hf : ∀ (k : Fin n) (i : ℕ), ∃ j, i ≤ j ∧ Reduces (B k) (f j)) :
    Reduces (pgl (repSeq B)) (pgl f) := by
  apply pgl_reduces_of_local
  intro i V hVopen hxV
  by_cases hn : 0 < n
  · rw [show repSeq B i = B ⟨i % n, Nat.mod_lt i hn⟩ from dif_pos hn]
    obtain ⟨m, hm⟩ := nbhd_basis' (pgl f).domain
      ⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩ V hVopen hxV
    obtain ⟨j, hjm, hj⟩ := hf ⟨i % n, Nat.mod_lt i hn⟩ m
    obtain ⟨σ', hσ', τ', hτ', h_eq⟩ := (ScatFun.reduces_iff _ _).1 hj
    refine ⟨fun z => ⟨prependZerosOne j (σ' z).val,
        prependZerosOne_mem_pointedGluingSet _ j _ (σ' z).prop⟩,
      fun w => τ' (stripZerosOne j w),
      ((continuous_prependZerosOne j).comp (continuous_subtype_val.comp hσ')).subtype_mk _,
      ?_, ?_, ?_, ?_⟩
    · intro z
      show (B ⟨i % n, Nat.mod_lt i hn⟩).func z = τ' (stripZerosOne j ((pgl f).func _))
      rw [pgl_func_block, stripZerosOne_prependZerosOne]
      exact h_eq z
    · refine hτ'.comp (continuous_stripZerosOne j).continuousOn ?_
      rintro _ ⟨z, rfl⟩
      dsimp only
      rw [pgl_func_block, stripZerosOne_prependZerosOne]
      exact ⟨z, rfl⟩
    · intro z
      refine hm ?_
      intro k hk
      have : prependZerosOne j (σ' z).val k = 0 :=
        prependZerosOne_head_eq_zero j _ k (lt_of_lt_of_le (Finset.mem_range.mp hk) hjm)
      simpa [zeroStream] using this
    · rw [pgl_func_zeroStream]
      have hsub : Set.range (fun z => (pgl f).func
          (⟨prependZerosOne j (σ' z).val, prependZerosOne_mem_pointedGluingSet _ j _ (σ' z).prop⟩ :
            ↑(pgl f).domain)) ⊆ {w : Baire | w j = 1} := by
        rintro _ ⟨z, rfl⟩
        dsimp only
        rw [pgl_func_block]
        exact prependZerosOne_at_i j _
      intro hcl
      have : zeroStream ∈ {w : Baire | w j = 1} :=
        (IsClosed.closure_subset_iff (isClosed_eq (continuous_apply j) continuous_const)).2
          hsub hcl
      simp [zeroStream] at this
  · rw [show repSeq B i = empty from dif_neg hn]
    refine ⟨fun z => (Set.notMem_empty z.1 z.2).elim,
      id, continuous_of_const fun z => z.2.elim,
      fun z => (Set.notMem_empty z.1 z.2).elim, continuousOn_id,
      fun z => (Set.notMem_empty z.1 z.2).elim, ?_⟩
    have : IsEmpty (↑(empty.domain)) := Set.isEmpty_coe_sort.mpr rfl
    rw [Set.range_eq_empty, closure_empty]
    exact Set.notMem_empty _

/- **Finite generation of CB-rank levels** has moved to `ScatFun.levels_finitely_generated`
in `ScatFun/Generators/Defs.lean`, now stated with the explicit witness `Generators α` (the
memoir's `𝒢_α`) instead of an existential family `B`.  (It can't live here: `Generators/Defs.lean`
needs `FinGl`, so it imports this file, not the other way around.) -/

end ScatFun

end
