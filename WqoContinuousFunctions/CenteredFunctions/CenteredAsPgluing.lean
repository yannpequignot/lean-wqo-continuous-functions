import WqoContinuousFunctions.CenteredFunctions.CenteredAsPgluing.Helpers
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Theorem 4.6 (CenteredAsPgluing) — §4.1

A centered function is equivalent to the pointed gluing of its rays (Item 1), and to the
pointed gluing of a monotone sequence (Item 2).  Upstream of `finitenessOfCenteredFunctions`.

* `centeredAsPgluing_forward` / `centeredAsPgluing_backward` — Item 1 (`≤` / `≥`)
* `centered_equiv_pgl_rays` — Item 1 full equivalence
* `monotone_pgluing_of_centered`, `centeredAsPgluing_iff_monotone` — Item 2
* `centeredAsPgluing_CBrank` — CB-rank consequence
-/

/-- **Theorem 4.6 (CenteredAsPgluing) — Item 1 (forward), `ScatFun` form.**
Every `ScatFun` `G` continuously reduces to the pointed gluing of its rays at any base
point `y` (in particular, at the cocenter when `G` is centered):
`G ≤ pgl_i Ray(G, y, i)`.

This lives here, rather than in `CenteredFunctions/Theorems.lean` (§4.1), because it now
consumes the constructive `ScatFun.reduces_pgl_rays` (the replacement for the old
degenerate `pointedGluing_rays_upper_bound`), which is defined in
`CenteredFunctions/LocallyCentered/Helpers.lean`. -/
theorem centeredAsPgluing_forward (G : ScatFun) (y : Baire) :
    ContinuouslyReduces G.func (ScatFun.pgl (fun i => G.rayOn y Set.univ i)).func :=
  ScatFun.reduces_pgl_rays G y

/-- **Theorem 4.6 (CenteredAsPgluing) — Item 1 (backward / lower bound), `ScatFun` form.**
The reverse of `centeredAsPgluing_forward` for a *centered* `G`: the pointed gluing of
the rays of `G` at its cocenter `y` reduces back to `G`, i.e. `pgl_i Ray(G, y, i) ≤ G`.
Combined with `centeredAsPgluing_forward` this yields `G ≡ pgl_i Ray(G, y, i)` whenever
`G` is centered.

## Provided solution (`4_centered_memo.tex`, proof of `CenteredasPgluing`)

`By Pgluingaslowerbound2, it is enough to show that for every clopen neighbourhood U of
x (a center for f) and every n, there is a continuous reduction (σ, τ) from Ray(f, y, n)
to f with im σ ⊆ U and y ∉ closure(im(f σ)). By centeredness there is a reduction (ρ, κ)
from f to f↾U; by Rigidityofthecocenter, for all n we have f(x)=y ∉ closure(f ρ
(f⁻¹(Ray(B, y, n)))), so (ρ, κ) restricts to witness the required reductions
Ray(f, y, n) ≤ f.`

Formal proof.  We feed `ScatFun.pgl_reduces_of_local` at a center `x₀` of `G` (so
`G.func x₀ = cocenter G.func hG_cent = y`).  For each block `i` and open `V ∋ x₀`,
centeredness (`hx₀ V`) gives the reduction `(ρ, κ)` of `G.func` into `G.func|_V`.  The
block `i` reduces by `z ↦ (ρ (incl z)).val` (where `incl` is the underlying-point
inclusion of `Ray(G, y, i)` into `↑G.domain`), `τ := κ`; its image lies in `V` and the
defining equation is `hred_c` precomposed with `incl`.  The separation `y ∉ closure …`
is *exactly* `ray_separation` (Prop. 4.4) at `F = G = G` with the identity reduction
`(id, id)`: that lemma's ray-indexed image family contains ours because every `incl z`
lies in the ray `{a | G.func a ∈ RaySet univ y i}`.  Unlike the informal text we do not
go through the partition `f⁻¹(Ray(B, y, n))` explicitly; the ray membership of `incl z`
suffices to land in `ray_separation`'s closure. -/
theorem centeredAsPgluing_backward (G : ScatFun) (hG_cent : IsCentered G.func) :
    ContinuouslyReduces
      (ScatFun.pgl (fun i => G.rayOn (cocenter G.func hG_cent) Set.univ i)).func
      G.func := by
  set y : Baire := cocenter G.func hG_cent with hy
  -- A center `x₀` of `G`; note `G.func x₀ = y` definitionally (`cocenter := G.func _`).
  set x₀ : ↑G.domain := hG_cent.choose with hx₀def
  have hx₀ : IsCenterFor G.func x₀ := hG_cent.choose_spec
  -- The pointed-gluing lower-bound criterion, applied at the center `x₀`.
  refine ScatFun.pgl_reduces_of_local (fun i => G.rayOn y Set.univ i) G x₀ ?_
  intro i V hV hx₀V
  -- Centeredness: a continuous reduction `(ρ, κ)` of `G.func` into `G.func|_V`.
  obtain ⟨ρ, hρ, κ, hκ, hred_c⟩ := hx₀ V hV hx₀V
  -- The underlying-point inclusion of the `i`-th ray into `↑G.domain`.
  set B : Set ↑G.domain := Set.univ ∩ {a | G.func a ∈ RaySet Set.univ y i} with hB
  set incl : (G.rayOn y Set.univ i).domain → ↑G.domain :=
    fun z => (G.restrictEquiv B z).val with hincl
  have hincl_cont : Continuous incl :=
    continuous_subtype_val.comp (G.restrictEquiv B).continuous
  -- The block-`i` reduction into `G`, with image in `V`.
  refine ⟨fun z => (ρ (incl z)).val, κ, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (hρ.comp hincl_cont)
  · -- `Ray(G,y,i).func z = G.func (incl z)` (defeq), then `hred_c (incl z)`.
    intro z
    show G.func (incl z) = κ (G.func ((ρ (incl z)).val))
    exact hred_c (incl z)
  · -- `ContinuousOn κ` on the smaller range, from the center reduction's range.
    refine hκ.mono ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨incl z, rfl⟩
  · exact fun z => (ρ (incl z)).property
  · -- Separation: `y ∉ closure (range (G.func ∘ σ))`, via `ray_separation`.
    have hsep := ray_separation G G hG_cent hG_cent (ContinuouslyEquiv.refl G.func)
      continuous_id continuousOn_id (fun _ => rfl) hV hx₀V hx₀ hρ hκ hred_c i
    intro hmem
    apply hsep
    -- Our range is contained in `ray_separation`'s ray-indexed range.
    refine closure_mono ?_ hmem
    rintro _ ⟨z, rfl⟩
    -- `incl z` lies in the `i`-th ray, so it indexes the separation family.
    have hp : incl z ∈ B := (G.restrictEquiv B z).property
    simp only [hB, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq,
      RaySet] at hp
    exact ⟨⟨incl z, hp⟩, rfl⟩

/-- **Theorem 4.6 (CenteredAsPgluing) — Item 1, full equivalence.**
A centered `ScatFun` `G` is continuously equivalent to the pointed gluing of its rays at
its cocenter `y`: `G ≡ pgl_i Ray(G, y, i)`.  This packages the upper bound
`centeredAsPgluing_forward` with the lower bound `centeredAsPgluing_backward`. -/
theorem centered_equiv_pgl_rays (G : ScatFun) (hG_cent : IsCentered G.func) :
    ContinuouslyEquiv G.func
      (ScatFun.pgl (fun i => G.rayOn (cocenter G.func hG_cent) Set.univ i)).func :=
  ⟨centeredAsPgluing_forward G (cocenter G.func hG_cent),
   centeredAsPgluing_backward G hG_cent⟩

/-- **Theorem 4.6 (CenteredAsPgluing) — Item 2 (forward).**
If `F` is centered then `F ≡ pgl g` for some `≤`-monotone sequence `(g_i)_i`.

## Provided solution (`4_centered_memo.tex`)

`By Rigidityofthecocenter, for all m,n there exists m'>m such that
Ray(f,y,n) ≤ gl_{i=m}^{m'} Ray(f,y,i). We recursively apply this to get a pairwise
disjoint family of finite sets (I_n)_n such that, setting f_n = gl_{i∈I_n} Ray(f,y,i),
the sequence (f_n)_n is monotone and Ray(f,y,n) ≤ f_n for all n. Moreover (f_n)_n is
reducible by pieces to (Ray(f,y,n))_n, so by a double application of Pgluingasupperbound,
pgl_n f_n ≡ pgl_n Ray(f,y,n).`

Formal status.  The centered equivalence `F ≡ pgl_i Ray(F, y, i)` is fully proved
(`centered_equiv_pgl_rays`).  What remains is the **monotonization** isolated below as the
single `obtain`: given the rays `R`, produce a monotone `g` with `pgl g ≡ pgl R`.  This is
the rigidity recursion of the provided solution (`rigidityOfCocenter_finiteGluing` building
deep, pairwise-disjoint finite index sets, then a double `pointedGluing_upper_bound`).  Note
the deep placement is essential: the naive monotone choice `g_n = gl(R_0,…,R_n)` (initial
segments) is monotone but provably fails `pgl g ≤ pgl R`, because its block `R_0` only
reduces to the *shallow* block `0` of `pgl R`, so its image cannot be pushed into an
arbitrary neighbourhood of `0^ω`. -/
theorem monotone_pgluing_of_centered (F : ScatFun) (hF_cent : IsCentered F.func) :
    ∃ (g : ℕ → ScatFun),
      IsMonotoneSeq g ∧
      ContinuouslyEquiv F.func (ScatFun.pgl g).func := by
  -- Monotonize the rays `R` of `F` (rigidity `glWindow`-regularity → monotone `g` with
  -- `pgl g ≡ pgl R`), then chain with the centered equivalence `F ≡ pgl R`.
  obtain ⟨g, hg_mono, hgR⟩ :=
    exists_monotone_pgl_equiv (fun i => F.rayOn (cocenter F.func hF_cent) Set.univ i)
      (rays_glRegular F hF_cent)
  exact ⟨g, hg_mono, (centered_equiv_pgl_rays F hF_cent).trans hgR.symm⟩

/-- **Theorem 4.6 (CenteredasPgluing) — Item 2.**
`f ∈ 𝒞` is centered iff `f ≡ pgl_i f_i` for some monotone (or regular) sequence `(f_i)_i`.

*Proof (⇒):* `monotone_pgluing_of_centered` (the forward construction, just above).
*Proof (⇐):* `pgluingOfRegularIsCentered` (a monotone sequence is regular) +
`isCentered_of_equiv`.

Relocated here from `CenteredFunctions/Theorems.lean` (§4.1): the forward direction now
consumes `monotone_pgluing_of_centered`, whose dependencies (`ScatFun.rayOn`,
`ray_separation`) live downstream of `Theorems.lean`. -/
theorem centeredAsPgluing_iff_monotone
    (F : ScatFun) :
    IsCentered F.func ↔
    ∃ (g : ℕ → ScatFun),
      IsMonotoneSeq g ∧
      ContinuouslyEquiv F.func (ScatFun.pgl g).func := by
  constructor
  · exact monotone_pgluing_of_centered F
  · rintro ⟨g, hg_mono, hequiv⟩
    have hg_reg : Preorder.IsRegularSeq ScatFun.Reduces g := IsMonotoneSeq.isRegularSeq g hg_mono
    have hg_cent : IsCentered (ScatFun.pgl g).func :=
      ⟨⟨zeroStream, zeroStream_mem_pointedGluingSet _⟩, pgluingOfRegularIsCentered g hg_reg⟩
    exact isCentered_of_equiv hg_cent hequiv


/-- **Theorem 4.6 — CB-rank consequence.**
If `f` is centered with cocenter `y`, then `f` is simple with distinguished point `y`
and `CB(f) = (sup_n CB(Ray(f, y, n))) + 1`. -/
theorem centeredAsPgluing_CBrank
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f)
    (y : ℕ → ℕ) (hy : ∀ x, IsCenterFor f x → f x = y) :
    CBRank f = Order.succ (⨆ n, CBRank (RayFun f y n)) := by
  -- `f` is simple: rank `α + 1`, with `f` constant `= y` on `CB_α`.
  obtain ⟨α, hrank, hne, _hempty, hsimple⟩ :=
    centered_scattered_simple_structure f hf_scat hf_cent y hy
  -- `RayFun f y n` has the same CB-rank as the `RaySet`-form ray used by the helpers
  -- (their domains coincide, since `f a ∈ B` always).
  have hray_eq : ∀ n, CBRank (RayFun f y n)
      = CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) := by
    intro n
    have hD : {a : A | (∀ k, k < n → f a k = y k) ∧ f a n ≠ y n}
            = {a : A | f a ∈ RaySet B y n} := by
      ext a; simp only [RaySet, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hfB a, h⟩, fun h => h.2⟩
    exact CBRank_comp_homeomorph (Homeomorph.setCongr hD)
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)
  -- The supremum of the ray CB-ranks is exactly `α` (`sup_ray_cb_eq_alpha`).
  have hsup : (⨆ n, CBRank (RayFun f y n)) = α := by
    rw [iSup_congr hray_eq]
    exact sup_ray_cb_eq_alpha f hfB hf hf_scat α hne y hsimple
      (fun n => CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val))
      (fun _ => rfl) (fun n => ray_cb_le_alpha f hf α y hsimple n)
  rw [hrank, hsup]


end