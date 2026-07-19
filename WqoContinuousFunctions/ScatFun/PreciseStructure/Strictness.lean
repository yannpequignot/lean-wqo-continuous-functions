import WqoContinuousFunctions.CenteredFunctions.SimpleSuccessorOfLimit

/-!
# Strict separation `k_{λ+1} < pgl ℓ_λ` — limit case (`cor:CenteredSucessor`)

The strict direction of Corollary 4.10: for `λ` a nonzero limit ordinal, `pgl ℓ_λ`
(`ScatFun.succMaxFun λ`) does **not** reduce to `k_{λ+1}` (`ScatFun.minFun λ`). The argument
compares CB-ranks: a ray of `pgl ℓ_λ` has rank `λ` (`succMaxFun_ray_cbRank`), while any finite
union of cocenter rays in the canonical limit presentation of `k_{λ+1}` has rank `< λ`
(`minFun_limit_pgl_finite_rays_cbRank_lt`), contradicting rank-monotonicity of reductions.

This strictness is not needed for finite generation itself; it records the memoir's exact
position of the two `λ+1` generators. See §4.2–4.3 of `4_centered_memo.tex`.
-/

open scoped Topology ScatFun
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-- Every ray of the constant pointed gluing of `maxFun lam` has CB-rank `lam`. -/
lemma succMaxFun_ray_cbRank (lam : Ordinal.{0}) (hlam_lt : lam < omega1) (n : ℕ) :
    CBRank ((ScatFun.succMaxFun lam hlam_lt).rayOn zeroStream Set.univ n).func = lam := by
  set f := ScatFun.succMaxFun lam hlam_lt
  have hf_eq_pgl : f = ScatFun.pgl (fun _ => ScatFun.maxFun lam hlam_lt) :=
    ScatFun.succMaxFun_eq lam hlam_lt
  rw [hf_eq_pgl, rayOn_cbRank_eq_rayFun, cbRank_rayFun_pgl]
  exact maxFun_cbRank_eq lam hlam_lt

/-- A finite union of cocenter rays in the canonical limit presentation of `minFun lam`
has CB-rank strictly below `lam`. -/
lemma minFun_limit_pgl_finite_rays_cbRank_lt (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0) (hlam_lt : lam < omega1)
    (J : Finset ℕ) :
    let P := ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n)
      (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt))
    CBRank (P.restrict {a : ↑P.domain |
      P.func a ∈ ⋃ i ∈ J, RaySet Set.univ zeroStream i}).func < lam := by
  apply cbRank_corestrict_W_lt
  · exact hlam_ne
  · apply pgl_rayOn_zeroStream_cbRank_lt
    intro i
    rw [minFun_cbRank_eq]
    exact hlim.succ_lt (cofinalSeq_lt lam hlim hlam_ne i)

open ScatFun in
/-- **Corollary 4.10, strict direction — limit case** (`cor:CenteredSucessor`).  For `λ` a
nonzero limit, `pgl ℓ_λ` (`SuccMaxFun λ`) does **not** reduce to `k_{λ+1}` (`MinFun λ`).

If it did, then with the easy direction `k_{λ+1} ≤ pgl ℓ_λ` (`minFun_le_pglMaxFun`) it would be
*equivalent* to `k_{λ+1} ≡ P` (`minFun_limit_equiv_pgl`, `P` the canonical limit presentation).
Cocenter rigidity (`rigidityOfCocenter_reducibleByPieces`) then embeds the `0`-th ray of
`pgl ℓ_λ` — of CB-rank `λ` (`succMaxFun_ray_cbRank`) — into a *finite* gluing of `P`-rays of
CB-rank `< λ` (`minFun_limit_pgl_finite_rays_cbRank_lt`), contradicting
`ContinuouslyReduces.rank_monotone`. -/
lemma pglMaxFun_not_le_minFunPlusOne_limit (lam : Ordinal.{0})
    (hlim : Order.IsSuccLimit lam) (hlam_ne : lam ≠ 0) (hlam_lt : lam < omega1) :
    ¬ ContinuouslyReduces (SuccMaxFun lam) (MinFun lam) := by
  intro hred
  -- `P` : the canonical limit presentation of `k_{λ+1} = MinFun λ` as `pgl` of a cofinal
  -- sequence of `minFun`s (matches `minFun_limit_equiv_pgl` and the ray-rank lemma above).
  set P : ScatFun := ScatFun.pgl (fun n => ScatFun.minFun (cofinalSeq lam n)
    (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt)) with hPdef
  -- Centeredness of both endpoints.
  have hFcent : IsCentered (ScatFun.succMaxFun lam hlam_lt).func := by
    rw [succMaxFun_func]; exact pglSuccMaxFun_isCentered lam hlam_lt
  have hreg : Preorder.IsRegularSeq ScatFun.Reduces
      (fun n => ScatFun.minFun (cofinalSeq lam n)
        (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt)) :=
    minFun_cofinalSeq_isRegularSeq lam hlam_lt hlim hlam_ne
  have hGcent : IsCentered P.func := pgl_isCentered_of_regular _ hreg
  -- Both cocenters are `zeroStream` (they are pointed gluings of value-`Subtype.val` blocks).
  have hcF : cocenter (ScatFun.succMaxFun lam hlam_lt).func hFcent = zeroStream :=
    cocenter_pgl_eq_zeroStream (fun _ => ScatFun.maxFun lam hlam_lt)
      (scatFun_const_isRegularSeq _) (fun _ _ => by rw [ScatFun.maxFun_func]; rfl) hFcent
  have hcG : cocenter P.func hGcent = zeroStream :=
    cocenter_pgl_eq_zeroStream (fun n => ScatFun.minFun (cofinalSeq lam n)
        (lt_trans (cofinalSeq_lt lam hlim hlam_ne n) hlam_lt)) hreg
      (fun _ _ => by rw [ScatFun.minFun_func]; rfl) hGcent
  -- Equivalence chain `pgl ℓ_λ ≡ k_{λ+1} ≡ P`.
  have hequiv : ContinuouslyEquiv (ScatFun.succMaxFun lam hlam_lt).func P.func := by
    rw [succMaxFun_func]
    have h1 : ContinuouslyEquiv (SuccMaxFun lam) (MinFun lam) :=
      ⟨hred, minFun_le_pglMaxFun lam hlam_lt hlam_ne⟩
    have h2 : ContinuouslyEquiv (MinFun lam) P.func := by
      have he := minFun_limit_equiv_pgl lam hlam_lt hlim hlam_ne
      exact ⟨he.1, he.2⟩
    exact h1.trans h2
  -- Cocenter rigidity: each ray of `pgl ℓ_λ` reduces into a finite gluing of `P`-rays.
  obtain ⟨I, hIdisj, hIred⟩ :=
    rigidityOfCocenter_reducibleByPieces (ScatFun.succMaxFun lam hlam_lt) P hFcent hGcent hequiv
  have hn := hIred 0
  -- (i) The `0`-th ray of `pgl ℓ_λ` has CB-rank `λ`.
  have hLHS : CBRank (fun (x : {a : ↑(ScatFun.succMaxFun lam hlam_lt).domain |
      (∀ k, k < 0 → (ScatFun.succMaxFun lam hlam_lt).func a k =
          cocenter (ScatFun.succMaxFun lam hlam_lt).func hFcent k) ∧
        (ScatFun.succMaxFun lam hlam_lt).func a 0 ≠
          cocenter (ScatFun.succMaxFun lam hlam_lt).func hFcent 0}) =>
      (ScatFun.succMaxFun lam hlam_lt).func x.val) = lam := by
    rw [hcF]
    have hset : {a : ↑(ScatFun.succMaxFun lam hlam_lt).domain |
        (∀ k, k < 0 → (ScatFun.succMaxFun lam hlam_lt).func a k = zeroStream k) ∧
          (ScatFun.succMaxFun lam hlam_lt).func a 0 ≠ zeroStream 0}
        = {z : ↑(ScatFun.succMaxFun lam hlam_lt).domain |
          (ScatFun.succMaxFun lam hlam_lt).func z ∈ RaySet Set.univ zeroStream 0} := by
      ext a; simp [RaySet]
    rw [← cbRank_restrict_eq, hset, ← rayOn_eq_corestrict]
    exact succMaxFun_ray_cbRank lam hlam_lt 0
  -- (ii) The finite gluing of `P`-rays over `I 0` has CB-rank `< λ`.
  have hRHS : CBRank (fun (x : {a : ↑P.domain | ∃ i ∈ I 0,
      (∀ k, k < i → P.func a k = cocenter P.func hGcent k) ∧
        P.func a i ≠ cocenter P.func hGcent i}) => P.func x.val) < lam := by
    rw [hcG]
    have hset : {a : ↑P.domain | ∃ i ∈ I 0,
        (∀ k, k < i → P.func a k = zeroStream k) ∧ P.func a i ≠ zeroStream i}
        = {a : ↑P.domain | P.func a ∈ ⋃ i ∈ I 0, RaySet Set.univ zeroStream i} := by
      ext a; simp [RaySet]; tauto
    rw [← cbRank_restrict_eq, hset]
    exact minFun_limit_pgl_finite_rays_cbRank_lt lam hlim hlam_ne hlam_lt (I 0)
  -- Scatteredness of the two ray functions (restrictions of scattered functions).
  have hscatL : ScatteredFun (fun (x : {a : ↑(ScatFun.succMaxFun lam hlam_lt).domain |
      (∀ k, k < 0 → (ScatFun.succMaxFun lam hlam_lt).func a k =
          cocenter (ScatFun.succMaxFun lam hlam_lt).func hFcent k) ∧
        (ScatFun.succMaxFun lam hlam_lt).func a 0 ≠
          cocenter (ScatFun.succMaxFun lam hlam_lt).func hFcent 0}) =>
      (ScatFun.succMaxFun lam hlam_lt).func x.val) := by
    exact scattered_restrict _ (ScatFun.succMaxFun lam hlam_lt).hScat _
  have hscatR : ScatteredFun (fun (x : {a : ↑P.domain | ∃ i ∈ I 0,
      (∀ k, k < i → P.func a k = cocenter P.func hGcent k) ∧
        P.func a i ≠ cocenter P.func hGcent i}) => P.func x.val) := by
    exact scattered_restrict _ P.hScat _
  -- CB-rank monotonicity yields `λ ≤ (CB-rank of gluing) < λ`, a contradiction.
  have hmono := hn.rank_monotone hscatL hscatR
  rw [hLHS] at hmono
  exact absurd (hmono.trans_lt hRHS) (lt_irrefl lam)

end
