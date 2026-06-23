import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic
import ZeroDimensionalSpaces.CantorScheme

/-!
# Cantor scheme → Cantor-space embedding (complete carrier)

When the carrier `Z` is a *complete* metric space and the scheme radii shrink geometrically,
each branch of `2^ℕ` has a well-defined limit `cantorSigmaFull c z = limₙ c (z|ₙ)`. This gives
a topological embedding `2^ℕ → Z` (and `g ∘ ·` into `Y` when a separating open family `U`
captures the images of a continuous `g`).

Moved out of `WqoContinuousFunctions.…Scattered.NonScattered` (the former `CantorFullScheme`
section). Only the project-specific assembly `nlc_cantor_embedding_concrete` stays behind.
-/

open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

section CantorFullScheme

variable {Z Y : Type*} [MetricSpace Z] [TopologicalSpace Y]
  {c : List (Fin 2) → Z} {r : List (Fin 2) → ℝ} {U : List (Fin 2) → Set Y}

/-- **Step 2a.** Along each branch the centres form a Cauchy sequence. -/
lemma scheme_centers_cauchySeq
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (z : CantorSpace) :
    CauchySeq (fun n => c (PiNat.res z n)) := by
  refine cauchySeq_of_le_geometric (1 / 2) (r []) (by norm_num) (fun n => ?_)
  -- consecutive centres lie in nested balls, with radius ≤ r[] / 2ⁿ
  have hmem : c (PiNat.res z (n + 1)) ∈ Metric.ball (c (PiNat.res z n)) (r (PiNat.res z n)) := by
    rw [PiNat.res_succ]
    exact hball (PiNat.res z n) (z n) (Metric.mem_closedBall_self (hr_pos _).le)
  have hlt : dist (c (PiNat.res z n)) (c (PiNat.res z (n + 1))) < r (PiNat.res z n) := by
    rw [dist_comm]; exact Metric.mem_ball.mp hmem
  have hrad : r (PiNat.res z n) ≤ r [] / 2 ^ n := by
    have h := scheme_radius_bound hr_half (PiNat.res z n)
    rwa [PiNat.res_length] at h
  calc dist (c (PiNat.res z n)) (c (PiNat.res z (n + 1)))
        ≤ r (PiNat.res z n) := hlt.le
    _ ≤ r [] / 2 ^ n := hrad
    _ = r [] * (1 / 2) ^ n := by rw [div_eq_mul_inv, one_div, inv_pow]

/-- **Step 2b (def).** The branch limit map `σ : 2^ℕ → Z`. -/
noncomputable def cantorSigmaFull [Nonempty Z] (c : List (Fin 2) → Z) (z : CantorSpace) : Z :=
  limUnder Filter.atTop (fun n => c (PiNat.res z n))

/-- **Step 2b.** `σ z` is the limit of the branch centres. -/
lemma cantorSigmaFull_tendsto [Nonempty Z] [CompleteSpace Z]
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (z : CantorSpace) :
    Filter.Tendsto (fun n => c (PiNat.res z n)) Filter.atTop (nhds (cantorSigmaFull c z)) := by
  obtain ⟨a, ha⟩ :=
    cauchySeq_tendsto_of_complete (scheme_centers_cauchySeq hr_pos hr_half hball z)
  have hlim : cantorSigmaFull c z = a := ha.limUnder_eq
  rw [hlim]; exact ha

/-- **Step 2c.** `σ z` lies in every closed ball along its branch. -/
lemma cantorSigmaFull_mem_closedBall [Nonempty Z] [CompleteSpace Z]
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (z : CantorSpace) (n : ℕ) :
    cantorSigmaFull c z ∈ Metric.closedBall (c (PiNat.res z n)) (r (PiNat.res z n)) := by
  refine Metric.isClosed_closedBall.mem_of_tendsto
    (cantorSigmaFull_tendsto hr_pos hr_half hball z) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  obtain ⟨l₁, hl₁⟩ : ∃ l₁, PiNat.res z m = l₁ ++ PiNat.res z n := by
    induction' hm with m hm ih
    · exact ⟨[], rfl⟩
    · obtain ⟨l₁, hl₁⟩ := ih
      exact ⟨z m :: l₁, by rw [PiNat.res_succ, hl₁, List.cons_append]⟩
  rw [hl₁]
  exact scheme_center_in_closedBall hr_pos hball l₁ (PiNat.res z n)

/-- **Step 3a.** `σ` is continuous. -/
lemma cantorSigmaFull_continuous [Nonempty Z] [CompleteSpace Z]
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l)) :
    Continuous (cantorSigmaFull c) := by
  refine continuous_iff_continuousAt.mpr (fun z => ?_)
  refine Metric.tendsto_nhds.mpr (fun ε εpos => ?_)
  -- choose depth `n` with `2 · r(z|ₙ) < ε`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * r (PiNat.res z n) < ε := by
    have h_bound : ∃ n : ℕ, 2 * r [] / 2 ^ n < ε := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
        |> fun h => h.eventually (gt_mem_nhds εpos) |> fun h => h.exists
    obtain ⟨n, hn⟩ := h_bound
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    rw [mul_div_assoc]
    have h := scheme_radius_bound hr_half (PiNat.res z n)
    rw [PiNat.res_length] at h
    exact mul_le_mul_of_nonneg_left h zero_le_two
  -- the depth-`n` cylinder is a neighbourhood of `z`
  have h_cyl_mem : {z' : CantorSpace | PiNat.res z' n = PiNat.res z n} ∈ nhds z := by
    have hopen : IsOpen {z' : CantorSpace | PiNat.res z' n = PiNat.res z n} := by
      rw [← PiNat.cylinder_eq_res]; exact PiNat.isOpen_cylinder (E := fun _ => Fin 2) z n
    exact hopen.mem_nhds rfl
  filter_upwards [h_cyl_mem] with z' hz'
  have hm1 : cantorSigmaFull c z' ∈ Metric.closedBall (c (PiNat.res z n)) (r (PiNat.res z n)) := by
    have h := cantorSigmaFull_mem_closedBall hr_pos hr_half hball z' n
    rwa [hz'] at h
  have hm2 := cantorSigmaFull_mem_closedBall hr_pos hr_half hball z n
  have hd : dist (cantorSigmaFull c z') (cantorSigmaFull c z) ≤ 2 * r (PiNat.res z n) :=
    calc dist (cantorSigmaFull c z') (cantorSigmaFull c z)
        ≤ dist (cantorSigmaFull c z') (c (PiNat.res z n))
          + dist (c (PiNat.res z n)) (cantorSigmaFull c z) := dist_triangle _ _ _
      _ ≤ r (PiNat.res z n) + r (PiNat.res z n) :=
          add_le_add (Metric.mem_closedBall.mp hm1) (Metric.mem_closedBall'.mp hm2)
      _ = 2 * r (PiNat.res z n) := by ring
  linarith [hd, hn]

/-- **Step 3b.** `σ` is injective (scheme disjointness, valid at limit points). -/
lemma cantorSigmaFull_injective [Nonempty Z] [CompleteSpace Z]
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Function.Injective (cantorSigmaFull c) := by
  classical
  intro z z' hzz
  by_contra hne
  -- first coordinate where `z` and `z'` differ
  obtain ⟨k, hk_ne, hk_min⟩ : ∃ k, z k ≠ z' k ∧ ∀ i, i < k → z i = z' i := by
    have hex : ∃ n, z n ≠ z' n := Function.ne_iff.mp hne
    exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  have hk_eq : PiNat.res z k = PiNat.res z' k := PiNat.res_eq_res.mpr hk_min
  have hzm := cantorSigmaFull_mem_closedBall hr_pos hr_half hball z (k + 1)
  have hz'm := cantorSigmaFull_mem_closedBall hr_pos hr_half hball z' (k + 1)
  rw [PiNat.res_succ] at hzm hz'm
  rw [← hk_eq] at hz'm
  have hz'm2 : cantorSigmaFull c z ∈
      Metric.closedBall (c (z' k :: PiNat.res z k)) (r (z' k :: PiNat.res z k)) := by
    rw [hzz]; exact hz'm
  -- the two depth-`(k+1)` balls are disjoint (they branch on `0`/`1`)
  have hzk : z k = 0 ∨ z k = 1 := by
    rcases Fin.exists_fin_two.mp (⟨z k, rfl⟩ : ∃ i : Fin 2, i = z k) with h | h
    exacts [Or.inl h.symm, Or.inr h.symm]
  have hz'k : z' k = 0 ∨ z' k = 1 := by
    rcases Fin.exists_fin_two.mp (⟨z' k, rfl⟩ : ∃ i : Fin 2, i = z' k) with h | h
    exacts [Or.inl h.symm, Or.inr h.symm]
  have hdis : Disjoint
      (Metric.closedBall (c (z k :: PiNat.res z k)) (r (z k :: PiNat.res z k)))
      (Metric.closedBall (c (z' k :: PiNat.res z k)) (r (z' k :: PiNat.res z k))) := by
    rcases hzk with h0 | h1 <;> rcases hz'k with h0' | h1'
    · exact absurd (h0.trans h0'.symm) hk_ne
    · rw [h0, h1']; exact hdisj (PiNat.res z k)
    · rw [h1, h0']; exact (hdisj (PiNat.res z k)).symm
    · exact absurd (h1.trans h1'.symm) hk_ne
  exact Set.disjoint_left.mp hdis hzm hz'm2

omit [TopologicalSpace Y] in
/-- **Step 3c.** `g (σ z)` lands in the separating open set at each branch node
(`σ z` sits in the *open* parent ball). -/
lemma g_cantorSigmaFull_in_U [Nonempty Z] [CompleteSpace Z] (g : Z → Y)
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l))
    (z : CantorSpace) (n : ℕ) :
    g (cantorSigmaFull c z) ∈ U (PiNat.res z (n + 1)) := by
  -- `σ z` sits in the *open* ball of the node `z|_{n+1}` (it is in the child closed ball)
  have hmem : cantorSigmaFull c z ∈
      Metric.ball (c (z n :: PiNat.res z n)) (r (z n :: PiNat.res z n)) := by
    rw [← PiNat.res_succ]
    have h2 := cantorSigmaFull_mem_closedBall hr_pos hr_half hball z (n + 2)
    rw [show n + 2 = (n + 1) + 1 from rfl, PiNat.res_succ] at h2
    exact hball (PiNat.res z (n + 1)) (z (n + 1)) h2
  have hgoal := hU_img (PiNat.res z n) (z n) (Set.mem_image_of_mem g hmem)
  rwa [← PiNat.res_succ] at hgoal

omit [TopologicalSpace Y] in
/-- **Step 3c.** `g ∘ σ` is injective. -/
lemma g_cantorSigmaFull_injective [Nonempty Z] [CompleteSpace Z] (g : Z → Y)
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hU_disj : ∀ l, Disjoint (U (0 :: l)) (U (1 :: l)))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) :
    Function.Injective (fun z => g (cantorSigmaFull c z)) := by
  classical
  intro z z' hzz
  by_contra hne
  obtain ⟨k, hk_ne, hk_min⟩ : ∃ k, z k ≠ z' k ∧ ∀ i, i < k → z i = z' i := by
    have hex : ∃ n, z n ≠ z' n := Function.ne_iff.mp hne
    exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  have hk_eq : PiNat.res z k = PiNat.res z' k := PiNat.res_eq_res.mpr hk_min
  have hzU := g_cantorSigmaFull_in_U g hr_pos hr_half hball hU_img z k
  have hz'U := g_cantorSigmaFull_in_U g hr_pos hr_half hball hU_img z' k
  rw [PiNat.res_succ] at hzU hz'U
  rw [← hk_eq] at hz'U
  have hz'U2 : g (cantorSigmaFull c z) ∈ U (z' k :: PiNat.res z k) := by
    rw [show g (cantorSigmaFull c z) = g (cantorSigmaFull c z') from hzz]; exact hz'U
  have hzk : z k = 0 ∨ z k = 1 := by
    rcases Fin.exists_fin_two.mp (⟨z k, rfl⟩ : ∃ i : Fin 2, i = z k) with h | h
    exacts [Or.inl h.symm, Or.inr h.symm]
  have hz'k : z' k = 0 ∨ z' k = 1 := by
    rcases Fin.exists_fin_two.mp (⟨z' k, rfl⟩ : ∃ i : Fin 2, i = z' k) with h | h
    exacts [Or.inl h.symm, Or.inr h.symm]
  have hdis : Disjoint (U (z k :: PiNat.res z k)) (U (z' k :: PiNat.res z k)) := by
    rcases hzk with h0 | h1 <;> rcases hz'k with h0' | h1'
    · exact absurd (h0.trans h0'.symm) hk_ne
    · rw [h0, h1']; exact hU_disj (PiNat.res z k)
    · rw [h1, h0']; exact (hU_disj (PiNat.res z k)).symm
    · exact absurd (h1.trans h1'.symm) hk_ne
  exact Set.disjoint_left.mp hdis hzU hz'U2

/-- **Step 4.** `σ : 2^ℕ → Z` is an embedding (injective continuous from compact `2^ℕ`). -/
lemma cantorSigmaFull_isEmbedding [Nonempty Z] [CompleteSpace Z] [T2Space Z]
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Topology.IsEmbedding (cantorSigmaFull c) :=
  ((cantorSigmaFull_continuous hr_pos hr_half hball).isClosedEmbedding
    (cantorSigmaFull_injective hr_pos hr_half hball hdisj)).isEmbedding

/-- **Step 4.** `g ∘ σ : 2^ℕ → Y` is an embedding. -/
lemma g_cantorSigmaFull_isEmbedding [Nonempty Z] [CompleteSpace Z] [T2Space Y] (g : Z → Y)
    (hg : Continuous g)
    (hr_pos : ∀ l, 0 < r l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hU_disj : ∀ l, Disjoint (U (0 :: l)) (U (1 :: l)))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) :
    Topology.IsEmbedding (fun z => g (cantorSigmaFull c z)) :=
  ((hg.comp (cantorSigmaFull_continuous hr_pos hr_half hball)).isClosedEmbedding
    (g_cantorSigmaFull_injective g hr_pos hr_half hball hU_disj hU_img)).isEmbedding


end CantorFullScheme
