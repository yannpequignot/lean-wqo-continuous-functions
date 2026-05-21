import WqoContinuousFunctions.PointedGluing.Defs
import WqoContinuousFunctions.PrelimMemo.Scattered.CBAnalysis

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for CBrank_pointedGluing_regular
-/



/-- The block set for index n: sequences starting with n zeros then a nonzero value. -/
def blockSet (n : ℕ) : Set (ℕ → ℕ) :=
  {x | (∀ k, k < n → x k = 0) ∧ x n ≠ 0}

/--
The block set is open.
-/
lemma blockSet_isOpen (n : ℕ) : IsOpen (blockSet n) := by
  have h_open : IsOpen {x : ℕ → ℕ | x n ≠ 0} := isOpen_ne.preimage (continuous_apply n)
  have h_open' : IsOpen {x : ℕ → ℕ | ∀ k < n, x k = 0} := by
    rw [isOpen_pi_iff]
    exact fun f hf => ⟨Finset.range n, fun k => {x | x = 0}, fun k hk => ⟨by aesop, by aesop⟩, fun x hx => by aesop⟩
  exact h_open'.inter h_open

/--
For x in a block, x ≠ zeroStream.
-/
lemma ne_zeroStream_of_blockSet {n : ℕ} {x : ℕ → ℕ} (hx : x ∈ blockSet n) :
    x ≠ zeroStream :=
  fun h => hx.2 <| h ▸ rfl

/--
prependZerosOne n maps into blockSet n.
-/
lemma prependZerosOne_mem_blockSet (n : ℕ) (x : ℕ → ℕ) :
    prependZerosOne n x ∈ blockSet n := by
  exact ⟨fun k hk => by unfold prependZerosOne; aesop, by unfold prependZerosOne; aesop⟩

/--
For x in block n of the pointed gluing, stripZerosOne n x ∈ A n.
-/
lemma strip_mem_of_blockSet (A : ℕ → Set (ℕ → ℕ)) (x : PointedGluingSet A) (n : ℕ)
    (hx : x.val ∈ blockSet n) :
    stripZerosOne n x.val ∈ A n := by
  rcases x with ⟨x, hx⟩
  cases' ‹x ∈ PointedGluingSet A› with hx_zero hx_image
  · cases hx.2 (by aesop)
  · obtain ⟨i, hi, hi'⟩ := Set.mem_iUnion.mp hx_image
    by_cases hi_lt_n : i < n <;> by_cases hi_eq_n : i = n <;> simp_all +decide
    · have := hx.1 i hi_lt_n; simp_all +decide
      have := congr_fun hi'.2 i; simp_all +decide [prependZerosOne]
    · convert hi'.1 using 1
      rw [← hi'.2, stripZerosOne_prependZerosOne]
    · have := hx.2; simp_all +decide
      exact False.elim <| this <| by rw [← hi'.2] ; exact if_pos <| by omega

/--
The composition stripZerosOne n ∘ Subtype.val is continuous on PointedGluingSet A.
-/
lemma continuous_strip_val (A : ℕ → Set (ℕ → ℕ)) (n : ℕ) :
    Continuous (fun (x : PointedGluingSet A) => stripZerosOne n x.val) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x; rw [ContinuousAt] ; exact (by
  rw [nhds_induced]
  exact Filter.Tendsto.comp (continuous_iff_continuousAt.mp (show Continuous fun x : ℕ → ℕ => stripZerosOne n x from by continuity) _) (Filter.tendsto_comap))

/--
PointedGluingFun on a block point equals prependZerosOne n applied to
    f_n on the stripped point (with explicit block index).
-/
lemma pointedGluingFun_block_eq
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (n : ℕ)
    (x : PointedGluingSet A) (hx : x.val ∈ blockSet n) :
    PointedGluingFun A B f x =
      prependZerosOne n (f n ⟨stripZerosOne n x.val, strip_mem_of_blockSet A x n hx⟩).val := by
  -- Since `x.val ∈ blockSet n`, we have `firstNonzero x.val = n`.
  have h_firstNonzero : firstNonzero x.val = n := by
    unfold firstNonzero
    split_ifs <;> simp_all +decide [Nat.find_eq_iff]
    · exact ⟨hx.2, fun k hk => hx.1 k hk⟩
    · exact absurd (hx.2) (by simp +decide [*])
  unfold PointedGluingFun
  split_ifs <;> simp_all +decide [ne_zeroStream_of_blockSet hx]
  grind +extAll

/--
If strip(x) is f_n-isolated in CBLevel g_n γ, then x is g-isolated in CBLevel g γ.
    This is the key step for the successor case of CBLevel_block_forward.
    Uses the IH that block_forward holds at level γ (for ALL points in block n).
-/
lemma isolatedLocus_block_transfer
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (n : ℕ) (γ : Ordinal.{0})
    (ih : ∀ (z : PointedGluingSet A) (hz : z.val ∈ blockSet n),
      z ∈ CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) γ →
      ⟨stripZerosOne n z.val, strip_mem_of_blockSet A z n hz⟩ ∈
        CBLevel (fun (y : A n) => (f n y : ℕ → ℕ)) γ)
    (x : PointedGluingSet A) (hx : x.val ∈ blockSet n)
    (hxCB : x ∈ CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) γ)
    (hiso : ⟨stripZerosOne n x.val, strip_mem_of_blockSet A x n hx⟩ ∈
      isolatedLocus (fun (y : A n) => (f n y : ℕ → ℕ))
        (CBLevel (fun (y : A n) => (f n y : ℕ → ℕ)) γ)) :
    x ∈ isolatedLocus (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ))
      (CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) γ) := by
  obtain ⟨V₀, hV₀_open, hV₀, hV₀_const⟩ := hiso.2
  obtain ⟨V₁, hV₁_open, rfl⟩ := hV₀_open
  refine ⟨hxCB, ?_, ?_, ?_⟩
  exact { y : PointedGluingSet A | y.val ∈ blockSet n ∧ stripZerosOne n y.val ∈ V₁ }
  · exact IsOpen.inter (blockSet_isOpen n |> IsOpen.preimage continuous_subtype_val) (hV₁_open.preimage (continuous_strip_val A n))
  · simp_all +decide
    intro a ha ha' ha'' ha'''
    rw [pointedGluingFun_block_eq A B f n ⟨a, ha⟩ ha', pointedGluingFun_block_eq A B f n x hx]
    rw [hV₀_const _ _ ha'' (ih _ _ ha' ha''')]

/--
For x in block n of the pointed gluing, if x ∈ CBLevel F β,
    then the stripped point is in CBLevel f_n β.
    This is proved by transfinite induction on β.
-/
lemma CBLevel_block_forward
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (n : ℕ) (β : Ordinal.{0})
    (x : PointedGluingSet A) (hx : x.val ∈ blockSet n)
    (hxCB : x ∈ CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) β) :
    ⟨stripZerosOne n x.val, strip_mem_of_blockSet A x n hx⟩ ∈
      CBLevel (fun (y : A n) => (f n y : ℕ → ℕ)) β := by
  induction' β using Ordinal.limitRecOn with β ih generalizing x
  · unfold CBLevel; aesop
  · rw [CBLevel_succ'] at *
    refine ⟨ih x hx hxCB.1, ?_⟩
    exact fun h => hxCB.2 <| isolatedLocus_block_transfer A B f n β ih x hx hxCB.1 h
  · rw [CBLevel_limit _ _ ‹_›] at hxCB ⊢
    aesop

/--
Block n of the pointed gluing eventually empties in the CB derivative
    once we pass CBRank of f_n.
-/
lemma CBLevel_block_empty_above_rank
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (n : ℕ) (β : Ordinal.{0})
    (hβ : CBRank (fun (x : A n) => (f n x : ℕ → ℕ)) ≤ β) :
    ∀ (x : PointedGluingSet A), x.val ∈ blockSet n →
      x ∉ CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) β := by
  intros x hx_block hx_level
  have hstrip_level : ⟨stripZerosOne n x.val, strip_mem_of_blockSet A x n hx_block⟩ ∈ CBLevel (fun y => (f n y : ℕ → ℕ)) β := by
    apply CBLevel_block_forward A B f n β x hx_block hx_level
  have hstrip_empty : CBLevel (fun y => (f n y : ℕ → ℕ)) (CBRank (fun y => (f n y : ℕ → ℕ))) = ∅ := by
    apply CBLevel_eq_empty_at_rank; exact hf_scat n
  exact hstrip_empty.subset (CBLevel_antitone _ hβ hstrip_level)

set_option maxHeartbeats 4000000 in
/-- Backward direction: if `strip(x) ∈ CBLevel f_n β`, then `x ∈ CBLevel F β`. -/
lemma CBLevel_block_backward
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (n : ℕ) (β : Ordinal.{0})
    (x : PointedGluingSet A) (hx : x.val ∈ blockSet n)
    (hxCB : ⟨stripZerosOne n x.val, strip_mem_of_blockSet A x n hx⟩ ∈
      CBLevel (fun (y : A n) => (f n y : ℕ → ℕ)) β) :
    x ∈ CBLevel (fun (y : PointedGluingSet A) => (PointedGluingFun A B f y : ℕ → ℕ)) β := by
  contrapose! hxCB with h
  induction' β using Ordinal.limitRecOn with β ih generalizing x
  · grind +suggestions
  · contrapose! h
    simp_all +decide [CBLevel_succ']
    refine ⟨?_, ?_⟩
    · exact Classical.not_not.1 fun hx' => ih _ x.2 hx hx' h.1
    · rintro ⟨U, hU₁, hU₂, hU₃⟩
      refine h.2 ⟨?_, ?_⟩
      · exact h.1
      · refine ⟨{ y : A n | ⟨prependZerosOne n y.val, prependZerosOne_mem_pointedGluingSet A n y.val y.prop⟩ ∈ hU₁ }, ?_, ?_, ?_⟩
        · convert hU₂.preimage _
          refine Continuous.subtype_mk ?_ ?_
          refine continuous_pi_iff.mpr ?_
          intro i; by_cases hi : i < n <;> simp +decide [hi, prependZerosOne]
          · exact continuous_const
          · split_ifs <;> [exact continuous_const; exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val]
        · convert hU₃.1 using 1
          simp +decide
          congr! 1
          exact Subtype.ext <| by have := hx.1; have := hx.2; exact (by
          ext k; by_cases hk : k < n <;> simp_all +decide [prependZerosOne, stripZerosOne]
          have := x.2
          cases this <;> simp_all +decide [PointedGluingSet]
          · exact False.elim <| this <| by rfl
          · obtain ⟨i, y, hy, hy'⟩ := ‹∃ i, ∃ x_1 ∈ A i, prependZerosOne i x_1 = x.val›; have := congr_fun hy' n; simp_all +decide [prependZerosOne]
            have := congr_fun hy' i; simp_all +decide [prependZerosOne]
            grind +revert)
        · intro y hy
          have := hU₃.2 ⟨prependZerosOne n y.val, prependZerosOne_mem_pointedGluingSet A n y.val y.prop⟩ ⟨hy.1, ?_⟩
          · convert congr_arg (fun z => stripZerosOne n z) this using 1
            · convert stripZerosOne_prependZerosOne n (f n y |> Subtype.val) using 1
              · exact Eq.symm (stripZerosOne_prependZerosOne n _)
              · convert congr_arg (fun z => stripZerosOne n z) (pointedGluingFun_block_eq A B f n ⟨prependZerosOne n y.val, prependZerosOne_mem_pointedGluingSet A n y.val y.prop⟩ (prependZerosOne_mem_blockSet n y.val)) using 1
                simp +decide [stripZerosOne_prependZerosOne]
            · grind +suggestions
          · convert CBLevel_block_forward A B f n β _ _ _ using 1
            rotate_left
            exact ⟨prependZerosOne n y.val, prependZerosOne_mem_pointedGluingSet A n y.val y.prop⟩
            exact prependZerosOne_mem_blockSet n y.val
            · grind +suggestions
            · grind +suggestions
  · rw [CBLevel_limit _ _ ‹_›] at h ⊢
    aesop

/--
CBLevel f_n γ is nonempty when γ < CBRank f_n and f_n is scattered.
-/
lemma CBLevel_nonempty_below_rank {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (_hf : ScatteredFun f) (γ : Ordinal.{0})
    (hγ : γ < CBRank f) : (CBLevel f γ).Nonempty := by
  contrapose! hγ
  refine csInf_le' ?_
  simp +decide [hγ, CBLevel_succ']

/--
For block points, the pointed gluing function value ≠ zeroStream.
-/
lemma pointedGluingFun_ne_zeroStream
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (n : ℕ)
    (x : PointedGluingSet A) (hx : x.val ∈ blockSet n) :
    PointedGluingFun A B f x ≠ zeroStream := by
  rw [pointedGluingFun_block_eq A B f n x hx]
  unfold prependZerosOne zeroStream
  exact fun h => by have := congr_fun h n; simp +decide at this

/--
For large enough n, prependZerosOne n x is in any open neighborhood of zeroStream.
-/
lemma prependZerosOne_eventually_in_nhds
    (U : Set (ℕ → ℕ)) (hU : IsOpen U) (hU0 : zeroStream ∈ U) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℕ → ℕ, prependZerosOne n x ∈ U := by
  rw [isOpen_pi_iff] at hU
  obtain ⟨I, u, hu⟩ := hU 0 hU0
  use I.sup id + 1
  intro n hn x; refine hu.2 ?_; intro i hi; by_cases hi' : i < n <;> simp_all +decide [prependZerosOne]
  exact absurd hi' (not_le_of_gt (lt_of_le_of_lt (Finset.le_sup (f := id) hi) hn))

/--
Given γ < α = ⨆ cbranks, there exist arbitrarily large n with cbranks n > γ.
-/
lemma exists_large_cbrank
    (cbranks : ℕ → Ordinal.{0}) (hreg : IsRegularOrdSeq cbranks)
    (γ : Ordinal.{0}) (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n)
    (hγ : γ < α) (N : ℕ) :
    ∃ n ≥ N, cbranks n > γ := by
  contrapose! hγ
  refine hαsup ▸ ciSup_le' ?_
  intro n
  induction' N with N ih generalizing n
  · exact hγ n n.zero_le
  · by_cases h : cbranks N ≤ γ
    · exact ih (fun n hn => if hn' : n = N then hn'.symm ▸ h else hγ n (Nat.lt_of_le_of_ne hn (Ne.symm hn'))) n
    · exact absurd (hreg N) (by rintro ⟨n, hn₁, hn₂⟩ ; exact h (hn₂.trans (hγ n (by linarith))))

/--
The zeroStream point is in CBLevel F β for all β ≤ α.
-/
lemma zeroStream_mem_CBLevel_le
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (cbranks : ℕ → Ordinal.{0})
    (hreg : IsRegularOrdSeq cbranks)
    (hα : ∀ i, CBRank (fun (x : A i) => (f i x : ℕ → ℕ)) = cbranks i)
    (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n) (hαpos : α > 0)
    (β : Ordinal.{0}) (hβ : β ≤ α) :
    ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ ∈
      CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) β := by
  induction' β using Ordinal.limitRecOn with β ih
  · -- The universal set contains all elements, including the zeroStream.
    simp [CBLevel]
  · have h_zeroStream_not_isolated : ¬(⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ ∈ isolatedLocus (fun y : PointedGluingSet A => (PointedGluingFun A B f y : ℕ → ℕ)) (CBLevel (fun y : PointedGluingSet A => (PointedGluingFun A B f y : ℕ → ℕ)) β)) := by
      intro h
      obtain ⟨U₀, hU₀_open, hU₀_zero, hU₀_const⟩ : ∃ U₀ : Set (ℕ → ℕ), IsOpen U₀ ∧ zeroStream ∈ U₀ ∧ ∀ y ∈ CBLevel (fun y : PointedGluingSet A => (PointedGluingFun A B f y : ℕ → ℕ)) β, y.val ∈ U₀ → PointedGluingFun A B f y = PointedGluingFun A B f ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ := by
        obtain ⟨U, hU₁, hU₂, hU₃⟩ := h.2
        obtain ⟨U₀, hU₀₁, hU₀₂⟩ := hU₁; use U₀; aesop
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℕ → ℕ, prependZerosOne n x ∈ U₀ := prependZerosOne_eventually_in_nhds U₀ hU₀_open hU₀_zero
      obtain ⟨n, hnN, hn⟩ : ∃ n ≥ N, cbranks n > β := exists_large_cbrank cbranks hreg β α hαsup (by
      exact lt_of_lt_of_le (Order.lt_succ β) hβ) N
      obtain ⟨a_n, ha_n⟩ : ∃ a_n : A n, ⟨a_n.val, a_n.prop⟩ ∈ CBLevel (fun y : A n => (f n y : ℕ → ℕ)) β := by
        have := CBLevel_nonempty_below_rank (fun y : A n => (f n y : ℕ → ℕ)) (hf_scat n) β (by aesop)
        exact ⟨⟨this.choose, this.choose_spec |> fun h => by
          exact this.choose.2⟩, this.choose_spec⟩
      have hy : ⟨prependZerosOne n a_n.val, prependZerosOne_mem_pointedGluingSet A n a_n.val a_n.prop⟩ ∈ CBLevel (fun y : PointedGluingSet A => (PointedGluingFun A B f y : ℕ → ℕ)) β := by
        apply CBLevel_block_backward
        convert ha_n using 1
        exact Subtype.ext <| stripZerosOne_prependZerosOne n a_n.val
        exact prependZerosOne_mem_blockSet n a_n.val
      have := hU₀_const _ hy (hN n hnN _)
      have := pointedGluingFun_ne_zeroStream A B f n ⟨prependZerosOne n a_n.val, prependZerosOne_mem_pointedGluingSet A n a_n.val a_n.prop⟩ (prependZerosOne_mem_blockSet n a_n.val) ; simp_all +decide [PointedGluingFun]
    grind +suggestions
  · rw [CBLevel_limit _ _ ‹_›]
    exact Set.mem_iInter₂.2 fun γ hγ => by rename_i h; exact h γ hγ (le_trans hγ.le hβ)

/--
Only the zeroStream point is in CBLevel F α.
-/
lemma CBLevel_pointedGluing_subset
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (cbranks : ℕ → Ordinal.{0})
    (_hreg : IsRegularOrdSeq cbranks)
    (hα : ∀ i, CBRank (fun (x : A i) => (f i x : ℕ → ℕ)) = cbranks i)
    (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n) (hαpos : α > 0) :
    CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) α ⊆
      {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩} := by
  intro x hx
  by_contra h_contra
  obtain ⟨n, hn⟩ : ∃ n, x.val ∈ blockSet n := by
    have h_block : x.val ∈ ⋃ i, prependZerosOne i '' (A i) := by
      exact Or.resolve_left (x.2) fun h => h_contra <| Subtype.ext <| by aesop
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h_block
    exact ⟨n, by obtain ⟨y, hy, hy'⟩ := hn; exact hy'.symm ▸ prependZerosOne_mem_blockSet n y⟩
  have h_cbrank_le : cbranks n ≤ α := by
    exact hαsup ▸ le_ciSup (Ordinal.bddAbove_range cbranks) n
  exact CBLevel_block_empty_above_rank A B f hf_scat n α (by aesop) x hn hx

end
