import GowersSzemeredi.Proofs05IntegerRefinement

/-! Average-size bookkeeping for genuine integer refinements. This is the
quantitative link from the modular inverse theorem to the paper's ordinary
progression partitions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Summing over the cells of an exact finite partition preserves the sum
of any additive function, without a real- or complex-valued restriction. -/
theorem IsPartition.sum_eq {X E : Type*} [DecidableEq X] [AddCommMonoid E]
    {M : Nat} {P : Fin M → Finset X} {S : Finset X}
    (hP : IsPartition P S) (f : X → E) :
    (∑ i, ∑ x ∈ P i, f x) = ∑ x ∈ S, f x := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hP.2 i j (bne_iff_ne.mpr hij)
  have hunion : Finset.univ.biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hP.1 x).symm
  rw [← hunion]
  exact (Finset.sum_biUnion hdisj).symm

/-- The norm of a sum is bounded by the sum of the norms of its cell sums. -/
theorem IsPartition.norm_sum_le {X E : Type*} [DecidableEq X] [NormedAddCommGroup E]
    {M : Nat} {P : Fin M → Finset X} {S : Finset X}
    (hP : IsPartition P S) (f : X → E) :
    ‖∑ x ∈ S, f x‖ ≤ ∑ i, ‖∑ x ∈ P i, f x‖ := by
  rw [← hP.sum_eq f]
  exact _root_.norm_sum_le (Finset.univ : Finset (Fin M)) (fun i => ∑ x ∈ P i, f x)

/-- Refinement increases the total discrepancy, for functions valued in
any normed abelian group. This preserves the inverse theorem's bias bound
when replacing modular cells by genuine integer progressions. -/
theorem IsRefinement.sum_norm_mono {X E : Type*} [DecidableEq X] [NormedAddCommGroup E]
    {M L : Nat} (P : Fin M → Finset X) (R : Fin L → Finset X) (S : Finset X)
    (hP : IsPartition P S) (hR : IsRefinement R P) (f : X → E) :
    (∑ i, ‖∑ x ∈ P i, f x‖) ≤ ∑ j, ‖∑ x ∈ R j, f x‖ := by
  classical
  have hinterpart (i : Fin M) : IsPartition (fun j => R j ∩ P i) (P i) := by
    constructor
    · intro x
      constructor
      · intro hx
        have hparent : ∃ i, x ∈ P i := ⟨i, hx⟩
        obtain ⟨j, hj⟩ := (hR.1 x).mpr hparent
        exact ⟨j, Finset.mem_inter.mpr ⟨hj, hx⟩⟩
      · rintro ⟨j, hj⟩
        exact (Finset.mem_inter.mp hj).2
    · intro j k hjk
      exact (hR.2.2 j k hjk).mono Finset.inter_subset_left Finset.inter_subset_left
  have hinner (j : Fin L) :
      (∑ i, ‖∑ x ∈ R j ∩ P i, f x‖) = ‖∑ x ∈ R j, f x‖ := by
    obtain ⟨i0, hsub⟩ := hR.2.1 j
    calc
      (∑ i, ‖∑ x ∈ R j ∩ P i, f x‖) = ‖∑ x ∈ R j ∩ P i0, f x‖ := by
        apply Finset.sum_eq_single i0
        · intro i _ hi
          have hdisj : Disjoint (R j) (P i) :=
            (hP.2 i0 i (bne_iff_ne.mpr hi.symm)).mono hsub Finset.Subset.rfl
          rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
          simp
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = ‖∑ x ∈ R j, f x‖ := by rw [Finset.inter_eq_left.mpr hsub]
  calc
    (∑ i, ‖∑ x ∈ P i, f x‖) ≤ ∑ i, ∑ j, ‖∑ x ∈ R j ∩ P i, f x‖ :=
      Finset.sum_le_sum (fun i _ => (hinterpart i).norm_sum_le f)
    _ = ∑ j, ∑ i, ‖∑ x ∈ R j ∩ P i, f x‖ := Finset.sum_comm
    _ = ∑ j, ‖∑ x ∈ R j, f x‖ := Finset.sum_congr rfl (fun j _ => hinner j)

/-- The average size of a partition of the cyclic group is exactly `N/M`,
including partitions with empty cells. -/
theorem partition_averageCellSize {N M : Nat} [NeZero N]
    (P : Fin M → Finset (ZMod N)) (hP : IsPartition P Finset.univ) :
    averageCellSize P = (N : Real) / M := by
  unfold averageCellSize
  rw [hP.sum_card]
  simp only [Finset.card_univ, ZMod.card]

/-- The genuine integer refinement has average cell size at least one
quarter of the square root of the old average. No primality is required. -/
theorem integer_representative_refinement_average {N M : Nat} [NeZero N]
    (P : Fin M → ModAP N)
    (hP : IsPartition (fun i => (P i).carrier) Finset.univ) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsRefinement (fun j => (R j).carrier) (fun i => (P i).carrier) ∧
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      Real.sqrt (averageCellSize (fun i => (P i).carrier)) / 4 ≤
        averageCellSize (fun j => (R j).carrier) := by
  classical
  obtain ⟨L, R, href, hR, hRinteger, hcount⟩ :=
    integer_representative_partition_refinement P Finset.univ hP
  have hMpos : 0 < M := by
    obtain ⟨i, _⟩ := (hP.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact (Nat.zero_le i.val).trans_lt i.isLt
  have hLpos : 0 < L := by
    obtain ⟨j, _⟩ := (hR.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact (Nat.zero_le j.val).trans_lt j.isLt
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMreal : (0 : Real) < M := by exact_mod_cast hMpos
  have hLreal : (0 : Real) < L := by exact_mod_cast hLpos
  have hcount' : (L : Real) ≤ 4 * Real.sqrt ((N : Real) * M) := by
    simpa only [Finset.card_univ, ZMod.card] using hcount
  have hproduct : Real.sqrt ((N : Real) / M) * Real.sqrt ((N : Real) * M) = N := by
    rw [← Real.sqrt_mul (div_nonneg hNreal.le hMreal.le)]
    have heq : ((N : Real) / M) * ((N : Real) * M) = (N : Real) ^ 2 := by
      field_simp [hMreal.ne'] <;> ring
    rw [heq, Real.sqrt_sq hNreal.le]
  have hscaled := mul_le_mul_of_nonneg_right hcount'
    (Real.sqrt_nonneg ((N : Real) / M))
  refine ⟨L, R, href, hR, hRinteger, ?_⟩
  rw [partition_averageCellSize _ hP, partition_averageCellSize _ hR,
    le_div_iff₀ hLreal]
  nlinarith [hproduct]

/-- The square-root and factor-four loss of genuine refinement can be
absorbed into any strictly smaller exponent than half the old exponent,
by increasing the modulus threshold. -/
theorem exists_integer_refinement_power_threshold (beta beta' : Real)
    (hgap : beta < beta' / 2) :
    ∃ N0 : Nat, 1 ≤ N0 ∧ ∀ N : Nat, N0 ≤ N →
      (N : Real) ^ beta ≤ Real.sqrt ((N : Real) ^ beta') / 4 := by
  let gap : Real := beta' / 2 - beta
  have hgap0 : 0 < gap := by dsimp [gap]; linarith
  let X : Real := max 1 ((4 : Real) ^ gap⁻¹)
  let N0 : Nat := Nat.ceil X
  have hfloor : X ≤ N0 := Nat.le_ceil X
  have hN0 : 1 ≤ N0 := by
    have hone : (1 : Real) ≤ N0 := (le_max_left _ _).trans hfloor
    exact_mod_cast hone
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  have hNreal : X ≤ (N : Real) := hfloor.trans (by exact_mod_cast hN)
  have hNpos : (0 : Real) < N := by
    have h := (le_max_left _ _).trans hNreal
    linarith
  have hbound : (4 : Real) ^ gap⁻¹ ≤ (N : Real) :=
    (le_max_right _ _).trans hNreal
  have hpow : (4 : Real) ≤ (N : Real) ^ gap := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbound hgap0.le
    rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ hgap0.ne', Real.rpow_one] at h
    exact h
  have hscaled := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNpos.le beta)
  have hexponent : gap + beta = beta' / 2 := by dsimp [gap]; ring
  have hproduct : (N : Real) ^ gap * (N : Real) ^ beta = (N : Real) ^ (beta' / 2) := by
    rw [← Real.rpow_add hNpos, hexponent]
  have hsqrt : Real.sqrt ((N : Real) ^ beta') = (N : Real) ^ (beta' / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  rw [hproduct] at hscaled
  rw [hsqrt]
  linarith

end LeanProofs.GowersSzemeredi
