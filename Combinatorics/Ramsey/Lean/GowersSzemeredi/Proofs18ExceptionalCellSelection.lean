import GowersSzemeredi.Proofs18RelativeBalance

/-! Discrepancy selection after discarding a small exceptional family of
partition cells, as needed for cells meeting an interval boundary. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Mean-zero discrepancy cannot be concentrated entirely in small,
low-increment, or exceptional cells when exceptional mass is small. -/
theorem exists_positive_large_cell_outside_exception {M : Nat}
    (w v : Fin M → Real) (B : Finset (Fin M)) (beta n : Real)
    (hM : 0 < M) (hβ : 0 < beta) (hn : 0 < n)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, v i ≤ w i)
    (hweights : ∑ i, w i = n) (hmean : ∑ i, v i = 0)
    (hdis : beta * n ≤ ∑ i, |v i|)
    (hbad : ∑ i ∈ B, w i ≤ beta * n / 8) :
    ∃ i, i ∉ B ∧ beta / 8 * w i ≤ v i ∧ beta * n / (8 * M) ≤ w i := by
  classical
  let T := beta * n / (8 * M)
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have hT : 0 < T := by dsimp [T]; positivity
  have habs (i : Fin M) : |v i| = 2 * max (v i) 0 - v i := by
    rcases le_total 0 (v i) with hi | hi
    · rw [abs_of_nonneg hi, max_eq_left hi]; ring
    · rw [abs_of_nonpos hi, max_eq_right hi]; ring
  have hpositive : beta * n ≤ 2 * ∑ i, max (v i) 0 := by
    simpa only [habs, Finset.sum_sub_distrib, ← Finset.mul_sum, hmean, sub_zero] using hdis
  by_contra hnone
  have hpoint (i : Fin M) :
      max (v i) 0 ≤ (if i ∈ B then w i else 0) + beta / 8 * w i + T := by
    by_cases hiB : i ∈ B
    · rw [if_pos hiB]
      have hmax : max (v i) 0 ≤ w i := max_le (hv i) (hw i)
      have hterm : 0 ≤ beta / 8 * w i := mul_nonneg (by positivity) (hw i)
      linarith only [hmax, hterm, hT]
    · rw [if_neg hiB, zero_add]
      have hbadCell : v i < beta / 8 * w i ∨ w i < T := by
        by_cases hinc : beta / 8 * w i ≤ v i
        · exact Or.inr (lt_of_not_ge (fun hsize ↦ hnone ⟨i, hiB, hinc, hsize⟩))
        · exact Or.inl (lt_of_not_ge hinc)
      have hterm : 0 ≤ beta / 8 * w i := mul_nonneg (by positivity) (hw i)
      apply max_le
      · rcases hbadCell with hi | hi
        · linarith only [hi, hT]
        · have hvi := hv i
          linarith only [hi, hvi, hterm]
      · linarith only [hterm, hT]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) ↦ hpoint i)
  have hbadEq : (∑ i : Fin M, if i ∈ B then w i else 0) = ∑ i ∈ B, w i := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hbadEq,
    ← Finset.mul_sum, hweights] at hsum
  have hTsum : (∑ _i : Fin M, T) = beta * n / 8 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T]
    field_simp
  rw [hTsum] at hsum
  have hpos := mul_pos hβ hn
  linarith only [hpositive, hsum, hbad, hpos]

/-- Discarding boundary cells of mass at most beta*N/8 retains a genuine
relative-density increment on a cell contained in the original support. -/
theorem relative_density_increment_away_from_boundary {N M : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (delta beta : Real) (P : Fin M → ModAP N)
    (B : Finset (Fin M))
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hβ : 0 < beta)
    (hcard : (A.card : Real) = delta * S.card)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (hgood : ∀ i, i ∉ B → (P i).carrier ⊆ S ∨ Disjoint (P i).carrier S)
    (hbad : ∑ i ∈ B, ((P i).carrier.card : Real) ≤ beta * N / 8)
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (P i).carrier, relativeBalanced A S delta x‖) :
    ∃ j : Fin M, j ∉ B ∧ (P j).carrier ⊆ S ∧
      beta * N / (8 * M) ≤ ((P j).carrier.card : Real) ∧
      (delta + beta / 8) * (P j).carrier.card ≤ (A ∩ (P j).carrier).card := by
  classical
  let w : Fin M → Real := fun i ↦ (P i).carrier.card
  let v : Fin M → Real := fun i ↦ ∑ x ∈ (P i).carrier, relativeBalancedReal A S delta x
  have hM := section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpart
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hweights : ∑ i, w i = N := by
    have hc : ∑ i, (P i).carrier.card = N := by simpa using hpart.sum_card
    dsimp only [w]
    exact_mod_cast hc
  have hmean : ∑ i, v i = 0 := by
    rw [show (∑ i, v i) = ∑ i, ∑ x ∈ (P i).carrier, relativeBalancedReal A S delta x from rfl,
      hpart.sum_weights]
    exact relativeBalancedReal_sum_zero A S delta hcard
  have hv (i : Fin M) : v i ≤ w i := by
    calc
      _ ≤ ∑ x ∈ (P i).carrier, |relativeBalancedReal A S delta x| :=
        Finset.sum_le_sum fun x _ ↦ le_abs_self _
      _ ≤ ∑ _x ∈ (P i).carrier, (1 : Real) :=
        Finset.sum_le_sum fun x _ ↦ relativeBalancedReal_abs_le_one A S delta hAS hδ hδone x
      _ = _ := by simp [w]
  obtain ⟨j, hjB, hjinc, hjsize⟩ := exists_positive_large_cell_outside_exception w v B beta N
    hM hβ hN (fun _ ↦ Nat.cast_nonneg _) hv hweights hmean
    (by simpa only [v, relativeBalanced, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hdis) hbad
  have hsub : (P j).carrier ⊆ S := by
    rcases hgood j hjB with hi | hi
    · exact hi
    · have hvzero : v j = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact relativeBalancedReal_eq_zero_outside A S delta hAS
          (fun hxS ↦ Finset.disjoint_left.mp hi hx hxS)
      have hsizepos : 0 < w j := lt_of_lt_of_le (by positivity : 0 < beta * (N : Real) / (8 * M)) hjsize
      have hincpos := mul_pos (by positivity : 0 < beta / 8) hsizepos
      rw [hvzero] at hjinc
      exact (not_le_of_gt hincpos hjinc).elim
  refine ⟨j, hjB, hsub, hjsize, ?_⟩
  change beta / 8 * ((P j).carrier.card : Real) ≤
    ∑ x ∈ (P j).carrier, relativeBalancedReal A S delta x at hjinc
  rw [relativeBalancedReal_sum, Finset.inter_eq_right.mpr hsub] at hjinc
  nlinarith only [hjinc]

end LeanProofs.GowersSzemeredi
