import GowersSzemeredi.Proofs13QuadraticPartition
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
  let T := beta * n / (8 * M)
  have hT : 0 < T := by dsimp [T]; positivity
  have habs (i : Fin M) : |v i| = 2 * max (v i) 0 - v i := by
    linarith only [max_zero_add_max_neg_zero_eq_abs_self (v i),
      max_zero_sub_max_neg_zero_eq_self (v i)]
  have hpositive : beta * n ≤ 2 * ∑ i, max (v i) 0 := by
    simpa only [habs, Finset.sum_sub_distrib, ← Finset.mul_sum, hmean, sub_zero] using hdis
  by_contra hnone
  have hpoint (i : Fin M) :
      max (v i) 0 ≤ (if i ∈ B then w i else 0) + beta / 8 * w i + T := by
    have hterm : 0 ≤ beta / 8 * w i := mul_nonneg (by positivity) (hw i)
    have hvi := hv i
    split_ifs with hiB
    · exact max_le (by linarith only [hvi, hterm, hT]) (by linarith only [hw i, hterm, hT])
    refine max_le ?_ (by linarith only [hterm, hT])
    by_cases hinc : beta / 8 * w i ≤ v i
    · linarith only [hvi, hterm, (lt_of_not_ge fun h => hnone ⟨i, hiB, hinc, h⟩ : w i < T)]
    · linarith only [hT, lt_of_not_ge hinc]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) ↦ hpoint i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem_eq, ← Finset.mul_sum,
    hweights, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hMT : (M : Real) * T = beta * n / 8 := by simp only [T]; field_simp
  linarith only [hpositive, hsum, hbad, mul_pos hβ hn, hMT]

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
  let w : Fin M → Real := fun i ↦ (P i).carrier.card
  let v : Fin M → Real := fun i ↦ ∑ x ∈ (P i).carrier, relativeBalancedReal A S delta x
  have hM := section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpart
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hweights : ∑ i, w i = N := by
    dsimp only [w]; exact_mod_cast (by simpa using hpart.sum_card : ∑ i, (P i).carrier.card = N)
  have hmean : ∑ i, v i = 0 :=
    (hpart.sum_weights _).trans (relativeBalancedReal_sum_zero A S delta hcard)
  have hv (i : Fin M) : v i ≤ w i := (Finset.sum_le_sum fun x _ => (le_abs_self _).trans
    (relativeBalancedReal_abs_le_one A S delta hAS hδ hδone x)).trans_eq (by simp [w])
  obtain ⟨j, hjB, hjinc, hjsize⟩ := exists_positive_large_cell_outside_exception w v B beta N
    hM hβ hN (fun _ ↦ Nat.cast_nonneg _) hv hweights hmean
    (by simpa only [v, relativeBalanced, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_eq_abs] using hdis) hbad
  have hsub : (P j).carrier ⊆ S := (hgood j hjB).resolve_right fun hi => by
    have hvzero : v j = 0 := Finset.sum_eq_zero fun x hx =>
      relativeBalancedReal_eq_zero_outside A S delta hAS (Finset.disjoint_left.mp hi hx)
    have hsizepos : 0 < w j := (by positivity : 0 < beta * (N : Real) / (8 * M)).trans_le hjsize
    linarith only [hjinc, hvzero, mul_pos (by positivity : 0 < beta / 8) hsizepos]
  refine ⟨j, hjB, hsub, hjsize, ?_⟩
  simp only [w, v, relativeBalancedReal_sum, Finset.inter_eq_right.mpr hsub] at hjinc
  linarith only [hjinc]

end LeanProofs.GowersSzemeredi
