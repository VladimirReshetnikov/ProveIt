import GowersSzemeredi.Proofs16BipartiteQuasirandom

/-! A box approximation inherits a lower bound for the graph density.
The argument uses constant test functions in the box correlation bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A uniform degree lower bound and a box error epsilon give
`delta >= beta - epsilon`, without an assumption that delta is positive. -/
theorem density_lower_of_box {X Y : Type*} [Fintype X] [Fintype Y]
    (G : X → Y → Real) (hX : 0 < Fintype.card X) (hY : 0 < Fintype.card Y)
    {beta delta epsilon : Real} (heps : 0 ≤ epsilon)
    (hdegree : ∀ y, beta * Fintype.card X ≤ ∑ x, G x y)
    (hbox : boxSum (fun x y => G x y - delta) ≤
      epsilon^4 * (Fintype.card X : Real)^2 * (Fintype.card Y : Real)^2) :
    beta - epsilon ≤ delta := by
  have hcor := abs_box_correlation_le (fun x y => G x y - delta) heps hbox
    (fun _ => 1) (fun _ => 1) (by intro x; norm_num) (by intro y; norm_num)
  simp only [mul_one] at hcor
  have hsum : ∑ x, ∑ y, (G x y - delta) =
      (∑ y, ∑ x, G x y) - delta * Fintype.card X * Fintype.card Y := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum] at hcor
  have hdeg : beta * Fintype.card X * Fintype.card Y ≤ ∑ y, ∑ x, G x y := by
    have h := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hdegree y)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_left_comm] using h
  have hx : (0 : Real) < Fintype.card X := by exact_mod_cast hX
  have hy : (0 : Real) < Fintype.card Y := by exact_mod_cast hY
  have h := (abs_le.mp hcor).2
  have hmul : (beta - epsilon - delta) * ((Fintype.card X : Real) * Fintype.card Y) ≤ 0 := by
    nlinarith only [h, hdeg]
  have : beta - epsilon - delta ≤ 0 := (mul_le_mul_iff_left₀ (mul_pos hx hy)).mp (by simpa only [zero_mul] using hmul)
  linarith

end LeanProofs.GowersSzemeredi
