import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ShiftedNumerator

/-- The shifted numerator has one discrete endpoint envelope before multiplication
by the independent positive factors `k`, `G`, `H`. -/
theorem shifted_Q_bounds {A C D G H k W J Q : ℤ}
    (hA : 2 ≤ A) (hC : 1 ≤ C) (hD : A^2 ≤ D) (hCD : C^2 < D)
    (hG : A ≤ G) (hH : 1 ≤ H) (hk : 3 ≤ k) (hW : 0 < W) (hWA : W < A)
    (hJ : J=4*A-5) (hQ : Q=3*W*C-2*(W^2-1)) :
    0 < J*(W^2+1)+Q ∧
      J*(W^2+1)+Q < k*(8*D^2-4*D-1)*G*H := by
  have hD1 : 1 ≤ D := by nlinarith only [hA,hD]
  have hW2 : W^2+1 ≤ D := by nlinarith only [hW,hWA,hD]
  have hWC : W*C+1 ≤ D := by nlinarith only [sq_nonneg (W-C),hW2,hCD]
  have hnum : J*(W^2+1)+Q = (4*A-7)*W^2+3*W*C+4*A-3 := by rw [hJ,hQ]; ring
  have hpos : 0 < J*(W^2+1)+Q := by
    rw [hnum]
    nlinarith only [mul_nonneg (show 0 ≤ 4*A-7 by omega) (sq_nonneg W),
      mul_pos hW (show 0 < C by omega),hA]
  have htop : J*(W^2+1)+Q ≤ (4*A-4)*D+1 := by
    rw [hnum]
    nlinarith only [mul_nonneg (show 0 ≤ 4*A-7 by omega)
      (show 0 ≤ D-W^2-1 by omega),hWC]
  have hfac : 0 ≤ 8*D^2-4*D-1 := by nlinarith only [hD1,sq_nonneg (D-1)]
  have hgap : (4*A-4)*D+1 < 3*(8*D^2-4*D-1)*A := by
    nlinarith only [mul_nonneg (show 0 ≤ A by omega)
      (mul_nonneg (show 0 ≤ D-1 by omega) (show 0 ≤ 24*D+8 by omega)),hA,hD1]
  have hlift : 3*(8*D^2-4*D-1)*A ≤ k*(8*D^2-4*D-1)*G*H := by
    calc
      _ ≤ k*(8*D^2-4*D-1)*G := mul_le_mul
        (mul_le_mul_of_nonneg_right hk hfac) hG (by omega) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (by omega) hfac) (by omega)) hH
  exact ⟨hpos,htop.trans_lt (hgap.trans_le hlift)⟩

#print axioms shifted_Q_bounds
end ShiftedNumerator
