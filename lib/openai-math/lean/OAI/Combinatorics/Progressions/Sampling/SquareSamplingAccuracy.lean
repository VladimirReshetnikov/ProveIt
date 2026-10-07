import OAI.Combinatorics.Progressions.Lattices.AffineSourceAccuracy

namespace OAI

section

namespace Erdos3

theorem squareSamplingAccuracy_bound {Q L δ E M η ε : ℝ}
    (hQ : 0 ≤ Q) (hδ0 : 0 ≤ δ) (hM0 : 0 ≤ M) (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε)
    (hδ : δ ≤ Real.exp (-(Q + 20))) (hE : E ≤ Real.exp (-(Q + 20)))
    (hM : M ≤ Real.exp L)
    (hη : η ≤ Real.exp (-(Q + 2 * L + 20)))
    (hε : ε ≤ Real.exp (-(Q + 2 * L + 20))) :
    6 * δ ^ 2 + 4 * E + 2 * M ^ 2 * (2 * η + ε) ≤ Real.exp (-Q) := by
  let b := Real.exp (-(Q + 20))
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hδ2 : δ ^ 2 ≤ b :=
    (pow_le_pow_left₀ hδ0 hδ 2).trans (by nlinarith)
  have hmass : M ^ 2 ≤ Real.exp (2 * L) := by
    calc
      M ^ 2 ≤ (Real.exp L) ^ 2 := pow_le_pow_left₀ hM0 hM 2
      _ = Real.exp (2 * L) := (Real.exp_nat_mul L 2).symm
  have herror : 2 * η + ε ≤ 3 * Real.exp (-(Q + 2 * L + 20)) := by linarith
  have hp := mul_le_mul hmass herror (by positivity : 0 ≤ 2 * η + ε) (Real.exp_pos _).le
  have heq : Real.exp (2 * L) * (3 * Real.exp (-(Q + 2 * L + 20))) = 3 * b := by
    rw [← mul_assoc, mul_comm (Real.exp (2 * L)) 3, mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [heq] at hp
  have hsum : 6 * δ ^ 2 + 4 * E + 2 * M ^ 2 * (2 * η + ε) ≤ 16 * b := by
    dsimp only [b] at hδ2 hp ⊢
    nlinarith
  have h20 : (16 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
  calc
    _ ≤ 16 * b := hsum
    _ ≤ Real.exp 20 * b := mul_le_mul_of_nonneg_right h20 hb
    _ = Real.exp (-Q) := by
      dsimp only [b]
      rw [← Real.exp_add]
      congr 1
      ring

theorem sourceSquareAccuracy_cost {M C V E W B D Q : ℝ}
    (hC0 : 0 ≤ C) (hV0 : 0 ≤ V) (hE0 : 0 ≤ E)
    (hM : M ≤ Real.exp W) (hC : C ≤ Real.exp B) (hV : V ≤ Real.exp D)
    (hE : E ≤ Real.exp (-(2 * Q + W + B + D + 4))) :
    M * (C * (V * E)) ≤ (Real.exp (-Q) / 2) ^ 2 := by
  have hprod : M * (C * (V * E)) ≤ Real.exp (-(2 * Q + 4)) := by
    calc
      _ ≤ Real.exp W * (Real.exp B * (Real.exp D * Real.exp (-(2 * Q + W + B + D + 4)))) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hh := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (-(2 * Q + 4))).le
  have heq : Real.exp (-(2 * Q + 4)) * Real.exp 4 = Real.exp (-Q) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hh
  have hdiv : Real.exp (-(2 * Q + 4)) ≤ (Real.exp (-Q) / 2) ^ 2 := by
    nlinarith
  exact hprod.trans hdiv

end Erdos3

end

end OAI
