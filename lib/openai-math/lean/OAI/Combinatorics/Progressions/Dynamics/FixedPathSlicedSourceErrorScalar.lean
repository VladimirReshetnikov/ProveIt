import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def fixedPathSlicedSourceError (rP rG C K Kφ ε η ξ : ℝ) : ℝ :=
  rP + (2 * ((2 * C + 2 * K) * rP + K * ε) + 2 * η) +
    (1 + 4 * C + 3 * Kφ) * rG + Kφ * ξ

theorem fixedPathSlicedSourceError_eq (rP rG C K Kφ ε η ξ : ℝ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ =
      (1 + 4 * C + 4 * K) * rP + (1 + 4 * C + 3 * Kφ) * rG +
        (2 * K) * ε + 2 * η + Kφ * ξ := by
  unfold fixedPathSlicedSourceError
  ring

theorem fixedPathSlicedSourceError_le_prefactor {P rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤
      Real.exp (P + 4) * (rP + rG + ε + η + ξ) := by
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp hP
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h
    linarith
  have hbudget : 9 * Real.exp P ≤ Real.exp (P + 4) := by
    rw [Real.exp_add]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnine (Real.exp_nonneg P)
  have hp : 1 + 4 * C + 4 * K ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 4 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hg : 1 + 4 * C + 3 * Kφ ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 3 * Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  have he : 2 * K ≤ Real.exp (P + 4) :=
    (show 2 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hh : (2 : ℝ) ≤ Real.exp (P + 4) :=
    (show (2 : ℝ) ≤ 9 * Real.exp P by linarith).trans hbudget
  have hx : Kφ ≤ Real.exp (P + 4) :=
    (show Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  rw [fixedPathSlicedSourceError_eq]
  calc
    _ ≤ Real.exp (P + 4) * rP + Real.exp (P + 4) * rG +
        Real.exp (P + 4) * ε + Real.exp (P + 4) * η + Real.exp (P + 4) * ξ :=
      add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hp hrP) (mul_le_mul_of_nonneg_right hg hrG))
        (mul_le_mul_of_nonneg_right he hε)) (mul_le_mul_of_nonneg_right hh hη))
        (mul_le_mul_of_nonneg_right hx hξ)
    _ = _ := by ring

theorem fixedPathSlicedSourceError_absorb_sharp {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 7)))
    (hrGs : rG ≤ Real.exp (-(P + E + 7)))
    (hεs : ε ≤ Real.exp (-(P + E + 7)))
    (hηs : η ≤ Real.exp (-(P + E + 7)))
    (hξs : ξ ≤ Real.exp (-(P + E + 7))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hpre := fixedPathSlicedSourceError_le_prefactor hP hC hK hφ hrP hrG hε hη hξ
  have hsum : rP + rG + ε + η + ξ ≤ 5 * Real.exp (-(P + E + 7)) := by linarith
  have hfive : (5 : ℝ) ≤ Real.exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    linarith
  calc
    _ ≤ Real.exp (P + 4) * (5 * Real.exp (-(P + E + 7))) :=
      hpre.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
    _ = 5 * Real.exp (-(E + 3)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 3 * Real.exp (-(E + 3)) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fixedPathSlicedSourceError_absorb {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (_hE : 0 ≤ E) (_hC0 : 0 ≤ C) (_hK0 : 0 ≤ K) (_hKφ0 : 0 ≤ Kφ)
    (hCP : C ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hKφP : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 12)))
    (hrGs : rG ≤ Real.exp (-(P + E + 12)))
    (hεs : ε ≤ Real.exp (-(P + E + 12)))
    (hηs : η ≤ Real.exp (-(P + E + 12)))
    (hξs : ξ ≤ Real.exp (-(P + E + 12))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hbudget : Real.exp (-(P + E + 12)) ≤ Real.exp (-(P + E + 7)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact fixedPathSlicedSourceError_absorb_sharp hP hCP hKP hKφP hrP hrG hε hη hξ
    (hrPs.trans hbudget) (hrGs.trans hbudget) (hεs.trans hbudget)
    (hηs.trans hbudget) (hξs.trans hbudget)

end Erdos3

end

end OAI
