import OAI.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

def coefficientMajorantMassLog {A : Type*} [Semiring A] (P : A) : A :=
  P ^ 5 + P * (3 * P + 3)

theorem coefficientMajorantMassLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coefficientMajorantMassLog P := by
  unfold coefficientMajorantMassLog
  positivity

theorem coefficientMajorantMassFactor_exp_bound {m : ℕ} (O Q J : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] [∀ j, Fintype (J j)]
    (C : Fin m → ℝ≥0) (period N : ℕ) {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ P)
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) (hN : (N : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2)) :
    coefficientDeckPeriodCap O Q period *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^ N ≤
      Real.exp (coefficientMajorantMassLog P) := by
  let T := ∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)
  have hT : T ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ Real.exp P * Real.exp P := mul_le_mul (hC j)
            (by linarith [hJ j, Real.add_one_le_exp P]) (by positivity) (by positivity)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) :=
        mul_le_mul_of_nonneg_right (hm.trans (by linarith [Real.add_one_le_exp P])) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have htwice : 2 * T ≤ Real.exp (3 * P + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (3 * P) := mul_le_mul
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hT (by dsimp [T]; positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hbox : 2 * T + 1 ≤ Real.exp (3 * P + 3) := by
    have h := one_add_le_exp_succ (by positivity : 0 ≤ 3 * P + 2) htwice
    calc
      _ = 1 + 2 * T := add_comm _ _
      _ ≤ Real.exp (3 * P + 2 + 1) := h
      _ = _ := congrArg Real.exp (by ring)
  have hp := pow_le_exp_mul_of_le_exp (by dsimp [T]; positivity) hbox
    (by positivity : 0 ≤ 3 * P + 3) N hN
  have hd : coefficientDeckPeriodCap O Q period ≤ Real.exp (P ^ 5) :=
    (coefficientDeckPeriodCap_exp_bound O Q period hP (sq_nonneg P) hm hO hQ hperiod).trans_eq
      (congrArg Real.exp (by ring))
  calc
    _ ≤ Real.exp (P ^ 5) * Real.exp (P * (3 * P + 3)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; rfl

end Erdos3.VectorPolynomial

end

end OAI
