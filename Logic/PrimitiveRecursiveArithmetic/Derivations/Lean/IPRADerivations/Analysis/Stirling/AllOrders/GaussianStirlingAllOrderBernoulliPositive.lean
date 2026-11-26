import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderBernoulliGreen

/-!
# A positive polynomial representation for centered Bernoulli functions

The signed odd polynomials determine the derivative of each centered
even polynomial. In the coordinate x = 1 - 2t they have the form
x times a polynomial with nonnegative coefficients in 1 - x².
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliPositive

open Polynomial Finset
open GaussianStirlingAllOrderBernoulliCoefficients
  (normalized normalized_derivative coefficient reflection odd_constant_zero)
open GaussianStirlingAllOrderBernoulliGreen
  (atom lift laplacian solve solve_constant solve_inverse solve_nonnegative lift_at_zero lift_at_one)

local notation "𝕏" => (Polynomial.X : Polynomial ℚ)

noncomputable def halfCoordinate : Polynomial ℚ := C (1/2:ℚ)*(1-𝕏)

noncomputable def oddProfile (m : ℕ) : Polynomial ℚ :=
  C ((-1:ℚ)^(m+1)) * (normalized (2*m+1)).comp halfCoordinate

private theorem half_derivative : halfCoordinate.derivative = C (-(1/2):ℚ) := by
  simp [halfCoordinate]

private theorem derivative_half_comp (j : ℕ) :
    ((normalized (j+1)).comp halfCoordinate).derivative =
      C (-(1/2):ℚ)*(normalized j).comp halfCoordinate := by
  rw [derivative_comp,half_derivative,normalized_derivative]

private theorem lap_profile (m : ℕ) :
    laplacian (oddProfile (m+1)) = (1/4:ℚ) • oddProfile m := by
  unfold laplacian oddProfile
  rw [show 2*(m+1)+1=(2*m+1)+1+1 by omega]
  simp only [derivative_C_mul,derivative_half_comp,smul_eq_C_mul]
  rw [pow_succ (-1 : ℚ) (m+1)]
  simp only [map_mul,map_neg,map_one]
  have scalar : C (1/2 : ℚ)*C (1/2 : ℚ) = C (1/4 : ℚ) := by
    rw [← C_mul]
    congr 1
    norm_num
  calc
    -(C ((-1 : ℚ)^(m+1)) * (-1) *
        (-C (1/2 : ℚ) * (-C (1/2 : ℚ) * (normalized (2*m+1)).comp halfCoordinate))) =
        C ((-1 : ℚ)^(m+1)) * (C (1/2 : ℚ)*C (1/2 : ℚ)) *
          (normalized (2*m+1)).comp halfCoordinate := by ring
    _ = _ := by rw [scalar]; ring

private theorem profile_zero (m : ℕ) : (oddProfile m).eval 0 = 0 := by
  let j := 2*m+1
  have hj : Odd j := ⟨m, rfl⟩
  have e := reflection j (1/2:ℚ)
  have eq : (1:ℚ)-1/2=1/2 := by norm_num
  rw [eq,hj.neg_one_pow] at e
  have z : (normalized j).eval (1/2:ℚ)=0 := by linarith
  have z' : (normalized j).eval (2:ℚ)⁻¹=0 := by simpa [one_div] using z
  simp [oddProfile,halfCoordinate,eval_comp,show (2*m+1)=j from rfl,z']

private theorem profile_one (m : ℕ) : (oddProfile (m+1)).eval 1 = 0 := by
  let j := 2*(m+1)+1
  have hj : Odd j := ⟨m+1, rfl⟩
  have h0 := odd_constant_zero hj (by dsimp [j]; omega)
  have z : (normalized j).eval 0=0 := by
    rw [← coeff_zero_eq_eval_zero,coefficient,h0]
  simp [oddProfile,halfCoordinate,eval_comp,show (2*(m+1)+1)=j from rfl,z]

private theorem lap_unique (p q : Polynomial ℚ) (h : laplacian p = laplacian q)
    (h₀ : p.eval 0 = q.eval 0) (h₁ : p.eval 1 = q.eval 1) : p=q := by
  let r := p-q
  have he : r.derivative.derivative=0 := by simpa [r,laplacian,sub_eq_zero] using h
  let a := r.derivative.coeff 0
  have ha : r.derivative=C a := eq_C_of_derivative_eq_zero he
  let tail := r-C a*𝕏
  have ht : tail.derivative=0 := by simp [tail,ha]
  let b := tail.coeff 0
  have hb : tail=C b := eq_C_of_derivative_eq_zero ht
  have hr : r=C a*𝕏+C b := by
    rw [show r=tail+C a*𝕏 by unfold tail; ring,hb]
    ring
  have ev₀ : r.eval 0=0 := by simp [r,h₀]
  have ev₁ : r.eval 1=0 := by simp [r,h₁]
  rw [hr] at ev₀ ev₁
  simp at ev₀ ev₁
  have hA : a=0 := by linarith
  have hR : r=0 := by simp [hr,hA,ev₀]
  exact sub_eq_zero.mp hR

noncomputable def coefficients : ℕ → Polynomial ℚ
  | 0 => C (1/2:ℚ)
  | m+1 => (1/4:ℚ) • solve (coefficients m)

theorem coefficients_nonnegative (m i : ℕ) : 0 ≤ (coefficients m).coeff i := by
  induction m generalizing i with
  | zero =>
      simp only [coefficients,coeff_C]
      split_ifs <;> norm_num
  | succ m hm =>
      simp only [coefficients,coeff_smul,smul_eq_mul]
      exact mul_nonneg (by norm_num) (solve_nonnegative _ hm i)

theorem odd_profile_value (m : ℕ) : oddProfile m = lift (coefficients m) := by
  induction m with
  | zero =>
      norm_num [oddProfile,coefficients,normalized,Polynomial.bernoulli_one,halfCoordinate,lift,sub_comp]
      ring
  | succ m ih =>
      apply lap_unique
      · rw [lap_profile,ih,coefficients]
        simp only [lift,laplacian,smul_comp,mul_smul_comm,derivative_smul]
        have e := solve_inverse (coefficients m)
        simpa only [laplacian,lift,smul_neg] using congrArg ((1/4:ℚ) • ·) e.symm
      · rw [profile_zero,lift_at_zero]
      · rw [profile_one,lift_at_one,coefficients,coeff_smul,solve_constant,smul_zero]

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliPositive
