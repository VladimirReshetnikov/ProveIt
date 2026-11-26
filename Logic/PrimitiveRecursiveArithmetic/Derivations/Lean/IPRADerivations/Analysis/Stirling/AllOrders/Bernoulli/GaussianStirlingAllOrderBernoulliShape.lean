import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliPositive

/-!
# Positive coefficients for the centered even Bernoulli profile

The antiderivative of the positive odd profile expresses the
centered even polynomial as a polynomial in 4t(1-t). The coefficients
are nonnegative, and at least one coefficient above degree zero is positive.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliShape

open Polynomial Finset
open GaussianStirlingAllOrderBernoulliCoefficients (normalized normalized_derivative)
open GaussianStirlingAllOrderBernoulliGreen (atom lift green alpha beta alpha_positive green_nonnegative solve)
open GaussianStirlingAllOrderBernoulliPositive (halfCoordinate oddProfile coefficients coefficients_nonnegative odd_profile_value)

local notation "𝕏" => (Polynomial.X : Polynomial ℚ)

noncomputable def primitive (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (p.natDegree+1), C (p.coeff i/((i : ℚ)+1))*𝕏^(i+1)

theorem primitive_constant (p : Polynomial ℚ) : (primitive p).coeff 0 = 0 := by
  simp [primitive,finsetSum_coeff]

theorem primitive_nonnegative (p : Polynomial ℚ) (h : ∀ i, 0 ≤ p.coeff i) (i : ℕ) :
    0 ≤ (primitive p).coeff i := by
  simp only [primitive,finsetSum_coeff,coeff_C_mul_X_pow]
  refine sum_nonneg fun j _ => ?_
  split_ifs
  · exact div_nonneg (h j) (by positivity)
  · norm_num

theorem primitive_derivative (p : Polynomial ℚ) : (primitive p).derivative = p := by
  simp only [primitive,derivative_sum]
  trans ∑ i ∈ range (p.natDegree+1), C (p.coeff i)*𝕏^i
  · refine sum_congr rfl fun j _ => ?_
    rw [derivative_C_mul_X_pow,Nat.add_sub_cancel]
    have h : p.coeff j / ((j : ℚ)+1)*((j+1 : ℕ):ℚ) = p.coeff j := by
      push_cast
      field_simp
    rw [h]
  · exact p.as_sum_range_C_mul_X_pow.symm

theorem green_linear_positive (j : ℕ) : 0 < (green j).coeff 1 := by
  induction j with
  | zero =>
      have h := alpha_positive 0
      simpa [green,coeff_smul,coeff_X,smul_eq_mul] using inv_pos.mpr h
  | succ j ih =>
      simp only [green,coeff_smul,smul_eq_mul,coeff_add,coeff_X_pow]
      have ha := alpha_positive (j+1)
      have hb : 0 < beta (j+1) := by unfold beta; positivity
      split_ifs with h1
      · omega
      · positivity

private theorem solve_linear_positive (p : Polynomial ℚ) (h : ∀ i, 0 ≤ p.coeff i)
    (hp : ∃ i, 0 < p.coeff i) : 0 < (solve p).coeff 1 := by
  obtain ⟨i,hi⟩ := hp
  have hd : i ≤ p.natDegree := by
    by_contra! h'
    rw [coeff_eq_zero_of_natDegree_lt h'] at hi
    linarith only [hi]
  simp only [solve,finsetSum_coeff,coeff_smul,smul_eq_mul]
  have pos := mul_pos hi (green_linear_positive i)
  apply pos.trans_le
  exact single_le_sum (fun j _ => mul_nonneg (h j) (green_nonnegative j 1)) (mem_range.mpr (Nat.lt_succ_iff.mpr hd))

theorem coefficients_have_positive (m : ℕ) : ∃ i, 0 < (coefficients m).coeff i := by
  induction m with
  | zero => exact ⟨0, by norm_num [coefficients,coeff_C]⟩
  | succ m ih =>
      refine ⟨1,?_⟩
      simp only [coefficients,coeff_smul,smul_eq_mul]
      exact mul_pos (by norm_num) (solve_linear_positive _ (coefficients_nonnegative m) ih)

noncomputable def centeredShape (m : ℕ) : Polynomial ℚ :=
  ((Nat.factorial (2*m+2) : ℚ)/4) • primitive (coefficients m)

noncomputable def centeredProfile (m : ℕ) : Polynomial ℚ :=
  C ((-1 : ℚ)^(m+1)*(Nat.factorial (2*m+2) : ℚ)) *
    ((normalized (2*m+2)).comp halfCoordinate-C ((normalized (2*m+2)).eval 0))

theorem centered_shape_constant (m : ℕ) : (centeredShape m).coeff 0 = 0 := by
  simp [centeredShape,coeff_smul,primitive_constant]

theorem centered_shape_nonnegative (m i : ℕ) : 0 ≤ (centeredShape m).coeff i := by
  simp only [centeredShape,coeff_smul,smul_eq_mul]
  exact mul_nonneg (by positivity) (primitive_nonnegative _ (coefficients_nonnegative m) i)

theorem centered_shape_has_positive (m : ℕ) : ∃ i, i ≠ 0 ∧ 0 < (centeredShape m).coeff i := by
  obtain ⟨j,hj⟩ := coefficients_have_positive m
  refine ⟨j+1, by omega,?_⟩
  simp only [centeredShape,coeff_smul,smul_eq_mul,primitive,finsetSum_coeff,coeff_C_mul_X_pow]
  apply mul_pos (by positivity)
  rw [sum_eq_single j]
  · simp [hj]
    positivity
  · intro i _ hi
    simp [hi,Ne.symm hi]
  · intro hj'
    have h := not_lt.mp (fun h' => hj' (mem_range.mpr h'))
    have e : (coefficients m).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [e] at hj
    linarith only [hj]

theorem centered_profile (m : ℕ) : centeredProfile m = (centeredShape m).comp atom := by
  have h1 : halfCoordinate.derivative = C (-(1/2):ℚ) := by simp [halfCoordinate]
  have h2 : atom.derivative = C (-2:ℚ)*𝕏 := by
    simp [atom,map_ofNat,map_neg]
    ring
  let f : Polynomial ℚ := centeredProfile m
  let g : Polynomial ℚ := (centeredShape m).comp atom
  let F : ℚ := Nat.factorial (2*m+2)
  have hF : f.derivative = C (-(F/2))*oddProfile m := by
    unfold f centeredProfile oddProfile F
    simp only [derivative_C_mul,derivative_sub,derivative_C,sub_zero,derivative_comp,h1,
      show 2*m+2=(2*m+1)+1 by omega,normalized_derivative]
    simp only [map_mul,map_neg,div_eq_mul_inv,C_1]
    ring
  have hG : g.derivative = C (-(F/2))*lift (coefficients m) := by
    unfold g centeredShape lift
    simp only [derivative_comp,derivative_C_mul,primitive_derivative,h2,smul_eq_C_mul,mul_comp,C_comp]
    have scale : C (-2:ℚ)*C (F/4) = C (-(F/2)) := by
      rw [← map_mul]
      congr 1
      ring
    calc
      _ = (C (-2:ℚ)*C (F/4))*𝕏*(coefficients m).comp atom := by dsimp only [F]; ring
      _ = _ := by rw [scale]; ring
  have h : (f-g).derivative = 0 := by rw [derivative_sub,hF,hG,odd_profile_value,sub_self]
  have e := eq_C_of_derivative_eq_zero h
  have hf : f.eval 1 = 0 := by simp [f,centeredProfile,halfCoordinate,eval_comp]
  have hg : g.eval 1 = 0 := by simp [g,atom,eval_comp,← coeff_zero_eq_eval_zero,centered_shape_constant]
  have h0 : (f-g).coeff 0=0 := by
    have ee := congrArg (Polynomial.eval 1) e
    simpa [hf,hg] using ee.symm
  exact sub_eq_zero.mp (by simpa [h0] using e)

theorem centered_at_rational (m : ℕ) (t : ℚ) :
    (-1 : ℚ)^(m+1)*(Nat.factorial (2*m+2) : ℚ)*
      ((normalized (2*m+2)).eval t-(normalized (2*m+2)).eval 0) =
        (centeredShape m).eval (4*t*(1-t)) := by
  have e := congrArg (Polynomial.eval (1-2*t)) (centered_profile m)
  have h : halfCoordinate.eval (1-2*t) = t := by simp [halfCoordinate]; try ring
  have a : atom.eval (1-2*t) = 4*t*(1-t) := by simp [atom]; try ring
  simpa only [centeredProfile,eval_mul,eval_C,eval_sub,eval_comp,h,a] using e

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliShape
