import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderBernoulliCoefficients

/-!
# A positive algebraic inverse of the negative second derivative

On the half interval use x = 1 - 2t and Y = 1 - x². The shape xY^j
has a zero-endpoint inverse under the negative second derivative
that is a nonnegative combination of xY^i. This gives coefficient
certificates for the sign argument without any analytic integration.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGreen

open Polynomial Finset

local notation "𝕏" => (Polynomial.X : Polynomial ℚ)

noncomputable def atom : Polynomial ℚ := 1-𝕏^2
noncomputable def lift (p : Polynomial ℚ) : Polynomial ℚ := 𝕏*p.comp atom
noncomputable def basis (j : ℕ) : Polynomial ℚ := 𝕏*atom^j
noncomputable def laplacian (p : Polynomial ℚ) : Polynomial ℚ := -p.derivative.derivative

def alpha (j : ℕ) : ℚ := 2*((j : ℚ)+1)*(2*j+3)
def beta (j : ℕ) : ℚ := 4*j*((j : ℚ)+1)

theorem alpha_positive (j : ℕ) : 0 < alpha j := by unfold alpha; positivity
theorem beta_nonnegative (j : ℕ) : 0 ≤ beta j := by unfold beta; positivity

private theorem derivative_atom : atom.derivative = -C (2 : ℚ)*𝕏 := by
  simp [atom,map_ofNat]
  ring

private theorem derivative_basis (j : ℕ) :
    (basis (j+1)).derivative = atom^(j+1)-C (2*((j : ℚ)+1))*𝕏^2*atom^j := by
  unfold basis
  rw [derivative_mul,derivative_X,derivative_pow_succ,derivative_atom]
  simp only [_root_.one_mul,C_add,C_mul,C_1,C_eq_natCast]
  ring

theorem basis_one_laplacian : laplacian (basis 1) = C (alpha 0)*basis 0 := by
  unfold laplacian
  rw [show (1 : ℕ) = 0+1 by rfl,derivative_basis]
  simp [alpha,basis,derivative_atom,map_ofNat]
  ring

theorem basis_succ_laplacian (j : ℕ) :
    laplacian (basis (j+2)) = C (alpha (j+1))*basis (j+1)-C (beta (j+1))*basis j := by
  unfold laplacian
  rw [show j+2=j+1+1 by omega,derivative_basis,derivative_sub,derivative_pow_succ,derivative_mul,derivative_pow_succ,
    derivative_atom,derivative_C_mul_X_pow,show (2 : ℕ)-1=1 by decide]
  simp only [Nat.cast_add,Nat.cast_one,pow_one, basis,alpha,beta]
  rw [pow_succ atom j]
  simp only [map_add,map_mul,map_ofNat,map_natCast,map_one]
  unfold atom
  ring

private theorem lift_pow (j : ℕ) : lift ((𝕏 : Polynomial ℚ)^j) = basis j := by
  simp [lift,basis,pow_comp]
private theorem lift_add (p q : Polynomial ℚ) : lift (p+q) = lift p+lift q := by
  simp [lift,_root_.mul_add]
private theorem lift_smul (a : ℚ) (p : Polynomial ℚ) : lift (a • p) = a • lift p := by
  simp [lift,smul_comp]
private theorem lap_add (p q : Polynomial ℚ) : laplacian (p+q) = laplacian p+laplacian q := by
  simp [laplacian]
  ring
private theorem lap_smul (a : ℚ) (p : Polynomial ℚ) : laplacian (a • p) = a • laplacian p := by
  simp [laplacian,smul_neg]

noncomputable def green : ℕ → Polynomial ℚ
  | 0 => (alpha 0)⁻¹ • 𝕏
  | j+1 => (alpha (j+1))⁻¹ • (𝕏^(j+2)+beta (j+1) • green j)

theorem green_nonnegative (j i : ℕ) : 0 ≤ (green j).coeff i := by
  induction j with
  | zero =>
      have ha := alpha_positive 0
      simp only [green,coeff_smul,smul_eq_mul,coeff_X]
      split_ifs <;> positivity
  | succ j ih =>
      simp only [green,coeff_smul,smul_eq_mul,coeff_add,coeff_X_pow]
      have ha := alpha_positive (j+1)
      have hb := beta_nonnegative (j+1)
      split_ifs <;> positivity

theorem green_constant (j : ℕ) : (green j).coeff 0 = 0 := by
  induction j with
  | zero => simp [green,coeff_X]
  | succ j ih => simp [green,ih,coeff_X_pow]

theorem green_inverse (j : ℕ) : laplacian (lift (green j)) = basis j := by
  induction j with
  | zero =>
      rw [green,lift_smul,show lift (𝕏 : Polynomial ℚ)=basis 1 by simp [lift,basis],lap_smul,basis_one_laplacian,
        smul_eq_C_mul,← _root_.mul_assoc,← C_mul,inv_mul_cancel₀ (ne_of_gt (alpha_positive 0)),C_1,_root_.one_mul]
  | succ j ih =>
      rw [green,lift_smul,lift_add,lift_smul,lift_pow,lap_smul,lap_add,lap_smul,basis_succ_laplacian,ih,
        smul_eq_C_mul (beta (j+1)),sub_add_cancel,smul_eq_C_mul,← _root_.mul_assoc,← C_mul,
        inv_mul_cancel₀ (ne_of_gt (alpha_positive (j+1))),C_1,_root_.one_mul]

private noncomputable def liftLinear : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ where
  toFun := lift
  map_add' := lift_add
  map_smul' := lift_smul

private noncomputable def lapLinear : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ where
  toFun := laplacian
  map_add' := lap_add
  map_smul' := lap_smul

noncomputable def solve (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (p.natDegree+1), p.coeff i • green i

theorem solve_nonnegative (p : Polynomial ℚ) (h : ∀ i, 0 ≤ p.coeff i) (i : ℕ) :
    0 ≤ (solve p).coeff i := by
  simp only [solve, finsetSum_coeff,coeff_smul,smul_eq_mul]
  exact sum_nonneg fun j _ => mul_nonneg (h j) (green_nonnegative j i)

theorem solve_constant (p : Polynomial ℚ) : (solve p).coeff 0 = 0 := by
  simp [solve,finsetSum_coeff,coeff_smul,green_constant]

theorem solve_inverse (p : Polynomial ℚ) : laplacian (lift (solve p)) = lift p := by
  have h := congrArg (liftLinear : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ) p.as_sum_range_C_mul_X_pow
  change lapLinear (liftLinear (solve p)) = liftLinear p
  simp only [solve,map_sum,map_smul]
  have step (i : ℕ) : lapLinear (liftLinear (green i)) = liftLinear (𝕏^i) := by
    change laplacian (lift (green i)) = lift (𝕏^i)
    rw [green_inverse,lift_pow]
  simp only [step]
  simpa only [map_sum,← smul_eq_C_mul,map_smul] using h.symm

theorem lift_at_zero (p : Polynomial ℚ) : (lift p).eval 0 = 0 := by
  simp [lift]

theorem lift_at_one (p : Polynomial ℚ) : (lift p).eval 1 = p.coeff 0 := by
  simp [lift,atom,eval_comp,coeff_zero_eq_eval_zero]

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGreen
