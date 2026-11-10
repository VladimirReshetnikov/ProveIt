import DiophantineConsistency.Current14Carrier65QFields
import DiophantineConsistency.Current14Carrier65OtherWeights

/-! Candidate binding and degree bounds for the non-Q Carrier65 factors. -/
namespace DiophantineConsistency.Current14Carrier65OtherFields
open Current14Carrier65QInputs Current14Carrier65OtherWeights

theorem b_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (b p).evalRing v = (p 0 : R) * v 0 := by
  simp only [b, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var]

theorem q_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (q p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).q := by
  simp only [q, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one, Carrier65.core]

theorem Y_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (Y p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).Y := by
  simp only [Y, Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var, q_eval] <;> rfl

theorem E_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (E p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).E := by
  simp only [E, Expr.evalRing_mul, X_eval, Y_eval] <;> rfl

theorem k_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    k.evalRing v = (Carrier65.core (fun j => (p j : R)) v).k := by
  simp only [k, Expr.evalRing_add, Expr.evalRing_var, Carrier65.core]

theorem C_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (C p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).C := by
  simp only [C, Expr.evalRing_sub, Expr.evalRing_var, q_eval] <;> rfl

theorem delta_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (delta p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).delta := by
  simp only [delta, Expr.evalRing_add, Expr.evalRing_pow, a_eval, H_eval] <;> rfl

theorem ell_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (ell p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).ell := by
  simp only [ell, k, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var,
    E_eval, Y_eval] <;> rfl

theorem rank_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (rank p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).rank := by
  simp only [rank, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_pow, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Nat.cast_one, b_eval, q_eval] <;> rfl

theorem tau_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (tau p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).tau := by
  simp only [tau, k, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, E_eval, rank_eval] <;> rfl

theorem V_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (V p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).V := by
  simp only [V, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, c_eval, rank_eval] <;> rfl

theorem S_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (S p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).S := by
  simp only [S, Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var, delta_eval, c_eval] <;> rfl

theorem P_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).P := by
  simp only [P, k, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_pow, Expr.evalRing_var, tau_eval, ell_eval] <;> rfl

theorem U_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (U p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).U := by
  simp only [U, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_pow, Expr.evalRing_var, S_eval, V_eval] <;> rfl

theorem W_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (W p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).W := by
  simp only [W, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, C_eval, q_eval, b_eval] <;> rfl

theorem Z_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (Z p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).Z := by
  simp only [Z, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, delta_eval, S_eval] <;> rfl

theorem core_delta_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).delta).totalDegree ≤ 12 := by
  have h := polynomial_bound (delta p)
  rw [delta_weight, delta_eval] at h
  exact h

theorem core_P_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).P).totalDegree ≤ 22 := by
  have h := polynomial_bound (P p)
  rw [P_weight, P_eval] at h
  exact h

theorem core_U_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).U).totalDegree ≤ 62 := by
  have h := polynomial_bound (U p)
  rw [U_weight, U_eval] at h
  exact h

theorem core_W_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).W).totalDegree ≤ 2 := by
  have h := polynomial_bound (W p)
  rw [W_weight, W_eval] at h
  exact h

theorem core_Z_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).Z).totalDegree ≤ 46 := by
  have h := polynomial_bound (Z p)
  rw [Z_weight, Z_eval] at h
  exact h

end DiophantineConsistency.Current14Carrier65OtherFields

#print axioms DiophantineConsistency.Current14Carrier65OtherFields.core_delta_degree
#print axioms DiophantineConsistency.Current14Carrier65OtherFields.core_P_degree
#print axioms DiophantineConsistency.Current14Carrier65OtherFields.core_U_degree
#print axioms DiophantineConsistency.Current14Carrier65OtherFields.core_W_degree
#print axioms DiophantineConsistency.Current14Carrier65OtherFields.core_Z_degree
