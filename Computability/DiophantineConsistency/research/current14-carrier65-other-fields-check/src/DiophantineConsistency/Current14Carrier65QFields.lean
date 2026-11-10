import DiophantineConsistency.Current14Carrier65QInputs
import DiophantineConsistency.Carrier65

/-! Candidate binding of the standalone Q input bounds to Carrier65 fields. -/
namespace DiophantineConsistency.Current14Carrier65QInputs

theorem X_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (X p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).X := by
  simp only [X, q, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one, Carrier65.core]

theorem c_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (c p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).c := by
  simp only [c, k, Y, q, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one,
    Carrier65.core]

theorem a_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (a p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).a := by
  simp only [a, E, X, Y, q, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one,
    Carrier65.core]

theorem H_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (H p).evalRing v = (Carrier65.core (fun j => (p j : R)) v).H := by
  simp only [H, a, E, X, Y, q, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_one,
    Nat.cast_ofNat, Carrier65.core]

theorem polynomial_bound (e : Expr (Fin 14)) :
    (e.evalRing (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)).totalDegree ≤
      e.weightedDegree weight := by
  apply Expr.degree_evalRing_le
  intro j
  simp only [weight, MvPolynomial.totalDegree_X, le_refl]

theorem core_X_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).X).totalDegree ≤ 2 := by
  have h := polynomial_bound (X p)
  rw [X_weight, X_eval] at h
  exact h

theorem core_c_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).c).totalDegree ≤ 5 := by
  have h := polynomial_bound (c p)
  rw [c_weight, c_eval] at h
  exact h

theorem core_a_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).a).totalDegree ≤ 6 := by
  have h := polynomial_bound (a p)
  rw [a_weight, a_eval] at h
  exact h

theorem core_H_degree (p : Fin 4 → ℤ) :
    ((Carrier65.core (fun j => (p j : MvPolynomial (Fin 14) ℤ)) MvPolynomial.X).H).totalDegree ≤ 6 := by
  have h := polynomial_bound (H p)
  rw [H_weight, H_eval] at h
  exact h

end DiophantineConsistency.Current14Carrier65QInputs

#print axioms DiophantineConsistency.Current14Carrier65QInputs.core_X_degree
#print axioms DiophantineConsistency.Current14Carrier65QInputs.core_c_degree
#print axioms DiophantineConsistency.Current14Carrier65QInputs.core_a_degree
#print axioms DiophantineConsistency.Current14Carrier65QInputs.core_H_degree
