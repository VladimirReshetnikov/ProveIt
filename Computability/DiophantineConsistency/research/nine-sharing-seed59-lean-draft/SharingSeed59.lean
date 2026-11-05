import DiophantineConsistency.NineFreshJones

/-! UNVERIFIED DRAFT. Generated from the externally audited 59-witness
sharing candidate. This file has not been compiled; model bridge and iPRA
endpoint are explicitly not provided. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed59

/-- The first residual; at zero witnesses its value is `-(p 0 + 1)^2`. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 60) :=
  ((Expr.var 15) - ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

/-- The remaining 45 quadratic residuals in graph order. -/
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 60)) :=
  [
    ((Expr.var 16) - ((Expr.var 15) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 17) - (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 18) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 16))),
    ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18))),
    ((Expr.var 20) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 18))),
    ((Expr.var 21) - ((Expr.var 19) * (Expr.var 20))),
    ((Expr.var 22) - (((Expr.var 19) + (Expr.var 18)) * ((Expr.var 19) + (Expr.var 18)))),
    ((Expr.var 23) - (((Expr.var 19) + (Expr.var 18)) * ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 24) - (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ))))),
    ((Expr.var 25) - (((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 26) - (((Expr.var 22) + (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ)))) * (Expr.var 25))),
    ((Expr.var 27) - ((((Expr.var 17) + (Expr.var 23)) + (Expr.var 24)) * (((Expr.var 17) + (Expr.var 23)) + (Expr.var 24)))),
    ((Expr.var 28) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 29) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 30) - ((((Expr.var 28) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + (Expr.var 29))),
    ((Expr.var 31) - (((Expr.var 28) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) + ((Expr.var 29) * (Expr.var 15)))),
    ((Expr.var 32) - (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 33) - ((Expr.var 19) * ((Expr.var 10) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 34) - (((((Expr.var 33) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 31)) * (((Expr.var 33) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 31))) + (((Expr.var 30) + (Expr.var 32)) * ((Expr.var 30) + (Expr.var 32))))),
    ((Expr.var 35) - (((((Expr.var 33) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 31)) * ((Expr.var 30) + (Expr.var 32))) + (((Expr.var 30) + (Expr.var 32)) * (((Expr.var 33) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 31))))),
    ((Expr.var 36) - ((Expr.var 21) * ((Expr.var 21) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))),
    ((Expr.var 37) - (((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 38) - (((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 39) - (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 40) - (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 41) - (((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 42) - ((Expr.var 40) * ((Expr.var 41) + (Expr.var 31)))),
    ((Expr.var 43) - ((Expr.var 40) * ((Expr.var 30) + (Expr.var 32)))),
    ((Expr.var 44) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 26))),
    ((Expr.var 45) - ((Expr.var 44) * (Expr.var 44))),
    ((Expr.var 46) - (((Expr.var 42) * (Expr.var 42)) + (((Expr.var 43) + ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))) * ((Expr.var 43) + ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))),
    ((Expr.var 47) - (((Expr.var 42) * ((Expr.var 43) + ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 43) + ((Expr.var 20) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))) * (Expr.var 42)))),
    ((Expr.var 48) - (((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ))))),
    ((Expr.var 49) - ((Expr.var 45) * (Expr.var 46))),
    ((Expr.var 50) - ((Expr.var 45) * ((Expr.var 47) + (Expr.var 48)))),
    ((Expr.var 51) - (((Expr.var 22) + (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ)))) * (Expr.var 40))),
    ((Expr.var 52) - (((Expr.var 34) * (Expr.var 27)) + (((Expr.var 35) + (Expr.var 36)) * (Expr.var 26)))),
    ((Expr.var 53) - (((Expr.var 34) * (Expr.var 26)) + (((Expr.var 35) + (Expr.var 36)) * (Expr.var 27)))),
    ((Expr.var 54) - (((Expr.var 52) * ((Expr.var 49) + (Expr.var 48))) + ((Expr.var 53) * (Expr.var 50)))),
    ((Expr.var 55) - (((Expr.var 52) * (Expr.var 50)) + ((Expr.var 53) * ((Expr.var 49) + (Expr.var 48))))),
    ((Expr.var 56) - (((Expr.var 54) * ((Expr.var 37) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + ((Expr.var 55) * (((Expr.var 38) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (Expr.var 39))))),
    ((Expr.var 57) - (((Expr.var 54) * (((Expr.var 38) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (Expr.var 39))) + ((Expr.var 55) * ((Expr.var 37) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))))),
    ((Expr.var 58) - (((Expr.var 56) * (Expr.var 51)) + ((Expr.var 57) * (Expr.var 45)))),
    ((Expr.var 59) - (((Expr.var 56) * (Expr.var 45)) + ((Expr.var 57) * (Expr.var 51)))),
    ((Expr.var 58) - ((Expr.var 59) + ((Expr.var 22) + (((Expr.constant (4 : ℤ)) * ((Expr.var 19) + (Expr.var 18))) + (Expr.constant (3 : ℤ))))))
  ]

/-- Sum of squared residuals; coordinate 0 is not used. -/
def seed (p : Fin 4 → ℤ) : Expr (Fin 60) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)

/-- Candidate syntax-degree calculation; not yet checked by Lean. -/
theorem seed_weightedDegree (p : Fin 4 → ℤ) :
    (seed p).weightedDegree (fun _ => 1) ≤ 4 := by
  simp [seed, firstResidual, remainingResiduals, QuarticSyntax.sumExpressions,
    Expr.weightedDegree]

/-- Candidate polynomial-degree bound; not yet checked by Lean. -/
theorem seed_degree (p : Fin 4 → ℤ) : (seed p).toPolynomial.totalDegree ≤ 4 := by
  have h := Expr.degree_evalRing_le (seed p) (fun _ => 1)
    (MvPolynomial.X : Fin 60 → MvPolynomial (Fin 60) ℤ) (by intro i; simp)
  rw [Expr.evalRing_X] at h
  exact h.trans (seed_weightedDegree p)

/-- Jones normalization valuation: the distinguished input is arbitrary. -/
def zeroWitness (x : ℤ) (j : Fin 60) : ℤ := if j = 0 then x else 0

/-- Candidate first-residual evaluation; not yet checked by Lean. -/
theorem firstResidual_zeroWitness (p : Fin 4 → ℤ) (x : ℤ) :
    (firstResidual p).eval (zeroWitness x) = -(p 0 + 1) ^ 2 := by
  simp [firstResidual, zeroWitness, Expr.eval]
  ring

/-- Candidate nonnegativity helper for every finite squared residual sum. -/
theorem eval_sumSquares_nonneg (es : List (Expr (Fin 60))) (v : Fin 60 → ℤ) :
    0 ≤ (QuarticSyntax.sumExpressions (es.map fun e => e * e)).eval v := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions, Expr.eval]
  | cons e es ih =>
    simp only [List.map_cons, QuarticSyntax.sumExpressions, Expr.eval_add, Expr.eval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

/-- Candidate all-input normalization, assuming the first port is positive. -/
theorem seed_normalized (p : Fin 4 → ℤ) (hp : 0 < p 0) (x : ℤ) :
    (seed p).eval (zeroWitness x) ≠ 0 := by
  have hne : (firstResidual p).eval (zeroWitness x) ≠ 0 := by
    rw [firstResidual_zeroWitness]
    nlinarith
  have hs : 0 < (firstResidual p).eval (zeroWitness x) *
      (firstResidual p).eval (zeroWitness x) := mul_self_pos.mpr hne
  have ht := eval_sumSquares_nonneg (remainingResiduals p) (zeroWitness x)
  have hpos : 0 < (seed p).eval (zeroWitness x) := by
    simpa only [seed, Expr.eval_add, Expr.eval_mul] using add_pos_of_pos_of_nonneg hs ht
  exact ne_of_gt hpos

-- Unresolved: prove the all-IΣ₁-model zero bridge, then instantiate
-- NineFreshJones.nine_iff and transfer the current iPRA endpoint.
end DiophantineConsistency.SharingSeed59
