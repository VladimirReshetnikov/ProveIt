import DiophantineConsistency.NineFreshJones

/-! UNCOMPILED generated syntax only. External JSON binding is separately
checked; no all-model bridge or iPRA endpoint is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed28Sextic

/-- The first residual; all witness-zero values make it `-(p 0 + 1)^3`. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  ((Expr.var 15) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))

/-- The remaining 18 residuals, in the external candidate order. -/
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 29)) :=
  [
    ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15))),
    ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16))),
    ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16))),
    ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18))),
    ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))),
    ((Expr.var 21) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))),
    ((Expr.var 22) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))))),
    ((((Expr.var 21) * (Expr.var 21)) - (Expr.var 22)) - (Expr.constant (1 : ℤ))),
    ((Expr.var 23) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 24) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))),
    ((((Expr.var 24) * (Expr.var 24)) - ((Expr.var 19) * ((Expr.var 19) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ))),
    ((((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) - (((((Expr.constant (p 1)) + ((Expr.var 9) + (Expr.constant (1 : ℤ)))) * (((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))) + ((Expr.var 2) + (Expr.constant (1 : ℤ)))) + (((Expr.var 4) + (Expr.constant (1 : ℤ))) * ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ))),
    ((Expr.var 25) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 23)) - (((Expr.var 23) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))))),
    ((Expr.var 26) - (((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 25)) - ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))),
    ((Expr.var 27) - (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (Expr.var 22))),
    ((Expr.var 28) - ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 26) * (Expr.var 26)))),
    (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - (((Expr.var 27) * (Expr.var 27)) * (Expr.var 28))) - (Expr.constant (1 : ℤ))),
    ((((Expr.var 20) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - ((Expr.var 27) * (Expr.var 27))) - (Expr.var 20))
  ]

/-- Sum of the 19 squared residuals; coordinate 0 is unused. -/
def seed (p : Fin 4 → ℤ) : Expr (Fin 29) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)

/-- Keep the distinguished input arbitrary and set all 28 witnesses to zero. -/
def zeroWitness (x : ℤ) (j : Fin 29) : ℤ := if j = 0 then x else 0

end DiophantineConsistency.SharingSeed28Sextic
