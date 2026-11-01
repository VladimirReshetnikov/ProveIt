import DiophantineConsistency.QuarticCompilerCore

/-! # Literal syntax of the quartic gate compiler -/
namespace DiophantineConsistency.QuarticSyntax
open QuarticCompiler
def sumExpressions {σ : Type*} : List (Expr σ) → Expr σ
  | [] => .constant 0
  | e :: es => e + sumExpressions es

private def sumIndex {A B : Type*} {a b : ℕ} (f : A ≃ Fin a) (g : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) := (Equiv.sumCongr f g).trans finSumFinEquiv

/-- Explicit indexing of residuals, avoiding a choice of list order. -/
def equationIndex {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Equation p q ≃ Fin (1 + (Gates.count p + (Gates.count q + 1))) :=
  sumIndex (Equiv.refl (Fin 1))
    (sumIndex (Gates.index p) (sumIndex (Gates.index q) (Equiv.refl (Fin 1))))

/-- The same sum of squared residuals as `QuarticCompiler.quartic`, as syntax. -/
def expression {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    Expr (Fin (witnessCount p q + 1)) :=
  (sumExpressions (List.ofFn fun i =>
    let e := residualSyntax p q ((equationIndex p q).symm i)
    e * e)).rename (coordinate p q)


end DiophantineConsistency.QuarticSyntax
