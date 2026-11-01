import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! Reverse signed-factor lemmas for literal adaptive construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
  ArithmeticAdaptiveStrongNorm2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A represented natural root and its exact squared right-hand side make a
literal `1+(root²-rhs)` factor a positive unit. -/
theorem square_factor_unit {σ : Type*} (z rhs : Expr σ) (v : σ → V) (a b : V)
    (hz : Equivalent (pairEval z v) (natural a))
    (hr : Equivalent (pairEval rhs v) (natural b)) (hn : a*a=b) :
    (pairEval (1+(z*z-rhs)) v).1=(pairEval (1+(z*z-rhs)) v).2+1 := by
  have hs := equivalent_multiply hz hz
  have hmul : multiply (natural a) (natural a)=natural b := by
    simp [multiply,natural,hn]
  rw [hmul] at hs
  have he := equivalent_trans hs (equivalent_symm hr)
  change (multiply (pairEval z v) (pairEval z v)).1+(pairEval rhs v).2 =
    (multiply (pairEval z v) (pairEval z v)).2+(pairEval rhs v).1 at he
  have he' := congrArg (fun x : V => 1+x) he
  change (pairEval (Expr.add (Expr.constant 1) (Expr.sub (Expr.mul z z) rhs)) v).1 =
    (pairEval (Expr.add (Expr.constant 1) (Expr.sub (Expr.mul z z) rhs)) v).2+1
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,multiply,add_assoc,add_comm,add_left_comm] using he'

/-- The literal strong factor is a positive unit whenever its additive strong
norm holds; no factor-unit hypothesis is used. -/
theorem strong_unit_of_norm (p : Fin 4 → ℕ) (v : Fin 13 → V) (hn : StrongNorm v) :
    (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).1 =
      (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v).2+1 := by
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let D : V := (3+4*a)+a*a
  let I : V := (c*c)*v 4
  have hr : Equivalent (pairEval (factors (fun j => (p j:ℤ))).2.2.2 v)
      (1+I*I+D,D*(v 3*v 3)) := strong_rep p v
  have hn' : I*I+D=D*(v 3*v 3) := hn
  have ht : Equivalent (1+I*I+D,D*(v 3*v 3)) (natural (1:V)) := by
    change (1+I*I+D)+0=D*(v 3*v 3)+1
    rw [←hn']
    ring
  exact equivalent_one.mp (equivalent_trans hr ht)
end DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011
