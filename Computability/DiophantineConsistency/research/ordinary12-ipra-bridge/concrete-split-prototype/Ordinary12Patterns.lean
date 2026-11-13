import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12Patterns
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def firstPattern (qm z n : Expr (Fin 12)) : Expr (Fin 12) :=
  let q := 1 + qm
  let m := q * (q*q) * qm
  1+(z*z-m*m*n)

def mainPattern (u a c d : Expr (Fin 12)) : Expr (Fin 12) :=
  1+(d*d-u*u*(1+(3+4*a+a*a)*(c*c)))

def ordinaryPattern (an x y d q : Expr (Fin 12)) : Expr (Fin 12) :=
  1+(an*an-(q*d)*(((2*x)*y)*((2*x)*y)))

private theorem ordinary_mod : ∀ a b d q : ZMod 4,
    1+a*a-(q*d)*((2*b)*(2*b)) ≠ -1 := by decide

theorem first_ne (qm z n : Expr (Fin 12)) (v : Fin 12 → V) :
    (pairEval (firstPattern qm z n) v).1 + 1 ≠ (pairEval (firstPattern qm z n) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let qv := 1 + syntaxEval (fun i => residue (v i)) qm
  let zv := syntaxEval (fun i => residue (v i)) z
  let nv := syntaxEval (fun i => residue (v i)) n
  have he : syntaxEval (fun i => residue (v i)) (firstPattern qm z n) =
      1+zv^2-(qv^3*(qv-1))^2*nv := by
    simp only [firstPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one]
    dsimp only [qv,zv,nv]
    ring
  rw [he] at hn
  exact first_bad qv zv nv hn

theorem main_ne (u a c d : Expr (Fin 12)) (v : Fin 12 → V) :
    (pairEval (mainPattern u a c d) v).1 + 1 ≠ (pairEval (mainPattern u a c d) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let uv := syntaxEval (fun i => residue (v i)) u
  let av := syntaxEval (fun i => residue (v i)) a
  let cv := syntaxEval (fun i => residue (v i)) c
  let dv := syntaxEval (fun i => residue (v i)) d
  have he : syntaxEval (fun i => residue (v i)) (mainPattern u a c d) =
      1+dv^2-uv^2*(1+(av^2+4*av+3)*cv^2) := by
    simp only [mainPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one, Nat.cast_ofNat]
    dsimp only [uv,av,cv,dv]
    ring
  rw [he] at hn
  exact main_bad uv av cv dv hn

theorem ordinary_ne (an x y d q : Expr (Fin 12)) (v : Fin 12 → V) :
    (pairEval (ordinaryPattern an x y d q) v).1 + 1 ≠ (pairEval (ordinaryPattern an x y d q) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  apply ordinary_mod (syntaxEval (fun i => residue (v i)) an)
    (syntaxEval (fun i => residue (v i)) x * syntaxEval (fun i => residue (v i)) y) (syntaxEval (fun i => residue (v i)) d)
    (syntaxEval (fun i => residue (v i)) q)
  simp only [ordinaryPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one, Nat.cast_ofNat] at hn
  convert hn using 1
  all_goals ring
end DiophantineConsistency.Ordinary12Patterns
#print axioms DiophantineConsistency.Ordinary12Patterns.first_ne
#print axioms DiophantineConsistency.Ordinary12Patterns.main_ne
#print axioms DiophantineConsistency.Ordinary12Patterns.ordinary_ne
