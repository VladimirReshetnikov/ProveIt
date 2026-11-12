import P74PositiveGuard
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Literal 74 restricted-factor modulo-four exclusions, proposed source
only. No graph zero, positivity or provider property is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.FactorResidues74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Pattern
variable {σ : Type*}
def mainPattern (u a c d : Expr σ) : Expr σ :=
  1+(d*d-u*u*(1+((3+4*a)+a*a)*(c*c)))
def auxPattern (y z a f : Expr σ) : Expr σ :=
  y*y-(((3+4*a)+a*a)*(f*f-1))*(y*y-z*z)
def strongPattern (i a f : Expr σ) : Expr σ :=
  1+(i*i-(((3+4*a)+a*a)*(f*f-1)))

/-- Generic modulo-four exclusions for the three exact factor patterns. -/
theorem main_ne (u a c d : Expr σ) (v : σ → V) :
    pairResidue (pairEval (mainPattern u a c d) v) ≠ -1 := by
  rw [pairEval_residue]
  let uv := syntaxEval (fun j => residue (v j)) u
  let av := syntaxEval (fun j => residue (v j)) a
  let cv := syntaxEval (fun j => residue (v j)) c
  let dv := syntaxEval (fun j => residue (v j)) d
  have he : syntaxEval (fun j => residue (v j)) (mainPattern u a c d)=
      1+dv^2-uv^2*(1+(av^2+4*av+3)*cv^2) := by
    simp only [mainPattern,syntax_add,syntax_sub,syntax_mul,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
    dsimp only [uv,av,cv,dv]
    ring
  rw [he]
  exact main_bad uv av cv dv

theorem aux_ne (y z a f : Expr σ) (v : σ → V) :
    pairResidue (pairEval (auxPattern y z a f) v) ≠ -1 := by
  rw [pairEval_residue]
  let yv := syntaxEval (fun j => residue (v j)) y
  let zv := syntaxEval (fun j => residue (v j)) z
  let av := syntaxEval (fun j => residue (v j)) a
  let fv := syntaxEval (fun j => residue (v j)) f
  have he : syntaxEval (fun j => residue (v j)) (auxPattern y z a f)=
      (av^2+4*av+3)*(fv^2-1)*zv^2+
        (1-(av^2+4*av+3)*(fv^2-1))*yv^2 := by
    simp only [auxPattern,syntax_add,syntax_sub,syntax_mul,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
    dsimp only [yv,zv,av,fv]
    ring
  rw [he]
  exact aux_bad av fv zv yv

theorem strong_ne (i a f : Expr σ) (v : σ → V) :
    pairResidue (pairEval (strongPattern i a f) v) ≠ -1 := by
  rw [pairEval_residue]
  let iv := syntaxEval (fun j => residue (v j)) i
  let av := syntaxEval (fun j => residue (v j)) a
  let fv := syntaxEval (fun j => residue (v j)) f
  have he : syntaxEval (fun j => residue (v j)) (strongPattern i a f)=
      1+iv^2-(av^2+4*av+3)*(fv^2-1) := by
    simp only [strongPattern,syntax_add,syntax_sub,syntax_mul,syntax_ofNat,Nat.cast_one,Nat.cast_ofNat]
    dsimp only [iv,av,fv]
    ring
  rw [he]
  exact strong_bad av fv iv
end Pattern

/-- These are literal factor identities, not evaluation approximations. -/
theorem main_shape (p : Fin 4 → ℤ) : (P74PositiveGuard.graph p).main =
    mainPattern (P74PositiveGuard.graph p).U (P74PositiveGuard.graph p).a
      (P74PositiveGuard.graph p).c (P74PositiveGuard.graph p).Dstar := by rfl

theorem aux_shape (p : Fin 4 → ℤ) : (P74PositiveGuard.graph p).aux =
    auxPattern (.var 11) (P74PositiveGuard.graph p).vroot
      (P74PositiveGuard.graph p).a (.var 3) := by rfl

theorem strong_shape (p : Fin 4 → ℤ) : (P74PositiveGuard.graph p).strong =
    strongPattern (P74PositiveGuard.graph p).I (P74PositiveGuard.graph p).a (.var 3) := by rfl

theorem restricted_residues (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    pairResidue (pairEval (P74PositiveGuard.graph p).main v) ≠ -1 ∧
    pairResidue (pairEval (P74PositiveGuard.graph p).aux v) ≠ -1 ∧
    pairResidue (pairEval (P74PositiveGuard.graph p).strong v) ≠ -1 := by
  rw [main_shape,aux_shape,strong_shape]
  exact ⟨main_ne _ _ _ _ v,aux_ne _ _ _ _ v,strong_ne _ _ _ v⟩

end DiophantineConsistency.FactorResidues74Draft

#print axioms DiophantineConsistency.FactorResidues74Draft.restricted_residues
