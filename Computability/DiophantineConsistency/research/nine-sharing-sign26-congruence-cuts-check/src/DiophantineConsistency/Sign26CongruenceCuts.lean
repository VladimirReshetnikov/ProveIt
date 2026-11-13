import DiophantineConsistency.Sign26ZeroExtraction
import DiophantineConsistency.SharingSign27Squares

/-! SOURCE-ONLY: gap and q3-conditional affected residual identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26CongruenceCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} (gap : S) (v : Fin 27 → S) : Fin 28 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, gap, v 22, v 23, v 24, v 25, v 26]

def ringGap (p : Fin 4 → ℤ) (v : Fin 27 → V) : DiffRing V :=
  let a := ((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)
  a * (a + 1) + (ι (v 3) + 1) - a * (ι (v 2) + 1)

def oldGap (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 22) - (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))))

theorem old_Gap_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 7).head? = some (oldGap p) := by rfl

theorem oldGap_zero (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V)
    (hgap : ι gap = ringGap p v) : InternalZero (oldGap p) (lift gap v) := by
  apply (internalZero_iff _ _).mpr
  simp [oldGap, lift, ringGap, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, hgap]

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (SharingSeed27Sextic.firstResidual p).evalRing (fun j => ι (lift gap v j)) =
      (SharingSeed26Sextic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed27Sextic.firstResidual, SharingSeed26Sextic.firstResidual,
    lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]

def oldTau (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 23) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (Expr.var 22)) - (((Expr.var 22) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newTau (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 22) - (((((Expr.var 17) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_Tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 8).head? = some (oldTau p) := by rfl

theorem new_Tau_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 7).head? = some (newTau p) := by rfl

theorem Tau_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V)
    (hgap : ι gap = ringGap p v)
    (hq3 : ι (v 15) = (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1)) :
    (oldTau p).evalRing (fun j => ι (lift gap v j)) =
      (newTau p).evalRing (fun j => ι (v j)) := by
  simp [oldTau, newTau, lift, ringGap, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, hgap, hq3] <;> ring

def oldInner (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 24) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (Expr.var 22)) - (((Expr.var 22) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

def newInner (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 23) - (((((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) - (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ)))))) - ((((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ)))) * (Expr.var 15)) + ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))))) + (((Expr.constant (p 2)) + ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))))

theorem old_Inner_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 11).head? = some (oldInner p) := by rfl

theorem new_Inner_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 10).head? = some (newInner p) := by rfl

theorem Inner_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V)
    (hgap : ι gap = ringGap p v)
    (hq3 : ι (v 15) = (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) *
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1)) :
    (oldInner p).evalRing (fun j => ι (lift gap v j)) =
      (newInner p).evalRing (fun j => ι (v j)) := by
  simp [oldInner, newInner, lift, ringGap, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, hgap, hq3] <;> ring
end DiophantineConsistency.Sign26CongruenceCuts
#print axioms DiophantineConsistency.Sign26CongruenceCuts.old_Gap_row
#print axioms DiophantineConsistency.Sign26CongruenceCuts.oldGap_zero
#print axioms DiophantineConsistency.Sign26CongruenceCuts.first_eval
#print axioms DiophantineConsistency.Sign26CongruenceCuts.old_Tau_row
#print axioms DiophantineConsistency.Sign26CongruenceCuts.new_Tau_row
#print axioms DiophantineConsistency.Sign26CongruenceCuts.Tau_eval
#print axioms DiophantineConsistency.Sign26CongruenceCuts.old_Inner_row
#print axioms DiophantineConsistency.Sign26CongruenceCuts.new_Inner_row
#print axioms DiophantineConsistency.Sign26CongruenceCuts.Inner_eval
