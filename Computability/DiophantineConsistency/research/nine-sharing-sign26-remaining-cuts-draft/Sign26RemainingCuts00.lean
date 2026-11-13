import DiophantineConsistency.Sign26CongruenceCuts

/-! SOURCE-ONLY: unaffected residual reindexing under the gap lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26RemainingCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldR01 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

def newR01 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 16) - (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (Expr.var 15)))

theorem old_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 0).head? = some (oldR01 p) := by rfl

theorem new_R01_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 0).head? = some (newR01 p) := by rfl

theorem R01_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR01 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR01 p).evalRing (fun j => ι (v j)) := by
  simp [oldR01, newR01, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR02 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newR02 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 17) - ((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 1).head? = some (oldR02 p) := by rfl

theorem new_R02_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 1).head? = some (newR02 p) := by rfl

theorem R02_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR02 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR02 p).evalRing (fun j => ι (v j)) := by
  simp [oldR02, newR02, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR03 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

def newR03 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 18) - ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (Expr.var 16)))

theorem old_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 2).head? = some (oldR03 p) := by rfl

theorem new_R03_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 2).head? = some (newR03 p) := by rfl

theorem R03_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR03 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR03 p).evalRing (fun j => ι (v j)) := by
  simp [oldR03, newR03, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR04 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

def newR04 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 19) - ((Expr.var 17) * (Expr.var 18)))

theorem old_R04_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 3).head? = some (oldR04 p) := by rfl

theorem new_R04_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 3).head? = some (newR04 p) := by rfl

theorem R04_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR04 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR04 p).evalRing (fun j => ι (v j)) := by
  simp [oldR04, newR04, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR05 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

def newR05 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  ((Expr.var 20) - ((((Expr.var 17) + (Expr.var 16)) * ((Expr.var 17) + (Expr.var 16))) + (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ)))))

theorem old_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 4).head? = some (oldR05 p) := by rfl

theorem new_R05_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 4).head? = some (newR05 p) := by rfl

theorem R05_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR05 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR05 p).evalRing (fun j => ι (v j)) := by
  simp [oldR05, newR05, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR06 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  (((Expr.var 21) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

def newR06 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  (((Expr.var 21) + (Expr.constant (1 : ℤ))) - (((((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ)))) + (((Expr.var 17) + (Expr.var 16)) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))) + (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (((Expr.constant (4 : ℤ)) * ((Expr.var 17) + (Expr.var 16))) + (Expr.constant (3 : ℤ))))))

theorem old_R06_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 5).head? = some (oldR06 p) := by rfl

theorem new_R06_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 5).head? = some (newR06 p) := by rfl

theorem R06_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR06 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR06 p).evalRing (fun j => ι (v j)) := by
  simp [oldR06, newR06, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]


def oldR07 (p : Fin 4 → ℤ) : Expr (Fin 28) :=
  (((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ)))) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

def newR07 (p : Fin 4 → ℤ) : Expr (Fin 27) :=
  (((Expr.var 21) * ((Expr.var 21) + (Expr.constant (2 : ℤ)))) - ((Expr.var 20) * (((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))) * ((Expr.var 18) + ((Expr.var 11) + (Expr.constant (1 : ℤ)))))))

theorem old_R07_row (p : Fin 4 → ℤ) :
    ((SharingSeed27Sextic.remainingResiduals p).drop 6).head? = some (oldR07 p) := by rfl

theorem new_R07_row (p : Fin 4 → ℤ) :
    ((SharingSeed26Sextic.remainingResiduals p).drop 6).head? = some (newR07 p) := by rfl

theorem R07_eval (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V) :
    (oldR07 p).evalRing (fun j => ι (Sign26CongruenceCuts.lift gap v j)) =
      (newR07 p).evalRing (fun j => ι (v j)) := by
  simp [oldR07, newR07, Sign26CongruenceCuts.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant]

end DiophantineConsistency.Sign26RemainingCuts
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R01_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R01_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R01_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R02_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R02_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R02_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R03_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R03_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R03_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R04_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R04_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R04_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R05_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R05_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R05_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R06_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R06_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R06_eval
#print axioms DiophantineConsistency.Sign26RemainingCuts.old_R07_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.new_R07_row
#print axioms DiophantineConsistency.Sign26RemainingCuts.R07_eval
