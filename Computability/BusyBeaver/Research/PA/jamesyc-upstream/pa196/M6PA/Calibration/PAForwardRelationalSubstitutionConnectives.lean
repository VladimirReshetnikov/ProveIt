module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionFormulaTypes
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def realizedFormulaAnd {n : Nat} (p q : SourceFormula n)
    (ihp : RealizedFormulaCompatible p) (ihq : RealizedFormulaCompatible q) :
    RealizedFormulaCompatible (.and p q) where
  forward := by
    intro k σ Γ A b f c g H h
    exact andIntro (ihp.forward σ A b f c g (fun v hv => H v (.andLeft hv)) (andLeft h))
      (ihq.forward σ A b f c g (fun v hv => H v (.andRight hv)) (andRight h))
  backward := by
    intro k σ Γ A b f c g H h
    exact andIntro (ihp.backward σ A b f c g (fun v hv => H v (.andLeft hv)) (andLeft h))
      (ihq.backward σ A b f c g (fun v hv => H v (.andRight hv)) (andRight h))

def realizedFormulaOr {n : Nat} (p q : SourceFormula n)
    (ihp : RealizedFormulaCompatible p) (ihq : RealizedFormulaCompatible q) :
    RealizedFormulaCompatible (.or p q) where
  forward := by
    intro k σ Γ A b f c g H h
    apply orElim h
    · let r := formula (Semiformula.rewAux σ p) b f
      exact orLeft (ihp.forward σ (A.up r) b f c g
        (fun v hv => (H v (.orLeft hv)).up r) (assumption (by simp [r])))
    · let r := formula (Semiformula.rewAux σ q) b f
      exact orRight (ihq.forward σ (A.up r) b f c g
        (fun v hv => (H v (.orRight hv)).up r) (assumption (by simp [r])))
  backward := by
    intro k σ Γ A b f c g H h
    apply orElim h
    · let r := formula p c g
      exact orLeft (ihp.backward σ (A.up r) b f c g
        (fun v hv => (H v (.orLeft hv)).up r) (assumption (by simp [r])))
    · let r := formula q c g
      exact orRight (ihq.backward σ (A.up r) b f c g
        (fun v hv => (H v (.orRight hv)).up r) (assumption (by simp [r])))

#print axioms realizedFormulaAnd
#print axioms realizedFormulaOr
end M6.PA.ForwardRelational
