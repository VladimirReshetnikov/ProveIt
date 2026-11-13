module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionConnectives
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain value equal PairGraph.orderIso

def realizedFormulaAll {n : Nat} (p : SourceFormula (n+1))
    (ih : RealizedFormulaCompatible p) : RealizedFormulaCompatible (.all p) where
  forward := by
    intro k σ Γ A b f c g H h
    apply formulaAllIntro p c g
    let d : Form := Ordinal.domain (.fvar 0)
    have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
    let A' := A.shift.up d
    have H' := FormulaRealization.up (FormulaRealization.shift H) d
    have HL := formulaRealizationLift p σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) A'.coherence.equality (.fvar 0) hd
      (fun v hv => H' v (.all hv))
    exact ih.forward σ.q A' _ _ _ _ HL
      (mp hd (up (formulaAllOpen (Semiformula.rewAux σ.q p) b f h) d))
  backward := by
    intro k σ Γ A b f c g H h
    apply formulaAllIntro (Semiformula.rewAux σ.q p) b f
    let d : Form := Ordinal.domain (.fvar 0)
    have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
    let A' := A.shift.up d
    have H' := FormulaRealization.up (FormulaRealization.shift H) d
    have HL := formulaRealizationLift p σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) A'.coherence.equality (.fvar 0) hd
      (fun v hv => H' v (.all hv))
    exact ih.backward σ.q A' _ _ _ _ HL (mp hd (up (formulaAllOpen p c g h) d))

def realizedFormulaExists {n : Nat} (p : SourceFormula (n+1))
    (ih : RealizedFormulaCompatible p) : RealizedFormulaCompatible (.exs p) where
  forward := by
    intro k σ Γ A b f c g H h
    apply formulaExistsElim (Semiformula.rewAux σ.q p) b f _ h
    let d : Form := Ordinal.domain (.fvar 0) ⋏ formula (Semiformula.rewAux σ.q p)
      (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f)
    have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
    let A' := A.shift.up d
    have H' := FormulaRealization.up (FormulaRealization.shift H) d
    have HL := formulaRealizationLift p σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) A'.coherence.equality (.fvar 0) (andLeft hd)
      (fun v hv => H' v (.exs hv))
    exact formulaExistsFresh p c g
      (andIntro (andLeft hd) (ih.forward σ.q A' _ _ _ _ HL (andRight hd)))
  backward := by
    intro k σ Γ A b f c g H h
    apply formulaExistsElim p c g _ h
    let d : Form := Ordinal.domain (.fvar 0) ⋏ formula p
      (Fin.cases (.fvar 0) (freeShiftEnv c)) (freeShiftEnv g)
    have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
    let A' := A.shift.up d
    have H' := FormulaRealization.up (FormulaRealization.shift H) d
    have HL := formulaRealizationLift p σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) A'.coherence.equality (.fvar 0) (andLeft hd)
      (fun v hv => H' v (.exs hv))
    exact formulaExistsFresh (Semiformula.rewAux σ.q p) b f
      (andIntro (andLeft hd) (ih.backward σ.q A' _ _ _ _ HL (andRight hd)))

#print axioms realizedFormulaAll
#print axioms realizedFormulaExists
end M6.PA.ForwardRelational
