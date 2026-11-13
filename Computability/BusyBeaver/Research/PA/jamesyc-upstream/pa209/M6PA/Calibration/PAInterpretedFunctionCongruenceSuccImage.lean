module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFunctionCongruenceSuccessor
public import M6PA.Calibration.PAInterpretedVariableEquality
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! The literal frozen successor-congruence axiom, with both domain guards
and both actual interpreted successor values retained. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedSuccCongruence {Γ : List Form}
    (A : CoherencePremises Γ) (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.succCongruence Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let b : Fin 2 → Term 0 := Fin.cases (.fvar 0) (fun i => Rew.shift (Fin.cases (.fvar 0) (fun j : Fin 0 => Rew.shift (Fin.elim0 j)) i))
  let fs := freeShiftEnv (freeShiftEnv f)
  let e := equal (.bvar 0) (.bvar 1) b fs
  change ND.Proof (d :: shifted (d :: shifted Γ))
    (e 🡒 equal (Presentation.succ (.bvar 0)) (Presentation.succ (.bvar 1)) b fs)
  apply impIntro
  let AA := ((A.shift.up d).shift.up d).up e
  let TT := ((T.shift.up d).shift.up d).up e
  have h0 : ND.Proof (e :: d :: shifted (d :: shifted Γ)) (Ordinal.domain (b 0)) :=
    assumption (by simp [b,d])
  have h1 : ND.Proof (e :: d :: shifted (d :: shifted Γ)) (Ordinal.domain (b 1)) := by
    change ND.Proof (e :: d :: shifted (d :: shifted Γ)) (Ordinal.domain (.fvar 1))
    have hh : ND.Proof (d :: shifted Γ) d := assumption (by simp)
    simpa [d,Semiformula.shift,Rewriting.shift,app_eq_rewAux,Ordinal.domain_rew,Rew.shift_fvar,b] using
      up (up (shiftProof hh) d) e
  have he : ND.Proof (e :: d :: shifted (d :: shifted Γ)) e := assumption (by simp)
  exact successorVariablesEqual AA TT 0 1 b fs h0 h1
    (boundVariableEqualityIso AA.equality 0 1 b fs he)

#print axioms interpretedSuccCongruence
end M6.PA.ForwardRelational

