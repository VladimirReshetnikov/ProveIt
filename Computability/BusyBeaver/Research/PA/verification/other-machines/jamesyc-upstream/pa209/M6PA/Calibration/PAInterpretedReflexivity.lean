module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualityWitnesses
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! One literal fixed PAeq axiom under the typed relational interpretation.
This does not assume a theory interpretation or source substitution theorem. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 600000

def interpretedReflexivity {Γ : List Form} (E : FormulaEquality Γ)
    (hidentity : ND.Proof Γ PairGraph.identityStatement) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.reflexivity Fin.elim0 f) := by
  have href := PairGraph.orderIsoReflexivityProof E hidentity
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let C := d::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0)) := assumption (by simp [C,d])
  let EE := E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hs : ND.Proof (shifted Γ) PairGraph.orderIsoReflexivityStatement := by
    convert shiftProof href using 1 <;>
      ((try simp only [PairGraph.orderIsoReflexivityStatement]) <;> interpretedWitnessSyntax)
  have hself : ND.Proof C (PairGraph.orderIso (.fvar 0) (.fvar 0)) := by
    have hh : ND.Proof C (Ordinal.domain (.fvar 0) 🡒 PairGraph.orderIso (.fvar 0) (.fvar 0)) := by
      convert allElim _ (.fvar 0) (up hs d) using 1 <;>
        ((try simp only [PairGraph.orderIsoReflexivityStatement]) <;> interpretedWitnessSyntax)
    exact mp hd hh
  let b : Fin 1 → Term 0 := fun _ => .fvar 0
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hv : ND.Proof C (value (.bvar 0) b fs (.fvar 0)) := by
    rw [value_bvar]
    exact andIntro hd (EE.reflexive (.fvar 0))
  have out := equalityValueIntro (.bvar 0) (.bvar 0) b fs (.fvar 0) (.fvar 0) hv hv hself
  convert impIntro out using 1 <;>
    (dsimp [C,d,b,fs] <;>
      (try simp only [formula,Presentation.reflexivity,Presentation.eq,bindEnv]) <;>
      interpretedWitnessSyntax)

#print axioms interpretedReflexivity
end M6.PA.ForwardRelational

