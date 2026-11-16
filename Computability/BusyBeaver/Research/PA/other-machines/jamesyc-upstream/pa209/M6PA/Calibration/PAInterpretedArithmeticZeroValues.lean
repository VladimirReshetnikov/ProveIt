module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedArithmeticVariableValues
public import M6PA.Calibration.RelationalArithmeticZeroLaws
@[expose] public section

/-! Actual child witnesses of the two first-argument-zero term values. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.addResult PairGraph.mulResult Ordinal.zero
set_option maxHeartbeats 800000

def arithmeticZeroAddValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (Presentation.add Presentation.zero (.bvar i)) b f z)) :
    ND.Proof Γ (ND.eq z (b i)) := by
  obtain ⟨zn,rfl⟩ := groundName z
  apply binaryValueElim .addition Presentation.zero (.bvar i) b f (.fvar zn) _ h
  let d := binaryWitness .addition Presentation.zero (.bvar i) b f (.fvar zn)
  let C := d :: shifted (shifted Γ)
  have hd : ND.Proof C d := assumption (by simp [C])
  have hz := andLeft hd
  have hb := andLeft (andRight hd)
  rw [value_zero] at hz
  rw [value_bvar] at hb
  let EE := E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hg : ND.Proof C (PairGraph.addResult (.fvar 1) (.fvar 0) (.fvar (zn+2))) := andRight (andRight hd)
  have he := PairGraph.addResultZeroOutput EE 1 0 (zn+2) (andRight hz) hg
  have out := EE.transitivityOf he (andRight hb)
  convert out using 1 <;> (dsimp [C,d,freeShiftEnv]; try simp only [ND.eq]; interpretedWitnessSyntax)

def arithmeticZeroMulValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (Presentation.mul Presentation.zero (.bvar i)) b f z)) :
    ND.Proof Γ (Ordinal.zero z) := by
  obtain ⟨zn,rfl⟩ := groundName z
  apply binaryValueElim .multiplication Presentation.zero (.bvar i) b f (.fvar zn) _ h
  let d := binaryWitness .multiplication Presentation.zero (.bvar i) b f (.fvar zn)
  let C := d :: shifted (shifted Γ)
  have hd : ND.Proof C d := assumption (by simp [C])
  have hz := andLeft hd
  rw [value_zero] at hz
  let EE := E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hg : ND.Proof C (PairGraph.mulResult (.fvar 1) (.fvar 0) (.fvar (zn+2))) := andRight (andRight hd)
  have out := PairGraph.mulResultZeroOutput EE 1 0 (zn+2) (andRight hz) hg
  convert out using 1 <;> (dsimp [C,d,freeShiftEnv]; interpretedWitnessSyntax)

#print axioms arithmeticZeroAddValue
#print axioms arithmeticZeroMulValue
end M6.PA.ForwardRelational
