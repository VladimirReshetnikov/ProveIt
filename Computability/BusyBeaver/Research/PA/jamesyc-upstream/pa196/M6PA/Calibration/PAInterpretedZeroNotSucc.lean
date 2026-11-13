module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedZeroSuccessorEquality
public import M6PA.Calibration.PAPresentationAxioms
public import M6PA.Calibration.RelationalArithmeticLawContext
@[expose] public section

/-! Literal typed image of PAeq's zero/successor disjointness. No canonical
empty object or raw extensional equality is assumed. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000

def interpretedZeroNotSucc {Γ : List Form} (E : FormulaEquality Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.zeroNotSucc Fin.elim0 f) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let EE := E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  let b : Fin 1 → Term 0 := fun _ => .fvar 0
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have out := zeroSuccessorEqualityNeg EE (.bvar 0) b fs
  convert impIntro out using 1 <;>
    (dsimp [d,b,fs] <;>
      (try simp only [formula_neg,formula,Presentation.zeroNotSucc,Presentation.eq,bindEnv]) <;>
      interpretedWitnessSyntax <;>
      (try simp only [formula_rew,formula_neg,formula,bindEnv,rew_neg]) <;>
      (try interpretedWitnessSyntax))

def interpretedZeroNotSuccDerivation (ρ : Nat → Term 0) :
    ND.Proof arithmeticLawAxioms (formula Presentation.zeroNotSucc Fin.elim0 ρ) :=
  interpretedZeroNotSucc
    ⟨⟨assumption (by simp [arithmeticLawAxioms]),assumption (by simp [arithmeticLawAxioms]),
      assumption (by simp [arithmeticLawAxioms])⟩,assumption (by simp [arithmeticLawAxioms])⟩ ρ

def interpretedZeroNotSuccSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : ArithmeticLawBudget f lo z)
    (hbudget : lo+lkBudget (interpretedZeroNotSuccDerivation ρ)≤z) :
    NativeCalculus.ActualBasis.Proof (code (formula Presentation.zeroNotSucc Fin.elim0 ρ) f lo z) :=
  compileContext arithmeticLawAxioms _ (interpretedZeroNotSuccDerivation ρ) f lo z
    B.positive B.labels hbudget (arithmeticLawAxiomSupplier f lo z B)

#print axioms interpretedZeroNotSucc
#print axioms interpretedZeroNotSuccDerivation
#print axioms interpretedZeroNotSuccSupplier
end M6.PA.ForwardRelational

