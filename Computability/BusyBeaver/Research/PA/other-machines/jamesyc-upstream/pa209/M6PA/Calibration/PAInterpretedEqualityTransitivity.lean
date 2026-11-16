module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedVariableEquality
public import M6PA.Calibration.RelationalOrderIsoClosedTransitivity
@[expose] public section

/-! Variable equality transitivity uses the actual closed order-isomorphism
composition theorem, with its source-domain premise explicit. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedIsoTransitivity {Γ : List Form} (a b c : Term 0)
    (h : ND.Proof Γ PairGraph.isoTransitivityClosed)
    (ha : ND.Proof Γ (Ordinal.domain a))
    (hab : ND.Proof Γ (PairGraph.orderIso a b)) (hbc : ND.Proof Γ (PairGraph.orderIso b c)) :
    ND.Proof Γ (PairGraph.orderIso a c) := by
  cases a with
  | bvar i => nomatch i
  | func fn _ => nomatch fn
  | fvar i =>
    cases b with
    | bvar j => nomatch j
    | func fn _ => nomatch fn
    | fvar j =>
      cases c with
      | bvar k => nomatch k
      | func fn _ => nomatch fn
      | fvar k => exact PairGraph.isoTransitivityClosedAt i j k h ha hab hbc

def interpretedTransitivityShift {Γ : List Form} (h : ND.Proof Γ PairGraph.isoTransitivityClosed) :
    ND.Proof (shifted Γ) PairGraph.isoTransitivityClosed := by
  convert shiftProof h using 1 <;>
    ((try simp only [PairGraph.isoTransitivityClosed_eq]) <;> interpretedWitnessSyntax)

def boundVariableEqualityTransitive {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j k : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (htrans : ND.Proof Γ PairGraph.isoTransitivityClosed)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) (hk : ND.Proof Γ (Ordinal.domain (b k)))
    (hij : ND.Proof Γ (equal (.bvar i) (.bvar j) b f))
    (hjk : ND.Proof Γ (equal (.bvar j) (.bvar k) b f)) :
    ND.Proof Γ (equal (.bvar i) (.bvar k) b f) :=
  boundVariableEqualityIntro E i k b f hi hk
    (interpretedIsoTransitivity (b i) (b j) (b k) htrans hi
      (boundVariableEqualityIso E i j b f hij) (boundVariableEqualityIso E j k b f hjk))

#print axioms interpretedIsoTransitivity
#print axioms interpretedTransitivityShift
#print axioms boundVariableEqualityTransitive
end M6.PA.ForwardRelational

