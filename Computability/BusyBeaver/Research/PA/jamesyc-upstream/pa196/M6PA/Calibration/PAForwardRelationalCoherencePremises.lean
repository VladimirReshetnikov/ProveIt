module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotality
public import M6PA.Calibration.RelationalAdditionCoherenceApplications
public import M6PA.Calibration.RelationalMultiplicationCoherenceApplications
public import M6PA.Calibration.RelationalOrderIsoTransport
public import M6PA.Calibration.RelationalOrderIsoSuccessor
public import M6PA.Calibration.RelationalZeroIso
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso

structure CoherencePremises (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  addition : ND.Proof Γ addCoherenceStatement
  multiplication : ND.Proof Γ mulCoherenceStatement

def CoherencePremises.up {Γ : List Form} (A : CoherencePremises Γ) (p : Form) :
    CoherencePremises (p :: Γ) :=
  ⟨A.equality.weaken (fun _ h => List.mem_cons_of_mem p h), ND.up A.empty p,
    ND.up A.adjunction p, ND.up A.addition p, ND.up A.multiplication p⟩

def CoherencePremises.shift {Γ : List Form} (A : CoherencePremises Γ) :
    CoherencePremises (shifted Γ) where
  equality := A.equality.shifted
  empty := emptyClosedShift A.empty
  adjunction := adjunctionClosedShift A.adjunction
  addition := additionCoherenceClosedShift A.addition
  multiplication := by
    convert shiftProof A.multiplication using 1
    simp only [mulCoherenceStatement]
    mulCoherenceInductionSyntax

def groundName (x : Term 0) : {i : Nat // x = .fvar i} := by
  cases x with
  | bvar i => exact Fin.elim0 i
  | func fn _ => nomatch fn
  | fvar i => exact ⟨i,rfl⟩

def isoShift {Γ : List Form} {x y : Term 0}
    (h : ND.Proof Γ (orderIso x y)) :
    ND.Proof (shifted Γ) (orderIso (Rew.shift x) (Rew.shift y)) :=
  by
  simpa only [Semiformula.shift,Rewriting.shift,app_eq_rewAux,orderIso_rew] using shiftProof h

def isoEqualityTransport {Γ : List Form} (E : FormulaEquality Γ)
    (x y r s : Term 0) (hr : ND.Proof Γ (eq r x)) (hs : ND.Proof Γ (eq s y))
    (h : ND.Proof Γ (orderIso x y)) : ND.Proof Γ (orderIso r s) := by
  obtain ⟨x,rfl⟩ := groundName x
  obtain ⟨y,rfl⟩ := groundName y
  obtain ⟨r,rfl⟩ := groundName r
  obtain ⟨s,rfl⟩ := groundName s
  exact orderIsoRightTransport E r y s (E.symmetryOf hs)
    (orderIsoLeftTransport E x r y (E.symmetryOf hr) h)

def zeroValuesCoherent {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0) (r s : Term 0)
    (hr : ND.Proof Γ (value Presentation.zero b f r))
    (hs : ND.Proof Γ (value Presentation.zero b' f' s)) :
    ND.Proof Γ (orderIso r s) := by
  obtain ⟨r,rfl⟩ := groundName r
  obtain ⟨s,rfl⟩ := groundName s
  exact zeroOrderIso E r s (andRight hr) (andRight hs)

#print axioms CoherencePremises.shift
#print axioms isoEqualityTransport
#print axioms zeroValuesCoherent
end M6.PA.ForwardRelational
