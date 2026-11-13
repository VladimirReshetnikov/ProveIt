module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceOutputRight
public import M6PA.Calibration.RelationalAdditionZeroLaw
public import M6PA.Calibration.RelationalZeroIso
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! Right zero for arbitrary actual addition traces. The zero and output
representatives remain universally quantified; no canonical empty set is used. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightZeroPoint (x e r : Term n) : Formula n :=
  (Ordinal.zero e ⋏ addResult x e r) 🡒 orderIso x r

def addRightZero (x : Term n) : Formula n :=
  ∀¹ ∀¹ addRightZeroPoint (Rew.bShift (Rew.bShift x)) (.bvar 1) (.bvar 0)

def addRightZeroProperty : Formula 1 := addRightZero (.bvar 0)

macro "addRightZeroSyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,addRightZero,addRightZeroProperty,addRightZeroPoint,
    addPredecessorResult,addResult_rew,orderIso_rew,Ordinal.domain_rew,
    Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def addRightZeroAt {Γ : List Form} (x e r : Nat)
    (h : ND.Proof Γ (addRightZero (.fvar x)))
    (he : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar e) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar r)) := by
  have hh : ND.Proof Γ (addRightZeroPoint (.fvar x) (.fvar e) (.fvar r)) := by
    convert allElim _ (.fvar r) (allElim _ (.fvar e) h) using 1 <;> addRightZeroSyntax
  exact mp (andIntro he hr) hh

def addRightZeroShift {Γ : List Form} (x : Nat)
    (h : ND.Proof Γ (addRightZero (.fvar x))) :
    ND.Proof (shifted Γ) (addRightZero (.fvar (x+1))) := by
  convert shiftProof h using 1 <;> addRightZeroSyntax

def addRightZeroBasePoint {Γ : List Form} (E : FormulaEquality Γ) (x e r : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (he : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar e) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar r)) :=
  zeroOrderIso E x r hx (zeroTransport E e r
    (E.symmetryOf (addResultZeroOutput E x e r hx hr)) he)

def addRightZeroBase {Γ : List Form} (E : FormulaEquality Γ) (x : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addRightZero (.fvar x)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.zero (.fvar 1) ⋏ addResult (.fvar (x+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  have out := addRightZeroBasePoint
    (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) (x+1+1) 1 0
    (up (Ordinal.zeroShift (x+1) (Ordinal.zeroShift x hx)) d) (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightZeroSyntax)

def addRightZeroSuccessorPoint {Γ : List Form} (E : FormulaEquality Γ)
    (p x e r : Nat) (hempty : ND.Proof Γ emptyFormula)
    (hadj : ND.Proof Γ adjunctionFormula)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (hp : ND.Proof Γ (Ordinal.domain (.fvar p)))
    (hsucc : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x)))
    (hih : ND.Proof Γ (addRightZero (.fvar p)))
    (he : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar e) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar r)) := by
  apply exsElim (addResultPredecessor E p x e r hsep hp hsucc hr)
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar p) (.fvar e) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar r))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (p+1)) (.fvar (e+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> addRightZeroSyntax)
  let EE := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have lower := addRightZeroAt (p+1) (e+1) 0
    (up (addRightZeroShift p hih) body.free)
    (up (Ordinal.zeroShift e he) body.free) (andLeft (andRight hd))
  have out := orderIsoSuccessor EE (p+1) 0 (x+1) (r+1)
    (up (emptyClosedShift hempty) body.free) (up (adjunctionClosedShift hadj) body.free)
    (up (Ordinal.domainShift p hp) body.free) (andLeft hd)
    (up (Ordinal.successorShift p x hsucc) body.free) (andRight (andRight hd)) lower
  convert out using 1 <;> (dsimp [C,body] <;> addRightZeroSyntax)

structure AdditionRightZeroFrame (Γ : List Form) (p x : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  separation : ND.Proof Γ closedInclusiveSeparation
  domain : ND.Proof Γ (Ordinal.domain (.fvar p))
  successor : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))
  hypothesis : ND.Proof Γ (addRightZero (.fvar p))

def AdditionRightZeroFrame.shift {Γ : List Form} {p x : Nat}
    (I : AdditionRightZeroFrame Γ p x) : AdditionRightZeroFrame (shifted Γ) (p+1) (x+1) :=
  ⟨I.equality.shifted,emptyClosedShift I.empty,adjunctionClosedShift I.adjunction,
    additionInclusiveSeparationShift I.separation,Ordinal.domainShift p I.domain,
    Ordinal.successorShift p x I.successor,addRightZeroShift p I.hypothesis⟩

def addRightZeroSuccessor {Γ : List Form} (p x : Nat) (I : AdditionRightZeroFrame Γ p x) :
    ND.Proof Γ (addRightZero (.fvar x)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.zero (.fvar 1) ⋏ addResult (.fvar (x+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let J := I.shift.shift
  have out := addRightZeroSuccessorPoint
    (J.equality.weaken (fun q hq => List.mem_cons_of_mem d hq)) (p+1+1) (x+1+1) 1 0
    (up J.empty d) (up J.adjunction d) (up J.separation d) (up J.domain d)
    (up J.successor d) (up J.hypothesis d) (andLeft hd) (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightZeroSyntax)

#print axioms addRightZeroBase
#print axioms addRightZeroSuccessor
end M6.PA.RelationalSource.PairGraph
