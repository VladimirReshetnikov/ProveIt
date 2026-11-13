module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightZero
public import M6PA.Calibration.RelationalOrderIsoTransport
@[expose] public section

/-! Right-successor syntax and the genuine zero-input case. All five other
parameters are bound in the induction property, including the displayed successor. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightSuccessorPremise (x b c r s v : Term n) : Formula n :=
  Ordinal.domain b ⋏ (Ordinal.domain c ⋏ (Ordinal.domain r ⋏
    (Ordinal.successor b c ⋏ (addResult x b r ⋏
      (addResult x c s ⋏ Ordinal.successor r v)))))
def addRightSuccessorPoint (x b c r s v : Term n) : Formula n :=
  addRightSuccessorPremise x b c r s v 🡒 orderIso v s

def addRightSuccessor (x : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ ∀¹ ∀¹ addRightSuccessorPoint
    (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift x)))))
    (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
def addRightSuccessorProperty : Formula 1 := addRightSuccessor (.bvar 0)

macro "addRightSuccessorSyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,addRightSuccessor,addRightSuccessorProperty,
    addRightSuccessorPoint,addRightSuccessorPremise,
    addPredecessorResult,addResult_rew,orderIso_rew,Ordinal.domain_rew,
    Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def addRightSuccessorAt {Γ : List Form} (x b c r s v : Nat)
    (h : ND.Proof Γ (addRightSuccessor (.fvar x))) :
    ND.Proof Γ (addRightSuccessorPoint (.fvar x) (.fvar b) (.fvar c) (.fvar r) (.fvar s) (.fvar v)) := by
  convert allElim _ (.fvar v) (allElim _ (.fvar s) (allElim _ (.fvar r)
    (allElim _ (.fvar c) (allElim _ (.fvar b) h)))) using 1 <;> addRightSuccessorSyntax

def addRightSuccessorShift {Γ : List Form} (x : Nat)
    (h : ND.Proof Γ (addRightSuccessor (.fvar x))) :
    ND.Proof (shifted Γ) (addRightSuccessor (.fvar (x+1))) := by
  convert shiftProof h using 1 <;> addRightSuccessorSyntax

def rightSuccessorIdentityShift {Γ : List Form} (h : ND.Proof Γ identityStatement) :
    ND.Proof (shifted Γ) identityStatement := by
  convert shiftProof h using 1 <;>
    ((try simp only [identityStatement,Ordinal.inductionConclusion,identityProperty]) <;> isoSyntax)

structure AdditionRightSuccessorBasis (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  identity : ND.Proof Γ identityStatement
  separation : ND.Proof Γ closedInclusiveSeparation

def AdditionRightSuccessorBasis.shift {Γ : List Form} (I : AdditionRightSuccessorBasis Γ) :
    AdditionRightSuccessorBasis (shifted Γ) :=
  ⟨I.equality.shifted,emptyClosedShift I.empty,adjunctionClosedShift I.adjunction,
    rightSuccessorIdentityShift I.identity,additionInclusiveSeparationShift I.separation⟩

def AdditionRightSuccessorBasis.weaken {Γ Δ : List Form} (I : AdditionRightSuccessorBasis Γ)
    (inc : ∀ q,q∈Γ→q∈Δ) : AdditionRightSuccessorBasis Δ :=
  ⟨I.equality.weaken inc,ND.weaken I.empty inc,ND.weaken I.adjunction inc,
    ND.weaken I.identity inc,ND.weaken I.separation inc⟩

def addRightSuccessorBasePoint {Γ : List Form} (I : AdditionRightSuccessorBasis Γ)
    (x b c r s v : Nat) (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addRightSuccessorPoint (.fvar x) (.fvar b) (.fvar c) (.fvar r) (.fvar s) (.fvar v)) := by
  apply impIntro
  let d : Form := addRightSuccessorPremise (.fvar x) (.fvar b) (.fvar c) (.fvar r) (.fvar s) (.fvar v)
  have hd : ND.Proof (d::Γ) d := assumption (by simp)
  let J := I.weaken (fun q hq => List.mem_cons_of_mem d hq)
  have h1 := andRight (andRight (andRight hd))
  have er := addResultZeroOutput J.equality x b r (up hz d) (andLeft (andRight h1))
  have es := addResultZeroOutput J.equality x c s (up hz d) (andLeft (andRight (andRight h1)))
  have lower := orderIsoFromEquality J.equality r b J.identity (andLeft (andRight (andRight hd))) er
  have out := orderIsoSuccessor J.equality r b v c J.empty J.adjunction
    (andLeft (andRight (andRight hd))) (andLeft hd)
    (andRight (andRight (andRight h1))) (andLeft h1) lower
  exact orderIsoRightTransport J.equality v c s (J.equality.symmetryOf es) out

def addRightSuccessorBase {Γ : List Form} (I : AdditionRightSuccessorBasis Γ)
    (x : Nat) (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addRightSuccessor (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  have h0 := Ordinal.zeroShift x hz
  have h1 := Ordinal.zeroShift (x+1) h0
  have h2 := Ordinal.zeroShift (x+1+1) h1
  have h3 := Ordinal.zeroShift (x+1+1+1) h2
  have h4 := Ordinal.zeroShift (x+1+1+1+1) h3
  have out := addRightSuccessorBasePoint I.shift.shift.shift.shift.shift
    (x+1+1+1+1+1) 4 3 2 1 0 h4
  convert out using 1 <;> addRightSuccessorSyntax

#print axioms addRightSuccessorAt
#print axioms addRightSuccessorBase
end M6.PA.RelationalSource.PairGraph
