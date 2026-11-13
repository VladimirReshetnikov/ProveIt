module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightZeroApplications
public import M6PA.Calibration.RelationalAdditionRightSuccessorApplications
public import M6PA.Calibration.RelationalOrderIsoClosedTransitivity
public import M6PA.Calibration.PAForwardRelationalTotalityOutputs
@[expose] public section

/-! The exact three-parameter commutativity induction property. Outputs are
compared by actual order isomorphism, never by extensional object equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addCommutativityPremise (x y r s : Term n) : Formula n :=
  Ordinal.domain y ⋏ (addResult x y r ⋏ addResult y x s)
def addCommutativityPoint (x y r s : Term n) : Formula n :=
  addCommutativityPremise x y r s 🡒 orderIso r s
def addCommutativity (x : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ addCommutativityPoint (Rew.bShift (Rew.bShift (Rew.bShift x)))
    (.bvar 2) (.bvar 1) (.bvar 0)
def addCommutativityProperty : Formula 1 := addCommutativity (.bvar 0)

macro "addCommutativitySyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,addCommutativity,addCommutativityProperty,
    addCommutativityPoint,addCommutativityPremise,
    addPredecessorResult,addResult_rew,orderIso_rew,Ordinal.domain_rew,
    Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def addCommutativityAt {Γ : List Form} (x y r s : Nat)
    (h : ND.Proof Γ (addCommutativity (.fvar x))) :
    ND.Proof Γ (addCommutativityPoint (.fvar x) (.fvar y) (.fvar r) (.fvar s)) := by
  convert allElim _ (.fvar s) (allElim _ (.fvar r) (allElim _ (.fvar y) h)) using 1 <;>
    addCommutativitySyntax

def addCommutativityShift {Γ : List Form} (x : Nat)
    (h : ND.Proof Γ (addCommutativity (.fvar x))) :
    ND.Proof (shifted Γ) (addCommutativity (.fvar (x+1))) := by
  convert shiftProof h using 1 <;> addCommutativitySyntax

def addRightZeroClosedShift {Γ : List Form} (h : ND.Proof Γ addRightZeroStatement) :
    ND.Proof (shifted Γ) addRightZeroStatement := by
  convert shiftProof h using 1 <;>
    ((try simp only [addRightZeroStatement]) <;> addRightZeroSyntax)

def addCommutativityBasePoint {Γ : List Form} (E : FormulaEquality Γ)
    (hzero : ND.Proof Γ addRightZeroStatement) (x y r s : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addCommutativityPoint (.fvar x) (.fvar y) (.fvar r) (.fvar s)) := by
  apply impIntro
  let d : Form := addCommutativityPremise (.fvar x) (.fvar y) (.fvar r) (.fvar s)
  have hd : ND.Proof (d::Γ) d := assumption (by simp)
  let EE := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
  have er := addResultZeroOutput EE x y r (up hx d) (andLeft (andRight hd))
  have hi := additionRightZeroApply y x s (up hzero d) (andLeft hd) (up hx d)
    (andRight (andRight hd))
  exact orderIsoLeftTransport EE y r s (EE.symmetryOf er) hi

def addCommutativityBase {Γ : List Form} (E : FormulaEquality Γ)
    (hzero : ND.Proof Γ addRightZeroStatement) (x : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addCommutativity (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have out := addCommutativityBasePoint E.shifted.shifted.shifted
    (addRightZeroClosedShift (addRightZeroClosedShift (addRightZeroClosedShift hzero)))
    (x+1+1+1) 2 1 0 (Ordinal.zeroShift (x+1+1) (Ordinal.zeroShift (x+1) (Ordinal.zeroShift x hx)))
  convert out using 1 <;> addCommutativitySyntax

#print axioms addCommutativityAt
#print axioms addCommutativityBase
end M6.PA.RelationalSource.PairGraph
