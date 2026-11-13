module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceRules
public import M6PA.Calibration.RelationalAdditionCoherenceApplications
@[expose] public section

/-! Explicit proof data for using the coherence induction hypothesis. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] mulResult orderIso Ordinal.domain
set_option maxHeartbeats 600000

def mulCoherenceIsoShift {Γ : List Form} (a b : Nat)
    (h : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (orderIso (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> mulCoherenceSyntax

def mulCoherenceResultShift {Γ : List Form} (a b c : Nat)
    (h : ND.Proof Γ (mulResult (.fvar a) (.fvar b) (.fvar c))) :
    ND.Proof (shifted Γ) (mulResult (.fvar (a+1)) (.fvar (b+1)) (.fvar (c+1))) := by
  convert shiftProof h using 1 <;> mulCoherenceSyntax

def additionCoherenceClosedShift {Γ : List Form}
    (h : ND.Proof Γ addCoherenceStatement) : ND.Proof (shifted Γ) addCoherenceStatement := by
  convert shiftProof h using 1 <;>
    ((try simp only [addCoherenceStatement]) <;> coherenceInductionSyntax)

structure MultiplicationCoherenceFrame (Γ : List Form) (p q b c : Nat) where
  addition : ND.Proof Γ addCoherenceStatement
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  hypothesis : ND.Proof Γ (mulCoherence (.fvar p))
  targetDomain : ND.Proof Γ (Ordinal.domain (.fvar q))
  leftBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar b))
  rightBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar c))
  inputIso : ND.Proof Γ (orderIso (.fvar p) (.fvar q))
  baseIso : ND.Proof Γ (orderIso (.fvar b) (.fvar c))

def MultiplicationCoherenceFrame.weaken {Γ Δ : List Form} {p q b c : Nat}
    (I : MultiplicationCoherenceFrame Γ p q b c) (inc : ∀ t,t∈Γ→t∈Δ) :
    MultiplicationCoherenceFrame Δ p q b c where
  addition := ND.weaken I.addition inc
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  hypothesis := ND.weaken I.hypothesis inc
  targetDomain := ND.weaken I.targetDomain inc
  leftBaseDomain := ND.weaken I.leftBaseDomain inc
  rightBaseDomain := ND.weaken I.rightBaseDomain inc
  inputIso := ND.weaken I.inputIso inc
  baseIso := ND.weaken I.baseIso inc

def MultiplicationCoherenceFrame.shift {Γ : List Form} {p q b c : Nat}
    (I : MultiplicationCoherenceFrame Γ p q b c) :
    MultiplicationCoherenceFrame (shifted Γ) (p+1) (q+1) (b+1) (c+1) where
  addition := additionCoherenceClosedShift I.addition
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  hypothesis := mulCoherenceShift p I.hypothesis
  targetDomain := Ordinal.domainShift q I.targetDomain
  leftBaseDomain := Ordinal.domainShift b I.leftBaseDomain
  rightBaseDomain := Ordinal.domainShift c I.rightBaseDomain
  inputIso := mulCoherenceIsoShift p q I.inputIso
  baseIso := mulCoherenceIsoShift b c I.baseIso

def multiplicationCoherenceUse {Γ : List Form} (p q b c r s : Nat)
    (I : MultiplicationCoherenceFrame Γ p q b c)
    (hr : ND.Proof Γ (mulResult (.fvar p) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  mp (andIntro I.targetDomain (andIntro I.leftBaseDomain (andIntro I.rightBaseDomain
    (andIntro I.inputIso (andIntro I.baseIso (andIntro hr hs))))))
    (mulCoherenceAt p q b c r s I.hypothesis)

#print axioms MultiplicationCoherenceFrame.shift
#print axioms multiplicationCoherenceUse
end M6.PA.RelationalSource.PairGraph
