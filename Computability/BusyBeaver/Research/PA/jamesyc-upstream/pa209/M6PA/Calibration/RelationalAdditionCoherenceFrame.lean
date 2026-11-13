module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceRules
public import M6PA.Calibration.RelationalOrderIsoSuccessor
@[expose] public section

/-! Explicit proof data for using the coherence induction hypothesis. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain
set_option maxHeartbeats 600000

def coherenceIsoShift {Γ : List Form} (a b : Nat)
    (h : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (orderIso (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> addCoherenceSyntax

def coherenceResultShift {Γ : List Form} (a b c : Nat)
    (h : ND.Proof Γ (addResult (.fvar a) (.fvar b) (.fvar c))) :
    ND.Proof (shifted Γ) (addResult (.fvar (a+1)) (.fvar (b+1)) (.fvar (c+1))) := by
  convert shiftProof h using 1 <;> addCoherenceSyntax

structure AdditionCoherenceFrame (Γ : List Form) (p q b c : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  hypothesis : ND.Proof Γ (addCoherence (.fvar p))
  targetDomain : ND.Proof Γ (Ordinal.domain (.fvar q))
  leftBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar b))
  rightBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar c))
  inputIso : ND.Proof Γ (orderIso (.fvar p) (.fvar q))
  baseIso : ND.Proof Γ (orderIso (.fvar b) (.fvar c))

def AdditionCoherenceFrame.weaken {Γ Δ : List Form} {p q b c : Nat}
    (I : AdditionCoherenceFrame Γ p q b c) (inc : ∀ t,t∈Γ→t∈Δ) :
    AdditionCoherenceFrame Δ p q b c where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  hypothesis := ND.weaken I.hypothesis inc
  targetDomain := ND.weaken I.targetDomain inc
  leftBaseDomain := ND.weaken I.leftBaseDomain inc
  rightBaseDomain := ND.weaken I.rightBaseDomain inc
  inputIso := ND.weaken I.inputIso inc
  baseIso := ND.weaken I.baseIso inc

def AdditionCoherenceFrame.shift {Γ : List Form} {p q b c : Nat}
    (I : AdditionCoherenceFrame Γ p q b c) :
    AdditionCoherenceFrame (shifted Γ) (p+1) (q+1) (b+1) (c+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  hypothesis := addCoherenceShift p I.hypothesis
  targetDomain := Ordinal.domainShift q I.targetDomain
  leftBaseDomain := Ordinal.domainShift b I.leftBaseDomain
  rightBaseDomain := Ordinal.domainShift c I.rightBaseDomain
  inputIso := coherenceIsoShift p q I.inputIso
  baseIso := coherenceIsoShift b c I.baseIso

def additionCoherenceUse {Γ : List Form} (p q b c r s : Nat)
    (I : AdditionCoherenceFrame Γ p q b c)
    (hr : ND.Proof Γ (addResult (.fvar p) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  mp (andIntro I.targetDomain (andIntro I.leftBaseDomain (andIntro I.rightBaseDomain
    (andIntro I.inputIso (andIntro I.baseIso (andIntro hr hs))))))
    (addCoherenceAt p q b c r s I.hypothesis)

#print axioms AdditionCoherenceFrame.shift
#print axioms additionCoherenceUse
end M6.PA.RelationalSource.PairGraph
