import PA194MulCoherenceShifts
import PA194AdditionCoherenceApply
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain

def isoShift {Γ : List Form} (a b : Nat) (h : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof (ND.shifted Γ) (orderIso (.fvar (a+1)) (.fvar (b+1))) := by
  convert ND.shiftProof h using 1
  simp [Semiformula.shift,orderIso_rew,Rew.shift,Rew.map]

def additionClosedShift {Γ : List Form} (h : ND.Proof Γ addCoherenceStatement) :
    ND.Proof (ND.shifted Γ) addCoherenceStatement := by
  convert ND.shiftProof h using 1 <;> ((try simp only [addCoherenceStatement]) <;> coherenceInductionSyntax)

structure Frame (Γ : List Form) (p q b c : Nat) where
  addition : ND.Proof Γ addCoherenceStatement
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  hypothesis : ND.Proof Γ (coherence (.fvar p))
  targetDomain : ND.Proof Γ (Ordinal.domain (.fvar q))
  leftBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar b))
  rightBaseDomain : ND.Proof Γ (Ordinal.domain (.fvar c))
  inputIso : ND.Proof Γ (orderIso (.fvar p) (.fvar q))
  baseIso : ND.Proof Γ (orderIso (.fvar b) (.fvar c))

def Frame.weaken {Γ Δ : List Form} {p q b c : Nat} (I : Frame Γ p q b c) (inc : ∀ t, t ∈ Γ → t ∈ Δ) : Frame Δ p q b c where
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

def Frame.shift {Γ : List Form} {p q b c : Nat} (I : Frame Γ p q b c) :
    Frame (ND.shifted Γ) (p+1) (q+1) (b+1) (c+1) where
  addition := additionClosedShift I.addition
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  hypothesis := PA194MulCoherence.shift p I.hypothesis
  targetDomain := Ordinal.domainShift q I.targetDomain
  leftBaseDomain := Ordinal.domainShift b I.leftBaseDomain
  rightBaseDomain := Ordinal.domainShift c I.rightBaseDomain
  inputIso := isoShift p q I.inputIso
  baseIso := isoShift b c I.baseIso

def frameUse {Γ : List Form} (p q b c r s : Nat) (I : Frame Γ p q b c)
    (hr : ND.Proof Γ (mulResult (.fvar p) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  use p q b c r s I.hypothesis I.targetDomain I.leftBaseDomain I.rightBaseDomain I.inputIso I.baseIso hr hs
#print axioms Frame.shift
#print axioms frameUse
end PA194MulCoherence
