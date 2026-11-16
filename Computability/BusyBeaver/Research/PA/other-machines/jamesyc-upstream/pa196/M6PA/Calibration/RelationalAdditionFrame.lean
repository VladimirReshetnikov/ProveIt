module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRecurrenceExtension
public import M6PA.Calibration.RelationalOrdinalSuccessor
@[expose] public section

/-! Finite proof data for an addition-trace extension. Every field is an
ordinary actual derivation; no trace-existence premise is hidden. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

structure SetProofs (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  intersection : ND.Proof Γ Ordinal.intersectionFormula

def SetProofs.weaken {Γ Δ} (S : SetProofs Γ) (inc : ∀ p, p ∈ Γ → p ∈ Δ) : SetProofs Δ where
  equality := S.equality.weaken inc
  empty := ND.weaken S.empty inc
  adjunction := ND.weaken S.adjunction inc
  intersection := ND.weaken S.intersection inc

def SetProofs.shift {Γ} (S : SetProofs Γ) : SetProofs (shifted Γ) where
  equality := S.equality.shifted
  empty := emptyClosedShift S.empty
  adjunction := adjunctionClosedShift S.adjunction
  intersection := Ordinal.intersectionAxiomShift S.intersection

def prefixShift {Γ : List Form} (top base z g : Nat)
    (h : ND.Proof Γ (addPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g))) :
    ND.Proof (shifted Γ) (addPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar (g+1))) := by
  convert shiftProof h using 1 ; previousSyntax

structure AdditionFrame (Γ : List Form) (top u base z g : Nat) where
  sets : SetProofs Γ
  topDomain : ND.Proof Γ (Ordinal.domain (.fvar top))
  inputSucc : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u))
  trace : ND.Proof Γ (addPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g))

def AdditionFrame.weaken {Γ Δ} {top u base z g : Nat} (I : AdditionFrame Γ top u base z g)
    (inc : ∀ p, p ∈ Γ → p ∈ Δ) : AdditionFrame Δ top u base z g where
  sets := I.sets.weaken inc
  topDomain := ND.weaken I.topDomain inc
  inputSucc := ND.weaken I.inputSucc inc
  trace := ND.weaken I.trace inc

def AdditionFrame.shift {Γ} {top u base z g : Nat} (I : AdditionFrame Γ top u base z g) :
    AdditionFrame (shifted Γ) (top+1) (u+1) (base+1) (z+1) (g+1) where
  sets := I.sets.shift
  topDomain := domainShift top I.topDomain
  inputSucc := Ordinal.successorShift top u I.inputSucc
  trace := prefixShift top base z g I.trace

def AdditionFrame.up {Γ} {top u base z g : Nat} (I : AdditionFrame Γ top u base z g) (q : Form) :
    AdditionFrame (q::Γ) top u base z g := I.weaken (fun p hp => List.mem_cons_of_mem q hp)

def extendPrefix {Γ : List Form} (top u base z g c v h : Nat)
    (I : AdditionFrame Γ top u base z g)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar c) (.fvar v)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))) :
    ND.Proof Γ (addPrefix (.fvar u) (.fvar base) (.fvar z) (.fvar h)) := by
  let E := I.sets.equality
  have oldDomain := andLeft I.trace
  have oldFunctional := andLeft (andRight I.trace)
  have oldRange := andLeft (andRight (andRight I.trace))
  have oldEdge := andLeft (andRight (andRight (andRight I.trace)))
  have oldRecurrence := andRight (andRight (andRight (andRight I.trace)))
  have du := Ordinal.successorDomain E.core E.transitive I.sets.intersection
    (.fvar top) (.fvar u) I.topDomain I.inputSucc
  have dc := graphRangeAt g top c oldRange he
  have dv := Ordinal.successorDomain E.core E.transitive I.sets.intersection (.fvar c) (.fvar v) dc hs
  have hd := successorGraphDomain E top u v g h I.inputSucc oldDomain hx
  have hf := successorFunctional E top u v g h I.topDomain I.inputSucc oldDomain oldFunctional hx
  have hr := graphRangeExtension E g h u v oldRange hx dv
  have hb := exactPreservesEdge g h u v z base hx oldEdge
  have hrec := recurrenceExtension E top u c v g h ⟨du,I.inputSucc,hs,he,hx,oldRecurrence⟩
  exact andIntro hd (andIntro hf (andIntro hr (andIntro hb hrec)))

#print axioms extendPrefix
end M6.PA.RelationalSource.PairGraph
