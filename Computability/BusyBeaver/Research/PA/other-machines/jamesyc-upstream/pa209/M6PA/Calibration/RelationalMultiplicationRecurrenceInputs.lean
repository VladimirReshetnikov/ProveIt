module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCompactSyntax
public import M6PA.Calibration.RelationalAdditionRecurrenceExtension
public import M6PA.Calibration.RelationalMultiplicationPreviousPreserve
public import M6PA.Calibration.RelationalMultiplicationResultTransport
@[expose] public section

/-! The actual successor step for multiplication recurrence with an explicit additive result. New predecessor cases
are discharged by local ordinal predecessor uniqueness, not extensionality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

structure MulRecurrenceInputs (Γ : List Form) (top u c v g h base : Nat) where
  topDomain : ND.Proof Γ (Ordinal.domain (.fvar u))
  inputSucc : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u))
  outputAdd : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v))
  endpoint : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c))
  extension : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))
  recurrence : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))

def MulRecurrenceInputs.weaken {Γ Δ} {top u c v g h base : Nat}
    (I : MulRecurrenceInputs Γ top u c v g h base) (inc : ∀ p, p ∈ Γ → p ∈ Δ) :
    MulRecurrenceInputs Δ top u c v g h base where
  topDomain := ND.weaken I.topDomain inc
  inputSucc := ND.weaken I.inputSucc inc
  outputAdd := ND.weaken I.outputAdd inc
  endpoint := ND.weaken I.endpoint inc
  extension := ND.weaken I.extension inc
  recurrence := ND.weaken I.recurrence inc

def mulRecurrenceShift {Γ : List Form} (g base : Nat) (hr : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))) :
    ND.Proof (shifted Γ) (mulRecurrence (.fvar (g+1)) (.fvar (base+1))) := by
  convert shiftProof hr using 1 ; mulCompactSyntax

def MulRecurrenceInputs.shift {Γ} {top u c v g h base : Nat} (I : MulRecurrenceInputs Γ top u c v g h base) :
    MulRecurrenceInputs (shifted Γ) (top+1) (u+1) (c+1) (v+1) (g+1) (h+1) (base+1) where
  topDomain := domainShift u I.topDomain
  inputSucc := Ordinal.successorShift top u I.inputSucc
  outputAdd := by
    convert shiftProof I.outputAdd using 1; mulCompactSyntax
  endpoint := edgeShift g top c I.endpoint
  extension := exactShift g h u v I.extension
  recurrence := mulRecurrenceShift g base I.recurrence

#print axioms MulRecurrenceInputs.shift

end M6.PA.RelationalSource.PairGraph
