import ConPAMachineRelative
import PA1944LFinal
import PA1944LFastRows
import PA1944LSELRows
import PA1944LFastSELRows
import PA1944LHistoryRows
import PA1944LFastHistoryRows
import PA1944LSELHistoryRows
import PA1944LFastSELHistoryRows

set_option autoImplicit false

namespace PA1944LFastFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LFastRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => PA194GuardedShortcuts.sameHalt (V := V) PA1944LFastRows.certificate)

#print axioms consistency_iff_literal_nonhalt
end PA1944LFastFinal

set_option autoImplicit false

namespace PA1944LSELFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LSELRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedSelectors.sameHalt (V := V) PA1944LSELRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LSELFinal

set_option autoImplicit false

namespace PA1944LFastSELFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LFastSELRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFastFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedSelectors.sameHalt (V := V) PA1944LFastSELRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LFastSELFinal

set_option autoImplicit false

namespace PA1944LHistoryFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LHistoryRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedHistory.sameHalt (V := V) PA1944LHistoryRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LHistoryFinal

set_option autoImplicit false

namespace PA1944LFastHistoryFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LFastHistoryRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFastFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedHistory.sameHalt (V := V) PA1944LFastHistoryRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LFastHistoryFinal

set_option autoImplicit false

namespace PA1944LSELHistoryFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LSELHistoryRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LSELFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedHistory.sameHalt (V := V) PA1944LSELHistoryRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LSELHistoryFinal

set_option autoImplicit false

namespace PA1944LFastSELHistoryFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LFastSELHistoryRows.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    PA1944LFastSELFinal.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedHistory.sameHalt (V := V) PA1944LFastSELHistoryRows.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end PA1944LFastSELHistoryFinal
