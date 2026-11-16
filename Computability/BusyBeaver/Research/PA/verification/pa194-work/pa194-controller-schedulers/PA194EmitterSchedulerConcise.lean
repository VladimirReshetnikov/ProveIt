import PA194EmitterSchedulerPA
import IPRABridge.Standard

/-! ConciseIPRA forms of the checked command-scheduler equivalences. The
halting predicates are the original scheduler halting sentences. Literal
machine bindings have their own proof interfaces. -/

set_option autoImplicit false

namespace PA194EmitterSchedulerConcise

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open ConPA.Ctl (MPKind)
open PA194EmitterScheduler (Emitter)
open PA194EmitterSchedulerPA (haltSentenceE)
open DiophantineConsistency.IPRAPA196Consistency (nativePAConsistency)

/-- Keep the selected emitter, modus ponens protocol, halting test, and AX
layout in the translated Foundation sentence. -/
noncomputable def sentence (e : Emitter) (k : MPKind) (ct a : Bool) : Fm PTm 0 :=
  IPRABridge.toConciseSentence (nativePAConsistency 🡘 ∼haltSentenceE e k ct a)

theorem consistency_iff_scheduler_nonhalt (e : Emitter) (k : MPKind) (ct a : Bool) :
    Prf PRAAx [] (sentence e k ct a) :=
  IPRABridge.standardToConcise
    (PA194EmitterSchedulerPA.consistency_iff_scheduler_nonhalt e k ct a)

/-- Original PA195's bundled diagonal command scheduler. -/
theorem pa195_consistency_iff_scheduler_nonhalt :
    Prf PRAAx [] (sentence
      { gd := false, q := false, x := false, ga := false, bundled := true, delta := false }
      .push false false) :=
  consistency_iff_scheduler_nonhalt _ _ _ _

/-- PA196's equality-vacuity command scheduler. -/
theorem pa196_consistency_iff_scheduler_nonhalt :
    Prf PRAAx [] (sentence
      { gd := false, q := false, x := false, ga := false, bundled := false, delta := true }
      .push false false) :=
  consistency_iff_scheduler_nonhalt _ _ _ _

#print axioms consistency_iff_scheduler_nonhalt
#print axioms pa195_consistency_iff_scheduler_nonhalt
#print axioms pa196_consistency_iff_scheduler_nonhalt

end PA194EmitterSchedulerConcise
