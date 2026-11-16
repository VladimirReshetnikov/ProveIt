import KIFCS.OpenContract

/-!
# Proof-bearing interfaces for the three coherence levels

The structures deliberately keep finite-use stability, path extension, and
metric regularity separate.  Constructing a record is the theorem-specific
proof obligation; no semantic existence field is silently converted to a PR
selector.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open scoped Fm

/-- Level I: a finite observed conclusion is stable over all viable choices. -/
structure StableObserver (n : Nat) where
  assumptions : List (Fm PTm n)
  observedConclusion : Fm PTm n
  eliminateChoice : Contract assumptions observedConclusion

/-- Level II: an explicitly represented extension step preserves viability and
compatibility.  The formulas are kept abstract so applications can choose
pairing and table encodings already available in `IPRADerivations`. -/
structure ExtensionSystem (n : Nat) where
  initialPremises : List (Fm PTm n)
  initialConclusion : Fm PTm n
  stepPremises : List (Fm PTm (n + 1))
  stepConclusion : Fm PTm (n + 1)
  initial : Contract initialPremises initialConclusion
  step : Contract stepPremises stepConclusion
  stepQF : stepConclusion.QF

/-- Level III: finite rational triangle and tail obligations needed to expose a
regular metric name. -/
structure RegularNameData (n : Nat) where
  premises : List (Fm PTm n)
  localMotion : Fm PTm n
  finiteTail : Fm PTm n
  regularity : Fm PTm n
  proveMotion : Contract premises localMotion
  proveTail : Contract premises finiteTail
  proveRegularity : Contract (localMotion :: finiteTail :: premises) regularity

namespace RegularNameData

/-- Compose the local motion and finite-tail producers with the regularity
consumer. -/
theorem compile (d : RegularNameData n) : Contract d.premises d.regularity :=
  d.proveRegularity.trans (fun psi hpsi => by
    rcases List.mem_cons.mp hpsi with hmotion | hrest
    · simpa [hmotion] using d.proveMotion
    · rcases List.mem_cons.mp hrest with htail | hprem
      · simpa [htail] using d.proveTail
      · exact Contract.hyp hprem)

end RegularNameData

end LeanProofs.ConciseIPRA.KIFCS
