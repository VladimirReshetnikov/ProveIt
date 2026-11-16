import FQNF.KernelCore
import IPRADerivations.Core.Division

/-!
# Quantitative names, independent certificates, and guarded exactness

Infinite mathematical objects are represented by finite observations requested
at an explicit precision.  A name theorem produces a valid finite certificate
for each query.  Cross-certificate stability proves that independently chosen
certificates have compatible observables; no coherent infinite witness stream
is selected.
-/

namespace LeanProofs.IPRA.FQNF

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- Planned fixed representation of a rational interval certificate. -/
structure IntervalInterface where
  valid : PR 3       -- precision, code, packed parameters
  lower : PR 2       -- code, parameters
  upper : PR 2
  widthOK : PR 2

/-- Cross-precision stability is an object-iPRA theorem about any two valid
certificates, not a host-level metric fact. -/
structure StableNameProof (I : IntervalInterface) where
  validityQF : Fm PTm 3
  stability : Fm PTm 5
  validity_qf : validityQF.QF
  stability_prf : ([] : List (Fm PTm 5)) ⊢[PRAAx] stability

/-- The exact-label adapter is deliberately guarded by an apartness formula. -/
structure GapAdapter where
  approximate : Fm PTm 2
  gap : Fm PTm 2
  exactLabel : Fm PTm 2
  recover : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    (approximate ⟶ gap ⟶ exactLabel)

end LeanProofs.IPRA.FQNF
