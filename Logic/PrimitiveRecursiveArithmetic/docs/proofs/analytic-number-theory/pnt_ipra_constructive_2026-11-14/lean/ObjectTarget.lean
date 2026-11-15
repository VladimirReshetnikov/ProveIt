import ConciseIPRA.NativeBiInterpretation

/-!
# The required object-level endpoint

STATUS: uncompiled integration outline. Requires the ProveIt `ConciseIPRA`
Lake library, audited at commit b03925cccc76d55b9dc2a00864a5e0544b64aa7f.

The parameter `compiledCheck` below is intentionally NOT postulated as a
constant and no PNT proof is assumed by an axiom. It must be constructed
from the concrete recursive definitions in RationalPNT.lean. The only
theorems here are generic, already justified proof-transfer wrappers.
-/

namespace ConstructivePNT.Object

open LeanProofs.ConciseIPRA
open scoped LeanProofs.ConciseIPRA.Fm

/-- Read the two arguments as k,n even though the innermost binder has
    de Bruijn index 0 (n) and the outer binder has index 1 (k). -/
def checkMatrix (compiledCheck : PR 2) : Fm PTm 2 :=
  Fm.eq
    (PTm.app compiledCheck
      (fun i => if i.val = 0 then PTm.var 1 else PTm.var 0))
    (PTm.succ PTm.zero)

/-- The required closed theorem: forall k, forall n, check(k,n)=1. -/
def universalCheck (compiledCheck : PR 2) : Fm PTm 0 :=
  Fm.all (Fm.all (checkMatrix compiledCheck))

/-- This type, with a concrete compiledCheck and a proved interpretation
    theorem for that code, is the principal completion criterion. -/
def RequiredCertificate (compiledCheck : PR 2) : Prop :=
  Prf PRAAx [] (universalCheck compiledCheck)

/-- A completed iPRA derivation transfers to the concise native calculus
    using the audited repository theorem. This is generic proof transport,
    not the missing number-theoretic proof. -/
theorem nativeCertificate_of_iPRACertificate (compiledCheck : PR 2)
    (h : RequiredCertificate compiledCheck) :
    NPrf [] (NFm.ofPRA (universalCheck compiledCheck)) := by
  exact pra_iff_native.mp h

/-- Conversely, a native certificate is an iPRA certificate. -/
theorem iPRACertificate_of_nativeCertificate (compiledCheck : PR 2)
    (h : NPrf [] (NFm.ofPRA (universalCheck compiledCheck))) :
    RequiredCertificate compiledCheck := by
  exact pra_iff_native.mpr h

/-!
Acceptance checks for the completed development:

* `compiledCheck` is a defined term of PR 2, not an axiom or parameter in
  the final exported theorem.
* Its evaluation is proved equal to the exact Boolean pntCheck for the
  chosen explicit primitive-recursive modulus.
* The final exported theorem inhabits RequiredCertificate compiledCheck.
* No `sorry`, `admit`, PNT axiom, or extra arithmetic induction rule occurs.
* `#print axioms` is recorded for the certificate and its dependencies.
  The presence or absence of Classical.choice in ambient Lean metatheory
  is not by itself the test for intuitionistic object logic; the explicit
  derivation datatype and its allowed rules are the decisive boundary.
* Standard-model semantics and the conventional Real.log corollary are
  checked separately, so a faithful statement is established as well as
  a valid derivation.
-/

end ConstructivePNT.Object
