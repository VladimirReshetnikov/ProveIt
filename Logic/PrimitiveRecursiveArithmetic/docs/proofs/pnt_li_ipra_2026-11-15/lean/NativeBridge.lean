import ConciseIPRA.NativeBiInterpretation

/-!
# The actual object-theory endpoint and the existing native bridge

STATUS: UNCOMPILED INTERFACE DRAFT.

The import and signatures were checked against the source at ProveIt commit
b5a3ad037723c44d69a3d5b28a950c554327a989. The current repository toolchain is
leanprover/lean4:v4.32.0. This source was not compiled in this environment.

The parameter check below must eventually be replaced by a concrete PR 3
term computing the exact liPntCheck in ArithmeticTarget.lean. No such term
or derivation is constructed in this interface file.

The theorems are generic proof transport. They neither assume PNT through
an added axiom nor turn an ambient Lean theorem into an iPRA derivation.
-/

namespace LiPNT.Object

open LeanProofs.ConciseIPRA

/-- check's arguments are (m,n,v). Under forall m, forall n, forall v,
the corresponding de Bruijn variable indices are respectively 2,1,0. -/
def checkerArguments (i : Fin 3) : PTm 3 :=
  if i.val = 0 then PTm.var 2 else
    if i.val = 1 then PTm.var 1 else PTm.var 0

def checkMatrix (check : PR 3) : Fm PTm 3 :=
  Fm.eq (PTm.app check checkerArguments) (PTm.succ PTm.zero)

/-- The desired closed sentence, once check is a fixed correctly compiled code. -/
def targetSentence (check : PR 3) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (checkMatrix check)))

/-- This is a type naming the required endpoint, not an assertion that it exists. -/
def RequiredDerivation (check : PR 3) : Prop :=
  Prf PRAAx [] (targetSentence check)

/-- Transfers a supplied object-theory derivation using the audited bridge. -/
theorem native_of_iPRA {check : PR 3}
    (h : RequiredDerivation check) :
    NPrf [] (NFm.ofPRA (targetSentence check)) := by
  simpa [RequiredDerivation] using
    (pra_iff_native (Γ := []) (φ := targetSentence check)).mp h

/-- The converse generic bridge is available as well. -/
theorem iPRA_of_native {check : PR 3}
    (h : NPrf [] (NFm.ofPRA (targetSentence check))) :
    RequiredDerivation check := by
  simpa [RequiredDerivation] using
    (pra_iff_native (Γ := []) (φ := targetSentence check)).mpr h

end LiPNT.Object
