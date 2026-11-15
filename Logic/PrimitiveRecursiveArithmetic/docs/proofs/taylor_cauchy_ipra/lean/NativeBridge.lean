import ConciseIPRA.NativeBiInterpretation

/-!
# The final object-theory bridge

Status: NOT compiled in the producing environment. The imported declarations
were inspected at ProveIt commit 876ef598f674759da5f084dc34f63ca4e182aae0.

This file provides the final transport step once an arithmetic derivation has
been built. It does not claim that the Taylor/Cauchy derivations already exist.
-/

namespace LeanProofs.ConciseIPRA.TaylorCauchy

/-- This is an object-theory derivation, not merely truth in Lean's naturals. -/
theorem native_of_ipra {n : Nat} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Prf PRAAx Γ φ) :
    NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

#print axioms native_of_ipra

end LeanProofs.ConciseIPRA.TaylorCauchy
