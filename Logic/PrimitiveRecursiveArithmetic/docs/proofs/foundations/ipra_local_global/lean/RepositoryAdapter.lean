import ConciseIPRA.NativeBiInterpretation

/-!
Source-level adapter for the pinned ProveIt repository. This file is NOT
included in the standalone build. In a repository build, change the
ObjectIteration and NegativeSyntax import from ObjectKernel to ConciseIPRA.PR;
do not import both copies of the same kernel declarations.
-/

namespace LeanProofs.ConciseIPRA.LocalGlobal

theorem toNative {n : Nat} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Prf PRAAx Γ φ) : NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

end LeanProofs.ConciseIPRA.LocalGlobal
