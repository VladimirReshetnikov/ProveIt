import ConciseIPRA.NativeBiInterpretation

/-!
# Interface for transporting completed object-iPRA proofs

STATUS: small interface scaffold, not a formalization of Dirichlet or
Kronecker. It is written against ProveIt commit
6ad3d9f37184ac242a8946f1c5d45a5603cf57f2 and has not been compiled here.

The input must already be an actual derivation in the inductively defined
object theory `PRAAx`. An ambient Lean proof of a semantic statement cannot
be substituted for this input. There are no `sorry` declarations or new
axioms in this scaffold.
-/

namespace DirichletKroneckerIPRA

open LeanProofs.ConciseIPRA

/-- A completed object theorem, before translation to the native syntax. -/
structure ObjectTheorem where
  arity : Nat
  formula : Fm PTm arity
  derivation : Prf PRAAx [] formula

/-- The verified repository bridge preserves an already supplied proof. -/
theorem ObjectTheorem.toNative (t : ObjectTheorem) :
    NPrf [] (NFm.ofPRA t.formula) := by
  exact (pra_iff_native (Γ := []) (φ := t.formula)).mp t.derivation

end DirichletKroneckerIPRA
