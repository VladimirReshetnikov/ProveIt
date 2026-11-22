import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.Core.OrderCertificates

/-!
Uncompiled ProveIt integration outline.
The import paths and derive_imp / ipra_poly / Prf PRAAx interface were
inspected in the repository. Small displayed ring identities are written
as object-language proof terms. The main endpoint is DEFINED, not proved.
The file requires ProveIt's own Lake workspace and transitive imports.
-/

namespace LeanProofs.IPRA.PlatonicSections

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ZExp

section Cube
local notation "r" => (ZExp.var 0 : ZExp 1)

theorem cube_slack_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (imp []
        (2*(1+r)^4-(2+r^2)*(1+2*r)^2, r^2*(3+4*r-2*r^2))) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Cube

section Octahedron
local notation "a" => (ZExp.var 0 : ZExp 3)
local notation "b" => (ZExp.var 1 : ZExp 3)
local notation "c" => (ZExp.var 2 : ZExp 3)

theorem octa_slack_identity :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (imp []
        (((a+b)*(a+c)*(b+c))^2-(a^2+b^2+c^2)*(a*b+a*c+b*c)^2,
         2*(a^3*b^3+a^3*c^3+b^3*c^3) +
         4*a*b*c*(a^2*b+a^2*c+a*b^2+a*c^2+b^2*c+b*c^2) +
         7*a^2*b^2*c^2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Octahedron

/-- The five free natural numbers code the solid index, three normal
coordinates, and the plane offset. `valid` and `comparison` are the
primitive-recursive Boolean terms described in the report. -/
def endpointBody (valid comparison : PTm 5) : Fm PTm 5 :=
  (valid ≐ LeanProofs.IPRA.PTm.num 1) ⟶
  (comparison ≐ LeanProofs.IPRA.PTm.num 1)

def endpointSentence (valid comparison : PTm 5) : Fm PTm 0 :=
  univ 5 (endpointBody valid comparison)

/-- Intended theorem TYPE. This definition is deliberately not a proof. -/
def SharpEndpoint (valid comparison : PTm 5) : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] endpointSentence valid comparison

/-!
Instantiation obligations (not claimed completed):

* Compile the explicit code functions in arithmetic.tex to PTm terms.
  `valid` checks solid < 5, valid field denominators, and a nonzero normal.
  `comparison` is leK (SecSq solid normal offset) (bound solid).
* Prove their equations and the geometric Boolean invariants using
  quantifier-free induction and the finite sign-case elimination rules.
* Derive positive coefficient evaluation in the object language. Use
  Core/OrderCertificates.ipra_le after clearing positive denominators;
  do not cancel arbitrary nonzero elements of Groth (Q Γ), which is
  a commutative ring but is not assumed to be a domain.
* Lift the central-section identity CS5 and finite symmetry maximum to
  object-language derivations.
* Instantiate the exact constant certificates by kernel-checked arithmetic,
  compose the five cases, and close the five universal quantifiers.

A theorem about area over Mathlib.Real alone would not complete this
endpoint. No axiom of classical real analysis is inserted into PRAAx.
-/

end LeanProofs.IPRA.PlatonicSections
