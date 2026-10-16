import GowersSzemeredi.Proofs15Walsh2

/-! Compatibility exports for arbitrary-coefficient Walsh invariance.
The unchanged sign-cube and Boolean-cube producers now live in
`Proofs15Walsh` and `Proofs15Walsh2`; the printed statements specialize them. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise ZMod
open Finset
namespace LeanProofs.GowersSzemeredi

alias parityCharacter_eq_prod_general := parityCharacter_eq_prod

alias corollary_15_2_of_general := corollary_15_2_holds

end LeanProofs.GowersSzemeredi
