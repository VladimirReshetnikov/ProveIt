import DiophantineConsistency.PRAFiniteCodeSyntax
import Foundation.Syntax.Predicate.Term

/-! The equality-only language of the Foundation iPRA reference theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualityOnlyReference
open LO LO.FirstOrder PRAFiniteFunctionCodes

inductive EqualityRel : ℕ → Type
  | eq : EqualityRel 2
  deriving DecidableEq

def language : Language where
  Func := Code
  Rel := EqualityRel

abbrev TermN (n : ℕ) := Semiterm language Empty n

end DiophantineConsistency.IPRAEqualityOnlyReference
