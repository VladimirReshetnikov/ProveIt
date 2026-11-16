import Foundation.FirstOrder.Intuitionistic.Formula

/-! Quantifier-free intuitionistic formulas. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAQuantifierFree
open LO LO.FirstOrder

/-- Quantifier-freeness in the intuitionistic syntax, including implication. -/
def OpenI {L : Language} {ξ : Type} : ∀ {n : ℕ}, Semiformulaᵢ L ξ n → Prop
  | _, .falsum => True
  | _, .rel _ _ => True
  | _, .and a b => OpenI a ∧ OpenI b
  | _, .or a b => OpenI a ∧ OpenI b
  | _, .imp a b => OpenI a ∧ OpenI b
  | _, .all _ => False
  | _, .exs _ => False

end DiophantineConsistency.IPRAQuantifierFree
