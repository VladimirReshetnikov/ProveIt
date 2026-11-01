import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

/-! Native intuitionistic reading of Foundation's classical NNF syntax. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeFormula
open LO LO.FirstOrder
open scoped LO.FirstOrder
variable {L : Language} {ξ : Type*}

/-- Read classical NNF directly: a negative atom becomes an intuitionistic
negation, while disjunction and existential remain native connectives. -/
def native : {n : ℕ} → Semiformula L ξ n → Semiformulaᵢ L ξ n
  | _, .verum => ⊤
  | _, .falsum => ⊥
  | _, .rel r v => .rel r v
  | _, .nrel r v => ∼(.rel r v)
  | _, .and p q => native p ⋏ native q
  | _, .or p q => native p ⋎ native q
  | _, .all p => ∀⁰ native p
  | _, .exs p => ∃⁰ native p
end DiophantineConsistency.IPRANativeFormula
