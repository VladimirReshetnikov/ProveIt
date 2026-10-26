import DiophantineConsistency.FoundationHAClosure
import DiophantineConsistency.HANegativeStability

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAClosureChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAClosure

def sparse : Proposition ℒₒᵣ := “&0 + &7 = &3”
def nested : Proposition ℒₒᵣ := “∀ x, ∃ y, x + &7 < y + &0”

example : formula (Rew.fixitr 0 0 ▹ sparseᴺ) = formula sparseᴺ :=
  formula_fixitr 0 sparseᴺ
example : formula (Rew.fixitr 0 3 ▹ sparseᴺ) = formula sparseᴺ :=
  formula_fixitr 3 sparseᴺ
example : formula (Rew.fixitr 0 12 ▹ nestedᴺ) = formula nestedᴺ :=
  formula_fixitr 12 nestedᴺ

example : sentence (Semiformula.univCl sparse)ᴺ =
    SetTheory.PA.Formula.closeN sparse.fvSup (formula sparseᴺ) := sentence_univCl sparse
example : sentence (Semiformula.univCl nested)ᴺ =
    SetTheory.PA.Formula.closeN nested.fvSup (formula nestedᴺ) := sentence_univCl nested

theorem closed_reflexivity : HA.Proves
    (sentence (Semiformula.univCl (“&7 = &7” : Proposition ℒₒᵣ))ᴺ) := by
  apply proves_univCl
  exact (HA.Proves.of_derives (HA.Derives.doubleNeg_intro [] _)).mp
    (HA.Relative.eq_refl (.var 7))

#print axioms doubleNegation_allClosure
#print axioms formula_allClosure
#print axioms formula_fixitr
#print axioms sentence_univCl
#print axioms proves_univCl
#print axioms closed_reflexivity
end DiophantineConsistency.FoundationHAClosureChecks
