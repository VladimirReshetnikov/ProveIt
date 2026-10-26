import DiophantineConsistency.ArithmeticCurrentEquation2011
import DiophantineConsistency.HANegativeStability

/-! # An actual HA stability proof for the exact current equation sentence

This supplies proof existence inside the genuine intuitionistic calculus.
It uses no arithmetic axioms. It is the stability of the no-zero sentence,
not the as-yet-open consistency equivalence or a PA-to-HA translation.
-/

set_option Elab.async false
namespace DiophantineConsistency.HAEquationStability2011
open SetTheory.PA
open ArithmeticCurrentEquation2011

theorem negative_unsolvabilitySentence : HA.Negative unsolvabilitySentence :=
  (HA.Negative.neg (ArithmeticExpression.equation
    ObjectCurrentEquation2011.naturalExpression Fin.val)).closeN 14

/-- The proof is purely logical, with an empty assumption and axiom list. -/
theorem derives_stability : HA.Derives []
    (.imp (HA.doubleNeg unsolvabilitySentence) unsolvabilitySentence) :=
  negative_unsolvabilitySentence.stable []

/-- HA proves double-negation stability of the exact14-variable sentence. -/
theorem proves_stability : HA.Proves
    (.imp (HA.doubleNeg unsolvabilitySentence) unsolvabilitySentence) :=
  HA.Proves.of_derives derives_stability

theorem of_proves_doubleNeg (h : HA.Proves (HA.doubleNeg unsolvabilitySentence)) :
    HA.Proves unsolvabilitySentence :=
  HA.Proves.mp proves_stability h

end DiophantineConsistency.HAEquationStability2011
