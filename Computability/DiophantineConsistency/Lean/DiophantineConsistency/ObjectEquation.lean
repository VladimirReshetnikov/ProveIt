import DiophantineConsistency.ObjectPolynomial
import DiophantineConsistency.ExplicitZFC

/-!
# The actual polynomial-unsolvability sentence for the closed equation

The formula quantifies over the model's own natural tuples, including
nonstandard ones. This supplies the polynomial-side target of the internal
ZFC obligation; it does not assert its equivalence to an internal consistency
sentence or convert the external Lean theorem into a ZFC derivation.
-/

namespace DiophantineConsistency.ObjectEquation

set_option maxRecDepth 16000

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

attribute [local irreducible] ExplicitZFC.expression

/-- A closed set-theory sentence, with the fixed equation's coefficients
supplied by its executable syntax. -/
def unsolvabilitySentence : Form := ObjectPolynomial.noZeroForm ExplicitZFC.expression

theorem sentence_unsolvabilitySentence : Sentence unsolvabilitySentence :=
  ObjectPolynomial.sentence_noZeroForm _

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem sat_unsolvabilitySentence_iff (H : ZFAxioms mem) :
    (∀ ee : Nat → V, Sat mem ee unsolvabilitySentence) ↔
      ObjectPolynomial.NoZeroRel H ExplicitZFC.expression :=
  ObjectPolynomial.sat_noZeroForm_iff H _

/-- Only this external implication is asserted: satisfaction on every
internal natural tuple in particular excludes all external numeral zeros. -/
theorem conZFC_of_sat (H : ZFAxioms mem)
    (h : ∀ ee : Nat → V, Sat mem ee unsolvabilitySentence) : ConZFC :=
  ExplicitZFC.noSyntaxZero_iff_conZFC.mp
    (ObjectPolynomial.no_external_zero_of_sat H ExplicitZFC.expression h)

end DiophantineConsistency.ObjectEquation
