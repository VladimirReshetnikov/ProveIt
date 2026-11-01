import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
import DiophantineConsistency.FoundationPAHFSyntax
import DiophantineConsistency.HAMultiplicativeArithmetic
import DiophantineConsistency.HANegativeStability

/-! # Eight actual Foundation arithmetic axioms proved in conventional HA

These are the literal Goedel--Gentzen translations of the eight universal
equation axioms in Foundation's existing `PeanoMinus`. HA arithmetic proves
the equality body; constructive double-negation introduction and universal
closure give the exact translated sentence. No arithmetic-image hypothesis,
model semantics, or new negative-translation algorithm is used.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax
local notation "PF" => SetTheory.PA.Formula

private theorem dni {a : PF} (h : HA.Proves a) : HA.Proves (HA.doubleNeg a) :=
  (HA.Proves.of_derives (HA.Derives.doubleNeg_intro [] a)).mp h

theorem addZero : HA.Proves (sentence PeanoMinus.Axiom.addZeroᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 1 (HA.doubleNeg (.eq (.add (.var 0) .zero) (.var 0))))
  exact HA.Arithmetic.reclose 1 (dni (HA.Arithmetic.add_zero (.var 0)))

theorem addAssoc : HA.Proves (sentence PeanoMinus.Axiom.addAssocᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 3 (HA.doubleNeg (.eq
    (.add (.add (.var 2) (.var 1)) (.var 0))
    (.add (.var 2) (.add (.var 1) (.var 0))))))
  exact HA.Arithmetic.reclose 3 (dni (HA.Arithmetic.add_assoc (.var 2) (.var 1) (.var 0)))

theorem addComm : HA.Proves (sentence PeanoMinus.Axiom.addCommᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 2 (HA.doubleNeg (.eq
    (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1)))))
  exact HA.Arithmetic.reclose 2 (dni (HA.Arithmetic.add_comm (.var 1) (.var 0)))

theorem mulZero : HA.Proves (sentence PeanoMinus.Axiom.mulZeroᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 1 (HA.doubleNeg (.eq (.mul (.var 0) .zero) .zero)))
  exact HA.Arithmetic.reclose 1 (dni (HA.Arithmetic.mul_zero (.var 0)))

theorem mulOne : HA.Proves (sentence PeanoMinus.Axiom.mulOneᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 1 (HA.doubleNeg (.eq (.mul (.var 0) (.succ .zero)) (.var 0))))
  exact HA.Arithmetic.reclose 1 (dni (HA.Arithmetic.mul_one (.var 0)))

theorem mulAssoc : HA.Proves (sentence PeanoMinus.Axiom.mulAssocᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 3 (HA.doubleNeg (.eq
    (.mul (.mul (.var 2) (.var 1)) (.var 0))
    (.mul (.var 2) (.mul (.var 1) (.var 0))))))
  exact HA.Arithmetic.reclose 3 (dni (HA.Arithmetic.mul_assoc (.var 2) (.var 1) (.var 0)))

theorem mulComm : HA.Proves (sentence PeanoMinus.Axiom.mulCommᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 2 (HA.doubleNeg (.eq
    (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))))
  exact HA.Arithmetic.reclose 2 (dni (HA.Arithmetic.mul_comm (.var 1) (.var 0)))

theorem distr : HA.Proves (sentence PeanoMinus.Axiom.distrᴺ) := by
  change HA.Proves (SetTheory.PA.Formula.closeN 3 (HA.doubleNeg (.eq
    (.mul (.var 2) (.add (.var 1) (.var 0)))
    (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 0))))))
  exact HA.Arithmetic.reclose 3 (dni (HA.Arithmetic.mul_add (.var 2) (.var 1) (.var 0)))

/-- A concrete source-axiom list, not a supplied predicate asserting HA provability. -/
def semiringAxioms : List ArithmeticSentence :=
  [PeanoMinus.Axiom.addZero, PeanoMinus.Axiom.addAssoc, PeanoMinus.Axiom.addComm,
   PeanoMinus.Axiom.mulZero, PeanoMinus.Axiom.mulOne, PeanoMinus.Axiom.mulAssoc,
   PeanoMinus.Axiom.mulComm, PeanoMinus.Axiom.distr]

theorem semiringAxioms_length : semiringAxioms.length = 8 := rfl

theorem semiringAxioms_subset {σ : ArithmeticSentence} (h : σ ∈ semiringAxioms) :
    PeanoMinus σ := by
  simp only [semiringAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst σ
  · exact PeanoMinus.addZero
  · exact PeanoMinus.addAssoc
  · exact PeanoMinus.addComm
  · exact PeanoMinus.mulZero
  · exact PeanoMinus.mulOne
  · exact PeanoMinus.mulAssoc
  · exact PeanoMinus.mulComm
  · exact PeanoMinus.distr

/-- Every member of that exact eight-axiom list has its actual GG image proved in HA. -/
theorem semiring_axiom {σ : ArithmeticSentence} (h : σ ∈ semiringAxioms) :
    HA.Proves (sentence σᴺ) := by
  simp only [semiringAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst σ
  · exact addZero
  · exact addAssoc
  · exact addComm
  · exact mulZero
  · exact mulOne
  · exact mulAssoc
  · exact mulComm
  · exact distr

end DiophantineConsistency.FoundationHAArithmetic
