import DiophantineConsistency.FoundationHATheoryTransfer
import DiophantineConsistency.FoundationHAInduction
import DiophantineConsistency.FoundationHAOrderMultiplicative
import DiophantineConsistency.FoundationHAOrderIrreflexive
import DiophantineConsistency.FoundationHAOrderTrichotomy

/-! # Actual full Peano arithmetic proof transfer into conventional HA

Every source equality, arithmetic and unrestricted induction axiom has its
literal GG image proved in HA. The proof composition therefore has no
remaining axiom-image premise. Its conclusion is the translated sentence;
identifying a particular target with that image is separate work.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAPeano
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax

theorem peano_minus_axiom {σ : ArithmeticSentence} (h : PeanoMinus σ) :
    HA.Proves (sentence σᴺ) := by
  cases h with
  | equal _ h => exact FoundationHAEquality.equality_axiom h
  | addZero => exact FoundationHAArithmetic.addZero
  | addAssoc => exact FoundationHAArithmetic.addAssoc
  | addComm => exact FoundationHAArithmetic.addComm
  | addEqOfLt => exact FoundationHAOrderAdditive.addEqOfLt
  | zeroLe => exact FoundationHAOrderBase.zeroLe
  | zeroLtOne => exact FoundationHAOrderBase.zeroLtOne
  | oneLeOfZeroLt => exact FoundationHAOrderWitnesses.oneLeOfZeroLt
  | addLtAdd => exact FoundationHAOrderAdditive.addLtAdd
  | mulZero => exact FoundationHAArithmetic.mulZero
  | mulOne => exact FoundationHAArithmetic.mulOne
  | mulAssoc => exact FoundationHAArithmetic.mulAssoc
  | mulComm => exact FoundationHAArithmetic.mulComm
  | mulLtMul => exact FoundationHAOrderMultiplicative.mulLtMul
  | distr => exact FoundationHAArithmetic.distr
  | ltIrrefl => exact FoundationHAOrderIrreflexive.ltIrrefl
  | ltTrans => exact FoundationHAOrderWitnesses.ltTrans
  | ltTri => exact FoundationHAOrderTrichotomy.ltTri

theorem peano_axiom {σ : ArithmeticSentence} (h : σ ∈ Peano) :
    HA.Proves (sentence σᴺ) := by
  rcases h with h | h
  · exact peano_minus_axiom h
  · exact FoundationHAInduction.induction_axiom h

/-- Every actual classical Foundation PA proof yields an actual HA proof
of its literal existing GG image, without any image-provability premise. -/
theorem peano_provable {σ : ArithmeticSentence} (h : Peano ⊢ σ) :
    HA.Proves (sentence σᴺ) :=
  FoundationHATheoryTransfer.classical_theory h (fun _ hτ => peano_axiom hτ)

theorem subtheory_provable {T : ArithmeticTheory} {σ : ArithmeticSentence}
    (hT : T ⊆ Peano) (h : T ⊢ σ) : HA.Proves (sentence σᴺ) :=
  FoundationHATheoryTransfer.classical_theory h (fun _ hτ => peano_axiom (hT hτ))

theorem iSigma_provable {k : Nat} {σ : ArithmeticSentence} (h : ISigma k ⊢ σ) :
    HA.Proves (sentence σᴺ) :=
  peano_provable (Entailment.weakening (inferInstance : ISigma k ⪯ Peano) h)

end DiophantineConsistency.FoundationHAPeano
