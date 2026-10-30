import DiophantineConsistency.HAExpressionAssembly

/-! A one-sided HA proof-producing endpoint from an all-model implication. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.HAExpressionImplication
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
open FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor

/-- Every model sees no-zero imply represented-machine nonhalting. -/
def PolynomialImplication {n : ℕ} (e : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (classicalNoZero e).Evalb (M := V) ![] →
      ¬∃ time : V, first (ArithmeticMachineRun215.run time) = 0

/-- An actual IΣ₁ proof, conditional on the all-model implication. -/
theorem isigma1_implication {n : ℕ} (e : Expr (Fin n)) (hp : PolynomialImplication e) :
    𝗜𝚺₁ ⊢ classicalNoZero e 🡒 sourceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have h2 := sourceBridge M
  have h3 := ArithmeticCheckerMachine215.refutation_iff_blank_halts (V := M)
  simp only [Semantics.Imp.models_imply,models_iff]
  intro hn
  exact h2.mpr ((not_congr h3).mpr (hp M hn))

/-- An actual HA proof of the one-sided implication, not an equivalence. -/
theorem ha_implication {n : ℕ} (e : Expr (Fin n)) (hp : PolynomialImplication e) :
    Proves (.imp (ArithmeticExpression.noZeroSentence e)
      FoundationHAConsistencyNormalization.ordinaryConsistency) := by
  have hpa : Peano ⊢ classicalNoZero e 🡒 sourceSentence :=
    Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) (isigma1_implication e hp)
  have ht := FoundationHAPeano.peano_provable hpa
  have h := (noZero_to_source e).imp_trans (FoundationHACurrentTransfer.sentence_imp_elim ht)
  exact h.imp_trans FoundationHAConsistencyNormalization.equivalence.and_left
end DiophantineConsistency.HAExpressionImplication
