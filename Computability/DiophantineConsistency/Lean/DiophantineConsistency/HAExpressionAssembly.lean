import DiophantineConsistency.HACurrentAssembly2011
import DiophantineConsistency.ArithmeticCurrentSentence2011
/-! A generic, proof-producing endpoint for an arithmetic expression once its
all-model machine equivalence is given. It does not prove the bridge. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.HAExpressionAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
open FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Semantic interpretation of the exact source for any finite expression. -/
theorem classicalNoZero_iff {n : ℕ} (e : Expr (Fin n)) :
    (classicalNoZero e).Evalb (M := V) ![] ↔
      ∀ v : Fin n → V, e.splitNatural.1.evalSemiring v ≠ e.splitNatural.2.evalSemiring v := by
  unfold classicalNoZero
  simp only [Semiformula.eval_allClosure, Semiformula.eval_nrel]
  refine forall_congr' fun v => ?_
  change ¬ ((sourceTerm n _).val v Empty.elim = (sourceTerm n _).val v Empty.elim) ↔ _
  rw [ArithmeticCurrentSentence2011.val_sourceTerm, ArithmeticCurrentSentence2011.val_sourceTerm]
end Model

/-- Every model sees no zero exactly when the represented run never halts. -/
def PolynomialBridge {n : ℕ} (e : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (classicalNoZero e).Evalb (M := V) ![] ↔
      ¬∃ time : V, first (ArithmeticMachineRun215.run time) = 0

/-- An actual IΣ₁ proof, conditional only on the explicit all-model bridge. -/
theorem isigma1_equivalence {n : ℕ} (e : Expr (Fin n)) (hp : PolynomialBridge e) :
    𝗜𝚺₁ ⊢ classicalNoZero e 🡘 sourceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have h1 := hp M
  have h2 := sourceBridge M
  have h3 := ArithmeticCheckerMachine215.refutation_iff_blank_halts (V := M)
  have hiff : (classicalNoZero e).Evalb (M := M) ![] ↔ sourceSentence.Evalb (M := M) ![] :=
    h1.trans ((not_congr h3).symm.trans h2.symm)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    models_iff]
  exact ⟨hiff.1, hiff.2⟩

/-- An actual HA derivation for the expression's literal no-zero formula and
Foundation's ordinary consistency formula, under the all-model bridge. -/
theorem ha_equivalence {n : ℕ} (e : Expr (Fin n)) (hp : PolynomialBridge e) :
    ProofEquiv (ArithmeticExpression.noZeroSentence e)
      FoundationHAConsistencyNormalization.ordinaryConsistency := by
  have hpa : Peano ⊢ classicalNoZero e 🡘 sourceSentence :=
    Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) (isigma1_equivalence e hp)
  have ht := FoundationHAPeano.peano_provable hpa
  change Proves (.and (sentence (classicalNoZero e 🡒 sourceSentence)ᴺ)
    (sentence (sourceSentence 🡒 classicalNoZero e)ᴺ)) at ht
  have h : ProofEquiv (ArithmeticExpression.noZeroSentence e) ggConsistency :=
    ((noZero_to_source e).imp_trans (FoundationHACurrentTransfer.sentence_imp_elim ht.and_left)).and_intro
      ((FoundationHACurrentTransfer.sentence_imp_elim ht.and_right).imp_trans (source_to_noZero e))
  have hn := FoundationHAConsistencyNormalization.equivalence
  exact (h.and_left.imp_trans hn.and_left).and_intro (hn.and_right.imp_trans h.and_right)
end DiophantineConsistency.HAExpressionAssembly
