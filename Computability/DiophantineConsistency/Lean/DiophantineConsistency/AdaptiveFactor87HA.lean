import DiophantineConsistency.FoundationHANoZero
import DiophantineConsistency.FoundationHAPeano
import DiophantineConsistency.ArithmeticSignedPairs
import DiophantineConsistency.AdaptiveFirstRootFactor87Literal
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveFactor87HA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA FoundationHANoZero ArithmeticSignedPairs AdaptiveFirstRootFactor87Literal

def source : Sentence ℒₒᵣ := classicalNoZero AdaptiveEquationSyntax2011.naturalExpression
def reduced : Sentence ℒₒᵣ := classicalNoZero naturalExpression87

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

theorem val_reflectTerm {n : ℕ} (v : ℕ → Semiterm ℒₒᵣ Empty n) (b : Fin n → V) (t : Term) :
    (reflectTerm v t).val b Empty.elim =
      Term.eval (ArithmeticExpression.semiringStructure V) (fun i => (v i).val b Empty.elim) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | succ t ih => exact congrArg (· + 1) ih
  | add s t ihs iht => exact congrArg₂ (· + ·) ihs iht
  | mul s t ihs iht => exact congrArg₂ (· * ·) ihs iht

theorem val_sourceTerm {n : ℕ} (e : NatExpr (Fin n)) (b : Fin n → V) :
    (sourceTerm n (ArithmeticExpression.term Fin.val e)).val b Empty.elim = e.evalSemiring b := by
  unfold sourceTerm
  rw [val_reflectTerm, ArithmeticExpression.eval_term]
  congr 1
  funext i
  simp [slot, i.isLt]

theorem modelNoZero {n : ℕ} (e : Expr (Fin n)) :
    (classicalNoZero e).Evalb (M := V) ![] ↔
      ∀ v : Fin n → V, ¬ AdaptiveEquationSyntax2011.InternalZero e v := by
  unfold classicalNoZero
  simp only [Semiformula.eval_allClosure, Semiformula.eval_nrel]
  refine forall_congr' fun b => ?_
  change ¬ ((sourceTerm n _).val b Empty.elim = (sourceTerm n _).val b Empty.elim) ↔ _
  rw [val_sourceTerm, val_sourceTerm]
  rfl

theorem modelEquivalence : source.Evalb (M := V) ![] ↔ reduced.Evalb (M := V) ![] := by
  rw [source, reduced, modelNoZero, modelNoZero]
  exact forall_congr' fun v => not_congr (current_natural_zero_iff v)

theorem isigma0_proves_equivalence : 𝗜𝚺₀ ⊢ source 🡘 reduced := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₀ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := hM
  have h := modelEquivalence (V := M)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    models_iff]
  exact ⟨h.1,h.2⟩
/-- PA proves the two exact no-zero sentences equivalent. -/
theorem peano_proves_equivalence : Peano ⊢ source 🡘 reduced :=
  Entailment.weakening (inferInstance : 𝗜𝚺₀ ⪯ Peano)
    isigma0_proves_equivalence

private theorem sentence_imp_elim {φ ψ : ArithmeticSentence}
    (h : HA.Proves (FoundationPAHFSyntax.sentence (φ 🡒 ψ)ᴺ)) :
    HA.Proves (.imp (FoundationPAHFSyntax.sentence φᴺ) (FoundationPAHFSyntax.sentence ψᴺ)) := by
  simp only [FoundationPAHFSyntax.sentence, Semiformula.emb_doubleNegation,
    LogicalConnective.HomClass.map_imply] at h ⊢
  exact FoundationHAInduction.translated_imp_elim (Rewriting.emb φ) (Rewriting.emb ψ) h

/-- An actual HA derivation of the equivalence of the two arithmetic no-zero
sentences; this does not assert their equivalence to ZFC consistency. -/
theorem ha_proves_equivalence : HA.Proves (.and
    (.imp (ArithmeticExpression.noZeroSentence AdaptiveEquationSyntax2011.naturalExpression)
      (ArithmeticExpression.noZeroSentence naturalExpression87))
    (.imp (ArithmeticExpression.noZeroSentence naturalExpression87)
      (ArithmeticExpression.noZeroSentence AdaptiveEquationSyntax2011.naturalExpression))) := by
  have hp := FoundationHAPeano.peano_provable peano_proves_equivalence
  change HA.Proves (.and (FoundationPAHFSyntax.sentence (source 🡒 reduced)ᴺ)
    (FoundationPAHFSyntax.sentence (reduced 🡒 source)ᴺ)) at hp
  exact ((noZero_to_source _).imp_trans (sentence_imp_elim hp.and_left)).imp_trans (source_to_noZero _) |>.and_intro
    (((noZero_to_source _).imp_trans (sentence_imp_elim hp.and_right)).imp_trans (source_to_noZero _))
end DiophantineConsistency.AdaptiveFactor87HA
