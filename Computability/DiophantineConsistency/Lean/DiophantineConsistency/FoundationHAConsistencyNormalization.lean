import DiophantineConsistency.FoundationHASigmaOneGG
import DiophantineConsistency.FoundationHACurrentTransfer
import DiophantineConsistency.FoundationZFCConsistencyNat

/-! Actual HA normalization of the fixed Foundation consistency sentence.
The ordinary target negates the actual positive provability predicate.
It is not ordinary interpretation of NNF negation and is not a comparison
with an independently encoded checker or the current equation. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAConsistencyNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HA FoundationPAHFSyntax FoundationHADeltaZero
open FoundationHADeltaZeroGG FoundationHASigmaOneGG
open FoundationZFCConsistencyNat

/-- Exactly the positive refutation predicate underlying the retained source. -/
noncomputable def rho : ArithmeticSentence :=
  provabilityPred (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)
    (⊥ : SetTheorySentence)

theorem source_eq_neg_rho : sourceSentence = ∼rho := rfl

/-- Actual syntactic Σ1 evidence, retaining the source theory/coding instance. -/
theorem rho_sigma_one : Hierarchy 𝚺 1 rho := by
  simpa only [rho, provabilityPred'_val] using
    (provabilityPred' (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)
      (⊥ : SetTheorySentence)).sigma_prop

/-- The canonical embedding of a closed intuitionistic source formula agrees
with the direct interpretation under both empty source environments. -/
theorem sentence_empty_env (φ : Sentenceᵢ ℒₒᵣ) :
    sentence φ = formulaAux Fin.elim0 Empty.elim φ := by
  unfold sentence formula
  change formulaAux _ _ (Rew.emb ▹ φ) = _
  rw [formulaAux_rew]
  congr 1
  · funext i
    exact Fin.elim0 i
  · funext x
    exact Empty.elim x

noncomputable def ordinaryRefutation : SetTheory.PA.Formula :=
  ordinaryAux Fin.elim0 Empty.elim rho

noncomputable def ordinaryConsistency : SetTheory.PA.Formula := neg ordinaryRefutation

/-- No positive witness is extracted: only the negations are identified. -/
theorem negative_predicate_equivalence :
    ProofEquiv (neg (sentence rhoᴺ)) ordinaryConsistency := by
  rw [sentence_empty_env]
  exact neg_of_doubleNeg_equiv (sigma_one_doubleNeg rho_sigma_one Fin.elim0 Empty.elim)

/-- Unconditional genuine HA proof for this fixed consistency sentence. -/
theorem equivalence : ProofEquiv ggConsistency ordinaryConsistency := by
  have hn := FoundationHACurrentTransfer.translated_neg rho
  have hp := negative_predicate_equivalence
  have hf : ggConsistency = sentence (∼rho)ᴺ := by
    unfold ggConsistency
    rw [source_eq_neg_rho]
  rw [hf]
  exact (hn.and_right.imp_trans hp.and_left).and_intro
    (hp.and_right.imp_trans hn.and_left)

theorem gg_to_ordinary : Proves (.imp ggConsistency ordinaryConsistency) := equivalence.and_left

theorem ordinary_to_gg : Proves (.imp ordinaryConsistency ggConsistency) := equivalence.and_right

theorem equivalence_relative (G : List SetTheory.PA.Formula) :
    Relative SetTheory.PA.Formula.Ax_s G (.and
      (.imp ggConsistency ordinaryConsistency) (.imp ordinaryConsistency ggConsistency)) :=
  equivalence.weaken (by simp)

end DiophantineConsistency.FoundationHAConsistencyNormalization
