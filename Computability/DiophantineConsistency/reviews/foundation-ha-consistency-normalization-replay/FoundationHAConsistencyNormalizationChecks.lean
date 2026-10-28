import DiophantineConsistency.FoundationHAConsistencyNormalization

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAConsistencyNormalizationChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HA FoundationPAHFSyntax FoundationZFCConsistencyNat
open FoundationHAConsistencyNormalization

example : sourceSentence = ∼rho := rfl
example : Hierarchy 𝚺 1 rho := rho_sigma_one
example : ordinaryConsistency = neg (FoundationHADeltaZero.ordinaryAux Fin.elim0 Empty.elim rho) := rfl

example : Proves (.imp ggConsistency ordinaryConsistency) := gg_to_ordinary
example : Proves (.imp ordinaryConsistency ggConsistency) := ordinary_to_gg
example (G : List SetTheory.PA.Formula) :
    Relative SetTheory.PA.Formula.Ax_s G (.and
      (.imp ggConsistency ordinaryConsistency) (.imp ordinaryConsistency ggConsistency)) :=
  equivalence_relative G

-- A nested closed source exercises the exact empty-environment syntax map.
example (p : Semiformulaᵢ ℒₒᵣ Empty 2) :
    sentence (∀⁰ (∃⁰ p)) = formulaAux Fin.elim0 Empty.elim (∀⁰ (∃⁰ p)) :=
  sentence_empty_env _

-- The positive ordinary predicate is not asserted decidable or recovered.
example : Proves (.and
    (.imp (neg (sentence rhoᴺ)) (neg ordinaryRefutation))
    (.imp (neg ordinaryRefutation) (neg (sentence rhoᴺ)))) :=
  negative_predicate_equivalence

#print axioms source_eq_neg_rho
#print axioms rho_sigma_one
#print axioms sentence_empty_env
#print axioms negative_predicate_equivalence
#print axioms equivalence
#print axioms gg_to_ordinary
#print axioms ordinary_to_gg
#print axioms equivalence_relative
end DiophantineConsistency.FoundationHAConsistencyNormalizationChecks
