import DiophantineConsistency.IPRAStandardTheory

/-! # Intuitionistic assembly of a consistency/nonhalting equivalence

This module supplies only the logical final step. In an application, `P` must
be the chosen PA-refutation sentence and `H` the specified machine-halting
sentence, both expressed in the language of standard iPRA. The two displayed
implications remain hypotheses: this file does not establish either for PA196
or any other particular machine.

It is enough to obtain `H → ¬¬P` rather than the stronger `H → P`.
In particular, the argument never uses double-negation elimination or an
unproved instance of Markov's principle. -/
set_option autoImplicit false
noncomputable section

namespace BusyBeaver.PA196.IPRAAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRAStandardTheory

/-- Given internal refutation-to-halt and halt-to-double-negated-refutation
    implications, standard iPRA derives the desired negative equivalence. -/
def consistency_iff_nonhalting
    (P H : Sentenceᵢ language)
    (refutation_implies_halt : standardTheory ⊢! P 🡒 H)
    (halt_implies_not_not_refutation : standardTheory ⊢! H 🡒 ∼∼P) :
    standardTheory ⊢! ∼P 🡘 ∼H := by
  apply Entailment.K_intro
  · exact Entailment.C_trans Entailment.dni (Entailment.contra halt_implies_not_not_refutation)
  · exact Entailment.contra refutation_implies_halt

#print axioms consistency_iff_nonhalting
end BusyBeaver.PA196.IPRAAssembly
