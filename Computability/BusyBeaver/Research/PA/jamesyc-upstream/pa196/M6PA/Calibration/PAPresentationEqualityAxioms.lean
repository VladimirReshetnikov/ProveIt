module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationTrichotomy
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def equalityImageProof (p : ArithmeticSentence)
    (d : ND.Proof equalityContext (Rewriting.emb (formula p))) : ordinaryPAeq.Proof (formula p) := by
  have h := ND.parameterTheoryProof d (T := ordinaryPAeq)
    (fun q hq => ⟨q,equalityContext_is_PAeq q hq,rfl⟩)
  simpa only [Semiformula.univCl_coe_sentence] using h

def foundationEqReflProof : ordinaryPAeq.Proof (formula (Theory.Eq.refl ℒₒᵣ)) := by
  apply equalityImageProof
  have d : ND.Proof equalityContext reflexivity := equalityContextPremises.refl
  change ND.Proof equalityContext (Semiformula.rewAux Rew.emb (formula (Theory.Eq.refl ℒₒᵣ)))
  rw [←formula_emb]
  exact d

def foundationEqSymmProof : ordinaryPAeq.Proof (formula (Theory.Eq.symm ℒₒᵣ)) := by
  apply equalityImageProof
  have d : ND.Proof equalityContext symmetry := equalityContextPremises.symm
  change ND.Proof equalityContext (Semiformula.rewAux Rew.emb (formula (Theory.Eq.symm ℒₒᵣ)))
  rw [←formula_emb]
  exact d

def foundationEqTransProof : ordinaryPAeq.Proof (formula (Theory.Eq.trans ℒₒᵣ)) := by
  apply equalityImageProof
  have d : ND.Proof equalityContext transitivity := equalityContextPremises.trans
  change ND.Proof equalityContext (Semiformula.rewAux Rew.emb (formula (Theory.Eq.trans ℒₒᵣ)))
  rw [←formula_emb]
  exact d

#print axioms foundationEqReflProof
#print axioms foundationEqSymmProof
#print axioms foundationEqTransProof
end M6.PA.Presentation

