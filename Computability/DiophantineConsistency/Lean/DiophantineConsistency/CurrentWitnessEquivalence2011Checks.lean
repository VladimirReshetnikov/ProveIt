import DiophantineConsistency.CurrentWitnessEquivalence2011

namespace DiophantineConsistency.CurrentWitnessEquivalence2011Checks

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency
open CurrentWitnessEquivalence2011 CurrentPolynomialWindow2011 CurrentCarrierArithmetic2011

set_option Elab.async false
set_option maxRecDepth 10000

example (href : BProv ZFCax_s [] Form.fBot) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧ MvPolynomial.eval v polynomial=0 :=
  zfc_refutation_positive_zero href

-- The direct reverse map also applies to the literal evaluator at the
-- complete current ports, rather than a substituted polynomial predicate.
example (href : BProv ZFCax_s [] Form.fBot) :
    ∃ v : Fin 14 → ℤ, (∀ j,0<v j) ∧
      Carrier65.value CurrentWindowCarry2011.ports v=0 := by
  obtain ⟨v,hv,hz⟩ := zfc_refutation_positive_zero href
  exact ⟨v,hv,by simpa only [polynomial,Carrier65.eval_polynomial] using hz⟩

example (v : Fin 14 → ℤ) (hv : ∀ j,0<v j)
    (hz : Carrier65.value CurrentWindowCarry2011.ports v=0) :
    BProv ZFCax_s [] Form.fBot := by
  apply positive_zero_zfc_refutation
  exact ⟨v,hv,by simpa only [polynomial,Carrier65.eval_polynomial] using hz⟩

example : (¬ PositiveZero polynomial) ↔ DiophantineConsistency.ConZFC :=
  no_positive_zero_iff_conZFC

-- This logical step itself requires neither decidability nor excluded middle.
example (P Q : Prop) (hpq : P → Q) (hqp : Q → P) : (¬ P) ↔ ¬ Q :=
  ⟨fun hn hq => hn (hqp hq),fun hn hp => hn (hpq hp)⟩

example : (∀ v : Fin 14 → ℤ, (∀ j,0<v j) → MvPolynomial.eval v polynomial≠0) ↔
    DiophantineConsistency.ConZFC := by
  constructor
  · intro hn href
    obtain ⟨v,hv,hz⟩ := zfc_refutation_positive_zero href
    exact hn v hv hz
  · intro hc v hv hz
    exact hc (positive_zero_zfc_refutation ⟨v,hv,hz⟩)

#print axioms blank_halts_positive_zero
#print axioms zfc_refutation_positive_zero
#print axioms positive_zero_zfc_refutation
#print axioms positive_zero_iff_zfc_refutation
#print axioms no_positive_zero_iff_conZFC

end DiophantineConsistency.CurrentWitnessEquivalence2011Checks
