import DiophantineConsistency.PRAWitnessDerivation
import DiophantineConsistency.PRAStrictConReverse
import DiophantineConsistency.PRACurrentStrictCon
/-! # PRA proves: the current equation has no positive zero ↔ ZFC is consistent

`PRAStrictConReverse.comparison_if_bound` reduced the literal equivalence
between the maintained equation's unsolvability and Foundation's actual ZFC
consistency sentence to one input, the bound certificate for the refutation
sentence `rho = ZFC ⊢ ⊥`: in every candidate-PRA model, a true `rho` has a
witness for its bounded form `bnd rho`. `PRAWitnessDerivation.wb_provable_falsum`
gives that witness, through the witness-bound calculus for every layer of
`rho` (syntax, recursions, the ZFC axiom recognizer, derivations), so
`boundCertificate_rho` holds and the equivalence is a PRA theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.PRACurrentConsistencyEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus StrictSigmaOneInduction

/-- **The bound certificate for `ZFC ⊢ ⊥`.** -/
theorem boundCertificate_rho :
    PRAStrictConReverse.BoundCertificate FoundationHAConsistencyNormalization.rho := by
  unfold PRAStrictConReverse.BoundCertificate
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  have hwb : WB M FoundationHAConsistencyNormalization.rho :=
    PRAWitnessDerivation.wb_provable_falsum (M := M)
  simp only [models_iff]
  rw [PRAWitnessTransfer.eval_lMap_std]
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_ex]
  intro h
  obtain ⟨w, hw⟩ := exists_bound hwb ![] h
  refine ⟨w, ?_⟩
  have hv : (Fin.snoc (![] : Fin 0 → M) w : Fin 1 → M) = w :> ![] :=
    funext fun i => Fin.cases rfl (fun j => j.elim0) i
  rw [hv] at hw
  exact hw

open FoundationHANoZero FoundationHAConsistencyNormalization ObjectCurrentEquation2011 in
/-- **PRA proves that the maintained equation has no positive zero iff ZFC is
consistent**, for Foundation's actual ZFC consistency sentence. -/
theorem pra_current_iff_consistency : PRA ⊢
    (Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘
      Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence) := by
  have h : 𝗜𝚺₁ ⊢
      (PRANoZeroUnary.noZero 14
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2)) 🡘 ∼rho) := by
    simpa only [PRANoZeroUnary.noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
      source_eq_neg_rho] using HACurrentEquation2011.isigma1_proves_current_iff_consistency
  have hc := PRAStrictConReverse.comparison_if_bound 14
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))
    rho rho_sigma_one h boundCertificate_rho
  simpa only [PRANoZeroUnary.noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
    source_eq_neg_rho] using hc

end DiophantineConsistency.PRACurrentConsistencyEndpoint
