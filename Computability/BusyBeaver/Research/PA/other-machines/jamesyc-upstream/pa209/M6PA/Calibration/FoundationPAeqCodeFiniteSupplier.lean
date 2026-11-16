module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTheory
public import M6PA.Calibration.FoundationPAeqCodeFormulaCalibration
public import M6PA.Calibration.FoundationPAAxiomCodeComplete
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Coding
@[expose] public section

/-! Genuine all-model numeric proof witnesses for the exact original finite26
axiom branch. Only fixed host-tagged axioms are quoted; arbitrary induction
formula codes are not standardized. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_sentence (param : V) (σ : ArithmeticSentence) :
    formulaCode param (⌜σ⌝ : V)=(⌜Presentation.formula σ⌝ : V) := by
  rw [Sentence.quote_def,formulaCode_quote,Sentence.quote_def]
  congr 1
  exact Presentation.formula_emb σ

theorem quoted_image_proof {σ : ArithmeticSentence}
    (h : Presentation.ordinaryPAeq.Proof (Presentation.formula σ)) :
    Proof Presentation.ordinaryPAeq (⌜h⌝ : V) (formulaCode 0 (⌜σ⌝ : V)) := by
  rw [formulaCode_sentence]
  exact proof_of_quote_proof h

def finiteImageProof (t : FoundationAxiomCode.FiniteTag) :
    Presentation.ordinaryPAeq.Proof (Presentation.formula t.sentence) :=
  match t with
  | .inl t => t.proof
  | .inr t => t.proof

theorem finiteTag_proof (t : FoundationAxiomCode.FiniteTag) :
    Proof Presentation.ordinaryPAeq (⌜finiteImageProof t⌝ : V)
      (formulaCode 0 (t.code : V)) := by
  simpa only [FoundationAxiomCode.FiniteTag.code,Sentence.quote_eq_encode] using
    quoted_image_proof (V:=V) (finiteImageProof t)

theorem finite_axiom_supplier {c : V} (hc : c∈PeanoMinus.Δ₁Class) :
    Provable Presentation.ordinaryPAeq (formulaCode 0 c) := by
  obtain ⟨t,rfl⟩:=(FoundationAxiomCode.peanoMinus_iff_tag c).mp hc
  exact ⟨⌜finiteImageProof t⌝,finiteTag_proof t⟩

theorem finite_axiom_derivation {c : V} (hc : c∈PeanoMinus.Δ₁Class) :
    ∃d : V, DerivationOf Presentation.ordinaryPAeq d {formulaCode 0 c} :=
  finite_axiom_supplier hc

#print axioms formulaCode_sentence
#print axioms quoted_image_proof
#print axioms finiteTag_proof
#print axioms finite_axiom_supplier
#print axioms finite_axiom_derivation
end M6.PA.FoundationPAeqCode

