module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationInductionTransport
public import M6PA.Calibration.PAPresentationParameterClosure
@[expose] public section

/-! Uniform actual ordinary-PAeq proof data for the exact translated
Foundation induction schema, including universal closure of all parameters.
The seventeen fixed PA-minus axiom images remain a separate obligation. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def additiveInductionProof (p : Semiproposition language 1) :
    ordinaryPAeq.Proof (additiveInductionFormula p).univCl :=
  ND.parameterTheoryProof (inductionTemplate p)
    (fun q hq => ⟨q,inductionContext_is_PAeq p q hq,rfl⟩)

def foundationInductionImageProof (p : ArithmeticSemiproposition 1) :
    ordinaryPAeq.Proof (formula (Arithmetic.succInd p)).univCl := by
  rw [formula_succInd]
  exact additiveInductionProof (formula p)

theorem paeq_proves_induction_image (p : ArithmeticSemiproposition 1) :
    ordinaryPAeq ⊢ (formula (Arithmetic.succInd p)).univCl :=
  ⟨foundationInductionImageProof p⟩

#print axioms additiveInductionProof
#print axioms foundationInductionImageProof
#print axioms paeq_proves_induction_image
end M6.PA.Presentation
