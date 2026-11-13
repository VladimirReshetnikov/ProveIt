module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqCanonicalMatrixSupply
public import PA196.Arithmetic.Transport.NumericPAeqGuardedAllsFinish
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqCanonicalMatrix NumericPAeqGuardedAlls
open RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem induction_axiom_requested_certificate {q:V} (hq:FoundationPAeqCode.targetInductionR q)
    (f native lo z:V)
    (hc:FormulaCovered 0 native lo z (formulaSyntax (NumericPAeqFormula.parameters 0 f) q)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (formulaSyntax (NumericPAeqFormula.parameters 0 f) q)+1 := by
  rcases hq with ⟨m,_,b,_,rfl,hb,hs,hbv,p,_,hp,he⟩
  have hbm :IsSemiformula Presentation.language m b :=by rw [←hbv];exact hb.isSemiformula
  have hs0 :=freeSupported_zero_of_shift_fixed hb hs
  have hsource :IsSemiformula Presentation.language ((0:V)+m) b :=by simpa using hbm
  have hall :MatrixSupply 0 (qqAlls b m) :=
    matrixSupply_alls hsource hs0 (by simpa using matrix_supply hbm hs hp he)
  exact closed_matrix_certificate hsource.qqAlls (freeSupported_alls hs0 m) hall f native lo z hc
#print axioms induction_axiom_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation

