module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeSubstitution
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Iteration
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_alls (param m : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (qqAlls p m)=qqAlls (formulaCode param p) m := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [qqAlls_succ,formulaCode_all _ _ (isUFormula_qqAlls.mpr hp),ih,qqAlls_succ]

theorem termVector_one {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termVector (1:V) (t∷0)=termCode t∷0 := by
  simpa using termVector_cons (k:=0) (ts:=0) ht (by simp)

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaCode_substs1 (param : V) {n p t : V}
    (hp : IsSemiformula ℒₒᵣ 1 p) (ht : IsSemiterm ℒₒᵣ n t) :
    formulaCode param (substs1 ℒₒᵣ t p)=
      substs1 Presentation.language (termCode t) (formulaCode param p) := by
  simp only [substs1]
  rw [formulaCode_subst param hp (show IsSemitermVec ℒₒᵣ 1 n (t∷0) from by simp [ht]),
    termVector_one ht.isUTerm]

theorem formulaCode_free (param : V) {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaCode param (Bootstrapping.free ℒₒᵣ p)=
      Bootstrapping.free Presentation.language (formulaCode param p) := by
  simp only [Bootstrapping.free]
  rw [formulaCode_substs1 param hp.shift (show IsSemiterm ℒₒᵣ 0 (qqFvar 0) from by simp),
    termCode_fvar,formulaCode_shift param hp.isUFormula]

#print axioms formulaCode_alls
#print axioms termVector_one
#print axioms formulaCode_substs1
#print axioms formulaCode_free
end M6.PA.FoundationPAeqCode

