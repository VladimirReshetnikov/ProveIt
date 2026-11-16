module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShapeBase
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateTemplate RelationalPredicateTemplate.Ordinal
open NumericPAeqTerm (domainCode zeroCode successorCode)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem step_value {P f:V} (hP:IsSemiformula L 1 P) (hf:IsSemitermVec L (len f) 0 f):
    formulaValue (inductionStep hole) P 0 f=stepCode P := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by simpa using bindEnvironments_valid h0
  have hi1 : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 (fun i=>Fin.elim0 i)
  have h2 : EnvironmentsValid (2:V) 2 (bindBound (bindBound 0)) (bindFree (bindFree f)) := by
    convert bindEnvironments_valid h1 using 1 <;> norm_num
  have hi2 : IdentityBound 2 (bindBound (bindBound (0:V))) := identityBound_bind (s:=1) (by simpa using h1.1) hi1
  change qqAll (qqAll (formulaValue
    ((Ordinal.domain (.bvar 1 : Term 2) ⋏ (Ordinal.domain (.bvar 0 : Term 2) ⋏ (successor (.bvar 1 : Term 2) (.bvar 0) ⋏
      (.rel .predicate ![.bvar 1])))) 🡒 (.rel .predicate ![.bvar 0]))
      P (bindBound (bindBound 0)) (bindFree (bindFree f))))=_
  rw [closed_imp_value _ _ hP (by simpa using h2) (by decide)]
  change qqAll (qqAll (imp L (qqAnd (formulaValue (Ordinal.domain (.bvar 1 : Term 2)) P _ _)
    (qqAnd (formulaValue (Ordinal.domain (.bvar 0 : Term 2)) P _ _)
      (qqAnd (formulaValue (successor (.bvar 1 : Term 2) (.bvar 0)) P _ _)
        (formulaValue (.rel .predicate ![.bvar (1:Fin 2)]) P _ _))))
      (formulaValue (.rel .predicate ![.bvar (0:Fin 2)]) P _ _)))=_
  rw [domain_two_value 1 h2 hi2,domain_two_value 0 h2 hi2,successor_step_value h2 hi2,
    hole_at_value 1 hi2,hole_at_value 0 hi2]
  simp only [Fin.val_one,Fin.val_zero,Nat.cast_one,Nat.cast_zero]
  rfl


#print axioms step_value
end PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape

