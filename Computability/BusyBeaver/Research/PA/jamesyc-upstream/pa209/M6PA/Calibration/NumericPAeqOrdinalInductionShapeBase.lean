module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqOrdinalInductionShapePrimitives
@[expose] public section
namespace M6.PA.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateTemplate RelationalPredicateTemplate.Ordinal
open NumericPAeqTerm (domainCode zeroCode successorCode)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def baseCode (P:V):V := qqAll (imp L (qqAnd (domainCode (qqBvar 0)) (zeroCode (qqBvar 0))) P)
noncomputable def stepCode (P:V):V := qqAll (qqAll (imp L
  (qqAnd (domainCode (qqBvar 1)) (qqAnd (domainCode (qqBvar 0))
    (qqAnd (successorCode (qqBvar 1) (qqBvar 0)) (substs1 L (qqBvar 1) P))))
  (substs1 L (qqBvar 0) P)))
noncomputable def conclusionCode (P:V):V := qqAll (imp L (domainCode (qqBvar 0)) P)
noncomputable def inductionCode (P:V):V := imp L (qqAnd (baseCode P) (stepCode P)) (conclusionCode P)

theorem base_value {P f:V} (hP:IsSemiformula L 1 P) (hf:IsSemitermVec L (len f) 0 f):
    formulaValue (inductionBase hole) P 0 f=baseCode P := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by simpa using bindEnvironments_valid h0
  have hi : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 (fun i=>Fin.elim0 i)
  change qqAll (formulaValue ((Ordinal.domain (.bvar 0) ⋏ zero (.bvar 0)) 🡒 hole) P (bindBound 0) (bindFree f))=_
  rw [closed_imp_value _ _ hP (by simpa using h1) (by decide)]
  change qqAll (imp L (qqAnd (formulaValue (Ordinal.domain (.bvar 0 : Term 1)) P _ _)
    (formulaValue (zero (.bvar 0 : Term 1)) P _ _)) (formulaValue hole P _ _))=_
  rw [Successor.domain_body_value h1 hi,zero_body_value h1 hi]
  have hv : formulaValue hole P (bindBound 0) (bindFree f)=P := by
    exact Successor.pred_zero_value hP hi
  rw [hv]
  rfl

theorem conclusion_value {P f:V} (hP:IsSemiformula L 1 P) (hf:IsSemitermVec L (len f) 0 f):
    formulaValue (inductionConclusion hole) P 0 f=conclusionCode P := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by simpa using bindEnvironments_valid h0
  have hi : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 (fun i=>Fin.elim0 i)
  change qqAll (formulaValue (Ordinal.domain (.bvar 0) 🡒 hole) P (bindBound 0) (bindFree f))=_
  rw [closed_imp_value _ _ hP (by simpa using h1) (by decide),Successor.domain_body_value h1 hi]
  rw [show formulaValue hole P (bindBound 0) (bindFree f)=P from Successor.pred_zero_value hP hi]
  rfl


#print axioms base_value
#print axioms conclusion_value
end M6.PA.NumericPAeqOrdinalInductionShape

