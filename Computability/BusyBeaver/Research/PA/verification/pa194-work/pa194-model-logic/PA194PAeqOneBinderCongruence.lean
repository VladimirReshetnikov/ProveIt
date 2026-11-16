import PA194PAeqQFCongruence
import PA194PAeqOpenSubstitution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqOneBinderCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Entailment Entailment.FiniteContext Classical PA194PAeq.OpenSubstitution PA194ModelLogic PA194PAeqTermBlueprint PA194PAeq.AtomicCongruence PA194PAeq.BooleanCongruence
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance oneBinderPAeqZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance oneBinderPAeqOne : One M := ⟨F oneCode Fin.elim0⟩
local instance oneBinderPAeqAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance oneBinderPAeqMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance oneBinderPAeqLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance oneBinderPAeqIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






noncomputable local instance : PA194PAeq.ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem shift_equality {a b : M} (ha : IsSemiterm PA194PAeq.language 0 a) (hb : IsSemiterm PA194PAeq.language 0 b)
    (h : Provable PA194PAeq.ordinaryPAeq (PA194PAeqTermBlueprint.equalityCode a b)) :
    Provable PA194PAeq.ordinaryPAeq (PA194PAeqTermBlueprint.equalityCode
      (termShift PA194PAeq.language a) (termShift PA194PAeq.language b)) := by
  let T : InternalTheory M PA194PAeq.language := ⟨PA194PAeq.ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula M PA194PAeq.language := ⟨PA194PAeqTermBlueprint.equalityCode a b, equality_valid ha hb⟩
  have ht : T ⊢ P := (TProvable.iff_provable).mpr h
  have hts : T ⊢ P.shift := TProof.shift! ht
  have hraw := (TProvable.iff_provable).mp hts
  simpa [T,P,equality_shift ha hb] using hraw

theorem opened_qf_replace {p a b : M} (hp : IsSemiformula PA194PAeq.language 2 p)
    (hqf : InternalQuantifierFree (free1 PA194PAeq.language p))
    (ha : IsSemiterm PA194PAeq.language 0 a) (hb : IsSemiterm PA194PAeq.language 0 b)
    (hab : Provable PA194PAeq.ordinaryPAeq (PA194PAeqTermBlueprint.equalityCode a b)) :
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language
      (Bootstrapping.free PA194PAeq.language (subst PA194PAeq.language (qVec PA194PAeq.language (a∷(0:M))) p))
      (Bootstrapping.free PA194PAeq.language (subst PA194PAeq.language (qVec PA194PAeq.language (b∷(0:M))) p))) := by
  let P : Semiformula M PA194PAeq.language 2 := ⟨p,by simpa using hp⟩
  let A : Term M PA194PAeq.language := ⟨a,ha⟩
  let B : Term M PA194PAeq.language := ⟨b,hb⟩
  have hshift := shift_equality ha hb hab
  have hP : IsSemiformula PA194PAeq.language 1 P.free1.val := by simpa using P.free1.isSemiformula
  have hqf' : InternalQuantifierFree P.free1.val := by simpa [P] using hqf
  have h := PA194PAeqQFCongruence.replace P.free1.val A.shift.val B.shift.val hP hqf'
    A.shift.isSemiterm B.shift.isSemiterm hshift
  have hA : (P.free1.subst ![A.shift]).val =
      Bootstrapping.free PA194PAeq.language (subst PA194PAeq.language (qVec PA194PAeq.language (a∷(0:M))) p) := by
    rw [← open_subst P A]
    simp [P,A,Semiformula.val_substs,SemitermVec.q_val_eq_qVec,SemitermVec.val_succ,qVec,termBShiftVec_cons₁,ha.isUTerm,hb.isUTerm]
  have hB : (P.free1.subst ![B.shift]).val =
      Bootstrapping.free PA194PAeq.language (subst PA194PAeq.language (qVec PA194PAeq.language (b∷(0:M))) p) := by
    rw [← open_subst P B]
    simp [P,B,Semiformula.val_substs,SemitermVec.q_val_eq_qVec,SemitermVec.val_succ,qVec,termBShiftVec_cons₁,ha.isUTerm,hb.isUTerm]
  simpa [substs1,← hA,← hB,Semiformula.val_substs,SemitermVec.val_succ] using h

theorem all_qf_replace {p a b : M} (hp : IsSemiformula PA194PAeq.language 2 p)
    (hqf : InternalQuantifierFree (free1 PA194PAeq.language p))
    (ha : IsSemiterm PA194PAeq.language 0 a) (hb : IsSemiterm PA194PAeq.language 0 b)
    (hab : Provable PA194PAeq.ordinaryPAeq (PA194PAeqTermBlueprint.equalityCode a b)) :
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language
      (substs1 PA194PAeq.language a (^∀ p)) (substs1 PA194PAeq.language b (^∀ p))) := by
  have hva : IsSemitermVec PA194PAeq.language 1 0 (a∷(0:M)) := by simp [ha]
  have hvb : IsSemitermVec PA194PAeq.language 1 0 (b∷(0:M)) := by simp [hb]
  have hp' : IsSemiformula PA194PAeq.language (1+1) p := by simpa [one_add_one_eq_two] using hp
  have hpa : IsSemiformula PA194PAeq.language 1 (subst PA194PAeq.language (qVec PA194PAeq.language (a∷(0:M))) p) := by
    simpa using hp'.subst hva.qVec
  have hpb : IsSemiformula PA194PAeq.language 1 (subst PA194PAeq.language (qVec PA194PAeq.language (b∷(0:M))) p) := by
    simpa using hp'.subst hvb.qVec
  have h := PA194PAeq.BooleanCongruence.all_imp hpa hpb (opened_qf_replace hp hqf ha hb hab)
  simpa [substs1,substs_all hp.isUFormula] using h

theorem exs_qf_replace {p a b : M} (hp : IsSemiformula PA194PAeq.language 2 p)
    (hqf : InternalQuantifierFree (free1 PA194PAeq.language p))
    (ha : IsSemiterm PA194PAeq.language 0 a) (hb : IsSemiterm PA194PAeq.language 0 b)
    (hab : Provable PA194PAeq.ordinaryPAeq (PA194PAeqTermBlueprint.equalityCode a b)) :
    Provable PA194PAeq.ordinaryPAeq (imp PA194PAeq.language
      (substs1 PA194PAeq.language a (^∃ p)) (substs1 PA194PAeq.language b (^∃ p))) := by
  have hva : IsSemitermVec PA194PAeq.language 1 0 (a∷(0:M)) := by simp [ha]
  have hvb : IsSemitermVec PA194PAeq.language 1 0 (b∷(0:M)) := by simp [hb]
  have hp' : IsSemiformula PA194PAeq.language (1+1) p := by simpa [one_add_one_eq_two] using hp
  have hpa : IsSemiformula PA194PAeq.language 1 (subst PA194PAeq.language (qVec PA194PAeq.language (a∷(0:M))) p) := by
    simpa using hp'.subst hva.qVec
  have hpb : IsSemiformula PA194PAeq.language 1 (subst PA194PAeq.language (qVec PA194PAeq.language (b∷(0:M))) p) := by
    simpa using hp'.subst hvb.qVec
  have h := PA194PAeq.BooleanCongruence.exs_imp hpa hpb (opened_qf_replace hp hqf ha hb hab)
  simpa [substs1,substs_ex hp.isUFormula] using h

#print axioms all_qf_replace
#print axioms exs_qf_replace
#print axioms opened_qf_replace
#print axioms shift_equality
end models
end PA194PAeqOneBinderCongruence
