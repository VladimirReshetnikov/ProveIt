import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalSeparationShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_sepRoot (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (sepRoot p) = sepRoot (shift SourceL p) := by
  have hrel := relExt_relation_one (M := M)
  have h01 : IsUTermVec SourceL 2 (relExtVector (0 : M) 1) := relExt_vector_valid _ _
  have h02 : IsUTermVec SourceL 2 (relExtVector (0 : M) 2) := relExt_vector_valid _ _
  have hneg : IsUFormula SourceL (neg SourceL p) := hp.isUFormula.neg
  have hv : IsUFormula SourceL (sepInner p) := sepInner_valid p hp.isUFormula
  unfold sepRoot
  rw [shift_all (IsUFormula.ex.mpr (IsUFormula.all.mpr hv)),
    shift_exs (IsUFormula.all.mpr hv), shift_all hv]
  congr 3
  have hna : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 1)) := IsUFormula.nrel.mpr ⟨hrel,h01⟩
  have hnb : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 2)) := IsUFormula.nrel.mpr ⟨hrel,h02⟩
  have ha : IsUFormula SourceL (^rel (2 : M) (1 : M) (relExtVector 0 1)) := IsUFormula.rel.mpr ⟨hrel,h01⟩
  have hb : IsUFormula SourceL (^rel (2 : M) (1 : M) (relExtVector 0 2)) := IsUFormula.rel.mpr ⟨hrel,h02⟩
  simp only [sepInner, shift_and, shift_or, hna, hnb, ha, hb, hp.isUFormula, hneg,
    IsUFormula.and, IsUFormula.or, true_and, shift_neg hp, shift_rel hrel h01, shift_rel hrel h02,
    shift_nrel hrel h01, shift_nrel hrel h02]
  have hvec (a b : M) : termShiftVec SourceL 2 (relExtVector a b) = relExtVector a b := by
    change termShiftVec SourceL 2 (?[ ^#a, ^#b] : M) = ?[ ^#a, ^#b]
    rw [termShiftVec_cons₂ (by simp) (by simp)]
    simp
  simp only [hvec 0 1, hvec 0 2]


theorem shift_neg_sepRoot (p : M) (hp : IsSemiformula SourceL 1 p) :
    shift SourceL (sepRoot (neg SourceL p)) = sepRoot (neg SourceL (shift SourceL p)) := by
  rw [shift_sepRoot (neg SourceL p) hp.neg, shift_neg hp]

noncomputable def shiftSeparationProof (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨sepRoot (shift SourceL p), sepRoot_scoped (shift SourceL p) hp.shift⟩ : Formula M SourceL) := by
  have h := TProof.shift d
  have he : (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL).shift =
      (⟨sepRoot (shift SourceL p), sepRoot_scoped (shift SourceL p) hp.shift⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa using shift_sepRoot p hp
  exact he ▸ h

noncomputable def shiftNegSeparationProof (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL)) :
    T ⊢! (⟨sepRoot (neg SourceL (shift SourceL p)), sepRoot_scoped _ hp.shift.neg⟩ : Formula M SourceL) := by
  have h := shiftSeparationProof T (neg SourceL p) hp.neg d
  have he : (⟨sepRoot (shift SourceL (neg SourceL p)), sepRoot_scoped _ hp.neg.shift⟩ : Formula M SourceL) =
      (⟨sepRoot (neg SourceL (shift SourceL p)), sepRoot_scoped _ hp.shift.neg⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    change sepRoot (shift SourceL (neg SourceL p)) = sepRoot (neg SourceL (shift SourceL p))
    exact congrArg (sepRoot (M := M)) (shift_neg hp)
  exact he ▸ h

#print axioms shift_neg_sepRoot
#print axioms shiftSeparationProof
#print axioms shiftNegSeparationProof
#print axioms shift_sepRoot
end models
end PA194InternalSeparationShift
