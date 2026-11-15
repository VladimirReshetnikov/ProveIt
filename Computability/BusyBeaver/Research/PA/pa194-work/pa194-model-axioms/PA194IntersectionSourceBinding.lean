import PA194AtomicParameterSeparation
import PA194SourceIntersection
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IntersectionSourceBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource

/-- The source intersection formula, with no free variables. -/
def sourceIntersection : Sentence M6.PA.RelationalSource.language :=
  Ordinal.intersectionFormula.univCl

theorem intersection_coe : (sourceIntersection : Proposition M6.PA.RelationalSource.language) = Ordinal.intersectionFormula := by
  unfold sourceIntersection
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance intBindZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance intBindOne : One M := ⟨F oneCode Fin.elim0⟩
local instance intBindAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance intBindMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance intBindLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance intBindIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem intersection_quote : (⌜sourceIntersection⌝ : M) =
    ^∀ (sepRoot (^rel (2 : M) (1 : M) ?[^#(0 : M), ^#(3 : M)])) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M), ^#(3 : M)] : M) := by simp
  rw [Sentence.quote_def, intersection_coe]
  change (⌜(∀⁰ ∀⁰ ∃⁰ ∀⁰
    ((Semiformula.nrel Relation.mem ![#0,#1] ⋎
      (Semiformula.rel Relation.mem ![#0,#2] ⋏ Semiformula.rel Relation.mem ![#0,#3])) ⋏
     ((Semiformula.nrel Relation.mem ![#0,#2] ⋎ Semiformula.nrel Relation.mem ![#0,#3]) ⋎
      Semiformula.rel Relation.mem ![#0,#1])) : Proposition M6.PA.RelationalSource.language)⌝ : M) = _
  simp [Semiformula.quote_all, sepRoot, sepInner, relExtVector, Matrix.vecHead,
    Matrix.vecTail, Function.comp_def, adjoin_def]
  constructor
  · change ((1 : ℕ) : M) = 1
    simp
  constructor
  · constructor
    · change ((1 : ℕ) : M) = 1
      simp
    · change ^nrel (2 : M) ((1 : ℕ) : M) (?[ ^#(0 : M), ^#(3 : M)] : M) =
        neg SourceL (^rel (2 : M) (1 : M) ?[ ^#(0 : M), ^#(3 : M)])
      simpa only [Nat.cast_one] using (neg_rel hr hv).symm
  · change ((1 : ℕ) : M) = 1
    simp

/-- The actual quoted source intersection sentence supplies its numerical
compiler axiom leaf at any seeded axiom node. -/
theorem intersection_axiom (bound reserve e s : M)
    (hs : IsFormulaSet SourceL s) (hm : (⌜sourceIntersection⌝ : M) ∈ s)
    (ha : SeedAdmission bound reserve e (axm s (⌜sourceIntersection⌝ : M))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (⌜sourceIntersection⌝ : M)) 1) := by
  rw [intersection_quote] at hm ha ⊢
  exact PA194AtomicParameterSeparation.atomicParameter_axiom bound reserve e s hs hm ha
#print axioms intersection_axiom
#print axioms intersection_coe
#print axioms intersection_quote
end models
end PA194IntersectionSourceBinding
