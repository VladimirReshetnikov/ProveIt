import PA194FullyClosedSeparation
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedSeparation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
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
local instance typedSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance typedSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance typedSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem liftMember_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    (⌜liftMember p⌝ : M) = ⌜p⌝ := by
  have hrew : (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id : SyntacticRew M6.PA.RelationalSource.language 1 3) = Rew.castLE (by decide : 1 ≤ 3) := by
    ext x
    · have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · simp
  unfold liftMember
  rw [hrew]
  exact Semiformula.quote_castLE p (by decide : 1 ≤ 3)

theorem quote_neg {n : Nat} (p : Semiproposition M6.PA.RelationalSource.language n) :
    (⌜∼p⌝ : M) = neg SourceL (⌜p⌝ : M) := by
  change ((Semiformula.typedQuote M (∼p)).val : M) = neg SourceL (Semiformula.typedQuote M p).val
  rw [Semiformula.typedQuote_neg]
  rfl

theorem separationFormula_quote (p : Semiproposition M6.PA.RelationalSource.language 1) :
    (⌜separationFormula p⌝ : M) = sepRoot (⌜p⌝ : M) := by
  change (⌜(∀⁰ ∃⁰ ∀⁰ (((∼memAtom 1 0) ⋎ ((memAtom 2 0) ⋏ liftMember p)) ⋏
    ((∼((memAtom 2 0) ⋏ liftMember p)) ⋎ memAtom 1 0)) :
    Proposition M6.PA.RelationalSource.language)⌝ : M) = _
  simp only [Semiformula.quote_all,Semiformula.quote_ex,sourceIff,sourceImply,
    Semiformula.quote_and,Semiformula.quote_or,quote_neg]
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv01 : IsUTermVec SourceL 2 (?[ ^#(0 : M), ^#(1 : M)] : M) := by simp
  have hv02 : IsUTermVec SourceL 2 (?[ ^#(0 : M), ^#(2 : M)] : M) := by simp
  have hp : IsUFormula SourceL (⌜p⌝ : M) := (Semiformula.quote_isSemiformul₁ p).isUFormula
  simp [memAtom,sepRoot,sepInner,relExtVector,liftMember_quote,Semiformula.quote_rel,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  constructor
  · constructor
    · change neg SourceL (^rel (2 : M) ((1 : Nat) : M) (?[ ^#(0 : M), ^#(1 : M)] : M)) = _
      simpa only [Nat.cast_one, adjoin_def] using neg_rel hr hv01
    · change ((1 : Nat) : M) = 1
      simp
  · constructor
    · change neg SourceL ((^rel (2 : M) ((1 : Nat) : M) (?[ ^#(0 : M), ^#(2 : M)] : M)) ^⋏ (⌜p⌝ : M)) = _
      rw [Nat.cast_one,neg_and (IsUFormula.rel.mpr ⟨hr,hv02⟩) hp,neg_rel hr hv02]
      simp only [adjoin_def]
    · change ((1 : Nat) : M) = 1
      simp

#print axioms separationFormula_quote
#print axioms liftMember_quote
end models
end PA194TypedSeparation
