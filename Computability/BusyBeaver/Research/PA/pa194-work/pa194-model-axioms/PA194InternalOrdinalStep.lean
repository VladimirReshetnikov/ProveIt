import PA194InternalOrdinalBase
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalOrdinalStep
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
local instance ordinalStepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalStepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalStepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalStepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalStepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalStepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Outer ordinal-induction step syntax, parameterized by its five arity-two inputs. -/
noncomputable def inductionStepCode (d₁ d₀ s p₁ p₀ : M) : M :=
  ^∀ (^∀ (neg SourceL (d₁ ^⋏ (d₀ ^⋏ (s ^⋏ p₁))) ^⋎ p₀))

noncomputable def inductionStepGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out d1 d0 s p1 p0. ∃ a, !qqAndDef a s p1 ∧ ∃ b, !qqAndDef b d0 a ∧
    ∃ c, !qqAndDef c d1 b ∧ ∃ n, !(negGraph SourceL) n c ∧
    ∃ e, !qqOrDef e n p0 ∧ ∃ f, !qqAllDef f e ∧ !qqAllDef out f”

theorem inductionStepGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => inductionStepCode (v 0) (v 1) (v 2) (v 3) (v 4)) inductionStepGraph := .mk fun v => by
  simp [inductionStepGraph,inductionStepCode]

theorem inductionStepCode_scoped (d₁ d₀ s p₁ p₀ : M)
    (hd₁ : IsSemiformula SourceL 2 d₁) (hd₀ : IsSemiformula SourceL 2 d₀)
    (hs : IsSemiformula SourceL 2 s) (hp₁ : IsSemiformula SourceL 2 p₁)
    (hp₀ : IsSemiformula SourceL 2 p₀) : IsSemiformula SourceL 0 (inductionStepCode d₁ d₀ s p₁ p₀) := by
  have htwo : (1 : M)+1 = 2 := by norm_num
  simp only [inductionStepCode,IsSemiformula.all,zero_add,htwo,IsSemiformula.or,IsSemiformula.neg_iff,IsSemiformula.and]
  exact ⟨⟨hd₁,hd₀,hs,hp₁⟩,hp₀⟩

#print axioms inductionStepGraph_defined
#print axioms inductionStepCode_scoped
end models
end PA194InternalOrdinalStep
