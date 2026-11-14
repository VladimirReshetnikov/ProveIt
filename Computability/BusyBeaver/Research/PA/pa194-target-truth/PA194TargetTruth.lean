import PA194TargetProofLeaf
import PA194VerumNode
import PA194RelationalEncoding
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetTruth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetLeaves PA194TargetGate PA194TargetProofLeaf
 PA194AllFields PA194VerumNode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
theorem standard_truth_binding (z lo : Nat) :
    PA194Logic.Relational.relationalCode z
      (M6.PA.RelationalSource.toNamed (ξ := Empty) (n := 0) .verum Fin.elim0 Empty.elim lo) = 0 := rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_imp_zero : impValue (0 : M) 0 = 0 := by
  simp [impValue, cantor, triangle]

theorem truth_certificate : TargetProof ((pair (8 : M) (pair 0 (pair 0 (pair 0 0)))) ∷ (0 : M)) (0 : M) := by
  constructor
  · simp
  · rw [rootCode_model,one_line,tag8,if_neg (by simp)]
    simp [rho8Value,zero_imp_zero]

theorem verum_node_target (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    {d : M} (hd : Derivation T d) (ht : F tag (fun _ => d) = 1) :
    IsFormulaSet M6.PA.RelationalSource.language (F context (fun _ => d)) ∧
      qqVerum ∈ F context (fun _ => d) ∧
      TargetProof ((pair (8 : M) (pair 0 (pair 0 (pair 0 0)))) ∷ (0 : M)) (0 : M) := by
  obtain ⟨hs,hv⟩ := selected_verum T hd ht
  exact ⟨hs,hv,truth_certificate⟩

#print axioms standard_truth_binding
#print axioms zero_imp_zero
#print axioms truth_certificate
#print axioms verum_node_target
end models
end PA194TargetTruth
