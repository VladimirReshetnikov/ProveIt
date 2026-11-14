import PA194PathIterator
import DiophantineConsistency.PRAHistoryInsertCode

/-! Encoded root and arbitrary branch-word parameters for PA194 paths.
The seed uses Foundation's auxiliary pair only to pack the root and branch
word; PA194's formula decoder continues to use its distinct Cantor pair. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194BranchSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRABoundedWitness PRAHistoryInsertCode PRAHistoryPairCode PRABoundedCharacteristic PRABoundedFormula

/-- The seed encodes `[root, branchWord]` using the auxiliary Foundation
pair; the branch selector reads the indexed bit from its second component. -/
def branchChoice (bit : Code 2) (seedSecond : Code 1) : Code 2 :=
  bin bit (.proj 1) (PA194PathIterator.unary seedSecond (.proj 0))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelPi1Total : M↓[language] ⊧ (∀⁰* ∃⁰ Semiformula.lMap embedding pi₁Def.val) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨π₁ (e 0), ?_⟩
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have he : (π₁ (e 0) :> e) = ![π₁ (e 0),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he]
  exact (pi₁_defined.defined ![π₁ (e 0),e 0]).mpr rfl

theorem modelPi2Total : M↓[language] ⊧ (∀⁰* ∃⁰ Semiformula.lMap embedding pi₂Def.val) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨π₂ (e 0), ?_⟩
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have he : (π₂ (e 0) :> e) = ![π₂ (e 0),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he]
  exact (pi₂_defined.defined ![π₂ (e 0),e 0]).mpr rfl

theorem modelPi1Code (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) f)
    (n : M) : Structure.func (L := language) f (fun _ => n) = π₁ n :=
  (pi₁_defined.defined ![Structure.func (L := language) f (fun _ => n),n]).mp
    (PA194ChildCodes.modelSelected pi₁Def.val f h n)

theorem modelPi2Code (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) f)
    (n : M) : Structure.func (L := language) f (fun _ => n) = π₂ n :=
  (pi₂_defined.defined ![Structure.func (L := language) f (fun _ => n),n]).mp
    (PA194ChildCodes.modelSelected pi₂Def.val f h n)

/-- A certified root projection recovers the chosen root from a packed seed. -/
theorem modelSeedRoot (rootCode : Code 1)
    (hroot : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) rootCode)
    (root branchWord : M) :
    Structure.func (L := language) rootCode (fun _ => pair root branchWord) = root := by
  rw [modelPi1Code rootCode hroot, pi₁_pair]

/-- A certified bit code reads exactly the desired bit of the packed branch
word at every, possibly nonstandard, index. -/
theorem modelBranchChoice (bit : Code 2) (seedSecond : Code 1)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) seedSecond)
    (hcorrect : PRA ⊢ oneCorrectSentence bit bitGraph)
    (root branchWord i : M) :
    Structure.func (L := language) (branchChoice bit seedSecond) ![pair root branchWord,i] =
        Structure.func (L := language) oneCode Fin.elim0 ↔
      bitDef.val.Evalb ![i,branchWord] := by
  have hval : Structure.func (L := language) (branchChoice bit seedSecond) ![pair root branchWord,i] =
      Structure.func (L := language) bit ![i,branchWord] := by
    rw [branchChoice, modelBin, modelProjection, PA194PathIterator.modelUnary, modelProjection,
      modelPi2Code seedSecond hsecond]
    change Structure.func (L := language) bit ![i,π₂ (pair root branchWord)] = _
    rw [pi₂_pair]
  rw [hval]
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect
  have hc := (oneCorrectSentence_iff bit bitGraph).mp hm ![i,branchWord]
  rw [bitGraph, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hc
  exact hc

/-- The constructed iterator starts at the root packed into its seed. -/
theorem modelSeedPathBase (rootCode firstChild secondChild : Code 1) (bit : Code 2) (seedSecond : Code 1)
    (hroot : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) rootCode)
    (root branchWord : M) :
    PA195PathBound.pathValue
      (PA194PathIterator.pathCode rootCode firstChild secondChild (branchChoice bit seedSecond))
      (pair root branchWord) 0 = root := by
  rw [PA194PathIterator.modelPathBase, modelSeedRoot rootCode hroot]

/-- At each model index, the branch-word bit selects the first or second
exact PA194 decoder child. -/
theorem modelSeedPathBranch (rootCode firstChild secondChild : Code 1) (bit : Code 2) (seedSecond : Code 1)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.firstMatrix.val) firstChild)
    (hsecondChild : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding PA194ChildCodes.secondMatrix.val) secondChild)
    (hsecondSeed : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) seedSecond)
    (hbit : PRA ⊢ PRACharacteristicBit.bitSentence bit)
    (hcorrect : PRA ⊢ oneCorrectSentence bit bitGraph)
    (root branchWord i : M) :
    let f := PA194PathIterator.pathCode rootCode firstChild secondChild (branchChoice bit seedSecond)
    let current := PA195PathBound.pathValue f (pair root branchWord) i
    (bitDef.val.Evalb ![i,branchWord] →
      PA195PathBound.pathValue f (pair root branchWord) (i+1) =
        SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (current / 4)) ∧
    (¬bitDef.val.Evalb ![i,branchWord] →
      PA195PathBound.pathValue f (pair root branchWord) (i+1) =
        SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (current / 4)) := by
  dsimp only
  rw [PA194PathIterator.modelPathStepRaw,
    PA194ChildCodes.modelFirstCode firstChild hfirst,
    PA194ChildCodes.modelSecondCode secondChild hsecondChild]
  have hchoice := modelBranchChoice bit seedSecond hsecondSeed hcorrect root branchWord i
  constructor
  · intro hb
    rw [hchoice.mpr hb, PRASelectCode.modelSelectOne]
  · intro hb
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit
    have hbits := (PRACharacteristicBit.bitSentence_iff bit).mp hm ![i,branchWord]
    have hraw : Structure.func (L := language) (branchChoice bit seedSecond) ![pair root branchWord,i] =
        Structure.func (L := language) bit ![i,branchWord] := by
      rw [branchChoice, modelBin, modelProjection, PA194PathIterator.modelUnary, modelProjection,
        modelPi2Code seedSecond hsecondSeed]
      change Structure.func (L := language) bit ![i,π₂ (pair root branchWord)] = _
      rw [pi₂_pair]
    have hz : Structure.func (L := language) (branchChoice bit seedSecond) ![pair root branchWord,i] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      rcases hbits with hzero | hone
      · exact hraw.trans hzero
      · exact False.elim (hb (hchoice.mp (hraw.trans hone)))
    rw [hz, PRASelectCode.modelSelectZero]

end models

theorem PRA_has_pi1Code : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy pi₁Def.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelPi1Total

theorem PRA_has_pi2Code : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy pi₂Def.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelPi2Total

theorem PRA_has_branchBitCode : ∃ f : Code 2, Primrec (eval f) ∧
    PRA ⊢ PRACharacteristicBit.bitSentence f ∧ PRA ⊢ oneCorrectSentence f bitGraph := by
  apply PRA_proves_boundedBooleanCharacteristic bitGraph
  exact ParsonsHierarchyMap.hierarchy bitDef.sigma_prop

#print axioms modelSeedPathBase
#print axioms modelSeedPathBranch
#print axioms modelSeedRoot
#print axioms modelBranchChoice
#print axioms PRA_has_pi1Code
#print axioms PRA_has_pi2Code
#print axioms PRA_has_branchBitCode
end PA194BranchSeed
