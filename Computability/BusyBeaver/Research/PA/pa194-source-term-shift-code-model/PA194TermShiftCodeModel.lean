import PA194TermShiftModel
import PA194BranchSeed
import PA194CodeGraph
import DiophantineConsistency.PRAExhaustion
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194TermShiftCodeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryPairCode PRASelectCode PRAExhaustion PRAModelIOpenPairing
open PA194PathIterator PA194BranchSeed PA194TermShiftModel PA194SourceSearchCoding

def candidate (first second : Code 1) : Code 1 :=
  let d := unary predCode (.proj 0)
  let tag := unary first d
  let payload := unary second d
  let one : Code 1 := .comp oneCode (.nil 1)
  let shifted := unary .succ (bin pairCode one (unary .succ payload))
  selectAmong tag shifted (.proj 0)

noncomputable def firstProjection : Code 1 := Classical.choose PRA_has_pi1Code
noncomputable def secondProjection : Code 1 := Classical.choose PRA_has_pi2Code

theorem firstProjection_certified : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
    (Semiformula.lMap embedding pi₁Def.val) firstProjection :=
  (Classical.choose_spec PRA_has_pi1Code).2

theorem secondProjection_certified : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
    (Semiformula.lMap embedding pi₂Def.val) secondProjection :=
  (Classical.choose_spec PRA_has_pi2Code).2

noncomputable def fixedTermShiftCode : Code 1 := candidate firstProjection secondProjection

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

omit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem modelSucc (x : M) : F .succ (fun _ => x) = x+1 := (modelAddOne x).symm

omit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem modelPredAddOne (x : M) : F predCode (fun _ => x+1) = x := by
  rw [← modelSucc]
  exact modelPredSucc x

theorem candidate_bound (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (z : M) : F (candidate first second) ![^#z] = ^#z := by
  simp only [candidate, modelSelectAmong, modelUnary, modelBin, modelProjection,
    modelPi1Code first hf, modelPi2Code second hs, modelSucc, modelPairCode]
  have hp : F predCode (fun _ => ^#z) = pair 0 z := by
    simpa [qqBvar] using modelPredAddOne (pair (0 : M) z)
  simp only [Matrix.cons_val_zero]
  rw [hp, pi₁_pair]
  change F selectCode ![F (.zero 0) Fin.elim0, _, ^#z] = ^#z
  exact modelSelectZero _ _

omit [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem modelConstantOne (t : M) : F (.comp oneCode (.nil 1)) ![t] = 1 := by
  rw [modelComposition]
  change F oneCode (fun i => F (getCode (.nil 1) i) ![t]) = F oneCode Fin.elim0
  congr 1
  exact Subsingleton.elim _ _

theorem candidate_free (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (x : M) : F (candidate first second) ![^&x] = ^&(x+1) := by
  simp only [candidate, modelSelectAmong, modelUnary, modelBin, modelProjection,
    modelPi1Code first hf, modelPi2Code second hs, modelSucc, modelPairCode]
  have hp : F predCode (fun _ => ^&x) = pair 1 x := by
    simpa [qqFvar] using modelPredAddOne (pair (1 : M) x)
  simp only [Matrix.cons_val_zero]
  rw [hp, pi₁_pair, pi₂_pair]
  change F selectCode ![F oneCode Fin.elim0, _, ^&x] = ^&(x+1)
  rw [modelSelectOne, modelConstantOne]
  rfl

theorem candidate_correct (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    {t : M} (ht : IsUTerm M6.PA.RelationalSource.language t) :
    F (candidate first second) ![t] = termShift M6.PA.RelationalSource.language t := by
  rcases term_cases ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [candidate_bound first second hf hs, termShift_bvar]
  · rw [candidate_free first second hf hs, termShift_fvar]

theorem fixedTermShiftCode_correct {t : M} (ht : IsUTerm M6.PA.RelationalSource.language t) :
    F fixedTermShiftCode ![t] = termShift M6.PA.RelationalSource.language t :=
  candidate_correct firstProjection secondProjection firstProjection_certified secondProjection_certified ht

theorem fixedGraph_correct {t y : M} (ht : IsUTerm M6.PA.RelationalSource.language t) :
    (PA194CodeGraph.graph fixedTermShiftCode).val.Eval ![y,t] Empty.elim ↔
      y = termShift M6.PA.RelationalSource.language t := by
  have h := (PA194CodeGraph.modelGraph (M := M) fixedTermShiftCode).defined ![y,t]
  have he : (fun i : Fin 1 => ![y,t] i.succ) = ![t] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [Matrix.cons_val_zero] at h
  rw [he, fixedTermShiftCode_correct ht] at h
  exact h

#print axioms fixedGraph_correct
#print axioms fixedTermShiftCode_correct
#print axioms candidate_correct
#print axioms firstProjection_certified
#print axioms secondProjection_certified
#print axioms candidate_free
#print axioms candidate_bound
end models
end PA194TermShiftCodeModel
