import PA194TermShiftCodeModel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194VectorShiftCodeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryPairCode PRASelectCode PRAExhaustion PRAModelIOpenPairing
open PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194SourceSearchCoding

noncomputable def vectorShiftCode : Code 1 := by
  let d : Code 1 := unary predCode (.proj 0)
  let a : Code 1 := unary firstProjection d
  let tail : Code 1 := unary secondProjection d
  let b : Code 1 := unary firstProjection (unary predCode tail)
  let sa : Code 1 := unary fixedTermShiftCode a
  let sb : Code 1 := unary fixedTermShiftCode b
  let tailOut : Code 1 := unary .succ (bin pairCode sb (.zero 1))
  exact unary .succ (bin pairCode sa tailOut)

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

theorem modelTerm (t : M) (ht : IsUTerm M6.PA.RelationalSource.language t) :
    F fixedTermShiftCode (fun _ => t) = termShift M6.PA.RelationalSource.language t := by
  have h := fixedTermShiftCode_correct ht
  have he : (fun _ : Fin 1 => t) = ![t] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [he]
  exact h

theorem vectorShift_model (a b : M)
    (ha : IsUTerm M6.PA.RelationalSource.language a)
    (hb : IsUTerm M6.PA.RelationalSource.language b) :
    F vectorShiftCode ![pair a (pair b 0+1)+1] =
      pair (termShift M6.PA.RelationalSource.language a)
        (pair (termShift M6.PA.RelationalSource.language b) 0+1)+1 := by
  simp only [vectorShiftCode, modelUnary, modelBin, modelProjection, modelSucc, modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,
    PRAMultiplication.modelZero, Matrix.cons_val_zero, modelPredAddOne, pi₁_pair, pi₂_pair,
    modelTerm a ha, modelTerm b hb]
  rfl

theorem vectorShift_complete {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F vectorShiftCode ![v] = termShiftVec M6.PA.RelationalSource.language 2 v := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  rw [termShiftVec_cons₂ ha hb]
  simpa [adjoin_def] using vectorShift_model a b ha hb

#print axioms vectorShift_complete
#print axioms vectorShift_model
end models
end PA194VectorShiftCodeModel
