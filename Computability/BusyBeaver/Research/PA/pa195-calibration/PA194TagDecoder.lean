import PA194ChildCodes

/-! Candidate-PRA code for the exact PA194 source constructor tag. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
namespace PA194TagDecoder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHerbrandSelection PRABoundedWitness PA194ChildCodes

def tagMatrix : 𝚺₀.Semisentence 2 := .mkSigma “r n. !remDef r n 4”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem tagMatrix_eval (r n : M) : tagMatrix.val.Evalb ![r,n] ↔ r = n % 4 := by
  have h (r n : M) : remDef.val.Evalb ![r,n,4] ↔ r = n % 4 := rem_defined.defined ![r,n,4]
  simp [tagMatrix, h]

theorem modelTagTotal : M↓[language] ⊧ (∀⁰* ∃⁰ Semiformula.lMap embedding tagMatrix.val) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨e 0 % 4, ?_⟩
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  have he : ((e 0 % 4) :> e) = ![e 0 % 4,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he, tagMatrix_eval]

theorem modelTagCode (f : Code 1)
    (h : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) f)
    (n : M) : Structure.func (L := language) f (fun _ => n) = n % 4 :=
  (tagMatrix_eval _ n).mp (modelSelected tagMatrix.val f h n)
/-- Each numerical constructor with tag below four is dispatched to that tag,
including for nonstandard payloads and tags. Code zero remains a separately
handled alias of the implication tag. -/
theorem modelTagConstructor (f : Code 1)
    (h : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) f)
    (payload tag : M) (htag : tag < 4) :
    Structure.func (L := language) f (fun _ => 4 * payload + tag) = tag := by
  rw [modelTagCode f h]
  simpa only [mul_comm] using (mod_mul_add_of_lt payload 4 htag)

end models

theorem PRA_has_tagCode : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy tagMatrix.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelTagTotal

#print axioms tagMatrix_eval
#print axioms modelTagCode
#print axioms modelTagConstructor
#print axioms PRA_has_tagCode
end PA194TagDecoder
