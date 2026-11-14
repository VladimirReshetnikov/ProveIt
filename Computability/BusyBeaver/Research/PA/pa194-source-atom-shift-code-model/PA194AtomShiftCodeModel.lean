import PA194VectorShiftCodeModel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194AtomShiftCodeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryPairCode PRASelectCode PRAExhaustion PRAModelIOpenPairing
open PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194VectorShiftCodeModel PA194SourceSearchCoding

noncomputable def atomShiftCode : Code 1 := by
  let d : Code 1 := unary predCode (.proj 0)
  let tag : Code 1 := unary firstProjection d
  let p : Code 1 := unary secondProjection d
  let arity : Code 1 := unary firstProjection p
  let q : Code 1 := unary secondProjection p
  let r : Code 1 := unary firstProjection q
  let v : Code 1 := unary secondProjection q
  let sv : Code 1 := unary vectorShiftCode v
  exact unary .succ (bin pairCode tag (bin pairCode arity (bin pairCode r sv)))

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

theorem sourceRelation_arity {k r : M} (hr : M6.PA.RelationalSource.language.IsRel k r) : k = 2 := by
  change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![k,r]) at hr
  have h : (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by simpa using hr
  exact h.elim And.left And.left

theorem modelVector (v : M) (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F vectorShiftCode (fun _ => v) = termShiftVec M6.PA.RelationalSource.language 2 v := by
  have h := vectorShift_complete hv
  have he : (fun _ : Fin 1 => v) = ![v] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [he]
  exact h

theorem atom_model (tag r v : M)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F atomShiftCode ![pair tag (pair 2 (pair r v))+1] =
      pair tag (pair 2 (pair r (termShiftVec M6.PA.RelationalSource.language 2 v)))+1 := by
  simp only [atomShiftCode, modelUnary, modelBin, modelProjection, modelSucc, modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,
    Matrix.cons_val_zero, modelPredAddOne, pi₁_pair, pi₂_pair, modelVector v hv]

theorem positiveAtom_model (r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F atomShiftCode ![^rel (2 : M) r v] =
      shift M6.PA.RelationalSource.language (^rel (2 : M) r v) := by
  rw [shift_rel hr hv]
  simpa [qqRel] using atom_model (0 : M) r v hv

theorem negativeAtom_model (r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F atomShiftCode ![^nrel (2 : M) r v] =
      shift M6.PA.RelationalSource.language (^nrel (2 : M) r v) := by
  rw [shift_nrel hr hv]
  simpa [qqNRel] using atom_model (1 : M) r v hv

theorem positiveAtom_model_all (k r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel k r)
    (hv : IsUTermVec M6.PA.RelationalSource.language k v) :
    F atomShiftCode ![^rel k r v] = shift M6.PA.RelationalSource.language (^rel k r v) := by
  rw [sourceRelation_arity hr] at *
  exact positiveAtom_model r v hr hv

theorem negativeAtom_model_all (k r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel k r)
    (hv : IsUTermVec M6.PA.RelationalSource.language k v) :
    F atomShiftCode ![^nrel k r v] = shift M6.PA.RelationalSource.language (^nrel k r v) := by
  rw [sourceRelation_arity hr] at *
  exact negativeAtom_model r v hr hv

theorem atomGraph_relation (t y : M) :
    (PA194CodeGraph.graph atomShiftCode).val.Eval ![y,t] Empty.elim ↔ y = F atomShiftCode ![t] := by
  have h := (PA194CodeGraph.modelGraph (M := M) atomShiftCode).defined ![y,t]
  have he : (fun i : Fin 1 => ![y,t] i.succ) = ![t] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  exact h

theorem positiveAtom_graph (k r v y : M)
    (hr : M6.PA.RelationalSource.language.IsRel k r)
    (hv : IsUTermVec M6.PA.RelationalSource.language k v) :
    (PA194CodeGraph.graph atomShiftCode).val.Eval ![y,^rel k r v] Empty.elim ↔
      y = shift M6.PA.RelationalSource.language (^rel k r v) := by
  rw [atomGraph_relation, positiveAtom_model_all k r v hr hv]

theorem negativeAtom_graph (k r v y : M)
    (hr : M6.PA.RelationalSource.language.IsRel k r)
    (hv : IsUTermVec M6.PA.RelationalSource.language k v) :
    (PA194CodeGraph.graph atomShiftCode).val.Eval ![y,^nrel k r v] Empty.elim ↔
      y = shift M6.PA.RelationalSource.language (^nrel k r v) := by
  rw [atomGraph_relation, negativeAtom_model_all k r v hr hv]

#print axioms atomGraph_relation
#print axioms positiveAtom_graph
#print axioms negativeAtom_graph
#print axioms sourceRelation_arity
#print axioms positiveAtom_model_all
#print axioms negativeAtom_model_all
#print axioms positiveAtom_model
#print axioms negativeAtom_model
#print axioms atom_model
end models
end PA194AtomShiftCodeModel
