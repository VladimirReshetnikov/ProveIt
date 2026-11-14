import PA194SetSearch
/-! A fixed binary source preimage code and its parameter-free Σ₁ graph.
This is a universal-rule search component, not a complete proof compiler. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
namespace PA194SetSearchRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PA194SetSearch

/-- Search the actual bit-coded set, using the set value itself as the bound. -/
noncomputable def preimageCode : Code 2 :=
  .comp setSearch (.cons (.proj 0) (.cons (.proj 0) (.cons (.proj 1) (.nil 2))))

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

theorem preimage_model (a target : M) : F preimageCode ![a,target] = F setSearch ![a,a,target] := by
  rw [preimageCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 0 _
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      exact modelProjection 1 _

theorem preimage_correct (a target : M)
    (hset : IsFormulaSet M6.PA.RelationalSource.language a)
    (htarget : target ∈ setShift M6.PA.RelationalSource.language a) :
    let found := F preimageCode ![a,target]
    found ∈ a ∧ shift M6.PA.RelationalSource.language found = target := by
  rw [preimage_model]
  exact find_setShift a target hset htarget

theorem preimage_graph_correct {a target y : M}
    (hset : IsFormulaSet M6.PA.RelationalSource.language a)
    (htarget : target ∈ setShift M6.PA.RelationalSource.language a)
    (hy : (PA194CodeGraph.graph preimageCode).val.Eval ![y,a,target] Empty.elim) :
    y ∈ a ∧ shift M6.PA.RelationalSource.language y = target := by
  have h := (PA194CodeGraph.modelGraph (M := M) preimageCode).defined ![y,a,target]
  have he : (fun i : Fin 2 => ![y,a,target] i.succ) = ![a,target] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  rw [h.mp hy]
  exact preimage_correct a target hset htarget

#print axioms preimage_model
#print axioms preimage_correct
#print axioms preimage_graph_correct
end models
end PA194SetSearchRoot
