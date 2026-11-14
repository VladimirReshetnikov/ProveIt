import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic

/-! Generic four-field Foundation syntax constructor, also used by function terms. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194QuadCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing

def inner : Code 4 := bin pairCode (.proj 2) (.proj 3)
def middle : Code 4 := bin pairCode (.proj 1) inner
def outer : Code 4 := bin pairCode (.proj 0) middle
/-- Inputs are the syntax tag, arity, symbol code, and argument vector. -/
def quadCode : Code 4 := .comp Code.succ (.cons outer (.nil 4))

noncomputable def quadGraph : ArithmeticSemisentence 5 :=
  “out tag arity sym vec. ∃ p < out, !pair₄Def p tag arity sym vec ∧ out = p + 1”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelQuadValue (tag arity sym vec : M) :
    Structure.func (L := language) quadCode ![tag,arity,sym,vec] =
      pair tag (pair arity (pair sym vec)) + 1 := by
  rw [quadCode, modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons outer (.nil 4)) i) ![tag,arity,sym,vec]) =
      (fun _ : Fin 1 => pair tag (pair arity (pair sym vec))) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) outer ![tag,arity,sym,vec] = _
    rw [outer,modelBin,modelProjection,middle,modelBin,modelProjection,
      inner,modelBin,modelProjection,modelProjection,modelPairCode,modelPairCode,modelPairCode]
    rfl
  rw [he, ←modelAddOne]
  rfl

theorem modelQuadGraph (tag arity sym vec : M) :
    quadGraph.Eval ![Structure.func (L := language) quadCode ![tag,arity,sym,vec],tag,arity,sym,vec] Empty.elim := by
  rw [modelQuadValue]
  simp [quadGraph, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]
/-- Tag 2 is Foundation's function-term constructor. -/
theorem modelFunctionGraph (arity sym vec : M) :
    qqFuncDef.val.Evalb ![Structure.func (L := language) quadCode ![2,arity,sym,vec],arity,sym,vec] := by
  rw [modelQuadValue]
  simp [qqFuncDef, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]
  constructor
  · exact lt_succ_iff_le.mpr (le_trans (le_pair_right arity (pair sym vec))
      (le_pair_right 2 (pair arity (pair sym vec))))
  · exact lt_succ_iff_le.mpr (le_pair_right 2 (pair arity (pair sym vec)))

end models

noncomputable def quadGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func quadCode ![#0,#1,#2,#3],#0,#1,#2,#3] : Rew language Empty 5 Empty 4) ▹
    Semiformula.lMap embedding quadGraph : Semisentence language 4)

theorem PRA_proves_quadGraph : PRA ⊢ quadGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, quadGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_four e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1,e 2,e 3] Empty.elim ∘
      Rew.embSubsts ![.func quadCode ![#0,#1,#2,#3],#0,#1,#2,#3] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) quadCode ![e 0,e 1,e 2,e 3],e 0,e 1,e 2,e 3] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      refine Fin.cases (by simp) (fun l => ?_) k
      refine Fin.cases (by simp) (fun m => ?_) l
      exact Fin.cases (by simp) (fun n => Fin.elim0 n) m
  have he : (Semiterm.val (L := language) ![e 0,e 1,e 2,e 3] Empty.elim ∘
      Rew.embSubsts ![.func quadCode ![#0,#1,#2,#3],#0,#1,#2,#3] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelQuadGraph (e 0) (e 1) (e 2) (e 3)

#print axioms PRA_proves_quadGraph
#print axioms modelQuadValue
#print axioms modelQuadGraph
#print axioms modelFunctionGraph
end PA194QuadCode
