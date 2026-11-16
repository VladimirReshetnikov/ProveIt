import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic

/-! Certified primitive-recursive Foundation relation syntax construction. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194RelCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing

def relPayload : Code 3 := bin pairCode (.proj 1) (.proj 2)
def relArgs : Code 3 := bin pairCode (.proj 0) relPayload
def relTag : Code 3 := bin pairCode (.zero 3) relArgs
/-- Code for `qqRel` from `[arity, encoded relation symbol, argument vector]`. -/
def relCode : Code 3 := .comp Code.succ (.cons relTag (.nil 3))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelRelValue (arity sym vec : M) :
    Structure.func (L := language) relCode ![arity,sym,vec] =
      pair 0 (pair arity (pair sym vec)) + 1 := by
  rw [relCode, modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons relTag (.nil 3)) i) ![arity,sym,vec]) =
      (fun _ : Fin 1 => pair 0 (pair arity (pair sym vec))) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) relTag ![arity,sym,vec] = _
    rw [relTag, modelBin, PRAMultiplication.modelZero, relArgs, modelBin,
      modelProjection, relPayload, modelBin, modelProjection, modelProjection]
    rw [modelPairCode,modelPairCode,modelPairCode]
    rfl
  rw [he, ←modelAddOne]
  rfl

theorem modelRelGraph (arity sym vec : M) :
    qqRelDef.val.Evalb ![Structure.func (L := language) relCode ![arity,sym,vec],arity,sym,vec] := by
  rw [modelRelValue]
  simp [qqRelDef, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]
end models

noncomputable def relGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func relCode ![#0,#1,#2],#0,#1,#2] : Rew language Empty 4 Empty 3) ▹
    Semiformula.lMap embedding qqRelDef.val : Semisentence language 3)

theorem PRA_proves_relGraph : PRA ⊢ relGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, relGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_three e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1,e 2] Empty.elim ∘
      Rew.embSubsts ![.func relCode ![#0,#1,#2],#0,#1,#2] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) relCode ![e 0,e 1,e 2],e 0,e 1,e 2] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      refine Fin.cases (by simp) (fun l => ?_) k
      exact Fin.cases (by simp) (fun m => Fin.elim0 m) l
  have he : (Semiterm.val (L := language) ![e 0,e 1,e 2] Empty.elim ∘
      Rew.embSubsts ![.func relCode ![#0,#1,#2],#0,#1,#2] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelRelGraph (e 0) (e 1) (e 2)

#print axioms PRA_proves_relGraph
#print axioms modelRelValue
#print axioms modelRelGraph
end PA194RelCode
