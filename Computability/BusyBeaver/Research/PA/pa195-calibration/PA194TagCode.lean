import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic

/-! Certified primitive-recursive Foundation syntax tag construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194TagCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing

/-- Foundation's single-payload tagged syntax code, `pair(tag,payload)+1`. -/
def tagCode : Code 2 := .comp Code.succ (.cons pairCode (.nil 2))

noncomputable def tagGraph : ArithmeticSemisentence 3 :=
  “r tag payload. ∃ p < r, !pairDef p tag payload ∧ r = p + 1”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelTagValue (tag payload : M) :
    Structure.func (L := language) tagCode ![tag,payload] = pair tag payload + 1 := by
  rw [tagCode,modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons pairCode (.nil 2)) i) ![tag,payload]) =
      (fun _ : Fin 1 => pair tag payload) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelPairCode tag payload
  rw [he, ←modelAddOne]
  rfl

theorem modelTagGraph (tag payload : M) :
    tagGraph.Eval ![Structure.func (L := language) tagCode ![tag,payload],tag,payload] Empty.elim := by
  rw [modelTagValue]
  have hp (a b c : M) : pairDef.val.Evalb ![a,b,c] ↔ a = pair b c := pair_defined.defined ![a,b,c]
  simp [tagGraph, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hp]

theorem modelAllGraph (body : M) :
    qqAllDef.val.Evalb ![Structure.func (L := language) tagCode ![6,body],body] := by
  rw [modelTagValue]
  have hp (a b c : M) : pairDef.val.Evalb ![a,b,c] ↔ a = pair b c := pair_defined.defined ![a,b,c]
  simp [qqAllDef, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hp, numeral_eq_natCast]
end models

noncomputable def tagGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func tagCode ![#0,#1],#0,#1] : Rew language Empty 3 Empty 2) ▹
    Semiformula.lMap embedding tagGraph : Semisentence language 2)

theorem PRA_proves_tagGraph : PRA ⊢ tagGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, tagGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func tagCode ![#0,#1],#0,#1] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) tagCode ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      exact Fin.cases (by simp) (fun k => Fin.elim0 k) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func tagCode ![#0,#1],#0,#1] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelTagGraph (e 0) (e 1)

#print axioms PRA_proves_tagGraph
#print axioms modelTagValue
#print axioms modelTagGraph
#print axioms modelAllGraph
end PA194TagCode
