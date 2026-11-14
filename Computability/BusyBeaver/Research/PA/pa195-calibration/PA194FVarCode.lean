import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic

/-! A certified primitive-recursive constructor for Foundation free-variable
term codes. This is one atomic component of the source-to-PA translator. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194FVarCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing

def oneUnary : Code 1 := .comp oneCode (.nil 1)
def pairOneCode : Code 1 := bin pairCode oneUnary (.proj 0)
def fvarCode : Code 1 := .comp Code.succ (.cons pairOneCode (.nil 1))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelFvarValue (x : M) :
    Structure.func (L := language) fvarCode (fun _ => x) = pair 1 x + 1 := by
  rw [fvarCode, modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons pairOneCode (.nil 1)) i) (fun _ => x)) =
      (fun _ : Fin 1 => pair 1 x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) pairOneCode (fun _ => x) = _
    rw [pairOneCode,modelBin,modelProjection]
    have h : Structure.func (L := language) oneUnary (fun _ => x) = 1 := by
      rw [oneUnary,modelComposition]
      congr 1
      exact Subsingleton.elim _ _
    rw [h]
    exact modelPairCode 1 x
  rw [he, ←modelAddOne]
  rfl

theorem modelFvarGraph (x : M) :
    qqFvarDef.val.Evalb ![Structure.func (L := language) fvarCode (fun _ => x),x] := by
  rw [modelFvarValue]
  have hp (a b c : M) : pairDef.val.Evalb ![a,b,c] ↔ a = pair b c := pair_defined.defined ![a,b,c]
  simp [qqFvarDef, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hp]
end models

noncomputable def fvarGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func fvarCode ![#0],#0] : Rew language Empty 2 Empty 1) ▹
    Semiformula.lMap embedding qqFvarDef.val : Semisentence language 1)

theorem PRA_proves_fvarGraph : PRA ⊢ fvarGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, fvarGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) e Empty.elim ∘
      Rew.embSubsts ![.func fvarCode ![#0],#0] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) fvarCode (fun _ => e 0), e 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Rew.embSubsts_bvar, Matrix.cons_val_zero, Semiterm.val_func,
        Function.comp_def]
      congr 1
      funext j
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have he : (Semiterm.val (L := language) e Empty.elim ∘
      Rew.embSubsts ![.func fvarCode ![#0],#0] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelFvarGraph (e 0)

#print axioms PRA_proves_fvarGraph
#print axioms modelFvarValue
#print axioms modelFvarGraph
end PA194FVarCode
