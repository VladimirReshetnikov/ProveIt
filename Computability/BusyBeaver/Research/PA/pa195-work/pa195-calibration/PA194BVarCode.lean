import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic

/-! A certified primitive-recursive constructor for Foundation bound-variable
term codes. This is one atomic component of the source-to-PA translator. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194BVarCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing

def zeroUnary : Code 1 := .zero 1
def pairZeroCode : Code 1 := bin pairCode zeroUnary (.proj 0)
def bvarCode : Code 1 := .comp Code.succ (.cons pairZeroCode (.nil 1))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelBvarValue (x : M) :
    Structure.func (L := language) bvarCode (fun _ => x) = pair 0 x + 1 := by
  rw [bvarCode, modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons pairZeroCode (.nil 1)) i) (fun _ => x)) =
      (fun _ : Fin 1 => pair 0 x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) pairZeroCode (fun _ => x) = _
    rw [pairZeroCode,modelBin,modelProjection]
    have h : Structure.func (L := language) zeroUnary (fun _ => x)= 0 := by
      exact PRAMultiplication.modelZero _
    rw [h]
    exact modelPairCode 0 x
  rw [he, ←modelAddOne]
  rfl

theorem modelBvarGraph (x : M) :
    qqBvarDef.val.Evalb ![Structure.func (L := language) bvarCode (fun _ => x),x] := by
  rw [modelBvarValue]
  have hp (a b c : M) : pairDef.val.Evalb ![a,b,c] ↔ a = pair b c := pair_defined.defined ![a,b,c]
  simp [qqBvarDef, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hp]
end models

noncomputable def bvarGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func bvarCode ![#0],#0] : Rew language Empty 2 Empty 1) ▹
    Semiformula.lMap embedding qqBvarDef.val : Semisentence language 1)

theorem PRA_proves_bvarGraph : PRA ⊢ bvarGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, bvarGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) e Empty.elim ∘
      Rew.embSubsts ![.func bvarCode ![#0],#0] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) bvarCode (fun _ => e 0), e 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Rew.embSubsts_bvar, Matrix.cons_val_zero, Semiterm.val_func,
        Function.comp_def]
      congr 1
      funext j
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have he : (Semiterm.val (L := language) e Empty.elim ∘
      Rew.embSubsts ![.func bvarCode ![#0],#0] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelBvarGraph (e 0)

#print axioms PRA_proves_bvarGraph
#print axioms modelBvarValue
#print axioms modelBvarGraph
end PA194BVarCode
