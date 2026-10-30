import DiophantineConsistency.PRAModelIOpenPairing
import DiophantineConsistency.PRAPrimitiveRecursionInduction
import DiophantineConsistency.PRABoundedWitness
import DiophantineConsistency.ParsonsHierarchyMap
import Foundation.FirstOrder.Arithmetic.Exponential.Exp
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryExpCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
  PRAPrimitiveRecursionInduction PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
  PRAModelISigmaZero PRAModelIOpenPairing

def doubleStep : Code 2 := .comp addCode (.cons (.proj 1) (.cons (.proj 1) (.nil 2)))
def expCode : Code 1 := .prec oneCode doubleStep
def expGraph : Semisentence language 2 := Semiformula.lMap embedding exponentialDef.val

theorem expGraph_bounded : Hierarchy 𝚺 0 expGraph :=
  ParsonsHierarchyMap.hierarchy exponentialDef.sigma_prop

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem graph_iff (a b : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := modelReductISigmaZero (M := M)
      rw [reduct_eq_standard] at h
      exact h
    expGraph.Eval ![a,b] Empty.elim ↔ Exponential a b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := modelReductISigmaZero (M := M)
    rw [reduct_eq_standard] at h
    exact h
  have hh : Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding)
      ![a,b] Empty.elim exponentialDef.val ↔
      Semiformula.Eval (s := Arithmetic.standardModel M) ![a,b] Empty.elim exponentialDef.val := by
    rw [reduct_eq_standard]
  rw [expGraph, Semiformula.eval_lMap]
  exact hh.trans (Exponential.defined.defined ![a,b])

theorem modelDoubleStep (a b : M) :
    Structure.func (L := language) doubleStep ![a,b] = b+b := by
  rw [doubleStep, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection _ _
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact modelProjection _ _

theorem modelExpCode (x : M) : expGraph.Eval
    ![x,Structure.func (L := language) expCode (fun _ => x)] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := modelReductISigmaZero (M := M)
    rw [reduct_eq_standard] at h
    exact h
  obtain ⟨pred,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic expGraph expGraph_bounded
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  have eqGraph (a b : M) :
      Structure.func (L := language) pred ![a,b] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ Exponential a b := by
    have h := modelCharacteristicMatrix pred expGraph hm ![a,b]
    have hz : (Semiterm.val (L := language) ![a,b] Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have hv : (Semiterm.val (L := language) ![a,b] Empty.elim ∘ vars 2) = ![a,b] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    simpa [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode,
      Semiterm.val_func, hz, hv, graph_iff] using h
  have hbase : Structure.func (L := language) pred
      (Fin.cases (0 : M) (Fin.cases (1 : M) (fun i : Fin 0 => Fin.elim0 i))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
    apply (eqGraph 0 1).mpr
    exact Or.inl ⟨rfl,rfl⟩
  have hstep : ∀ a b : M, Structure.func (L := language) pred
      (Fin.cases a (Fin.cases b (fun i : Fin 0 => Fin.elim0 i))) =
        Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred (Fin.cases (Structure.func (L := language) Code.succ (fun _ => a))
        (Fin.cases (Structure.func (L := language) doubleStep (Fin.cases a (Fin.cases b (fun i : Fin 0 => Fin.elim0 i))))
          (fun i : Fin 0 => Fin.elim0 i))) = Structure.func (L := language) oneCode Fin.elim0 := by
    intro a b h
    have hg : Exponential a b := (eqGraph a b).mp h
    have hdouble := modelDoubleStep a b
    change Structure.func (L := language) doubleStep ![a,b] = b+b at hdouble
    change Structure.func (L := language) pred
      ![Structure.func (L := language) Code.succ (fun _ => a),
        Structure.func (L := language) doubleStep ![a,b]] = _
    rw [hdouble, ←modelAddOne]
    apply (eqGraph (a+1) (b+b)).mpr
    simpa [two_mul] using Exponential.succ hg
  have he : (fun _ : Fin 0 => x) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hb : Structure.func (L := language) pred
      (Fin.cases (0 : M) (Fin.cases (Structure.func (L := language) oneCode (fun _ : Fin 0 => x))
        (fun _ : Fin 0 => x))) = Structure.func (L := language) oneCode Fin.elim0 := by
    rw [he]
    exact hbase
  have hs : ∀ a b : M, Structure.func (L := language) pred
      (Fin.cases a (Fin.cases b (fun _ : Fin 0 => x))) =
        Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred (Fin.cases (Structure.func (L := language) Code.succ (fun _ => a))
        (Fin.cases (Structure.func (L := language) doubleStep (Fin.cases a (Fin.cases b (fun _ : Fin 0 => x))))
          (fun _ : Fin 0 => x))) = Structure.func (L := language) oneCode Fin.elim0 := by
    rw [he]
    exact hstep
  have hi := modelRecursiveWitness (M := M) pred oneCode doubleStep (fun _ => x) hb hs x
  rw [he] at hi
  have hx : Fin.cases x (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => x) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hx] at hi
  change Structure.func (L := language) pred
    ![x,Structure.func (L := language) expCode (fun _ => x)] = _ at hi
  exact (graph_iff x _).mpr ((eqGraph x _).mp hi)
def graphRew : Rew language Empty 2 Empty 1 := Rew.embSubsts
  ![#0,.func expCode ![#0]]

def graphSentence : Sentence language := ∀⁰* (graphRew ▹ expGraph)

theorem modelGraphSentence : M↓[language] ⊧ graphSentence := by
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_one e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ graphRew ∘ Semiterm.bvar) =
      ![e 0,Structure.func (L := language) expCode (fun _ => e 0)] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) expCode
      (Semiterm.val (L := language) ![e 0] Empty.elim ∘ ![#0]) = _
    congr 1
    funext k
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0] Empty.elim ∘ graphRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelExpCode (e 0)
end models

theorem PRA_proves_expCodeGraph : PRA ⊢ graphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelGraphSentence
end DiophantineConsistency.PRAHistoryExpCode
