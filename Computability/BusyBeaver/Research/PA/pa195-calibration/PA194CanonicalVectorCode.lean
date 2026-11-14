import PA194TagCode
import PA194FVarCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Typed

/-! Foundation's actual term vectors use HFS Vec.adjoin, not Seq.seqCons. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194CanonicalVectorCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
  PRAModelIOpenPairing PA194TagCode PA194FVarCode

def varAt (i : Fin 2) : Code 2 := .comp fvarCode (.cons (.proj i) (.nil 2))
def vectorTail : Code 2 := bin tagCode (varAt 1) (.zero 2)
/-- Exact Foundation `matrixToVec` code for two source variable terms. -/
def vectorCode : Code 2 := bin tagCode (varAt 0) vectorTail

noncomputable def vectorGraph : ArithmeticSemisentence 3 :=
  “out a b. ∃ va vb tail, !qqFvarDef va a ∧ !qqFvarDef vb b ∧
    !adjoinDef tail vb 0 ∧ !adjoinDef out va tail”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelVarAt (i : Fin 2) (a b : M) :
    Structure.func (L := language) (varAt i) ![a,b] =
      Structure.func (L := language) fvarCode (fun _ => (![a,b] : Fin 2 → M) i) := by
  rw [varAt,modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  exact modelProjection i ![a,b]

theorem modelVectorValue (a b : M) :
    Structure.func (L := language) vectorCode ![a,b] =
      pair (pair 1 a + 1) (pair (pair 1 b + 1) 0 + 1) + 1 := by
  rw [vectorCode,modelBin,vectorTail,modelBin,modelVarAt,modelVarAt,
    PRAMultiplication.modelZero,modelFvarValue,modelFvarValue,
    modelTagValue,modelTagValue]
  rfl

theorem modelVectorGraph (a b : M) :
    vectorGraph.Eval ![Structure.func (L := language) vectorCode ![a,b],a,b] Empty.elim := by
  let va := Structure.func (L := language) fvarCode (fun _ => a)
  let vb := Structure.func (L := language) fvarCode (fun _ => b)
  let tail := Structure.func (L := language) tagCode ![vb,0]
  let out := Structure.func (L := language) tagCode ![va,tail]
  have ha := modelFvarGraph a
  have hb := modelFvarGraph b
  have ht : adjoinDef.val.Evalb ![tail,vb,0] := by
    have h := modelTagGraph vb (0 : M)
    change adjoinDef.val.Evalb ![Structure.func (L := language) tagCode ![vb,0],vb,0] at h
    exact h
  have ho : adjoinDef.val.Evalb ![out,va,tail] := by
    have h := modelTagGraph va tail
    change adjoinDef.val.Evalb ![Structure.func (L := language) tagCode ![va,tail],va,tail] at h
    exact h
  have he : Structure.func (L := language) vectorCode ![a,b] = out := by
    rw [vectorCode,modelBin,vectorTail,modelBin,modelVarAt,modelVarAt,PRAMultiplication.modelZero]
    rfl
  rw [he]
  simp only [vectorGraph, Semiformula.eval_ex]
  refine ⟨va,vb,tail, ?_⟩
  simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_substs]
  have hv1 : (Semiterm.val (L := ℒₒᵣ) ![tail,vb,va,out,a,b] Empty.elim ∘ ![#2,#4]) = ![va,a] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hv2 : (Semiterm.val (L := ℒₒᵣ) ![tail,vb,va,out,a,b] Empty.elim ∘ ![#1,#5]) = ![vb,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hv3 : (Semiterm.val (L := ℒₒᵣ) ![tail,vb,va,out,a,b] Empty.elim ∘ ![#0,#1,‘0’]) = ![tail,vb,0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    change Structure.func (L := language) (Code.zero 0) Fin.elim0 = 0
    rfl
  have hv4 : (Semiterm.val (L := ℒₒᵣ) ![tail,vb,va,out,a,b] Empty.elim ∘ ![#3,#2,#0]) = ![out,va,tail] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv1,hv2,hv3,hv4]
  exact ⟨ha,hb,ht,ho⟩

end models

/-- The all-model numeric expression is Foundation's actual matrix-to-vector
code when its term-syntax interpretation is available. -/
theorem matchesFoundationMatrix {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : V) :
    matrixToVec ![Arithmetic.Bootstrapping.qqFvar a, Arithmetic.Bootstrapping.qqFvar b] =
      pair (pair 1 a + 1) (pair (pair 1 b + 1) 0 + 1) + 1 := by
  simp [matrixToVec, Arithmetic.Bootstrapping.qqFvar, adjoin_def]

noncomputable def vectorGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func vectorCode ![#0,#1],#0,#1] : Rew language Empty 3 Empty 2) ▹
    Semiformula.lMap embedding vectorGraph : Semisentence language 2)

theorem PRA_proves_vectorGraph : PRA ⊢ vectorGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, vectorGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func vectorCode ![#0,#1],#0,#1] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) vectorCode ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      exact Fin.cases (by simp) (fun k => Fin.elim0 k) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func vectorCode ![#0,#1],#0,#1] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelVectorGraph (e 0) (e 1)

#print axioms matchesFoundationMatrix
#print axioms PRA_proves_vectorGraph
#print axioms modelVectorValue
#print axioms modelVectorGraph
end PA194CanonicalVectorCode
