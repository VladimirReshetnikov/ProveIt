import PA194FVarCode
import DiophantineConsistency.PRAHistorySeqConsCode

/-! A two-entry HFS sequence of Foundation free-variable codes. This sequence
is not yet shown to be Foundation's `Vec.adjoin` term-vector encoding. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194VarVectorCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHistoryPairCode PRAAddOne
  PRAModelIOpenPairing PRAHistorySeqConsCode PA194FVarCode

def varAt (i : Fin 2) : Code 2 := .comp fvarCode (.cons (.proj i) (.nil 2))
def firstVec (cons : Code 2) : Code 2 := bin cons (.zero 2) (varAt 0)
def varVectorCode (cons : Code 2) : Code 2 := bin cons (firstVec cons) (varAt 1)

noncomputable def varVectorGraph : ArithmeticSemisentence 3 :=
  “out a b. ∃ va vb mid, !qqFvarDef va a ∧ !qqFvarDef vb b ∧
    !seqConsDef mid 0 va ∧ !seqConsDef out mid vb”

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

theorem modelConsGraph (cons : Code 2) (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (s x : M) :
    seqConsDef.val.Evalb ![Structure.func (L := language) cons ![s,x],s,x] := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcons
  simp only [models_iff, PRAHistorySeqConsCode.graphSentence, Semiformula.eval_allClosure] at hm
  have hm := hm ![s,x]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard] at hm
  have hv : (Semiterm.val (L := language) ![s,x] Empty.elim ∘ graphRew cons ∘ Semiterm.bvar) =
      ![Structure.func (L := language) cons ![s,x],s,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [graphRew, Semiterm.val_func]
    · refine Fin.cases (by simp [graphRew]) (fun k => ?_) j
      exact Fin.cases (by simp [graphRew]) (fun k => Fin.elim0 k) k
  have he : (Semiterm.val (L := language) ![s,x] Empty.elim ∘ graphRew cons ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he] at hm
  exact hm

theorem modelVarVectorGraph (cons : Code 2) (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (a b : M) :
    varVectorGraph.Eval ![Structure.func (L := language) (varVectorCode cons) ![a,b],a,b] Empty.elim := by
  let va := Structure.func (L := language) fvarCode (fun _ => a)
  let vb := Structure.func (L := language) fvarCode (fun _ => b)
  let mid := Structure.func (L := language) cons ![0,va]
  have ha := modelFvarGraph a
  have hb := modelFvarGraph b
  have hmid := modelConsGraph cons hcons 0 va
  have hend := modelConsGraph cons hcons mid vb
  have he : Structure.func (L := language) (varVectorCode cons) ![a,b] =
      Structure.func (L := language) cons ![mid,vb] := by
    rw [varVectorCode,modelBin,firstVec,modelBin,modelVarAt,modelVarAt, PRAMultiplication.modelZero]
    rfl
  rw [he]
  simp only [varVectorGraph, Semiformula.eval_ex]
  refine ⟨va,vb,mid, ?_⟩
  simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_substs]
  have hv1 : (Semiterm.val (L := ℒₒᵣ) ![mid,vb,va,Structure.func (L := language) cons ![mid,vb],a,b] Empty.elim ∘ ![#2,#4]) = ![va,a] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hv2 : (Semiterm.val (L := ℒₒᵣ) ![mid,vb,va,Structure.func (L := language) cons ![mid,vb],a,b] Empty.elim ∘ ![#1,#5]) = ![vb,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hv3 : (Semiterm.val (L := ℒₒᵣ) ![mid,vb,va,Structure.func (L := language) cons ![mid,vb],a,b] Empty.elim ∘ ![#0,‘0’,#2]) = ![mid,0,va] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => ?_) j
    · change Structure.func (L := language) (Code.zero 0) Fin.elim0 = 0
      rfl
    · exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hv4 : (Semiterm.val (L := ℒₒᵣ) ![mid,vb,va,Structure.func (L := language) cons ![mid,vb],a,b] Empty.elim ∘ ![#3,#0,#1]) =
      ![Structure.func (L := language) cons ![mid,vb],mid,vb] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv1,hv2,hv3,hv4]
  exact ⟨ha,hb,hmid,hend⟩
end models

noncomputable def varVectorGraphSentence (cons : Code 2) : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func (varVectorCode cons) ![#0,#1],#0,#1] : Rew language Empty 3 Empty 2) ▹
    Semiformula.lMap embedding varVectorGraph : Semisentence language 2)

theorem PRA_proves_varVectorGraph (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) :
    PRA ⊢ varVectorGraphSentence cons := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, varVectorGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func (varVectorCode cons) ![#0,#1],#0,#1] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (varVectorCode cons) ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      exact Fin.cases (by simp) (fun k => Fin.elim0 k) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func (varVectorCode cons) ![#0,#1],#0,#1] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelVarVectorGraph cons hcons (e 0) (e 1)

theorem PRA_has_varVectorCode : ∃ cons : Code 2,
    (PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) ∧ PRA ⊢ varVectorGraphSentence cons := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  exact ⟨cons,hcons,PRA_proves_varVectorGraph cons hcons⟩

#print axioms PRA_has_varVectorCode
#print axioms PRA_proves_varVectorGraph
#print axioms modelVarAt
#print axioms modelConsGraph
#print axioms modelVarVectorGraph
end PA194VarVectorCode
