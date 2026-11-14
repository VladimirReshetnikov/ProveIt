import PA194RelCode
import PA194VarVectorCode

/-! Represented atomic relation translation from two source labels. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194AtomCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistorySeqConsCode PA194RelCode PA194VarVectorCode

def argsVector (cons : Code 2) : Code 4 :=
  .comp (varVectorCode cons) (.cons (.proj 2) (.cons (.proj 3) (.nil 4)))
/-- Input `[arity,symbol,a,b]`, building both source-label terms and a
Foundation relation formula. The intended atomic cases use arity two. -/
def atomCode (cons : Code 2) : Code 4 :=
  .comp relCode (.cons (.proj 0) (.cons (.proj 1) (.cons (argsVector cons) (.nil 4))))

noncomputable def atomGraph : ArithmeticSemisentence 5 :=
  “out arity sym a b. ∃ vec, !varVectorGraph vec a b ∧ !qqRelDef out arity sym vec”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelArgsVector (cons : Code 2) (arity sym a b : M) :
    Structure.func (L := language) (argsVector cons) ![arity,sym,a,b] =
      Structure.func (L := language) (varVectorCode cons) ![a,b] := by
  rw [argsVector,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 2 ![arity,sym,a,b]
  · exact Fin.cases (modelProjection 3 ![arity,sym,a,b]) (fun k => Fin.elim0 k) j

theorem modelAtomValue (cons : Code 2) (arity sym a b : M) :
    Structure.func (L := language) (atomCode cons) ![arity,sym,a,b] =
      Structure.func (L := language) relCode
        ![arity,sym,Structure.func (L := language) (varVectorCode cons) ![a,b]] := by
  rw [atomCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 ![arity,sym,a,b]
  · refine Fin.cases (modelProjection 1 ![arity,sym,a,b]) (fun k => ?_) j
    exact Fin.cases (modelArgsVector cons arity sym a b) (fun l => Fin.elim0 l) k

theorem modelAtomGraph (cons : Code 2) (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons)
    (arity sym a b : M) :
    atomGraph.Eval ![Structure.func (L := language) (atomCode cons) ![arity,sym,a,b],arity,sym,a,b] Empty.elim := by
  let vec := Structure.func (L := language) (varVectorCode cons) ![a,b]
  let out := Structure.func (L := language) relCode ![arity,sym,vec]
  have hv := modelVarVectorGraph cons hcons a b
  have hr := modelRelGraph arity sym vec
  rw [modelAtomValue]
  simp only [atomGraph, Semiformula.eval_ex]
  refine ⟨vec, ?_⟩
  simp only [LogicalConnective.HomClass.map_and, Semiformula.eval_substs]
  have hvec : (Semiterm.val (L := ℒₒᵣ) ![vec,out,arity,sym,a,b] Empty.elim ∘ ![#0,#4,#5]) = ![vec,a,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hrel : (Semiterm.val (L := ℒₒᵣ) ![vec,out,arity,sym,a,b] Empty.elim ∘ ![#1,#2,#3,#0]) = ![out,arity,sym,vec] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  rw [hvec,hrel]
  exact ⟨hv,hr⟩
end models

noncomputable def atomGraphSentence (cons : Code 2) : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func (atomCode cons) ![#0,#1,#2,#3],#0,#1,#2,#3] :
    Rew language Empty 5 Empty 4) ▹ Semiformula.lMap embedding atomGraph : Semisentence language 4)

theorem PRA_proves_atomGraph (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) : PRA ⊢ atomGraphSentence cons := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, atomGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_four e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1,e 2,e 3] Empty.elim ∘
      Rew.embSubsts ![.func (atomCode cons) ![#0,#1,#2,#3],#0,#1,#2,#3] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (atomCode cons) ![e 0,e 1,e 2,e 3],e 0,e 1,e 2,e 3] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      refine Fin.cases (by simp) (fun l => ?_) k
      refine Fin.cases (by simp) (fun m => ?_) l
      exact Fin.cases (by simp) (fun n => Fin.elim0 n) m
  have he : (Semiterm.val (L := language) ![e 0,e 1,e 2,e 3] Empty.elim ∘
      Rew.embSubsts ![.func (atomCode cons) ![#0,#1,#2,#3],#0,#1,#2,#3] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelAtomGraph cons hcons (e 0) (e 1) (e 2) (e 3)

theorem PRA_has_atomCode : ∃ cons : Code 2,
    (PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) ∧ PRA ⊢ atomGraphSentence cons := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  exact ⟨cons,hcons,PRA_proves_atomGraph cons hcons⟩

#print axioms PRA_has_atomCode
#print axioms PRA_proves_atomGraph
#print axioms modelAtomValue
#print axioms modelAtomGraph
end PA194AtomCode
