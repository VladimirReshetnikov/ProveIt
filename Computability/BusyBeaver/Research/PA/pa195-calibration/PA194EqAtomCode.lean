import PA194CanonicalAtomCode

/-! Represented Foundation equality atom from two source labels. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194EqAtomCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PA194CanonicalAtomCode

/-- Foundation's relation symbol encoding fixes equality to code zero. -/
theorem equalitySymbolCode : Encodable.encode Language.ORing.Rel.eq = 0 := by decide

def oneTwoArgs : Code 2 := .comp oneCode (.nil 2)
def twoTwoArgs : Code 2 := .comp Code.succ (.cons oneTwoArgs (.nil 2))
/-- Bind the generic atom constructor to arity two and equality symbol zero. -/
def eqAtomCode : Code 2 := .comp atomCode
  (.cons twoTwoArgs (.cons (.zero 2) (.cons (.proj 0) (.cons (.proj 1) (.nil 2)))))

noncomputable def eqAtomGraph : ArithmeticSemisentence 3 :=
  “out a b. !atomGraph out 2 0 a b”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelTwo (a b : M) : Structure.func (L := language) twoTwoArgs ![a,b] = 2 := by
  rw [twoTwoArgs,modelComposition]
  have he : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons oneTwoArgs (.nil 2)) i) ![a,b]) = (fun _ : Fin 1 => (1 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) oneTwoArgs ![a,b] = _
    rw [oneTwoArgs,modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  rw [he, ←modelAddOne]
  change (1 : M) + 1 = 2
  norm_num

theorem modelEqAtomValue (a b : M) :
    Structure.func (L := language) eqAtomCode ![a,b] =
      Structure.func (L := language) atomCode ![2,0,a,b] := by
  rw [eqAtomCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelTwo a b
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact PRAMultiplication.modelZero ![a,b]
    · refine Fin.cases (modelProjection 0 ![a,b]) (fun l => ?_) k
      exact Fin.cases (modelProjection 1 ![a,b]) (fun m => Fin.elim0 m) l

theorem modelEqAtomGraph (a b : M) : eqAtomGraph.Eval
      ![Structure.func (L := language) eqAtomCode ![a,b],a,b] Empty.elim := by
  rw [modelEqAtomValue]
  have h := modelAtomGraph 2 0 a b
  unfold eqAtomGraph
  rw [Semiformula.eval_substs]
  have hv : (Semiterm.val (L := ℒₒᵣ) ![Structure.func (L := language) atomCode ![2,0,a,b],a,b] Empty.elim ∘
      ![#0,‘2’,‘0’,#1,#2]) = ![Structure.func (L := language) atomCode ![2,0,a,b],2,0,a,b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => ?_) j
    · simp []
    · refine Fin.cases ?_ (fun l => ?_) k
      · rfl
      · refine Fin.cases rfl (fun m => ?_) l
        exact Fin.cases rfl (fun n => Fin.elim0 n) m
  rw [hv]
  exact h
/-- In IΣ₁ models, this value agrees with Foundation's actual equality
relation constructor applied to its two free-variable term codes. -/
theorem modelEqAtomMatchesFoundation [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) :
    Structure.func (L := language) eqAtomCode ![a,b] =
      Arithmetic.Bootstrapping.qqRel 2 0
        (matrixToVec ![Arithmetic.Bootstrapping.qqFvar a, Arithmetic.Bootstrapping.qqFvar b]) := by
  rw [modelEqAtomValue]
  exact modelAtomMatchesFoundation 2 0 a b

end models

noncomputable def eqAtomGraphSentence : Sentence language := ∀⁰*
  ((Rew.embSubsts ![.func eqAtomCode ![#0,#1],#0,#1] : Rew language Empty 3 Empty 2) ▹
    Semiformula.lMap embedding eqAtomGraph : Semisentence language 2)

theorem PRA_proves_eqAtomGraph : PRA ⊢ eqAtomGraphSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, eqAtomGraphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  rw [Semiformula.eval_rew, Semiformula.eval_lMap, reduct_eq_standard]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func eqAtomCode ![#0,#1],#0,#1] ∘ Semiterm.bvar) =
      ![Structure.func (L := language) eqAtomCode ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.val_func]
    · refine Fin.cases (by simp) (fun k => ?_) j
      exact Fin.cases (by simp) (fun k => Fin.elim0 k) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      Rew.embSubsts ![.func eqAtomCode ![#0,#1],#0,#1] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelEqAtomGraph (e 0) (e 1)

#print axioms PRA_proves_eqAtomGraph
#print axioms modelEqAtomMatchesFoundation
#print axioms equalitySymbolCode
#print axioms modelTwo
#print axioms modelEqAtomValue
#print axioms modelEqAtomGraph
end PA194EqAtomCode
