import DiophantineConsistency.PRATwoInductionTagCodes
import DiophantineConsistency.PRAExhaustion
/-! Finite tagged dispatch for predicates without induction parameters. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteInductionTagCodes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRASelectCode PRATwoInductionTagCodes PRAMultiplication

/-- Feed a three-input code the predecessor of its third input. -/
def advance (f : Code 3) : Code 3 :=
  .comp f (.cons (.proj 0) (.cons (.proj 1)
    (.cons (.comp predCode (.cons (.proj 2) (.nil 3))) (.nil 3))))

/-- The c input is a finite tag. Each leaf ignores c. -/
def dispatch : List (Code 2) → Code 3
  | [] => .zero 3
  | f :: fs => selectAmong (.proj 2) (advance (dispatch fs)) (liftTwo f)

/-- A unary code for the closed numeral tag, ignoring its input. -/
def tagCode : ℕ → Code 1
  | 0 => .zero 1
  | k+1 => .comp Code.succ (.cons (tagCode k) (.nil 1))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

def tagValue : ℕ → M
  | 0 => Structure.func (L := language) (Code.zero 0) Fin.elim0
  | n+1 => Structure.func (L := language) Code.succ (fun _ => tagValue n)

theorem modelAdvance (f : Code 3) (x y c : M) :
    Structure.func (L := language) (advance f) ![x,y,c] =
      Structure.func (L := language) f ![x,y,Structure.func (L := language) predCode (fun _ => c)] := by
  rw [advance, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection _ _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection _ _
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change Structure.func (L := language) (.comp predCode (.cons (.proj 2) (.nil 3))) ![x,y,c] = _
      rw [modelComposition]
      congr 1
      funext i
      exact Fin.cases (modelProjection _ _) (fun j => Fin.elim0 j) i

theorem modelTagCode (k : ℕ) (c : M) :
    Structure.func (L := language) (tagCode k) ![c] = tagValue k := by
  induction k with
  | zero => exact modelZero _
  | succ k ih =>
    rw [tagCode, modelComposition]
    change Structure.func (L := language) Code.succ
      (fun i => Structure.func (L := language) (getCode (.cons (tagCode k) (.nil 1)) i) ![c]) =
      Structure.func (L := language) Code.succ (fun _ => tagValue k)
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact ih

theorem modelDispatch_zero (f : Code 2) (fs : List (Code 2)) (x y : M) :
    Structure.func (L := language) (dispatch (f::fs)) ![x,y,tagValue 0] =
      Structure.func (L := language) f ![x,y] := by
  rw [dispatch, modelSelectAmong, modelProjection]
  change Structure.func (L := language) selectCode
    ![Structure.func (L := language) (Code.zero 0) Fin.elim0,_,_] = _
  rw [modelSelectZero]
  exact modelLiftTwo f x y _

theorem modelDispatch_succ (f : Code 2) (fs : List (Code 2)) (x y : M) (k : ℕ) :
    Structure.func (L := language) (dispatch (f::fs)) ![x,y,tagValue (k+1)] =
      Structure.func (L := language) (dispatch fs) ![x,y,tagValue k] := by
  rw [dispatch, modelSelectAmong, modelProjection]
  change Structure.func (L := language) selectCode
    ![Structure.func (L := language) Code.succ (fun _ => tagValue k),_,_] = _
  rw [modelSelectSucc, modelAdvance]
  change Structure.func (L := language) (dispatch fs)
    ![x,y,Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) Code.succ (fun _ => tagValue k))] = _
  rw [modelPredSucc]

theorem modelDispatch_get (fs : List (Code 2)) (i : Fin fs.length) (x y : M) :
    Structure.func (L := language) (dispatch fs) ![x,y,tagValue i.val] =
      Structure.func (L := language) (fs.get i) ![x,y] := by
  induction fs with
  | nil => exact Fin.elim0 i
  | cons f fs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelDispatch_zero f fs x y
    · simpa using (modelDispatch_succ f fs x y j.val).trans (ih j)
end models

/-- The dispatcher substitution for each list member has a closed actual
candidate-PRA proof, uniformly in all x, y and c. -/
theorem PRA_proves_dispatch_substitution (fs : List (Code 2)) (i : Fin fs.length) :
    PRA ⊢ substitutionEquation (dispatch fs) (liftTwo (fs.get i)) (tagCode i.val) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, substitutionEquation, Semiformula.eval_allClosure]
  intro e
  simp only [Semiformula.eval_rel, eqRel]
  change Structure.func (L := language) (dispatch fs)
      (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func (tagCode i.val) ![#2]]) =
    Structure.func (L := language) (liftTwo (fs.get i))
      (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2])
  have ha : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func (tagCode i.val) ![#2]]) =
      ![e 0,e 1,Structure.func (L := language) (tagCode i.val) ![e 2]] := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change Structure.func (L := language) (tagCode i.val) (Semiterm.val e Empty.elim ∘ ![#2]) = _
    congr 1
    funext j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hb : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2]) = ![e 0,e 1,e 2] := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  rw [ha,hb,modelTagCode,modelDispatch_get,modelLiftTwo]
end DiophantineConsistency.PRAFiniteInductionTagCodes
