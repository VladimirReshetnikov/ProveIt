import DiophantineConsistency.PRASelectCode
set_option autoImplicit false
namespace DiophantineConsistency.PRATwoInductionTagCodes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASelectCode PRAMultiplication

/-- Ignore the third, induction-parameter argument. -/
def liftTwo (f : Code 2) : Code 3 := .comp f (.cons (.proj 0) (.cons (.proj 1) (.nil 3)))

def tagged (first second : Code 2) : Code 3 := selectAmong (.proj 2) (liftTwo second) (liftTwo first)
def zeroTag : Code 1 := .zero 1
def oneTag : Code 1 := .comp oneCode (.nil 1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelLiftTwo (f : Code 2) (x y c : M) :
    Structure.func (L := language) (liftTwo f) ![x,y,c] = Structure.func (L := language) f ![x,y] := by
  rw [liftTwo, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact modelProjection _ _
  · exact Fin.cases (modelProjection _ _) (fun i => Fin.elim0 i) i

theorem modelZeroTag (c : M) : Structure.func (L := language) zeroTag ![c] =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelZero (M := M) (n := 1) ![c]
  exact h

theorem modelOneTag (c : M) : Structure.func (L := language) oneTag ![c] =
    Structure.func (L := language) oneCode Fin.elim0 := by
  rw [oneTag, modelComposition]
  congr 1
  exact Subsingleton.elim _ _

theorem modelTaggedZero (first second : Code 2) (x y c : M) :
    Structure.func (L := language) (tagged first second)
      ![x,y,Structure.func (L := language) zeroTag ![c]] =
      Structure.func (L := language) (liftTwo first) ![x,y,c] := by
  rw [modelZeroTag, tagged, modelSelectAmong]
  rw [modelProjection]
  change Structure.func (L := language) selectCode ![Structure.func (L := language) (Code.zero 0) Fin.elim0,_,_] = _
  rw [modelSelectZero]
  exact (modelLiftTwo first x y _).trans (modelLiftTwo first x y c).symm

theorem modelTaggedOne (first second : Code 2) (x y c : M) :
    Structure.func (L := language) (tagged first second)
      ![x,y,Structure.func (L := language) oneTag ![c]] =
      Structure.func (L := language) (liftTwo second) ![x,y,c] := by
  rw [modelOneTag, tagged, modelSelectAmong]
  rw [modelProjection]
  change Structure.func (L := language) selectCode ![Structure.func (L := language) oneCode Fin.elim0,_,_] = _
  rw [modelSelectOne]
  exact (modelLiftTwo second x y _).trans (modelLiftTwo second x y c).symm
end models
/-- The exact object-language substitution identity used by the two-axiom
reduction. -/
def substitutionEquation (combined original : Code 3) (encode : Code 1) : Sentence language :=
  ∀⁰* (Semiformula.rel Language.ORing.Rel.eq
    ![.func combined ![#0,#1,.func encode ![#2]], .func original ![#0,#1,#2]] : Semisentence language 3)

theorem PRA_proves_zero_substitution (first second : Code 2) :
    PRA ⊢ substitutionEquation (tagged first second) (liftTwo first) zeroTag := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hPRA
  simp only [models_iff, substitutionEquation, Semiformula.eval_allClosure]
  intro e
  simp only [Semiformula.eval_rel, eqRel]
  have h := modelTaggedZero first second (e 0) (e 1) (e 2)
  change Structure.func (L := language) (tagged first second)
      (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func zeroTag ![#2]]) =
    Structure.func (L := language) (liftTwo first) (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2])
  have ha : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func zeroTag ![#2]]) =
      ![e 0,e 1,Structure.func (L := language) zeroTag ![e 2]] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    change Structure.func (L := language) zeroTag (Semiterm.val e Empty.elim ∘ ![#2]) = _
    congr 1
    funext i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  have hb : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2]) = ![e 0,e 1,e 2] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  rw [ha,hb]
  exact h

theorem PRA_proves_one_substitution (first second : Code 2) :
    PRA ⊢ substitutionEquation (tagged first second) (liftTwo second) oneTag := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hPRA
  simp only [models_iff, substitutionEquation, Semiformula.eval_allClosure]
  intro e
  simp only [Semiformula.eval_rel, eqRel]
  have h := modelTaggedOne first second (e 0) (e 1) (e 2)
  change Structure.func (L := language) (tagged first second)
      (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func oneTag ![#2]]) =
    Structure.func (L := language) (liftTwo second) (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2])
  have ha : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,.func oneTag ![#2]]) =
      ![e 0,e 1,Structure.func (L := language) oneTag ![e 2]] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    change Structure.func (L := language) oneTag (Semiterm.val e Empty.elim ∘ ![#2]) = _
    congr 1
    funext i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  have hb : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#1,#2]) = ![e 0,e 1,e 2] := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  rw [ha,hb]
  exact h
end DiophantineConsistency.PRATwoInductionTagCodes
