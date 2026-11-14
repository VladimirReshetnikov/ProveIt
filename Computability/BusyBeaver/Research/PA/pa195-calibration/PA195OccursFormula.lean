import PA195PathBound
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA195OccursFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing

noncomputable def occurrenceMatrix : ArithmeticSemisentence 4 :=
  “node i limit v. i ≤ limit ∧ 0 < node ∧
    ∃ p a b, !divDef p node 4 ∧ !PA195FreshBound.cantorGraph p a b ∧ (v = a ∨ v = b)”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem occurrenceMatrix_eval (node i limit v : V) :
    occurrenceMatrix.Evalb ![node,i,limit,v] ↔
      i ≤ limit ∧ 0 < node ∧ (v = first (node / 4) ∨ v = second (node / 4)) := by
  have hdiv (p : V) : divDef.val.Evalb ![p,node,4] ↔ p = node / 4 := by
    simp [divDef, div_graph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
      le_iff_eq_or_lt]
  have hp (p a b : V) : PA195FreshBound.cantorGraph.val.Evalb ![p,a,b] ↔ p = cantor a b := by
    simp [PA195FreshBound.cantorGraph, SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef,
      cantor_graph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  simp [occurrenceMatrix, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
    le_iff_eq_or_lt, hdiv, hp]
  intro _ _
  constructor
  · rintro ⟨a, b, he, hv⟩
    have hh := cantor_injective ((cantor_projections (node / 4)).trans he)
    simpa [←hh.1, ←hh.2] using hv
  · intro hv
    exact ⟨first (node / 4), second (node / 4), (cantor_projections (node / 4)).symm, hv⟩

/-- Formula for the explicit path-occurrence over-approximation, parameterized
by the supplied primitive-recursive path-value code. -/
def occursRew (f : Code 2) : Rew language Empty 4 Empty 4 :=
  Rew.embSubsts ![.func f ![#1,#0], #0, #2, #3]

noncomputable def pathOccursFormula (f : Code 2) : Semisentence language 3 :=
  ∃⁰ (occursRew f ▹ Semiformula.lMap embedding occurrenceMatrix)

/-- The matrix checks one successor is an exact quotient/Cantor child. -/
def stepRew (f : Code 2) : Rew language Empty 4 Empty 3 :=
  Rew.embSubsts ![.func f ![#1,#0], #0, #2,
    .func f ![#1,.func addCode ![#0,.func oneCode Fin.elim0]]]

noncomputable def stepsFormula (f : Code 2) : Semisentence language 2 :=
  ∀⁰ (∼(Semiformula.rel Language.ORing.Rel.lt ![#0,#2]) ⋎
    (stepRew f ▹ Semiformula.lMap embedding occurrenceMatrix))

def rootRew (f : Code 2) : Rew language Empty 3 Empty 2 :=
  Rew.embSubsts ![#0,#1,.func f ![#0,.func (Code.zero 0) Fin.elim0]]

noncomputable def freshnessFormula (f : Code 2) : Semisentence language 2 :=
  stepsFormula f 🡒 ∼(rootRew f ▹ pathOccursFormula f)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem pathOccursFormula_eval (f : Code 2) (seed limit label : M) :
    (pathOccursFormula f).Eval ![seed,limit,label] Empty.elim ↔
      PA195PathBound.PathOccurs f seed limit label := by
  simp only [pathOccursFormula, Semiformula.eval_ex, Semiformula.eval_rew]
  apply exists_congr
  intro i
  have hv : (Semiterm.val (L := language) ![i,seed,limit,label] Empty.elim ∘
      occursRew f ∘ Semiterm.bvar) = ![PA195PathBound.pathValue f seed i,i,limit,label] := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [occursRew, PA195PathBound.pathValue, Semiterm.val_func]
    · refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
  have hf : (Semiterm.val (L := language) ![i,seed,limit,label] Empty.elim ∘
      occursRew f ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv, hf, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simpa [PA195PathBound.PathOccurs] using
    (occurrenceMatrix_eval (PA195PathBound.pathValue f seed i) i limit label)
theorem stepMatrix_eval (f : Code 2) (i seed limit : M) :
    (stepRew f ▹ Semiformula.lMap embedding occurrenceMatrix).Eval ![i,seed,limit] Empty.elim ↔
      i ≤ limit ∧ 0 < PA195PathBound.pathValue f seed i ∧
      (PA195PathBound.pathValue f seed (i+1) = first (PA195PathBound.pathValue f seed i / 4) ∨
       PA195PathBound.pathValue f seed (i+1) = second (PA195PathBound.pathValue f seed i / 4)) := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![i,seed,limit] Empty.elim ∘
      stepRew f ∘ Semiterm.bvar) =
      ![PA195PathBound.pathValue f seed i, i, limit, PA195PathBound.pathValue f seed (i+1)] := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [stepRew, PA195PathBound.pathValue, Semiterm.val_func]
    · refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun l => ?_) k
      refine Fin.cases ?_ (fun m => Fin.elim0 m) l
      simp [stepRew, PA195PathBound.pathValue, Semiterm.val_func]
      have hz : (Semiterm.val (L := language) ![i,seed,limit] Empty.elim ∘ Fin.elim0) =
          (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [hz]
      rfl
  have hf : (Semiterm.val (L := language) ![i,seed,limit] Empty.elim ∘
      stepRew f ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv, hf, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  exact occurrenceMatrix_eval _ _ _ _

theorem stepsFormula_eval (f : Code 2) (seed limit : M) :
    (stepsFormula f).Eval ![seed,limit] Empty.elim ↔
      ∀ i < limit, 0 < PA195PathBound.pathValue f seed i ∧
        (PA195PathBound.pathValue f seed (i+1) = first (PA195PathBound.pathValue f seed i / 4) ∨
         PA195PathBound.pathValue f seed (i+1) = second (PA195PathBound.pathValue f seed i / 4)) := by
  simp [stepsFormula, Semiformula.eval_all, stepMatrix_eval]
  constructor
  · intro h i hi
    have hh := h i
    change ¬(i < limit) ∨ _ at hh
    rcases hh with hh | hh
    · exact False.elim (hh hi)
    · exact hh.2
  · intro h i
    by_cases hi : i < limit
    · right
      exact ⟨le_of_lt hi, h i hi⟩
    · left
      exact hi

theorem rootFormula_eval (f : Code 2) (seed limit : M) :
    (rootRew f ▹ pathOccursFormula f).Eval ![seed,limit] Empty.elim ↔
      PA195PathBound.PathOccurs f seed limit (PA195PathBound.pathValue f seed 0) := by
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![seed,limit] Empty.elim ∘
      rootRew f ∘ Semiterm.bvar) = ![seed,limit,PA195PathBound.pathValue f seed 0] := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    simp [rootRew, PA195PathBound.pathValue, Semiterm.val_func]
    have hz : (Semiterm.val (L := language) ![seed,limit] Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hz]
    rfl
  have hf : (Semiterm.val (L := language) ![seed,limit] Empty.elim ∘
      rootRew f ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv, hf, pathOccursFormula_eval]

/-- Under the step hypothesis, represented path occurrence cannot name the root. -/
theorem represented_path_self_fresh (f : Code 2) (seed limit : M)
    (hstep : ∀ i < limit, 0 < PA195PathBound.pathValue f seed i ∧
      (PA195PathBound.pathValue f seed (i+1) = first (PA195PathBound.pathValue f seed i / 4) ∨
       PA195PathBound.pathValue f seed (i+1) = second (PA195PathBound.pathValue f seed i / 4))) :
    ¬ (pathOccursFormula f).Eval ![seed,limit,PA195PathBound.pathValue f seed 0] Empty.elim := by
  rw [pathOccursFormula_eval]
  exact PA195PathBound.path_self_fresh f seed limit hstep

end models

/-- Candidate PRA proves freshness for the explicitly represented path
predicate, conditional on its represented child-step premise. This does not
identify it with PA194's full recursive occurrence predicate. -/
theorem candidate_pra_represented_path_fresh (f : Code 2) :
    PRA ⊢ ∀⁰* freshnessFormula f := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  have h (seed limit : M) : (stepsFormula f).Eval ![seed,limit] Empty.elim →
      ¬ (rootRew f ▹ pathOccursFormula f).Eval ![seed,limit] Empty.elim := by
    intro hs
    rw [rootFormula_eval]
    exact PA195PathBound.path_self_fresh f seed limit ((stepsFormula_eval f seed limit).mp hs)
  have he : e = ![e 0,e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he]
  simpa [freshnessFormula] using h (e 0) (e 1)

#print axioms candidate_pra_represented_path_fresh
#print axioms represented_path_self_fresh
#print axioms pathOccursFormula_eval
#print axioms occurrenceMatrix_eval
end PA195OccursFormula
