import PA194StrongInduction
import PA195DecodedFields

/-! Conditional strong-induction freshness criterion for any fixed PR
occurrence code satisfying the PA194 numeric decoder's one-step coverage.
The actual occurrence-code constructor and its equations are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194OccurrenceStrong
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRABoundedFormula PRABoundedCharacteristic PA194StrongInduction

def goodFormula (occ : Code 2) : Semisentence language 2 :=
  (Semiformula.rel Language.ORing.Rel.lt ![#1,#0]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq ![.func occ ![#0,#1],.func (Code.zero 0) Fin.elim0])

theorem goodFormula_open (occ : Code 2) : (goodFormula occ).Open := by
  simp [goodFormula, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem goodFormula_eval (occ : Code 2) (n v : M) :
    (goodFormula occ).Eval ![n,v] Empty.elim ↔ v < n ∨ value occ n v = 0 := by
  have hz : (Semiterm.val (L := language) ![n,v] Empty.elim ∘
      (Fin.elim0 : Fin 0 → Semiterm language Empty 2)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [goodFormula, Semiformula.eval_rel, eqRel, Semiterm.val_func, value, hz]
  rfl

/-- If every positive result of a represented occurrence code is explained
by a direct field or one of its child results, every occurrence label is
strictly below its code. The premise is required uniformly for all model
codes and labels, including nonstandard ones. -/
theorem model_occurrence_bound (occ : Code 2)
    (hrec : ∀ n v : M, value occ n v ≠ 0 →
      0 < n ∧
      (v = first (n / 4) ∨ v = second (n / 4) ∨
       value occ (first (n / 4)) v ≠ 0 ∨ value occ (second (n / 4)) v ≠ 0)) :
    ∀ n v : M, value occ n v ≠ 0 → v < n := by
  obtain ⟨good, _, _, hcorrect⟩ := PRA_proves_boundedBooleanCharacteristic
    (goodFormula occ) (Hierarchy.of_open (goodFormula_open occ))
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect
  have hgood (n v : M) : value good n v = 1 ↔ v < n ∨ value occ n v = 0 := by
    have h := (oneCorrectSentence_iff good (goodFormula occ)).mp hm ![n,v]
    exact h.trans (goodFormula_eval occ n v)
  intro n v hnz
  have hall : ∀ n : M, value good n v = 1 := by
    apply modelStrongCode good v
    intro n ih
    apply (hgood n v).mpr
    by_cases hnv : n ≤ v
    · right
      by_contra hnz'
      obtain ⟨hnpos, hlabel1 | hlabel2 | hchild1 | hchild2⟩ := hrec n v hnz'
      · have hf := (PA195DecodedFields.decoded_fields_lt n hnpos).1
        rw [←hlabel1] at hf
        exact not_lt_of_ge hnv hf
      · have hf := (PA195DecodedFields.decoded_fields_lt n hnpos).2
        rw [←hlabel2] at hf
        exact not_lt_of_ge hnv hf
      · have hf := (PA195DecodedFields.decoded_fields_lt n hnpos).1
        have hg := (hgood _ v).mp (ih _ hf)
        rcases hg with hbad | hzero
        · exact not_lt_of_ge (le_trans (le_of_lt hf) hnv) hbad
        · exact hchild1 hzero
      · have hf := (PA195DecodedFields.decoded_fields_lt n hnpos).2
        have hg := (hgood _ v).mp (ih _ hf)
        rcases hg with hbad | hzero
        · exact not_lt_of_ge (le_trans (le_of_lt hf) hnv) hbad
        · exact hchild2 hzero
    · left
      exact lt_of_not_ge hnv
  have hr := (hgood n v).mp (hall n)
  exact hr.resolve_right hnz

/-- Under the same recursion-coverage hypothesis, the decoder's own code is
never reported as one of its variable labels. -/
theorem model_occurrence_self_fresh (occ : Code 2)
    (hrec : ∀ n v : M, value occ n v ≠ 0 →
      0 < n ∧
      (v = first (n / 4) ∨ v = second (n / 4) ∨
       value occ (first (n / 4)) v ≠ 0 ∨ value occ (second (n / 4)) v ≠ 0)) :
    ∀ n : M, value occ n n = 0 := by
  intro n
  by_contra hnz
  exact _root_.lt_irrefl n (model_occurrence_bound occ hrec n n hnz)
end models
#print axioms model_occurrence_bound
#print axioms model_occurrence_self_fresh
end PA194OccurrenceStrong
