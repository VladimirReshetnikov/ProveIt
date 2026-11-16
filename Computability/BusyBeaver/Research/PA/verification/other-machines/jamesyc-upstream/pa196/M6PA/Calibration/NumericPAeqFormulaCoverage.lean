module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaAtomParameters
@[expose] public section

/-! A conservative finite free-environment coverage invariant. The code bound
is sufficient, not necessary; existence of a sufficiently long environment is
not assumed here. All source and target context arities are explicit. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def FormulaCovered (s n param p : V) : Prop :=
  ParametersValid s n param ∧ IsSemiformula Presentation.language s p ∧ p≤len (nth param 1)
noncomputable def coverageGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s n param p. ∃ b f k, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !lenDef k f ∧
    !((isSemitermVec language).sigma) s n b ∧ !((isSemitermVec language).sigma) k n f ∧
    !((isSemiformula Presentation.language).sigma) s p ∧ p≤k”
theorem coverage_graph (s n param p : V) :
    coverageGraph.val.Evalb ![s,n,param,p] ↔ FormulaCovered s n param p := by
  simp [coverageGraph,FormulaCovered,ParametersValid,Matrix.comp_vecCons'',and_assoc]

theorem coverage_all {s n param p : V} (h : FormulaCovered s n param (qqAll p)) :
    FormulaCovered (s+1) (n+1) (binderParameters param) p := by
  refine ⟨binderParameters_valid h.1,IsSemiformula.all.mp h.2.1,?_⟩
  have hf := NumericPAeqTerm.shiftTerms_length h.1.2
  simp only [binderParameters,parameters_free]
  rw [hf]
  exact le_trans (lt_forall p).le h.2.2

theorem coverage_exs {s n param p : V} (h : FormulaCovered s n param (qqExs p)) :
    FormulaCovered (s+1) (n+1) (binderParameters param) p := by
  refine ⟨binderParameters_valid h.1,IsSemiformula.exs.mp h.2.1,?_⟩
  have hf := NumericPAeqTerm.shiftTerms_length h.1.2
  simp only [binderParameters,parameters_free]
  rw [hf]
  exact le_trans (lt_exists p).le h.2.2

theorem coverage_and {s n param p q : V} (h : FormulaCovered s n param (qqAnd p q)) :
    FormulaCovered s n param p ∧ FormulaCovered s n param q := by
  have hpq := IsSemiformula.and.mp h.2.1
  exact ⟨⟨h.1,hpq.1,le_trans (lt_K!_left p q).le h.2.2⟩,
    ⟨h.1,hpq.2,le_trans (lt_K!_right p q).le h.2.2⟩⟩
theorem coverage_or {s n param p q : V} (h : FormulaCovered s n param (qqOr p q)) :
    FormulaCovered s n param p ∧ FormulaCovered s n param q := by
  have hpq := IsSemiformula.or.mp h.2.1
  exact ⟨⟨h.1,hpq.1,le_trans (lt_or_left p q).le h.2.2⟩,
    ⟨h.1,hpq.2,le_trans (lt_or_right p q).le h.2.2⟩⟩

theorem coverage_rel {s n param k r ts : V} (h : FormulaCovered s n param (qqRel k r ts)) :
    k=2 ∧ r=0 ∧ IsSemitermVec Presentation.language 2 s ts ∧
    (∀i,i<2→nth ts i≤len (nth param 1)) := by
  obtain ⟨hr,ht⟩ := IsSemiformula.rel.mp h.2.1
  obtain ⟨hk,htag⟩ := (Presentation.source_relations k r).mp hr
  subst k
  refine ⟨rfl,htag,ht,?_⟩
  intro i hi
  exact le_trans (nth_lt_qqRel_of_lt (by rw [ht.lh]; exact hi)).le h.2.2

theorem coverage_nrel {s n param k r ts : V} (h : FormulaCovered s n param (qqNRel k r ts)) :
    k=2 ∧ r=0 ∧ IsSemitermVec Presentation.language 2 s ts ∧
    (∀i,i<2→nth ts i≤len (nth param 1)) := by
  obtain ⟨hr,ht⟩ := IsSemiformula.nrel.mp h.2.1
  obtain ⟨hk,htag⟩ := (Presentation.source_relations k r).mp hr
  subst k
  refine ⟨rfl,htag,ht,?_⟩
  intro i hi
  exact le_trans (nth_lt_qqNRel_of_lt (by rw [ht.lh]; exact hi)).le h.2.2

#print axioms coverage_graph
#print axioms coverage_all
#print axioms coverage_exs
#print axioms coverage_and
#print axioms coverage_or
#print axioms coverage_rel
#print axioms coverage_nrel
end M6.PA.NumericPAeqFormula

