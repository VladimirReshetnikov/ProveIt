module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentShiftSet
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Guarded finite term-label substitution environments for the existing
function-free relational source language. This is not native substitution. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- w substitutes source bound variables labeled by a with terms interpreted
under target bound/free environments b/f. Every lookup is explicitly in range. -/
def LabelSubstitution (w a b f : V) : Prop :=
  len w=len a ∧ ∀ i<len w, VariableLabel (nth a i) (nth w i) b f

attribute [local irreducible] variableLabelGraph
noncomputable def labelSubstitutionGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “w a b f. ∃ n, !lenDef n w ∧ !lenDef n a ∧
    ∀ i<n, ∃ y t, !nthDef y a i ∧ !nthDef t w i ∧ !variableLabelGraph y t b f”

theorem labelSubstitution_graph (w a b f : V) :
    labelSubstitutionGraph.val.Evalb ![w,a,b,f] ↔ LabelSubstitution w a b f := by
  simp [labelSubstitutionGraph,LabelSubstitution,variableLabel_graph,Matrix.comp_vecCons'',eq_comm]

theorem LabelSubstitution.isSemitermVec {w a b f : V} (h : LabelSubstitution w a b f) :
    IsSemitermVec language (len a) (len b) w := by
  apply IsSemitermVec.iff.mpr
  refine ⟨h.1,?_⟩
  intro i hi
  exact (label_covered (h.2 i (by simpa [h.1] using hi))).1

theorem totalLabel_termBShift (t b f x : V) (ht : IsUTerm language t) :
    totalLabel (termBShift language t) (x∷b) f=totalLabel t b f := by
  have hc : (∃ i, t=qqBvar i) ∨ ∃ i, t=qqFvar i := by
    simpa only [IsUTerm.case_iff,source_no_functions,false_and,exists_false,or_false] using ht
  rcases hc with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> simp

theorem variableLabel_termBShift {y t b f : V} (x : V) (h : VariableLabel y t b f) :
    VariableLabel y (termBShift language t) (x∷b) f := by
  rcases h with ⟨i,hi,rfl,rfl⟩ | ⟨i,hi,rfl,rfl⟩
  · simpa using label_bvar (x∷b) f (i+1) (by simpa using hi)
  · simpa using label_fvar (x∷b) f i hi

theorem LabelSubstitution.qVec {w a b f : V} (h : LabelSubstitution w a b f) (x : V) :
    LabelSubstitution (qVec language w) (x∷a) (x∷b) f := by
  have hw : IsUTermVec language (len w) w := by
    simpa only [h.1] using h.isSemitermVec.isUTerm
  constructor
  · simp [len_qVec hw,h.1]
  · intro i hi
    rw [len_qVec hw] at hi
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simpa [Bootstrapping.qVec] using label_bvar (x∷b) f 0 (by simp)
    · have hi' : i<len w := by simpa using hi
      simpa [Bootstrapping.qVec,nth_termBShiftVec hw hi'] using
        variableLabel_termBShift x (h.2 i hi')

theorem totalLabel_termSubst {w a b f t : V} (h : LabelSubstitution w a b f)
    (ht : IsSemiterm language (len a) t) :
    totalLabel (termSubst language w t) b f=totalLabel t a f := by
  rcases (source_term_cases _ _).mp ht with ⟨i,hi,rfl⟩ | ⟨i,rfl⟩
  · simp only [termSubst_bvar,totalLabel_bvar]
    exact (totalLabel_agrees (h.2 i (by simpa [h.1] using hi))).symm
  · simp

theorem variableLabel_termSubst {w a b f y t : V} (h : LabelSubstitution w a b f)
    (ht : VariableLabel y t a f) : VariableLabel y (termSubst language w t) b f := by
  rcases ht with ⟨i,hi,rfl,rfl⟩ | ⟨i,hi,rfl,rfl⟩
  · simpa using h.2 i (by simpa [h.1] using hi)
  · simpa using label_fvar b f i hi

theorem totalAtom_termSubstVec {w a b f lo z ts : V} (r : V)
    (h : LabelSubstitution w a b f) (hts : IsSemitermVec language 2 (len a) ts) :
    totalAtom (parameters b f lo z) 2 r (termSubstVec language 2 w ts)=
      totalAtom (parameters a f lo z) 2 r ts := by
  have h0 : (0:V)<2 := by simp
  have h1 : (1:V)<2 := by simp
  simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve,
    nth_termSubstVec hts.isUTerm h0,nth_termSubstVec hts.isUTerm h1]
  rw [totalLabel_termSubst h (hts.nth h0),totalLabel_termSubst h (hts.nth h1)]

#print axioms labelSubstitution_graph
#print axioms LabelSubstitution.isSemitermVec
#print axioms totalLabel_termBShift
#print axioms variableLabel_termBShift
#print axioms LabelSubstitution.qVec
#print axioms totalLabel_termSubst
#print axioms variableLabel_termSubst
#print axioms totalAtom_termSubstVec
end PA196.Arithmetic.Transport.RelationalSource.Numeric

