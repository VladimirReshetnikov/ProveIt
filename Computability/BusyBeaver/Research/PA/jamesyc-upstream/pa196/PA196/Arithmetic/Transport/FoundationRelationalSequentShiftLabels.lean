module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPropositional
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Numeric free-environment extension for Foundation shift. This proves the
variable/atom and binder-parameter prerequisites, not a formula induction or
quantifier certificate transport. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prependFree (x param : V) : V :=
  parameters (nth param 0) (x ∷ nth param 1) (nth param 2) (nth param 3)

attribute [local irreducible] parametersGraph
noncomputable def prependFreeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out x param. ∃ b f lo z fs, !nthDef b param 0 ∧ !nthDef f param 1 ∧
    !nthDef lo param 2 ∧ !nthDef z param 3 ∧ !adjoinDef fs x f ∧
    !parametersGraph out b fs lo z”

theorem prependFree_graph (out x param : V) :
    prependFreeGraph.val.Evalb ![out,x,param] ↔ out=prependFree x param := by
  simp [prependFreeGraph,parameters_graph,prependFree,Matrix.comp_vecCons'']

theorem prependFree_total_unique (x param : V) :
    ∃! out, prependFreeGraph.val.Evalb ![out,x,param] := by
  refine ⟨prependFree x param,(prependFree_graph _ _ _).mpr rfl,?_⟩
  intro out h
  exact (prependFree_graph _ _ _).mp h

@[simp] theorem prependFree_parameters (x b f lo z : V) :
    prependFree x (parameters b f lo z)=parameters b (x∷f) lo z := by
  simp [prependFree]

theorem prependFree_advance (x param : V) :
    prependFree x (advance param)=advance (prependFree x param) := by
  simp [prependFree,advance]

theorem totalLabel_termShift (t b f x : V) (ht : IsUTerm language t) :
    totalLabel (termShift language t) b (x∷f)=totalLabel t b f := by
  have hc : (∃ i, t=qqBvar i) ∨ ∃ i, t=qqFvar i := by
    simpa only [IsUTerm.case_iff,source_no_functions,false_and,exists_false,or_false] using ht
  rcases hc with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;> simp

theorem variableLabel_termShift {y t b f : V} (x : V) (h : VariableLabel y t b f) :
    VariableLabel y (termShift language t) b (x∷f) := by
  rcases h with ⟨i,hi,rfl,rfl⟩ | ⟨i,hi,rfl,rfl⟩
  · simpa using label_bvar b (x∷f) i hi
  · simpa using label_fvar b (x∷f) (i+1) (by simpa using hi)

theorem covered_termShift {t b f : V} (x : V) (h : Covered t b f) :
    Covered (termShift language t) b (x∷f) := by
  obtain ⟨y,hy⟩ := (label_exists_iff _ _ _).mpr h
  exact label_covered (variableLabel_termShift x hy)

theorem environments_prependFree {b f lo z x : V}
    (h : EnvironmentsValid b f lo z) (hx : x<lo) :
    EnvironmentsValid b (x∷f) lo z := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa using hx
  · have hi' : i<len f := by simpa using hi
    simpa using h.2.2.2 i hi'

/-- Only the environment changes here: the same supplied budget p is retained.
This deliberately does not claim a code-bound guard for shift(p). -/
theorem guard_prependFree {b f lo z p x : V} (h : Guard b f lo z p) (hx : x<lo) :
    Guard b (x∷f) lo z p := ⟨environments_prependFree h.1 hx,h.2⟩

theorem totalAtom_termShiftVec (param k r ts x : V)
    (hk : k=2) (hts : IsUTermVec language k ts) :
    totalAtom (prependFree x param) k r (termShiftVec language k ts)=totalAtom param k r ts := by
  subst k
  have h0 : (0:V)<2 := by simp
  have h1 : (1:V)<2 := by simp
  simp only [totalAtom,prependFree,parameters_bound,parameters_free,parameters_reserve,
    nth_termShiftVec hts h0,nth_termShiftVec hts h1]
  rw [totalLabel_termShift _ _ _ _ (hts.nth h0),totalLabel_termShift _ _ _ _ (hts.nth h1)]

#print axioms prependFree_graph
#print axioms prependFree_total_unique
#print axioms prependFree_parameters
#print axioms prependFree_advance
#print axioms totalLabel_termShift
#print axioms variableLabel_termShift
#print axioms covered_termShift
#print axioms environments_prependFree
#print axioms guard_prependFree
#print axioms totalAtom_termShiftVec
end PA196.Arithmetic.Transport.RelationalSource.Numeric

