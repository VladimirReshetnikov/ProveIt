module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalCodeConstruction
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric

namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph PA196.Arithmetic.HeadGraphs
attribute [local irreducible] ActualArithmeticGraph.graph totalAtomGraph advanceGraph
  translationNeg translationAnd translationOr translationExs universalExpr

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


noncomputable def translate (param p : V) : V := formulaConstruction.result language param p
noncomputable def translateGraph : 𝚺ᴬ₁.Semisentence 3 := formulaBlueprint.result language

instance translate_defined : 𝚺ᴬ₁-Function₂ (translate : V → V → V) via translateGraph :=
  formulaConstruction.result_defined (L := language)

/-- This is the original recursion theorem's invalid-formula policy, not an
acceptance certificate for the native calculus. -/
theorem translate_invalid (param p : V) (h : ¬IsUFormula language p) :
    translate param p=0 := formulaConstruction.result_prop_not (L := language) param h

theorem translate_graph (y param p : V) :
    translateGraph.val.Evalb ![y,param,p] ↔ y=translate param p :=
  translate_defined.defined ![y,param,p]

theorem translate_total_unique (param p : V) :
    ∃! y, translateGraph.val.Evalb ![y,param,p] := by
  refine ⟨translate param p,(translate_graph _ _ _).mpr rfl,?_⟩
  intro y hy
  exact (translate_graph _ _ _).mp hy

theorem translate_rel (param k r ts : V) (hr : language.IsRel k r)
    (ht : IsUTermVec language k ts) :
    translate param (qqRel k r ts)=totalAtom param k r ts :=
  formulaConstruction.result_rel (L := language) (param := param) hr ht

theorem translate_nrel (param k r ts : V) (hr : language.IsRel k r)
    (ht : IsUTermVec language k ts) :
    translate param (qqNRel k r ts)=eval translationNeg (totalAtom param k r ts) 0 0 0 :=
  formulaConstruction.result_nrel (L := language) (param := param) hr ht

theorem translate_verum (param : V) : translate param qqVerum=0 :=
  formulaConstruction.result_verum (L := language) (param := param)

theorem translate_falsum (param : V) : translate param qqFalsum=1 :=
  formulaConstruction.result_falsum (L := language) (param := param)

theorem translate_and (param p q : V) (hp : IsUFormula language p) (hq : IsUFormula language q) :
    translate param (qqAnd p q)=eval translationAnd (translate param p) (translate param q) 0 0 :=
  formulaConstruction.result_and (L := language) (param := param) hp hq

theorem translate_or (param p q : V) (hp : IsUFormula language p) (hq : IsUFormula language q) :
    translate param (qqOr p q)=eval translationOr (translate param p) (translate param q) 0 0 :=
  formulaConstruction.result_or (L := language) (param := param) hp hq

theorem translate_all (param p : V) (hp : IsUFormula language p) :
    translate param (qqAll p)=eval universalExpr (nth param 2) (translate (advance param) p) 0 0 := by
  simpa [formulaConstruction,translate] using
    formulaConstruction.result_all (L := language) (param := param) hp rfl

theorem translate_exs (param p : V) (hp : IsUFormula language p) :
    translate param (qqExs p)=eval translationExs (nth param 2) (translate (advance param) p) 0 0 := by
  simpa [formulaConstruction,translate] using
    formulaConstruction.result_exs (L := language) (param := param) hp rfl

/-- Guarded leaf agreement is inherited by the actual formula recursion. -/
theorem translate_rel_guarded {y k r ts b f lo z : V}
    (hr : language.IsRel k r) (ht : IsUTermVec language k ts)
    (h : AtomTranslation y k r ts b f lo z) :
    translate (parameters b f lo z) (qqRel k r ts)=y := by
  rw [translate_rel _ _ _ _ hr ht]
  exact (totalAtom_agrees h).symm

/-- The quantified equation and its conservative reserve survive together. -/
theorem translate_all_guarded {b f lo z p : V}
    (hp : IsUFormula language p) (h : Guard b f lo z (qqAll p)) :
    translate (parameters b f lo z) (qqAll p)=
      eval universalExpr lo (translate (parameters (lo ∷ b) f (lo+1) z) p) 0 0 ∧
      Guard (lo ∷ b) f (lo+1) z p := by
  refine ⟨?_,guard_all h⟩
  rw [translate_all _ _ hp]
  simp

theorem translate_exs_guarded {b f lo z p : V}
    (hp : IsUFormula language p) (h : Guard b f lo z (qqExs p)) :
    translate (parameters b f lo z) (qqExs p)=
      eval translationExs lo (translate (parameters (lo ∷ b) f (lo+1) z) p) 0 0 ∧
      Guard (lo ∷ b) f (lo+1) z p := by
  refine ⟨?_,guard_exs h⟩
  rw [translate_exs _ _ hp]
  simp

#print axioms translate_rel_guarded
#print axioms translate_all_guarded
#print axioms translate_exs_guarded
#print axioms formulaConstruction
#print axioms translate_defined
#print axioms translate_invalid
#print axioms translate_graph
#print axioms translate_total_unique
#print axioms translate_rel
#print axioms translate_nrel
#print axioms translate_verum
#print axioms translate_falsum
#print axioms translate_and
#print axioms translate_or
#print axioms translate_all
#print axioms translate_exs
end PA196.Arithmetic.Transport.RelationalSource.Numeric

