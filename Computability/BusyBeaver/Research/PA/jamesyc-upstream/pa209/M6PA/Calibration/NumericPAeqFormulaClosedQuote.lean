module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaQuote
public import M6PA.Calibration.PAForwardRelationalClosureSupport
public import M6PA.Calibration.PAInterpretedFixedClosure
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closed_interpretation_quote_shift (p : ForwardRelational.SourceFormula 0)
    (h : p.freeVariables=∅) (f : Nat → Term 0) :
    shift language (⌜ForwardRelational.formula p Fin.elim0 f⌝ : V)=
      ⌜ForwardRelational.formula p Fin.elim0 f⌝ := by
  rw [← Semiformula.quote_shift]
  exact congrArg (fun q : RelationalSource.Ordinal.Formula 0 => (⌜q⌝ : V))
    (ForwardRelational.formula_closed_source_shift p h f)

theorem fixed_interpretation_quote_closed (p : ForwardRelational.SourceFormula 0)
    (hp : p∈Presentation.fixedAxioms) (f : Nat → Term 0) :
    IsSemiformula language 0 (⌜ForwardRelational.formula p Fin.elim0 f⌝ : V) ∧
    shift language (⌜ForwardRelational.formula p Fin.elim0 f⌝ : V)=
      ⌜ForwardRelational.formula p Fin.elim0 f⌝ :=
  ⟨by simpa using Semiformula.quote_isSemiformula (V:=V) (ForwardRelational.formula p Fin.elim0 f),
    closed_interpretation_quote_shift p (ForwardRelational.fixedAxiom_freeVariables p hp) f⟩

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaSyntax_closed_source_quote {p : ForwardRelational.SourceFormula 0}
    (hp : p.freeVariables=∅) (param : V)
    (hv : ParametersValid 0 0 param) :
    formulaSyntax param (⌜p⌝ : V)=
      ⌜ForwardRelational.formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ := by
  apply formulaSyntax_quote p param Fin.elim0 (fun _ => (.fvar 0 : Term 0)) hv
  · intro i; exact Fin.elim0 i
  · intro i hi
    simp [Semiformula.FVar?,hp] at hi

#print axioms closed_interpretation_quote_shift
#print axioms fixed_interpretation_quote_closed
#print axioms formulaSyntax_closed_source_quote
end M6.PA.NumericPAeqFormula

