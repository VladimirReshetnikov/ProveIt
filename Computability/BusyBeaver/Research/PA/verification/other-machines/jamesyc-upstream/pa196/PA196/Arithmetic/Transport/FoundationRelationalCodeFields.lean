module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalCodeBlueprint
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Independently typed field proofs, avoiding whole-Blueprint normalization. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph PA196.Arithmetic.HeadGraphs
attribute [local irreducible] ActualArithmeticGraph.graph totalAtomGraph advanceGraph
  translationNeg translationAnd translationOr translationExs universalExpr

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negativeAtom_defined :
    𝚺ᴬ₁-Function₄ (fun param k r ts : V =>
      eval translationNeg (totalAtom param k r ts) 0 0 0) via negativeAtomGraph :=
  .mk fun v => by
    simp only [negativeAtomGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [graph_correct,Matrix.comp_vecCons'']

#print axioms negativeAtom_defined

theorem truthTranslation_defined :
    𝚺ᴬ₁-Function₁ (fun _ : V => (0:V)) via truthTranslationGraph :=
  .mk fun v => by
    simp only [truthTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem falseTranslation_defined :
    𝚺ᴬ₁-Function₁ (fun _ : V => (1:V)) via falseTranslationGraph :=
  .mk fun v => by
    simp only [falseTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem andTranslation_defined :
    𝚺ᴬ₁-Function₅ (fun (_ _ _ a b : V) => eval translationAnd a b 0 0) via andTranslationGraph :=
  .mk fun v => by
    simp only [andTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [graph_correct,Matrix.comp_vecCons'']

#print axioms andTranslation_defined

theorem orTranslation_defined :
    𝚺ᴬ₁-Function₅ (fun (_ _ _ a b : V) => eval translationOr a b 0 0) via orTranslationGraph :=
  .mk fun v => by
    simp only [orTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [graph_correct,Matrix.comp_vecCons'']

#print axioms orTranslation_defined

theorem allTranslation_defined :
    𝚺ᴬ₁-Function₃ (fun (param _ ys : V) =>
      eval universalExpr (nth param 2) (nth ys 0) 0 0) via allTranslationGraph :=
  .mk fun v => by
    simp only [allTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [graph_correct,Matrix.comp_vecCons'']

#print axioms allTranslation_defined

theorem exsTranslation_defined :
    𝚺ᴬ₁-Function₃ (fun (param _ ys : V) =>
      eval translationExs (nth param 2) (nth ys 0) 0 0) via exsTranslationGraph :=
  .mk fun v => by
    simp only [exsTranslationGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [graph_correct,Matrix.comp_vecCons'']

#print axioms exsTranslation_defined

theorem binderChange_defined :
    𝚺ᴬ₁-Function₂ (fun (param _ : V) => advance param) via binderChangeGraph :=
  .mk fun v => by
    simp only [binderChangeGraph, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [Matrix.comp_vecCons'']

#print axioms truthTranslation_defined
#print axioms falseTranslation_defined
#print axioms binderChange_defined
end PA196.Arithmetic.Transport.RelationalSource.Numeric

