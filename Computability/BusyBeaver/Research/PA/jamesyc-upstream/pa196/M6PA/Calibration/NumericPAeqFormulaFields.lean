module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaBlueprint
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] atomGraph guardedAllGraph guardedExsGraph binderParametersGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem negativeAtom_defined :
    𝚺ᴬ₁-Function₄ (fun param k r ts : V =>
      neg RelationalSource.language (atomCode param k r ts)) via negativeAtomGraph :=
  .mk fun v => by
    simp only [negativeAtomGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [atom_graph,Matrix.comp_vecCons'']
theorem truthTranslation_defined :
    𝚺ᴬ₁-Function₁ (fun _ : V => (qqVerum:V)) via truthTranslationGraph :=
  .mk fun v => by
    simp only [truthTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem falseTranslation_defined :
    𝚺ᴬ₁-Function₁ (fun _ : V => (qqFalsum:V)) via falseTranslationGraph :=
  .mk fun v => by
    simp only [falseTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem andTranslation_defined :
    𝚺ᴬ₁-Function₅ (fun (_ _ _ a b : V) => qqAnd a b) via andTranslationGraph :=
  .mk fun v => by
    simp only [andTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem orTranslation_defined :
    𝚺ᴬ₁-Function₅ (fun (_ _ _ a b : V) => qqOr a b) via orTranslationGraph :=
  .mk fun v => by
    simp only [orTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp

theorem allTranslation_defined :
    𝚺ᴬ₁-Function₃ (fun (_ _ ys : V) => guardedAllCode (nth ys 0)) via allTranslationGraph :=
  .mk fun v => by
    simp only [allTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [guardedAll_graph,Matrix.comp_vecCons'']

theorem exsTranslation_defined :
    𝚺ᴬ₁-Function₃ (fun (_ _ ys : V) => guardedExsCode (nth ys 0)) via exsTranslationGraph :=
  .mk fun v => by
    simp only [exsTranslationGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [guardedExs_graph,Matrix.comp_vecCons'']

theorem binderChange_defined :
    𝚺ᴬ₁-Function₂ (fun (param _ : V) => binderParameters param) via binderChangeGraph :=
  .mk fun v => by
    simp only [binderChangeGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [binderParameters_graph,Matrix.comp_vecCons'']

#print axioms negativeAtom_defined
#print axioms truthTranslation_defined
#print axioms falseTranslation_defined
#print axioms andTranslation_defined
#print axioms orTranslation_defined
#print axioms allTranslation_defined
#print axioms exsTranslation_defined
#print axioms binderChange_defined
end M6.PA.NumericPAeqFormula

