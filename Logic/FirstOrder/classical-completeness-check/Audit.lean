import FirstOrder.ClassicalCompleteness

open SetTheory SetTheory.Form
open SetTheory.FirstOrderCompactness SetTheory.FirstOrderClassicalCompleteness

#print axioms SetTheory.FirstOrderClassicalCompleteness.theoryConsistent_iff_BCon
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_completeness
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_soundness_and_completeness
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_original_completeness
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_completeness_for_theories
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_soundness_and_completeness_for_theories
#print axioms SetTheory.FirstOrderClassicalCompleteness.godel_model_existence
#print axioms SetTheory.FirstOrderClassicalCompleteness.theory_consistent_iff_has_model

example (T : Form → Prop) : TheoryConsistent T ↔ BCon T [] :=
  SetTheory.FirstOrderClassicalCompleteness.theoryConsistent_iff_BCon T

example (G : List Form) (phi : Form) :
    SemanticConsequence G phi → SyntacticConsequence G phi :=
  SetTheory.FirstOrderClassicalCompleteness.godel_completeness G phi

example (G : List Form) (phi : Form) :
    SyntacticConsequence G phi ↔ SemanticConsequence G phi :=
  SetTheory.FirstOrderClassicalCompleteness.godel_soundness_and_completeness G phi

example (phi : Form) : LogicallyValid phi → Prov [] phi :=
  SetTheory.FirstOrderClassicalCompleteness.godel_original_completeness phi

example (T : Form → Prop) (phi : Form) (hT : Sentences T) :
    TheorySemanticConsequence T phi → TheorySyntacticConsequence T phi :=
  SetTheory.FirstOrderClassicalCompleteness.godel_completeness_for_theories T phi hT

example (T : Form → Prop) (phi : Form) (hT : Sentences T) :
    TheorySyntacticConsequence T phi ↔ TheorySemanticConsequence T phi :=
  SetTheory.FirstOrderClassicalCompleteness.godel_soundness_and_completeness_for_theories
    T phi hT

example (T : Form → Prop) (hT : Sentences T) :
    TheoryConsistent T → TheoryHasModel T :=
  SetTheory.FirstOrderClassicalCompleteness.godel_model_existence T hT

example (T : Form → Prop) (hT : Sentences T) :
    TheoryConsistent T ↔ TheoryHasModel T :=
  SetTheory.FirstOrderClassicalCompleteness.theory_consistent_iff_has_model T hT
