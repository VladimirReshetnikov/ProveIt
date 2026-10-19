import FirstOrder.Compactness

open SetTheory SetTheory.Form SetTheory.FirstOrderCompactness

#print axioms SetTheory.FirstOrderCompactness.theoryHasModel_finiteSubtheoriesHaveModels
#print axioms SetTheory.FirstOrderCompactness.theoryHasModel_of_finiteSubtheoriesHaveModels
#print axioms SetTheory.FirstOrderCompactness.compactness

example {T : Form → Prop} (hT : TheoryHasModel T) : FiniteSubtheoriesHaveModels T :=
  SetTheory.FirstOrderCompactness.theoryHasModel_finiteSubtheoriesHaveModels hT

example (T : Form → Prop) (hSentences : Sentences T)
    (hfinite : FiniteSubtheoriesHaveModels T) : TheoryHasModel T :=
  SetTheory.FirstOrderCompactness.theoryHasModel_of_finiteSubtheoriesHaveModels
    T hSentences hfinite

example (T : Form → Prop) (hSentences : Sentences T) :
    TheoryHasModel T ↔ FiniteSubtheoriesHaveModels T :=
  SetTheory.FirstOrderCompactness.compactness T hSentences
