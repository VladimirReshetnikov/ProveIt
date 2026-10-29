import DiophantineConsistency.ParsonsPrenexTree

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ParsonsRule DiophantineConsistency.ParsonsPrenexTree

example (A B C : ArithmeticSemiformula ℕ 2)
    (hA : Hierarchy 𝚺 0 A) (hB : Hierarchy 𝚺 0 B) (hC : Hierarchy 𝚺 0 C) :
    Hierarchy 𝚺 0 (matrix (.disj (.leaf (n := 1) (k := 1) A)
      (.conj (.leaf (n := 1) (k := 1) B) (.leaf (n := 1) (k := 1) C)))) :=
  matrix_bounded _ ⟨hA,hB,hC⟩

noncomputable example (A B C : ArithmeticSemiformula ℕ 2)
    (h : Proof 𝗣𝗔⁻ (source (.disj (.leaf (n := 1) (k := 1) A)
      (.conj (.leaf (n := 1) (k := 1) B) (.leaf (n := 1) (k := 1) C))))) :
    Proof 𝗣𝗔⁻ (DiophantineConsistency.ParsonsPrenexTuple.block
      (matrix (.disj (.leaf (n := 1) (k := 1) A)
        (.conj (.leaf (n := 1) (k := 1) B) (.leaf (n := 1) (k := 1) C))))) :=
  forward _ h

#print axioms matrix_bounded
#print axioms semantic
#print axioms forward
#print axioms backward
#check forward
#check backward
