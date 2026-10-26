import DiophantineConsistency.NativeQuadraticParent

/-! A replacement for NativeNinePolynomial52.map_rowCoefficient and its
22 private wrappers. The statement is unchanged. -/
namespace DiophantineConsistency.NativeNinePolynomial52
open NativeQuadraticParent
variable {A B : Type*} [CommRing A] [CommRing B]

private theorem mapIte (f : A →+* B) (p : Prop) [Decidable p] (a b : A) :
    f (if p then a else b) = if p then f a else f b := by
  by_cases h : p <;> simp only [h, if_true, if_false]

theorem map_rowCoefficient (f : A →+* B) (ports : Fin 4 → A)
    (k : Fin 22) (p : SidonPositions.PairIndex 31) :
    f (rowCoefficient ports k p) = rowCoefficient (fun i => f (ports i)) k p := by
  fin_cases k <;> dsimp only [rowCoefficient, Fin.reduceFinMk, Matrix.cons_val]
  all_goals
    simp only [mapIte, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_one, map_zero]

#print axioms map_rowCoefficient
end DiophantineConsistency.NativeNinePolynomial52
