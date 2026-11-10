import DiophantineConsistency.Sign17KStreamBump

/-! SOURCE ONLY. Decompose the in-Lean coefficient vector into block lists. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KCoefficientDecompose

theorem ofFn_fin_append {α : Type} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [List.ofFn_add]
  simp [Fin.append_left', Fin.append_right]

theorem coefficient_list :
    List.ofFn Sign17KLiteralCoefficients.literal =
      (List.ofFn Sign17KTileCoefficients00.literal) ++ (List.ofFn Sign17KTileCoefficients01.literal) ++ (List.ofFn Sign17KTileCoefficients02.literal) ++ (List.ofFn Sign17KTileCoefficients03.literal) ++ (List.ofFn Sign17KTileCoefficients04.literal) ++ (List.ofFn Sign17KTileCoefficients05.literal) ++ (List.ofFn Sign17KTileCoefficients06.literal) ++ (List.ofFn Sign17KTileCoefficients07.literal) ++ (List.ofFn Sign17KTileCoefficients08.literal) ++ (List.ofFn Sign17KTileCoefficients09.literal) ++ (List.ofFn Sign17KTileCoefficients10.literal) ++ (List.ofFn Sign17KTileCoefficients11.literal) ++ (List.ofFn Sign17KTileCoefficients12.literal) ++ (List.ofFn Sign17KTileCoefficients13.literal) ++ (List.ofFn Sign17KTileCoefficients14.literal) ++ (List.ofFn Sign17KTileCoefficients15.literal) ++ (List.ofFn Sign17KControlBlocks.literal) := by
  simp only [Sign17KLiteralCoefficients.literal, Sign17KTileCoeffUnion96.literal, Sign17KTileCoeffUnion224.literal, Sign17KTileCoeffUnion352.literal, Sign17KTileCoeffUnion480.literal, Sign17KTileCoeffUnion608.literal, Sign17KTileCoeffUnion736.literal, Sign17KTileCoeffUnion864.literal, Sign17KTileCoeffUnion942.literal, Sign17KTileCoeffUnion224.literal160, Sign17KTileCoeffUnion352.literal288, Sign17KTileCoeffUnion480.literal416, Sign17KTileCoeffUnion608.literal544, Sign17KTileCoeffUnion736.literal672, Sign17KTileCoeffUnion864.literal800, Sign17KTileCoeffUnion942.literal928, ofFn_fin_append, List.append_assoc]

theorem coefficient_list_reversed :
    (List.ofFn Sign17KLiteralCoefficients.literal).reverse =
      ((List.ofFn Sign17KControlBlocks.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients15.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients14.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients13.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients12.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients11.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients10.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients09.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients08.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients07.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients06.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients05.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients04.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients03.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients02.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients01.literal).reverse) ++ ((List.ofFn Sign17KTileCoefficients00.literal).reverse) := by
  rw [coefficient_list]
  simp only [List.reverse_append, List.append_assoc]

end DiophantineConsistency.Sign17KCoefficientDecompose
#print axioms DiophantineConsistency.Sign17KCoefficientDecompose.ofFn_fin_append
#print axioms DiophantineConsistency.Sign17KCoefficientDecompose.coefficient_list
#print axioms DiophantineConsistency.Sign17KCoefficientDecompose.coefficient_list_reversed
