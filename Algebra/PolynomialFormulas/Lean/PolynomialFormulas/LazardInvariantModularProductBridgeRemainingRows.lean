import PolynomialFormulas.LazardInvariantModularProductBridgeRows84To86
import PolynomialFormulas.LazardInvariantModularProductBridgeRows86To88
import PolynomialFormulas.LazardInvariantModularProductBridgeRows88To90
import PolynomialFormulas.LazardInvariantModularProductBridgeRows90To92
import PolynomialFormulas.LazardInvariantModularProductBridgeRows92To94
import PolynomialFormulas.LazardInvariantModularProductBridgeRows94To96
import PolynomialFormulas.LazardInvariantModularProductBridgeRows96To98
import PolynomialFormulas.LazardInvariantModularProductBridgeRows98To100
import PolynomialFormulas.LazardInvariantModularProductBridgeRows100To102
import PolynomialFormulas.LazardInvariantModularProductBridgeRows102To104
import PolynomialFormulas.LazardInvariantModularProductBridgeRows104To106
import PolynomialFormulas.LazardInvariantModularProductBridgeRows106To108
import PolynomialFormulas.LazardInvariantModularProductBridgeRows108To110
import PolynomialFormulas.LazardInvariantModularProductBridgeRows110To112
import PolynomialFormulas.LazardInvariantModularProductBridgeRows112To114
import PolynomialFormulas.LazardInvariantModularProductBridgeRows114To116
import PolynomialFormulas.LazardInvariantModularProductBridgeRows116To118
import PolynomialFormulas.LazardInvariantModularProductBridgeRows118To120

/-!
# Aggregate for the remaining degree-seven product-row certificates

The first twelve product-row shards cover source rows `0,...,83`, while the
legacy polynomial shards start at row `120`.  Eighteen two-row ordinary
kernel-reduction checks cover the exact intervening interval.  This module
reassembles them without performing another finite computation.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false

/-- Exact coverage of every source row in the formerly missing interval
`84,...,119`. -/
theorem degreeSevenProductRow_eq_productCoefficient_rows_eightyFour_to_oneTwenty :
    ∀ i : Fin 159, 84 ≤ i.1 ∧ i.1 < 120 → ∀ j : Fin 132,
      degreeSevenProductRow i j =
        productCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j) := by
  intro i hi
  by_cases h86 : i.1 < 86
  · exact degreeSevenProductRow_eq_productCoefficient_rows_84_86 i
      ⟨hi.1, h86⟩
  by_cases h88 : i.1 < 88
  · exact degreeSevenProductRow_eq_productCoefficient_rows_86_88 i
      ⟨Nat.le_of_not_gt h86, h88⟩
  by_cases h90 : i.1 < 90
  · exact degreeSevenProductRow_eq_productCoefficient_rows_88_90 i
      ⟨Nat.le_of_not_gt h88, h90⟩
  by_cases h92 : i.1 < 92
  · exact degreeSevenProductRow_eq_productCoefficient_rows_90_92 i
      ⟨Nat.le_of_not_gt h90, h92⟩
  by_cases h94 : i.1 < 94
  · exact degreeSevenProductRow_eq_productCoefficient_rows_92_94 i
      ⟨Nat.le_of_not_gt h92, h94⟩
  by_cases h96 : i.1 < 96
  · exact degreeSevenProductRow_eq_productCoefficient_rows_94_96 i
      ⟨Nat.le_of_not_gt h94, h96⟩
  by_cases h98 : i.1 < 98
  · exact degreeSevenProductRow_eq_productCoefficient_rows_96_98 i
      ⟨Nat.le_of_not_gt h96, h98⟩
  by_cases h100 : i.1 < 100
  · exact degreeSevenProductRow_eq_productCoefficient_rows_98_100 i
      ⟨Nat.le_of_not_gt h98, h100⟩
  by_cases h102 : i.1 < 102
  · exact degreeSevenProductRow_eq_productCoefficient_rows_100_102 i
      ⟨Nat.le_of_not_gt h100, h102⟩
  by_cases h104 : i.1 < 104
  · exact degreeSevenProductRow_eq_productCoefficient_rows_102_104 i
      ⟨Nat.le_of_not_gt h102, h104⟩
  by_cases h106 : i.1 < 106
  · exact degreeSevenProductRow_eq_productCoefficient_rows_104_106 i
      ⟨Nat.le_of_not_gt h104, h106⟩
  by_cases h108 : i.1 < 108
  · exact degreeSevenProductRow_eq_productCoefficient_rows_106_108 i
      ⟨Nat.le_of_not_gt h106, h108⟩
  by_cases h110 : i.1 < 110
  · exact degreeSevenProductRow_eq_productCoefficient_rows_108_110 i
      ⟨Nat.le_of_not_gt h108, h110⟩
  by_cases h112 : i.1 < 112
  · exact degreeSevenProductRow_eq_productCoefficient_rows_110_112 i
      ⟨Nat.le_of_not_gt h110, h112⟩
  by_cases h114 : i.1 < 114
  · exact degreeSevenProductRow_eq_productCoefficient_rows_112_114 i
      ⟨Nat.le_of_not_gt h112, h114⟩
  by_cases h116 : i.1 < 116
  · exact degreeSevenProductRow_eq_productCoefficient_rows_114_116 i
      ⟨Nat.le_of_not_gt h114, h116⟩
  by_cases h118 : i.1 < 118
  · exact degreeSevenProductRow_eq_productCoefficient_rows_116_118 i
      ⟨Nat.le_of_not_gt h116, h118⟩
  exact degreeSevenProductRow_eq_productCoefficient_rows_118_120 i
    ⟨Nat.le_of_not_gt h118, hi.2⟩

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
