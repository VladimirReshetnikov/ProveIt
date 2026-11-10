import DiophantineConsistency.Sign17KWeightAggregateProbe
import DiophantineConsistency.Sign17KWeightAggregateBatch01
import DiophantineConsistency.Sign17KWeightAggregateBatch02
import DiophantineConsistency.Sign17KWeightAggregateBatch03
import DiophantineConsistency.Sign17KWeightAggregateBatch04
import DiophantineConsistency.Sign17KWeightAggregateBatch05
import DiophantineConsistency.Sign17KWeightAggregateBatch06
import DiophantineConsistency.Sign17KWeightAggregateBatch07
import DiophantineConsistency.Sign17KWeightAggregateBatch08
import DiophantineConsistency.Sign17KWeightAggregateBatch09
import DiophantineConsistency.Sign17KWeightAggregateBatch10
import DiophantineConsistency.Sign17KWeightAggregateBatch11
import DiophantineConsistency.Sign17KWeightAggregateBatch12
import DiophantineConsistency.Sign17KWeightAggregateBatch13
import DiophantineConsistency.Sign17KWeightAggregateBatch14
import DiophantineConsistency.Sign17KWeightAggregateBatch15

/-! SOURCE-ONLY: all 15 adjacent-block boundary comparisons. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KOrderAllBoundaries
open WangTiles942

theorem boundary00 : Sign17KWeightAggregateBatch01.weights 0 < Sign17KWeightAggregateProbe.weights 31 := by decide +kernel

theorem actual_boundary00 :
    selectorWeight (tile (Sign17KWeightAggregateBatch01.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateProbe.indices 31)) := by
  rw [Sign17KWeightAggregateBatch01.all_weights, Sign17KWeightAggregateProbe.all_weights]
  exact boundary00

theorem boundary01 : Sign17KWeightAggregateBatch02.weights 0 < Sign17KWeightAggregateBatch01.weights 63 := by decide +kernel

theorem actual_boundary01 :
    selectorWeight (tile (Sign17KWeightAggregateBatch02.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch01.indices 63)) := by
  rw [Sign17KWeightAggregateBatch02.all_weights, Sign17KWeightAggregateBatch01.all_weights]
  exact boundary01

theorem boundary02 : Sign17KWeightAggregateBatch03.weights 0 < Sign17KWeightAggregateBatch02.weights 63 := by decide +kernel

theorem actual_boundary02 :
    selectorWeight (tile (Sign17KWeightAggregateBatch03.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch02.indices 63)) := by
  rw [Sign17KWeightAggregateBatch03.all_weights, Sign17KWeightAggregateBatch02.all_weights]
  exact boundary02

theorem boundary03 : Sign17KWeightAggregateBatch04.weights 0 < Sign17KWeightAggregateBatch03.weights 63 := by decide +kernel

theorem actual_boundary03 :
    selectorWeight (tile (Sign17KWeightAggregateBatch04.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch03.indices 63)) := by
  rw [Sign17KWeightAggregateBatch04.all_weights, Sign17KWeightAggregateBatch03.all_weights]
  exact boundary03

theorem boundary04 : Sign17KWeightAggregateBatch05.weights 0 < Sign17KWeightAggregateBatch04.weights 63 := by decide +kernel

theorem actual_boundary04 :
    selectorWeight (tile (Sign17KWeightAggregateBatch05.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch04.indices 63)) := by
  rw [Sign17KWeightAggregateBatch05.all_weights, Sign17KWeightAggregateBatch04.all_weights]
  exact boundary04

theorem boundary05 : Sign17KWeightAggregateBatch06.weights 0 < Sign17KWeightAggregateBatch05.weights 63 := by decide +kernel

theorem actual_boundary05 :
    selectorWeight (tile (Sign17KWeightAggregateBatch06.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch05.indices 63)) := by
  rw [Sign17KWeightAggregateBatch06.all_weights, Sign17KWeightAggregateBatch05.all_weights]
  exact boundary05

theorem boundary06 : Sign17KWeightAggregateBatch07.weights 0 < Sign17KWeightAggregateBatch06.weights 63 := by decide +kernel

theorem actual_boundary06 :
    selectorWeight (tile (Sign17KWeightAggregateBatch07.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch06.indices 63)) := by
  rw [Sign17KWeightAggregateBatch07.all_weights, Sign17KWeightAggregateBatch06.all_weights]
  exact boundary06

theorem boundary07 : Sign17KWeightAggregateBatch08.weights 0 < Sign17KWeightAggregateBatch07.weights 63 := by decide +kernel

theorem actual_boundary07 :
    selectorWeight (tile (Sign17KWeightAggregateBatch08.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch07.indices 63)) := by
  rw [Sign17KWeightAggregateBatch08.all_weights, Sign17KWeightAggregateBatch07.all_weights]
  exact boundary07

theorem boundary08 : Sign17KWeightAggregateBatch09.weights 0 < Sign17KWeightAggregateBatch08.weights 63 := by decide +kernel

theorem actual_boundary08 :
    selectorWeight (tile (Sign17KWeightAggregateBatch09.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch08.indices 63)) := by
  rw [Sign17KWeightAggregateBatch09.all_weights, Sign17KWeightAggregateBatch08.all_weights]
  exact boundary08

theorem boundary09 : Sign17KWeightAggregateBatch10.weights 0 < Sign17KWeightAggregateBatch09.weights 63 := by decide +kernel

theorem actual_boundary09 :
    selectorWeight (tile (Sign17KWeightAggregateBatch10.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch09.indices 63)) := by
  rw [Sign17KWeightAggregateBatch10.all_weights, Sign17KWeightAggregateBatch09.all_weights]
  exact boundary09

theorem boundary10 : Sign17KWeightAggregateBatch11.weights 0 < Sign17KWeightAggregateBatch10.weights 63 := by decide +kernel

theorem actual_boundary10 :
    selectorWeight (tile (Sign17KWeightAggregateBatch11.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch10.indices 63)) := by
  rw [Sign17KWeightAggregateBatch11.all_weights, Sign17KWeightAggregateBatch10.all_weights]
  exact boundary10

theorem boundary11 : Sign17KWeightAggregateBatch12.weights 0 < Sign17KWeightAggregateBatch11.weights 63 := by decide +kernel

theorem actual_boundary11 :
    selectorWeight (tile (Sign17KWeightAggregateBatch12.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch11.indices 63)) := by
  rw [Sign17KWeightAggregateBatch12.all_weights, Sign17KWeightAggregateBatch11.all_weights]
  exact boundary11

theorem boundary12 : Sign17KWeightAggregateBatch13.weights 0 < Sign17KWeightAggregateBatch12.weights 63 := by decide +kernel

theorem actual_boundary12 :
    selectorWeight (tile (Sign17KWeightAggregateBatch13.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch12.indices 63)) := by
  rw [Sign17KWeightAggregateBatch13.all_weights, Sign17KWeightAggregateBatch12.all_weights]
  exact boundary12

theorem boundary13 : Sign17KWeightAggregateBatch14.weights 0 < Sign17KWeightAggregateBatch13.weights 63 := by decide +kernel

theorem actual_boundary13 :
    selectorWeight (tile (Sign17KWeightAggregateBatch14.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch13.indices 63)) := by
  rw [Sign17KWeightAggregateBatch14.all_weights, Sign17KWeightAggregateBatch13.all_weights]
  exact boundary13

theorem boundary14 : Sign17KWeightAggregateBatch15.weights 0 < Sign17KWeightAggregateBatch14.weights 63 := by decide +kernel

theorem actual_boundary14 :
    selectorWeight (tile (Sign17KWeightAggregateBatch15.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch14.indices 63)) := by
  rw [Sign17KWeightAggregateBatch15.all_weights, Sign17KWeightAggregateBatch14.all_weights]
  exact boundary14

end DiophantineConsistency.Sign17KOrderAllBoundaries
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary00
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary01
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary02
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary03
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary04
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary05
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary06
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary07
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary08
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary09
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary10
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary11
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary12
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary13
#print axioms DiophantineConsistency.Sign17KOrderAllBoundaries.actual_boundary14
