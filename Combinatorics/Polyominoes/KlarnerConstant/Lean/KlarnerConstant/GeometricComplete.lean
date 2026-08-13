import KlarnerConstant.GeometricProfile
import KlarnerConstant.GeometricPPartition
import KlarnerConstant.GeometricQ
import KlarnerConstant.GeometricFourFive
import KlarnerConstant.GeometricU
import KlarnerConstant.GeometricV
import KlarnerConstant.GeometricW
import KlarnerConstant.GeometricTwoDeletion
import KlarnerConstant.Asymptotic
import KlarnerConstant.Concatenation

/-!
# The unconditional geometric `4.5235` bound

This module closes the finite-geometric boundary isolated in
`GeometricProfile.lean`.  Each of the nine non-elementary fields of
`GeometricBuiGaps` is supplied by an explicit injection between finite types
of marked polyomino occurrences.  Together with the elementary recurrence
rows already proved in `GeometricProfile.lean`, these injections give the
literal seventeen-row coefficient system from Bui's argument for the actual
polyomino occurrence counts.

The exact rational certificate then yields

```
growthSup fixedPolyominoCount <= 9047 / 2000.
```

The final theorem identifies this supremal formulation with the conventional
limit of real nth roots.  Its positivity and supermultiplicativity inputs are
the geometric stacking theorems from `Concatenation.lean`, and its boundedness
input is the just-proved `4.5235` exponential majorant.
-/

namespace LeanProofs.KlarnerConstant

open Filter Topology

/-- All nine non-elementary geometric recurrence fields, assembled from the
concrete finite injections in the dedicated Appendix-B modules. -/
theorem geometricBuiGaps : GeometricBuiGaps where
  p := geometricCoefficientProfile_p_recurrence
  q := geometricCoefficientProfile_q_recurrence
  s := geometricCoefficientProfile_s_recurrence
  u := geometricCoefficientProfile_u_recurrence
  v := geometricCoefficientProfile_v_recurrence
  w := geometricCoefficientProfile_w_recurrence
  x := by
    intro n _hn
    simpa [geometricCoefficientProfile] using
      buiX_coefficient_le_d_add_g_add_u n
  y := by
    intro n _hn
    simpa [geometricCoefficientProfile] using
      buiY_coefficient_le_c_add_g_add_t n
  z := by
    intro n _hn
    simpa [geometricCoefficientProfile] using
      buiZ_coefficient_le_c_add_e_add_x n

/-- Bui's literal published recurrence system for the actual finite counts of
marked neighborhood occurrences. -/
theorem geometricPublishedBuiRecurrences :
    PublishedBuiRecurrences geometricCoefficientProfile :=
  publishedBuiRecurrences_of_geometricGaps geometricBuiGaps

/-- The coefficientwise exponential majorant for the actual fixed-polyomino
counting sequence.  Its base is the exact rational number `9047 / 2000`. -/
theorem fixedPolyominoCount_le_9047_div_2000_pow (n : ℕ) :
    (fixedPolyominoCount n : ℚ) ≤ (9047 / 2000 : ℚ) ^ n :=
  PublishedBuiRecurrences.dominatedCoefficient_le_9047_div_2000_pow
    geometricPublishedBuiRecurrences
    fixedPolyominoCount_le_geometricCoefficientProfile_g n

/-- The same exponential majorant after casting to the reals. -/
theorem fixedPolyominoCount_real_le_9047_div_2000_pow (n : ℕ) :
    (fixedPolyominoCount n : ℝ) ≤ (9047 / 2000 : ℝ) ^ n := by
  have hq := fixedPolyominoCount_le_9047_div_2000_pow n
  have hcast :
      (((fixedPolyominoCount n : ℚ) : ℝ)) ≤
        ((((9047 / 2000 : ℚ) ^ n : ℚ) : ℝ)) :=
    (Rat.cast_le (K := ℝ)).2 hq
  have hbase : (((9047 / 2000 : ℚ) : ℝ)) = (9047 / 2000 : ℝ) := by
    norm_num
  simpa only [Rat.cast_natCast, Rat.cast_pow, hbase] using hcast

/-- The unconditional supremal growth bound for fixed polyominoes. -/
theorem growthSup_fixedPolyominoCount_le_9047_div_2000 :
    growthSup fixedPolyominoCount ≤ (9047 / 2000 : ℝ) :=
  PublishedBuiRecurrences.growthSup_le_9047_div_2000
    geometricPublishedBuiRecurrences
    fixedPolyominoCount_le_geometricCoefficientProfile_g

/-- The conventional fixed-polyomino growth constant exists: the sequence of
positive real nth roots converges to the supremal growth constant used by the
certificate proof. -/
theorem tendsto_realNthRoot_fixedPolyominoCount_growthSup :
    Tendsto (realNthRoot fixedPolyominoCount) atTop
      (nhds (growthSup fixedPolyominoCount)) := by
  have hpos : PositiveOnPositiveIndices fixedPolyominoCount := by
    intro n hn
    exact fixedPolyominoCount_pos hn
  have hsuper : SupermultiplicativeOnPositive fixedPolyominoCount := by
    intro m n _hm _hn
    exact fixedPolyominoCount_supermultiplicative m n
  exact tendsto_realNthRoot_growthSup hpos hsuper (by norm_num)
    fixedPolyominoCount_real_le_9047_div_2000_pow

end LeanProofs.KlarnerConstant
