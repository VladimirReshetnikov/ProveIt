import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The longitude and latitude rectangles shared by the construction and the chart -/

namespace GlobeFlattening

open Set

/-- The closed coordinate rectangle, on which the scalar function is continuous. -/
def chartClosedRectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Icc a b ×ˢ Icc c d

/-- The open longitude and latitude rectangle. -/
def chartRectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Ioo a b ×ˢ Ioo c d

theorem chartRectangle_subset_closed {a b c d : ℝ} :
    chartRectangle a b c d ⊆ chartClosedRectangle a b c d :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem isOpen_chartRectangle (a b c d : ℝ) : IsOpen (chartRectangle a b c d) :=
  isOpen_Ioo.prod isOpen_Ioo

/-- The closure of the longitude and latitude domain of the cut sphere. -/
def sphereClosedBox : Set (ℝ × ℝ) :=
  chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

/-- The open longitude and latitude domain of the cut sphere. -/
def sphereLongitudeDomain : Set (ℝ × ℝ) :=
  chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

theorem isOpen_sphereLongitudeDomain : IsOpen sphereLongitudeDomain :=
  isOpen_chartRectangle _ _ _ _

theorem sphereLongitudeDomain_subset_box : sphereLongitudeDomain ⊆ sphereClosedBox :=
  chartRectangle_subset_closed

end GlobeFlattening
