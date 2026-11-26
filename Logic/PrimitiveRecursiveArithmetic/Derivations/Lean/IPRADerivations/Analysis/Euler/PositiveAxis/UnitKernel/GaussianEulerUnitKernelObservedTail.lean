import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelNestedObservations
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalRadiusCorrectionSum
import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalSignedPanelTailDistance

/-!
# The signed real gap controls the actual complex omitted strips

At one shared auxiliary observation index, the containing and contained
complex quadratures differ by at most the signed real companion gap
plus twelve dyadic errors. The two exact split estimates each cost four
errors, and the two positive real radius corrections cost four more.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelObservedTail

open_ipra
open GaussianEulerUnitKernelCompactName (nameF data)
open GaussianEulerUnitKernelNestedPanels (source leftData rightData commonDen rightStart tail_sources)
open RationalNestedPanelGeometry (leftWidth rightWidth)
open GaussianEulerUnitKernelNestedObservations (original_observations projected_nested_source)
open GaussianEulerUnitKernelCompactPositiveRadius (positiveRadius original_boundBy)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianRationalPanelTailDistance (threeSum)
open GaussianRationalSignedPanelTailDistance (original_signed_companion_split_distance tailNumerator tailDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem diagonal_split (u z R B a C E G b D H J : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF u (data z R B a C E G))
      (threeSum (ap2 nameF u (leftData z R B a E b H)) (ap2 nameF u (data z R B b D H J))
        (ap2 nameF u (rightData z R B a C E b D H))) (num 4) (unit u) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive u) (unit_positive u)) (unit_positive u)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by
      unfold GaussianNamedThreeSumObservations.numerator
      ipra_ring)) (original_observations u u z R B a C E G b D H J h)

theorem original_tail_bound (u z R B a C E G b D H J X Y : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) (hY : Γ ⊢[PRAAx] le one Y)
    (gap : Γ ⊢[PRAAx] upper (fstT (ap2 nameF u (data (argument z) R B a C E G)))
      (fstT (ap2 nameF u (data (argument z) R B b D H J))) X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF u (data z R B a C E G)) (ap2 nameF u (data z R B b D H J))
      (X*unit u+num 12*Y) (Y*unit u) := by
  let Z := argument z
  let U := unit u
  let fO := ap2 nameF u (data z R B a C E G)
  let fM := ap2 nameF u (data z R B b D H J)
  let fL := ap2 nameF u (leftData z R B a E b H)
  let fR := ap2 nameF u (rightData z R B a C E b D H)
  let gO := ap2 nameF u (data Z R B a C E G)
  let gM := ap2 nameF u (data Z R B b D H J)
  let gL := ap2 nameF u (leftData Z R B a E b H)
  let gR := ap2 nameF u (rightData Z R B a C E b D H)
  let rL := positiveRadius gL U U
  let rR := positiveRadius gR U U
  let M := commonDen E H
  have hU := unit_positive (Γ := Γ) u
  have strips := tail_sources z R B a C E G b D H J h
  have hl : Γ ⊢[PRAAx] GaussianPositiveRadiusFiniteSum.boundBy fL rL :=
    original_boundBy u u z R B (H*a) (leftWidth a E b H) M M strips.andE₁
  have hr : Γ ⊢[PRAAx] GaussianPositiveRadiusFiniteSum.boundBy fR rR :=
    original_boundBy u u z R B (rightStart a E b D H) (rightWidth a C E b D H) M M strips.andE₂
  have split : Γ ⊢[PRAAx] distanceBounded fO (threeSum fL fM fR) (num 4) U :=
    diagonal_split u z R B a C E G b D H J h
  have realSplit : Γ ⊢[PRAAx] distanceBounded gO (threeSum gL gM gR) (num 4) U :=
    diagonal_split u Z R B a C E G b D H J (projected_nested_source z R B a C E G b D H J h)
  have correction := GaussianRationalRadiusCorrectionSum.sum_correction_upper (Γ := Γ) gL gR u
  have actual := original_signed_companion_split_distance fO fM fL fR gO gM gL gR rL rR
    (num 4) U (num 4) U X Y (num 4) U hU hU hY hU split hl hr realSplit gap correction
  have d := positive_product _ _ hY hU
  have wide := positive_product _ _ hU (positive_product _ _ (positive_product _ _ hU hY) hU)
  exact distance_radius_mono _ _ _ _ _ _ wide d
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold tailNumerator; dsimp only [U]; ipra_ring)) actual

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelObservedTail
