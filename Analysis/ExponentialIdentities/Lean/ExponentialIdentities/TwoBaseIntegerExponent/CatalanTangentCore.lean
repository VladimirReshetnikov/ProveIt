import Mathlib

/-!
Finite algebraic core for the four adjacent-smooth directions.
-/

namespace LeanProofs.TwoBaseIntegerExponent.CatalanTangentCore

variable {R : Type*} [CommRing R]

def defectOne (U : R) : R := U - 2
def defectTwo (U V : R) : R := V - U - 1
def defectThree (U V : R) : R := U ^ 2 - V - 1
def defectEight (U V : R) : R := V ^ 2 - U ^ 3 - 1

theorem first_tangent_defect_identity (U V : R) :
    -3 * defectOne U + defectTwo U V + defectThree U V =
      defectOne U ^ 2 := by
  simp only [defectOne, defectTwo, defectThree]
  ring

theorem second_tangent_defect_identity (U V : R) :
    6 * defectOne U - 6 * defectTwo U V + defectEight U V =
      -(defectOne U ^ 3) - 5 * defectOne U ^ 2
        + 2 * defectOne U * defectTwo U V + defectTwo U V ^ 2 := by
  simp only [defectOne, defectTwo, defectEight]
  ring

theorem balanceVector_parametrization
    (wOne wTwo wThree wEight : ℤ)
    (hFirst : wOne + 2 * wThree = 0)
    (hSecond : wTwo + 2 * wEight = 0)
    (hTotal : wOne + wTwo + wThree + wEight = 0) :
    wOne = 2 * wEight ∧ wTwo = -2 * wEight ∧ wThree = -wEight := by
  omega

theorem tangentLattice_parametrization
    (rOne rTwo rThree rEight : ℤ)
    (hTwo :
      2 * rOne - 2 * rTwo + 8 * rThree - 24 * rEight = 0)
    (hThree :
      3 * rTwo - 3 * rThree + 18 * rEight = 0) :
    rOne = -3 * rThree + 6 * rEight ∧
      rTwo = rThree - 6 * rEight := by
  omega

theorem fourResidues_first_relation
    (qTwo qThree x y : R) :
    -3 * (-2 * qTwo + x)
      + (2 * qTwo - 3 * qThree + y - x)
      + (-8 * qTwo + 3 * qThree + 4 * x - y) = 0 := by
  ring

theorem fourResidues_second_relation
    (qTwo qThree x y : R) :
    6 * (-2 * qTwo + x)
      - 6 * (2 * qTwo - 3 * qThree + y - x)
      + (24 * qTwo - 18 * qThree + 6 * y - 12 * x) = 0 := by
  ring

theorem balancedResidual_cross_identity
    (wOne wTwo wThree wEight t : R)
    (hTwo : wTwo = t * wOne)
    (hThree : wThree = (3 - t) * wOne)
    (hEight : wEight = 6 * (t - 1) * wOne) :
    (wOne ^ 2 * wEight) * (t ^ 2 * (3 - t)) =
      (6 * (t - 1)) * (wThree * wTwo ^ 2) := by
  rw [hTwo, hThree, hEight]
  ring

end LeanProofs.TwoBaseIntegerExponent.CatalanTangentCore
