import GowersSzemeredi.Proofs16HigherArrangementSymmetry

/-! Four involutions move the first endpoint to any of the sixteen
positions: reverse pairs, exchange adjacent shifts, exchange the two
shift halves, and exchange the left and right sides. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementReverseParameter {N : Nat} (p : HigherArrangementParameter N) :
    HigherArrangementParameter N :=
  let a := p.1.1
  let z := p.1.2
  ((-a,![-z 0,-z 1,z 2+z 0,z 3+z 1,z 4+(a+z 0-z 1),z 5+a,z 6+z 0,z 7+z 1,z 8+(a+z 0-z 1)]),p.2+a)

def higherArrangementReverseCoordinate : Fin 16 → Fin 16 :=
  ![1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14]

theorem higherArrangementReverseParameter_involutive {N : Nat} :
    Function.Involutive (@higherArrangementReverseParameter N) := by
  intro p
  apply Prod.ext
  · apply Prod.ext
    · dsimp [higherArrangementReverseParameter]
      ring
    · funext j
      fin_cases j <;> dsimp [higherArrangementReverseParameter] <;> ring
  · dsimp [higherArrangementReverseParameter]
    ring

theorem higherArrangementReverse_endpoints {N : Nat} (p : HigherArrangementParameter N) (j : Fin 16) :
    higherArrangementEndpoints (higherArrangementReverseParameter p) j =
      higherArrangementEndpoints p (higherArrangementReverseCoordinate j) := by
  fin_cases j <;> dsimp [higherArrangementEndpoints,higherArrangementReverseParameter,higherArrangementReverseCoordinate] <;> ring

def higherArrangementReverse (N : Nat) : HigherArrangementSymmetry N :=
  HigherArrangementSymmetry.ofInvolutions higherArrangementReverseParameter higherArrangementReverseCoordinate
    higherArrangementReverseParameter_involutive (by intro j; fin_cases j <;> rfl)
    higherArrangementReverse_endpoints (by
      intro v h
      dsimp [higherArrangementReverseCoordinate]
      linear_combination -h)

def higherArrangementAdjacentParameter {N : Nat} (p : HigherArrangementParameter N) :
    HigherArrangementParameter N :=
  let a := p.1.1
  let z := p.1.2
  ((z 0,![a,a+z 0-z 1,p.2,z 4,z 3,z 6,z 5,z 8,z 7]),z 2)

def higherArrangementAdjacentCoordinate : Fin 16 → Fin 16 :=
  ![2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13]

theorem higherArrangementAdjacentParameter_involutive {N : Nat} :
    Function.Involutive (@higherArrangementAdjacentParameter N) := by
  intro p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      fin_cases j <;> dsimp [higherArrangementAdjacentParameter]
      ring
  · rfl

theorem higherArrangementAdjacent_endpoints {N : Nat} (p : HigherArrangementParameter N) (j : Fin 16) :
    higherArrangementEndpoints (higherArrangementAdjacentParameter p) j =
      higherArrangementEndpoints p (higherArrangementAdjacentCoordinate j) := by
  fin_cases j <;> dsimp [higherArrangementEndpoints,higherArrangementAdjacentParameter,higherArrangementAdjacentCoordinate] <;> ring

def higherArrangementAdjacent (N : Nat) : HigherArrangementSymmetry N :=
  HigherArrangementSymmetry.ofInvolutions higherArrangementAdjacentParameter higherArrangementAdjacentCoordinate
    higherArrangementAdjacentParameter_involutive (by intro j; fin_cases j <;> rfl)
    higherArrangementAdjacent_endpoints (by
      intro v h
      dsimp [higherArrangementAdjacentCoordinate]
      linear_combination h)

def higherArrangementHalfParameter {N : Nat} (p : HigherArrangementParameter N) :
    HigherArrangementParameter N :=
  let a := p.1.1
  let z := p.1.2
  ((z 1,![a+z 0-z 1,a,z 4,p.2,z 2,z 7,z 8,z 5,z 6]),z 3)

def higherArrangementHalfCoordinate : Fin 16 → Fin 16 :=
  ![4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11]

theorem higherArrangementHalfParameter_involutive {N : Nat} :
    Function.Involutive (@higherArrangementHalfParameter N) := by
  intro p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      fin_cases j <;> dsimp [higherArrangementHalfParameter]
      ring
  · rfl

theorem higherArrangementHalf_endpoints {N : Nat} (p : HigherArrangementParameter N) (j : Fin 16) :
    higherArrangementEndpoints (higherArrangementHalfParameter p) j =
      higherArrangementEndpoints p (higherArrangementHalfCoordinate j) := by
  fin_cases j <;> dsimp [higherArrangementEndpoints,higherArrangementHalfParameter,higherArrangementHalfCoordinate] <;> ring

def higherArrangementHalf (N : Nat) : HigherArrangementSymmetry N :=
  HigherArrangementSymmetry.ofInvolutions higherArrangementHalfParameter higherArrangementHalfCoordinate
    higherArrangementHalfParameter_involutive (by intro j; fin_cases j <;> rfl)
    higherArrangementHalf_endpoints (by
      intro v h
      dsimp [higherArrangementHalfCoordinate]
      linear_combination h)

def higherArrangementSidesParameter {N : Nat} (p : HigherArrangementParameter N) :
    HigherArrangementParameter N :=
  let a := p.1.1
  let z := p.1.2
  ((a,![z 0,z 1,z 6,z 7,z 8,p.2,z 2,z 3,z 4]),z 5)

def higherArrangementSidesCoordinate : Fin 16 → Fin 16 :=
  ![8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7]

theorem higherArrangementSidesParameter_involutive {N : Nat} :
    Function.Involutive (@higherArrangementSidesParameter N) := by
  intro p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      fin_cases j <;> rfl
  · rfl

theorem higherArrangementSides_endpoints {N : Nat} (p : HigherArrangementParameter N) (j : Fin 16) :
    higherArrangementEndpoints (higherArrangementSidesParameter p) j =
      higherArrangementEndpoints p (higherArrangementSidesCoordinate j) := by
  fin_cases j <;> rfl

def higherArrangementSides (N : Nat) : HigherArrangementSymmetry N :=
  HigherArrangementSymmetry.ofInvolutions higherArrangementSidesParameter higherArrangementSidesCoordinate
    higherArrangementSidesParameter_involutive (by intro j; fin_cases j <;> rfl)
    higherArrangementSides_endpoints (by
      intro v h
      dsimp [higherArrangementSidesCoordinate]
      linear_combination -h)

end LeanProofs.GowersSzemeredi
