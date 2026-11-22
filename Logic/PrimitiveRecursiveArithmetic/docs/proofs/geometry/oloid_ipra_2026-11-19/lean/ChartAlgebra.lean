import IPRADerivations.Core.PolynomialImplications

/-!
# Cleared polynomial identities for an oloid ruling

All coordinates below are *numerators* at a common positive denominator d.
Set Q = d+c, t = d-s.  The normal is N/d.  The vector W is d Q times
the difference between the two endpoints. E is a cleared tangent vector.
The resulting theorems are sequents of ConciseIPRA's object theory.

The ring certificates work even for inexact radical evaluations: the
linear combinations give explicit polynomial multiples of each residual.
-/

namespace Oloid.Chart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "d" => (ZExp.var 0 : ZExp 5)
local notation "c" => (ZExp.var 1 : ZExp 5)
local notation "a" => (ZExp.var 2 : ZExp 5)
local notation "b" => (ZExp.var 3 : ZExp 5)
local notation "s" => (ZExp.var 4 : ZExp 5)

def Q : ZExp 5 := d + c
def T : ZExp 5 := d - s
def M : ZExp 5 := d ^ 2 + (2 * d - 3 * s) * c

def circleEqs : List (ZExp 5 × ZExp 5) :=
  [(c ^ 2 + a ^ 2, d ^ 2), (c ^ 2 + b ^ 2, Q ^ 2)]

def N : Vec3 5 := ⟨-c, a, b⟩
def W : Vec3 5 := ⟨Q ^ 2 - c * d, -a * Q, b * d⟩
def E : Vec3 5 :=
  ⟨a * b * (T * Q ^ 2 + s * d ^ 2),
   T * b * c * Q ^ 2, s * a * c * d ^ 2⟩

/-- Twice d times the normal projection at the first endpoint. -/
theorem support_A :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs (c * (d + 2 * c) + 2 * a ^ 2, d * (2 * d + c))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q]
    obtain ⟨h₁, _⟩ := h
    linear_combination 2 * h₁)

/-- Twice Q times the same projection at the second endpoint. -/
theorem support_B :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs (-c * (Q - 2 * c) + 2 * b ^ 2, Q * (2 * d + c))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q]
    obtain ⟨_, h₂⟩ := h
    linear_combination 2 * h₂)

theorem normal_length :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs (dot N N, 2 * d * Q)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, N]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ + h₂)

theorem normal_perp_ruling :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs (dot N W, 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, N, W]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-(ρ 0 + ρ 1)) * h₁ + ρ 0 * h₂)

theorem ruling_length :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs (dot W W, 3 * d ^ 2 * Q ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, W]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 0 + ρ 1) ^ 2 * h₁ + ρ 0 ^ 2 * h₂)

/-- The two endpoint weights in the area factor are nonnegative on the chart. -/
theorem area_weight :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [] (M, T * (d + 2 * c) + s * (d - c))) :=
  derive_imp _ _ (by ipra_poly R ρ h [M, T]; ring)

/-- Q^2 d^2 M N is the cleared vector area. -/
theorem area_vector_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs ((cross W E).x, d ^ 2 * Q ^ 2 * M * N.x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, T, M, N, W, E]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination
      (-(ρ 1) * (ρ 0 + ρ 1) * ρ 4 * ρ 0 ^ 2) * h₁ +
      (-(ρ 1) * ρ 0 * (ρ 0 - ρ 4) * (ρ 0 + ρ 1) ^ 2) * h₂)

theorem area_vector_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs ((cross W E).y, d ^ 2 * Q ^ 2 * M * N.y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, T, M, N, W, E]
    obtain ⟨_, h₂⟩ := h
    linear_combination (ρ 2 * ρ 0 *
      ((ρ 0 - ρ 4) * (ρ 0 + ρ 1) ^ 2 + ρ 4 * ρ 0 ^ 2)) * h₂)

theorem area_vector_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp circleEqs ((cross W E).z, d ^ 2 * Q ^ 2 * M * N.z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [circleEqs, Q, T, M, N, W, E]
    obtain ⟨h₁, _⟩ := h
    linear_combination (ρ 3 * (ρ 0 + ρ 1) *
      ((ρ 0 - ρ 4) * (ρ 0 + ρ 1) ^ 2 + ρ 4 * ρ 0 ^ 2)) * h₁)

end Oloid.Chart
