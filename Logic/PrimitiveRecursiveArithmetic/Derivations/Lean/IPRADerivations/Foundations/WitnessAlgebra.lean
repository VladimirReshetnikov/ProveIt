import IPRADerivations.Core.PolynomialImplications

/-!
# Integrality certificates (`ipra_presentations_to_witnesses`, Sections 3 and 4)

Packet: `foundations/ipra_presentations_to_witnesses`. Two divisibility arguments of the
packet are identities over the integers once the coprimality hypotheses are given by their
Bezout coefficients. They are derived as polynomial implications
(`Core/PolynomialImplications`): each integer variable is a difference of two natural-number
variables and every statement is a closed sentence of iPRA.

**`lem:integer-eigenvalue`, integrality** (dimensions `2` and `3`). Let `w A = (a / b) w` for
an integer matrix `A` and an integer row vector `w`, that is `a w_j = b ∑_i w_i A_{ij}`. Let
`w` be primitive with `∑_j e_j w_j = 1`, and let `a / b` be reduced with `r a + s b = 1`. Then
`b` is a unit:

`b · ∑_j e_j (r ∑_i w_i A_{ij} + s w_j) = 1`

(`eigen_unit_2`, `eigen_unit_3`). This is the proof of the packet: `w_j = (r a + s b) w_j` is
a multiple of `b`, and then so is `1 = ∑ e_j w_j`.

**`lem:norm-rational-roots`, equation (RR2)** (degrees `2` and `3`). Let
`c_0 q^d + c_1 p q^{d−1} + … + c_d p^d = 0` and `u p + v q = 1`. Then `p ∣ c_0` and
`q ∣ c_d`, with explicit cofactors (`root_num_2`, `root_den_2`, `root_num_3`, `root_den_3`):
for example in degree `2`,

`c_0 = p · (c_0 u² p + 2 c_0 u v q − v² (c_1 q + c_2 p))`.

Not derived: these statements for an arbitrary dimension or degree (they need sums of
variable length), the bound `|λ| ≤ R(A)`, the scan over candidate roots and the remaining
algebraic sections of the packet.
-/

namespace LeanProofs.IPRA.Foundations.WitnessAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## Integer eigenvalues, dimension `2` -/

section Eigen2

local notation "wa" => (ZExp.var 0 : ZExp 12)
local notation "wb" => (ZExp.var 1 : ZExp 12)
local notation "m11" => (ZExp.var 2 : ZExp 12)
local notation "m12" => (ZExp.var 3 : ZExp 12)
local notation "m21" => (ZExp.var 4 : ZExp 12)
local notation "m22" => (ZExp.var 5 : ZExp 12)
local notation "na" => (ZExp.var 6 : ZExp 12)
local notation "nb" => (ZExp.var 7 : ZExp 12)
local notation "ea" => (ZExp.var 8 : ZExp 12)
local notation "eb" => (ZExp.var 9 : ZExp 12)
local notation "br" => (ZExp.var 10 : ZExp 12)
local notation "bs" => (ZExp.var 11 : ZExp 12)

/-- `w A = (a / b) w` cleared of the denominator, primitivity of `w` and reducedness of
`a / b`, the last two by Bezout coefficients. -/
abbrev eigen2 : List (ZExp 12 × ZExp 12) :=
  [(na * wa, nb * (wa * m11 + wb * m21)), (na * wb, nb * (wa * m12 + wb * m22)),
    (ea * wa + eb * wb, 1), (br * na + bs * nb, 1)]

/-- The denominator of a rational eigenvalue of an integer `2 × 2` matrix with a primitive
integer eigenvector is a unit. -/
theorem eigen_unit_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 12)
      (imp eigen2
        (nb * (ea * (br * (wa * m11 + wb * m21) + bs * wa) +
          eb * (br * (wa * m12 + wb * m22) + bs * wb)), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination h₃ + (ρ 8 * ρ 0 + ρ 9 * ρ 1) * h₄ - ρ 10 * (ρ 8 * h₁ + ρ 9 * h₂))

end Eigen2

/-! ## Integer eigenvalues, dimension `3` -/

section Eigen3

local notation "wa" => (ZExp.var 0 : ZExp 19)
local notation "wb" => (ZExp.var 1 : ZExp 19)
local notation "wc" => (ZExp.var 2 : ZExp 19)
local notation "m11" => (ZExp.var 3 : ZExp 19)
local notation "m12" => (ZExp.var 4 : ZExp 19)
local notation "m13" => (ZExp.var 5 : ZExp 19)
local notation "m21" => (ZExp.var 6 : ZExp 19)
local notation "m22" => (ZExp.var 7 : ZExp 19)
local notation "m23" => (ZExp.var 8 : ZExp 19)
local notation "m31" => (ZExp.var 9 : ZExp 19)
local notation "m32" => (ZExp.var 10 : ZExp 19)
local notation "m33" => (ZExp.var 11 : ZExp 19)
local notation "na" => (ZExp.var 12 : ZExp 19)
local notation "nb" => (ZExp.var 13 : ZExp 19)
local notation "ea" => (ZExp.var 14 : ZExp 19)
local notation "eb" => (ZExp.var 15 : ZExp 19)
local notation "ec" => (ZExp.var 16 : ZExp 19)
local notation "br" => (ZExp.var 17 : ZExp 19)
local notation "bs" => (ZExp.var 18 : ZExp 19)

/-- The three columns `∑_i w_i A_{ij}`. -/
abbrev col1 : ZExp 19 := wa * m11 + wb * m21 + wc * m31
abbrev col2 : ZExp 19 := wa * m12 + wb * m22 + wc * m32
abbrev col3 : ZExp 19 := wa * m13 + wb * m23 + wc * m33

abbrev eigen3 : List (ZExp 19 × ZExp 19) :=
  [(na * wa, nb * col1), (na * wb, nb * col2), (na * wc, nb * col3),
    (ea * wa + eb * wb + ec * wc, 1), (br * na + bs * nb, 1)]

/-- The denominator of a rational eigenvalue of an integer `3 × 3` matrix with a primitive
integer eigenvector is a unit. -/
theorem eigen_unit_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 19)
      (imp eigen3
        (nb * (ea * (br * col1 + bs * wa) + eb * (br * col2 + bs * wb) +
          ec * (br * col3 + bs * wc)), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    linear_combination h₄ + (ρ 14 * ρ 0 + ρ 15 * ρ 1 + ρ 16 * ρ 2) * h₅ -
      ρ 17 * (ρ 14 * h₁ + ρ 15 * h₂ + ρ 16 * h₃))

end Eigen3

/-! ## Rational roots, degree `2` -/

section Root2

local notation "c0" => (ZExp.var 0 : ZExp 7)
local notation "c1" => (ZExp.var 1 : ZExp 7)
local notation "c2" => (ZExp.var 2 : ZExp 7)
local notation "rp" => (ZExp.var 3 : ZExp 7)
local notation "rq" => (ZExp.var 4 : ZExp 7)
local notation "bu" => (ZExp.var 5 : ZExp 7)
local notation "bv" => (ZExp.var 6 : ZExp 7)

/-- (RR2) in degree `2` and the Bezout relation of the reduced root `p / q`. -/
abbrev root2 : List (ZExp 7 × ZExp 7) :=
  [(c0 * rq ^ 2 + c1 * rp * rq + c2 * rp ^ 2, 0), (bu * rp + bv * rq, 1)]

/-- The numerator of a reduced rational root divides the constant coefficient. -/
theorem root_num_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp root2
        (c0, rp * (c0 * bu ^ 2 * rp + 2 * c0 * bu * bv * rq - bv ^ 2 * (c1 * rq + c2 * rp)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 6) ^ 2 * h₁ - ρ 0 * (ρ 5 * ρ 3 + ρ 6 * ρ 4 + 1) * h₂)

/-- The denominator of a reduced rational root divides the leading coefficient. -/
theorem root_den_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp root2
        (c2, rq * (c2 * bv ^ 2 * rq + 2 * c2 * bu * bv * rp - bu ^ 2 * (c1 * rp + c0 * rq)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 5) ^ 2 * h₁ - ρ 2 * (ρ 5 * ρ 3 + ρ 6 * ρ 4 + 1) * h₂)

end Root2

/-! ## Rational roots, degree `3` -/

section Root3

local notation "c0" => (ZExp.var 0 : ZExp 8)
local notation "c1" => (ZExp.var 1 : ZExp 8)
local notation "c2" => (ZExp.var 2 : ZExp 8)
local notation "c3" => (ZExp.var 3 : ZExp 8)
local notation "rp" => (ZExp.var 4 : ZExp 8)
local notation "rq" => (ZExp.var 5 : ZExp 8)
local notation "bu" => (ZExp.var 6 : ZExp 8)
local notation "bv" => (ZExp.var 7 : ZExp 8)

/-- `u p + v q`. -/
abbrev bez : ZExp 8 := bu * rp + bv * rq

/-- (RR2) in degree `3` and the Bezout relation of the reduced root `p / q`. -/
abbrev root3 : List (ZExp 8 × ZExp 8) :=
  [(c0 * rq ^ 3 + c1 * rp * rq ^ 2 + c2 * rp ^ 2 * rq + c3 * rp ^ 3, 0), (bez, 1)]

/-- The numerator of a reduced rational root divides the constant coefficient. -/
theorem root_num_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp root3
        (c0, rp * (c0 * bu * (bez ^ 2 + bez * (bv * rq) + (bv * rq) ^ 2) -
          bv ^ 3 * (c1 * rq ^ 2 + c2 * rp * rq + c3 * rp ^ 2)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 7) ^ 3 * h₁ -
      ρ 0 * ((ρ 6 * ρ 4 + ρ 7 * ρ 5) ^ 2 + (ρ 6 * ρ 4 + ρ 7 * ρ 5) + 1) * h₂)

/-- The denominator of a reduced rational root divides the leading coefficient. -/
theorem root_den_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp root3
        (c3, rq * (c3 * bv * (bez ^ 2 + bez * (bu * rp) + (bu * rp) ^ 2) -
          bu ^ 3 * (c2 * rp ^ 2 + c1 * rp * rq + c0 * rq ^ 2)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (ρ 6) ^ 3 * h₁ -
      ρ 3 * ((ρ 6 * ρ 4 + ρ 7 * ρ 5) ^ 2 + (ρ 6 * ρ 4 + ρ 7 * ρ 5) + 1) * h₂)

end Root3

end LeanProofs.IPRA.Foundations.WitnessAlgebra
