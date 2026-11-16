import IPRADerivations.Core.LinearAlgebra
import Mathlib.Algebra.Ring.GeomSum

/-!
# Identities used by the quantitative frameworks

* `ipra_finite_use_framework_2026-11-15` (`sections/06_quantitative.tex`), the product
  contract: `ab − a'b' = (a − a')b + a'(b − b')`.
* `ipra_cfp_contract_compiler_2026-11-15` (`paper/sections/09_cubic.tex`), the
  monotonicity of `y³ + y` used in the cubic bisection:
  `(y³ + y) − (z³ + z) = (y − z)(y² + yz + z² + 1)`.
* `ipra_embedding_framework_2026-11-15` (`sections/06_represented_objects.tex`), the
  difference of powers behind its Lipschitz bound, as a schema in `k`:
  `xᵏ − yᵏ = (x − y) ∑_{i<k} xⁱ y^{k−1−i}`.
* `goldbach_euler_ipra` (`goldbach_euler_ipra.tex`), the geometric identity as a
  schema in `k`: `xᵏ = (x − 1) ∑_{i<k} xⁱ + 1`.
* `zeta_zeros_ipra_2026-11-15` (`sections/elementary.tex`), the polynomial form of
  `3 + 4 cos u + cos 2u = 2 (1 + cos u)² ≥ 0`: `3 + 4c + (2c² − 1) = 2(1 + c)²`.
* `gamma_ipra` (T1) and `ipra_stable_observables` (`04_jacobi.tex`), the rational
  parametrisation of the circle: `(1 − t²)² + (2t)² = (1 + t²)²`.
-/

namespace LeanProofs.IPRA.Foundations.QuantitativeIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-- `uᵏ` as an iterated product. -/
def zpow {m : ℕ} (u : ZT m) : ℕ → ZT m
  | 0 => ZT.natLit 1
  | k + 1 => zpow u k * u

@[simp] theorem toZ_zpow {m : ℕ} {Γ : List (Fm PTm m)} (u : ZT m) (k : ℕ) :
    ZT.toZ Γ (zpow u k) = ZT.toZ Γ u ^ k := by
  induction k with
  | zero => simp [zpow]
  | succ k ih => simp [zpow, ih, pow_succ]

section Products

abbrev a : ZT 8 := .var2 0 1
abbrev b : ZT 8 := .var2 2 3
abbrev a' : ZT 8 := .var2 4 5
abbrev b' : ZT 8 := .var2 6 7

def productContractFormula : Fm PTm 8 :=
  ZT.eq (a * b - a' * b') ((a - a') * b + a' * (b - b'))

theorem product_contract : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 productContractFormula :=
  closeUniv 8 (by unfold productContractFormula; ipra_ring)

end Products

section Cubic

abbrev y : ZT 4 := .var2 0 1
abbrev z : ZT 4 := .var2 2 3

def cubicFormula : Fm PTm 4 :=
  ZT.eq ((y * y * y + y) - (z * z * z + z)) ((y - z) * (y * y + y * z + z * z + ZT.natLit 1))

theorem cubic_difference : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 cubicFormula :=
  closeUniv 4 (by unfold cubicFormula; ipra_ring)

/-- `xᵏ − yᵏ = (x − y) ∑_{i<k} xⁱ y^{k−1−i}`, one iPRA theorem for each `k`. -/
def powDiffFormula (k : ℕ) : Fm PTm 4 :=
  ZT.eq (zpow y k - zpow z k) ((y - z) * ZT.sumFin fun i : Fin k => zpow y i * zpow z (k - 1 - i))

theorem pow_difference (k : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (powDiffFormula k) := by
  refine closeUniv 4 (ZT.derive ?_)
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sumFin, toZ_zpow]
  rw [Fin.sum_univ_eq_sum_range (fun i => ZT.toZ [] y ^ i * ZT.toZ [] z ^ (k - 1 - i)) k,
    _root_.mul_comm, Commute.geom_sum₂_mul (Commute.all _ _)]

/-- `xᵏ = (x − 1) ∑_{i<k} xⁱ + 1`, one iPRA theorem for each `k`. -/
def geomFormula (k : ℕ) : Fm PTm 4 :=
  ZT.eq (zpow y k) ((y - ZT.natLit 1) * ZT.sumFin (fun i : Fin k => zpow y i) + ZT.natLit 1)

theorem geometric_sum (k : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (geomFormula k) := by
  refine closeUniv 4 (ZT.derive ?_)
  simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sumFin, toZ_zpow, ZT.toZ_natLit,
    Nat.cast_one]
  rw [Fin.sum_univ_eq_sum_range (fun i => ZT.toZ [] y ^ i) k, _root_.mul_comm, geom_sum_mul]
  ring

end Cubic

section Trigonometric

abbrev c : ZT 2 := .var2 0 1

def zetaZerosFormula : Fm PTm 2 :=
  ZT.eq (ZT.natLit 3 + ZT.natLit 4 * c + (ZT.natLit 2 * ZT.sq c - ZT.natLit 1))
    (ZT.natLit 2 * ZT.sq (ZT.natLit 1 + c))

theorem zeta_zeros_cosine : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 zetaZerosFormula :=
  closeUniv 2 (by unfold zetaZerosFormula; ipra_ring)

abbrev t : ZT 2 := .var2 0 1

def circleFormula : Fm PTm 2 :=
  ZT.eq (ZT.sq (ZT.natLit 1 - ZT.sq t) + ZT.sq (ZT.natLit 2 * t)) (ZT.sq (ZT.natLit 1 + ZT.sq t))

theorem circle_parametrisation : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 circleFormula :=
  closeUniv 2 (by unfold circleFormula; ipra_ring)

end Trigonometric

end LeanProofs.IPRA.Foundations.QuantitativeIdentities
