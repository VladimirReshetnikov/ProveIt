import IPRADerivations.Probability.Variance
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.LinearCombination

/-!
# Triangle isoperimetry, with exact polynomial cores

Packet: `isoperimetric_ipra_constructive_2026-11-15`, `report/triangles.tex` (Theorem "Triangle
isoperimetry" and Theorem `thm:triangle-product`). A triangle is given by its Ravi variables
`x, y, z ≥ 0`: `a = y + z`, `b = z + x`, `c = x + y`, `s = x + y + z`, perimeter `ℓ = 2s`, and
`H = (a+b+c)(−a+b+c)(a−b+c)(a+b−c) = 16 s x y z = 16 T²`. With `|a − b| = (a ∸ b) + (b ∸ a)`:

* `amgm3` (reusable): `27 x y z ≤ (x + y + z)³`, from the sum-of-squares certificate
  `2((x+y+z)³ − 27xyz) = s Σ (x − y)² + 6 Σ z (x − y)²`;
* `pq_ge`: `9 x y z ≤ (x + y + z)(xy + yz + zx)`, from `pq − 9r = Σ x (y − z)²`;
* `abc_add`: `(x+y)(y+z)(z+x) + xyz = (x+y+z)(xy+yz+zx)`, i.e. `w = pq − r`;
* `triangle_isoperimetry`: `27 H ≤ ℓ⁴`, i.e. `ℓ² ≥ 12√3 T`;
* `triangle_product`: `H³ ≤ 27 (abc)⁴`, i.e. `4096 T⁶ ≤ 27 (abc)⁴` and `T ≤ (√3/4)(abc)^{2/3}`;
* `equilateral_iso`, `equilateral_product`: equality for `x = y = z`.

The square roots and the classification of the equality cases are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.TriangleIsoperimetry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos two_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(a − b)²` as a natural term. -/
abbrev sq2 (a b : PTm n) : PTm n := ad a b * ad a b

/-- Three-variable AM–GM: `27 x y z ≤ (x + y + z)³`. -/
theorem amgm3 (x y z : PTm n) : Γ ⊢[PRAAx] le (num 27 * (x * y * z)) ((x + y + z) * (x + y + z) * (x + y + z)) := by
  have fxy := natEq (ad_sq (Γ := Γ) x y); have fyz := natEq (ad_sq (Γ := Γ) y z)
  refine le_cancel_pos two_pos (le_of_eq_add (d := (x + y + z) * (sq2 x y + sq2 y z + sq2 z x) +
    num 6 * (z * sq2 x y + x * sq2 y z + y * sq2 z x)) ?_)
  ipra_lc (-(𝔞 x + 𝔞 y + 𝔞 z) - 6 * 𝔞 z) * fxy + (-(𝔞 x + 𝔞 y + 𝔞 z) - 6 * 𝔞 x) * fyz +
    (-(𝔞 x + 𝔞 y + 𝔞 z) - 6 * 𝔞 y) * natEq (ad_sq (Γ := Γ) z x)

/-- `9 x y z ≤ (x + y + z)(xy + yz + zx)`. -/
theorem pq_ge (x y z : PTm n) :
    Γ ⊢[PRAAx] le (num 9 * (x * y * z)) ((x + y + z) * (x * y + y * z + z * x)) := by
  have fxy := natEq (ad_sq (Γ := Γ) x y); have fyz := natEq (ad_sq (Γ := Γ) y z)
  refine le_of_eq_add (d := z * sq2 x y + x * sq2 y z + y * sq2 z x) ?_
  ipra_lc -𝔞 z * fxy - 𝔞 x * fyz - 𝔞 y * natEq (ad_sq (Γ := Γ) z x)

/-- `(x+y)(y+z)(z+x) + xyz = (x+y+z)(xy+yz+zx)`. -/
theorem abc_add (x y z : PTm n) :
    Γ ⊢[PRAAx] (x + y) * (y + z) * (z + x) + x * y * z ≐ (x + y + z) * (x * y + y * z + z * x) := by
  ipra_ring

/-- Triangle isoperimetry: `27 H ≤ ℓ⁴` with `H = 16 s x y z` and `ℓ = 2s`. -/
theorem triangle_isoperimetry (x y z : PTm n) :
    Γ ⊢[PRAAx] le (num 27 * (num 16 * ((x + y + z) * x * y * z)))
      (two * (x + y + z) * (two * (x + y + z)) * (two * (x + y + z)) * (two * (x + y + z))) := by
  have h := le_mul_mono (le_refl (num 16 * (x + y + z))) (amgm3 (Γ := Γ) x y z)
  refine le_congr ?_ ?_ h
  · ipra_ring
  · ipra_ring

/-- The stronger product-of-sides inequality: `H³ ≤ 27 (abc)⁴`. -/
theorem triangle_product (x y z : PTm n) :
    Γ ⊢[PRAAx] le ((num 16 * ((x + y + z) * x * y * z)) * (num 16 * ((x + y + z) * x * y * z)) *
        (num 16 * ((x + y + z) * x * y * z)))
      (num 27 * (((y + z) * (z + x) * (x + y)) * ((y + z) * (z + x) * (x + y)) *
        ((y + z) * (z + x) * (x + y)) * ((y + z) * (z + x) * (x + y)))) := by
  -- p = s, q = xy + yz + zx, r = xyz, w = abc
  have h₁ := pq_ge (Γ := Γ) x y z
  have h₂ := amgm3 (Γ := Γ) (x * y) (y * z) (z * x)
  -- 8 pq ≤ 9 w
  have h₃ : Γ ⊢[PRAAx] le (num 8 * ((x + y + z) * (x * y + y * z + z * x))) (num 9 * ((y + z) * (z + x) * (x + y))) := by
    refine le_of_eq_add (d := monus ((x + y + z) * (x * y + y * z + z * x)) (num 9 * (x * y * z))) ?_
    ipra_lc 9 * natEq (abc_add (Γ := Γ) x y z) + natEq (eq_add_of_le h₁)
  -- 243 r³ ≤ p q⁴
  have h₄ := le_mul_mono h₁ h₂
  have h₅ := le_mul_mono (le_mul_mono h₃ h₃) (le_mul_mono h₃ h₃)
  have h₆ := le_mul_mono (le_refl (num 4096 * ((x + y + z) * (x + y + z) * (x + y + z)))) h₄
  have big : Γ ⊢[PRAAx] le (num 243 * ((num 16 * ((x + y + z) * x * y * z)) * (num 16 * ((x + y + z) * x * y * z)) *
        (num 16 * ((x + y + z) * x * y * z))))
      (num 243 * (num 27 * (((y + z) * (z + x) * (x + y)) * ((y + z) * (z + x) * (x + y)) *
        ((y + z) * (z + x) * (x + y)) * ((y + z) * (z + x) * (x + y))))) := by
    refine le_congr ?_ ?_ (le_trans h₆ (le_congr (by ipra_ring) (.eqRefl _) h₅))
    · ipra_ring
    · ipra_ring
  have p243 : Γ ⊢[PRAAx] (num 243 : PTm n) ≐ succ (pred (num 243)) :=
    pos_of_eq_succ (c := num 242) (by apply deriveNat; ipra_simps; norm_num)
  exact le_cancel_pos p243 big

/-- Equality in triangle isoperimetry for the equilateral triangle `x = y = z = t`. -/
theorem equilateral_iso (t : PTm n) :
    Γ ⊢[PRAAx] num 27 * (num 16 * ((t + t + t) * t * t * t)) ≐
      two * (t + t + t) * (two * (t + t + t)) * (two * (t + t + t)) * (two * (t + t + t)) := by
  ipra_ring

/-- Equality in the product-of-sides inequality for the equilateral triangle. -/
theorem equilateral_product (t : PTm n) :
    Γ ⊢[PRAAx] (num 16 * ((t + t + t) * t * t * t)) * (num 16 * ((t + t + t) * t * t * t)) *
        (num 16 * ((t + t + t) * t * t * t)) ≐
      num 27 * (((t + t) * (t + t) * (t + t)) * ((t + t) * (t + t) * (t + t)) *
        ((t + t) * (t + t) * (t + t)) * ((t + t) * (t + t) * (t + t))) := by
  ipra_ring

end LeanProofs.IPRA.Geometry.TriangleIsoperimetry
