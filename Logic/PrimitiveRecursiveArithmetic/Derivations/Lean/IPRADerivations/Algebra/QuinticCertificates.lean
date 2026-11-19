import IPRADerivations.Core.Integers

/-!
# Certificates for the Bring quintic

Packet: `algebra/bring_quintic_ipra_2026-11-16`:

* Theorem `thm:trinomial-discriminant` (`Disc_X(X⁵ + pX + q) = 256p⁵ + 3125q⁴`), the elimination form of
  its proof: "a common root has `X⁴ = −p/5` and `q = −4pX/5`; raising the latter equation to the fourth
  power and substituting the former yields the displayed relation";
* Corollary `cor:bring-odd-decreasing` ("Oddness …"): `BR(−a) = −BR(a)`, from the oddness of
  `x⁵ + x`;
* Theorem `thm:bring-lipschitz`, `eq:residual-bound`: `|q − BR(a)| ≤ |q⁵ + q + a|`, in squared
  certificate form.

With signed integer terms (`Core/Integers`):

* `disc_common_root`: if `X⁵ + pX + q = 0` and `5X⁴ + p = 0` are derivable, then `256p⁵ + 3125q⁴ = 0`.
  The certificate is the Bézout identity
  `256p⁵ + 3125q⁴ = (256p⁴ + 5CX)(5X⁴ + p) − 25C (X⁵ + pX + q)` with
  `C = u³ + u²w + uw² + w³`, `u = 4pX`, `w = −5q` (from `5f − Xg = 4pX + 5q` and
  `u⁴ − w⁴ = (u − w) C`);
* `bring_odd`: `(−x)⁵ + (−x) + (−a) = −(x⁵ + x + a)`, so `−x` solves the equation for `−a`;
* `residual_square`: if `x⁵ + x + a = 0`, then with
  `Σ = 3(2x² + xq)² + (3xq + 2q²)² + 8q⁴` (`= 12 S₄(x, q)`, a sum of squares),
  `144 (q⁵ + q + a)² = 144 (q − x)² + (q − x)² Σ (24 + Σ)`; the last term is a product of squares and
  sums of squares, which is the squared form of `|q − x| ≤ |q⁵ + q + a|`.

The discriminant as a resultant determinant, the real Bring radical and the order statements themselves
are not formalized here; `Algebra/Quintic` has the factorization behind strong monotonicity.
-/

namespace LeanProofs.IPRA.Algebra.QuinticCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:trinomial-discriminant`, elimination form: a common root of `X⁵ + pX + q` and its derivative
forces `256p⁵ + 3125q⁴ = 0`. -/
theorem disc_common_root {X p q : ZT n}
    (hf : Γ ⊢[PRAAx] ZT.eq (X * X * X * X * X + p * X + q) (ZT.natLit 0))
    (hg : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 5 * (X * X * X * X) + p) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 256 * (p * p * p * p * p) + ZT.natLit 3125 * (q * q * q * q))
      (ZT.natLit 0) := by
  have hf' := ZT.toZ_eq hf
  have hg' := ZT.toZ_eq hg
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at hf' hg' ⊢
  push_cast at hf' hg' ⊢
  generalize ZT.toZ Γ X = x at hf' hg' ⊢
  generalize ZT.toZ Γ p = P at hf' hg' ⊢
  generalize ZT.toZ Γ q = Qv at hf' hg' ⊢
  linear_combination
    (256 * P ^ 4 + 5 * ((4 * P * x) ^ 3 + (4 * P * x) ^ 2 * (-5 * Qv) + (4 * P * x) * (-5 * Qv) ^ 2 +
      (-5 * Qv) ^ 3) * x) * hg' -
    25 * ((4 * P * x) ^ 3 + (4 * P * x) ^ 2 * (-5 * Qv) + (4 * P * x) * (-5 * Qv) ^ 2 +
      (-5 * Qv) ^ 3) * hf'

/-- `cor:bring-odd-decreasing`, oddness: `(−x)⁵ + (−x) + (−a) = −(x⁵ + x + a)`. -/
theorem bring_odd (x a : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((-x) * (-x) * (-x) * (-x) * (-x) + (-x) + (-a))
      (-(x * x * x * x * x + x + a)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_neg]
    ring)

/-- `eq:residual-bound` in squared certificate form: if `x⁵ + x + a = 0`, then
`144 (q⁵ + q + a)² = 144 (q − x)² + (q − x)² Σ (24 + Σ)` with the sum of squares
`Σ = 3(2x² + xq)² + (3xq + 2q²)² + 8q⁴`. -/
theorem residual_square {x q a : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (x * x * x * x * x + x + a) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 144 * ((q * q * q * q * q + q + a) * (q * q * q * q * q + q + a)))
      (ZT.natLit 144 * ((q - x) * (q - x)) +
        (q - x) * (q - x) *
          ((ZT.natLit 3 * ((ZT.natLit 2 * (x * x) + x * q) * (ZT.natLit 2 * (x * x) + x * q)) +
              (ZT.natLit 3 * (x * q) + ZT.natLit 2 * (q * q)) *
                (ZT.natLit 3 * (x * q) + ZT.natLit 2 * (q * q)) +
              ZT.natLit 8 * (q * q * q * q)) *
            (ZT.natLit 24 +
              (ZT.natLit 3 * ((ZT.natLit 2 * (x * x) + x * q) * (ZT.natLit 2 * (x * x) + x * q)) +
                (ZT.natLit 3 * (x * q) + ZT.natLit 2 * (q * q)) *
                  (ZT.natLit 3 * (x * q) + ZT.natLit 2 * (q * q)) +
                ZT.natLit 8 * (q * q * q * q))))) := by
  have h' := ZT.toZ_eq h
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit] at h' ⊢
  push_cast at h' ⊢
  generalize ZT.toZ Γ x = X at h' ⊢
  generalize ZT.toZ Γ q = Qv at h' ⊢
  generalize ZT.toZ Γ a = A at h' ⊢
  have ha : A = -(X * X * X * X * X + X) := by linear_combination h'
  rw [ha]
  ring

end LeanProofs.IPRA.Algebra.QuinticCertificates
