import Mathlib.Data.Int.Basic

/-!
# The 90-operation universal system (satellite work on Jones 1980)

The binary coefficient compiler and the matching base-two Pell shift
(`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, `BASE_TWO_PELL_90_PROOF.md`,
building on `PRODUCT_BOUND_91_PROOF.md` and `HALF_PARAMETER_PELL_92_PROOF.md`;
receipt `Papers/verification/round37_1980_binary_product_certificate.json`)
give a system with 90 operations (48 multiplications, 42 additions): 22
equations in 34 positive unknowns with the supplied parameters `x, V, H, Tindex`.

Relative to the 93-operation system `Sys93`: the coding equations are
`σ = (e − l)(x + g)²` and `l + σ + α = q` (no supplied `Ω`); the radix is
`B = H + b + 2` (`θ = H + b = B − 2`), so the geometric equation reads
`λ(B − 1) = q² − 1`; the main Pell base is `A = a + 2` (`A² − 1 = a² + 4a + 3`,
exponent modulus `4a + 3`); and the doubled-index signed norm is replaced by
the half-parameter block `u = 2r + 1 + jc = c + of`,
`(A² − 1)(f² − 1)(u² − y²) = 1 − y²` with the new unknown `y = y_aux`.

Every equation is the source residual of the receipt; the agreement of each
field with the receipt's `source_residual_polynomial` is checked by
`Papers/verification/lean_sys90_transcription_check.py`.  Subtraction is
interpreted over the integers.
-/

namespace Jones1980

/-- The 22 equations of the 90-operation system. -/
structure Sys90 (x V H Tindex : ℕ)
    (a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ) : Prop where
  /-- `positive_product_bound`: `l + σ + α = q`. -/
  E1 : l + σ + α = q
  /-- `E1b`: `b = x + β`. -/
  E1b : b = x + β
  /-- `E2`: the geometric equation `λ(B − 1) = q² − 1` with `B = H + b + 2`. -/
  E2 : lam + q ^ 2 = 1 + lam * (H + b + 2)
  /-- `E3`: `θ = H + b`. -/
  E3 : θ = H + b
  /-- `E4/E5` packed: `l + e q = V + t θ`. -/
  E45 : l + e * q = V + t * θ
  /-- `E6`: `n = q⁸`. -/
  E6 : n = q ^ 8
  /-- `E7`: `r = S(n² − n) + T⁺(n² − 1)`. -/
  E7 : (r : ℤ) = ((g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ)) * ((n : ℤ) ^ 2 - n) +
    ((q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4) * ((n : ℤ) ^ 2 - 1)
  /-- `E9`: the first Pell norm. -/
  E9 : τ * (τ + 1) = (w * n ^ 2 * (s * n ^ 2) ^ 2) * (w * n ^ 2 * (s * n ^ 2) ^ 2 + 1) * k ^ 2
  /-- `E10a`: `c = k Y + η`. -/
  E10a : c = k * (s * n ^ 2) + η
  /-- `E10b`: `k = η + ζ`. -/
  E10b : k = η + ζ
  /-- `E11`: `k = r + 1 + h U Y`. -/
  E11 : k = r + 1 + h * (w * n ^ 2) * (s * n ^ 2)
  /-- `E12`: `a = Y(U + 1)`. -/
  E12 : a = s * n ^ 2 * (w * n ^ 2 + 1)
  /-- `E13`: `c = κ + φ`. -/
  E13 : c = κ + φ
  /-- `E14`: the base-two exponent congruence `d = U + a c + γ(4a + 3)`. -/
  E14 : d = w * n ^ 2 + a * c + γ * (4 * a + 3)
  /-- `E15`: the main Pell norm with `A = a + 2`. -/
  E15 : d ^ 2 = 1 + (a ^ 2 + 4 * a + 3) * c ^ 2
  /-- `E16`: the relaxed auxiliary norm. -/
  E16 : (i * c ^ 2) ^ 2 = (a ^ 2 + 4 * a + 3) * (f ^ 2 - 1)
  /-- `E17`: the half-parameter norm `K(u² − y²) = 1 − y²`, `K = (A² − 1)(f² − 1)`,
  `u = 2r + 1 + jc`. -/
  E17 : (((a : ℤ) ^ 2 + 4 * a + 3) * (f ^ 2 - 1)) * ((2 * r + 1 + j * c) ^ 2 - (y : ℤ) ^ 2) =
    1 - (y : ℤ) ^ 2
  /-- `E17` normalized-root congruence: `2r + 1 + jc = c + of`. -/
  E17b : 2 * r + 1 + j * c = c + o * f
  /-- `E18`: the second exponent congruence with `A = a + 2`, `B = H + b + 2`. -/
  E18 : (μ : ℤ) = q + κ * ((a : ℤ) + 2 - (H + b + 2)) +
    ρ * (2 * ((a : ℤ) + 2) * (H + b + 2) - ((H : ℤ) + b + 2) ^ 2 - 1)
  /-- `E19`: the second main Pell norm. -/
  E19 : μ ^ 2 = 1 + (a ^ 2 + 4 * a + 3) * κ ^ 2
  /-- `E20`: the fixed index `κ = Tindex + Δ a`. -/
  E20 : κ = Tindex + Δ * a
  /-- `positive_product`: `σ = (e − l)(x + g)²`. -/
  ES : (σ : ℤ) = ((e : ℤ) - l) * ((x : ℤ) + g) ^ 2

/-- Solvability in positive integers for the input `x` and the index `(V, H, Tindex)`. -/
def Solvable90 (x V H Tindex : ℕ) : Prop :=
  ∃ a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧ 0 < i ∧ 0 < j ∧
    0 < k ∧ 0 < l ∧ 0 < n ∧ 0 < o ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧
    0 < γ ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧ 0 < κ ∧ 0 < μ ∧ 0 < ρ ∧ 0 < Δ ∧
    0 < β ∧ 0 < ζ ∧ 0 < σ ∧ 0 < y ∧
    Sys90 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y

end Jones1980
