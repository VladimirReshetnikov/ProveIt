import Mathlib.Data.Int.Basic

/-!
# The 93-operation universal system (satellite work on Jones 1980)

The satellite article to the 1980 announcement measures the complexity of a
system of Diophantine equations by the number of additions and
multiplications of a straight-line certificate that verifies a proposed
solution (fixed numerals free, intermediates reused, every power by repeated
multiplication).  The final system reached by the successive reductions —
`Papers/1980/FACTORED_MASK_93_PROOF.md` and `SHIFTED_AFFINE_94_PROOF.md`,
building on `AFFINE_RADIX_95_PROOF.md`, receipt
`Papers/verification/round34_1980_factored_mask_certificate.json` — has 93
operations (50 multiplications, 43 additions): 22 equations in 34 positive
unknowns with the four supplied parameters `x, V, H, Tindex`.  The three
parameters `V, H, Tindex` form the *admissible index* of the represented set;
they do not depend on the input.

This module transcribes that system.  Every equation is the source residual
of the receipt (the receipt writes the defining expression of `σ` in place
of `σ` inside the packing equation `E7`; the two forms are equivalent by
`ES`).  Subtraction is interpreted over the integers, as in the 1982 article.
The agreement of each field with the receipt's `source_residual_polynomial`
is checked by `Papers/verification/lean_sys93_transcription_check.py`.

Abbreviations of the notes, written out here: `B = θ + 4 = H + b + 4` (the
shifted affine radix), `C = x + g`, `U = w n²`, `Y = s n²`, `Q = U Y²`, `A = a + 4`,
`A² − 1 = a² + 8a + 15`, `J = 2r + 1`, `v = o f − d²`,
`K_aux = (A² − 1)(f² − 1) = (i c²)²`,
`S = g + q²(l + e q + q² σ)`, `T⁺ = q²(1 + θλ) − b l + θ l q⁴`.

Relative to the 99-operation system `Sys99`: the combined code bound
`l + e + α = q` replaces `l + e q + α = q²`; the radix is `H + b + 4` instead of
`H b²`; the first packed mask is `q² − 1 − b l`; the auxiliary Pell norm is
the relaxed `(i c²)² = (A² − 1)(f² − 1)`; and `σ = (λ − e)(q − (x + g)²)`
with `Ω = λ − e`.
-/

namespace Jones1980

/-- The 22 equations of the 93-operation system. -/
structure Sys93 (x V H Tindex : ℕ)
    (a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ) : Prop where
  /-- `E1`: the combined code bound with positive slack, `l + e + α = q`. -/
  E1 : l + e + α = q
  /-- `E1b`: `b = x + β`, so `b > x`. -/
  E1b : b = x + β
  /-- `E2`: the geometric equation `λ(B − 1) = q² − 1` with `B = H + b + 4`. -/
  E2 : lam + q ^ 2 = 1 + lam * (H + b + 4)
  /-- `E3`: `θ = H + b`, so `B = θ + 4`. -/
  E3 : θ = H + b
  /-- `E4/E5` packed: the base-four congruence `l + e q = V + t θ`. -/
  E45 : l + e * q = V + t * θ
  /-- `E6`: `n = q⁸`. -/
  E6 : n = q ^ 8
  /-- `E7`: the central code `r = S(n² − n) + T⁺(n² − 1)`. -/
  E7 : (r : ℤ) = ((g : ℤ) + q ^ 2 * (l + e * q + q ^ 2 * σ)) * ((n : ℤ) ^ 2 - n) +
    ((q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4) * ((n : ℤ) ^ 2 - 1)
  /-- `E9`: the first Pell norm `τ(τ + 1) = Q(Q + 1) k²`, `Q = U Y²`. -/
  E9 : τ * (τ + 1) = (w * n ^ 2 * (s * n ^ 2) ^ 2) * (w * n ^ 2 * (s * n ^ 2) ^ 2 + 1) * k ^ 2
  /-- `E10a`: the positive interval `c = k Y + η`. -/
  E10a : c = k * (s * n ^ 2) + η
  /-- `E10b`: `k = η + ζ`, so `η < k`. -/
  E10b : k = η + ζ
  /-- `E11`: the first index congruence `k = r + 1 + h U Y`. -/
  E11 : k = r + 1 + h * (w * n ^ 2) * (s * n ^ 2)
  /-- `E12`: the main Pell parameter shift `a = Y(U + 1)`; the parameter is `A = a + 4`. -/
  E12 : a = s * n ^ 2 * (w * n ^ 2 + 1)
  /-- `E13`: the gap `c = κ + φ`. -/
  E13 : c = κ + φ
  /-- `E14`: the base-four exponent congruence `d = U + a c + γ(8a + 15)`. -/
  E14 : d = w * n ^ 2 + a * c + γ * (8 * a + 15)
  /-- `E15`: the main Pell norm `d² = 1 + (A² − 1) c²`. -/
  E15 : d ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * c ^ 2
  /-- `E16`: the relaxed auxiliary Pell norm `(i c²)² = (A² − 1)(f² − 1)`. -/
  E16 : (i * c ^ 2) ^ 2 = (a ^ 2 + 8 * a + 15) * (f ^ 2 - 1)
  /-- `E17`: the doubled-index signed norm `v(v + 1) = K_aux(K_aux − 1)(2r + 1 + j c)²`. -/
  E17 : ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
    (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1)) * (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1) - 1) *
      (2 * r + 1 + j * c) ^ 2
  /-- `E18`: the second exponent congruence `μ = q + κ(A − B) + ρ(2AB − B² − 1)`. -/
  E18 : (μ : ℤ) = q + κ * ((a : ℤ) + 4 - (H + b + 4)) +
    ρ * (2 * ((a : ℤ) + 4) * (H + b + 4) - ((H : ℤ) + b + 4) ^ 2 - 1)
  /-- `E19`: the second main Pell norm `μ² = 1 + (A² − 1) κ²`. -/
  E19 : μ ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * κ ^ 2
  /-- `E20`: the fixed index `κ = Tindex + Δ a`. -/
  E20 : κ = Tindex + Δ * a
  /-- `S3_positive`: `σ = (λ − e)(q − (x + g)²)`. -/
  ES : (σ : ℤ) = ((lam : ℤ) - e) * (q - (x + g) ^ 2)
  /-- `coefficient_positive`: `Ω = λ − e`. -/
  EΩ : (Ω : ℤ) = lam - e

/-- Solvability of the system in positive integers, for the input `x` and the
index `(V, H, Tindex)`. -/
def Solvable93 (x V H Tindex : ℕ) : Prop :=
  ∃ a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧ 0 < i ∧ 0 < j ∧
    0 < k ∧ 0 < l ∧ 0 < n ∧ 0 < o ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < w ∧ 0 < α ∧
    0 < γ ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧ 0 < τ ∧ 0 < φ ∧ 0 < κ ∧ 0 < μ ∧ 0 < ρ ∧ 0 < Δ ∧
    0 < β ∧ 0 < ζ ∧ 0 < σ ∧ 0 < Ω ∧
    Sys93 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ Ω

end Jones1980
