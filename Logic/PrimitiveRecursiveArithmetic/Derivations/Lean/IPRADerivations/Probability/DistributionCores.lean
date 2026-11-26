import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.PolynomialInequalities

/-!
# The finite cores of the continuous laws

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/distributions.tex`, the finite arithmetic
behind the approximation contracts, as iPRA derivations about integer terms (`ZT`) and natural terms (rational
data cleared of denominators), with the certificates of `Core/IntCertificates`:

* `normalization_cauchy` (normalization theorem): quadratures `a_k`, `a_ℓ` within `e` of the finite integrals
  `I_k ≤ I_ℓ` whose difference is a tail at most `e` give `|a_ℓ − a_k| ≤ 3e` ("Thus
  `|a_ℓ − a_k| ≤ 3·2^{−k−2}`");
* `recip_bound`: "for positive `u, v ≥ z_0/2`, `|u⁻¹ − v⁻¹| ≤ 4 z_0^{−2} |u − v|`", cleared:
  `z_0² D ≤ 4 u v D` for `D = |u − v| ≥ 0`;
* `uniform_mean`, `uniform_var` (uniform law): `b² − a² = (b − a)(a + b)` (so `E X = (a + b)/2`) and
  `4(b³ − a³) − 3(b − a)(a + b)² = (b − a)³` (so `Var X = (b − a)²/12`);
* `third_moment` (`eq:normal-third`): "`2|x|³ ≤ x² + x⁴`", homogeneous in `x = a/N`:
  `2 a³ N ≤ a² N² + a⁴`, the certificate `a²(a − N)²`;
* `gaussian_exponent` (the identification `Z = √(2π)`): `4s + 2 ≤ 2(s + 1)²`, that is
  `3s − 2(s + 1)² ≤ −s − 2`, so `T e^{−R²/2} ≤ 2^{3s − 2(s+1)²} ≤ 2^{−s−2}`.
-/

namespace LeanProofs.IPRA.Probability.DistributionCores

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The normalization Cauchy estimate: `|a_ℓ − a_k| ≤ 3e`, two-sided. -/
theorem normalization_cauchy {ak al Ik Il e : ZT n} (hk₁ : Γ ⊢[PRAAx] zle (-e) (ak - Ik))
    (hk₂ : Γ ⊢[PRAAx] zle (ak - Ik) e) (hl₁ : Γ ⊢[PRAAx] zle (-e) (al - Il)) (hl₂ : Γ ⊢[PRAAx] zle (al - Il) e)
    (ht₁ : Γ ⊢[PRAAx] zle (ZT.natLit 0) (Il - Ik)) (ht₂ : Γ ⊢[PRAAx] zle (Il - Ik) e) :
    (Γ ⊢[PRAAx] zle (-(ZT.natLit 3 * e)) (al - ak)) ∧ (Γ ⊢[PRAAx] zle (al - ak) (ZT.natLit 3 * e)) := by
  refine ⟨?_, ?_⟩
  · ipra_zle zsl hl₁ + zsl hk₂ + 2 * zsl ht₁ + zsl ht₂
  · ipra_zle zsl hl₂ + zsl hk₁ + zsl ht₂

/-- The reciprocal bound, cleared: `z₀ ≤ 2u`, `z₀ ≤ 2v`, `z₀ ≥ 0`, `D ≥ 0` give `z₀² D ≤ 4uvD`. -/
theorem recip_bound {u v z D : ZT n} (hu : Γ ⊢[PRAAx] zle z (ZT.natLit 2 * u))
    (hv : Γ ⊢[PRAAx] zle z (ZT.natLit 2 * v)) (hz : Γ ⊢[PRAAx] zle (ZT.natLit 0) z)
    (hD : Γ ⊢[PRAAx] zle (ZT.natLit 0) D) :
    Γ ⊢[PRAAx] zle (z * z * D) (ZT.natLit 4 * u * v * D) := by
  ipra_zle zsl hD * (zsl hu * (zsl hv + zsl hz) + zsl hz * zsl hv)

/-- Uniform law, mean: `b² − a² = (b − a)(a + b)`. -/
theorem uniform_mean (a b : ZT n) : Γ ⊢[PRAAx] ZT.eq (b * b - a * a) ((b - a) * (a + b)) := by
  ipra_lc

/-- Uniform law, variance: `4(b³ − a³) − 3(b − a)(a + b)² = (b − a)³`. -/
theorem uniform_var (a b : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 4 * (b * b * b - a * a * a) - ZT.natLit 3 * (b - a) * ((a + b) * (a + b)))
      ((b - a) * (b - a) * (b - a)) := by
  ipra_lc

/-- `eq:normal-third`, cleared: `2 a³ N ≤ a² N² + a⁴`. -/
theorem third_moment (a N : PTm n) :
    Γ ⊢[PRAAx] le (num 2 * (a * a * a * N)) (a * a * (N * N) + a * a * a * a) := by
  refine le_of_comb ((𝔟 a) ^ 2 * ((𝔟 a - 𝔟 N) * (𝔟 a - 𝔟 N))) ?_ (nn_mul (nn_pow (nn_term _) 2) (nn_sq _))
  ipra_simps
  ring

/-- The Gaussian identification stage: `4s + 2 ≤ 2(s + 1)²`. -/
theorem gaussian_exponent (s : PTm n) : Γ ⊢[PRAAx] le (num 4 * s + num 2) (num 2 * (succ s * succ s)) := by
  refine le_of_comb (2 * 𝔟 s * 𝔟 s) ?_ (nn_mul (nn_mul (nn_ofNat 2) (nn_term _)) (nn_term _))
  ipra_simps
  ring

end LeanProofs.IPRA.Probability.DistributionCores
