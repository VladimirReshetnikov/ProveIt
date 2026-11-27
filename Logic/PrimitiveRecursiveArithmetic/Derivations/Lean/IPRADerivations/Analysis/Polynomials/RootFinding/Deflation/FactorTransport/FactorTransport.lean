import IPRADerivations.Core.CertificateTactics

/-!
# Certified factor transport: the contraction arithmetic

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/05_factors.tex`, Theorem
`thm:factortransport` ("Certified factor transport") and `eq:factorstability`, the inequalities between
coefficient norms, as iPRA derivations (norms as natural terms cleared of a common denominator; the scalar
identities as integer-term equations). The halving and the finite geometric tail `eq:factorstep`,
`eq:factortail` are `Analysis/SignedPolysolver.poly_step`, `poly_tail`.

* `split_product`: "write `uv − u'v' = (u − u')v + u'(v − v')`";
* `gain_bound`: "`‖uv − u'v'‖_1 ≤ ρ(‖u − u'‖_1 + ‖v − v'‖_1) = ρ‖z − z'‖`", from the two product bounds and
  `‖v‖, ‖u'‖ ≤ ρ`;
* `ball_preserved` (`eq:factorball`): "`‖S(E − uv)‖ ≤ Kε + K‖u‖_1‖v‖_1 ≤ ρ/2 + Kρ² ≤ 3ρ/4`. Thus the map
  preserves the ball with spare room", from `Kε ≤ ρ/2` and `Kρ² ≤ ρ/4` (`eq:factorcertificate`);
* `quarter_gain`: the update has gain at most `Kρ ≤ 1/4`: `‖Tz − Tz'‖ ≤ K‖uv − u'v'‖` gives
  `4‖Tz − Tz'‖ ≤ ‖z − z'‖` (cleared);
* `residual_identity`: "`f − (g_0 + u)(h_0 + v) = E − ℒz − uv`" with `E = f − g_0 h_0`, `ℒz = h_0 u + g_0 v`;
* `stability` (`eq:factorstability`): "`‖z_{n+1} − z̃_{n+1}‖ ≤ K‖f − f̃‖_1 + ½‖z_n − z̃_n‖`. Since both initial
  corrections are zero, finite induction gives `‖z_n − z̃_n‖ ≤ 2K‖f − f̃‖_1` for every `n`".
-/

namespace LeanProofs.IPRA.Analysis.FactorTransport

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `uv − u'v' = (u − u')v + u'(v − v')`. -/
theorem split_product (u v u' v' : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (u * v - u' * v') ((u - u') * v + u' * (v - v')) := by
  ipra_lc

/-- The gain of the product: `P ≤ a V + U' b`, `V ≤ ρ`, `U' ≤ ρ` give `P ≤ ρ (a + b)`. -/
theorem gain_bound {P a b V U' ρ : PTm n} (hP : Γ ⊢[PRAAx] le P (a * V + U' * b)) (hV : Γ ⊢[PRAAx] le V ρ)
    (hU : Γ ⊢[PRAAx] le U' ρ) : Γ ⊢[PRAAx] le P (ρ * (a + b)) := by
  ipra_le sl hP + 𝔟 a * sl hV + sl hU * 𝔟 b

/-- `eq:factorball`: `T ≤ A + B` with `2A ≤ ρ` (`Kε ≤ ρ/2`) and `4B ≤ ρ` (`K‖u‖‖v‖ ≤ Kρ² ≤ ρ/4`) gives
`4T ≤ 3ρ`. -/
theorem ball_preserved {T A B ρ : PTm n} (hT : Γ ⊢[PRAAx] le T (A + B)) (hA : Γ ⊢[PRAAx] le (num 2 * A) ρ)
    (hB : Γ ⊢[PRAAx] le (num 4 * B) ρ) : Γ ⊢[PRAAx] le (num 4 * T) (num 3 * ρ) := by
  ipra_le 4 * sl hT + 2 * sl hA + sl hB

/-- The quarter gain: `D ≤ K P`, `P ≤ ρ d` and `4 K ρ ≤ J` give `4 D ≤ J d` (`J` the unit of the scale of
`K ρ`). -/
theorem quarter_gain {D K P ρ d J : PTm n} (hD : Γ ⊢[PRAAx] le D (K * P)) (hP : Γ ⊢[PRAAx] le P (ρ * d))
    (hK : Γ ⊢[PRAAx] le (num 4 * (K * ρ)) J) : Γ ⊢[PRAAx] le (num 4 * D) (J * d) := by
  ipra_le 4 * sl hD + 4 * 𝔟 K * sl hP + sl hK * 𝔟 d

/-- The exact residual identity: `f − (g₀ + u)(h₀ + v) = (f − g₀ h₀) − (h₀ u + g₀ v) − u v`. -/
theorem residual_identity (f g₀ h₀ u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (f - (g₀ + u) * (h₀ + v)) (f - g₀ * h₀ - (h₀ * u + g₀ * v) - u * v) := by
  ipra_lc

/-- `eq:factorstability`: `d_0 = 0` and `2 d_{k+1} ≤ 2B + d_k` give `d_k ≤ 2B` for every `k`. -/
theorem stability (d : ℕ → PTm n) (B : PTm n) (h0 : Γ ⊢[PRAAx] le (d 0) zero)
    (hstep : ∀ k, Γ ⊢[PRAAx] le (num 2 * d (k + 1)) (num 2 * B + d k)) (k : ℕ) :
    Γ ⊢[PRAAx] le (d k) (num 2 * B) := by
  induction k with
  | zero => ipra_le sl h0 + 2 * 𝔟 B
  | succ k ih =>
    have hk := hstep k
    apply le_of_two_mul
    ipra_le sl hk + sl ih

end LeanProofs.IPRA.Analysis.FactorTransport
