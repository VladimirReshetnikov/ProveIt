import IPRADerivations.Geometry.PowerCover
import IPRADerivations.Geometry.PowerCover3

/-!
# Principal-cover gluing

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (`thm:principal-gluing`,
`cor:equalizer`). The ring is the integers and the module is the ring itself; the derivations use
only ring identities, so they do not depend on cancellation. Letters `Qᵢ` stand for the common
denominator powers `fᵢ^q`.

* `cross_common`: an overlap witness `W (f_j^N aᵢ − fᵢ^N a_j) = 0`, enlarged to the kill factor
  `fᵢ^(K+1) f_j^(K+1) = V W`, gives `f_j^q bᵢ = fᵢ^q b_j` for `bᵢ = fᵢ^(K+1) aᵢ`,
  `fᵢ^q = fᵢ^N fᵢ^(K+1)`;
* `glue₂`, `glue₃`: from a cover `∑ dᵢ Qᵢ = 1` and the cross identities `Q_j bᵢ = Qᵢ b_j`, the
  section `m = ∑ dᵢ bᵢ` satisfies `Q_j m = b_j` on every chart;
* `restrict_witness`: `Q m = b` with `b = K (L m_j)` and `Q = (K L) F` is the localization
  witness `(K L)(F m − 1 · m_j) = 0` that `m/1 = m_j / f_j^(n_j)`;
* `unique₂`, `unique₃`: if `Qᵢ (m − m') = 0` on every chart and `∑ uᵢ Qᵢ = 1`, then `m = m'`;
* `glue_power₂`, `glue_power₃`: the same with the denominators `fᵢ^(k+1)` and the coefficients of
  the power-cover constructor (`Geometry/PowerCover`, `Geometry/PowerCover3`): from the cover
  certificate `∑ cᵢ fᵢ = 1` alone, for every `k`.

A number of charts given as a parameter, modules other than the ring, and the atlas and sheaf
constructions are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.Gluing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔷" t:max => ZT.toZ _ t

/-! ## The cross identity -/

/-- `eq:cross-common`. Here `Ni = fᵢ^N`, `Nj = f_j^N`, `Ki = fᵢ^(K+1)`, `Kj = f_j^(K+1)`. -/
theorem cross_common {W V Ni Nj Ki Kj ai aj : ZT n}
    (hw : Γ ⊢[PRAAx] ZT.eq (W * (Nj * ai - Ni * aj)) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] ZT.eq (Ki * Kj) (V * W)) :
    Γ ⊢[PRAAx] ZT.eq ((Nj * Kj) * (Ki * ai)) ((Ni * Ki) * (Kj * aj)) := by
  have ew := ZT.toZ_eq hw; have ev := ZT.toZ_eq hv
  apply ZT.derive
  ipra_simps
  linear_combination (𝔷(Nj) * 𝔷(ai) - 𝔷(Ni) * 𝔷(aj)) * ev + 𝔷(V) * ew

/-! ## Existence -/

section Two

variable {d₀ d₁ Q₀ Q₁ b₀ b₁ : ZT n}

/-- Two charts: `m = d₀ b₀ + d₁ b₁` restricts to `b₀` and `b₁`. -/
theorem glue₂ (hc : Γ ⊢[PRAAx] ZT.eq (d₀ * Q₀ + d₁ * Q₁) (ZT.natLit 1))
    (hx : Γ ⊢[PRAAx] ZT.eq (Q₁ * b₀) (Q₀ * b₁)) :
    Γ ⊢[PRAAx] ZT.eq (Q₀ * (d₀ * b₀ + d₁ * b₁)) b₀ ⋏ ZT.eq (Q₁ * (d₀ * b₀ + d₁ * b₁)) b₁ := by
  have ec := ZT.toZ_eq hc; have ex := ZT.toZ_eq hx
  refine .andI ?_ ?_
  · apply ZT.derive
    ipra_simps
    linear_combination 𝔷(b₀) * ec - 𝔷(d₁) * ex
  · apply ZT.derive
    ipra_simps
    linear_combination 𝔷(b₁) * ec + 𝔷(d₀) * ex

/-- Two charts: sections with the same restrictions are equal. -/
theorem unique₂ {u₀ u₁ m m' : ZT n} (hc : Γ ⊢[PRAAx] ZT.eq (u₀ * Q₀ + u₁ * Q₁) (ZT.natLit 1))
    (h₀ : Γ ⊢[PRAAx] ZT.eq (Q₀ * (m - m')) (ZT.natLit 0))
    (h₁ : Γ ⊢[PRAAx] ZT.eq (Q₁ * (m - m')) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq m m' := by
  have ec := ZT.toZ_eq hc; have e₀ := ZT.toZ_eq h₀; have e₁ := ZT.toZ_eq h₁
  apply ZT.derive
  ipra_simps
  linear_combination -(𝔷(m) - 𝔷(m')) * ec + 𝔷(u₀) * e₀ + 𝔷(u₁) * e₁

end Two

section Three

variable {d₀ d₁ d₂ Q₀ Q₁ Q₂ b₀ b₁ b₂ : ZT n}

/-- Three charts: `m = d₀ b₀ + d₁ b₁ + d₂ b₂` restricts to each `b_j`. -/
theorem glue₃ (hc : Γ ⊢[PRAAx] ZT.eq (d₀ * Q₀ + d₁ * Q₁ + d₂ * Q₂) (ZT.natLit 1))
    (h₀₁ : Γ ⊢[PRAAx] ZT.eq (Q₁ * b₀) (Q₀ * b₁)) (h₀₂ : Γ ⊢[PRAAx] ZT.eq (Q₂ * b₀) (Q₀ * b₂))
    (h₁₂ : Γ ⊢[PRAAx] ZT.eq (Q₂ * b₁) (Q₁ * b₂)) :
    Γ ⊢[PRAAx] ZT.eq (Q₀ * (d₀ * b₀ + d₁ * b₁ + d₂ * b₂)) b₀ ⋏
      (ZT.eq (Q₁ * (d₀ * b₀ + d₁ * b₁ + d₂ * b₂)) b₁ ⋏ ZT.eq (Q₂ * (d₀ * b₀ + d₁ * b₁ + d₂ * b₂)) b₂) := by
  have ec := ZT.toZ_eq hc
  have e₀₁ := ZT.toZ_eq h₀₁; have e₀₂ := ZT.toZ_eq h₀₂; have e₁₂ := ZT.toZ_eq h₁₂
  refine .andI ?_ (.andI ?_ ?_)
  · apply ZT.derive
    ipra_simps
    linear_combination 𝔷(b₀) * ec - 𝔷(d₁) * e₀₁ - 𝔷(d₂) * e₀₂
  · apply ZT.derive
    ipra_simps
    linear_combination 𝔷(b₁) * ec + 𝔷(d₀) * e₀₁ - 𝔷(d₂) * e₁₂
  · apply ZT.derive
    ipra_simps
    linear_combination 𝔷(b₂) * ec + 𝔷(d₀) * e₀₂ + 𝔷(d₁) * e₁₂

/-- Three charts: sections with the same restrictions are equal. -/
theorem unique₃ {u₀ u₁ u₂ m m' : ZT n}
    (hc : Γ ⊢[PRAAx] ZT.eq (u₀ * Q₀ + u₁ * Q₁ + u₂ * Q₂) (ZT.natLit 1))
    (h₀ : Γ ⊢[PRAAx] ZT.eq (Q₀ * (m - m')) (ZT.natLit 0))
    (h₁ : Γ ⊢[PRAAx] ZT.eq (Q₁ * (m - m')) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Q₂ * (m - m')) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq m m' := by
  have ec := ZT.toZ_eq hc; have e₀ := ZT.toZ_eq h₀; have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  linear_combination -(𝔷(m) - 𝔷(m')) * ec + 𝔷(u₀) * e₀ + 𝔷(u₁) * e₁ + 𝔷(u₂) * e₂

end Three

/-! ## The restriction witness -/

/-- `Q m = b`, `b = K (L m_j)`, `Q = (K L) F` give `(K L)(F m − 1 · m_j) = 0`: the witness, with
killing exponent `q − n_j`, that `m / 1 = m_j / f_j^(n_j)`. -/
theorem restrict_witness {Q m b K L F mj : ZT n} (hQ : Γ ⊢[PRAAx] ZT.eq (Q * m) b)
    (hb : Γ ⊢[PRAAx] ZT.eq b (K * (L * mj))) (hq : Γ ⊢[PRAAx] ZT.eq Q ((K * L) * F)) :
    Γ ⊢[PRAAx] ZT.eq ((K * L) * (F * m - ZT.natLit 1 * mj)) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq hQ; have e₂ := ZT.toZ_eq hb; have e₃ := ZT.toZ_eq hq
  apply ZT.derive
  ipra_simps
  linear_combination e₁ + e₂ - 𝔷(m) * e₃

/-! ## Gluing from the cover certificate alone -/

section Power

open LeanProofs.IPRA.Geometry

/-- Two charts with denominators `fᵢ^(k+1)`: the coefficients come from `PowerCover.st k x`. -/
theorem glue_power₂ {x : PTm n} (hu : Γ ⊢[PRAAx] PowerCover.Cover x) (k : PTm n) {b₀ b₁ : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq ((PowerCover.F1 x * PowerCover.Qk x k) * b₀)
      ((PowerCover.F0 x * PowerCover.Pk x k) * b₁)) :
    Γ ⊢[PRAAx]
      ZT.eq ((PowerCover.F0 x * PowerCover.Pk x k) *
        (PowerCover.D0 (PowerCover.st k x) * b₀ + PowerCover.D1 (PowerCover.st k x) * b₁)) b₀ ⋏
      ZT.eq ((PowerCover.F1 x * PowerCover.Qk x k) *
        (PowerCover.D0 (PowerCover.st k x) * b₀ + PowerCover.D1 (PowerCover.st k x) * b₁)) b₁ :=
  glue₂ (PowerCover.power_cover hu k) hx

/-- `fᵢ^(k+1)` for the three-chart parameter code. -/
abbrev q0 (x k : PTm n) : ZT n := ZT.ofNat (PowerCover3.g0 x) * ZT.ofNat (pw (PowerCover3.g0 x) k)
abbrev q1 (x k : PTm n) : ZT n := ZT.ofNat (PowerCover3.g1 x) * ZT.ofNat (pw (PowerCover3.g1 x) k)
abbrev q2 (x k : PTm n) : ZT n := ZT.ofNat (PowerCover3.g2 x) * ZT.ofNat (pw (PowerCover3.g2 x) k)

/-- Three charts with denominators `fᵢ^(k+1)`: the coefficients come from `PowerCover3.st k x`. -/
theorem glue_power₃ {x : PTm n} (hu : Γ ⊢[PRAAx] PowerCover3.Cover x) (k : PTm n) {b₀ b₁ b₂ : ZT n}
    (h₀₁ : Γ ⊢[PRAAx] ZT.eq (q1 x k * b₀) (q0 x k * b₁))
    (h₀₂ : Γ ⊢[PRAAx] ZT.eq (q2 x k * b₀) (q0 x k * b₂))
    (h₁₂ : Γ ⊢[PRAAx] ZT.eq (q2 x k * b₁) (q1 x k * b₂)) :
    Γ ⊢[PRAAx]
      ZT.eq (q0 x k * (PowerCover3.D0 (PowerCover3.st k x) * b₀ + PowerCover3.D1 (PowerCover3.st k x) * b₁ +
        PowerCover3.D2 (PowerCover3.st k x) * b₂)) b₀ ⋏
      (ZT.eq (q1 x k * (PowerCover3.D0 (PowerCover3.st k x) * b₀ + PowerCover3.D1 (PowerCover3.st k x) * b₁ +
        PowerCover3.D2 (PowerCover3.st k x) * b₂)) b₁ ⋏
       ZT.eq (q2 x k * (PowerCover3.D0 (PowerCover3.st k x) * b₀ + PowerCover3.D1 (PowerCover3.st k x) * b₁ +
        PowerCover3.D2 (PowerCover3.st k x) * b₂)) b₂) :=
  glue₃ (d₀ := PowerCover3.D0 (PowerCover3.st k x)) (d₁ := PowerCover3.D1 (PowerCover3.st k x))
    (d₂ := PowerCover3.D2 (PowerCover3.st k x)) (Q₀ := q0 x k) (Q₁ := q1 x k) (Q₂ := q2 x k)
    (PowerCover3.power_cover₃ hu k) h₀₁ h₀₂ h₁₂

end Power

end LeanProofs.IPRA.Geometry.Gluing
