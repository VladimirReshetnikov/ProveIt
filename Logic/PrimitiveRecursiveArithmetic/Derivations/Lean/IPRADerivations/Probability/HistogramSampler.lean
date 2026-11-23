import IPRADerivations.Core.IntCertificates

/-!
# The histogram sampler and the coherent realization: the finite budgets

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/realization.tex`, "An explicit histogram
sampler" and Theorem `thm:density-realization`, the finite inequalities between masses and distances, as iPRA
derivations (masses and CDF values as integer terms `ZT`, distances and budgets as natural terms, all cleared
of a common denominator). The coupling identity itself is `Probability/MonotoneCoupling`.

* `exact_mass`: "add an atom at zero of weight `1 − ∑_j p_j`. These are nonnegative dyadic weights summing
  exactly to one": with `p_0 = N − S` and `S ≤ N`, `S + p_0 = N` and `p_0 ≥ 0`;
* `histogram_cdf` (`eq:histogram-cdf`): the cell mass and the omitted and rounded masses, each at most `η/4`,
  give `|F_{μ_k}(t) − F(t)| ≤ 3η/4 ≤ η`;
* `tail_mass`: "`μ_j(|x| > K_k) ≤ ε_k/16 + 2η_j` by the two one-sided CDF comparisons";
* `band_mass`: "`μ_k([t − δ, t + δ]) ≤ ∫_{t−δ}^{t+δ} q + 2η_k`";
* `clipped_coupling` (`eq:coupling-clipped`): the clipped coupling bound plus the two exceptional masses;
* `realization_budget`: "`d_0(Q_k, Q_l) ≤ 2(K_k + 1)(η_k + η_l) + ε_k/8 ≤ ε_k/16 + ε_k/8 < ε_k`", with
  `64 (K + 1) η_k = ε` and `η_l ≤ η_k`: `16 d_0 ≤ 3ε`.
-/

namespace LeanProofs.IPRA.Probability.HistogramSampler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The weights sum exactly to one: `p₀ = N − S` with `S ≤ N` gives `S + p₀ = N` and `p₀ ≥ 0`. -/
theorem exact_mass {S p₀ N : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq p₀ (N - S)) (hS : Γ ⊢[PRAAx] zle S N) :
    (Γ ⊢[PRAAx] ZT.eq (S + p₀) N) ∧ (Γ ⊢[PRAAx] zle (ZT.natLit 0) p₀) := by
  have e := ZT.toZ_eq hp
  simp only [ZT.toZ_sub] at e
  refine ⟨?_, ?_⟩
  · apply ZT.derive
    simp only [ZT.toZ_add]
    linear_combination e
  · refine zle_of_comb (zsl hS) ?_ (nn_zsl _)
    zsimp
    linear_combination e

/-- `eq:histogram-cdf`: `|ΔF| ≤ c + o₁ + o₂` with `4c, 4o₁, 4o₂ ≤ η` gives `4|ΔF| ≤ 3η`, two-sided. -/
theorem histogram_cdf {ΔF c o₁ o₂ η : ZT n} (h₁ : Γ ⊢[PRAAx] zle (-(c + o₁ + o₂)) ΔF)
    (h₂ : Γ ⊢[PRAAx] zle ΔF (c + o₁ + o₂)) (hc : Γ ⊢[PRAAx] zle (ZT.natLit 4 * c) η)
    (ho₁ : Γ ⊢[PRAAx] zle (ZT.natLit 4 * o₁) η) (ho₂ : Γ ⊢[PRAAx] zle (ZT.natLit 4 * o₂) η) :
    (Γ ⊢[PRAAx] zle (-(ZT.natLit 3 * η)) (ZT.natLit 4 * ΔF)) ∧
      (Γ ⊢[PRAAx] zle (ZT.natLit 4 * ΔF) (ZT.natLit 3 * η)) := by
  refine ⟨?_, ?_⟩
  · ipra_zle 4 * zsl h₁ + zsl hc + zsl ho₁ + zsl ho₂
  · ipra_zle 4 * zsl h₂ + zsl hc + zsl ho₁ + zsl ho₂

/-- The tail of the finite law: `μ(|x| > K) = (1 − Fμ(K)) + Fμ(−K)`, the true tail at most `τ` and the two CDF
comparisons within `η` give `μ(|x| > K) ≤ τ + 2η`. -/
theorem tail_mass {mu Fp Fm Gp Gm one τ η : ZT n} (hmu : Γ ⊢[PRAAx] ZT.eq mu (one - Fp + Fm))
    (hτ : Γ ⊢[PRAAx] zle (one - Gp + Gm) τ) (hp : Γ ⊢[PRAAx] zle (Gp - Fp) η)
    (hm : Γ ⊢[PRAAx] zle (Fm - Gm) η) : Γ ⊢[PRAAx] zle mu (τ + ZT.natLit 2 * η) := by
  have e := ZT.toZ_eq hmu
  simp only [ZT.toZ_sub, ZT.toZ_add] at e
  refine zle_of_comb (zsl hτ + zsl hp + zsl hm) ?_ (by znn)
  zsimp
  linear_combination -e

/-- The band of the finite law: `Fμ(t+δ) − Fμ(t−δ) ≤ (F(t+δ) − F(t−δ)) + 2η`. -/
theorem band_mass {Fμa Fμb Fa Fb η : ZT n} (ha : Γ ⊢[PRAAx] zle (Fa - Fμa) η)
    (hb : Γ ⊢[PRAAx] zle (Fμb - Fb) η) : Γ ⊢[PRAAx] zle (Fμb - Fμa) (Fb - Fa + ZT.natLit 2 * η) := by
  ipra_zle zsl ha + zsl hb

/-- `eq:coupling-clipped`: `d_0(Q_μ, Q_ν) ≤ d_0` of the clipped tables plus the two exceptional masses, and the
clipped distance is at most `2K sup |F_μ − F_ν|`. -/
theorem clipped_coupling {d dc K s m₁ m₂ : PTm n} (hclip : Γ ⊢[PRAAx] le d (dc + m₁ + m₂))
    (hcoup : Γ ⊢[PRAAx] le dc (num 2 * K * s)) : Γ ⊢[PRAAx] le d (num 2 * K * s + m₁ + m₂) := by
  ipra_le sl hclip + sl hcoup

/-- The Cauchy budget of the realization: `16 d_0(Q_k, Q_l) ≤ 3ε`. -/
theorem realization_budget {D K ηk ηl T ε : PTm n}
    (hD : Γ ⊢[PRAAx] le D (num 2 * (K + succ zero) * (ηk + ηl) + T))
    (hη : Γ ⊢[PRAAx] le ηl ηk) (hε : Γ ⊢[PRAAx] num 64 * (K + succ zero) * ηk ≐ ε)
    (hT : Γ ⊢[PRAAx] le (num 8 * T) ε) : Γ ⊢[PRAAx] le (num 16 * D) (num 3 * ε) := by
  have e := natEq hε
  ipra_le 16 * sl hD + 32 * (𝔟 K + 1) * sl hη + 2 * sl hT with e

end LeanProofs.IPRA.Probability.HistogramSampler
