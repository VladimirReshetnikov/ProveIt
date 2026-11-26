import IPRADerivations.DiophantineNumberTheory.FractionCount
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.Core.Header

/-!
# The arithmetic of the Khinchin block (`hurwitz_khinchin_ipra`, (K10)–(K11))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"A finite block covers a fixed
fraction of every interval": from `∫F ≥ LST/128`, `∫F² ≤ L(S²/16 + 11S/24)` and Cauchy–Schwarz,
`|⋃_k E_k| ≥ L/16384` when `S ≥ 1`.

On the grid of `T` cells, with `u_k = Q_k² w_k`, the block quantities are
`ΣE = Σ_k |E_k|`, `ΣL = Σ_ℓ Σ_{k<ℓ} |E_k ∩ E_ℓ|`, `ΣU = Σ_k u_k`, `ΣC = Σ_ℓ u_ℓ Σ_{k<ℓ} u_k`, and
`V = |⋃_k E_k|`. `block_arith` derives the conclusion from the five summed estimates

* (K8): `D ΣU ≤ 16β ΣE` and `β ΣE ≤ 2D ΣU`;
* (K9) summed with `Σ_{k<ℓ} Q_k² ≤ Q_ℓ²/3`: `3βT ΣL ≤ 12D ΣC + 5DT ΣU`;
* `2ΣC ≤ (ΣU)²` (`KhinchinMoment.cross_le`);
* Cauchy–Schwarz with the ordered moment (`Foundations/SecondMoment`): `(ΣE)² ≤ V (ΣE + 2ΣL)`;

together with `S ≥ 1`, i.e. `T ≤ 4ΣU`, and `D, β, T ≥ 1`:

  `D T ≤ 8192 β V`,                                                             (`block_arith`)

which is `|⋃_k E_k| / T ≥ L/16384` for `L = 2D/β`. The proof: `3βT(ΣE + 2ΣL) ≤ 76 D (ΣU)²`
(`moment_le`), `(DΣU)² ≤ 256β²(ΣE)²`, the chain `3βT(DΣU)² ≤ 19456 β² V D (ΣU)²`, and two
cancellations (by `βD(ΣU)²`, then by `3`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockArith

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.DiophantineNumberTheory.FractionCount (pos_of_le_one)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The second moment against the first: `3βT(ΣE + 2ΣL) ≤ 76 D (ΣU)²`. -/
theorem moment_le {SE SL SU SC T D β : PTm n}
    (h2 : Γ ⊢[PRAAx] le (β * SE) (num 2 * D * SU))
    (h3 : Γ ⊢[PRAAx] le (num 3 * β * T * SL) (num 12 * D * SC + num 5 * D * T * SU))
    (h4 : Γ ⊢[PRAAx] le (two * SC) (SU * SU)) (hT : Γ ⊢[PRAAx] le T (num 4 * SU)) :
    Γ ⊢[PRAAx] le (num 3 * β * T * (SE + two * SL)) (num 76 * D * (SU * SU)) := by
  ipra_le 3 * 𝔞 T * sl h2 + 2 * sl h3 + 12 * 𝔞 D * sl h4 + 16 * 𝔞 D * 𝔞 SU * sl hT

/-- The first moment squared: `(DΣU)² ≤ 256β²(ΣE)²`. -/
theorem first_sq {SE SU D β : PTm n} (h1 : Γ ⊢[PRAAx] le (D * SU) (num 16 * β * SE)) :
    Γ ⊢[PRAAx] le (D * SU * (D * SU)) (num 256 * (β * β) * (SE * SE)) := by
  ipra_le sl h1 * (16 * 𝔞 β * 𝔞 SE + 𝔞 D * 𝔞 SU)

/-- `1 ≤ T ≤ 4 ΣU` gives `ΣU ≥ 1`. -/
theorem su_pos {SU T : PTm n} (hT1 : Γ ⊢[PRAAx] T ≐ succ (pred T)) (hT : Γ ⊢[PRAAx] le T (num 4 * SU)) :
    Γ ⊢[PRAAx] SU ≐ succ (pred SU) := by
  refine .orE (zero_or_succ SU) ?_ ?_
  · let Θ : List (Fm PTm n) := (SU ≐ zero) :: Γ
    have e0 := natEq (Prf.hyp0 : Θ ⊢[PRAAx] SU ≐ zero)
    have e1 := natEq (hT1.wk : Θ ⊢[PRAAx] T ≐ succ (pred T))
    have hT' : Θ ⊢[PRAAx] le T (num 4 * SU) := hT.wk
    have hz : Θ ⊢[PRAAx] le one zero := by ipra_le sl hT' + 𝔞 (pred T) with e1 - 4 * e0
    exact .botE _ (succ_ne_zero ((monus_zero _).eqSymm.eqTrans hz))
  · exact Prf.hyp0

/-- (K11), the arithmetic: `D T ≤ 8192 β V`, i.e. `|⋃_k E_k| ≥ L T/16384` for `L = 2D/β`. -/
theorem block_arith {SE SL SU SC V T D β : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (hβ : Γ ⊢[PRAAx] β ≐ succ (pred β)) (hT1 : Γ ⊢[PRAAx] T ≐ succ (pred T))
    (h1 : Γ ⊢[PRAAx] le (D * SU) (num 16 * β * SE)) (h2 : Γ ⊢[PRAAx] le (β * SE) (num 2 * D * SU))
    (h3 : Γ ⊢[PRAAx] le (num 3 * β * T * SL) (num 12 * D * SC + num 5 * D * T * SU))
    (h4 : Γ ⊢[PRAAx] le (two * SC) (SU * SU)) (hcs : Γ ⊢[PRAAx] le (SE * SE) (V * (SE + two * SL)))
    (hT : Γ ⊢[PRAAx] le T (num 4 * SU)) : Γ ⊢[PRAAx] le (D * T) (num 8192 * β * V) := by
  have a := moment_le h2 h3 h4 hT
  have b := first_sq h1
  have c : Γ ⊢[PRAAx] le (num 3 * β * T * (D * SU * (D * SU))) (num 19456 * (β * β) * V * D * (SU * SU)) := by
    ipra_le 3 * 𝔞 β * 𝔞 T * sl b + 768 * 𝔞 β * 𝔞 β * 𝔞 β * 𝔞 T * sl hcs + 256 * 𝔞 β * 𝔞 β * 𝔞 V * sl a
  have hSU := su_pos hT1 hT
  have hN : Γ ⊢[PRAAx] β * D * (SU * SU) ≐ succ (pred (β * D * (SU * SU))) :=
    pos_mul' (pos_mul' hβ hD) (pos_mul' hSU hSU)
  have d : Γ ⊢[PRAAx] le (num 3 * T * D) (num 19456 * β * V) := cancel_le hN (by ipra_le sl c)
  have h3' : Γ ⊢[PRAAx] (num 3 : PTm n) ≐ succ (pred (num 3)) := congrSucc (pred_succ _).eqSymm
  exact cancel_le h3' (by ipra_le sl d + 5120 * 𝔞 β * 𝔞 V)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockArith
