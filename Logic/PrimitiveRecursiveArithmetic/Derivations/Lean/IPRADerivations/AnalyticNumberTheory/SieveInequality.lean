import IPRADerivations.AnalyticNumberTheory.SieveMajorant
import IPRADerivations.AnalyticNumberTheory.SieveClosedForms

/-!
# The sieve inequality for arbitrary signed weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
summing the majorant `eq:sieve-majorant` over the progression, expanding the square and applying `eq:crt-count` to
every pair gives, for every weight vector `λ`,

  `(λ_1)² · S ≤ (x/q) · Σ_{d,e} λ_d λ_e / [d, e] + (Σ_d |λ_d|)²`,

where `S` counts the `n ≤ x` of the progression that the sieve keeps.

For signed weights `λ = λ⁺ − λ⁻` with natural parts given by bodies `U^±` (`λ^±_d = d [d ≥ 1][gcd(d, q) = 1] U^±_d`),
`q = fst P ≥ 2`, `gcd(a₀, q) = 1` and `Z ≥ 2`, with `a = λ⁺_1`, `b = λ⁻_1`, the bilinear forms
`G^{st} = Σ_{d<Z} Σ_{e<Z} [d ≥ 1] u^s_d v^t_e gcd(d, e)` and the sums `L^± = Σ_{d<Z} λ^±_d`, the statement cleared of
signs is `sieve_ineq`:

  `q (a² + b²) S + X (G⁺⁻ + G⁻⁺) ≤ X (G⁺⁺ + G⁻⁻) + q (L⁺ + L⁻)² + q · 2ab · S`,

that is `q (a − b)² S ≤ X (G⁺⁺ + G⁻⁻ − G⁺⁻ − G⁻⁺) + q (L⁺ + L⁻)²`. It combines `SieveMajorant.majorant` with
`SieveClosedForms.bil_le` (for `(+,+)`, `(−,−)`) and `bil_ge` (for `(+,−)`, `(−,+)`).

The quadratic form is not yet evaluated through `SieveDiagonal.diag`, and no weights are chosen here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveInequality

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (cB lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU sgV bil_le bil_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant (S0 Nb majorant)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Lb)
open LeanProofs.IPRA.Probability.Independence (dsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The combination over opaque terms. -/
theorem combine {q X S K1 K2 Npp Nnn Npn Nnp Gpp Gnn Gpn Gnp Lp Ln : PTm n}
    (M : Γ ⊢[PRAAx] le (K1 * S + (Npn + Nnp)) ((Npp + Nnn) + K2 * S))
    (h1 : Γ ⊢[PRAAx] le (q * Npp) (X * Gpp + q * (Lp * Lp)))
    (h2 : Γ ⊢[PRAAx] le (q * Nnn) (X * Gnn + q * (Ln * Ln)))
    (h3 : Γ ⊢[PRAAx] le (X * Gpn) (q * Npn + q * (Lp * Ln)))
    (h4 : Γ ⊢[PRAAx] le (X * Gnp) (q * Nnp + q * (Ln * Lp))) :
    Γ ⊢[PRAAx] le (q * (K1 * S) + X * (Gpn + Gnp))
      (X * (Gpp + Gnn) + q * ((Lp + Ln) * (Lp + Ln)) + q * (K2 * S)) := by
  ipra_le 𝔞 q * sl M + sl h1 + sl h2 + sl h3 + sl h4

/-- The sieve inequality for arbitrary signed weights, cleared of signs. -/
theorem sieve_ineq (UP UN : PTm 2) {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) (hZ : Γ ⊢[PRAAx] lt one Z) :
    Γ ⊢[PRAAx] le
      (fstT P * ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          ap2 (sumF S0) X (pairT Z (pairT Z P))) +
        X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UN))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UP))) Z Z (pairT X P)))
      (X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UP))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UN))) Z Z (pairT X P)) +
        fstT P * ((ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P)) *
          (ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P))) +
        fstT P * ((two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) *
          ap2 (sumF S0) X (pairT Z (pairT Z P)))) :=
  combine (majorant UP UN (X := X) (P := P) hZ) (bil_le UP UP hq ha) (bil_le UN UN hq ha) (bil_ge UP UN hq ha)
    (bil_ge UN UP hq ha)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveInequality
