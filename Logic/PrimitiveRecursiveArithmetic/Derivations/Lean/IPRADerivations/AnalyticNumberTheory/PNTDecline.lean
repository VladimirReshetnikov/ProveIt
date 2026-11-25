import IPRADerivations.AnalyticNumberTheory.LogElementary
import IPRADerivations.Core.Gcd
import IPRADerivations.DiophantineNumberTheory.KhinchinAmplify

/-!
# The one-sided regularity of `r` at rational points (`pnt_ipra_constructive_2026-11-14`, `con:decline`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`: "Monotonicity of `ψ` gives,
for `v ≥ u`, `r(v) + 1 ≥ e^{u−v}(r(u) + 1)`. Since `0 ≤ ψ(e^u)e^{−u} ≤ 4` and `1 − e^{−h} ≤ h`, it follows
that `r(v) ≥ r(u) − 5(v − u)` (`con:decline`). … At rational spatial points `x ≤ y`, the same calculation is
simply `ψ(y)/y ≥ ψ(x)/y` together with `1 − x/y ≤ log(y/x)`; no exponential evaluation is needed in its
arithmetic implementation."

With `y = x + T`, values `P = ψ(x) ≤ Q = ψ(y)`, `P ≤ 4x`, and a logarithm numerator `L` over the denominator `F`
with `1 − x/y ≤ L/F`:

* `decline_rat`: `ψ(y)/y ≥ ψ(x)/x − 4 L/F`, cleared: `F y P ≤ F x Q + 4 x y L`;
* `tail_lower`: the harmonic tail `B = Σ_{i<T} ⌊F/(c₀ + i + 1)⌋` (so `λ = B/F`, `B = S(c₀+T) − S(c₀)`) satisfies
  `F T ≤ (c₀ + T) B` when `c₀ + T` divides `F` (`LogElementary.log_lower`);
* `decline_harmonic`: at mesh `1/M` (`M = M' + 1`), with the packet's logarithm `λ_M(y/x) = B/F` for
  `c₀ = Mx`, `c₀ + T' = My`: `F y P ≤ F x Q + 4 x y B`, i.e. `r(v) ≥ r(u) − 4 λ_M(y/x)` — the packet's
  constant `5` with a unit to spare.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PNTDecline

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_lower)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `ψ(y)/y ≥ ψ(x)/x − 4 L/F` for `y = x + T`, from `ψ(x) ≤ ψ(y)`, `ψ(x) ≤ 4x` and `1 − x/y ≤ L/F`. -/
theorem decline_rat {x T P Q F L : PTm n} (hPQ : Γ ⊢[PRAAx] le P Q) (hP : Γ ⊢[PRAAx] le P (num 4 * x))
    (hL : Γ ⊢[PRAAx] le (F * T) ((x + T) * L)) :
    Γ ⊢[PRAAx] le (F * (x + T) * P) (F * x * Q + num 4 * x * (x + T) * L) := by
  ipra_le 𝔞 F * 𝔞 x * sl hPQ + 4 * 𝔞 x * sl hL + 𝔞 F * 𝔞 T * sl hP

/-- The harmonic tail `B = S(c₀+T) − S(c₀)` satisfies `F T ≤ (c₀ + T) B` when `c₀ + T` divides `F`. -/
theorem tail_lower (c0 T : PTm n) {F u : PTm n} (hF : Γ ⊢[PRAAx] F ≐ (c0 + T) * u) :
    Γ ⊢[PRAAx] le (F * T) ((c0 + T) * ap2 (sumF (offB hB)) T (pairT c0 F)) := by
  have ll := log_lower c0 T hF
  have es := natEq (sum_split (Γ := Γ) hB c0 T F)
  ipra_le sl ll with (𝔞 c0 + 𝔞 T) * es

/-- `con:decline` at rational points with the packet's logarithm `λ_M(y/x) = B/F` (`c₀ = Mx`, `T' = MT`):
`F y P ≤ F x Q + 4 x y B`, i.e. `r(v) ≥ r(u) − 4 λ_M(y/x)`. -/
theorem decline_harmonic (M' x T : PTm n) {P Q F u : PTm n}
    (hF : Γ ⊢[PRAAx] F ≐ (succ M' * x + succ M' * T) * u)
    (hPQ : Γ ⊢[PRAAx] le P Q) (hP : Γ ⊢[PRAAx] le P (num 4 * x)) :
    Γ ⊢[PRAAx] le (F * (x + T) * P)
      (F * x * Q + num 4 * x * (x + T) * ap2 (sumF (offB hB)) (succ M' * T) (pairT (succ M' * x) F)) := by
  have tl := tail_lower (succ M' * x) (succ M' * T) hF
  have hL : Γ ⊢[PRAAx] le (F * T) ((x + T) * ap2 (sumF (offB hB)) (succ M' * T) (pairT (succ M' * x) F)) :=
    mul_le_cancel (d' := M') (by ipra_le sl tl)
  exact decline_rat hPQ hP hL

/-- `N − 1` for `N = 327680 (p+1)² (i'+1)`, as a polynomial. -/
abbrev candK (p i' : PTm n) : PTm n :=
  num 327680 * (succ p * succ p) * i' + num 327680 * (p * p + num 2 * p) + num 327679

/-- `con:one-step`, the candidate count: "Bernoulli's finite inequality gives `Q^{mi} ≥ 1 + mi/(320q) =
1 + 1024qi > i`" for `Q = 1 + 1/(320q)`, `m = 327680 q²`, cleared: `x^N (1 + 1024 q i) ≤ (x + 1)^N` with
`x = 320q`, `N = m i` (`q = p + 1`, `i = i' + 1`), from `KhinchinAmplify.bern` at `k = N − 1`. -/
theorem candidates (p i' : PTm n) :
    Γ ⊢[PRAAx] le (pw (num 320 * succ p) (num 327680 * (succ p * succ p) * succ i') *
        (one + num 1024 * succ p * succ i'))
      (pw (succ (num 320 * succ p)) (num 327680 * (succ p * succ p) * succ i')) := by
  have eN : Γ ⊢[PRAAx] succ (candK p i') ≐ num 327680 * (succ p * succ p) * succ i' := by
    ipra_ring
  have b := LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify.bern (Γ := Γ) (candK p i') (num 320 * succ p)
  have e1 := natEq (congrAp2 (Γ := Γ) powF eN (.eqRefl (num 320 * succ p)))
  have e2 := natEq (congrAp2 (Γ := Γ) powF eN (.eqRefl (succ (num 320 * succ p))))
  have e3 := natEq (pw_succ (Γ := Γ) (num 320 * succ p) (candK p i'))
  ipra_le sl b with -e2 + (1 + 1024 * (𝔞 p + 1) * (𝔞 i' + 1)) * e1 - 1024 * (𝔞 p + 1) * (𝔞 i' + 1) * e3

end LeanProofs.IPRA.AnalyticNumberTheory.PNTDecline
