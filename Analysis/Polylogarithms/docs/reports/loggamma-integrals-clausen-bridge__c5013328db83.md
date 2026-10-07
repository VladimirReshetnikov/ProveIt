# Log-gamma integrals and the Clausen lattice: ψ^(−2) at rationals

- Status: Report (experimental findings, numerically certified)
- Created (UTC): 2026-06-10T23:27:17Z
- Repository HEAD: 508de707b5b02a02a24ed0df38613947a234f76c
- Continues: the polylog↔polygamma DFT bridge
  ([`../reduction-method.md`](../reduction-method.md) §4); prompted by
  Vladimir's "keep researching connections between polylog and polygamma"
- Method: mpmath 60-digit quadrature + PSLQ, every relation re-verified at
  100 digits (the canary discipline); kernel-free

## 1. The finding

One integration below the digamma sits `ψ^(−2)(z) = ∫₀^z log Γ(t) dt`
(Wolfram's `PolyGamma[-2, z]`). Integrating Kummer's Fourier series of
`log Γ` predicts that at rational points this grid lands in
`{Clausen values}/π ⊕ ζ′(−1) ⊕ logs` — the **weight-2 Clausen world enters
through the negative-order polygamma ladder**, with the Glaisher-layer
constant `ζ′(−1)` as the genuinely new atom. PSLQ confirms, with 100-digit
canaries (residuals ≤ 10⁻⁶⁰):

```
∫₀^{1/4} log Γ = 3/32 + (1/8)log 2 + (1/8)log π + Catalan/(4π) − (9/8)·ζ′(−1)

∫₀^{1/3} log Γ = 1/9 + (1/6)log 2 − (1/72)log 3 + (1/6)log π
                 + Cl₂(2π/3)/(4π) − (4/3)·ζ′(−1)

∫₀^{1/6} log Γ = 5/72 + (7/72)log 2 + (1/144)log 3 + (1/12)log π
                 + Cl₂(π/3)/(4π)·(…)  [coefficient 1/4 on Cl₂(π/3)/π]
                 − (5/6)·ζ′(−1)
```

(`Cl₂(θ) = Im Li₂(e^{iθ})`; `Cl₂(π/2) = Catalan`.)

The structural punchline: **the quarter-point integral carries Catalan and
the third-point integral carries Gieseking's constant `Cl₂(2π/3)`** — the
very "level-3 Catalan" of the 2026-05-31 Eisenstein-ladder work
(`src/Hypergeometric/identities/harvested-eisenstein-ladder.wl`), now
surfacing from a completely independent direction. The ladder of bridges
reads:

| object | polylog side (at roots of unity) | new atom entering |
|---|---|---|
| `ψ^(m)`, m ≥ 1 | `Re/Im Li_{m+1}` — exact two-way DFT | — |
| `log Γ` = `ψ^(−1)` | `Li₁` (Kummer's log-sin series) | `log 2π` |
| `ψ^(−2)` | `Cl₂ = Im Li₂` (this report) | `ζ′(−1)` |
| `ψ^(−3)` | expected `Im/Re Li₃` layer | expected `ζ′(−2)`-flavor |

## 2. Honest negatives (recorded on purpose)

- `∫₀^{1/2} log Γ` found no relation in the working basis — and the
  follow-up probe exposed why the probe set was flawed: `log Γ(1/2) =
  (1/2)log π` made the basis ℚ-dependent, and PSLQ happily returned that
  degeneracy instead of the target relation. Basis atoms must be
  ℚ-independent (the same lesson as the 2026-05-26 PSLQ sessions).
- The `ψ^(−3)(1/4)` probe (via Cauchy's repeated-integration kernel
  `∫₀^z (z−t) log Γ(t) dt`) produced only a large-coefficient candidate
  (heights ~10⁶) with a weak canary (10⁻⁴⁶ at 100 dps) — **rejected as a
  PSLQ false positive**. The weight-3 level needs a properly prepared basis
  (independent atoms; presumably `ζ(3)/π²` ≡ `ζ′(−2)`-equivalents plus
  Barnes-G-layer logs). Queued.

## 3. Reproduction

```python
import mpmath as mp
mp.mp.dps = 60
I = lambda z: mp.quad(mp.loggamma, [0, z])
# e.g. the quarter-point identity:
lhs = I(mp.mpf(1)/4)
rhs = (mp.mpf(3)/32 + mp.log(2)/8 + mp.log(mp.pi)/8
       + mp.catalan/(4*mp.pi) - mp.mpf(9)/8*mp.zeta(-1, 1, 1))
assert abs(lhs - rhs) < mp.mpf(10)**-55
```

## Correction (2026-06-11)

S1 attached the name "Gieseking''s constant" to `Cl2(2pi/3)`; Gieseking''s
constant is standardly `Cl2(pi/3) = (3/2) Cl2(2pi/3) ~ 1.0149416`. The
third-point integral carries `Cl2(2pi/3)`, i.e. two-thirds of Gieseking''s
constant. The identities themselves are unaffected (re-verified at 60 dps
during the 2026-06-11 article pass).
