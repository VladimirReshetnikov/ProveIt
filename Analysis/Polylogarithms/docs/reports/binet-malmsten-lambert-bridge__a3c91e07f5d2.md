# Binet's second formula and Malmsten integrals: the Lambert-kernel bridge

- Status: Report (verified first results + research directions)
- Created (UTC): 2026-06-11T01:01:24Z
- Repository HEAD: 65641d214cd82eeed3095bf925822e3986634b0b
- Prompted by Vladimir: MathWorld's *Binet's Log Gamma Formulas* and
  *Malmsten's Formula* pages — "see if you can get any ideas".

## 1. Where these formulas sit relative to the current program

Binet's second formula

```
ln Γ(z) = (z−1/2)ln z − z + ln√(2π) + 2∫₀^∞ arctan(t/z)/(e^{2πt}−1) dt
```

is the integrated Abel–Plana formula with the **Lambert kernel
`1/(e^{2πt}−1)`** — the same kernel whose moment sums are the Eisenstein
`q`-series of the CM report (`polygamma-complex-arguments-cm-lattices__*.md`).
Malmsten/Vardi log-log integrals `∫₀¹ lnln(1/x)·R(x) dx` are the **Mellin
avatars of the Kummer Fourier series** used for the `ψ^(−2)` Clausen bridge
(`loggamma-integrals-clausen-bridge__*.md`): expanding the rational kernel
`R` in a geometric series produces `Σ χ(k)·ln k/k = L′(χ,1)`-type sums, and
Kummer's formula converts odd-character `L′(1)` into `ln Γ` at rationals.

## 2. Verified results (mpmath; canaries at the stated precision)

**Binet-2 replays exactly** at `z = 1, 1/2, 1/4` (residuals ≤ 10⁻⁵²),
turning every Gamma-store atom into a closed-form **arctan-Lambert
integral**; e.g. at `z = 1/4`:

```
∫₀^∞ arctan(4t)/(e^{2πt}−1) dt
   = [ln Γ(1/4) − (1/2)ln 2 + 1/4 − (1/2)ln(2π)] / 2
```

**Vardi's integral re-derived blind** (PSLQ over `{πγ, πln2, πlnπ,
πlnΓ(1/4)}`; the `γ` atom *declined*, coefficient 0; canary exact at 80
dps):

```
∫₀¹ ln ln(1/x)/(1+x²) dx = (π/4) ln(4π³/Γ(1/4)⁴)
```

**The q = 3 Malmsten variant** (canary 3.4×10⁻⁸¹; `γ` declined again):

```
∫₀¹ ln ln(1/x)/(1+x+x²) dx = (π/(6√3)) ln( 2⁸π⁸ / (3³ Γ(1/3)¹²) )
```

Both integrals carry exactly the harvested-Gamma-store atoms — the
log-log family is a systematic *integral-representation generator* for the
identity stores: every odd Dirichlet character (each denominator `q`)
yields one such evaluation through Kummer, with the Γ-lattice reducer
supplying the closed form mechanically.

## 2a. The log-gamma moment ladder (second MathWorld pass)

Three further items from the *Log Gamma Function* page, checked and placed:

**The Whittaker–Watson Hurwitz series** (verified exactly at `z = 1/3`):

```
ln Γ(z) = (z−1/2)ln z − z + ln√(2π) + (1/2) Σ_{n≥2} (n−1)/(n(n+1)) · ζ(n, z+1)
```

is a **ℚ-linear ladder between ln Γ and the entire polygamma tower at the
same point** (`ζ(n, z+1)` is `ψ^{(n−1)}(z+1)` up to factorials). As a
certificate law it would bind the Gamma stores and the trigamma store into
*one* linear system — a candidate "Hurwitz ladder law" for
`functional-equations.wl` (infinite-sum claims need the store-schema
extension of idea 4).

**The Espinosa–Moll second moment** (verified to 1.6×10⁻⁶¹):

```
∫₀¹ [ln Γ(x)]² dx = γ²/12 + π²/48 + γL/6 + L²/3 − (γ+L)ζ′(2)/π² + ζ″(2)/(2π²),
    L = ln(2π)
```

— the quadratic-moment layer adds `ζ″(2)` to the atom inventory (the
first-moment layer of the ψ^(−2) report needed only `ζ′(−1)`-equivalents).

**The cubic moment is open, and stays open here** (honest negative):
`∫₀¹ [ln Γ(x)]³ dx = 5.74038880722947428001957168810246146296101300745…`
(50 digits, tanh-sinh quadrature cross-calibrated by the second moment).
PSLQ over the natural 14-atom weight-mixed basket (`γ³ … L³, π²γ, π²L,
ζ(3), (γ+L)ζ′(2)/π², (γ+L)ζ″(2)/π², ζ‴(2)/π², ζ′(2)²/π⁴, ζ′(3), γζ′(2)/π²`)
returns only uniform-height junk at 60 dps — consistent with Espinosa–Moll
and Bailey et al. The Kummer-cube resonance `k₁ ± k₂ ± k₃ = 0` produces a
genuinely new depth-2 constant (Tornheim–Witten derivative flavor); finding
the right *named* atom for it is the actual open problem, not search depth.

## 3. Ideas worth pursuing (ranked)

1. **Opaque-constant diagnosis via Abel–Plana resonance.** The §4 opaque
   components of the CM report (`Im ψ₁(i) = −2Σ k/(k²+1)²`) hit the
   Lambert kernel at its **resonance**: Abel–Plana for `f(n) = n/(n²+1)²`
   produces a principal-value integral `PV∫ t/((1−t²)²(e^{2πt}−1)) dt`
   (pole at `t = 1` exactly because the summand's poles sit *on* the
   imaginary lattice). This is a precise structural reason these constants
   are outside the Γ/Clausen world — they are Eichler-integral periods of
   the quasi-modular `E₂` layer, reachable (if at all) through
   `E₂(i) = 3/π`-type identities, not through `L′(1)`/Kummer.
2. ~~Even-character log-log integrals~~ — **executed, with the atoms
   named**. Differentiating `L(s,χ) = q^{−s}Σχ(k)ζ(s,k/q)` at `s = 1`
   gives the exact ladder `L′(χ,1) = −ln q·L(1,χ) − (1/q)Σχ(k)γ₁(k/q)`,
   so every Malmsten log-log integral is a **first generalized Stieltjes
   constant** statement (Blagouchine's program; ≡ Deninger's `ζ″(0,a)`
   layer via the functional equation). Verified (10⁻⁵¹), even character
   mod 5:

   ```
   ∫₀¹ lnln(1/x)·(1−x)(1−x²)/(1−x⁵) dx
      = −(γ + ln 5)·(2 ln φ/√5) − [γ₁(1/5) − γ₁(2/5) − γ₁(3/5) + γ₁(4/5)]/5
   ```

   The parity dichotomy is empirically sharp: the **even** `γ₁`-combination
   above does *not* reduce to standard atoms (PSLQ junk at height 10⁸ —
   honest negative; it is a genuinely new atom), while the **odd**
   combination reduces exactly as differentiated-Kummer predicts
   (verified blind):

   ```
   γ₁(1/3) − γ₁(2/3) = −(π/√3)(γ + 4ln2 − ½ln3 + 4lnπ − 6lnΓ(1/3))
   ```

   Consequence for the program: `γ₁(k/q)` (even combinations) join
   `ζ″(2)`-type atoms as the honest next layer; any PSLQ basket for
   exotic values that *might* sit at this depth should offer them.

   **Classical placement (second pass, via Wikipedia's generalized
   Stieltjes constants article):** the odd reduction above is **Malmsten's
   1846 reflection identity** (long misattributed to Almkvist–Meurman;
   verified here verbatim at `q = 3`), and the even residue is governed by
   **Blagouchine's rational-arguments theorem** (J. Number Theory 148,
   2015): `γ₁(r/m)` = elementary + `lnΓ`-DFT + `Σ cos(2πrl/m)·ζ″(0,l/m)`.
   Blagouchine's particular value `γ₁(1/4)` re-verified exactly against
   `mp.stieltjes`. Pushing the theorem through the even combination
   collapses everything except the `ζ″`-block and a `ψ`-block — derived
   and verified to 10⁻⁵⁰:

   ```
   γ₁(1/5) − γ₁(2/5) − γ₁(3/5) + γ₁(4/5)
      = √5·[ζ″(0,1/5) − ζ″(0,2/5) − ζ″(0,3/5) + ζ″(0,4/5)]
        − 2√5·ln φ·(γ + ln 10π)
   ```

   So the canonical atom for the even layer is the **even-character
   `ζ″(0, l/q)` combination** (Deninger's layer); Malmsten integrals,
   even `γ₁`-combos, and even `L′(χ,1)` are all elementary-equivalent to
   it. PSLQ caveat recorded: the reduction coefficients live in `ℚ(√q)` —
   rational-coefficient baskets miss it (a √5-weighted basket or direct
   derivation is required).
3. **Differentiated Binet-2** gives `ψ₁(z) = 1/z + 1/(2z²) + Lambert
   integral` — a uniform integral representation tying the trigamma store
   to the same kernel; at imaginary `z` it reproduces the §2.1/§4
   elementary-vs-opaque split (the integral picks up the PV resonance
   exactly at the opaque components).
4. **Store schema for integral claims.** §2's evaluations (and the ψ^(−2)
   identities) want a store of `{integral representation, closed form,
   proofStatus}` entries; the kernel-free harvest verified them at 60–80
   digits, and the Kummer/Lerch derivation path is certificate-friendly
   (linear over `L′` atoms).

## Correction (2026-06-11)

S2a printed the cubic-moment value with the label "(50 digits ...)" but listed
48 significant digits. The 50-digit value is
`5.7403888072294742800195716881024614629610130074549...` (independent
tanh-sinh quadrature at 60 dps, error estimate ~1e-90, agrees with the printed
48 digits and supplies the two missing ones). The "14-atom" basket label also
counts 13 enumerated atoms as written; the list, not the count, is normative.
