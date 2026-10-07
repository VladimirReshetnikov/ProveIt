# Polygamma at non-real arguments: CM lattices, Γ-periods, and vanishing identities

- Status: Report (verified experimental results; certification = mpmath
  residuals at the stated precision, not yet multiplier certificates)
- Created (UTC): 2026-06-10T23:42:01Z
- Repository HEAD: 7de562490d88e431394c19f7c09232486f152d53
- Requested by Vladimir: *"Is there any interesting identities for polygamma
  values at any non-real arguments? (or a Re/Im component of those values even
  if the other component is opaque.) … build a set of values that* might *be
  connected and run them through PSLQ … Follow a hunch."*

## 1. The hunch

Polygamma values at points of an **imaginary quadratic lattice** should see
the lattice's complex multiplication. The mechanism: for `a` off the real
axis,

```
Σ_{m ∈ ℤ} 1/(m+a)^{s+1} = [ψ_s(a) + ψ_s(1−a)] / s!        (s ≥ 1)
```

(split the bilateral sum at `m = 0`), so **row-summing an Eisenstein series
turns it into a polygamma sum**. For the weight-`2k` Eisenstein series of the
lattice `ℤ + ℤτ`,

```
G_{2k}(τ) = Σ'_{(m,n)} 1/(m+nτ)^{2k}
          = 2ζ(2k) + (2/(2k−1)!) Σ_{n≥1} [ψ_{2k−1}(nτ) + ψ_{2k−1}(1−nτ)]
```

(the `±n` rows coincide because the power is even). At the two CM points with
extra symmetry — `τ = i` (square lattice, j = 1728) and `τ = ρ = e^{iπ/3}`
(hexagonal lattice, j = 0) — classical theory pins `G_{2k}` exactly:

- `G₆(i) = 0` (the square lattice admits no weight-6 form: `i·(ℤ+ℤi) = ℤ+ℤi`
  forces `G₆ = i⁻⁶G₆ = −G₆`);
- `G₄(ρ) = 0` (same argument with `ρ²`, weight 4: `G₄ = ρ⁻⁸G₄ ≠ G₄`);
- `G₄(i)` and `G₆(ρ)` are the lemniscatic and equianharmonic period powers —
  `Γ(1/4)` and `Γ(1/3)` monomials by Chowla–Selberg.

So the hunch set was: trigamma at small Gaussian-rational points (reflection +
conjugation closures), and the four Eisenstein row-sums above.

## 2. Verified identities

All residuals from `mpmath` at 50–60 dps; polygamma at complex `a` computed
as `ψ_m(a) = (−1)^{m+1} m! (a^{−m−1} + ζ(m+1, 1+a))` (shift keeps the Hurwitz
zeta in its safe region).

### 2.1 Elementary single components (reflection ∘ conjugation)

`ψ_m(z̄) = conj ψ_m(z)` turns the reflection law into statements about one
real component, leaving the other opaque:

```
Re ψ₁((1+i)/2) = π²/(2 cosh²(π/2))            (residual 0 at 50 dps)
Re ψ₁(i)       = −1/2 − π²/(2 sinh² π)        (residual 0 at 50 dps)
```

The first is the cleanest possible specimen: `1 − z = z̄` exactly on the line
`Re z = 1/2`, so reflection alone evaluates `2 Re ψ₁(z)` there for *any*
height: `Re ψ₁(1/2 + it) = π²/(2 cosh²(πt))` — a closed form along an entire
vertical line. The imaginary parts stay opaque (they are odd-power analogues
of the `coth` family; see §4).

### 2.1a The "FoxTrot identity" demystified, and its two-parameter family

MathWorld's *Digamma Function* page calls this "surprising" (it arises from
the FoxTrot series `Σ(−1)ⁿn²/(n³+1)`, whose partial fractions hit the roots
of `n²−n+1`):

```
−ψ(½ω) − ψ(−½ω²) + ψ(½(1+ω)) + ψ(½(1−ω²)) = 2π sech(√3π/2),  ω = e^{iπ/3}
```

It is the §2.1 mechanism verbatim. The four arguments pair into
`2Re[ψ(z+½) − ψ(z)]` at `z = ¼ + i√3/4`, and on the line `Re z = ¼` the
shift satisfies `z + ½ = 1 − z̄` — so reflection∘conjugation eliminates the
digammas: `Re[ψ(z+½) − ψ(z)] = π Re cot(πz̄) = π sech(2πt)`. The MathWorld
identity is the point `t = √3/4` of a line of identities, itself one member
of the two-parameter family (verified for `c = ½, ⅓, ⅔` at generic `t`):

```
Re[ψ(z+c) − ψ(z)] = π Re cot(πz̄)      on the line  Re z = (1−c)/2
```

— elementary `sinh/cos` closed forms for every shift `c ∈ (0,1)`, no CM
needed. Differentiating in `t` ladders it up the polygamma tower
(weights 2, 3 verified at 10⁻⁵⁰):

```
Im[ψ₁(¾+it) − ψ₁(¼+it)] = 2π² sech(2πt) tanh(2πt)
Re[ψ₂(¾+it) − ψ₂(¼+it)] = 8π³ sech³(2πt) − 4π³ sech(2πt)
```

The alternating component (`Re` at odd weight, `Im` at even weight) stays
opaque, exactly as in §2.1/§4.

### 2.2 Vanishing identities (the CM gems)

The two "missing modular form" slots collapse infinite polygamma sums to
single zeta values:

```
Σ_{n≥1} [ψ₅(ni) + ψ₅(1−ni)] = −120 ζ(6)             (residual 1.7e−49)

Σ_{n≥1} [ψ₃(nρ) + ψ₃(1−nρ)] = −6 ζ(4),  ρ = e^{iπ/3}   (residual 6.8e−50)
```

Unexpected on their face — each individual bracket is a transcendental-looking
complex number (elementary in `coth/csch` of `πn√3/2` etc. after the bilateral
cotangent expansion, but nobody would guess the total) — yet the sums are
rational multiples of `ζ(6)`, `ζ(4)` because the corresponding modular forms
*do not exist*.

### 2.3 Γ-period identities (Chowla–Selberg made polygamma-visible)

```
2ζ(4) + (1/3) Σ_{n≥1} [ψ₃(ni) + ψ₃(1−ni)]  = Γ(1/4)⁸ / (960 π²)
                                                       (residual 2.1e−50)

2ζ(6) + (1/60) Σ_{n≥1} [ψ₅(nρ) + ψ₅(1−nρ)] = Γ(1/3)¹⁸ / (8960 π⁶)
                                                       (residual 2.0e−60)
```

Polygamma values at purely imaginary (resp. hexagonal) points, summed over
the integer multiples of the point, know the lemniscate constant and its
equianharmonic sibling. These connect directly to this repository's CM
corpus: `Γ(1/4)²/π`-class atoms are exactly the `cmPeriodReduce` currency of
`src/Hypergeometric`, and the Gamma stores here hold both atoms.

### 2.4 The complete low-weight table

The symmetry argument and the Hurwitz recursion
`(2n+1)(2n−1)(n−3) G_{2n} = 3 Σ_{m=2}^{n−2} (2m−1)(2n−2m−1) G_{2m} G_{2n−2m}`
extend §2.2–2.3 with no new constants; all verified (residuals 10⁻⁶⁰–10⁻²⁶³):

| weight | square lattice `τ = i` | hexagonal lattice `τ = ρ` |
|---|---|---|
| 4  | `Γ(1/4)⁸/(960π²)` | **0** |
| 6  | **0** | `Γ(1/3)¹⁸/(8960π⁶)` |
| 8  | `(3/7)G₄(i)² = 3Γ(1/4)¹⁶/(7·960²π⁴)` | **0** |
| 10 | **0** | **0** |
| 12 | `(18·G₄³+25·G₆²)/143`-type | `(25/143)G₆(ρ)² ∝ Γ(1/3)³⁶` |

Every bold zero is a vanishing identity
`Σ_{n≥1}[ψ_{w−1}(nτ) + ψ_{w−1}(1−nτ)] = −(w−1)!·ζ(w)`, and every entry is a
`ψ_{w−1}`-sum evaluation. The pattern is exhaustive: `G_{2k}(i) = 0` iff
`2k ≢ 0 (mod 4)`, `G_{2k}(ρ) = 0` iff `2k ≢ 0 (mod 6)`, and all non-zero
values are ℚ-monomials in the two period powers — so the *entire* Eisenstein
tower over both lattices is now polygamma-explicit.

### 2.5 Beyond the maximal-symmetry points: 2i and i√2

The same row-sum at the next two CM points (PSLQ-discovered, 120-dps
canaries):

```
G₄(2i)  = (11/15360) Γ(1/4)⁸ / π²                  (canary 0 at 120 dps)
G₄(i√2) = Γ(1/8)⁴ Γ(3/8)⁴ / (4608 π²)              (canary 3.9e−121)
```

The first confirms the isogeny picture — `2i` sits over the same field
`ℚ(i)`, so only the rational factor changes (`G₄(i)/G₄(2i) = 16/11`). The
second imports a **new period**: disc −8, field `ℚ(√−2)`, and the polygamma
sum `Σ_n [ψ₃(ni√2) + ψ₃(1−ni√2)]` evaluates in `Γ(1/8)Γ(3/8)` — the
fundamental unit `1+√2` was offered in the PSLQ basis and declined (exponent
0). Together with §2.3–2.4 this makes three distinct Chowla–Selberg periods
polygamma-visible.

### 2.6 Class number 2: the disc −20 and −15 pairs (ratio + class product)

At `ℚ(√−5)` (class number 2) the single-value log-PSLQ *must* fail: the
algebraic factor in `G₄/Ω⁴` lives in the Hilbert class field and is not a
monomial. The structure that works is the Hecke/Damerell pair over the two
reduced forms `x²+5y²` (`τ₁ = i√5`) and `2x²+2xy+3y²` (`τ₂ = (−1+i√5)/2`):

```
G₄(τ₁) / G₄(τ₂) = (29 + 12√5)/44 = (3 + 2√5)²/44      (canary 0 at 160 dps)

G₄(τ₁) · G₄(τ₂) = 11 · φ⁴ · Γ(3/20)⁸ Γ(7/20)⁸ / (2¹⁴·3⁴·5⁴·π⁴)
                                                       (canary 5.3e−160)
```

(`φ` the golden ratio.) The **ratio is algebraic of degree 2** — its norm is
`121 = 11²` — and the **class product is a period monomial** carrying the
prime `11` and a golden unit.

Disc −15 (`τ₁ = (1+i√15)/2` for `x²+xy+4y²`, `τ₂ = (1+i√15)/4` for
`2x²+xy+2y²`) repeats the pattern, even more cleanly (160-dps canaries):

```
G₄(τ₁) / G₄(τ₂) = 2(4 + √5)²/77

G₄(τ₁) · G₄(τ₂) = 77 · (Γ(1/15)Γ(2/15)Γ(4/15)Γ(8/15))⁴ / (2¹³·3⁶·5⁵·π⁴)
```

— the Γ-block is exactly the `χ₋₁₅ = +1` residues `{1,2,4,8}`, the golden
unit is declined (exponent 0), and the prime content `77 = 7·11` of the
product matches the ratio's denominator (`N(4+√5) = 11`). The heuristic
that emerges: *run the ratio first; its norm names the primes the
class-product basis needs.*

The `G₆` row at the §2.5 points completes the weight-6 picture (160-dps
canaries; fundamental units declined again):

```
G₆(2i)  = Γ(1/4)¹² / (2¹⁴·5·π³)
G₆(i√2) = Γ(1/8)⁶ Γ(3/8)⁶ / (2¹²·3³·5·π³)
``` Three search-discipline traps fired en route,
each match­ing a recorded lesson: the first basis was ℚ-dependent (PSLQ
returned the known `Γ(1/20)Γ(9/20)/(Γ(3/20)Γ(7/20)) = 5^{1/4}φ` dependency
instead of the target — leading coefficient 0 is the tell); the value-level
probe failed under a wrong π-normalization; and the class-product log-PSLQ
needed `ln 11` in the basis (forecast by the ratio's norm and by
`G₄(2i) ∝ 11`).

### 2.7 Class number 3: disc −23 and the x³−x−1 class field

`ℚ(√−23)` (h = 3, the Hilbert class field generated by the famous
`x³−x−1`) pushes the pattern one degree higher. The three reduced forms give
`τ₁ = (1+i√23)/2`, `τ₂,₃ = (±1+i√23)/4`; `G₄(τ₁)` is real, `G₄(τ₂,₃)` a
conjugate pair. Verified results:

```
G₄(τ₁)·G₄(τ₂)·G₄(τ₃) = 11·17 · P⁴ / (2²⁴·3⁶·23⁵·π¹⁶)   (canary 1.4e−160)
    where P = Π Γ(k/23) over the 11 quadratic residues k mod 23
```

and the weight-0 split: with `γ₂ = E₄/η⁸` phase-corrected by the canonical
cube root (the `q^{1/3}` ambiguity of `η⁸` at these points), the three
`γ₂(τᵢ)` from the polygamma row-sums are exactly the roots of the classical
class polynomial

```
x³ + 155x² + 650x + 23375 = 0        (coefficients integer to 10⁻⁸⁰)
```

whose constant term `23375 = 5³·11·17` *forecast* the primes 11, 17 in the
class product — the §2.6 norm-heuristic again, one degree up.

**Honest negative, structural**: the dimensionless symmetric functions
`e₁³/e₃`, `e₂³/e₃²` of the raw `G₄` values are **not** rational (PSLQ to
height 10³⁰ at 300 dps). Unlike the value *product* (a norm) and the
weight-0 `γ₂` invariants, sums of weight-4 CM values across classes are not
Galois-clean — the period correction under `Gal(H/K)` is nontrivial at
weight 4. The class polynomial must be formed from `γ₂ = E₄/η⁸`, not from
the `G₄` values themselves.

### 2.8 Class number 4: disc −39, and the Hilbert class polynomial itself

The four reduced forms of disc −39 (`(1,1,10), (2,±1,5), (3,3,4)`) give
`τ ∈ {(1+i√39)/2, (±1+i√39)/4, (3+i√39)/6}`. Verified (160-dps canaries):

```
Π G₄(τᵢ) = 17·23·29 · P⁴ / (2²⁸·3⁹·5⁴·13⁸·π¹⁶)
    where P = Π Γ(k/39) over the 12 residues with χ₋₃₉(k) = +1
```

A wrinkle vs §2.7: **γ₂ is not a class invariant here** (3 | 39 — the
classical obstruction; no cube-root phase choice makes the γ₂-sums
rational, observed directly). But `j` always is, and the row-sum values
deliver the **Hilbert class polynomial of disc −39** outright:

```
H₋₃₉(x) = x⁴ + 331531596x³ − 429878960946x² + 109873509788637459x
            + 20919104368024767633
```

(`e₁..e₃` PSLQ-exact integers; `e₄` integral to 10⁻¹³⁷.) Worth dwelling on:
a quartic with 20-digit integer coefficients recovered from sums of
polygamma values at quadratic-irrational complex points — the polygamma
row-sum is a perfectly serviceable special-function front door to the
classical CM tower.

**Genus structure inside the quartet** (Cl = ℤ/4; the ambiguous form
`(3,3,4)` is the order-2 class): the raw cross-class ratio `v₁/v₄` is
honestly *quartic* (no degree-2 minimal polynomial to height 10¹²), but the
genus-wise ratio — principal genus `{1, A²}` over `{A, A³}` — is exactly
quadratic, in the real part of the genus field `ℚ(√−3, √13)` as genus
theory demands (160-dps canary; `√3`, `√39` declined by PSLQ):

```
G₄(τ₁)G₄(τ₄) / (G₄(τ₂)G₄(τ₃)) = (103299 + 4440√13)/181424,
    N = (9/16)²,  181424 = 16·17·23·29
```

— the denominator reuses the class-product primes 17, 23, 29.

### 2.9 Class number 5: disc −47

The five reduced forms (`(1,1,12), (2,±1,6), (3,±1,4)`) give the quintet
`τ ∈ {(1+i√47)/2, (±1+i√47)/4, (±1+i√47)/6}`. Verified (200-dps canary):

```
Π G₄(τᵢ) = 11²·23·29 · P⁴ / (2⁵²·3⁶·47⁹·π³⁶)
    where P = Π Γ(k/47) over the 23 quadratic residues mod 47
```

and the row-sum `j`-values deliver the quintic Hilbert class polynomial
(all symmetric functions integral to 10⁻¹²⁹ or better):

```
H₋₄₇(x) = x⁵ + 2257834125x⁴ − 9987963828125x³ + 5115161850595703125x²
            − 14982472850828613281250x + 16042929600623870849609375
```

The CM tower is now polygamma-explicit through class number 5 with one
uniform recipe: row-sum → class product log-PSLQ (norm-forecast primes) →
`j`-symmetric-function integrality.

### 2.10 The MathWorld Clausen specials are two one-line laws

MathWorld's *Polygamma Function* page lists 16 closed forms (`ψ₁, ψ₂, ψ₃`
at `p/q`, `q ∈ {2,3,4,6}`) in Catalan/Clausen/β atoms. All of them — and
their extension to **every** rational argument — are instances of the
sine-weighted Clausen DFT (the `reduction-method.md` §4 bridge made
explicit), verified here at `q = 3, 4, 5, 8, 12` to 10⁻⁴⁶ or better:

```
ψ₁(p/q) = π²/(2 sin²(πp/q)) + 2q · Σ_{j=1}^{⌊(q−1)/2⌋} sin(2πjp/q) Cl₂(2πj/q)

ψ₃(p/q) − ψ₃(1−p/q) = 24q³ · Σ_j sin(2πjp/q) Cl₄(2πj/q)
```

(the even halves are elementary by reflection). **Attribution**: the `ψ₁`
law is classical — it is Lewin 1991 (MathWorld *Trigamma Function* eq. 14,
"(Lewin 1991)"), independently re-derived here from the DFT bridge before
the attribution was spotted; the `ψ₃` analogue and the general-`m`
odd-half version follow by the same derivation and are presumably in
Lewin's orbit as well. The value of this section is therefore not novelty
but *placement*: the law is the explicit form of the store-level DFT
bridge, and its `q = 5, 8, 12` instances below feed the planned store
emission. MathWorld's coefficients are the small-`q` shadows: `3√3·Cl₂`
is `2q·sin(2π/3)` at `q=3`, `8K` is `2q·Cl₂(π/2)` at `q=4`, `162√3` and
`768β(4)` are `24q³`-instances. New
beyond the table, e.g.:

```
ψ₁(1/5)  = π²/(2sin²(π/5)) + 10[sin(2π/5)Cl₂(2π/5) + sin(4π/5)Cl₂(4π/5)]
ψ₁(1/12) = π²/(2sin²(π/12)) + 24[…five Clausen atoms incl. Cl₂(π/2) = K…]
```

Also, MathWorld's (27) simplifies: `Cl₃(2π/3) = −(4/9)ζ(3)`, so
`ψ₂(1/3) = −4π³/(3√3) − 26ζ(3)`. One sharpening found during the store
emission below: the odd-weight collapse `Cl₃(2πj/q) ∈ ℚ·ζ(3)` holds
exactly for lowest-terms denominators with `φ(q) ≤ 2`
(`q ∈ {1,2,3,4,6}`, the crystallographic angles), where only the
principal even character survives the cosine DFT — *not* for every
rational angle. For `q = 5, 8, 12` the even quadratic character `χ_q`
survives, and `s = 3` odd against `χ(−1) = +1` is the parity-*mismatch*
case, so `Cl₃(2π/5)`, `Cl₃(π/4)`, `Cl₃(π/6)` are genuine atoms
(PSLQ-canaried independent of `{ζ(3), π³}` at coefficient height 10¹⁰),
with exact bridges `Cl₃(2π/5) = −(6/25)ζ(3) + (√5/4)L(3,χ₅)`,
`Cl₃(π/4) = −(3/256)ζ(3) + L(3,χ₈)/√2`,
`Cl₃(π/6) = ζ(3)/24 + (√3/2)L(3,χ₁₂)`.

The store emission queued here is **done**:
[`identities/polygamma-clausen-values.wl`](../../identities/polygamma-clausen-values.wl)
— 54 entries (`ψ_m(p/q)`, `m = 1,2,3`, `q ∈ {3,4,5,6,8,12}`, all `p`
coprime to `q`) in canonicalized Clausen atoms, each verified at 60
digits in-kernel by
[`tools/generate-polygamma-clausen-store.wl`](../../tools/generate-polygamma-clausen-store.wl),
cross-engine by
[`tools/verify-polygamma-clausen-mpmath.py`](../../tools/verify-polygamma-clausen-mpmath.py)
(mpmath, 70 dps: raw DFT bridge, store-form laws, all canonicalization
relations, Hurwitz-zeta `L`-bridges, PSLQ canaries), and guarded by
`tests/smoke.wl`.

## 3. How the equianharmonic constant was pinned (methodology note)

The `Γ(1/3)¹⁸/(8960π⁶)` form resisted a first PSLQ pass, and the failure
chain is worth recording:

1. **A factor-of-2 bug**: the row-sum prefactor is `2/(2k−1)!`; the weight-6
   probe initially used `1/120` instead of `1/60`. The *vanishing* tests are
   blind to such a factor (zero swallows it) — they passed while the value
   probe quietly computed garbage. Cross-checking the lattice row-sum against
   the modular `q`-series `G₆ = 2ζ(6)E₆(ρ)`, `q = −e^{−π√3}` (agreement to
   30+ digits) caught it. *Lesson: a vanishing identity passing is weak
   evidence for the machinery around it.*
2. **Span failure, not precision failure**: with the right value, log-PSLQ
   over `{ln Γ(1/3), ln π, ln 2, ln 3}` still found nothing — because
   `8960 = 2⁸·5·7` and `ζ(6) = π⁶/945` drags in the primes 5 and 7. The
   debugging anchor was the η function: PSLQ over the same basis instantly
   gave `|η(ρ)| = 3^{1/8} Γ(1/3)^{3/2} / (2π)` (the classical value), and
   then `E₆(ρ)² = 1728 η(ρ)²⁴` forces the closed form with no further search.
   *Lesson: when a CM-value PSLQ fails, anchor on η — its closed forms have
   tiny prime support — and derive upward through the modular algebra rather
   than widening the basis blindly.*

## 4. The opaque components and what they are (negative + structure)

The components *not* fixed by reflection∘conjugation — `Im ψ₁(i)`,
`Re ψ(i)`-beyond-γ, `Im ψ₁((1+i)/2)` — are **odd-row** lattice data: e.g.
`Im ψ₁(i) = −2 Σ_{k≥1} k/(k²+1)²` is an odd-power analogue of the `coth`
family, which the bilateral (even) cotangent expansion cannot reach. These
are Eichler-integral / quasi-modular territory (the `E₂`-flavored layer:
compare `Σ k/(e^{2πk}−1) = 1/24 − 1/(8π)` from `E₂(i) = 3/π`). A small PSLQ
basket against `{1, π, coth π, π²/sinh²π, π·coth, …}` products found nothing
with small heights — consistent with genuinely new constants, recorded here
as an honest negative. The Lambert-series face (`Σ σ₅(n)qⁿ` etc. at
`q = e^{−2π}, −e^{−π√3}`) is the natural next probe surface.

## 5. Follow-ups

1. ~~Weight 8 and 10~~ — **done** (§2.4): the full table through weight 12.
2. ~~Other CM points~~ — **done through h = 5** (§2.5–2.9: `2i`, `i√2`,
   discs −20, −15, −23, −39, −47). Still open: the `G₆` row at the
   non-maximal points, and the ratio/Galois structure inside the −39
   quartet (the ℤ/4 class group should show in which pairs of `G₄` values
   generate which subfield).
3. The quasi-modular layer (§4): `E₂(i) = 3/π` row-summed is *weight 2* —
   conditionally convergent rows (Eisenstein summation needed) — relating
   `ψ₁`-sums at `ni` to `π`; the careful version would explain exactly which
   combination of the opaque odd constants is reachable.
4. Fold §2.3 into the identity stores once a store schema for
   infinite-sum/limit claims exists (current stores hold finite reduction
   rules only).

## Correction addendum (2026-06-11, article-verification pass)

During preparation of the LaTeX article
[`../articles/eisenstein-row-sums-cm-polygamma.tex`](../articles/eisenstein-row-sums-cm-polygamma.tex),
every displayed identity of this report was independently re-verified (mpmath
at 60 dps; PARI/GP `polclass`/`polresultant` for the class polynomials). All
passed at ~1e-60 residuals except the following corrections, each confirmed
numerically:

1. **S2.6, disc -15**: `G4(t2)` at `t2 = (1+i sqrt15)/4` is genuinely complex
   (`~ 2.140345949886946 + 1.184217745576377 i`; the form `(2,1,2)` sits on
   `|t| = 1`, where conjugation acts nontrivially). The displayed ratio and
   class-product identities hold (rel. residual ~1e-60) with `Re G4(t2)` -
   equivalently the class-pair average over `(+-1+i sqrt15)/4` - not with the
   literal complex value. The disc -20 pair is unaffected (`G4((-1+i sqrt5)/2)`
   is real).
2. **S3 item 2**: `E6(rho)^2 = 1728 eta(rho)^24` has the wrong sign: with
   `q = -e^(-pi sqrt3)` and `E4(rho) = 0`, `eta(rho)^24 = Delta(rho) =
   -E6(rho)^2/1728 < 0`. The correct anchor is `E6(rho)^2 = -1728 eta(rho)^24
   = 1728 |eta(rho)|^24`.
3. **S2.10**: MathWorld''s *Polygamma Function* special-cases block (eqs.
   (22)-(36)) lists **15** closed forms, not 16 (psi1 at 1/3,2/3,1/4,3/4; psi2
   at 1/2,1/3,2/3,1/4,3/4,1/6,5/6; psi3 at 1/3,2/3,1/4,3/4).
4. **S2.10**: the `162 sqrt3` and `768 beta(4)` MathWorld coefficients are
   `12 q^3 sin(2 pi j/q)` instances of the one-sided psi3 law; the `24 q^3`
   prefactor belongs to the difference form `psi3(p/q) - psi3(1-p/q)`.
5. **S2.1a** (cosmetic): MathWorld''s FoxTrot series is
   `Sum (-1)^(n-1) n^2/(n^3+1)` (overall sign flipped vs the spelling here);
   harmless for the partial-fraction argument.
