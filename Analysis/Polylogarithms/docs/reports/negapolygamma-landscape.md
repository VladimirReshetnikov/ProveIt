# Polygamma of negative integer order: the ladder, reflection and multiplication laws, the rational-value landscape, and a closed open question

- Status: Report (exact derivations + verified experimental results; all
  numerics at the stated precisions)
- Created (UTC): 2026-06-11T23:31:46Z
- Repository HEAD: d91a74ba7c1a0dbfaee920749bd37738a2f06815
- Requested by Vladimir: *"Let's explore polygamma of negative integer
  orders."* Notation: `ψ^(−n)(z)` in the Wolfram convention
  (`ψ^(−1) = lnΓ`, `ψ^(−n)(z) = ∫₀^z ψ^(−(n−1))`); `ζ′(−k,z) :=
  ∂_s ζ(s,z)|_{s=−k}`; `A` = Glaisher (`ln A = 1/12 − ζ′(−1)`);
  `χ_D` the Kronecker character; `β` = Dirichlet beta; `B_n(x)` Bernoulli
  polynomials; `H_k` harmonic numbers; `Cl_k` Clausen/Glaisher functions.

## 1. Executive summary

The negative-order polygamma functions are the **first-jet floor of the
Hurwitz zeta at non-positive integers**: one explicit ladder identity
(§2) reduces every `ψ^(−n)` to a single `ζ′(1−n, z)` plus an elementary
polynomial, and the rational-argument theory of the `ζ′(−k, p/q)` layers
then splits cleanly by character parity (§5): per level and character one
direction reduces through trivial-zero/value bridges, the other carries
exactly one new constant. Everything that follows is exact (derivations,
verified at 60–230 digits, several against Mathematica's `PolyGamma[-n,z]`
directly):

- the **ladder** `ψ^(−n)(z) = [ζ′(1−n,z) − ζ′(1−n)]/(n−1)! + Q_n(z)`,
  with `Q_n` explicit (harmonic-Bernoulli polynomial; §2), shown to equal
  Mathematica's `PolyGamma[-n, z]` for `n = 2..6` to 213+ digits;
- the **reflection laws** (§3): at the `ζ′`-floor,
  `ζ′(−k,z) + (−1)^k ζ′(−k,1−z) = (−1)^⌊k/2⌋ k!·Cl_{k+1}(2πz)/(2π)^k`
  (= the real part of Adamchik Prop. 1 eq. (9), stated there for all
  orders; the bare-Clausen spelling is as verified here for
  all k, with the mechanism), whence explicit negapolygamma reflection
  formulas for `n = 2..5` — **filling a gap Espinosa–Moll (2004) declared
  open** (§8);
- the **multiplication theorems** (§4; the `ψ`-level law is
  Espinosa–Moll 2004 Thm 3.2 in their convention — re-derived here in the
  Wolfram convention): the universal row
  `Σ_j ζ′(−k, z+j/m) = m^{−k}[ζ′(−k, mz) − ln m·B_{k+1}(mz)/(k+1)]` and its
  negapolygamma lift;
- the **bridge laws** (§5): the trivial-zero family (e.g.
  `β′(−1) = 2β(2)/π`, `β′(−3) = −48 β(4)/π³`, general
  `β′(1−2k) = (−1)^{k+1}(2k−1)!\,2^{2k−1} β(2k)/π^{2k−1}`) and the
  **harmonic-number law**
  `L′(k+1,χ)/L(k+1,χ) + conj(L′(−k,χ)/L(−k,χ)) = γ + ln(2π/q) − H_k`
  (whenever `L(−k,χ) ≠ 0`; the conjugation is invisible for real `χ` and
  essential for complex `χ` — see the phase-2 addendum; verified through
  `k = 4`; the `H_k` comes from `ψ(k+1) = H_k − γ` in the Γ-factor);
- the **value table** (§6), including the general `ψ^(−n)(1/2)` theorem and

```
ψ^(−3)(1/2) = 7ζ(3)/(32π²) + (1/2)ln A + (1/16)ln 2π
ψ^(−3)(1/4) = 35ζ(3)/(256π²) + β′(3)/(4π³) + (1/4)ln A + (1/128)ln 2π − γ/128
ψ^(−3)(1/3) = 13ζ(3)/(72π²) + (√3/(8π³))L′(3,χ₋₃) + (1/3)ln A + (7/324)ln 2π − γ/162
ψ^(−4)(1/4) = explicit with NO new atom (β(4) + Glaisher layer; parity alternation)
```

- the **closure of an open question from 2026-06-10** (§6.3): the
  loggamma-Clausen report's `ψ^(−3)(1/4)` PSLQ probe failed honestly; the
  missing basket atom is now identified — `β′(3)` (equivalently `β′(−2)`,
  by the exact bridge `β′(−2) = (3−2γ−2ln(π/2))/4 + 16β′(3)/π³`) — and the
  closed form above settles the item;
- **sporadic hunts over the new atom layers** (§7) — apparently the first
  such sweep — all negative, with the bridges as exact must-hit controls.

## 2. The ladder

From `∫₀^z ζ(s,t)dt = −[ζ(s−1,z) − ζ(s−1)]/(s−1)` (valid for `Re s < 1`,
boundary term at 0 vanishing), differentiating at `s = −k`:

```
∫₀^z ζ′(−k,t) dt = [ζ′(−k−1,z) − ζ′(−k−1)]/(k+1) + [ζ(−k−1,z) − ζ(−k−1)]/(k+1)²
```

with `ζ(−m,z) = −B_{m+1}(z)/(m+1)`. Iterating from `ψ^(−1) = ζ′(0,z) +
½ln2π` gives, exactly,

```
ψ^(−n)(z) = [ζ′(1−n,z) − ζ′(1−n)]/(n−1)!
            + (ln 2π/2)·z^{n−1}/(n−1)!
            − Σ_{j=1}^{n−2} ζ′(−j)·z^{n−1−j}·c_{n,j}
            + R_n(z)
```

with explicit rational `c_{n,j}` and harmonic-Bernoulli polynomials `R_n`
(leading term `−H_{n−1} zⁿ/n!`); the n = 2..6 instances are printed by
[`scratch/negapolygamma_ladder.py`](../../tools/scratch/negapolygamma_ladder.py):

```
ψ^(−2)(z) = [ζ′(−1,z) − ζ′(−1)] + (z/2)ln2π + z(1−z)/2
ψ^(−3)(z) = ½[ζ′(−2,z) − ζ′(−2)] + (z²/4)ln2π − z³/4 + 3z²/8 − z/24 − z·ζ′(−1)
ψ^(−4)(z) = (1/6)[ζ′(−3,z) − ζ′(−3)] + (z³/12)ln2π − 11z⁴/144 + 11z³/72 − 5z²/144
            − (z²/2)ζ′(−1) − (z/2)ζ′(−2)
…
```

[ladder verified against iterated quadrature at 1e−36 (n=2,3); against
Mathematica's `PolyGamma[-n,z]` at `z = 1/3, 2/7, 5/8` to 213–234 digits
for n = 2..6 — i.e. the ladder **is** the Wolfram convention; the n=2 case
additionally matches the classical Alexeiewsky/Barnes-G form]. The
structure matches Adamchik (J. Comput. Appl. Math. 100 (1998) 191–199);
see §8.

A bookkeeping lesson recorded: the first implementation dropped the
`−c·ζ′(−k)·z` term produced by the subtracted constant of the bracket upon
integration; the n=3 quadrature check failed by exactly `−ζ′(−1)·z` —
constant-recognizable residuals localize such errors instantly.

## 3. The reflection law

**Unified law** (all `k ≥ 0`; for `k ≥ 1` this is the real part of
Adamchik's Proposition 1 eq. (9), which is stated for *every* positive
integer order with the Bernoulli term as the imaginary part — see §8; the
bare-Clausen real spelling, the `k = 0` inclusion, and the mechanism note
are as derived here):

```
ζ′(−k, z) + (−1)^k ζ′(−k, 1−z) = (−1)^⌊k/2⌋ · k! · Cl_{k+1}(2πz) / (2π)^k
```

Mechanism: in Hurwitz's formula, at integer `s = k+1` exactly one of
`cos(πs/2)`, `sin(πs/2)` vanishes; differentiating the parity-matching
combination, the product rule keeps only the term where `d/ds` hits the
vanishing factor, so a **single bare Clausen value** appears, with no
derivative of the Dirichlet series. (`k = 0` is Kummer-flavored:
`lnΓ(z) − lnΓ(1−z)` ↔ `Cl₁(2πz) = −ln(2sin πz)`.) The opposite
combination does **not** close — it produces the order-derivative series
`Σ ln n·{cos|sin}(2πnz)/n^{k+1}`, i.e. precisely the generalized-Glaisher
atoms of §5. [67/67 numerical checks at 60 dps;
`scratch/negapolygamma-reflection/verify.py`]

Propagated through the ladder this yields explicit reflection formulas for
`ψ^(−n)(z) ∓ ψ^(−n)(1−z)` for n = 2..5 (Clausen value + polynomial +
lower-`ζ′` constants), e.g. the classical Kinkelin-type
`ψ^(−2)(z) + ψ^(−2)(1−z)`-relation at n = 2 and its new n = 4, 5 siblings
(full forms in the verify script).

## 4. The multiplication theorems

Universal row (differentiate the distribution relation at `s = −k`; exact
for all `k ≥ 0`, `m ≥ 2`):

```
Σ_{j=0}^{m−1} ζ′(−k, z + j/m) = m^{−k} [ ζ′(−k, mz) − ln m · B_{k+1}(mz)/(k+1) ]
```

(`k = 0` = Gauss's multiplication theorem for `lnΓ` via Lerch). Lifted
through the ladder:

```
Σ_{j=0}^{m−1} ψ^(−n)(z + j/m) = m^{1−n} [ ψ^(−n)(mz) − ln m · B_n(mz)/n! ] + ρ_{n,m}(z)
```

with elementary `ρ` (a pleasant fact: the `ln m`-coefficient is the
Bernoulli polynomial of the same index `n`). For n = 2 the remainder is

```
ρ_{2,m}(z) = (m−1)(2z+1)/4 · ln 2π + (m²−1)/(12m) − ((m²−1)/m)·ζ′(−1)
```

— z-dependent, with `(m²−1)/(12m)` as its rational part only (an earlier
revision of this report mis-stated the whole remainder as that constant;
caught by the phase-2 adversarial review, the formula above matching
`verify_mult.py` all along). [81/81 checks at 60 dps incl. anti-circular
quadrature checks; `scratch/negapolygamma-mult/verify_mult.py`]

## 5. The rational-argument landscape: parity split and bridges

For `z = p/q` the layers `ζ′(−k, p/q)` decompose along Dirichlet
characters. Two laws organize everything:

1. **Trivial-zero bridges** (parity-matching: `χ(−1) = (−1)^k`, where
   `L(−k,χ) = 0` — since `B_{k+1}(χ) ≠ 0` exactly when
   `χ(−1) = (−1)^{k+1}`): `L′(−k,χ)` is proportional to `L(k+1,χ̄)` —
   closed forms of the `ζ(k+1)`/Catalan-family. Examples:
   `ζ′(−2) = −ζ(3)/(4π²)`; `β′(−1) = 2β(2)/π = 2G/π`;
   `β′(−3) = −48β(4)/π³`; in general
   `β′(1−2k) = (−1)^{k+1}(2k−1)!·2^{2k−1}·β(2k)/π^{2k−1}`.
2. **The harmonic-number bridge** (parity-opposite,
   `χ(−1) = (−1)^{k+1}`, so `L(−k,χ) ≠ 0`):

   ```
   L′(k+1,χ)/L(k+1,χ) + conj( L′(−k,χ)/L(−k,χ) ) = γ + ln(2π/q) − H_k
   ```

   [discovered by lindep at levels k = 1,2,3 with exact small coefficients,
   then verified at k = 4 to 1e−96; provable from the Γ-factor
   log-derivative, where `ψ(k+1) = H_k − γ`]. For real `χ` the conjugation
   is invisible; for complex `χ` it is essential (the functional equation
   pairs `χ` at `s = k+1` with `χ̄` at `s = −k`; the un-conjugated sum has
   the purely imaginary defect `2i·Im[L′(−k,χ)/L(−k,χ)]` — measured
   exactly for the quartic mod 5 in the phase-2 addendum). The k = 1 case
   is the even-character bridge of the earlier derivative-landscape
   report; the law is uniform across parities and levels.

   (The parity labels in items 1–2 were inverted in the first revision of
   this report; the examples and formulas were always consistent with the
   correct rule `L(−k,χ) = 0 ⇔ χ(−1) = (−1)^k`, `k ≥ 1`.)

Consequently each level `−k` contributes per character exactly **one** new
constant (the parity-opposite `L′`), everything else reducing to lower
floors: level −1 even directions = generalized Glaisher; level −2 odd
directions = the `β′(3)`-family `L′(3,χ-odd)` (equivalently `L′(−2,χ)`);
level −3 even directions = the `L′(4,χ-even)`-family; and so on,
alternating.

## 6. Explicit values

### 6.1 The half-argument tower (all n)

`ζ′(1−n, 1/2) = 2^{1−n} ln2·ζ(1−n) + (2^{1−n}−1) ζ′(1−n)` gives the
general theorem

```
ψ^(−n)(1/2) = [ (2^{1−n}−2) ζ′(1−n) − 2^{1−n} ln2 · B_n/n ]/(n−1)! + Q_n(1/2)
```

[verified n = 4, 5 at 217+ digits in Mathematica]; flattened lowest cases:

```
ψ^(−3)(1/2) = 7ζ(3)/(32π²) + (1/2)ln A + (1/16)ln 2π          [220 digits]
```

### 6.2 Third- and quarter-argument values at n = 3, 4

```
ψ^(−3)(1/4) = 35ζ(3)/(256π²) + β′(3)/(4π³) + (1/4)ln A + (1/128)ln 2π − γ/128   [226 digits]
ψ^(−3)(1/3) = 13ζ(3)/(72π²) + (√3/(8π³))L′(3,χ₋₃) + (1/3)ln A + (7/324)ln 2π − γ/162   [1e−77]
```

(the two share one template: `ζ(3)/π²`-term + one odd-character
`L′(3,·)`-atom + Glaisher + logs; the constant terms cancel exactly in
both flattenings). Auxiliary exact bridges used:
`β′(−2) = (3 − 2γ − 2ln(π/2))/4 + 16β′(3)/π³` [222 digits];
`L′(−2,χ₋₃) = (2/9)(ln(3/2π) + 3/2 − γ) + (9√3/(2π³))L′(3,χ₋₃)` [1e−78];
`L(−2,χ₋₃) = −2/9` exactly. At the next level the parity alternates and
**no new atom enters**:

```
ψ^(−4)(1/4) = exact in {β(4), ζ′(−3), ζ′(−2), ζ′(−1), ln2, ln2π}   [234 digits]
```

via `β′(−3) = −48β(4)/π³` (β(−3) = 0). The values at `2/3, 3/4, 1/6, 5/6`
follow mechanically from §3–§4 (even sums + the `(6^s+3^s)L(s,χ₋₃)`
transport, as in the antiderivative-ladder program).

### 6.3 An open question from 2026-06-10, closed

The loggamma-Clausen report (`loggamma-integrals-clausen-bridge__c5013328db83.md`)
predicted the `ψ^(−3)` row of the bridge ladder ("expected Im/Re Li₃
layer; expected ζ′(−2)-flavor") and recorded an honest negative: its
`ψ^(−3)(1/4)` PSLQ probe produced only a rejected false positive, with the
note that the level needs "a properly prepared basis (independent atoms;
presumably ζ(3)/π² ≡ ζ′(−2)-equivalents plus Barnes-G-layer logs)". The
diagnosis is now exact: the basket lacked **`β′(3)`**. With it, the value
is the closed form of §6.2 — and the predicted layers were right
(`ζ(3)/π²` ✓, Glaisher/Barnes-G ✓), just one atom short.

## 7. Sporadic hunts over the new atom layers

[`../../tools/negapolygamma-hunts.gp`](../../tools/negapolygamma-hunts.gp),
protocol as in the earlier hunt batteries (lindep at 420 digits, planted
positive control found exactly, random negative control rejected; bridges
as structural must-hits — all HIT with exact small coefficients,
*discovering* the harmonic-number law of §5 in the process):

| hunt | atoms | dim | result | bound |
|---|---|---:|---|---|
| N1 | `L′(3,χ)/L(3,χ)`, 10 odd χ + ζ′(3)/ζ(3) + elementary | 18 | **none** | ~10¹⁹ |
| N2 | `L′(4,χ)/L(4,χ)`, 10 even χ + ζ′(4)/ζ(4) + elementary | 19 | **none** | ~10¹⁸ |
| N3 | same character across levels s = 1, −1, 4 (χ₅) and s = 1, 2, 3 (χ₋₃) | 10–11 | **none** | ~10³¹ |
| N4 | `β′(3)` raw vs {Gπ-, ζ(3)-, π³-, lnΓ(1/4)-, ζ′(3)-, lnA-} products | 15 | **none** | ~10²³ |
| N5 | omnibus: all four levels together | 17 | **none** | ~10²⁰ |

As at the previous levels: no sporadic rational relations; the
ladder + parity split + bridges appear to be the complete linear story,
with one genuinely new constant per character per level.

## 8. Literature placement

From the full survey (Adamchik's and Miller–Adamchik's preprints fetched
and transcribed from page images — the published PDFs' Type-3 fonts strip
digits under text extraction; verification scripts under
`scratch/negapolygamma/`):

- **The ladder** is Adamchik, "Polygamma functions of negative order",
  JCAM 100 (1998) 191–199, Proposition 2 eq. (14) (his eq. (13) is the
  Cauchy-kernel definition; the term "negapolygamma" is credited there to
  Gosper) — independently re-derived here; his printed particular values
  (`ψ^(−2)`, `ψ^(−3)` closed forms; `ψ^(−3)(1)`, **`ψ^(−3)(1/2)`**,
  `ψ^(−3)(1/3)+ψ^(−3)(2/3)`; six `ζ′(−n,p/q)` values at `q = 3,4,6`,
  `n = 1,3`; Barnes-G; `ln A_k = B_{k+1}H_k/(k+1) − ζ′(−k)`, his Prop. 4)
  all verify at 50 dps. So §6.1's `ψ^(−3)(1/2)` is a re-derivation of
  Adamchik's value.
- **The `ζ′`-floor reflection law** of §3 is the real part of Adamchik's
  Proposition 1 eq. (9), stated there for *every* positive integer order
  (the Bernoulli term is the imaginary part; = Miller–Adamchik eq. (21));
  the bare-Clausen real spelling, the `k = 0` inclusion, and the
  vanishing-trig-factor mechanism are as given here.
  **The `ψ^(−n)`-level reflection formulas appear to be new**: Espinosa–Moll,
  "A generalized polygamma function", Integral Transforms Spec. Funct. 15
  (2004) 101–115, state verbatim in the Note introducing their (3.6) (it
  follows their (3.5)): *"We have been unable
  to find a generalization of the other well-known functional relation for
  the polygamma function"* — §3's n = 2..5 formulas fill exactly that gap.
- **The multiplication theorem at the `ψ`-level is published**:
  Espinosa–Moll 2004, Thm 3.2 eq. (3.7) (their balanced-convention
  generalized polygamma; verified here at `z = −2,−3,−4`, `k = 2,3`);
  §4's lift is its Wolfram-convention re-derivation, the universal
  `ζ′(−k)`-row being elementary.
- **Conventions**: Mathematica's `PolyGamma[-n,z]` = the Adamchik/Gosper
  fractional integral with base point 0 (functions.wolfram.com
  06.15.02.0008.01 annotation), pinned experimentally; Espinosa–Moll's
  "balanced" negapolygamma (Part 2 §3, `[A_k(q) − H_{k−1}B_k(q)]/k!`)
  differs by an explicit polynomial with `ln A_r` coefficients (their
  (3.36)–(3.38)) — and even at `k = 1` by `−ln√2π`; a real convention trap.
- **Rational arguments at `n ≥ 4`: no journal paper** states them
  (Adamchik stops at `ψ^(−3)`); the only printed general-order
  rational-argument formulas are the Wolfram Functions site entries
  06.15.03.0052–0064 (in `ζ^{(1,0)}(2n, j/q)`/`Li`-at-roots-of-unity
  spelling). Mathematica's `FunctionExpand` fully reduces `ψ^(−2)` at
  `{1, 1/2, 1/3, 1/4, 3/4, 2}` and `ψ^(−3)` at `{1, 1/2}`, but leaves
  `Derivative[1,0][Zeta][-2, 1/4]` (resp. `[-2, 1/3]`) **unevaluated** in
  `ψ^(−3)(1/4)`, `ψ^(−3)(1/3)` — the cleanest witness that the
  parity-opposite atoms are the obstruction, and that §6.2's flattened
  minimal-atom forms (`β′(3)`, `L′(3,χ₋₃)`) go beyond the catalogued
  spellings.
- **The odd-level rational theorem** for `ζ′(−2k+1, p/q)` is
  Miller–Adamchik Prop. 1 eq. (5) (verified; one misprint in their printed
  variants caught — their companion paper p. 6 has the correct `k = 1`
  instance). The parity obstruction ("`ζ′(−2n, p/q)` does not reduce") is
  emphasized in their Discussion (eq. (21)).
- **Generalized Glaisher**: Bendersky (Acta Math. 61 (1933) 263–322);
  modern treatment M.-A. Coppo, Res. Number Theory 10 (2024), art. 19
  ("Bendersky–Adamchik constants").
- **Not found in print**: the harmonic-number bridge law of §5 (as a
  uniform statement across levels and parities), the flattened `n = 3`
  values of §6.2 in minimal atoms, the `ψ^(−4)(1/4)` no-new-atom
  evaluation, and any integer-relation sweep over these layers (§7
  appears to be the first).

## 9. Artifacts and reproduction

```powershell
# the ladder (symbolic) + quadrature verification
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/negapolygamma_ladder.py
# reflection theorem battery (67 checks)
uv run --with mpmath python src/PolyLog/tools/scratch/negapolygamma-reflection/verify.py
# multiplication theorem battery (81 checks)
uv run --with mpmath python src/PolyLog/tools/scratch/negapolygamma-mult/verify_mult.py
# the sporadic-hunt battery of record (~2 min)
Get-Content src/PolyLog/tools/negapolygamma-hunts.gp | gp.exe -q -f
```

(plus Wolfram-kernel spot checks of every §6 value against
`PolyGamma[-n, p/q]` directly, recorded in this report's residual labels).

## 10. Follow-ups

1. The `q ∈ {5, 8, 12}` values (`ψ^(−n)(1/5)` etc.): the even parts stop
   being elementary (Z-type atoms of the γ-program enter alongside the
   `L′`-atoms) — the natural joint frontier with the Stieltjes program.
2. A negapolygamma section for the antiderivative-ladder article (the two
   ladders are duals: `Γ_n` integrates in the Laurent index at `s = 1`,
   `ψ^(−n)` in the argument at the `s = 0` floor; the engine is shared).
3. Promote the reflection/multiplication laws into certificate-grade store
   entries; the `ζ′(−k, p/q)`-grid rank measurement (the analogue of
   `r_q = φ(q)/2 − 1`) is one afternoon of exact linear algebra away.
4. `FunctionExpand` coverage: Mathematica appears not to know the §6
   values; they would make natural additions to the repository's
   identity stores (and a nice note to Wolfram).

## Addendum: phase 2 (2026-06-12, HEAD ab8c72c69)

The "natural next steps" executed: the q in {5, 8, 12} values, the jet-grid
rank measurement, the q = 6 / reflection-companion values, and the article
section.

### A. The jet-grid rank law (the Koblitz-Ogus-style completeness measurement)

Exact Fraction row-reduction of the known-relation lattice (all reflection
+ all-divisor multiplication rows) on the grids {zeta'(-k, j/q): j=1..q-1},
for ALL q = 3..30 and k = 1..4 (112 cells; artifact
`scratch/negapolygamma/jet_grid_rank.py`):

    r_{q,k} = #{primitive chi of conductor f | q, f > 1, chi(-1) = (-1)^{k+1}}
            = phi(q)/2 - 1   (k odd)
            = phi(q)/2       (k even)

with NO exceptions. Structural content: the reflection rows pin exactly the
(-1)^k-parity eigenspace (the trivial-zero side, whose L-jets are the
Clausen material already on the reflection RHS); the surviving directions
are the parity-opposite L-derivatives; the principal direction never
contributes (pinned by the d = q multiplication row -- zeta'(-k) lives in
the RHS constant inventory: ln A_k for k odd, a zeta(k+1)-multiple for k
even). For k odd the count is numerically identical to the gamma_1-grid law
r_q = phi(q)/2 - 1: the two lattices see the same even-character
obstruction space. Rank-correctness was confirmed numerically at (q,k) =
(5,2) and (12,1): adding the parity-opposite character rows raises the
exact rank to q-1, and the completed system reconstructs the grids to
1.5e-63 (q=5, k=2) and 4.9e-62 (q=12, k=1).

### B. The complete psi^(-3) table at elementary denominators

Beyond the 1/2, 1/3, 1/4 values of the main report
(`scratch/negapolygamma/psi3_sixth_family.py`, residuals <= 1e-51):

- psi^(-3)(2/3), psi^(-3)(3/4): via the n = 3 reflection formula with
  Cl_3(2pi/3) = -(4/9) zeta(3) and Cl_3(pi/2) = -(3/32) zeta(3);
- psi^(-3)(1/6), psi^(-3)(5/6): via the q = 6 transport
  zeta(s,1/6) - zeta(s,5/6) = (6^s + 3^s) L(s,chi_-3) at s = -2 (the even
  part is (2/3) zeta'(-2) by inclusion-exclusion) -- SAME single atom
  L'(3,chi_-3) as the 1/3 value; the q = 6 reflection consistency check
  (Cl_3(pi/3) = zeta(3)/3) passes exactly.

Every elementary-denominator psi^(-3) value therefore lives in
{zeta(3)/pi^2, beta`(3) or L`(3,chi_-3), ln A, gamma, logs}. Gotcha
recorded: mp.nsum on the character L-series Sum chi(n) ln n/n^3
underconverges (~1e-5); use the exact Hurwitz-jet route
L'(3,chi) = -ln q * L(3,chi) + q^{-3} Sum chi(k) zeta'(3, k/q)|_s instead.

### C. Gamma_2 even-sum laws (the antiderivative-ladder side)

Companions of the article's Gamma_1 even sums, all verified at 1e-50
(`scratch/negapolygamma/gamma2_evensums*.py`):

    G2(1/3)+G2(2/3) = (2/3) zeta'''(0) - ln3 zeta''(0) + (L/2) ln^2 3 + ln^3 3/6
    G2(1/4)+G2(3/4) = (2/3) zeta'''(0) - ln2 zeta''(0) + (3L/2) ln^2 2 + (7/6) ln^3 2
    G2(1/6)+G2(5/6) = (2/3) zeta'''(0) + L ln2 ln3 + (1/2) ln2 ln3 ln6     [zeta''(0)-term vanishes]

(L = ln 2pi), giving Gamma_2(2/3), Gamma_2(3/4) for free from the known
Gamma_2(1/3), Gamma_2(1/4).

### D. Tooling and article

`tools/stieltjes_master.py` extended with negapolygamma(n, z) (n <= 5) and
a check battery (ladder vs the Barnes-G route, jet + psi-level reflections,
multiplication row) -- ALL GREEN. Python gotcha caught by the battery:
integer `m ** (-k)` silently yields a 53-bit float; use mp.mpf(m)**(-k).
The article `articles/stieltjes-antiderivative-ladder.tex` gains S7 "The
negative-order polygamma floor" (ladder, both reflection levels with the
Espinosa-Moll gap quote, multiplication, both bridge laws with the
duplication-formula proof of the harmonic-number law, rank proposition,
values) plus the Gamma_2 even-sum corollary in S6.

### E. Values at q = 5, 8, 12: the quadratic and quartic atoms

Full derivation + 59-check verifier (residuals <= ~1e-81 at 80 dps,
re-confirmed at 60 dps; five PARI `zetahurwitz` and four `lfun`
cross-checks via embedded 90-digit references; four independent
`mp.quad` integral checks pinning the Wolfram convention):
`scratch/negapolygamma/values_q5812.py`. Independent transcription check
of every display as typed into the article (29 checks, all <= 1.6e-61):
`scratch/negapolygamma/article_q5812_check.py`.

**k = 1 grids** (one new atom per q, exactly as the rank law demands):
with `Z1 = zeta'(-1)` and `chi_q` the even real quadratic character mod q
(Legendre mod 5, Kronecker (8|.), (12|.)), whose values at -1 are EXACT
rationals `L(-1,chi_5) = -2/5`, `L(-1,chi_8) = -1`, `L(-1,chi_12) = -2`
(confirmed exactly by PARI lfun):

    zeta'(-1,p/5)  = -Z1/5  + Cl2(2 pi p/5)/(4pi) + chi_5(p) [L'(-1,chi_5)/20 - ln5/50]            - ln5/240
    zeta'(-1,p/8)  = -Z1/32 + Cl2(pi p/4)/(4pi)   + chi_8(p) [L'(-1,chi_8)/32 - 3 ln2/32]          + ln2/384
    zeta'(-1,p/12) =  Z1/24 + Cl2(pi p/6)/(4pi)   + chi_12(p)[L'(-1,chi_12)/48 - ln2/12 - ln3/24]  + ln3/576

then `psi^(-2)(p/q) = zeta'(-1,p/q) - Z1 + Q_2(p/q)` through the ladder
(e.g. `psi^(-2)(1/5) = -6Z1/5 + Cl2(2pi/5)/(4pi) + L'(-1,chi_5)/20
- 29 ln5/1200 + ln(2pi)/10 + 2/25`). Proof structure: 2 reflection rows +
all-divisor multiplication rows + the character row
`sum_p chi(p) zeta'(-1,p/q) = (1/q)[L'(-1,chi) + ln q L(-1,chi)]`; for
composite q the known rows have one dependency, which is itself a Clausen
duplication law in disguise (q=8: refl(1/8) - refl(3/8) = m2(1/8) -
m2(3/8) <=> Cl2(3pi/4) = Cl2(pi/4) - G/2; q=12: the m=3 row at 1/12 =
refl(5/12) + m2(1/12)). New atoms (Conrey indices established by chareval
probes, NOT guessed — the even quadratic mod 8 is Conrey 8.5):

    L'(-1,chi_5)  [5.4]   = 0.19252642842052192916857598806603822135190188505537
    L'(-1,chi_8)  [8.5]   = 0.82657385857353997461938357294062271244400907575441
    L'(-1,chi_12) [12.11] = 2.3089345848219193355949190466879982272590360871120

**k = 2, q = 5 (the quartic floor)**: chi = Conrey 5.2 (odd quartic,
chi(2) = +i), `L(-2,chi) = -B_3(chi)/3 = -(4+2i)/5` exactly
(`B_3(chi) = (12+6i)/5`); write `L'(-2,chi) = R + iI`:

    zeta'(-2,{1,4}/5) = -Cl3(2pi/5)/(4pi^2) +- [R/50 - 2 ln5/125]
    zeta'(-2,{2,3}/5) = -Cl3(4pi/5)/(4pi^2) +- [I/50 -   ln5/125]

    R = 0.54428909115826433197888814662329643950201419569708
    I = 0.32168106875154101055735110342435304990087947338757

Flattened through the ladder and the store bridge
`Cl3(2pi/5), Cl3(4pi/5) = -(6/25) zeta(3) +- (sqrt5/4) L(3,chi_5)`:

    psi^(-3)(1/5) = 31 z3/(200 pi^2) - sqrt5 L(3,chi_5)/(32 pi^2) + R/100 - ln5/125 + ln(2pi)/100 + 7/1500  -  Z1/5
    psi^(-3)(2/5) = 31 z3/(200 pi^2) + sqrt5 L(3,chi_5)/(32 pi^2) + I/100 - ln5/250 + ln(2pi)/25  + 41/1500 - 2Z1/5
    psi^(-3)(3/5) = 31 z3/(200 pi^2) + sqrt5 L(3,chi_5)/(32 pi^2) - I/100 + ln5/250 + 9ln(2pi)/100 + 7/125  - 3Z1/5
    psi^(-3)(4/5) = 31 z3/(200 pi^2) - sqrt5 L(3,chi_5)/(32 pi^2) - R/100 + ln5/125 + 4ln(2pi)/25 + 59/750  - 4Z1/5

The multiplication row `sum_p zeta'(-2,p/5) = (6/25) zeta(3)/pi^2` is
DEPENDENT on the reflections (= the Clausen multiplication law
`Cl3(2pi/5) + Cl3(4pi/5) = -(12/25) zeta(3)`), so the residual is exactly
the quartic pair {R, I} — matching `r_{5,2} = phi(5)/2 = 2`.

### F. Phase-2 sporadic hunts: the new atom layer (all negative)

`tools/negapolygamma-hunts2.gp` (PARI 2.17.3, 420 digits, HCUT 1e12) —
apparently the first integer-relation sweep over the quartic pair
{R, I} and the real-quadratic Glaisher family. Controls: planted
relation recovered exactly; random canary correctly rejected. Must-hits
(all HIT with exact small coefficients): the four exact rationals
(L(-2,chi_5.2) = -(4+2i)/5, the three L(-1,chi_q)), the conjugated
bridge in BOTH coordinates — lindep itself recovered
`Im[L'(3,chi)/L(3,chi)] = R/2 - I` (coeffs [-2,1,-2]) and
`Re[L'(3,chi)/L(3,chi)] - R - I/2 = gamma + ln(2pi/5) - 3/2` — and the
three k=1 real-quadratic harmonic bridges. Open hunts, ALL NEGATIVE:

    H1  {R, I} x {beta'(3)/pi^3, L'(-2,chi_-3), standard constants}   (dim 14, height 1e24)
    H2  cross-conductor level -2 odd directions: quartic vs chi_-3, chi_-4, chi_-7, chi_-11  (dim 12, height 1e28)
    H3  real-quadratic Glaisher family L'(-1,chi_D), D = 5..28, + lnA  (dim 17, height 1e20)
    H4  omnibus: phase-2 atoms x phase-1 atoms                         (dim 16, height 1e21)

New PARI gotcha for the books: `I` is the reserved imaginary unit — an
assignment `I = imag(...)` fails with "variable name expected" and the
poisoned vector turns lindep instances into t_POL comparison errors.
Name real/imaginary parts RQ/IQ (or similar) in gp scripts.

### G. Errata found and fixed in phase 2

1. **Parity labels in §5 were inverted** (caught by the values agent
   computing generalized Bernoullis directly): the correct rule for
   k >= 1 is `L(-k,chi) = 0 <=> chi(-1) = (-1)^k` (equivalently
   `B_{k+1}(chi) != 0 <=> chi(-1) = (-1)^{k+1}`). All examples and
   formulas in this report were always consistent with the correct rule;
   only the two parity labels in §5 (and the corresponding hypothesis
   lines in the article's Proposition/Theorem) were swapped. Fixed in
   place.
2. **The harmonic-number bridge needs a conjugation for complex chi**:
   the FE pairs chi at s = k+1 with chi-bar at s = -k, so the law reads
   `L'(k+1,chi)/L + conj(L'(-k,chi)/L) = gamma + ln(2pi/q) - H_k`. For
   the quartic mod 5 (k = 2) the real part verifies to 1e-96 and the
   un-conjugated form leaves the purely imaginary defect
   `2i Im[L'(-2,chi)/L(-2,chi)]` (= -0.0990730463...i for Conrey 5.2),
   which incidentally proves `Im[L'(3,chi)/L(3,chi)] =
   Im[L'(-2,chi)/L(-2,chi)]`. Echo of the project's standing
   conjugation-axiom gotcha. Fixed in §5 and in the article.
3. PARI heredoc gotcha (recorded): a mangled `\\` comment can silently
   kill an `lfuncreate` assignment, after which `lfun(bare_variable,...)`
   interprets the variable as a polynomial defining Q and returns RIEMANN
   zeta jets (L(-2) = 0, L'(-2) = zeta'(-2)) — poison for must-hit
   controls. Keep lfuncreate lines comment-free when piping scripts
   into gp.
4. Python float trap (caught by the stieltjes_master battery): integer
   `m ** (-k)` silently yields a 53-bit float; spell `mp.mpf(m) ** (-k)`.
5. **The n = 2 ψ-level multiplication remainder is NOT the constant
   `(m²−1)/(12m)`** (caught by the phase-2 adversarial review, three
   independent skeptic agents, 504 checks total): the true remainder is
   `ρ_{2,m}(z) = (m−1)(2z+1)/4·ln2π + (m²−1)/(12m) − ((m²−1)/m)ζ′(−1)`
   — z-dependent, the constant being only its rational part. The
   project's own `verify_mult.py` encoded the full remainder all along;
   the prose in §4 and the article had compressed it. Fixed in both.
6. **Adamchik's Proposition 1 is stated for every positive integer
   order**, not n = 1..4 (verbatim: "Let n be a positive integer");
   our jet-floor reflection law is its real part, so the k ≥ 5 cases
   are his too. The novelty framing in §1/§3/§8 and the article was
   narrowed accordingly to: the bare-Clausen real spelling, the k = 0
   inclusion, and the vanishing-trig-factor mechanism note.
