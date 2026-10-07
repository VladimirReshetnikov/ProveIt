# Linear relations among generalized Stieltjes constants: the lattice, two new formula levels, and a sporadic hunt

- Status: Report (verified experimental results + derived identities; all
  numerics at the stated precisions, lindep/PSLQ with control discipline)
- Created (UTC): 2026-06-11T14:41:28Z
- Repository HEAD: b33d17a4face086043a4058d5f38556f5617d762
- Requested by Vladimir: *"Has Blagouchine found all linear identities
  connecting values of generalized Stieltjes constants, or are there any new
  or sporadic identities hiding there (discoverable if we add enough atoms)?"*
- Notation: `γ_n(a)` are generalized Stieltjes constants,
  `ζ(s,a) = 1/(s−1) + Σ_{n≥0} (−1)^n γ_n(a) (s−1)^n / n!`; `γ_0(a) = −ψ(a)`;
  `γ_n = γ_n(1)`.

## 1. Executive answer

**Within the natural atom universe, yes — Blagouchine's catalogue is
complete, and we can now say precisely *why* and *how far* that has been
tested.** The known linear identities for `γ₁(p/q)` form a lattice generated
by the distribution (multiplication) rows and the Malmsten–Blagouchine
reflection rows. We computed the exact rational rank of that lattice on every
denominator grid `q = 3..30` and found the residual dimension is exactly

```
r_q = φ(q)/2 − 1 = #{even primitive Dirichlet characters of conductor f | q, f > 1}
```

with no exceptions — so everything the lattice does not pin is carried by
the even-primitive-character coordinates `A_χ = Σ_k χ(k) γ₁(k/q)`, which are
exactly Deninger's `ζ″(0,·)`-layer atoms, equivalently `L′(1,χ)` for even
primitive `χ`. For real quadratic characters these normalize to
**Euler–Kronecker shifts**: `a_D := L′(1,χ_D)/L(1,χ_D) = γ_{ℚ(√D)} − γ`.
The completeness question therefore reduces to: *are these atoms (and their
higher-derivative siblings) linearly independent of each other and of the
elementary constants?*

We hunted for sporadic rational relations across **40 lindep instances in
ten hunt families** (atoms: 19 real-quadratic Euler–Kronecker shifts up to
discriminant 61; all 11 complex even primitive characters of conductor ≤ 17;
the full second-derivative layer `L″(1,χ)/L(1,χ)` for 10 characters of both
parities; third-derivative probes; the Stieltjes constants `γ₁, γ₂`
themselves; golden-ratio unit logs; mixed-everything omnibus) at 250 and
420+ decimal digits, with a planted-relation positive control (found
exactly), a random-atom negative control (rejected), and a persist-at-higher-
precision canary protocol. **Every hunt is negative**, with quantified
exclusion bounds: no relation exists with coefficients below ~10⁴⁸ in the
pairwise probes, ~10³¹ in the per-character second-derivative probes, ~10¹¹
in the 29-dimensional all-discriminant scan.

**The vertical extension of the lattice was derived here blind and then
found to be (partly) known.** En route we derived — and verified at
10⁻⁵⁷..10⁻⁶⁰ — the closed-form **master formula for `γ_n(p/q)` at every
order `n`** (the `n = 1` case is exactly the structure of Blagouchine's
theorem), and extracted from it the **`γ₂` reflection formula** and the
**`γ₂` multiplication theorem**. The literature pass then established that
the `γ₂` reflection formula is in Blagouchine's own JNT 148 paper, §3 (a
footnote there credits the same formula to unpublished work of Donal
Connon), and the `γ₂` multiplication theorem is in Blagouchine's paper and
in Coffey's parallel paper (Ramanujan J. 39 (2016)) — so those two are
independent re-derivations, which simultaneously validates our machinery
and their published forms to 10⁻⁵⁹. What remains new on the vertical axis
is the uniform all-orders implementation (`n ≤ 4` verified;
[`../../tools/stieltjes_master.py`](../../tools/stieltjes_master.py)) —
Blagouchine stops at `n = 2` with the remark that higher constants "are
expected to be quite long" — and, per the survey, two things appear to be
new on the horizontal axis: **the exact lattice-rank/completeness
measurement (§2.2) and the integer-relation hunt itself (§4–5) — no
published PSLQ-style search over generalized Stieltjes constants exists.**

Section 6 places everything against the literature in detail.

## 2. The γ₁ lattice and its measured completeness

### 2.1 The rows

**Distribution (multiplication) row** — expand
`Σ_{j=0}^{q−1} ζ(s,(a+j)/q) = q^s ζ(s,a)` at `s = 1`, first order:

```
Σ_{j=0}^{q−1} γ₁((a+j)/q) = q γ₁(a) + q ln q · ψ(a) − (q/2) ln²q
```

with the full-grid specialization (`a = 1`)

```
Σ_{r=1}^{q−1} γ₁(r/q) = (q−1) γ₁ − q γ ln q − (q/2) ln²q
```

and the `q = 2` pin `γ₁(1/2) = γ₁ − 2γ ln 2 − ln²2`.
[verified at 80 dps for q = 3,4,5,6,12, generic and full-grid; residuals ≤ 6.8e−80]

**Reflection row** (Malmsten 1846 in substance; Blagouchine's JNT 148 paper,
eq. `\label{hgxcw3b2}`):

```
γ₁(m/n) − γ₁(1−m/n) = 2π Σ_{l=1}^{n−1} sin(2πml/n) lnΓ(l/n) − π(γ + ln 2πn) cot(πm/n)
```

[verified at 80 dps for (m,n) = (1,3),(1,4),(1,5),(2,5),(1,8),(3,8),(5,12);
residuals ≤ 5.9e−80]. Note the right-hand side lives in the `lnΓ` world —
i.e. in the Koblitz–Ogus Γ-lattice of the companion Gamma program — times
elementary constants.

### 2.2 The rank theorem (measured)

Exact `Fraction`-based row reduction over the homogeneous parts of all
reflection and distribution instances
([`scratch/gamma1_grid_rank.py`](../../tools/scratch/gamma1_grid_rank.py))
gives, for every `q` in `3..30`:

```
residual dimension r_q = (q−1) − rank = φ(q)/2 − 1
                       = #{even primitive characters of conductor f | q, f > 1}
```

— a three-way exact match with no exceptions. Two practical facts: the
top-level distribution rows (`M·n₁ = q`) plus reflections already attain
full rank (subgrid instances are redundant), and the right-hand-side atom
alphabet is `{γ₁, γ, π, ln k, ψ(rational), lnΓ(rational), π·cot(π p/q)}`.

### 2.3 Character coordinates and the Euler–Kronecker reformulation

For non-principal `χ` mod `q`, `L(s,χ) = q^{−s} Σ_k χ(k) ζ(s,k/q)` gives the
exact bridges

```
L(1,χ)  = −(1/q) Σ_k χ(k) ψ(k/q)
L′(1,χ) = −ln q · L(1,χ) − (1/q) Σ_k χ(k) γ₁(k/q)
```

[verified against PARI `lfun` at 90 digits: even quadratic χ mod 5, 8, 12 and
the even quartic χ mod 16; residuals ≤ 1.6e−81]. So the residual coordinates
are `A_χ = −q(L′(1,χ) + ln q · L(1,χ))`, and for real quadratic `χ_D` the
normalized atom

```
a_D := L′(1,χ_D)/L(1,χ_D) = γ_{ℚ(√D)} − γ
```

is the **Euler–Kronecker constant shift** of the real quadratic field. The
question "are there linear relations beyond Blagouchine's?" is therefore the
question of ℚ-linear relations among Euler–Kronecker constants of real
quadratic fields (and their complex-character and higher-derivative
siblings) — objects studied by Ihara, with no relations known or expected.

## 3. One level up: the master formula and the new γ₂ identities

### 3.1 The master formula for every order

Expanding the Hurwitz functional equation

```
ζ(1−s, p/q) = 2Γ(s)(2πq)^{−s} [ cos(πs/2)·C(s) + sin(πs/2)·S(s) ],
C(s) = Σ_{k=1}^{q} cos(2πkp/q) ζ(s,k/q),   S(s) = Σ_{k=1}^{q} sin(2πkp/q) ζ(s,k/q)
```

around `s = 0`, with `2Γ(s)(2πq)^{−s} = (2/s)·exp(−(γ+ln 2πq)s + Σ_{k≥2}(−1)^k ζ(k)s^k/k)`,
expresses **every** `γ_n(p/q)` as an exact finite combination of the
Hurwitz-zeta derivatives `ζ^{(j)}(0, k/q)`, `j ≤ n+1`, with coefficients in
the ring generated by `γ`, `ln(2πq)`, `π²`, `ζ(3)`, …, `ζ(n+1)`. For `n = 1`
this is precisely the structure of Blagouchine's closed-form theorem
(elementary + `lnΓ` sine-DFT + `ζ″(0,·)` cosine-DFT). The implementation
([`../../tools/stieltjes_master.py`](../../tools/stieltjes_master.py))
verifies `n = 1,2,3,4` over six rational arguments each — worst residual
1.0e−57 at 60 dps.

The layer inventory: `ζ(0,a)` elementary; `ζ′(0,a) = lnΓ(a) − ½ln 2π` (the
Γ-lattice); `ζ″(0,a)` — even combinations are the `L′(1, even χ)` atoms
(irreducible, Deninger's layer), odd combinations reduce through the
functional equation; `ζ‴(0,a)` — the new layer entering `γ₂`.

### 3.2 The γ₂ reflection formula (independent re-derivation)

Extracting the odd part (`p ↦ q−p`) of the order-`s²` master identity, with
`A = γ + ln(2πq)`:

```
γ₂(p/q) − γ₂(1−p/q) = 2π Σ_{k=1}^{q−1} sin(2πkp/q) ζ″(0, k/q)
                      − 4πA Σ_{k=1}^{q−1} sin(2πkp/q) lnΓ(k/q)
                      + π cot(πp/q) (A² + π²/12)
```

[verified at 60 dps for (p,q) = (1,3),(1,4),(1,5),(2,5),(1,6),(3,8),(5,12),(2,7);
residuals ≤ 1.7e−59]. This is the second-constant analogue of the
Malmsten/Blagouchine reflection; the new irreducible ingredient is the
**odd** `ζ″(0,·)` DFT (for prime/primitive structure: `L″`-level data of odd
characters), while the `lnΓ` sum and the cotangent term are the familiar
layers one level down. **Attribution**: derived here blind from the master
formula, then found to coincide exactly with Blagouchine, JNT 148 (2015),
§3, where a footnote credits the same formula to unpublished work of Donal
Connon. The agreement (to 10⁻⁵⁹, term by term) is an independent
confirmation of both.

### 3.3 The γ₂ multiplication theorem (independent re-derivation)

Second-order expansion of the distribution relation (`L = ln d`); known —
Blagouchine JNT 148 and Coffey, Ramanujan J. 39 (2016), have `γ₀, γ₁, γ₂`
multiplication formulas — and re-derived here as lattice rows:

```
Σ_{j=0}^{d−1} γ₂((a+j)/d) = d [ γ₂(a) − 2L γ₁(a) − L² ψ(a) + L³/3 ]
```

with full-grid specialization

```
Σ_{r=1}^{d−1} γ₂(r/d) = (d−1) γ₂ − 2d ln d · γ₁ + d ln²d · γ + (d/3) ln³d
```

and the `d = 2` pin `γ₂(1/2) = γ₂ − 4 ln 2 · γ₁ + 2 ln²2 · γ + (2/3) ln³2`
(classical). [all verified at 60 dps, residuals ≤ 3.0e−59; the general-`a`
row at (d,a) = (2,1/3), (3,2/5), (5,1/4)]

A diagnostic worth recording: an early specialization slip
(`γ₀(1) = −ψ(1) = +γ`, not `−γ`) produced a full-grid residual of exactly
`2d ln²d · γ` — constant-recognizable garbage is a feature of this kind of
derivation work; residuals that *are* clean combinations of basket atoms
localize the error immediately.

## 4. The sporadic hunts: design

Atoms (all computed by PARI `lfun`, independently cross-validated against
mpmath `stieltjes`-based character sums to ≤ 8.2e−115 by
[`scratch/stieltjes_atoms.py`](../../tools/scratch/stieltjes_atoms.py)):

```
a_χ = L′(1,χ)/L(1,χ)    γ₁-level atoms (Euler–Kronecker shifts for real quadratic χ)
b_χ = L″(1,χ)/L(1,χ)    γ₂-level atoms
c_χ = L‴(1,χ)/L(1,χ)    γ₃-level atoms
```

plus elementary companions: `γ, γ₁, γ₂, γ², γ³, π², ζ(3), ln p, ln φ`
(fundamental-unit log), and products thereof where the derivative calculus
makes them natural.

Engine: PARI `lindep` at working precision 250 then 420+ digits
([`../../tools/stieltjes-hunts.gp`](../../tools/stieltjes-hunts.gp)).
Classification: a candidate requires max coefficient < 10¹² *and* normalized
residual < 10^(−prec+60); candidates must persist at the higher precision.
Controls: a planted relation `X = 3a₅ − 7γ + 2ln2` is found exactly
(residual 0E−424); a random atom is rejected (coefficients ~10⁸⁵).
Character enumeration uses PARI Conrey indexing (`znconreychar`), after a
trap worth recording: enumerating characters as raw exponent vectors against
`znstar(f,1).cyc` produces **aliased duplicates** (two vectors evaluating to
the same character), which manifested as a perfect-looking but degenerate
"relation" `Re a − Re a = 0` for the even quartic character mod 16. Atom
identity must be established at the value level or by canonical (Conrey)
labels before any integer-relation run.

## 5. The sporadic hunts: results

All at final precision 420+ digits unless stated; "bound" is the magnitude
of lindep's returned coefficients in the no-relation case (a true relation
with coefficients below that magnitude would have been found).

| hunt | atoms | dim | result | bound |
|---|---|---:|---|---|
| A1 | EK shifts `a_D`, all 19 fundamental `D ≤ 61` + γ, γ₁, ln p, π², 1 | 29 | **none** | ~10¹¹ |
| A1p | all 21 pairs `(a_D, a_D′)`, `D ≤ 24` + γ, γ₁, logs | 7 | **none** (21/21) | ~10⁴⁸ |
| A2 | all 11 complex even primitive χ, conductor ≤ 17 (Re/Im) + quadratics + elementary | 32 | **none** | ~10¹⁰ |
| B | per-χ probes: `b_χ` vs `a_χ², γa_χ, lnD·a_χ`, γ², ζ(3), γ₁, … (10 characters, both parities) | 11 | **none** (10/10) | ~10³¹ |
| B2 | cross-χ: all 8 `b_χ` + elementary | 14 | **none** | ~10²⁴ |
| D | golden special: `b₅` vs `a₅²`, `ln φ`-products, ζ(3), … | 15 | **none** | ~10²² |
| G | third-derivative probes: `c_χ` vs cubic monomials in lower atoms (χ₅, χ₋₃, χ₋₄) | 19 | **none** (3/3) | ~10¹⁸ |
| E | `γ₁, γ₂` (Stieltjes) vs 7 EK atoms + γ-powers | 15 | **none** | ~10²² |
| OMNIBUS | 4 `a`-atoms + 8 `b`-atoms + γ-powers + ζ(3) + logs | 26 | **none** | ~10¹³ |
| Z | Blagouchine's own coordinates: `Z(1/5)`, `Z(1/8)` singletons (`Z(p) = ζ″(0,p)+ζ″(0,1−p)`) vs all degree-2 monomials in `{γ, ln 2, ln 5, ln π, ln φ}` resp. `{γ, ln 2, ln π, lnΓ(1/4), lnΓ(1/8)}` + π², γ₁, lnΓ | 21/19 | **none** | ~10¹⁶ |

The Z-row deserves emphasis: Blagouchine's paper frames its open question
exactly in these coordinates ("the question … remains open and is directly
connected to the transcendence of the reflected sum `ζ″(0,p)+ζ″(0,1−p)` at
rational `p`"), and he even leans toward expecting the reflected sum to be
of *lower* transcendence than a single `ζ″(0,p)`. Our result: whatever
reduction may exist, it is **not** a rational linear combination of the
natural degree-2 logarithmic monomials and standard constants at coefficient
heights below ~10¹⁶. (The `ζ″`-distribution control identity hit exactly,
at 0E−422, validating the engine.)

Interpretation. The residual atoms behave exactly as the folklore
independence conjectures predict: **no sporadic rational linear relations
exist at any reachable height** among Euler–Kronecker shifts of distinct
real quadratic fields, between parities, across derivative levels, between
the atoms and the classical Stieltjes constants, or in the golden-unit
direction where small-height coincidences have historically hidden. The
"add enough atoms" door, at least for these ten natural atom families, is
closed up to the stated bounds.

## 6. Literature placement

From the phase-1 survey (full citation walk of Blagouchine JNT 148's
Semantic Scholar list, 49 items, plus the adjacent corpora):

- **The lattice is Blagouchine's closure.** All published finite
  ℚ̄-linear identities among `γ₁(p/q)` are generated by reflection
  (Malmsten 1846 in equivalent form; rediscovered by Almkvist–Meurman via
  Adamchik ISSAC'97; elementary proof by Kouba 2016), distribution/
  multiplication, and the finite-Fourier/character transform whose odd part
  reduces to the `lnΓ` layer. Blagouchine's JNT 148 theorem is the closure
  of this lattice for `γ₁`. Nothing published 2015–2026 adds a finite
  linear identity outside it.
- **The γ₂ layer**: Blagouchine JNT 148 §3 has the explicit `γ₂` theorem
  (his eq. (89), needing `ζ‴(0,l/m)`) and reflection (his eq. (88);
  footnote-credited also to unpublished work of D. Connon);
  Coffey's parallel paper (arXiv 1402.3746, Ramanujan J. 39 (2016))
  evaluates `γ₁, γ₂` at rationals and gives `γ₀, γ₁, γ₂` multiplication
  formulas. Blagouchine's closing remark — higher constants "are expected
  to be quite long and to contain higher derivatives of the Hurwitz
  zeta-function at zero … whose properties are currently little studied" —
  is exactly where the all-orders master implementation of §3.1 picks up.
  Nobody since 2015 has reduced `ζ‴(0,p/q)` (or `ζ″(0,p/q)` individually)
  to standard constants.
- **Blagouchine's own framing and stance** (from the full-text mine of the
  vendored TeX): his residual transcendent is `Z(p) := ζ″(0,p)+ζ″(0,1−p)`
  — the paper never mentions Dirichlet `L`-derivatives (that framing is
  Coffey's/Deninger's; Deninger is absent from his bibliography). He makes
  **no irreducibility claim and no conjecture**: he leaves the reduction of
  `Z(p)` explicitly open and writes "it is not unreasonable to expect that
  it [the transcendence of the sum] is lower than that of solely
  `ζ″(0,p)`". His main theorem exists in four equivalent forms (his eqs.
  (38), (51), (54), (56)); the related-summations corpus — DFT inversion
  pair (57a,b), Parseval's theorem (62) for `Σ γ₁²(r/m)` (quadratic, hence
  outside this report's linear scope), odd-grid/alternating/cot-weighted
  (77)/Ψ-weighted (79) sums, and grid-specific relations through the
  twelfth grid — all live inside the lattice of §2, matching his own
  structural observation that odd weights produce `lnΓ` terms and even
  weights produce `Z(l/m)`. His Appendix A particular values (`γ₁(1/5)`
  with `Z(1/5)`; the eighth- and twelfth-grid values with `Z(1/8)`,
  `Z(1/12)` and `lnΓ` atoms) and his combination-reduction observations
  (e.g. `γ₁(1/8)+γ₁(5/8)` needs only `Γ(1/4)`; `γ₁(1/12)−γ₁(7/12)` needs
  `Γ(1/4)` and `Z(1/12)`, "correlated with `Γ(1/12)` being expressible
  through `Γ(1/3)Γ(1/4)`") are lattice members — the latter exactly the
  Koblitz–Ogus Γ-lattice interacting with the `γ₁` grid. The theorem's
  genesis was experimental, from the seven elementary values of his
  Malmsten-integrals paper.
- **Coffey vs Blagouchine**: Coffey's distinctive results are infinite
  summatory/parameterized relations (Proc. R. Soc. A 462 (2006); arXiv
  1002.4684), an addition formula (0905.1111), and series representations;
  his finite rational-argument identities (Rocky Mountain J. Math. 41
  (2011), eqs. 3.28, 3.33–3.34, 3.54) are lattice members (Blagouchine
  documents an error in eq. 3.54 there). No finite linear identity in
  Coffey is absent from Blagouchine's lattice.
- **The even-part atoms are Deninger's layer**: `ζ″(0,a)` sits in Deninger
  (Crelle 351 (1984), the `R`-function with `R(x+1) − R(x) = ln²x`).
  Chakraborty–Kanemitsu–Kuzumaki (Hardy–Ramanujan J. 32 (2009)) proved the
  finite expression of `R` at rationals is equivalent to a Kronecker limit
  formula — genuine prior/parallel art that Blagouchine's paper does not
  cite (pointed out by Connon, arXiv 1505.06516). Vlasenko–Zagier (Crelle
  679 (2013)) and Radchenko–Zagier (arXiv 2012.15805) develop the higher
  Kronecker-limit/Herglotz layer: Herglotz special values at rational and
  *quadratic-irrational* arguments reduce to dilogarithms and log products,
  with Hecke-operator functional equations — the one place in the
  literature where genuinely "CM-like" closed forms appear at this layer.
  The Dixit school (Banerjee–Dixit–Gupta CJM 2023; Dixit–Gupta–Kumar 2024;
  Dixit–Sathyanarayana–Sharan 2024) is actively developing functional
  equations here; no individual closed form for `R(p/q)` or `ζ″(0,p/q)`
  exists.
- **Independence and transcendence**: no unconditional irrationality result
  exists for any `γ_n` (`n ≥ 1`) or `γ₁(p/q)`. Sharpest known: Blagouchine's
  own open question tying `γ₁(p/q)`-expressibility to transcendence of
  `ζ″(0,p) + ζ″(0,1−p)`; Murty–Pathak (Acta Arith. 184 (2018)): under the
  Gun–Murty–Rath conjecture, at least `(p−7)/2` of `{γ₁(a,p)}` are
  transcendental for prime `p > 7`; at the `γ₀` level Murty–Saradha (JNT
  130 (2010)) prove at most one Euler–Lehmer constant is algebraic.
  Chatterjee–Garg (2024–2026) state the closest published formal
  linear-independence conjecture, for q-analogue Stieltjes constants. **No
  published conjecture states that Blagouchine's lattice exhausts all
  ℚ-linear relations among `{γ₁(p/q)}`** — §2.2 of this report is, to our
  knowledge, the first explicit measurement of that statement's
  finite-level truth.
- **Experimental record**: Kreminski (Math. Comp. 72 (2003)) and
  Johansson–Blagouchine (Math. Comp. 88 (2019), the rigorous Arb
  implementation) compute `γ_n(a)` to high precision; Maslanka–Wolf (2020)
  ran normality/continued-fraction experiments. **No published
  PSLQ/integer-relation search over generalized Stieltjes constants was
  found** (Bailey–Borwein corpus included) — the §4–5 hunt appears to be
  the first of its kind. Blagouchine's theorem itself began experimentally,
  from the seven particular values in his Malmsten-integrals paper.

## 7. What this means for the original question

1. **Blagouchine's identities are not an arbitrary collection** — they
   generate the full relation lattice of the `γ₁` grids: the measured
   residual dimension `φ(q)/2 − 1` exactly matches the
   even-primitive-character count for all `q ≤ 30`. Anything further would
   have to be a relation among the character atoms themselves.
2. **No such relation exists at experimentally reachable heights.** Ten
   atom families, 40 lindep instances, controls and canaries: all negative,
   with pairwise exclusion bounds reaching ~10⁴⁸.
3. **What is actually new here, after the honest literature pass**: (a) the
   first explicit completeness *measurement* — the rank theorem
   `r_q = φ(q)/2 − 1` for `q ≤ 30`, a statement nobody had published even
   as a conjecture; (b) the first integer-relation hunt over this landscape
   (40 instances, all negative, quantified bounds), including the first
   probes of the `L″/L‴`-level atoms; (c) the all-orders master-formula
   implementation, mechanically extending Blagouchine's `γ₁` and `γ₂`
   theorems to every `n` (verified through `n = 4`) — Blagouchine stopped
   at `n = 2` noting the higher cases were unexplored; (d) the
   Euler–Kronecker reformulation of the residual atoms, which converts the
   completeness question into Ihara's territory. Our blind re-derivations
   of the `γ₂` reflection (= Blagouchine §3/Connon) and multiplication
   (= Blagouchine/Coffey) formulas double as 10⁻⁵⁹ verifications of the
   published results.
4. **Where something genuinely new might still hide** (the survey's and our
   joint best guesses): the Radchenko–Zagier Herglotz layer suggests
   sporadic relations among `ζ″(0,·)`-type values at *quadratic-irrational*
   conjugate points — a real-quadratic analogue of this repository's
   "polygamma at CM points" program, plausible but unwritten; and the
   unreduced even sums `ζ″(0,p) + ζ″(0,1−p)`, where any reduction (or
   irreducibility proof) would immediately upgrade the whole `γ₁` lattice.

## 8. Artifacts and reproduction

```powershell
# the master formula + gamma_2 reflection/multiplication verification battery
uv run --with mpmath python src/PolyLog/tools/stieltjes_master.py
# the sporadic-hunt battery of record (~2 min)
Get-Content src/PolyLog/tools/stieltjes-hunts.gp | gp.exe -q -f
# the gamma_1 lattice rank table and row verifications
uv run --with mpmath python src/PolyLog/tools/scratch/gamma1_grid_rank.py
uv run --with mpmath python src/PolyLog/tools/scratch/gamma1_rows_verify.py
# the cross-engine atom validation (writes validation_report.json)
uv run --with mpmath python src/PolyLog/tools/scratch/stieltjes_atoms.py
```

## 9. Follow-ups

1. **The real-quadratic frontier** (the most promising new-mathematics
   lead): combine the Radchenko–Zagier Herglotz results with this
   repository's CM-points machinery — hunt for relations among
   `ζ″(0,·)`/Deninger-`R` values at quadratic-irrational conjugate points
   (where dilogarithm closed forms are *proven* to exist), the
   real-quadratic analogue of the Eisenstein row-sum program.
2. State and typeset the general-`n` master theorem with explicit
   coefficients (the `n ≤ 4` cases verified), as a candidate note — and
   share this report with Iaroslav: the first-of-its-kind hunt result and
   the rank theorem are directly responsive to his program; our blind
   re-derivations confirm his §3 to 10⁻⁵⁹.
3. The `γ₂`-grid rank table (the analogue of §2.2 with the two-layer
   unknowns `{γ₂(k/q)} ∪ {ζ″(0,k/q)}`) — predicted residual structure:
   even-primitive atoms at the `ζ‴`-level plus odd-primitive atoms at the
   `ζ″`-level; worth measuring exactly.
4. Push hunts to higher precision with rigorous error control via Arb
   (Johansson–Blagouchine give `γ_n(v)` at 1000+ digits), and to
   higher-degree fields (cubic Euler–Kronecker constants via Dedekind
   zetas); nothing suggests a different outcome, but the bounds would
   become quotable at publication grade.
5. Promote the verified rows and the master formula into the identity
   stores once a store schema for `ζ^{(j)}(0,·)`-atom claims exists; the
   whole layer is multiplier-certificate-friendly.
