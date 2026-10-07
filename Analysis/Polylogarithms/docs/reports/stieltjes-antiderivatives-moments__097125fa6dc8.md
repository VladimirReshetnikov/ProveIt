# Antiderivatives and moments of generalized Stieltjes functions: the ladder formalized, all eight given identities verified, and a harvest of new ones

- Status: Report (verified experimental results + exact derivations; all
  numerics at the stated precisions)
- Created (UTC): 2026-06-11T20:04:55Z
- Repository HEAD: bd2eb075c8116517d518572e48c4f189eacc42c3
- Requested by Vladimir: research the eight identities (four weighted-moment
  integrals of `γ₁`; the `Γ₁(p)`-`ζ″(0,p)` law; `Γ₁(1/3)`, `Γ₁(1/4)`,
  `Γ₂(1/2)`), formally derive or experimentally discover more of the same
  kind; formalize the email sketch to Iaroslav Blagouchine on the
  `Γₙ ↔ ζ`-derivative ladder. Notation: `γₙ(p)` generalized Stieltjes
  functions; `Γₙ(p) = ∫₁^p γₙ(x)dx` (so `Γₙ(1) = 0`, Blagouchine's
  convention); `A_q := γ + ln(2πq)`; `ζ^{(k)}(s₀,a) := ∂_s^k ζ(s,a)|_{s₀}`.

## 1. Executive summary

**All eight given identities are correct** — verified at `1e−50..1e−56`
(§3) — and they all live in one mechanical framework, which is exactly the
formalization of Vladimir's email sketch (§2): the antiderivative ladder
`Γₙ ↔ ζ^{(n+1)}(0,·)`. With the framework in hand plus one new tool (the
**`γ₃` reflection formula**, derived and verified here, §5.3), the family
extends mechanically. New identities produced and verified in this session
(§5): the missing first moment `∫₀¹ x γ₁ dx`, the `m = 3` moments (where
`ζ(3)` and `ζ′(3)` enter), the `[1/2,1]` and `[1,2]` second moments, the
unit-interval-translates family `∫ₙ^{n+1} γₖ dx = −ln^{k+1}n/(k+1)`
(so `∫₁² γ₁ dx = 0` exactly), nine `γ₂`-moment closed forms, the complete
`Γ₁` table at the elementary denominators (`1/2`, `2/3`, `3/4`, `1/6`,
`5/6` — plus even-sum laws), and the next rung of the value ladder:
**`Γ₂(1/3)`, `Γ₂(1/4)`** (containing the new atom
`γ₃(p) − γ₃(1−p)`) **and `Γ₃(1/2)`** (via `ζ⁗(0)`, whose closed form with
the `19π⁴/480` term is assembled from the functional equation en route).

## 2. The ladder, formalized (the email sketch with exact constants)

**Lemma A (derivative chain).** From `∂_p ζ(s,p) = −s ζ(s+1,p)`, expanding
both sides at `s = 0`:

```
d/dp ζ^{(n+1)}(0,p) = (−1)^{n+1} (n+1) γₙ(p)
```

[verified n = 0,1,2 by finite differences at the FD floor]. This is
Connon's (2.15); the email's heuristic — differentiate `1^r + … + n^r =
ζ(−r) − ζ(−r, n+1)` k times in `r` at `r = 0` — is its integer-point
shadow.

**Antiderivative theorem.** Hence, with `Γₙ(1) = 0`,

```
Γₙ(p) = (−1)^{n+1}/(n+1) · [ ζ^{(n+1)}(0,p) − ζ^{(n+1)}(0) ]
```

(Connon's (2.16)). The `n = 1` case **is** the given identity (5), via the
classical `ζ″(0) = γ²/2 + γ₁ − π²/24 − ln²(2π)/2`.

**Interpolation at integers (the sketch's "sums of powers of logarithms",
with the constants pinned).**

```
Γ_{k−1}(N+1) = −(1/k) Σ_{j=1}^{N} lnᵏ j
```

[verified k = 1,2,3 at `1e−49`]. For `k = 1`: `Γ₀(N+1) = −ln N!` ✓ (`Γ₀ =
−lnΓ`). So `Γ_{k−1}` is precisely the analytic interpolant of
`−(1/k)·(lnᵏ-power sums)`, and `ζ^{(k)}(0,x)` is its closed form — the
email's picture is exact as stated once the factor `−1/k` and the offset
`ζ^{(k)}(0)` are included.

**The ζ-jets at 0, all orders** (needed for explicit constants), assembled
exactly from the functional equation
`ζ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)` [each verified `1e−44..1e−46`]:

```
ζ′(0)  = −ln(2π)/2
ζ″(0)  = γ²/2 + γ₁ − π²/24 − ln²(2π)/2
ζ‴(0)  = γ³ + 3γγ₁ + (3/2)γ₂ − ζ(3) + (3/2)γ² ln2π + 3γ₁ ln2π − (π²/8)ln2π − ln³(2π)/2
ζ⁗(0)  = (3/2)γ⁴ + 4γ³ln2π + 6γ²γ₁ + 3γ²ln²2π + (π²/4)γ² + 12γγ₁ln2π + 6γγ₂
         + 6γ₁ln²2π + (π²/2)γ₁ + 6γ₂ln2π + 2γ₃ − ln⁴(2π)/2 − (π²/4)ln²2π
         − 4ζ(3)ln2π − 19π⁴/480
```

(`ζ″(0)`, `ζ‴(0)` classical; `ζ⁗(0)` assembled here — the same machinery
gives every order).

## 3. Verification of the eight given identities

| identity | residual | engine |
|---|---|---|
| (1) `∫_{1/2}^1 γ₁` | 5.0e−51 | exact-parts quadrature over `ζ″(0,·)` |
| (2) `∫₁² x γ₁` | 2.7e−51 | same |
| (3) `∫₀¹ x² γ₁` | 2.7e−51 | same |
| (4) `∫_{1/2}^1 x γ₁` | 2.7e−51 | same — **the transcription is correct**, including the `−ln2·lnπ/6` and `γ ln2/12` terms |
| (5) `Γ₁(p)` law | ≡ Lemma A + `ζ″(0)`; spot-checked by direct `∫γ₁` quadrature | — |
| (6) `Γ₁(1/3)` | 3.6e−56 | independent re-derivation (§5.4) reproduces it |
| (7) `Γ₁(1/4)` | 1.7e−56 | same |
| (8) `Γ₂(1/2)` | 1.2e−50 | framework route `−⅓[ζ‴(0,½) − ζ‴(0)]`, no quadrature |

The "exact-parts" verification route (used throughout; non-circular, anchored
on Lemma A): `∫_a^b x^m γ₁ dx = ½[x^m ζ″(0,x)]_a^b − (m/2)∫_a^b x^{m−1} ζ″(0,x)dx`,
with the analogous `−⅓/+⅓` form for `γ₂` — quadrature only over the fast
`ζ-jet` functions.

## 4. The moment engine

Iterated integration by parts of the Hurwitz transform (via
`∂_x ζ(s−1,x) = −(s−1)ζ(s,x)`) gives the closed form (independently
re-derived here; for the unit interval this is **Espinosa–Moll Part 1,
Theorem 3.7**)

```
∫₀¹ x^m ζ(s,x) dx = − Σ_{j=1}^{m}  m!/(m−j+1)! · ζ(s−j) / [(s−1)(s−2)⋯(s−j)]
```

*(Correction 2026-06-11, round 2: the coefficient is `m!/(m−j+1)!` —
i.e. `m(m−1)⋯(m−j+2)` from unrolling the recursion — not `m!/(m−j)!` as
this display previously read; the engine code always implemented the
recursion itself, so every derived identity below is unaffected.)*

with `[1/2,1]`- and `[1,2]`-variants differing only in boundary terms
(`ζ(σ,1/2) = (2^σ−1)ζ(σ)`; `ζ(σ,2) = ζ(σ)−1`). Laurent-expanding at
`s = 1+t` against `∫x^m ζ(1+t,x)dx = (∫x^m)/t + M₀ − M₁t + (M₂/2)t² − …`
reads off every `γₖ`-moment as exact combinations of the atoms
`ζ^{(k)}(1−j)`, `j = 1..m` — i.e. the jets at `0, −1, −2, …`. Conversions to
Blagouchine's `s = 2,3` spelling (round 1: found exactly by lindep at 120
digits, residuals ≤ `1e−134`; round 2: derived rigorously from the
functional equation — `scratch/round2_assembly.py` part 4 — so these are
now theorems):

```
ζ′(−1) = [6ζ′(2)/π² − γ − ln2π + 1]/12
ζ″(−1) = −ζ″(2)/(2π²) + (ζ′(2)/π²)(γ+ln2π−1) − (γ+ln2π)²/12 + (γ+ln2π)/6 + π²/144
ζ′(−2) = −ζ(3)/(4π²)            (classical)
ζ″(−2) = (ζ(3)/4π²)(3 − 2γ − 2ln2π) + ζ′(3)/(2π²)
```

Implementation: [`scratch/gamma_moment_engine.py`](../../tools/scratch/gamma_moment_engine.py)
(sympy, exact). The engine **reproduces the given identities (1)–(4)
symbolically** — e.g. `[0,1] m=2` flattens, through the dictionary, to
identity (3) coefficient-for-coefficient — and all nine of its cases
(`m = 0..3` × three intervals) verify at `1e−40` for both the `γ₁`- and
`γ₂`-moments.

## 5. New identities (each verified at the stated precision)

### 5.1 New γ₁-moments

```
∫₀¹ x γ₁(x) dx        = ζ″(0)/2 = γ²/4 + γ₁/2 − π²/48 − ln²(2π)/4            [1e−50]

∫₀¹ x³ γ₁(x) dx       = 3γ²/8 + γ₁/2 − π²/32 + (γ ln2π)/4 − ln²(2π)/8
                        − (3/(4π²))(ζ(3) + 2ζ′(2))(γ + ln2π)
                        + (3/(4π²))(ζ′(3) + ζ″(2))                            [1e−46]

∫₁² x² γ₁(x) dx       = 9/4 + 3γ₁/2 + 5γ²/6 − 5π²/72 + (γ ln2π)/6 − (2/3)ln²(2π)
                        − (ζ′(2)/π²)(γ + ln2π) + ζ″(2)/(2π²)                 [6e−47]

∫_{1/2}^1 x² γ₁(x) dx = …                                                    [2e−46]
```

(the `[1/2,1] m=2` flattened form — atoms `γ², γ₁, π², γ·ln, ln², ζ(3)- and
ζ′(2)-weighted (γ+ln) blocks, ζ′(3), ζ″(2)` — is bulky; the normative exact
expression is the verified output of
[`scratch/moments_finalize.py`](../../tools/scratch/moments_finalize.py)).

**Unit translates** (from the interpolation theorem; `k ≥ 0`, `n ≥ 1`):

```
∫_n^{n+1} γₖ(x) dx = − ln^{k+1} n / (k+1)        e.g.  ∫₁² γ₁ dx = 0  exactly,
                                                       ∫₂³ γ₁ dx = −ln²2/2     [1e−51]
```

(the `n = 1` case `∫₁² γₖ dx = 0` is Connon 1902.00510 (2.18)–(2.19); the
general translate is its immediate extension).

### 5.2 New γ₂-moments

```
∫₀¹ x γ₂(x) dx = −ζ‴(0)/3
  = ζ(3)/3 − γ³/3 − γγ₁ − γ₂/2 − (γ²/2)ln2π − γ₁ln2π + (π²/24)ln2π + ln³(2π)/6   [3e−50]

∫₁² x γ₂(x) dx = ∫₀¹ x γ₂(x) dx − 2                                              [4e−46]

∫_{1/2}^1 γ₂(p) dp = −Γ₂(1/2)        (the given identity (8), negated)           [4e−46]
```

plus the engine's verified `M₂` closed forms for all nine interval/weight
cases (the `m = 2,3` ones additionally need `ζ‴(−1)`, `ζ‴(−2)` conversions —
left in jet spelling in the artifact).

### 5.3 The γ₃ reflection formula (new tool)

Extending the project's master-formula machinery one order:

```
γ₃(p/q) − γ₃(1−p/q) = 2π S₃ − 6π A_q S₂ + (6A_q² + π²/2) π S₁
                      − (2A_q³ + A_q π²/2 + 4ζ(3)) π S₀,
S_j := Σ_{k=1}^{q−1} sin(2πkp/q) ζ^{(j)}(0, k/q),   S₀ = ½cot(πp/q)
```

[verified at (1,3),(1,4),(1,5),(2,5),(3,8); residuals ≤ `1e−58`]. This is
the `γ₃` analogue of Malmsten's reflection (`γ₁`-level, 1846) and the
Blagouchine/Connon `γ₂` reflection; at `q = 3, 4` it inverts to express the
odd jet `ζ‴(0,p/q) − ζ‴(0,1−p/q)` through the single new atom
`γ₃(p/q) − γ₃(1−p/q)` — which is what unlocks §5.5.

### 5.4 The Γ₁ table completed at the elementary denominators

With `c := π²/48 + ln²(2π)/4 − γ²/4 − γ₁/2` (the constant of identity (5)):

```
Γ₁(1/2) = π²/48 − γ²/4 − γ₁/2 − ln²2/4 − (ln2·ln2π)/2 + ln²(2π)/4            [1e−79, PSLQ exact-hit]

Γ₁(1/3) + Γ₁(2/3) = 2c − ln²3/4 − (ln3·ln2π)/2                               [1e−79]
Γ₁(1/4) + Γ₁(3/4) = 2c − (3/4)ln²2 − (ln2·ln2π)/2                            [1e−79]
Γ₁(1/6) + Γ₁(5/6) = 2c − (ln2·ln3)/2                                         [exact]
```

and the individual values `Γ₁(2/3)`, `Γ₁(3/4)`, `Γ₁(1/6)`, `Γ₁(5/6)`
assembled exactly (q=6 by the character transport
`ζ(s,1/6) − ζ(s,5/6) = (6^s + 3^s) L(s,χ₋₃)`, which re-expresses everything
in the *same* atom `γ₂(1/3) − γ₂(2/3)` as identity (6)) — all verified at
`1e−45..1e−46`
([`scratch/gamma1_sixth_assembly.py`](../../tools/scratch/gamma1_sixth_assembly.py)).
Independent re-derivations of the given (6), (7) fall out of the same
assembly [1.7e−56, 3.6e−56].

### 5.5 The next rung: Γ₂(1/3), Γ₂(1/4), Γ₃(1/2)

Structural form (q = 3, 4), all pieces explicit:

```
Γ₂(p/q) = −⅓ [ ½(Z₃ + D₃) − ζ‴(0) ],
Z₃(1/q)  = ∂³_s[(q^s − …)ζ(s)]|₀                       (elementary, distribution)
D₃(1/q)  = (2/√3 at q=3; 1 at q=4) · S₃,  S₃ inverted from §5.3:
S₃ = [ (γ₃(p/q)−γ₃(1−p/q)) + 6πA_q S₂ − (6A_q²+π²/2)πS₁ + (2A_q³+A_qπ²/2+4ζ(3))πS₀ ] / 2π
```

with `S₂` likewise inverted from the `γ₂` reflection. Flattened and
verified [`1e−55`]: `Γ₂(1/3)` carries the atoms
`{γ₃(1/3)−γ₃(2/3), (γ, ln-weighted)·(γ₂(1/3)−γ₂(2/3)), lnΓ(1/3), γ₂, γγ₁,
γ³, ζ(3), cubic log monomials}` — the exact analogue of how (6) extends (5);
similarly `Γ₂(1/4)` with the q=4 atoms. The full flattened forms are the
verified output of
[`scratch/gamma_values_assembly.py`](../../tools/scratch/gamma_values_assembly.py).

And one more rung straight up the `1/2`-tower [1e−46]:

```
Γ₃(1/2) = ¼[ζ⁗(0,1/2) − ζ⁗(0)],   ζ⁗(0,1/2) = ∂⁴_s[(2^s−1)ζ(s)]|₀ :

Γ₃(1/2) = −(3/8)γ⁴ − (3/2)γ²γ₁ − (3/2)γγ₂ − γ₃/2 − (π²/16)γ² − (π²/8)γ₁ + 19π⁴/1920
          + γ³(ln2 − ln2π) + (3/4)γ²(ln²2 + 2ln2·ln2π − ln²2π) + 3γγ₁(ln2 − ln2π)
          + (3/2)γ₁(ln²2 + 2ln2·ln2π − ln²2π) + (3/2)γ₂(ln2 − ln2π)
          − ln⁴2/8 − (ln³2·ln2π)/2 − (3/4)ln²2·ln²2π − (ln2·ln³2π)/2 + ln⁴(2π)/8
          − (π²/16)(ln²2 + 2ln2·ln2π − ln²2π) + ζ(3)(ln2π − ln2)
```

(`= γ₂/…`-pattern check: the given (8) is the `k = 2` member; this is
`k = 3`; the `k = 4` member is one more turn of the same crank).

## 6. Literature placement

From the full survey (local PDF corpus + downloaded sources + web; the
whole chain re-verified numerically in
[`scratch/stieltjes-antideriv/verify.py`](../../tools/scratch/stieltjes-antideriv/verify.py)):

- **The `Γₙ` notation** appears in print only in Blagouchine's two papers,
  and only for `n = 1`: introduced in the Malmsten-integrals paper
  (Ramanujan J. 35 (2014), exercise no. 22, pp. 69–71; normalization left
  free) and reused in JNT 148 (2015) §II.5 p. 33, whose only printed `Γ₁`
  relation is the constant-free
  `ζ″(0,p)+ζ″(0,1−p) = −(3ln2+2lnπ)ln2 − 4Γ₁(1/2) + 2Γ₁(p) + 2Γ₁(1−p)`.
- **The master law** is published in three spellings: differential —
  Chakraborty–Kanemitsu–Kuzumaki, Hardy–Ramanujan J. 32 (2009), Lemma 2
  (`Rₙ′ = −n γₙ₋₁`, `Rₙ = (−1)^{n−1}ζ^{(n)}(0,·)`; `n = 2` is Deninger
  1984); integrated — **Connon, arXiv:1902.00510 (2019), eq. (2.16)**
  (eq. (2.15) the differential form); engine — **Espinosa–Moll Part 2,
  Thm 2.1** (`∫ζ(z,q)dq = ζ(z−1,q)/(1−z)`).
- **Identity (5)** as assembled is **apparently unpublished** — it is
  Connon (2.16) at `n = 1` composed with the Ramanujan/Apostol `ζ″(0)`
  closed form. Substituting it into Blagouchine's p. 33 display is an
  identity check (passes).
- **Identities (6), (7), (8) — not found anywhere in print** (consistent
  with the Blagouchine–Reshetnikov correspondence origin; Vladimir's own
  notebook corpus also lacks them). All ingredients are published: the even
  part via Connon arXiv:1505.06516 §4 (the `ζ″(0,·)` multiplication
  theorem) and Blagouchine RamJ no. 24(a)
  (`ζ″(0,1/2) = −(3/2)ln²2 − lnπ·ln2`); the odd part via **Blagouchine JNT
  eq. (89)** — the `γ₂` reflection (footnote 39 there credits the same
  formula to unpublished work of D. Connon) — with companion (90); `ζ‴(0)`
  is in Choudhury (1995) and inside Blagouchine's `C_m(r)` display (JNT
  p. 34). The *inversion for individual* `ζ″(0,p)`, `ζ‴(0,1/2)` is the
  unpublished step.
- **The four moment identities**: `∫₀¹x²γ₁` is *effectively published* —
  by parts it is exactly Blagouchine JNT p. 14's unnumbered
  `∫₀¹ p·ζ″(0,p)dp` display (obtained there from his Parseval formula (29)
  + Espinosa–Moll Part 1 (7.3)); the other three are unpublished assemblies
  of published ingredients. `∫₁²γₙ dx = 0` itself **is published**:
  Connon 1902.00510, eqs. (2.18)–(2.19) — our `∫ₙ^{n+1}` translate family
  is its immediate generalization — and `∫₀¹ζ^{(j)}(s,a)da = 0` is Coffey
  arXiv:0905.1111 Prop. 6 (Deninger 1984 for `j = 2`).
- **Attribution correction to §4**: the closed form of the unit-interval
  Hurwitz transform derived there is **Espinosa–Moll Part 1, Theorem 3.7
  (eq. (3.13))** — independently re-derived here; the `[1/2,1]`/`[1,2]`
  boundary variants and the systematic Laurent extraction of `γ₁/γ₂`-moments
  remain, to our knowledge, new as a method-and-table.
- **Adjacent published identities** worth keeping at hand (catalogued with
  equation numbers by the survey): Blagouchine JNT (28) (Fourier
  coefficients of `ζ(a,·)` — every moment here is a finite combination of
  them), (75) (the *discrete* first moment `Σ(r/m)γ₁(r/m)`), (78) (the
  integral representation governing what `Γ₁(p)+Γ₁(1−p)` can reduce to);
  Connon (5.18)/(5.19) (`(n+1)Γₙ(x)` as an explicit log-series) and the
  `g₁(x)` bridge (5.3)–(5.4); CKK Thm 1 (all `γₙ(p/q)` data in
  `ζ^{(j)}(0,l/q)` vocabulary); Espinosa–Moll Part 2 §3–4 (the
  negapolygamma/`A_k(q)` floor; Blagouchine's own Nota Bene:
  "antiderivatives of lnΓ are currently not well-studied"); Kölbig (1994)
  `∫₀¹ψ(x)sinπx dx` (the `γ₀`-level template for half-period moments);
  Coffey 0905.1111 eq. (1.13) (regularized generating function of the
  individually-divergent zeroth moments on `[0,1]`).

## 7. Artifacts and reproduction

```powershell
uv run --with mpmath python src/PolyLog/tools/stieltjes_master.py
#   (now includes: derivative master identity, gamma_1' rows, the
#    antiderivative ladder + interpolation + gamma_3 reflection -- ALL GREEN)
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/gamma_moment_engine.py
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/moments_finalize.py
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/gamma_values_assembly.py
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/gamma1_sixth_assembly.py
uv run --with sympy --with mpmath python src/PolyLog/tools/scratch/zeta_jets_assembly.py
uv run --with mpmath python src/PolyLog/tools/scratch/moments_fast_verify2.py
uv run --with mpmath python src/PolyLog/tools/scratch/gamma_antideriv_framework.py
```

## 8. Follow-ups

1. The general `Γₙ(p/q)` master statement: even part by distribution, odd
   part by the `γ_{n+1}`-reflection cascade (§5.3 generalizes to every
   order by the same expansion); at `q ∈ {5, 8, 12}` the even part
   additionally meets the `Z(p)`-atoms of the γ-level program — worth
   stating jointly with Iaroslav.
2. The `k = 4` rung (`Γ₄(1/2)`, `γ₄` reflection) is mechanical from the same
   machinery; so are mixed moments `∫ x^m γₙ` for higher `m` (each new `m`
   admits one new jet column `ζ^{(k)}(1−m)`).
3. Promote the ladder + reflections into certificate-grade store entries.
4. A short joint note ("the antiderivative ladder of the Stieltjes
   functions") packaging §2, §5.3, and the §5.5 values — the email thread
   with Iaroslav is the natural venue.

## Addendum: round 2 (2026-06-11T20:55:03Z, HEAD ca1bb4082)

Prompted by Vladimir, with the observation that Mathematica already knows
the Glaisher spelling of the bridge: `FunctionExpand[Zeta'[2]]` gives
`(1/6) pi^2 (EulerGamma + Log[2] - 12 Log[Glaisher] + Log[pi])`, i.e. our
even-parity bridge `zeta'(2) = zeta(2)(gamma + ln 2pi - 12 ln A)`.

New results (artifacts: `scratch/g4_reflection_check.py`,
`scratch/round2_assembly.py`; everything below now has a complete symbolic
derivation -- the lindep-found conversion dictionary entries of round 1 are
superseded by rigorous FE-jet derivations):

1. **The gamma_4 reflection formula** [verified 1e-47 at five (p,q)]:
   `g4(p/q) - g4(1-p/q) = 2pi S4 - 8pi A S3 + (12A^2+pi^2) pi S2
    - (8A^3 + 2 pi^2 A + 16 zeta(3)) pi S1
    + (2A^4 + pi^2 A^2 + 16 A zeta(3) + (19/120) pi^4) pi S0`,
   `A = gamma + ln(2 pi q)`, `S_j = sum_k sin(2pi k p/q) zeta^(j)(0,k/q)`.
2. **zeta^(5)(0)** assembled from the functional equation (terms include
   `-12 zeta(5)`, `-(19/96) pi^4 ln2pi`, `10 gamma^2 zeta(3)`, `(5/2)gamma_4`;
   full form in `round2_assembly.py` output) [1.7e-43].
3. **Gamma_4(1/2)** fully explicit (the k = 4 rung of the 1/2-tower;
   atoms up to `gamma_4`, `zeta(5)`, quintic logs) [1e-45].
4. **Gamma_3(1/3) and Gamma_3(1/4)** via the gamma_4-reflection inversion +
   distribution [1.2e-49, 1.4e-49]; values 0.36330171740758047...,
   0.92284974477155929... .
5. **The general first-moment theorem** [verified m = 1..6]:
   `int_0^1 x^m gamma_1(x) dx = sum_{j=1}^m (-1)^(j-1) C(m,j-1)
    [ (1/2) zeta''(1-j) + H_{j-1} zeta'(1-j) + (1/2)(H_{j-1}^2 + H_{j-1}^(2)) zeta(1-j) ]`
   -- binomial x harmonic-number coefficients on the zeta-jets at
   non-positive integers; the (j-1)-coefficients come from
   `1/((1-t)(2-t)...(j-1-t))`-expansion, so the gamma_n-moment analogue has
   complete-homogeneous-symmetric harmonic coefficients.
6. **Rigorous conversion dictionary**: the jets at s = -1 (from jets at 2)
   and s = -2 (from jets at 3) are now derived symbolically from the
   functional equation (`round2_assembly.py` part 4), reproducing the
   round-1 lindep entries exactly; in Glaisher spelling the first reads
   `zeta'(-1) = 1/12 - ln A` against
   `zeta'(2) = zeta(2)(gamma + ln 2pi - 12 ln A)`.
7. **Hurwitz-transform coefficient corrected** in section 4 (display-level
   only; engine and all derived identities unaffected).

The full result set of this report is also presented in publication form:
[`../articles/stieltjes-antiderivative-ladder.tex`](../articles/stieltjes-antiderivative-ladder.tex)
(LaTeX + PDF, committed alongside this addendum).

## Erratum and referee-round addendum (2026-06-12)

An external referee-style review (OpenAI ChatGPT, prompted by Vladimir)
of the companion article `docs/articles/stieltjes-antiderivative-ladder.tex`
found a SIGN ERROR in the article's transcription of the given identity
(6): the `Gamma_1(1/3)` display had `+ (2/3) ln3 ln2pi` where the correct
term is `- (2/3) ln3 ln2pi` (discrepancy exactly (4/3) ln3 ln2pi; the
corrected display verifies at 2.7e-51). The identity as verified in this
report (table row (6), residual 3.6e-56) was always the correct one — the
error was introduced in the article transcription, in a section whose
checker run predated the adversarial-review discipline. A subsequent full
re-verification of EVERY displayed equation in the article's sections 1-6
(185 checks at 50 dps, `tools/scratch/referee-round/verify_s1_6.py`)
found NO other mathematical error.

Two more referee-round results of record:

- **Literature correction**: Apostol (Math. Comp. 44 (1985), Theorem 3)
  gives a closed form of `zeta^(n)(0)` at EVERY order in terms of the
  Laurent coefficients of `Gamma(s) zeta(s)` at s=1, and prints the n=4
  instance in that vocabulary. The novelty claim for the article's jets
  is therefore narrowed to: the fully expanded Stieltjes-vocabulary form
  of `zeta^(4)(0)` (with the 19pi^4/480 constant) and any explicit form
  of `zeta^(5)(0)` (Apostol's symbolic examples stop at n=4; Choudhury
  1995 is credited in the citation trail only with zeta''(0)/zeta'''(0)).
  Kouba (J. Classical Anal. 9 (2016) 79-88) gives an elementary
  Kummer-expansion proof of the n=1 reflection (Malmsten's formula) — now
  cited in the article.
- **New article content**: an appendix with the FULLY EXPANDED closed
  forms of `Gamma_2(1/3)`, `Gamma_2(1/4)`, `Gamma_3(1/3)`, `Gamma_3(1/4)`
  (verified at 90 dps, residuals <= 2.5e-89,
  `tools/scratch/referee-round/appendix_values.py`); a Bell-polynomial
  recurrence remark for the zeta-jets at 0 (exact sympy check + 50-dps
  numerics, `tools/scratch/referee-round/jets_recurrence.py`); structure
  found during flattening: every special-atom coefficient is univariate
  in `A_q = gamma + ln(2pi q)` — the `lnGamma(1/q)` coefficient is
  `-(A_q^2 - pi^2/12)` at rung 2 and `A_q^3 - (pi^2/4)A_q + 2 zeta(3)`
  at rung 3, with the Stieltjes-difference coefficients the lower rows of
  the same triangular inversion.
