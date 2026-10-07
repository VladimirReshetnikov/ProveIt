# Derivatives of generalized Stieltjes constants at rational points: the s = 2 landscape, its lattice, bridges, and a sporadic hunt

- Status: Report (verified experimental results + derived identities; honest
  literature attribution; all numerics at the stated precisions; lindep/PSLQ
  with control discipline)
- Created (UTC): 2026-06-11T19:02:09Z
- Repository HEAD: c1b9341dab11b24562f801ad6804e2e4776203b6
- Requested by Vladimir: *"Please research derivatives of generalized
  Stieltjes constants at rational points (of course, 'constant' is a misnomer
  here; they are really functions). Are there any linear identities
  connecting them?"*
- Notation: `γ_n(a)` from `ζ(s,a) = 1/(s−1) + Σ_{n≥0} (−1)^n γ_n(a)(s−1)^n/n!`;
  primes on `γ_n` denote `d/da`; `ζ^{(j)}(s₀,a)` denotes `∂_s^j ζ(s,a)|_{s=s₀}`;
  `A` is the Glaisher–Kinkelin constant; `G` Catalan's constant.

## 1. Executive answer

**Yes — there are linear identities, and they organize completely.** The
*a*-derivative tower telescopes onto the `s = 2` derivative layers of the
Hurwitz zeta function:

```
γ_n′(a) = (−1)^{n+1} [ ζ^{(n)}(2,a) + n ζ^{(n−1)}(2,a) ]
```

so "linear identities among `γ_n′(p/q)`" = "linear identities among
`ζ^{(j)}(2, p/q)`". **This master identity is not new** — it is Coffey's
eq. (1.3) (arXiv:0905.1111, *Rocky Mountain J. Math.* 44 (2014) 443–477,
Prop. 1(ii)), obtained by differentiating his Wilton-type addition formula
in the parameter; its all-orders form (Coffey Cor. 2, with unsigned
Stirling-first-kind coefficients) is `γ_l^{(j)}(a) = (−1)^l Σ_k (−1)^k k!
\binom{l}{k} s(j+1,k+1) ζ^{(l−k)}(j+1,a)`, and Connon (2019) has it
independently. **What did not exist in the literature is the
rational-argument landscape** of these functions — the Blagouchine-style
theorem one level up. That is what this report maps:

1. **The relation lattice and its rank (apparently first).** The only rows
   with elementary right-hand sides are the **distribution rows**; their
   exact rational rank on every grid `q = 3..30` leaves residual dimension

   ```
   r′_q = φ(q) − 1  =  #{non-principal Dirichlet characters mod q, both parities}.
   ```

   Sharp contrast with the underived γ-level (`φ(q)/2 − 1`, even characters
   only): **differentiation destroys the Malmsten/Blagouchine reflection
   mechanism** — the reflection object `W(x) = ∂_s[ζ(s,x)+ζ(s,1−x)]|_{s=2}`
   is itself atom-bearing, not elementary (§5) — so both parities survive.

2. **The level-2 character coordinate (apparently new):**
   `Σ_k χ(k) γ₁′(k/q) = q² [ L′(2,χ) + (1 + ln q) L(2,χ) ]`, the derivative
   analogue of Murty–Pathak's level-1 `L′(1,f) = −Σ_a f(a) γ₁(a,q)`. The
   atoms are `L′(2,χ)` per non-principal χ (with `L(2,χ)`: elementary for
   even χ, Catalan/Clausen-family for odd χ), plus the principal `ζ′(2)`.

3. **The bridge theory to the s = −1 generalized Glaisher layer.** The
   functional equation makes the `s = 2` and `s = −1` derivative layers
   interchangeable through bridges with one uniform constant
   `C_q = γ + ln(2π/q) − 1`. The underlying FE-derivative machinery is
   classical (Miller–Adamchik 1998 for `ζ′(−1, p/q)`; Bailey–Borwein 2016,
   Thm 4, for both parities); the uniform `C_q` packaging and the
   q-independent second-order bridge `[(log L)″(2) − (log L)″(−1)] = 1 + π²/12`
   are our synthesis. The principal case is the classical
   `ζ′(2) = ζ(2)(γ + ln 2π − 12 ln A)` — Espinosa–Moll's `ζ′(2)` and
   Glaisher's `A` are **one atom**.

4. **The first integer-relation sweep over this landscape.** No published
   PSLQ search over the `ζ′(2,·)/ζ′(−1,·)` layers exists (Bailey–Borwein's
   character-MTW experiments are the nearest prior art). We ran 10 hunt
   families at 420 digits with controls: every structural bridge re-emerged
   as an exact lindep hit (16 must-hits), and **all open hunts are
   negative** (bounds 10¹⁸–10³⁴), including **`β′(2)` confirmed as a genuine
   atom** — `β′(2) = 0.08158073611659279510…`, not reducible over a rich
   Catalan/lnΓ(1/4)/π-power basket and not even present in OEIS.

## 2. The master identity (Coffey 2009; Connon 2019)

From `∂_a ζ(s,a) = −s ζ(s+1,a)`, matching Laurent coefficients at `s = 1`
(the right side is regular there — `ζ(2,a)` — which is why differentiation
*shifts the landscape from the s = 0/1 pair to the s = 2/−1 pair*):

```
γ_n′(a) = (−1)^{n+1} [ ζ^{(n)}(2,a) + n ζ^{(n−1)}(2,a) ].
```

[Coffey eq. (1.3); re-verified here for n = 0..3 at two arguments each
against central finite differences of `mp.stieltjes(n, ·)`, residuals at the
finite-difference floor; `γ₀′ = −ψ′` exact.] Coffey's only extracted value
is `γ₁′(1) = ζ(2)[γ + ln 2π + 12 ζ′(−1)]` (his Cor. 1; verified at 1e−51) —
he develops no rational-argument table, no character decomposition, no atom
analysis. Connon (2019) additionally gives the clean `s = 0 ↔ 1 ↔ 2`
antiderivative dictionary (e.g. `∂_x² ζ″(0,x) = 2ζ′(2,x) + 2ζ(2,x)`,
exhibiting the `ζ′(2,·)` layer as the second derivative of Deninger's `R`).

The ground floor `n = 0` is the trigamma grid — the π²/Clausen lattice
already catalogued in this repository (`psi_reducer.py`, residual `φ(q)/2`,
Cl₂ atoms). More generally `∂_a^k γ_n(a)` lives at the `s = k+1` layers
(Coffey Cor. 2); everything below specializes the first derivative, `k = 1`.

## 3. The lattice and the rank theorem

**Distribution rows** (the only elementary-RHS rows):

```
Σ_{j=0}^{d−1} γ₁′((a+j)/d) = d² γ₁′(a) + d² ln d · ψ′(a)
```

[verified at 60 dps, q = 3, 5, generic a; residual ≤ 8e−59], with character
coordinates `Σ_k χ(k) γ₁′(k/q) = q² [ L′(2,χ) + (1 + ln q) L(2,χ) ]`
[verified χ₅ at 60 dps, and χ₋₄ giving `16[β′(2) + (1+ln4)β(2)]` at 7e−40].

**Rank theorem (measured).** Exact `Fraction` row reduction of all
distribution instances on `{γ₁′(k/q)}_{k=1..q−1}`
([`scratch/g1p_grid_rank.py`](../../tools/scratch/g1p_grid_rank.py)) gives,
for every `q` in `3..30`,

```
r′_q = (q−1) − rank = φ(q) − 1
```

— exactly one residual direction per non-principal character mod `q`, both
parities. The same matrix governs every derivative order `n ≥ 1` (only
right-hand sides change), so the count is uniform in `n`. Landscapes
compared:

| landscape | FE pairing | elementary reflection? | residual per grid |
|---|---|---|---|
| `γ_n(p/q)` | `s = 1 ↔ s = 0` | yes (Malmsten/Blagouchine) | `φ(q)/2 − 1` (even χ) |
| `γ_n′(p/q)` | `s = 2 ↔ s = −1` | **no** (§5) | `φ(q) − 1` (all χ ≠ χ₀) |
| `γ₀′ = −ψ′` floor | — | yes (`π²/sin²`) | `φ(q)/2` (Cl₂ atoms) |

## 4. The bridge theory: s = 2 ↔ s = −1 (generalized Glaisher layer)

All derived from the completed-`L` functional equation and verified
dual-engine (mpmath 80 dps, residuals ≤ 2.2e−78; PARI `lfun` 95–135 digits);
the lindep battery independently *rediscovered* each bridge as an exact hit.
With `C_q := γ + ln(2π/q) − 1` (uniformity from `ψ(3/2) = ψ(−1/2) = 2 − γ − 2ln2`):

- **principal** (`q = 1`): `ζ′(2)/ζ(2) + ζ′(−1)/ζ(−1) = C₁ = γ + ln 2π − 1`,
  ≡ classical `ζ′(2) = ζ(2)(γ + ln 2π − 12 ln A)`. The Espinosa–Moll atom
  `ζ′(2)` and Glaisher's `A` are one atom.
- **even primitive χ**: `L′(2,χ)/L(2,χ) + L′(−1,χ̄)/L(−1,χ̄) = C_q`.
- **odd primitive χ** (trivial zero at `s = −1`): first order
  `L′(−1,χ) = ε(χ) q^{3/2} L(2,χ̄)/(4π)` (real χ: `ε = 1`; anchor
  `β′(−1) = 2G/π`); second order
  `L′(2,χ)/L(2,χ) + ½ L″(−1,χ)/L′(−1,χ) = C_q` (no `π²` until jet order 3).
- **second order, even, q-independent**:
  `[(log L)″(2,χ) − (log L)″(−1,χ)] = 1 + π²/12`
  [verified 1e−134 for D = 5, 8, 12, 13, 17].

**Concrete consequences at the small grids** (Miller–Adamchik 1998
territory, re-derived and verified): for `q ∈ {3,4,6}` *all* non-principal
characters are odd, so the `s = −1` layer fully reduces —

```
ζ′(−1,1/4) = −ζ′(−1)/8 + G/(4π),   ζ′(−1,1/4)+ζ′(−1,3/4) = −ζ′(−1)/4,
ζ′(−1,1/4)−ζ′(−1,3/4) = G/(2π)  (from ζ(s,1/4)−ζ(s,3/4) = 4^s β(s), β(−1)=0),
ζ′(−1,1/3)−ζ′(−1,2/3) = (√3/4π) L(2,χ₋₃)  (Smyth's m(1+x+y))
```

[all verified ≤ 1e−50]. At `q ∈ {5,8,12,…}` even non-principal characters
appear and `L′(−1, χ even)` are genuinely new generalized-Glaisher atoms —
exactly the `φ(q) − 1` count of §3, split into the odd-χ atoms (`β′(2)`-class
at `s = 2`) and the even-χ atoms (Barnes-G-at-rationals / `ζ′(−1)`-class).

So the `γ₁′` atom inventory canonicalizes entirely to the `s = 2` layer —
one atom `L′(2,χ)` per non-principal χ plus `ζ′(2)` — with the `s = −1`
spellings reachable by exact, certificate-friendly `C_q`-conversions.

## 5. The reflection object is atom-bearing, not elementary

`W(x) = ∂_s[ζ(s,x) + ζ(s,1−x)]|_{s=2}`, the would-be reflection row,
satisfies (differentiating Hurwitz's formula through the zero-times-pole at
`s = 2`):

```
W(x) = π²(γ + ln 2π − 1)/sin²(πx) + 2π² · ∂_s E(s,x)|_{s=−1},
E(s,x) = Li_s(e^{2πix}) + Li_s(e^{−2πix}),   E(−1,x) = −1/(2 sin²πx)
```

[verified at irrational x (0.3, 1/√2) via Lerch derivatives, and at
rationals]. At `x = p/q` the `∂_s E(−1,·)` term decomposes into the even
sector of the atom inventory,

```
W(p/q) = (2q²/φ(q)) Σ_{χ even} χ̄(p) [ ln q · L(2,χ) + L′(2,χ) ],
```

e.g. `W(1/5) = (25/2) ln5 ζ(2) + 12 ζ′(2) + (25/2)[L′(2,χ₅) + ln5 L(2,χ₅)]`,
`W(2/5)` with the character part negated [verified 1e−80; their sum
reproduces the `q = 5` distribution row]. This is *why* the γ-level
reflection halving disappears under differentiation: the reflection row's
right-hand side already contains the even-χ atoms, so it pins nothing new.

## 6. The sporadic hunts

Protocol as in the companion γ-level report (PARI `lindep` at 420 digits;
candidate = small coefficients + residual at the precision floor; planted
positive control found exactly; random negative control rejected); script of
record [`../../tools/stieltjes-deriv-hunts.gp`](../../tools/stieltjes-deriv-hunts.gp).

**Structural must-hits (all HIT exactly, 16 bridges + the planted control):** the even bridge
(D = 5,8,12,13), the trivial-zero ratio `= 1/4` (D = −3,−4,−7,−8,−11), the
second-order odd bridge (D = −3,−7,−11), the q-independent second-order even
bridge (D = 5,8,12,13). Two basis-hygiene traps fired and were corrected:
the odd second-order bridge has coefficient ½ on the jet ratio (pre-summing
the two ratios hides it), and `{ln D, ln 2}` is ℚ-dependent at D = −4, −8
(spurious `ln 4 = 2 ln 2` hits) — the corpus's standing PSLQ-basis lessons,
verbatim.

**Open hunts (all negative):**

| hunt | atoms | dim | result | bound |
|---|---|---:|---|---|
| H1 | Glaisher dirs `rg(χ)`, even D ≤ 33 (10) + `ζ′(−1)/ζ(−1)`, γ, γ₁, logs, π² | 19 | **none** | ~10¹⁸ |
| H2 | `r₂(χ)`, odd D ≤ 24 (10) + `ζ′(2)/ζ(2)`, γ, γ₁, logs, π² | 18 | **none** | ~10¹⁹ |
| H3 | mixed parity + principal, post-bridge | 16 | **none** | ~10²¹ |
| H4 | `β′(2)` raw vs `G·{γ,ln2,lnπ,lnΓ(1/4)}`, `π²·{…}`, `ζ′(2)`, `ζ(3)`, `π³` | 15 | **none** | ~10²² |
| H5 | golden special: `rg(χ₅)` with `ln φ` products | 13 | **none** | ~10²⁶ |
| H6 | same χ across levels `s = 1, 2/−1` (with the Euler–Kronecker atom of the γ-level report) | 10 | **none** | ~10³⁴ |
| H7 | second s-derivative `L″(2,χ)/L(2,χ)`, χ ∈ {χ₅, χ₋₃, χ₋₄}, vs quadratics in lower atoms | 12 | **none** | ~10²⁸ |

In particular **`β′(2) = 0.08158073611659279510291216978594…` is a genuine
atom** (no reduction over the Catalan/lnΓ(1/4)/π-power basket below height
~10²²; no OEIS entry; equivalently `β′(2) = −(π/4)β″(−1) − (1−γ−ln(π/2))G`,
Bailey–Borwein Thm 4 territory — its trivial-zero sibling `β′(−1) = 2G/π` is
classical, but `β′(2)` itself is uncatalogued). The Glaisher directions of
distinct conductors are mutually independent at reachable heights, and no
relation crosses the three derivative levels `s = 1, 2, −1`.

## 7. Literature placement

From the dual literature pass (full read of the local PDF corpus under
`docs/pdfs`, plus a web/arXiv survey):

- **Master identity & derivative ladder — Coffey 2009** (arXiv:0905.1111,
  RMJM 44 (2014) 443–477): Prop. 1(ii) eq. (1.3) is our master identity;
  (1.4)–(1.5) give the s = 3, 4 levels; Cor. 2 (1.7) the all-orders
  Stirling-number ladder; Cor. 1 (1.6) the value `γ₁′(1)`. **Connon 2019**
  ("On some new formulae involving the Stieltjes constants") has the master
  identity independently plus the full `s = 0/1/2` antiderivative dictionary
  and the Deninger-`R` connection. Coffey 1402.3746 ("Functional equations
  for the Stieltjes constants") does the *argument-side* (non-derivative)
  functional equations. **None develops the rational-argument derivative
  landscape.**
- **The s = −1 / generalized-Glaisher layer — Miller–Adamchik 1998** (JCAM
  100, 201–206): functional equation → closed forms for `ζ′(−1, p/q)` at
  `q ∈ {2,3,4,6}`; re-derived and verified here. **Espinosa–Moll** (Ramanujan
  J. 6 (2002), Parts 1–2) organize log-Gamma/Hurwitz integrals around
  `A_k(q) = k ζ′(1−k,q)`. **Choi–Srivastava** give Barnes-G at rationals
  (`log G(1/4)` in `A`, `G`, `ζ′`). **Adamchik** (negative-order polygamma;
  log-integrals; Barnes function) supplies adjacent machinery.
- **The derivative-of-order viewpoint with both parities — Bailey–Borwein
  2016** ("Computation and structure of character polylogarithms", Math.
  Comp. 85, 295–324): character polylogs `L^{(m)}_{±d}(s)` with derivatives
  in the order; Thm 4 gives `L^{(m)}(1−2n)`, `L^{(m)}(2−2n)` for both
  parities — the FE family underlying our bridges. They note such sums "do
  not appear to have been studied in detail, and never with derivatives";
  their integer-relation tooling (with Crandall) is the nearest prior art to
  our hunt, but no `ζ′(2,p/q)`-lattice sweep is published.
- **Level-1 character coordinate — Murty–Pathak 2018** (Acta Arith. 184):
  `L′(1,f) = −Σ_a f(a) γ₁(a,q)` for odd f, with conditional transcendence of
  `≥ (p−7)/2` of `{γ₁(a,p)}`. **Our level-2 analogue
  `Σ_k χ(k) γ₁′(k/q) = q²[L′(2,χ)+(1+ln q)L(2,χ)]` appears nowhere in the
  literature.**
- **The Deninger ladder — Deninger 1984**; active **Dixit-school** program
  (Banerjee–Dixit–Gupta CJM 2023; Dixit–Sathyanarayana–Sharan, JMAA, on
  generalized-digamma `ψ_k` ≡ the level-0 argument-derivative tower). **No
  one has defined the level-2 Deninger function** (a normalized `R₂` with
  `R₂(x) − R₂(x+1) = ln x / x²`, which `ζ′(2,x)` satisfies up to
  normalization) or its modular/Kronecker-limit theory.
- **Frontier 2024–2026**: no paper touches `γ_n′(a)` or `ζ′(2,p/q)`. arXiv
  2506.10206 (in the corpus) is Hakimoglu-Brown, "Analytic Dilogarithm
  Identities" — relevant to the PolyLog `Li₂` store, not to this program.
- **Corpus papers carrying nothing on this layer** (recorded so the survey
  is falsifiable): Bailey 1997 (BBP), bbz7 (Borwein–Zucker–Boersma character
  Euler sums; atoms are log-sine/`Li₄(1/2)`), 9906134 (Bailey–Broadhurst
  17th-order ladder), Jameson, Lewin, Zagier, Kirillov 1995.

**Incidental erratum found during the corpus mine** (reported here only — the
PDF tree is under independent review and was not modified): Connon's printed
explicit `γ₁(1/5)` carries `[γ + log(2π)]` where it should read
`[γ + log(10π)]` (i.e. `log 2πq`, q = 5); the deficit is exactly
`−(√5/2) ln5 · ln φ`, and the corrected formula verifies to 0 at 50 dps. The
defect is in the source PDF text (not an OCR artifact).

## 8. What this means for the original question

1. **The linear identities connecting `γ_n′(p/q)` are: the distribution
   lattice (residual `φ(q) − 1` per grid, measured for `q ≤ 30`), the master
   identity (Coffey) tying the tower to the `s = 2` layers, the level-2
   character coordinate, and the exact `C_q`-bridges to the `s = −1`
   generalized-Glaisher layer.** All derivable, certificate-friendly,
   verified at 10⁻⁷⁸..10⁻¹³⁴.
2. **Structural novelty vs the underived case:** differentiation kills the
   reflection mechanism (the parity halving), doubles the atom count per grid
   (`φ(q)−1` vs `φ(q)/2−1`), and replaces the `lnΓ`/`ζ″(0,·)` layers by the
   `L′(2,χ)`/`ζ′(−1,·)` pair, which the FE makes interchangeable under one
   uniform constant.
3. **No sporadic relations** at reachable heights in any of seven atom
   families, including across derivative levels; `β′(2)` is a fresh,
   uncatalogued atom.
4. **What appears genuinely new here** (the survey's verdict): the
   rational-argument *landscape* — the rank theorem, the level-2 character
   coordinate, the first integer-relation sweep, and the observation that the
   level-2 Deninger function is unclaimed. The master identity and the FE
   machinery are Coffey's and the Miller–Adamchik/Bailey–Borwein tradition's.

## 9. Artifacts and reproduction

```powershell
Get-Content src/PolyLog/tools/stieltjes-deriv-hunts.gp | gp.exe -q -f   # hunt battery (~2 min)
uv run python src/PolyLog/tools/scratch/g1p_grid_rank.py                 # rank theorem
uv run --with mpmath python src/PolyLog/tools/stieltjes_master.py        # master id + gamma_2 + derivative rows
uv run --with mpmath python src/PolyLog/tools/scratch/s2_sm1_bridges_verify.py   # FE bridges, dual-engine
uv run --with mpmath python src/PolyLog/tools/scratch/lit_reductions_check.py    # the small-grid reductions
```

## 10. Follow-ups

1. **The Blagouchine-style theorem one level up**: an explicit closed-form
   table for `γ_n′(p/q)`, now within reach — the `q ∈ {1,2,3,4,6}` cases are
   fully elementary (master identity + the §4 reductions), and the general
   obstruction is precisely the catalogued odd atoms `L′(2,χ)` (β′(2)-class)
   and even atoms `L′(−1,χ)` (Barnes-G class). A natural short note,
   coordinate with the γ-level program.
2. **The level-2 Deninger function** `R₂` and its modular/Herglotz theory —
   apparently unclaimed; the real-quadratic frontier flagged in the γ-level
   report applies here too (Radchenko–Zagier at the derivative level).
3. The `∂_a^k` towers for `k ≥ 2` (`s = k+1` layers); same machinery,
   expect residual `φ(q) − 1` uniformly.
4. Promote the master identity, `C_q`-bridges, and rank rows into the
   identity stores as certificate-grade entries; extend
   `tools/stieltjes_master.py` (already carries the derivative master
   identity and distribution row, verified) toward the bridge certificates.
5. Higher precision under rigorous error control (Arb) for
   publication-grade exclusion bounds on `β′(2)` and the cross-conductor
   independence.
