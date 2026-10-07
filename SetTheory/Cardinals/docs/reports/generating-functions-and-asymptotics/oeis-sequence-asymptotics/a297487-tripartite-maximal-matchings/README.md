# Maximal Matchings of Complete Tripartite Graphs

**OEIS A297487 and the triangle boundary: the balanced counts to every fixed order, a parity-conditioned Poisson law for the unmatched vertices, rare maximum matchings and threshold brackets; unequal parts `K_{2n+d,n,n}` across the triangle inequality, with a uniform moving window, Gaussian laws, boundary corrections and an exterior Poisson law**

This is a research report built on 6 October 2026 (write batch 109) from two
manuscripts of one external research session, Reports 176 and 178 of the
session bundle of Reports 1–243, both dated 3 October 2026. Vertices are
labelled and the three parts distinguished; a matching is *maximal* if no edge
can be added, *maximum* if it has the most edges. A matching of a complete
multipartite graph is maximal exactly when its unmatched vertices lie in one
part, which makes every count a sum of factorial ratios, with exponential
generating function `(e^{vx} + e^{vy} + e^{vz} − 2) e^{xy+xz+yz}` (`v` marks
unmatched vertices).

- **Part I** (Report 176, the base): `A_n` = maximal matchings of `K_{n,n,n}`
  ([A297487](https://oeis.org/A297487), `A_0 = 1`). With `λ = √(n/2)` and
  `B_n = (n!)³/Γ(n/2+1)³`: an expansion of the marked counts to every fixed
  order, uniform for real `v` in compacts of `(0,∞)`, with a finite
  coefficient algorithm and `q_1,…,q_4`; `A_n = (3/2) B_n e^{λ−3/8}(Q_J(λ) +
  O(λ^{−J−1}))`, i.e. Kotěšovec's OEIS equivalent
  `A_n ~ 3√2 (2n/e)^{3n/2} e^{√(n/2)−3/8}` times
  `1 + 13/(96λ) − 119/(18432λ²) − 4575127/(26542080λ³) + 1879441301/(10192158720λ⁴) + O(λ⁻⁵)`;
  the unmatched count `U_n` of a uniform maximal matching is within
  `O(n^{−1/4})` in total variation of a Poisson(`λ`) law conditioned on the
  parity of `n`, with `E U_n = λ − 3/4 + …`, `Var U_n = λ − 3/2 + …`, a CLT and
  a span-two local law; the probability of a maximum matching to every fixed
  relative order; a two-ceiling bracket for `min{n : A_n ≥ y}` and a
  Lambert-W approximation of the smooth inverse.
- **Part II** (Report 178): unequal parts. For compact sets of strictly
  triangular proportions, the three unmatched-part branches to leading order
  and a softmax law for the unmatched part near balance. For `K_{2n+d,n,n}`
  across the face `a = b + c` of the triangle inequality, with `N = n^{1/3}`:
  an expansion to every fixed order in `N^{−1}`, uniform for `d/N²` in a compact
  interval, with exponential suppression of the other branches; Gaussian
  moments, local, total-variation and Kolmogorov laws at scale `N`; for the
  boundary counts `M(2n,n,n) = (2n)! Z_n` (1, 3, 74, 4506, 489240, …; no OEIS
  entry), four corrections in `ℚ(a)`, `a = 4^{−1/3}`, `log M(2n,n,n)`, moments, a
  doubling lemma and a two-ceiling bracket; and, for `d/n` in a compact subset of
  `(0,∞)`, an all-orders Poisson expansion with the edge deficit tending to
  Poisson(`c⁻²`).
- **Added by the write**: the front matter (guide, status table, the OEIS
  entry quoted and its b-file checked, what Part II settles of Part I's
  question, the inverses against the transseries volume, notation,
  provenance, checks, neighbours); reading-conventions tables; dated notes;
  Section 26 (further questions).

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Maximal Matchings in Balanced Complete Tripartite Graphs: All fixed order asymptotics, unmatched vertices, and inverse thresholds* (author line "Research report 176", 3 October 2026); the base | 176 | `Tripartite_Maximal_Matchings_Asymptotics_and_Inverses_Source.zip` (550,292 bytes, 20 files; `report.tex`, 628 lines, 14 pp.) | none named (catalogue read as of `ca62e1488`) | `f7e9e5c2f` | Part I, Sections 1–11 |
| *Maximal Matchings Across the Triangle Boundary: Boundary asymptotics, a uniform moving window, and an exterior Poisson law* (author line "Research report 178", 3 October 2026) | 178 | `Unequal_Tripartite_Matchings_Transitions_and_Inverses_Source.zip` (633,432 bytes, 31 files; `Report178.tex`, 755 lines, 19 pp.) | none | `f7e9e5c2f` | Part II, Sections 12–25, plus the write's Section 26 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research archives
from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `f7e9e5c2f` (batch 109, cluster 109-TRIP) removed them from
`docs/incoming/`. The write is "Write batch 109
(a297487-tripartite-maximal-matchings): new report, maximal matchings of
complete tripartite graphs".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names a person, a tool or an addressee, or
carries "prepared for private review" wording; the PDF author fields read
"Research report 176" and "Research report 178". Every result, proof, remark,
question and limitation of both manuscripts is printed.

## Why the Parts are in this order

The base is Report 176; its `report.tex` was staged as `article.tex`, and it is
printed first, as Part I. It is the report on A297487, it defines the objects
and the method both use, and it is the predecessor: Report 178 says it continues
"the balanced `K_{n,n,n}` analysis of Report 176", cites it, and takes its
generating function, maximality lemma and gamma–Poisson method. The two prove
different theorems: Part II's strict-triangle Theorem 14.1 covers the balanced
case only to leading order (relative error `O(n^{−1/2})`), where Part I is
all-order, and Part II's other results concern `K_{2n+d,n,n}`. Report 178 is
Part II. The manuscripts were written about an hour apart (INDEX times 17:30
and 18:29 UTC); they share about 2–3 % of their 8-grams (intake measurement).

## Files

The directory holds 45 files: 8 at the root, 16 in `code/`, 21 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 176, prefix `176-balanced-`** (16 files): the code guide and the
source audit; `code/`: the exact verifier, the certificate regenerator, the
corruption guards, the deterministic PDF/ZIP builder and its tests, and the
manifest checker; `data/`: the exact certificate, the verifier and guard
receipts, the build information and guard receipts, and the frozen independent
symbolic reference.

```
176-balanced-README_CODE.md
176-balanced-SOURCES.md
code/176-balanced-build.py
code/176-balanced-guard_tests.py
code/176-balanced-regenerate.py
code/176-balanced-test_build.py
code/176-balanced-verify.py
code/176-balanced-verify_manifest.py
data/176-balanced-data-certificates.json
data/176-balanced-data-guard_results.json
data/176-balanced-data-verified_results.json
data/176-balanced-generated-BUILD_INFO.json
data/176-balanced-generated-build_guards.json
data/176-balanced-generated-verification.json
data/176-balanced-generated-verification_guards.json
data/176-balanced-references-independent_results.json
```

`data/176-balanced-data-verified_results.json` and
`data/176-balanced-generated-verification.json` are byte-identical, as are
`data/176-balanced-data-guard_results.json` and
`data/176-balanced-generated-verification_guards.json` (distinct delivered
records, staged as delivered).

**Report 178, prefix `178-boundary-`** (26 files): the code guide, the source
audit and the guide to the optional audits; `code/`: the exact core (verifier,
regenerator), guards, builder and build tests, and five optional SymPy/mpmath
audit programs; `data/`: the exact certificate, the verifier/guard/build
receipts, and the recorded outputs of the optional audits.

```
178-boundary-README_CODE.md
178-boundary-SOURCE_AUDIT.md
178-boundary-optional-README.md
code/178-boundary-build.py
code/178-boundary-code-regenerate.py
code/178-boundary-code-verify.py
code/178-boundary-guard_tests.py
code/178-boundary-optional-boundary-check.py
code/178-boundary-optional-boundary-derive.py
code/178-boundary-optional-window-check.py
code/178-boundary-optional-window-derive.py
code/178-boundary-optional-window-exterior_check.py
code/178-boundary-test_build.py
data/178-boundary-data-certificates.json
data/178-boundary-generated-BUILD_INFO.json
data/178-boundary-generated-build_guards.json
data/178-boundary-generated-verification.json
data/178-boundary-generated-verification_guards.json
data/178-boundary-optional-boundary-coefficients.txt
data/178-boundary-optional-boundary-coefficients_order6.txt
data/178-boundary-optional-boundary-diagnostics.json
data/178-boundary-optional-boundary-exact_counts.json
data/178-boundary-optional-window-coefficients.txt
data/178-boundary-optional-window-diagnostics.json
data/178-boundary-optional-window-exterior_diagnostics.json
data/178-boundary-optional-window-integer_checks.json
```

Report 178's `verify_manifest.py` is byte-identical to Report 176's (5006
bytes, blob `ed00651e1`; the same generic helper is in
`a089479-fixed-permanent-matrices` and `a271619-strict-twice-partitions`); it is
shipped once, as `code/176-balanced-verify_manifest.py`.

## Labels and numbering

Label prefix **`tmm:`** (none at HEAD before this report): Part I uses
`tmm:bal:` (Report 176's 78 labels), Part II `tmm:bd:` (Report 178's 86).
Nine bare names occur in both manuscripts (`eq:D`, `eq:egf`, `eq:mu`,
`lem:maximal`, `lem:monotone`, `sec:exact`, `sec:inverse`, `sec:sources`,
`sec:verification`); under the Part prefixes they are distinct. The write added
the two Part labels `tmm:bal:part`, `tmm:bd:part`; labels for Part I's
unlabelled Section 1 and Subsection 11.2, `tmm:bal:sec:convention` and
`tmm:bal:sec:questions`; the front matter's `tmm:sec:guide`, `…:status`,
`…:oeis`, `…:sequel`, `…:inverses`, `…:notation`, `…:provenance`, `…:trust`,
`…:neighbours`; and Section 26's `tmm:sec:further` with the twelve items
`tmm:q:parity`, `tmm:q:marking`, `tmm:q:complex`, `tmm:q:effective`,
`tmm:q:unequal`, `tmm:q:overlap`, `tmm:q:degenerate`, `tmm:q:tails`,
`tmm:q:reversion`, `tmm:q:identity`, `tmm:q:diagnostics`, `tmm:q:literature`.
190 labels in all, all distinct (164 delivered, 26 added).

| Part | Manuscript | Section here | Statements | Equations |
|---|---|---|---|---|
| I | Report 176 | `k` (1–11, unchanged) | `k.j`, unchanged | (1)–(57), unchanged |
| II | Report 178 | `k + 11` (12–25); 26 added | `(k + 11).j` | `(k)` → `(k + 57)`: (58)–(120) |

Both manuscripts number statements within sections and equations
continuously. Report 178's Lemma 2.1 → **13.1**, Theorem 3.1 → **14.1**,
Corollary 3.2 → **14.2**, Theorem 4.1 → **15.1**, Theorem 8.1 → **19.1**,
Corollary 9.1 → **20.1**, Lemma 10.1 → **21.1**, Theorem 10.2 → **21.2**,
Theorem 11.1 → **22.1**; its equation (1) is (58) and its last, (63), is (120).
A comparison of the build's `.aux` with separate builds of the two delivered
`.tex` files confirmed all 164 delivered labels under these offsets and
prefixes. The delivered guides, code and data use the manuscripts' own numbers.

Bibliography: the key `dlmf` is used by both manuscripts for different DLMF
sections; Report 176's (§5.11, §24.2) keeps `dlmf`, Report 178's (§16.11) is
`dlmf16`. Report 178's `r176` is kept, with a note that it is Part I. `oeis`,
`song`, `azor` and `paris` are merged, keeping both Parts' annotations.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`A_n`** is A297487 in Part I but the boundary count `M(2n,n,n)` in
Part II; **`λ`** is `√(n/2)` in Part I, the branch means `λ_i` and later `c⁻²`
in Part II; **`J`** is a truncation order in Part I and the random edge count
between the two small parts in Part II; **`t(n,k)`** (by unmatched vertices)
against **`t(n,d,j)`** (by edges); **`v`** is Part I's marking variable and
Part II's Gaussian variance (Part II marks with `w`); **`d`** is Part I's
Stirling polynomials `d_j` and Part II's imbalance; **`a`** (`q_j(1)`, the
marking compact `[a,b]`; `4^{−1/3}`, edge populations `a_i`), **`q`**, **`B`**,
**`h`**, **`G`**, **`H`**, **`N`** (Part I's threshold `N(y)`; Part II's `n^{1/3}`,
whose threshold is `H_*(y)`), **`R`**, **`C`**, **`D`**, **`P`**, **`K`**,
**`x`/`X`**. The transseries volume's symbols are subscripted `vol`
(`κ_vol`, `d_vol`, `v_vol`, `X_vol`, `L_vol`, `Φ_vol`, `ϱ_vol`). Same in both
Parts: `U` (unmatched count), `E`, `P`, `Var`, `Poisson`, `d_TV`, `ψ`, `B_{2m}`,
`W`.

## What the report claims

**Part I (Report 176).**
- Lemma 2.1 (maximal ⇔ unmatched vertices in one part), the counts (3),
  `A_n(v) = 3S_n(v) − 2[2|n]B_n` (5), the EGF (6): classical and elementary;
  Howroyd's program and Kotěšovec's equivalent are credited.
- Lemma 3.1: `0 < R_n(k) ≤ e²` and the Poisson representation.
- Theorem 4.1: the marked expansion (18), uniform for real `v` in compacts of
  `(0,∞)`, every fixed order, rational `q_j` of degree ≤ `3j` and parity `j`,
  with the coefficient algorithm (19); Remark 4.2: the parity sector is not
  identified.
- Corollary 5.1: (27), the four corrections to the OEIS equivalent and
  `log A_n` (29).
- Theorem 6.1: `E U_n = λ − 3/4 + 21/(32λ) − 9/(32λ²) + O(λ⁻³)`,
  `Var U_n = λ − 3/2 + 71/(32λ) − 41/(16λ²) + O(λ⁻³)`.
- Theorem 7.1: total variation `O(n^{−1/4})` to the parity-conditioned
  Poisson law, CLT, span-two local law; the gap from maximum size.
- Theorem 8.1: maximum-matching probabilities to every fixed relative order,
  `R_n(1)` expanded.
- Lemma 9.1, Theorem 9.2 (two-ceiling bracket), Theorem 9.3 (Lambert-W
  approximation with `o(1)` error).

**Part II (Report 178).**
- Lemma 13.1 (= Part I's Lemma 2.1), the EGF (58), the branch terms (59); the
  large-part branch (60)–(63); the boundary formula (64); the identities
  `Z_n = ₂F₂(−n,−n; ½,1; ¼)` and `M(2n,n,n) = E[He_{2n}(X+1) He_n(X)²]` (65),
  "a classical generating-function consequence, not a claim of a new Hermite
  formula".
- Theorem 14.1 (strict triangle, leading order) and Corollary 14.2 (softmax).
- Theorem 15.1 (compact moving window, every fixed order, suppression (75));
  Sections 16–18 (suppression, coefficient algorithm, localization and
  remainder); (94)–(95) and Theorem 19.1 (window corrections, moments, local,
  TV and Kolmogorov laws).
- Corollary 20.1: `M(2n,n,n) = (2n)! e^{3aN² − a²N + 1/12}/(√(12πa) N)·(1 +
  Σ c_k N^{−k})`, `c_1 = 211a/216`, `c_2 = 172781a²/466560`,
  `c_3 = −189855337/1209323520`, `c_4 = −6247138084769a/36569943244800`;
  `log M(2n,n,n)` (107); boundary moments; maximum matchings (110).
- Lemma 21.1 (`M(2n+2,n+1,n+1) ≥ 2M(2n,n,n)`), Theorem 21.2 (bracket), the
  Lambert initializer and its leading displacement.
- Theorem 22.1 (exterior, all orders, `κ_1 = −(c⁻⁴ + 2c⁻⁵ + 3c⁻³)`, TV
  `O(n⁻¹)` to Poisson(`c⁻²`)); Section 23 (regimes).

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter; reading-conventions tables; dated notes; Section 26; and these short
proofs: Howroyd's PARI program is (5) at `v = 1` term by term (its summand `k`
is `3t(n, n − 2k)`); Kotěšovec's formula equals (1); Part II's Theorem 14.1 and
Corollary 14.2 at `p_1 = p_2 = p_3 = n` give Part I's leading term and CLT
(`a_i = n/2`, `B = B_n`, `λ_i = λ`, `C_i = 3/8`); and the classification of the
inverses (below).

## The OEIS entry, and the boundary sequence

[A297487](https://oeis.org/A297487) (read 6 October 2026; revision #18 of
6 February 2026): "Number of maximal matchings in the complete tripartite graph
K_{n,n,n}." Author Eric W. Weisstein (30 December 2017); terms from `a(6)` on,
the b-file `n = 1..100` and the PARI program by Andrew Howroyd (30 December
2017); offset 1; Kotěšovec's order-five recurrence and
`a(n) ~ 3 * 2^((3*n+1)/2) * exp(sqrt(n/2) - 3*n/2 - 3/8) * n^(3*n/2)`
(6 February 2026); an unattributed Mathematica line with `HypergeometricPFQ`
and the even perfect-matching subtraction. Part I checked the 16 displayed
terms and did not retrieve the b-file; **the write compared all 100 b-file terms
with Part I's exact counts: all agree.** The write also recomputed Part I's
displayed `A_0…A_8` and Part II's displayed `M(2n,n,n)`, `n ≤ 10`, by
coefficient extraction from the generating function.

The boundary sequence `M(2n,n,n)` is not A297487. Part II found no OEIS entry;
the write's searches (6 October 2026) for `74,4506,489240,82306920` and
`4506,489240,82306920,19743705360` returned "No results". **Nothing was
submitted to the OEIS.**

## Part II and the question of Part I

Part I's question 5: "**Unequal parts and more parts.** For K_{a,b,c} or a
growing number of parts, identify the feasibility boundaries and competing
unmatched-part contributions." For `K_{p_1,p_2,p_3}` a branch other than `i`
(unmatched vertices in another part) is feasible only if `p_i ≤ p_j + p_ℓ`, so
the feasibility boundaries are the faces of the triangle inequality. Part II's
`K_{2n+d,n,n}` is literally a `K_{a,b,c}` and `d = 0` is the face `a = b + c`:
**Part II settles one instance of the unequal-parts half** (all fixed orders in
the window `d/n^{2/3}` compact, suppression of the competing branches, the
exterior `d/n` compact), and **advances** the general three-part case (Theorem
14.1: competing contributions for compact strictly triangular proportions, to
leading order only). Open: more parts; faces with unequal small parts and
several comparable branches near a degenerating triangle; uniformity as
`d/n^{2/3} → ±∞`; higher orders in the strict triangle (Section 26, items 5–7).

## The inverses and the transseries volume

(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.)
Instances of the factorial core `p0:prop:factorial-core`: Part I's `x_0 =
2ℓ/(3w)`, `w = W(4ℓ/(3e))` (`κ_vol = 3/2`, `d_vol = (3/2)(log 2 − 1)`,
`v_vol = w`, slope `(3/2)(w + 1)` = Part I's `D`), and Part II's `x_0 = log y /
(2W(log y / e))` (`κ_vol = 2`, `d_vol = 2(log 2 − 1)`, slope `2 log(2x_0)`).
Analogues: Part I's corrections `−(λ_0 + C)/D + 1/(4D²) − 3/(8D³)` are the
terms `m = 1, 2` of `p0:eq:operator-series` (`p0:prop:operator-form`) with
`ϱ_vol = g = √(x/2) + C`, and Part II's displacement `−3a x_0^{2/3}/(2 log(2x_0))`
is its term `m = 1` with `ϱ_vol = 3a x^{2/3}`; the error bounds are the Parts'
own. Not instances: the two-ceiling brackets (Theorems 9.2 and 21.2), proved
directly at the integers without an interpolation; when the ceilings agree they
reach the conclusion of `p0:thm:staircase` (2).

## What the report does not claim

Every limitation is printed in place. In short: the maximality lemma, the
generating function, Howroyd's sum, Kotěšovec's equivalent and the Hermite /
hypergeometric identities are prior or classical, as the manuscripts say; Paris
(2010) already has the all-order expansion for the nearby four-equal-Hermite
(perfect-matching) problem; neither Part makes a worldwide priority claim
(bounded searches of 3 October 2026; the Song, Azor and Luke full texts were not
obtained). **Part I**: fixed algebraic orders only (no convergent series); real
`v` in compacts of `(0,∞)` only; no complex-`v` theorem; no exponentially
accurate count parity sector; existential constants and onsets; no
unconditional rounding rule. **Part II**: no OEIS identifier, no new Hermite
formula, no global novelty, no effective constants, no unconditional rounding
rule, no uniform matching as `|d|/n^{2/3} → ∞`, Theorem 14.1 leading order only
and no estimate as a triangle degenerates; the high-precision diagnostics are
not outward-rounded. **Both packages**: finite exact checks prove no asymptotic
statement; manifests detect changes and authenticate nothing.

## Further questions, and the standing rule

Section 26 collects (Vladimir's standing rule of 4 October 2026), with sources,
sketches and what is missing:

1. the parity sector of the balanced count (Part I);
2. marking regimes `v → 0, ∞` (Part I);
3. complex marking, Edgeworth terms (Part I; Part II likewise);
4. effective constants, onsets, certified thresholds (both);
5. unequal parts and more parts (Part I's question 5, **re-scoped**: one
   instance settled by Part II);
6. a uniform overlap between the regimes (Part II);
7. unequal small parts near a degenerating triangle (Part II);
8. sharper tails (Part II);
9. a complete reversion for the inverses (Parts I, II);
10. the boundary sequence's OEIS identity and the unread full texts (Part II;
    still no OEIS entry);
11. uncertified numerics (Part II's diagnostics; Part I's reference; the
    sources of its two quotations corrected after the independent check of
    7 October 2026: "not outward-rounded" is Part II's package wording, in
    `178-boundary-optional-README.md`, and "read without executing code" is
    from Report 176's delivered, unshipped `README.md`, not from the cited
    sections);
12. literature and priority.

**Re-scoped**: Part I's question 5. **Superseded, sentence kept** (dated note):
Part I's "The remote b-file was not retrieved" (the write compared all 100
terms). No claim of either manuscript was found wrong; no published result is
corrected.

## Independent check of the write (7 October 2026)

An adversarial check made by the intake after the write (`8dacae7a7`), with
its own code, after fetching A297487 (revision #18) and its b-file again.

- **Counts**: a brute-force enumeration of maximal matchings, independent of
  every formula, gives `A_0, …, A_3`, `M(2n,n,n)` for `n ≤ 3` and
  `M(4+d,2,2)`, `−2 ≤ d ≤ 3`; (5) agrees with Howroyd's program (`n ≤ 100`),
  the entry's Mathematica line (`n ≤ 40`), EGF extraction (`n ≤ 8`), the
  certificate and all 100 b-file terms; Howroyd's summand `k` equals
  `3t(n, n−2k)` exactly for `n ≤ 60`; the boundary prefix reproduced. The OEIS
  again matches nothing for the boundary prefix (today's wording: "Sorry, but
  the terms do not match anything in the table").
- **Part II and Part I's question**: the edge populations satisfy the degree
  equations; enumeration shows a single branch outside the triangle and on the
  face (plus perfect matchings there), three inside.
- **Balance, boundary coefficients, inverses**: the specializations
  (`λ_i = λ`, `C_i = 3/8`, the softmax expansion), `c_1(2a) = 211a/216`, the
  four `ℓ_k`, `−83/648`, and the factorial-core and operator-series identities
  re-derived; the exact `log M(2n,n,n)` at `n = 500, …, 4000` matches (107)
  through `n^{−4/3}` to below `10^{−3} n^{−5/3}`.
- **Provenance**: archive sizes, counts, index times, the catalogue blobs and
  the shared `verify_manifest.py` blob confirmed (that blob is now also in
  `a262810-diagonal-alignments` and `a328716-lazy-closed-walks`).
- **One defect**: Section 26, item 11 attributed two quotations to sections
  that do not contain them; sources corrected with a dated note.

Both delivered verifiers still pass against the corrected `article.tex` (on a
copy, shipped names). The check is recorded at the end of Section 26.

## Relation to neighbouring reports

- No other placed report treats A297487, maximal matchings of complete
  multipartite graphs, or `K_{2n+d,n,n}` (searched 6 October 2026);
  `log-concavity-and-unimodality/matching-rank-normalization` and
  `enumerative-combinatorics/preorder-root-polytopes` use "matching" for
  unrelated objects.
- The transseries volume, for the inverses (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file treats matchings of complete
multipartite graphs (searched 6 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 42 staged code, data and guide files
  were checked against the pristine extraction at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files). Only
  names changed (tables at the end).
- **Nothing should be run in this directory.** The programs are written for the
  delivered layouts (`verify.py`, `data/…`, `references/…`, `report.tex` for
  Report 176; `code/verify.py`, `data/…`, `Report178.tex`, `optional/…` for
  Report 178). The two exact verifiers accept explicit paths and work on a copy
  of this directory under the shipped names, against this merged `article.tex`
  (whose two verification markers are kept unchanged): see "Rerunning the
  checks". The regenerators import `verify` by its delivered name, and the
  guards, builders and build tests expect the delivered layout and files that
  are not shipped (`report.tex`, `Report178.tex`, `SHA256SUMS.json`, the delivered
  READMEs); rerun them from the archives.
- The shipped guides use delivery names: `176-balanced-README_CODE.md` (`report.tex`,
  `SOURCES.md`, `references/…`), `178-boundary-README_CODE.md` (`code/verify.py`,
  `optional/boundary/coefficients_order6.txt`), `178-boundary-optional-README.md`
  (`optional/…`, `--output-dir ../…`), `178-boundary-SOURCE_AUDIT.md`
  (`Report176`). The JSON receipts name delivered paths.
- `176-balanced-SOURCES.md` cites the collection's `manifest.tex` and `README.md`
  by blob (`9b13df17…`, `398c8bff…`): those are the versions of `ca62e1488` (2
  October 2026), replaced by `7969f7168` (3 October, 09:49 Pacific). It also
  reports that Paris discusses corrections to an older printed four-Hermite
  formula; that is Paris's correction, not checked by the intake or the write.
- Report 178's delivered README (not shipped) says that "the authoring source
  directory … has no manifest"; the archive does contain `SHA256SUMS.json`
  (30 entries, all verified at intake; not shipped).
- **Windows hazard:** Report 178's `guard_tests.py` fails on Windows ("GUARD
  TEST FAILED: regenerated bytes differ"): `regenerate.py` writes in text mode,
  so Windows writes CRLF, and the guard compares raw bytes with the LF
  certificate. The regenerated certificate equals `data/certificates.json` after
  removing carriage returns. Platform-only, not mathematical; run the guards on a
  POSIX host. On Windows the verifiers also write CRLF to a redirected standard
  output; compare after removing carriage returns.
- Layout only: in Part II's regime table (Section 23) the columns are set
  ragged-right, to avoid underfull lines; the running heads name the Part; the
  table-of-contents section style is Report 176's.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. The quickest
route uses the shipped names (copy this directory first; Report 178's verifier
refuses relative paths containing `..`, so pass absolute paths):

```
cp -r a297487-tripartite-maximal-matchings /tmp/tmm && cd /tmp/tmm
python -B code/176-balanced-verify.py --data data/176-balanced-data-certificates.json \
  --reference data/176-balanced-references-independent_results.json \
  --manuscript article.tex | tr -d '\r' | cmp - data/176-balanced-data-verified_results.json
python -B code/178-boundary-code-verify.py --data "$PWD/data/178-boundary-data-certificates.json" \
  --manuscript "$PWD/article.tex" | tr -d '\r' | cmp - data/178-boundary-generated-verification.json
```

Both passed at the write (6 October 2026, Python 3.14.4, Windows), byte for
byte after removing carriage returns. For the full suites, recreate the
delivered layouts from the arrival commit (both archives are flat):

```
git show 60f54ea06:docs/incoming/Tripartite_Maximal_Matchings_Asymptotics_and_Inverses_Source.zip > r176.zip
git show 60f54ea06:docs/incoming/Unequal_Tripartite_Matchings_Transitions_and_Inverses_Source.zip > r178.zip
mkdir x176 x178 && unzip -q r176.zip -d x176 && unzip -q r178.zip -d x178
cd x176
python -B verify_manifest.py
python -B verify.py | tr -d '\r' | cmp - data/verified_results.json
python -B -O verify.py | tr -d '\r' | cmp - data/verified_results.json
python -B guard_tests.py | tr -d '\r' | cmp - data/guard_results.json
python -B regenerate.py --compare data/certificates.json
cd ../x178
python -B verify_manifest.py
python -B code/verify.py | tr -d '\r' | cmp - generated/verification.json
python -B -O code/verify.py | tr -d '\r' | cmp - generated/verification.json
python -B code/regenerate.py --compare data/certificates.json --output ../new-certificate.json
python -B guard_tests.py        # POSIX only (see the Windows hazard above)
python -B optional/boundary/derive.py --order 4   # needs SymPy (recorded: 1.14.0)
python -B optional/window/derive.py               # needs SymPy
```

Standard library only for the exact cores; Python 3.10 or later. At placement
(dossier of batch 109, 6 October 2026, Python 3.14.4, Windows, on copies):
Report 176's manifest check passed (19 files), `verify.py` in normal and `-O`
mode reproduced `data/verified_results.json`, `guard_tests.py` reproduced
`data/guard_results.json`, and `regenerate.py --compare` passed (about 23 s
in all); Report 178's manifest check passed (30 files), `code/verify.py` in both
modes reproduced `generated/verification.json`, `regenerate.py` passed and wrote
a certificate equal to `data/certificates.json` up to CRLF, `guard_tests.py`
failed only by the Windows hazard, and the two SymPy `derive.py` runs reproduced
their `coefficients.txt` exactly. The mpmath `check.py` diagnostics (long; not
proof) and the PDF/ZIP builders were not rerun.

## Rights

Repository contents are MIT-0. OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)): Report 176's certificate
(`data/176-balanced-data-certificates.json`, field `source`) and verifier
(`code/176-balanced-verify.py`) contain the 16 displayed terms of A297487; the
other 85 counts are computed. The boundary counts are computed (no OEIS entry).
No paper PDF is shipped. Credited: the OEIS entry (Eric W. Weisstein, Andrew
Howroyd, Václav Kotěšovec) for the sequence, the positive sum and the leading
equivalent; Azor–Gillis–Victor and Paris for the Hermite-pairing framework;
Hang–Luo and the DLMF for the hypergeometric comparison. Nothing was submitted
to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy of `article.tex` (no other inputs);
commit only `article.pdf`. The build (46 pages at the write; 47 after the
independent check of 7 October 2026, label numbers unchanged, aux files
compared): no errors, no undefined or
multiply defined references or citations, no duplicate destinations, no
overfull or underfull boxes, no warnings. The log carries one "Infinite glue
shrinkage found in box being split" message, from the notation longtable
breaking across pages. The two delivered `.tex` files compile with MiKTeX
pdfLaTeX to 14 and 19 pages; Report 178's has one underfull box, in its regime
table (removed here by the ragged-right columns).

## Delivered path → shipped path

Report 176 (`176-balanced-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `report.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `README_CODE.md`, `SOURCES.md` | `176-balanced-<name>` |
| `build.py`, `guard_tests.py`, `regenerate.py`, `test_build.py`, `verify.py`, `verify_manifest.py` | `code/176-balanced-<name>` |
| `data/<name>.json` | `data/176-balanced-data-<name>.json` |
| `generated/<name>.json` | `data/176-balanced-generated-<name>.json` |
| `references/independent_results.json` | `data/176-balanced-references-independent_results.json` |
| `Report176.pdf`, `SHA256SUMS.json` | not shipped |

Report 178 (`178-boundary-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report178.tex` | not shipped; printed as Part II of `article.tex` |
| `README_CODE.md`, `SOURCE_AUDIT.md` | `178-boundary-<name>` |
| `optional/README.md` | `178-boundary-optional-README.md` |
| `build.py`, `guard_tests.py`, `test_build.py` | `code/178-boundary-<name>` |
| `code/regenerate.py`, `code/verify.py` | `code/178-boundary-code-<name>` |
| `optional/<dir>/<name>.py` | `code/178-boundary-optional-<dir>-<name>.py` |
| `data/certificates.json` | `data/178-boundary-data-certificates.json` |
| `generated/<name>.json` | `data/178-boundary-generated-<name>.json` |
| `optional/<dir>/<name>` (outputs) | `data/178-boundary-optional-<dir>-<name>` |
| `verify_manifest.py` | not shipped (byte-identical to `code/176-balanced-verify_manifest.py`) |
| `README.md`, `Report178.pdf`, `SHA256SUMS.json` | not shipped |

## Provenance

Two manuscripts (bundle Reports 176, 178) → one report; base 176, printed as
Part I. Arrival `60f54ea06`, placement `f7e9e5c2f`, write batch 109 (6 October
2026). No manuscript pins a commit (Report 176 read the catalogue as of
`ca62e1488`). Merge choices (base first; the repeated lemma and generating
function printed in both Parts with pointers; Part II's sections offset by 11
and equations by 57; the merged bibliography with Part II's `dlmf` renamed
`dlmf16`) are listed in the article's front matter, "Provenance and merge
decisions".
