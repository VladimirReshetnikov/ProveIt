# Inversion Sequences Avoiding 100, 101, 201

**OEIS A279571 as a two-colour cone walk: the leading equivalent `a_n ~ C_A 9ⁿ n^{−κ}`, the exponent `κ = 1 + π/arccos(2/√7)`, a threshold inverse and non-D-finiteness**

This is a research report built on 5 October 2026 (write batch 104) from two
manuscripts of one external research session, Reports 123 and 125 of the
session bundle of Reports 1–243, both dated 2 October 2026. Both treat
Britt and Beaton's Class 2106: inversion sequences `e`, `0 ≤ e_i < i`, with no
indices `i < j < k` such that `e_i > e_j`, `e_j ≤ e_k`, `e_i ≥ e_k` (the
patterns 100, 101 and 201), counted by OEIS
[A279571](https://oeis.org/A279571) (`1, 1, 2, 6, 22, 92, 424, 2106, 11102, …`).
A positive change of weights turns Britt and Beaton's generating tree into a
centred Markov-additive walk with two colours `P, Q` and unbounded steps in
the quadrant; its effective covariance `Σ = [[7/3, −10/3], [−10/3, 25/3]]`
gives the wedge angle `θ = arccos(2/√7)` and the irrational exponent
`p = π/θ ∈ (4, 5)`. Throughout `κ = 1 + p = 5.4016888679…`.

- **Part I** (Report 125, the base): `a_n ~ C_A 9ⁿ n^{−κ}` with `0 < C_A < ∞`,
  `C_A` characterized by normalized forward and reversed killed harmonic
  functions `V`, `V*` and a positive endpoint series; a killed local limit
  theorem at every fixed pair of states; a threshold inverse with explicit
  real centre `v(y)` and a ceiling bracket of vanishing width; `1/9` the only
  singularity on the circle of convergence; the generating function is not
  D-finite over `ℂ(z)`.
- **Part II** (Report 123): the weaker law `a_n = 9ⁿ n^{−κ+o(1)}` by a
  different route (martingale functional limit theorem, geometric annuli,
  exact-time gluing), the inverse with error `o(log log y)`, and the
  functional equations, kernel and discriminant of the generating tree,
  which Part I does not have. Report 123 is the earlier proof of the
  exponent, of the circle statement and of non-D-finiteness.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *A279571: the leading equivalent. A positive harmonic constant and a sharp threshold inverse* (title block "REPORT 125 … Standalone proof and exact finite-check companion"; no author line); the base | 125 | `A279571_Leading_Equivalent_and_Harmonic_Constant_Source.zip` (952,684 bytes, 29 files; `report125.tex`, 1,575 lines, 25 pp.; archive created 15:12:25 UTC) | none | `612787fb4` | Part I, Sections 1–14 as delivered, plus the write's Section 14.1 |
| *A279571 exact logarithmic exponent. Unique dominant singularity and non D finiteness* (title block "REPORT 123 … Standalone proof and exact finite check companion"; no author line) | 123 | `A279571_Exact_Asymptotic_Exponent_and_Non_D_Finiteness_Source.zip` (887,643 bytes, 23 files; `report123.tex`, 979 lines, 16 pp.; archive created 14:23:20 UTC) | none | `612787fb4` | Part II, Sections 15–25 (its shared blocks as pointers), plus the write's Sections 26–27 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `612787fb4` (batch 104, cluster 104-INV, subfamily A279571) removed
them from `docs/incoming/`. The write is batch 104's "Write batch 104
(a279571-inversion-cone-walk): new report, the 9^n n^-kappa cone walk of
A279571".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee,
says it is AI-assisted, or carries "prepared for private review" wording;
both set an empty PDF author field. Every result, proof, remark, question
and limitation of the two manuscripts is printed. The text that the two
share word for word (Report 123's Sections 2.1, 3.1, 3.2, 4.2, 8 and 9 =
Report 125's Sections 2.1, 3.1, 3.2, 9.1, 12 and 13; about two fifths of
Report 123) is printed once, in Part I.

## Why this order

Report 125 is the base and comes first although it is the later manuscript
(49 minutes): its Theorem 1.1 and Corollaries 1.2 and 12.1 imply every
statement of Report 123's Theorem 1.1 under the same hypotheses, and it
proves the leading equivalent where Report 123 proves only the logarithmic
law. Report 123 is printed in full as Part II because its proof is a
genuinely different, weaker second route (it needs only Whitt's martingale
FCLT as probabilistic import, where Part I needs Bashtova–Shashkin's strong
approximation and Bañuelos–Smits' wedge kernel), because it alone has the
functional equations and kernel of the generating tree (its Section 2.2,
here 16.2), and because it keeps priority within the bundle for the
exponent, the circle statement and non-D-finiteness.

## Files

The directory holds 31 files: 5 at the root, 15 in `code/`, 11 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 125, prefix `125-equiv-`** (14 files): the guide to its exact
finite companion; `code/`: the checker and its negative (mutation) suite, the
package integrity checker (also standing for Report 123's byte-identical
copy) and its test, the PDF build script and its four-line `build.sh`
wrapper (also Report 123's, and byte for byte
`../a307316-leafless-multigraphs/code/build.sh`), the repacking and
full-replay scripts; `data/`: the companion's frozen evidence and provenance
records, the recorded checker and negative-suite outputs, and the build
environment (also Report 123's, byte for byte).

```
125-equiv-checks-README.md
code/125-equiv-build.py
code/125-equiv-build.sh
code/125-equiv-checks-negative_tests.py
code/125-equiv-checks-verify.py
code/125-equiv-integrity.py
code/125-equiv-repack.py
code/125-equiv-reproduce.py
code/125-equiv-test_integrity.py
data/125-equiv-build-environment.txt
data/125-equiv-checks-evidence.json
data/125-equiv-checks-provenance.json
data/125-equiv-negative_results.json
data/125-equiv-verification_results.json
```

**Report 123, prefix `123-logexp-`** (14 files), the same roles, plus the
archived GMP enumerator, the OEIS b-file it reproduces (`n = 0..1000`) and
the record of that historical run:

```
123-logexp-checks-README.md
code/123-logexp-build.py
code/123-logexp-checks-enumerate_gmp.cpp
code/123-logexp-checks-negative_tests.py
code/123-logexp-checks-verify.py
code/123-logexp-repack.py
code/123-logexp-reproduce.py
code/123-logexp-test_integrity.py
data/123-logexp-checks-b279571.txt
data/123-logexp-checks-evidence.json
data/123-logexp-checks-historical_verification.json
data/123-logexp-checks-provenance.json
data/123-logexp-negative_results.json
data/123-logexp-verification_results.json
```

Report 125's checker is, among other things, a rerun of Report 123's: its
package carries Report 123's `checks/` byte for byte as `checks/legacy/`
(anchored by the manifest SHA-256 `79f5dfa1…`), and its `checks/verify.py`
imports `checks/legacy/verify.py`. Those checks are shipped once, under the
`123-logexp-` prefix.

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`report123.tex` (printed as Part II) and Report 123's delivery README
(Report 125's was staged and is replaced by this guide); the checksum
manifests (`CHECKSUMS.sha256` and `checks/manifest.sha256` of each report,
and Report 125's `checks/legacy/manifest.sha256`; all verified at
placement; repository policy drops checksum manifests); Report 125's
`checks/legacy/` (11 byte copies of Report 123's `checks/`); the two
`historical_gmp_n0_1000.txt` and Report 125's `legacy/b279571.txt` (byte
copies of the shipped b-file); and Report 123's `integrity.py`,
`build-environment.txt` and `build.sh` (byte copies of Report 125's).

## Labels and numbering

Label prefix **`icw:`** (none at HEAD before this report): Part I keeps
Report 125's 98 labels under `icw:`, Part II carries 25 of Report 123's 42
labels under `icw:log:` (the sub-prefix mirrors `cps:log:` of
`a377922-corner-polyhedra-schnyder` Part III, the general form of Part II's
method). Report 123's other 17 labels name equations of the six shared
blocks; they resolve to Part I's labels (`eq:loops` of Report 123 is
`icw:eq:loops`). The write added 55 labels: the front matter
(`icw:sec:guide`, `icw:sec:status`, `icw:sec:notation`,
`icw:sec:provenance`, `icw:sec:neighbours`), the two Part labels, 11
section and subsection labels in Part I and 17 in Part II, Part I's
further-questions subsection `icw:sub:further` with its seven items
`icw:q:*`, and in Part II the section `icw:log:sec:cone` with
`icw:log:rem:seeds`, `icw:log:prop:endpoints`, `icw:log:eq:fixed-upper`,
`icw:log:eq:fixed-lower`, `icw:log:cor:exponent`, `icw:log:rem:amplitude`,
and the section `icw:log:sec:further` with its four items `icw:log:q:*`.
178 labels in all, all distinct. The two manuscripts share 25 bare label
names; two of them name different statements (`thm:main`, and `eq:harmonic`:
discrete harmonicity of `V` in Report 125, the Brownian harmonic-measure
series in Report 123).

**Part I keeps every delivered number**: Sections 1–14, statements and
equations (1)–(86) as in `report125.tex` (a comparison of the build's `.aux`
with a build of the delivered file: 98 of 98 labels with the same number).
**Part II shifts**: Report 123's Section `k` is Section `k + 14` (15–25),
its Theorem 1.1 is Theorem 15.1 and its Lemmas 4.1, 5.1, 6.1 are Lemmas
18.1, 19.1, 20.1. Both manuscripts number equations consecutively through
the document, and so does the merged article, so Report 123's equation
numbers change:

| Report 123 | Here | | Report 123 | Here |
|---|---|---|---|---|
| (1)–(5) | (87)–(91) | | (20)–(22) | (96)–(98) |
| (6)–(7) | Part I (13)–(14) | | (23) | Part I (68) |
| (8)–(11) | (92)–(95) | | (24)–(32) | (99)–(107) |
| (12)–(19) | Part I (15)–(22) | | (33)–(38) | Part I (81)–(86) |

The write's own displays are (108) and (109). The delivered READMEs, data and
code use the manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes between the Parts or inside
one, with the tempting false readings, and each Part opens with reading
conventions. The main collisions: **`A`** (Part I's explicit whitening
matrix, the steps `A_d`, a tail constant; Part II writes `W` for any
whitening and uses `A`, `B` for compact sets), **`T`**, **`q`** (the tilted
law; `q = p − 3`; Hölder exponents; the annulus ratio in Part II), **`v`**
(a displacement; the inverse centre `v(y)`; a row functional), **`L`**,
**`λ`** (`log 9` in the inverse; the Perron eigenvalue `λ(u)`), **`h`**,
**`H`**, **`B`**, **`K`**, **`J`**, **`P`**, **`Q`**, **`D`**, `ρ_0 = 1/9` in
Report 125's (2) but `ρ = 1/9` in its Section 12 and in Report 123. Against
`a377922-corner-polyhedra-schnyder` Part III: its `ν = π/θ` is `p` here; its
`κ` is a tail rate and its `κ_P`, `κ_S` are **amplitudes**, while `κ = 1 + p`
here is the **exponent** (its `α_P`, `α_S`).

## What the report claims

**Part I (Report 125).**
- Theorem 1.1: the limits `V(s,c) = lim E_{s,c}[U(S_n); τ > n]` and `V*`
  exist, are nonnegative killed-harmonic and satisfy
  `V = U + O((1+|s|)^{p−1+δ})`; at fixed states
  `K_n((s,c),(t,d)) = (b_θ π_d/√det Σ) V(s,c) V*(t,d) n^{−p−1} + o(n^{−p−1})`;
  `K_n(o,(t,d)) ≤ C(1+|t|)^{2p} n^{−p−1}` uniformly; hence
  `a_n ~ C_A 9ⁿ n^{−κ}`, `C_A = (2/9)(b_θ/√det Σ) V(o) Σ_{t,d} π_d g(t,d) V*(t,d)`,
  `0 < C_A < ∞`.
- Corollary 1.2: `⌈v(y) − ε(y)⌉ ≤ N(y) ≤ ⌈v(y) + ε(y)⌉` with `ε(y) → 0` and
  `v(y) = (L + κ log L − κ log λ − log C_A)/λ`, `L = log y`, `λ = log 9`.
- Corollary 12.1: radius `1/9`, `1/9` the only singularity on `|z| = 1/9`,
  `log F⁽⁵⁾(x)/log(1 − 9x) → κ − 6`, `p` and `κ` irrational, `F` not
  D-finite over `ℂ(z)` (proved first in Report 123's Sections 8–9, which are
  Sections 12–13 here up to the corollary's statement and two citations;
  the proof needs only the logarithmic law).
- Inside the proof: original-time strong approximation for both chains
  (Section 4), the side-uniform Brownian wedge bound (Section 5), stopped
  moments and the summable defect potential (Section 6), explicit
  second-order colour correctors (Section 7), deep-entrance sharp survival
  (Section 8), the off-diagonal free bound and last-window smoothing
  (Section 9), midpoint reversal and endpoint domination (Section 10).

**Part II (Report 123).**
- Theorem 15.1: `c_ε 9ⁿ n^{−κ−ε} ≤ a_n ≤ C_ε 9ⁿ n^{−κ+ε}`, the circle and
  non-D-finiteness statements of Corollary 12.1, and
  `N(y) = log y/log 9 + (κ/log 9) log log y + o(log log y)`. **Superseded by
  Part I** in every item (dated note after the theorem).
- Section 16.2: the functional equations, the kernel
  `K(z,x,y)`, the scalar identity `KB = …`,
  `Disc_y K = (x−1)(zx−1)(zx²+3zx−x+1)` and the collision of the branch points
  `r_±(z)` at `(z,x,y) = (1/9, 3, 5/3)`, Part I's Perron tilt.
- Lemma 18.1 (exact-time interior bridge), Lemma 19.1 (uniform annuli,
  forward and dual), Lemma 20.1 (survival from starts with `‖s‖_W ≤ L log n`),
  the endpoint upper bound and the two-arm exact-time gluing at the endpoint
  `e = (1,0,P)`: a second route, the model-specific form of
  `a377922-corner-polyhedra-schnyder`'s Lemma 24.2 and Sections 24.4–24.6.

**Added by the write** (all marked `[write]`, dated 5 October 2026), in
Section 26:
- Remark 26.1 (with proof): the walk satisfies (H1)–(H4) of Theorem 24.1 of
  `a377922-corner-polyhedra-schnyder` (`cps:log:thm:cone`), with wedge angle
  `arccos(2/√7)`; the forward half of (H5) holds at `((0,0),P)`, but the dual
  half fails at both phases of the origin, the only endpoints that theorem
  states; and `K_n(o, ((0,0),b)) = 0` for every `n ≥ 1` and both `b`. So
  that theorem's statement says nothing about this walk except the survival
  bound from `o`.
- Proposition 26.2 (with proof): Theorem 24.1 at arbitrary fixed endpoint
  states, from its proof: (i) under (H1)–(H4), survival
  `≤ C n^{−ν/2+ε}` uniformly over starts with `|x| ≤ D' log(n+2)`, and
  `K_n((x,a),(y,b)) ≤ C n^{−1−ν+ε}` for such endpoints; (ii) with seeds
  from `(x,a)` and, for the dual, from `(y,b)`,
  `K_n((x,a),(y,b)) ≥ c_η n^{−1−ν−η}`.
- Corollary 26.3 (with proof): `K_n(o,e) = n^{−1−p+o(1)}` and Report 123's
  two-sided bounds, as a corollary of a stated theorem; Report 123's exponent
  is an instance of the **proof** of Theorem 24.1, not of its statement.
- Remark 26.4: what Part I adds to Questions Q1 (`cps:log:q:amplitude`) and
  Q3 (`cps:log:q:seeds`) of that report, and where Part I uses `4 < p < 5`
  and `p > 2`.
- The two "Further questions and research" sections, the dated supersession
  and cross-reference notes, and the front matter. A note in Section 17.2
  records that Report 123's wording of the martingale increment's
  "conditional mean zero" (given a transition `c → d`) differs from Report
  125's (given the initial colour `c`, the correct conditioning; given
  `P → P` the mean is `(−1/4, 5/4)`); Report 123's proof uses only the
  latter reading, so this is wording, not an error.

*Observations, not claims* (placement dossier; recomputed at the write in
50-digit arithmetic on the shipped b-file): `a_n 9^{−n} n^κ = 77.91, 83.24,
86.55, 87.65` at `n = 100, 200, 500, 1000`, increasing; the secant exponent
`−log(a_1000 9^{−1000}/(a_500 9^{−500}))/log 2 = 5.3834` against
`κ = 5.40169`; the two-point extrapolation `2c(1000) − c(500) = 88.76` (the
order of the correction is unknown, so this is no digit of `C_A`); with it in
place of `C_A`, `N(y) = ⌈v(y)⌉` at `y = 10^100, 10^300, 10^600, 10^900`.

## What the report does not claim

Every limitation is printed in place. In short: **no digits of `C_A`** (it
is a characterization, with no truncation error for `V(o)` or the endpoint
series); **no rate** for `a_n/(C_A 9ⁿ n^{−κ}) → 1`, no `1/n` or other
correction, no correction transseries; no effective onsets (`n_ε`, `n_0`,
the inverse envelope `ε(y)`); **no local Δ-domain expansion** at `1/9` —
circle continuation is not one; **no unconditional `N(y) = ⌈v(y)⌉`** and no
next inverse correction; **no general Markov-additive cone theorem** with
amplitudes (Report 125 says so; its argument uses `4 < p < 5`). Report 123's
"What is not asserted" paragraph and its Section 10 (here 24) describe
Report 123 alone: the equivalent, the exclusion of log-periodic modulation
and an `O(1)` inverse with explicit centre are proved in Part I (dated
notes). Prior numerical exponent and amplitude estimates (Kotěšovec in the
OEIS entry, 13 January 2026, after Beaton; Britt and Beaton's Section 4.2
and Appendix B.3) are credited, not new. **Both companions**: finite exact
checks prove no asymptotic, coupling, Brownian, harmonic-limit, survival,
local-limit, domination or G-function statement; integrity inventories are
records relative to the supplied verifiers, not signatures. The write's
Proposition 26.2 is a statement about the proof of a theorem of a
neighbouring report, re-read at the write, not an independent new
probabilistic result.

## Further questions, and the standing rule

Section 14.1 (both Parts) and Section 27 (Part II's own) state every claim
made without proof, and every question left open, with source, sketch and
what is missing (Vladimir's standing rule of 4 October 2026):

1. digits of `C_A`, an effective evaluation of `V(o)` and the endpoint
   series (Report 125, Sections 10 and 14);
2. a remainder rate, corrections, a correction transseries (both);
3. a local Δ-domain expansion at `1/9` (both; Report 123's kernel is a
   possible entry point);
4. the unconditional ceiling rule `N(y) = ⌈v(y)⌉` (Report 125, Section 11);
5. effective onsets (`n_ε`, `n_0` of Lemma 18.1, `ε(y)`);
6. a general finite-colour amplitude theorem (Report 125, Section 14; =
   Question Q1 of `a377922-corner-polyhedra-schnyder`);
7. external inputs not re-checked at the write (Bashtova–Shashkin,
   Bañuelos–Smits, Whitt, Britt–Beaton (2.44)–(2.46), Section 4.2 and
   Appendix B.3) and the two condensed arguments of Part I (angular
   uniformity in Section 5, the tilted-resolvent bound in Section 9);
8. whether Britt–Beaton's (2.45)–(2.46) already print Report 123's
   functional equations (arXiv:2512.21943v3 was not retrieved; until checked
   they are credited to Report 123 as derived there);
9. an analytic route to the exponent or to `C_A` through the kernel;
10. endpoints without seeds in general (`cps:log:q:seeds`; for this walk:
    no exponent at the origin, because `K_n` vanishes there);
11. the bridge tightness of Lemma 18.1 and the uniform Brownian transfer of
    Lemma 19.1, read as sound, not expanded.

Answered inside the merge, with dated notes: Report 123's open leading law,
its constant, log-periodic modulation and an inverse with bounded error (by
Part I). **Nothing in the two manuscripts was found to be wrong.**

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- `a377922-corner-polyhedra-schnyder`, Part III (bundle Report 112): states
  Part II's method as Theorem 24.1 (`cps:log:thm:cone`) under (H1)–(H5).
  This walk satisfies (H1)–(H4) but not (H5) at the origin endpoints the
  theorem states (Remark 26.1); Report 123's exponent follows from the
  theorem's proof (Proposition 26.2, Corollary 26.3). Part I gives, for this
  one walk, the kind of amplitude statement its Question Q1 asks for, without
  a cycle buffer, by a phase-sensitive killed local limit; A279571 is an
  example for its Question Q3. Corollary 1.2 is an instance of its Theorem
  20.1 (`cps:amp:thm:inverse`, `γ = C_A`, `μ = 9`, `α = κ`), and the
  non-D-finiteness argument of its Remark 27.1 (`cps:log:rem:criterion`),
  with derivative order 5 > κ − 1. Its Section 22.5 and README still call
  Report 123 unplaced; a reciprocal note is a separate commit.
- `a348351-one-sided-rectangulations` (bundle Report 111): the same spine as
  Part II for a four-colour bounded-step walk; its non-D-finiteness criterion
  is Remark 10.1 (`osr:rem:criterion`). Its Questions 1 and 2
  (`osr:q:equivalent`, `osr:q:harmonic`) name Report 125 as a model "to be
  filed by a later intake batch": it is Part I here. Whether Part I's route
  transfers there was not checked; as written it does not (there
  `p ≈ 1.957`, while Part I uses `p > 2` and `4 < p < 5`). Reciprocal note
  in a separate commit.
- The transseries volume
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
  Corollary 1.2 is an instance of `p0:thm:lambert-core`,
  `p0:thm:lambert-centered` and `p0:thm:staircase`; no novelty is claimed
  for the inversion mechanics.
- `a279544-inversion-kernel-classes` (A279544, A279567, A279569, A279558;
  Reports 118, 119, 122) and `a279551-inversion-log-deficit` (A279551,
  A279556; Reports 126, 127, 129), placed in the same commit: other
  Britt–Beaton classes, by algebraic kernels and by commitment-tree
  deficits; no shared theorem, method or text and no cross-citation.
  Siblings, not hosts.
- No other report treats A279571 (searched 5 October 2026); `a113227`,
  `a336070` and `a196275` cite inversion-sequence papers but treat no
  Britt–Beaton class.

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of
this report is formalized: no Lean or Rocq file in the repository mentions
inversion sequences, A279571 or Markov-additive cone walks (searched
5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (all 30 staged files were checked
  against the pristine extraction again at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files).
  Only names changed (tables at the end). The delivered code and markdown
  use delivery paths (`checks/…`, `data/…`, `report12N.tex`,
  `report12N.pdf`, `README.md`, `CHECKSUMS.sha256`, `build-environment.txt`,
  `checks/legacy/…`), which are shipped under other names or not at all.
- **Closed inventories: none of the checkers runs in this directory.** Each
  `checks/verify.py` reads `checks/manifest.sha256` and refuses extra or
  missing members; Report 125's also validates and imports
  `checks/legacy/verify.py` and reads `legacy/b279571.txt` and
  `legacy/historical_gmp_n0_1000.txt`; `integrity.py`, `test_integrity.py`,
  `reproduce.py` and `repack.py` read `CHECKSUMS.sha256` and the delivery
  layout. Rerun from the archive (below).
- `data/125-equiv-checks-provenance.json` and `125-equiv-checks-README.md`
  pin an "audited analytic source" `proof_candidate.md` by SHA-256
  (`b2c806a5…`), and the companion READMEs speak of an "independently
  audited source" and "audited formulas". That document was never delivered;
  the audit is a statement of the producing session, not checkable here, and
  the companion itself says the digest is not a proof certificate.
- `data/123-logexp-checks-historical_verification.json` records the
  historical commands with `enumerate.cpp`; the file is shipped as
  `code/123-logexp-checks-enumerate_gmp.cpp`. Both companions refer to
  `../report12N.tex` for the analytic arguments: Parts I and II of
  `article.tex`.
- The companion READMEs use `/path/to/checks/…` and `/tmp/…`; use a scratch
  directory outside the repository. Report 125's delivered README (replaced)
  asked for Python 3.10 or newer, the companion READMEs for 3.9 or later.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/A279571_Leading_Equivalent_and_Harmonic_Constant_Source.zip > s125.zip
git show 60f54ea06:docs/incoming/A279571_Exact_Asymptotic_Exponent_and_Non_D_Finiteness_Source.zip > s123.zip
mkdir r125 r123 && unzip -q s125.zip -d r125 && unzip -q s123.zip -d r123
cd r125/report125
python3 -B integrity.py
python3 -B checks/verify.py --output ../../v125.json         # also with -O; compare with data/verification_results.json
python3 -B checks/negative_tests.py --output ../../n125.json
python3 -B test_integrity.py
python3 -B reproduce.py --output ../../replay125.json        # full replay; needs the recorded TeX and POSIX
```

and the same commands in `r123/report123`. Python's standard library
suffices; `reproduce.py` and `build.py` also need TeX Live 2025 (Debian, as
recorded in `build-environment.txt`) for byte-identical PDFs. The optional
GMP run of `checks/enumerate_gmp.cpp` (C++17 and GMP) reproduces the b-file
through `n = 1000`; it is not part of the default checks.

Results: at placement (5 October 2026, Python 3.14.4 on Windows, on copies,
recorded in the batch-104 dossier) every suite passed — `integrity.py`
(22 and 28 files); `checks/verify.py` of Reports 123 and 125 in normal and
`-O` mode (about 30 s and 23 s); the negative suites (Report 123: 19 cases
in both modes, 61 s; Report 125: 48 cases plus the 19 archived ones in both
modes, 4 min 10 s); `test_integrity.py` (14 mutations, 28 runs, each);
every checksum manifest. Report 125's outputs were byte-identical to the
recorded ones, Report 123's equal up to CRLF line ends (Windows text mode).
At the write (5 October 2026, fresh extraction, Windows, Python 3.14.4)
`integrity.py` passed (28 and 22 files) and `checks/verify.py` ran in 24 s
(Report 125) and 22 s (Report 123), each output equal to the shipped JSON
after CRLF normalization. `reproduce.py`, `build.py` and the GMP run were
not run (they need the recorded TeX, POSIX and GMP); the two delivered
`.tex` files compile with MiKTeX pdfLaTeX to 25 and 16 pages with no
warnings. The intake also checked the walk model against the b-file for
`n = 0..90` and against brute-force pattern avoidance for `n = 0..8`, with its
own code.

## Rights

Repository contents are MIT-0, except `data/123-logexp-checks-b279571.txt`,
the OEIS b-file of A279571 (attributed by the OEIS to Nicholas R. Beaton,
with terms 0..32 from Václav Kotěšovec), and the OEIS terms in the
companions' fixtures, which are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). The companions claim no fresh
raw-byte retrieval of the b-file. Britt and Beaton (arXiv:2512.21943v3) are
credited for the class and the generating tree; Bashtova–Shashkin,
Bañuelos–Smits, Whitt and Fischler–Rivoal for the imported theorems.
Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 50 pages, no errors, no warnings, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull or underfull
boxes. The log carries two "Infinite glue shrinkage found in box being
split" messages from the front matter's two longtables breaking across
pages.

## Delivered path → shipped path

Report 125 (`125-equiv-`):

| Delivered | Shipped |
|---|---|
| `report125.tex` | `article.tex` (Part I; front matter, Part II and the write's notes added) |
| `README.md` | replaced by this guide |
| `checks/README.md` | `125-equiv-checks-README.md` |
| `build.py`, `build.sh`, `integrity.py`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/125-equiv-<name>` |
| `checks/verify.py`, `checks/negative_tests.py` | `code/125-equiv-checks-<name>` |
| `checks/evidence.json`, `checks/provenance.json` | `data/125-equiv-checks-<name>` |
| `data/verification_results.json`, `data/negative_results.json` | `data/125-equiv-<name>` |
| `build-environment.txt` | `data/125-equiv-build-environment.txt` |
| `checks/legacy/` (11 files) | byte copies of Report 123's `checks/`; not shipped again |
| `report125.pdf`, `CHECKSUMS.sha256`, `checks/manifest.sha256` | not shipped |

Report 123 (`123-logexp-`):

| Delivered | Shipped |
|---|---|
| `report123.tex` | not shipped; printed as Part II (its shared blocks in Part I) |
| `checks/README.md` | `123-logexp-checks-README.md` |
| `build.py`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/123-logexp-<name>` |
| `checks/verify.py`, `checks/negative_tests.py`, `checks/enumerate_gmp.cpp` | `code/123-logexp-checks-<name>` |
| `checks/b279571.txt`, `checks/evidence.json`, `checks/historical_verification.json`, `checks/provenance.json` | `data/123-logexp-checks-<name>` |
| `data/verification_results.json`, `data/negative_results.json` | `data/123-logexp-<name>` |
| `checks/historical_gmp_n0_1000.txt` | byte copy of `checks/b279571.txt`; not shipped |
| `integrity.py`, `build-environment.txt`, `build.sh` | byte copies of Report 125's; not shipped again |
| `README.md`, `report123.pdf`, `CHECKSUMS.sha256`, `checks/manifest.sha256` | not shipped |

## Provenance

Two manuscripts (bundle Reports 125 and 123) → one report; base 125,
printed as Part I. Arrival `60f54ea06`, placement `612787fb4`, write batch
104 (5 October 2026). Neither manuscript pins a ProveIt commit. Merge choices
(Report 125 first as the stronger result, Report 123's six shared blocks
printed once in Report 125's wording with the three differences noted,
Report 123's Sections 1 and 3.3 kept in full under the union rule, the
merged bibliography with Report 123's `whitt` added) are listed in the
article's front matter, "Provenance and merge decisions".
