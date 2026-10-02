# Bell-scale growth of OEIS A088714

**Part I: a rigorous nth-root asymptotic, quantitative bounds, and a
separately identified finer conjecture. Part II: golden-ratio moment laws
for A088714 and A088713.**

A research report in two Parts on the series A(x) = sum a_n x^n defined
formally by

    A(x) = 1 + x A(x)^2 A(x A(x)),    a_0 = 1,

and, in Part II, its companion C(x) = 1/(1 - x A(x)) (OEIS A088713).
Both Parts are by OpenAI ChatGPT; Part II was prepared for Vladimir
Reshetnikov.

| Part | Source | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | report of September 20, 2026 (unnumbered, from the Cardinals repository) | — | — | merged into ProveIt with the Cardinals history in `dc54c3cb3` | Sections 1–10 |
| II | batch 73, manuscript 35 (cluster O2): *Golden-ratio moment laws for OEIS A088714 and A088713* (October 1, 2026; 1,524-line source, 23-page PDF) | `golden_moment_laws.zip`, arrival commit `f8c3a392a` | `1f1981f68` (it cites Part I as blob `ccb50ef33`, the blob of `article.tex` at the placement commit) | `6e193dd4f` | Sections 11–24, Appendix A |

Status: AI-assisted, unrefereed, **not formalized**. No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status.

## Files

```
article.tex                                   the report (both Parts), standalone LaTeX, internal bibliography
article.pdf                                   the compiled report, 38 pages
README.md                                     this guide
Makefile                                      Part I's build/verify/diagnostics targets
requirements.txt                              Part I's optional dependency (mpmath, for code/analyze.py)
02-golden-moments-SOURCE_AUDIT.md             Part II's source, dependency and novelty audit, as delivered
code/coefficients.py                          Part I: exact triangular recurrence (standard library)
code/compute_gmp.cpp                          Part I: the same recurrence in C++/GMP
code/verify.py                                Part I: polynomial, positivity and finite-bound checks
code/analyze.py                               Part I: high-precision diagnostics and Table 1
code/02-golden-moments-verify.py              Part II: exact audits (standard library)
code/02-golden-moments-orbit_bounds.py        Part II: outward-rounded orbit enclosures (Decimal, 100 digits)
code/02-golden-moments-make_tables.py         Part II: regenerates the three table fragments
code/02-golden-moments-build.sh               Part II's delivered three-pass pdflatex script (see Disclosures)
data/diagnostics.csv                          Part I: diagnostics for n = 2..1200, 40 significant digits
data/diagnostics_table.tex                    Part I: Table 1, input by article.tex
data/verification.txt                         Part I: recorded output of code/verify.py
data/analysis_output.txt                      Part I: recorded output of code/analyze.py
data/02-golden-moments-coefficients.csv       Part II: a_n and c_n for n = 0..401
data/02-golden-moments-verification.json      Part II: recorded audit report
data/02-golden-moments-verification.txt       Part II: its summary (PASS lines)
data/02-golden-moments-run_output.txt         Part II: recorded stdout of the audit
data/02-golden-moments-orbit_bounds.json      Part II: exact seed, location intervals, enclosures
data/02-golden-moments-orbit_output.txt       Part II: recorded stdout of the orbit script
data/02-golden-moments-hankel_table.tex       Part II: Hankel-determinant table fragment, input by article.tex
data/02-golden-moments-ratio_table.tex        Part II: scaled-ratio table fragment, input by article.tex
data/02-golden-moments-orbit_table.tex        Part II: orbit-enclosure table fragment, input by article.tex
data/02-golden-moments-environment.txt        Part II: software versions of the delivered run
```

**`data/coefficients.txt` is not distributed** (1.3 MB). Part I's
`code/verify.py`, `code/analyze.py` and the Makefile's `verify` and
`diagnostics` targets read it; rebuild it first with
`python code/coefficients.py --n 1200 --output data/coefficients.txt`.
Part II's manuscript, delivery README and 23-page PDF are not shipped
(they survive in the archive of `f8c3a392a`); `article.pdf` is a build of
the text above.

## Labels and numbering

Part I's 69 labels are bare (`thm:main`, `eq:…`) and unchanged. Part II
added **86** labels, all with the prefix `gml:` (155 in total): the
manuscript's 82 printed labels, unchanged after the prefix, and four new
ones (`gml:part`, `gml:sec:source`, `gml:sec:scope`, `gml:tab:notation`).
The ten labels of the manuscript's Appendix A, which is not reprinted, are
dropped. No Part I label was renamed or removed, and no Part I number
moved (the `.aux` numbers of all 69 labels equal those of a build of the
committed text). The manuscript's Section k is Section k + 11 here
(Theorems 1.1–1.3 are Theorems 12.1–12.3, the Tauberian lemma of its
Section 8 is Lemma 19.1, and so on); its Appendix B is Appendix A.

## Part I: what is proved

    log(a_n) = n log(n) - n log(log(n)) - n + O(n log(log(n))/log(n)),

and consequently a_n^(1/n) ~ n/(e log(n)) (Theorem 1.1), with explicit
finite-index bounds max h^(n+1-h) <= a_n <= inf (1+2/lambda)^n T_n'(lambda)
(Theorem 1.2). This is an nth-root/logarithmic asymptotic, NOT the
assertion `a_n ~ (n/(e log(n)))^n`. The ordinary generating function has
radius zero; the exponential generating function is entire.

The finer formula a_n ~ C Bell_n exp(W(n)^2 + 3 W(n)) is labelled a
CONJECTURE (Conjecture 8.1). Neither its constant nor the existence of its
limit is proved; Proposition 8.2 identifies a ratio estimate sufficient
to prove it. **It is still open after Part II.**

## Part II: what is proved

- **Moment structure (Theorem 12.1).** Unique (determinate) probability
  measures mu, nu on [0, inf) with moments a_n and c_n; all positive
  exponential moments finite; unbounded supports; every minor of both
  infinite Hankel matrices with increasing index lists strictly positive;
  every iterate of the log-convexity operator a Stieltjes moment sequence
  with positive entries; Stieltjes transforms with
  F(s) = 1 - s F(s)^2 F(s F(s)), G(s) = 1/(1 + s F(s)), and U(s) = s F(s) a
  homeomorphism of (0, inf) with U^(-1)(t) = t(1 + U(t)).
- **Golden-ratio endpoint laws (Theorem 12.2).** F(s) ~ s^(-alpha),
  G(s) ~ s^(-beta) with constant one, alpha = (3 - sqrt 5)/2,
  beta = (sqrt 5 - 1)/2; mu([0,t]) ~ sin(pi alpha) t^alpha/(pi alpha) and
  likewise for nu; no atom at zero; sharp negative-moment thresholds.
- **Ratios and far tails (Theorem 12.3).** a_{n+1}/a_n ~ c_{n+1}/c_n ~
  n/log n, and log mu([x, inf)) ~ log nu([x, inf)) ~ -x log x.
- Also: the moment-preserving nonlinear transform (Theorem 13.3), the
  determinant bridge D_n^(1)(c) = D_n^(0)(a), D_n^(0)(c) = D_{n-1}^(1)(a)
  (Proposition 15.4), monotone algebraic brackets of F with
  Fibonacci-ratio exponents f_r/f_{r+2} (Theorem 17.2), the iteration
  rigidity lemma (Lemma 18.1), log c_n = log a_{n-1} + O(log n)
  (Proposition 20.2), a quantitative ratio estimate with error
  O(sqrt(log log n / log n)), and eight research questions (Section 23).

Part II uses Part I's Theorem 1.1 as input. The manuscript re-proved it in
an appendix (its Appendix A, which follows Part I's Sections 2–5 step for
step and says it is "not claimed as new work"); that appendix is not
reprinted, and Section 11 says so.

**Not claimed by Part II:** absolute continuity or a density of either
measure; the absence of support gaps or positive atoms away from zero; a
multiplicative tail formula; a multiplicative equivalent for a_n; that
c_n ~ a_{n-1}; Part I's finer Bell conjecture (Research question 23.2);
historical priority (the novelty audit is bounded, Section 12.3 and
Appendix A); any formal verification. The orbit enclosures of Section
22.2 illustrate the constant-one law at particular inverse-orbit points;
they are not its proof. The exact checks audit implementations and finite
instances; the all-index statements are the written proofs.

## Notation across the Parts

The Parts were written independently and reuse letters (c, C, F, G, B, T,
D, H, K, S, M, R, Q, X, gamma, L, r). Every symbol of Part II is local to
Part II, and Table 2 in Section 11 lists both meanings of each shared
letter. The tempting false readings: Part II's F_1(s) = 2/(1+sqrt(1+4s))
is a Stieltjes transform, not Part I's F_1(x) = A(x); Part II's c_n is
A088713, not Part I's c_{n,k}; Part I's R_n = a_n/a_{n-1} is Part II's
forward ratio r_{n-1}. No symbol of the manuscript was renamed.

## Changes made when Part II was added

- Part I gained two dated notes (2026-10-01): after Theorem 1.1, at the
  sentence that an nth-root equivalent does not by itself imply an
  equivalent for a_n/a_{n-1} (Part II proves a_{n+1}/a_n ~ n/log n,
  Theorem 12.3), and in Section 7.2, at the sentence that R_n and
  D_n^num examine finer behaviour (R_n ~ n/log n is now proved; D_n^num and
  Conjecture 8.1 remain open). Part I's statement in Section 8.3 that its
  main theorem does not supply the ratio estimate (8.7) is still true and
  unchanged: Part II's ratio law is too weak for it, as Part II says after
  Research question 23.2.
- The title, date line and abstract mention Part II; the bibliography
  merges the manuscript's A088714 entry with Part I's and adds its other
  five entries.
- In Part II, references to "the earlier ProveIt article" point to Part I;
  the manuscript's link to a GitHub copy of Part I at the pin is replaced
  by an internal reference; file names are the shipped ones. Section 11
  (new) holds the summary, provenance, notation table and these changes.

## Relation to other reports

- `Analysis/Transseries/docs/series-and-transseries/Moment_Determinacy_Nonlinear_Transseries/`
  studies general positive Stieltjes inverses T(y) = y S(T(y)) and moment
  determinacy; Part II's U^(-1)(t) = t(1 + U(t)) belongs to that circle of
  ideas. That package does not mention A088714 or A088713, and Part II does
  not depend on it.
- No other repository file mentions A088714 or A088713 apart from the
  collection catalogue.

## Build

From this directory, with a TeX installation providing pdfLaTeX:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

(or `make`). The table fragments in `data/` are input directly; no script
needs to run first. The committed PDF was built this way with MiKTeX: 38
pages, no errors, warnings, undefined references, multiply defined labels,
duplicate destinations, or overfull/underfull boxes. Do not use
`code/02-golden-moments-build.sh` (see Disclosures).

## Rerun the checks

**Part I.** Python 3.10 or later; the exact code uses only the standard
library. After rebuilding `data/coefficients.txt` (above):

    python3 code/verify.py

The supplied run verified the first 21 OEIS terms, recomputed coefficients
through n = 400, checked the functional equation and inverse identities
through degree 40, the difference-polynomial identity and positivity
through n = 80, and the finite bounds through n = 150 at the five reported
Poisson means. `python3 -m pip install -r requirements.txt` and
`python3 code/analyze.py --precision 70` recompute the diagnostics; note
that `analyze.py` overwrites `data/diagnostics.csv` and
`data/diagnostics_table.tex`. Part I's C++ program:

    g++ -O3 -std=c++17 code/compute_gmp.cpp -lgmpxx -lgmp -o compute_gmp
    ./compute_gmp 1200 data/coefficients.txt

Both implementations use N(N+1)(N+2)/6 big-integer products and O(N^2)
integer cells. The numerical constant estimator of `analyze.py` is
exploratory, not a certified enclosure.

**Part II. Do not run its scripts in this directory.** They write
`data/coefficients.csv`, `data/verification.json`, `data/verification.txt`,
`data/orbit_bounds.json` and three `data/*_table.tex` files under their
delivery names, and `data/verification.txt` is Part I's recorded output,
which `code/02-golden-moments-verify.py` would overwrite. Run them on a copy
with the delivered layout (Python 3.10 or later, standard library only;
without `-O`, since assertions implement the checks):

    mkdir -p /tmp/gml/code /tmp/gml/data
    for f in verify orbit_bounds make_tables; do
      cp code/02-golden-moments-$f.py /tmp/gml/code/$f.py; done
    for f in data/02-golden-moments-*; do
      cp "$f" "/tmp/gml/data/${f#data/02-golden-moments-}"; done
    cd /tmp/gml
    python3 code/verify.py --n 401 > run_output.txt
    python3 code/orbit_bounds.py > orbit_output.txt
    python3 code/make_tables.py

Rerun on 2026-10-01 this way (Python 3.14.4, Windows, 39 s in total): the
regenerated coefficients, orbit bounds and the three table fragments, and
both stdout captures, equal the shipped files after removal of carriage
returns, except the wall-time field in `verification.json`,
`verification.txt` and `run_output.txt` (35.4 s against the recorded
5.087 s). On Windows the scripts write CRLF line endings.

The completed delivered run checked all displayed OEIS prefix values (21
terms of A088714, 22 of A088713), two independent formal identities
through degree 30, coefficient stabilization through stage 16, direct
rational full-Fock moments through order 10, 17,768 generalized Hankel
minors, 40 leading and shifted determinants, 20 determinant-bridge
identities, and 1,128 positive entries after six log-convexity iterations.

## Disclosures

- `code/02-golden-moments-build.sh` was delivered at the package root; it
  changes into its own directory and runs pdflatex on `article.tex`
  there, so in `code/` it finds no `article.tex` and fails. It is shipped
  byte-identical; use `latexmk` or `make` instead.
- `02-golden-moments-SOURCE_AUDIT.md` (byte-identical) uses delivery names
  and the manuscript's numbering: its "Appendix A" (the re-proof of
  Part I) is not reprinted; its "Section 8" is Section 19 here; its
  `data/verification.json` and `data/orbit_bounds.json` are
  `data/02-golden-moments-verification.json` and
  `data/02-golden-moments-orbit_bounds.json`; its "eight research
  questions" are Research questions 23.1–23.8. It describes the delivered
  23-page PDF, which is not shipped.
- `data/02-golden-moments-environment.txt` records the delivered build
  (pdfTeX in TeX Live 2025/dev, 23 pages, Python 3.13.5); it does not
  describe the committed 38-page `article.pdf`.
- The Part II scripts read and write delivery names (`data/coefficients.csv`,
  `data/verification.json`, …); the rename map is `data/<name>` →
  `data/02-golden-moments-<name>` and `code/<name>.py` →
  `code/02-golden-moments-<name>.py`, with `build.sh` →
  `code/02-golden-moments-build.sh` and `SOURCE_AUDIT.md` →
  `02-golden-moments-SOURCE_AUDIT.md`.
- Part I's text in Section 9 names `data/coefficients.txt`, which is not
  distributed (see Files).
