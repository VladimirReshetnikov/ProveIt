# Bell-scale growth of OEIS A088714

**Part I: a rigorous nth-root asymptotic, quantitative bounds, and a
separately identified finer conjecture. Part II: golden-ratio moment laws
for A088714 and A088713. Part III: local estimates for the finer Bell
comparison.**

A research report in three Parts on the series A(x) = sum a_n x^n defined
formally by

    A(x) = 1 + x A(x)^2 A(x A(x)),    a_0 = 1,

and, in Part II, its companion C(x) = 1/(1 - x A(x)) (OEIS A088713).
Parts I and II are by OpenAI ChatGPT; Part III's author line ("Research
continuation prepared for Vladimir Reshetnikov") names no person or
model. Parts II and III were prepared for Vladimir Reshetnikov.

| Part | Source | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | report of September 20, 2026 (unnumbered, from the Cardinals repository) | — | — | merged into ProveIt with the Cardinals history in `dc54c3cb3` | Sections 1–10 |
| II | batch 73, manuscript 35 (cluster O2): *Golden-ratio moment laws for OEIS A088714 and A088713* (October 1, 2026; 1,524-line source, 23-page PDF) | `golden_moment_laws.zip`, arrival commit `f8c3a392a` | `1f1981f68` (it cites Part I as blob `ccb50ef33`, the blob of `article.tex` at the placement commit) | `6e193dd4f` | Sections 11–24, Appendix A |
| III | batch 76, manuscript 01: *The missing local estimate in the finer Bell comparison. An endpoint reduction, a rigorous one-sided correction, and numerical stress tests for OEIS A088714* (October 2, 2026; 372-line source, 10-page PDF) | `A088714_Bell_Local_Estimates.zip`, arrival commit `6914ccca6` | `82afb9559` (a descendant of Part II's write `0a5908ec0`; `article.tex` is the same there as at the placement commit) | `2a04b60f2` | Sections 25–34 (Section 25 is editorial) |

Status: AI-assisted, unrefereed, **not formalized**. No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status.

## Files

```
article.tex                                   the report (all three Parts), standalone LaTeX, internal bibliography
article.pdf                                   the compiled report, 51 pages
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
code/03-local-estimates-diagnose.py           Part III: exact checks and Decimal diagnostics, writes the five Part III outputs (see Rerun)
code/03-local-estimates-decimal_math.py       Part III: the small Decimal interface diagnose.py imports (as decimal_math)
code/03-local-estimates-compute_runtime.c     Part III: header-free C adapter to the 64-bit Linux GMP runtime that produced the delivered coefficient table
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
data/03-local-estimates-diagnostics.csv       Part III: ratio, normalization and tilted-variance diagnostics, n = 2..1600, 45 digits (CRLF, see Disclosures)
data/03-local-estimates-endpoint_diagnostics.json  Part III: endpoint sums, J_n, curvature and balance defects at n = 100, 200, 400, 800, 1200, 1600
data/03-local-estimates-window_sweep.json     Part III: J_n for windows 8W, 12W, 16W, 24W at the same six n
data/03-local-estimates-results_table.tex     Part III: Table 3 fragment, input by article.tex
data/03-local-estimates-endpoint_table.tex    Part III: Table 4 fragment, input by article.tex
data/03-local-estimates-precision_check.json  Part III: recorded comparison of the 80- and 120-digit runs
data/03-local-estimates-run_80.txt            Part III: recorded stdout of diagnose.py at 80 digits
data/03-local-estimates-run_120.txt           Part III: recorded stdout of diagnose.py at 120 digits
data/03-local-estimates-build.txt             Part III: the delivered pdflatex log of the manuscript (TeX Live 2023, 10 pages)
```

**`data/coefficients.txt` is not distributed** (1.3 MB). Part I's
`code/verify.py`, `code/analyze.py` and the Makefile's `verify` and
`diagnostics` targets read it; rebuild it first with
`python code/coefficients.py --n 1200 --output data/coefficients.txt`.
Part II's manuscript, delivery README and 23-page PDF are not shipped
(they survive in the archive of `f8c3a392a`); `article.pdf` is a build of
the text above.

**Part III's `data/coefficients_snapshot.txt` (a_0..a_1600, 2.49 MB) is
not distributed** either; it is regenerable, and it agrees with
`data/02-golden-moments-coefficients.csv` on n <= 401.
`code/03-local-estimates-diagnose.py` reads it (see Rerun for the rebuild
command). The delivered copy survives in the arrival commit:

    git show 6914ccca6:docs/incoming/A088714_Bell_Local_Estimates.zip > ble.zip
    unzip -p ble.zip A088714_Bell_Local_Estimates/data/coefficients_snapshot.txt > coefficients_snapshot.txt

Also not shipped from that archive, and surviving there: Part III's
manuscript, delivery README and 10-page PDF; its copy of the root
`LICENSE`; and its copies of `code/coefficients.py`,
`code/compute_gmp.cpp` and `data/diagnostics.csv` (delivered as
`data/prior_diagnostics.csv`), which equal the shipped Part I files byte
for byte.

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

Part III added **37** labels, all with the prefix `ble:` (192 in total):
24 of the manuscript's 28 labels, unchanged after the prefix, and 13 new
ones (`ble:part`, the ten section labels `ble:sec:…`, and
`ble:tab:results`, `ble:tab:endpoint` for the two delivered table
fragments, which carry no label of their own). The manuscript's
`eq:A`, `eq:N`, `eq:target` and `eq:logdiff` are not printed, because
their displays are Part I's (1.1), (8.4), (8.7) and the summability step
of Proposition 8.2. No earlier label was renamed or removed, and no
earlier number moved (the `.aux` numbers of all 155 earlier labels equal
those of a build of the committed text). The manuscript's Section k is
Section k + 25 here (its Lemma 3.1 is Lemma 28.1, Theorem 4.1 is Theorem
29.1, Theorem 5.1 is Theorem 30.1, Proposition 6.1 is Proposition 31.1);
its two tables are Tables 3 and 4.

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
to prove it. **It is still open after Part III; Part III proves
liminf (r_n - n/W(n)) >= 3/2** (Theorem 29.1; the conjecture needs the
correction 2 + W/(2(1+W)^2) -> 2) and reduces the conjecture to one
scalar estimate (Section 30).

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

## Part III: what is proved

Notation of Part III: r_n = a_n/a_{n-1} (Part I's R_n), w = W(n),
R(n) = n/w + 2 + w/(2(1+w)^2) (Part I's candidate (8.3), not a ratio),
t = n/r_n, d = w/(1+w).

- **Uniform coefficient expansion (Lemma 28.1).** For every fixed C > 0,
  uniformly in 0 <= m <= C log n,
  [z^m] A(z)^(n+1-m) = (n^m/m!) (1 + 3m(m-1)/(2n) + O((1+m)^6/n^2)),
  with no hypothesis on the ratios. This is Part I's formal expansion
  (8.1), which Part I wrote with "+ ...". Exact certificates for m = 2, 3.
- **One-sided correction (Theorem 29.1).** From Parts I and II (growth,
  moment representation, increasing ratios):
  r_n >= n/W(n) + 3/2 + 1/(2(1+W(n))) - O(W(n)^4/n), hence
  liminf (r_n - n/W(n)) >= 3/2. The conjecture needs 2; the gap
  1/2 - 1/(2(1+w)^2) is the local-curvature contribution.
- **Averaged endpoint criterion (Theorem 30.1).** An exact
  Poisson-weighted form of the endpoint recurrence; if the averaged
  curvature estimate (30.6) and the complementary-mass estimate (30.7)
  hold with errors O(w^q/n^2), then Part I's ratio estimate (8.7) holds
  and Conjecture 8.1 follows (via Proposition 8.2). The single scalar
  defect E_n of (30.8) gives a sharper form: E_n = O(W(n)^q/n^2) for some
  fixed q is sufficient, and some such bound is necessary.
- **Tilted variance (Proposition 31.1).** A relative-variance estimate
  W(i)/(i(1+W(i))) + O(W(i)^q/i^2) for the (i-1)-tilted law of mu
  suffices for the local-curvature estimate (31.1).
- **Complementary endpoint (Section 32).** J_n - 2/r_n >= 5/(r_n r_{n-1})
  ~ 5w^2/n^2, so the complementary error cannot be discarded below
  w^2/n^2.
- **Numerics (Section 33).** Exact integers through n = 1600; Tables 3
  and 4; 80- and 120-digit runs agree to 1.6e-75.

Part III re-derives Part I's Proposition 8.2 (the summability step) in
its Section 2; that argument is not reprinted, and Section 27 points to
Proposition 8.2 instead.

**Not claimed by Part III:** the finer Bell conjecture or the ratio
estimate (8.7); the hypotheses (30.6), (30.7), (31.1), (31.4) or the
bound on E_n, which are the missing estimates, not proved conclusions; a
matching upper bound for the complementary mass; a density or local tail
law for mu; the existence or value of the constant C (the finite values
near e^(-3) = 0.0498 are not evidence of an exact constant: the table
reaches 0.04785 at n = 1600); any interval certificate (the 80/120-digit
comparison is a stability check); historical priority; any formal
verification.

## Notation across the Parts

The Parts were written independently and reuse letters (c, C, F, G, B, T,
D, H, K, S, M, R, Q, X, gamma, L, r). Every symbol of Part II is local to
Part II, and Table 2 in Section 11 lists both meanings of each shared
letter. The tempting false readings: Part II's F_1(s) = 2/(1+sqrt(1+4s))
is a Stieltjes transform, not Part I's F_1(x) = A(x); Part II's c_n is
A088713, not Part I's c_{n,k}; Part I's R_n = a_n/a_{n-1} is Part II's
forward ratio r_{n-1}. No symbol of the manuscript was renamed.

Part III reuses Part I's w, t, d (same meanings) and shares further
letters (r, R, L, C, D, H, K, M, B, X, p, q, Q, s); its symbols are local
to Part III, and the lower block of Table 2, added with Part III, lists
every shared letter with all meanings. The tempting false readings:
Part III's R(n) is the candidate right side n/w + 2 + w/(2(1+w)^2), not
Part I's ratio R_n; Part III's r_n = a_n/a_{n-1} is Part I's R_n but
Part II's r_{n-1}; Part III's L = ceil(16 W(n)) is a window, not Part I's
L = log n. Three symbols of the manuscript were renamed: its normalizer
N_n is Part I's script N_n (the same function), its Bell number B_n is
Part I's sans-serif B_n in the text (the shipped table fragments still
print B_n), and the excess degree e in the proof of Lemma 28.1 is eta.

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

## Changes made when Part III was added (batch 76, 2 October 2026)

- Part III is appended after Part II's Section 24 and before Appendix A,
  which still belongs to Part II (a one-line note at the appendix says
  so). No existing number moved: every one of the 155 earlier labels has
  the same number in the `.aux` as in a build of the committed text (only
  page numbers changed).
- Dated notes "[Batch 76, 2 October 2026.]": in Part I at the formal
  expansion (8.1) (now Lemma 28.1) and after Proposition 8.2 (Part III's
  reduction to one estimate and its correction 3/2; the conjecture stays
  open); in Part II after Research question 23.2 (partial progress, not an
  answer).
- Table 2 gained a lower block for Part III's letters and a new caption;
  it is set in footnotesize on a float page so that it fits.
- The title, author and date lines and the abstract mention Part III; the
  bibliography adds Moser–Wyman and Grunwald–Serafin and notes Part III's
  use of the A088714 entry. Part I's and Part II's mathematics are
  unchanged.
- In Part III: Section k of the manuscript is Section k + 25; the
  summability argument of its Section 2 (= Proposition 8.2) is a pointer;
  its displays of the defining equation and of the normalizer are
  replaced by Part I's (1.1) and (8.4); the sentence "This proves (avg)"
  became "Under (local), this proves (avg)", since that deduction uses
  the hypothesis (31.1); an unused "Unproved estimate" theorem environment is
  dropped; file names are the shipped ones.

## Relation to other reports

- `Analysis/Transseries/docs/series-and-transseries/Moment_Determinacy_Nonlinear_Transseries/`
  studies general positive Stieltjes inverses T(y) = y S(T(y)) and moment
  determinacy; Part II's U^(-1)(t) = t(1 + U(t)) belongs to that circle of
  ideas. That package does not mention A088714 or A088713, and Part II does
  not depend on it.
- Part III's normalizer rests on the Bell asymptotic (6.6) of Part I. An
  all-orders Bell saddle expansion, with W(n) the saddle w e^w = n, is
  `q2:thm:bell` with `q2:rem:bell-scale` in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`;
  Part III cites it and uses W(n) only as that saddle (no Lambert-W
  inversion).
- No other repository file mentions A088714 or A088713 apart from the
  collection catalogue.
- Placement in this collection confers no formal status: no Lean or Rocq
  declaration states or proves any result of the three Parts.

## Build

From this directory, with a TeX installation providing pdfLaTeX:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

(or `make`). The table fragments in `data/` are input directly; no script
needs to run first. The committed PDF was built this way with MiKTeX: 51
pages, no errors, warnings, undefined references, multiply defined labels,
duplicate destinations, or overfull/underfull boxes. Do not use
`code/02-golden-moments-build.sh` (see Disclosures), and ignore Part III's
`data/03-local-estimates-build.txt`, which is the delivered log of the
manuscript's own 10-page build.

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

**Part III. Do not run `code/03-local-estimates-diagnose.py` in this
directory.** It reads `data/coefficients_snapshot.txt` (not shipped) and
`data/prior_diagnostics.csv` (a delivery name for Part I's
`data/diagnostics.csv`), imports `decimal_math` (its delivery name for
`code/03-local-estimates-decimal_math.py`) and `coefficients` (Part I's
`code/coefficients.py`), and writes `data/diagnostics.csv`,
`data/endpoint_diagnostics.json`, `data/window_sweep.json`,
`data/results_table.tex` and `data/endpoint_table.tex`. Run in this
directory it stops at the missing `decimal_math`; with that import
satisfied it would **overwrite Part I's `data/diagnostics.csv`**. Run it on a copy with the
delivered layout (Python 3.11 or later, standard library only; without
`-O`, since assertions implement the checks):

    mkdir -p /tmp/ble/code /tmp/ble/data
    cp code/03-local-estimates-diagnose.py     /tmp/ble/code/diagnose.py
    cp code/03-local-estimates-decimal_math.py /tmp/ble/code/decimal_math.py
    cp code/coefficients.py                    /tmp/ble/code/coefficients.py
    cp data/diagnostics.csv                    /tmp/ble/data/prior_diagnostics.csv
    # the coefficient table a_0..a_1600: rebuild it with the shipped C++/GMP code,
    g++ -O3 -std=c++17 code/compute_gmp.cpp -lgmpxx -lgmp -o /tmp/ble/compute_gmp
    /tmp/ble/compute_gmp 1600 /tmp/ble/data/coefficients_snapshot.txt
    # or with the standard-library generator (same recurrence, much slower):
    #   python3 code/coefficients.py --n 1600 --output /tmp/ble/data/coefficients_snapshot.txt
    # or fetch the delivered copy (see Files)
    cd /tmp/ble
    python3 code/diagnose.py 80  > run_80.txt
    python3 code/diagnose.py 120 > run_120.txt

Each generator performs N(N+1)(N+2)/6 = 6.8 x 10^8 big-integer products
at N = 1600. The delivered table was produced by
`code/03-local-estimates-compute_runtime.c`, a header-free adapter that
declares GMP's internal symbols for the 64-bit Linux runtime because the
delivery machine lacked GMP's development headers; it implements the same
recurrence, is not portable, and is shipped only as a record of the code
actually run. The table was not regenerated here. Its first 402 values
equal `data/02-golden-moments-coefficients.csv`, and `diagnose.py` checks
a_0..a_80 against `coefficients.py` and every ratio a_n/a_{n-1}, n <= 1200,
against Part I's 40-digit `data/diagnostics.csv` to 1e-35.

Rerun on 2026-10-02 this way with the delivered table (Python 3.14.4,
Windows): both stdout captures equal the shipped `run_80.txt` and
`run_120.txt` after removal of carriage returns; after the 120-digit run
(the last delivered run), the CSV, both JSON files and both table
fragments equal the shipped `03-local-estimates-` files after removal of
carriage returns. (The JSON files record 80 or 120 digits according to
the last run; the CSV and the tables do not depend on the precision.) On
Windows the script writes CRLF text, and its CSV gets CR CR LF line ends.
No shipped script writes `data/03-local-estimates-precision_check.json`;
it is a recorded comparison of the two runs.

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
  describe the committed `article.pdf`.
- The Part II scripts read and write delivery names (`data/coefficients.csv`,
  `data/verification.json`, …); the rename map is `data/<name>` →
  `data/02-golden-moments-<name>` and `code/<name>.py` →
  `code/02-golden-moments-<name>.py`, with `build.sh` →
  `code/02-golden-moments-build.sh` and `SOURCE_AUDIT.md` →
  `02-golden-moments-SOURCE_AUDIT.md`.
- Part I's text in Section 9 names `data/coefficients.txt`, which is not
  distributed (see Files).
- Part III's shipped files are byte-identical to the delivery. Their
  rename map is `code/<name>` → `code/03-local-estimates-<name>` and
  `data/<name>` → `data/03-local-estimates-<name>`. Inside them the
  delivery names remain: `diagnose.py` reads and writes the delivery
  names listed under Rerun, `run_80.txt` and `run_120.txt` are its stdout
  under those names, and `data/03-local-estimates-build.txt` is the
  pdflatex log of the delivered 10-page manuscript (TeX Live 2023/Debian),
  not of the committed `article.pdf`.
- `data/03-local-estimates-diagnostics.csv` has CRLF line ends, as Python's
  `csv` module wrote it; `SetTheory/Cardinals/.gitattributes` marks it
  `-text` so that Git keeps it byte-identical. The three JSON files have no
  final newline.
- The delivered README's "Reproduce" section reads the unshipped
  `data/coefficients_snapshot.txt` and names `code/compute_gmp.cpp` and
  `code/coefficients.py` as part of the delivery; here those two are Part
  I's files of the same names (identical blobs), and the table must be
  rebuilt or fetched first (Rerun). The delivered README itself is not
  shipped.
- Part III's table fragments print the Bell numbers as `B_n`; the text
  writes Part I's sans-serif B_n. Its diagnostics column
  `log_smooth_normalization` is log(a_n / script N_n), the manuscript's
  D_n^N.
