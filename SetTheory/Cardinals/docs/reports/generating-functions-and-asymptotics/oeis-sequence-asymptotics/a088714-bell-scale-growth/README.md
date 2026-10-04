# Bell-scale growth of OEIS A088714

**Part I: a rigorous nth-root asymptotic, quantitative bounds, and a
separately identified finer conjecture. Part II: golden-ratio moment laws
for A088714 and A088713. Part III: local estimates for the finer Bell
comparison. Part IV: densities, the correction profile, and the companion
sequence. Part V: the Bell normalization of A088714 and A088713.**

A research report in five Parts on the series A(x) = sum a_n x^n defined
formally by

    A(x) = 1 + x A(x)^2 A(x A(x)),    a_0 = 1,

and, from Part II on, its companion C(x) = 1/(1 - x A(x)) (OEIS A088713).
Parts I and II are by OpenAI ChatGPT; Part III's author line ("Research
continuation prepared for Vladimir Reshetnikov") names no person or
model. Parts II and III were prepared for Vladimir Reshetnikov. Part IV
was "Prepared with ChatGPT", building on this repository; Part V's author
line is "ChatGPT".

| Part | Source | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | report of September 20, 2026 (unnumbered, from the Cardinals repository) | — | — | merged into ProveIt with the Cardinals history in `dc54c3cb3` | Sections 1–10 |
| II | batch 73, manuscript 35 (cluster O2): *Golden-ratio moment laws for OEIS A088714 and A088713* (October 1, 2026; 1,524-line source, 23-page PDF) | `golden_moment_laws.zip`, arrival commit `f8c3a392a` | `1f1981f68` (it cites Part I as blob `ccb50ef33`, the blob of `article.tex` at the placement commit) | `6e193dd4f` | Sections 11–24, Appendix A |
| III | batch 76, manuscript 01: *The missing local estimate in the finer Bell comparison. An endpoint reduction, a rigorous one-sided correction, and numerical stress tests for OEIS A088714* (October 2, 2026; 372-line source, 10-page PDF) | `A088714_Bell_Local_Estimates.zip`, arrival commit `6914ccca6` | `82afb9559` (a descendant of Part II's write `0a5908ec0`; `article.tex` is the same there as at the placement commit) | `2a04b60f2` | Sections 25–34 (Section 25 is editorial) |
| IV | batch 86, manuscript 01, its part on A088714/A088713 (Sections 3–6, with the matching passages of Sections 1, 8 and 9): *Three advances on OEIS conjectures and asymptotics. Bridgeless toroidal maps, golden-ratio moment laws, and unitary-divisor partitions* (4 October 2026 UTC; 2,894-line source, 40-page PDF) | `oeis_advances.zip`, arrival commit `ae9baa422` | `eaf08931c` (`article.tex` and `README.md` are the same there as at the placement commit) | `0f084afa9` | Sections 35–41 (Section 35 is editorial) |
| V | batch 86, manuscript 02, its part on A088714/A088713 (Sections 8–12, with the matching passages of Sections 1, 13–15 and Appendix B): *Signs, Factorial Divergence, and Bell Normalization. New results for OEIS A321941, A088714, and A088713* (4 October 2026; 2,537-line source, 36-page PDF) | `oeis_research_bundle.zip`, arrival commit `ae9baa422` | `b7e4f25b6` (an ancestor of `eaf08931c`; it cites this report as blob `3a4ade894`, the blob of `article.tex` at the placement commit) | `0f084afa9` | Sections 42–49 (Section 42 is editorial) |

The other parts of the two batch-86 manuscripts are printed elsewhere in
the collection: manuscript 01's Section 2 (A343093) is the report
`enumerative-combinatorics/a343093-bridgeless-toroidal-maps`, its Section
7 (A301981/A301982) is Part II of
`generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301981-unitary-divisor-partitions`,
and manuscript 02's Sections 2–7 and Appendix A (A321941) are Part II of
`congruences-and-valuations/a321941-asymptotic-coefficient-integrality`
(paths relative to `SetTheory/Cardinals/docs/reports/`).

Status: AI-assisted, unrefereed, **not formalized**. No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status.

**Part V proves Part I's Conjecture 8.1** (Theorem 46.1). That proof comes
from a single AI-generated manuscript and **has not yet been
independently reviewed**: at placement its argument was followed step by
step without finding a gap and its finite consequences were checked
against the data of Parts I–III, which is not a review. Cite the
conjecture as "proved in Part V (batch 86, manuscript 02), not yet
independently reviewed", not as settled.

## Files

```
article.tex                                   the report (all five Parts), standalone LaTeX, internal bibliography
article.pdf                                   the compiled report, 101 pages
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
code/04-densities-profile-verify_dynamics.py  Part IV: exact Stieltjes seed and outward-rounded 100-digit interval certificate for P != 0 (standard library)
code/04-densities-profile-verify_renewal.py   Part IV: independent formal coefficients, composition identity, renewal diagnostics (standard library)
data/04-densities-profile-dynamics_certificate.json  Part IV: recorded certificate (moments a_0..a_31, seed, orbit and profile enclosures)
data/04-densities-profile-renewal_checks.json Part IV: recorded renewal checks and diagnostics, n = 20..260
code/05-bell-norm-verify_complement.py        Part V: exact endpoint and companion decompositions through n = 32 (prints JSON)
code/05-bell-norm-normalization_diagnostics.py  Part V: exact a_n, c_n through 600 and Decimal normalization table
code/05-bell-norm-run_checks.py               manuscript 02's driver for both of its parts (see Rerun; it overwrites its two records)
data/05-bell-norm-endpoint_verification.json  Part V: recorded output of verify_complement.py
data/05-bell-norm-coefficients_600.txt        Part V: "n a_n" for n = 0..600, exact integers (294,919 bytes)
data/05-bell-norm-normalization_80.json       Part V: normalization diagnostics at 80 digits (Table 8)
data/05-bell-norm-normalization_120.json      Part V: the same at 120 digits
data/05-bell-norm-normalization_precision_check.json  Part V: recorded comparison of the two runs
data/05-bell-norm-verification_run.txt        manuscript 02: recorded log of run_checks.py --symbolic (both parts)
data/05-bell-norm-verification_summary.json   manuscript 02: recorded summary of that run
data/05-bell-norm-SOURCE_AUDIT.json           manuscript 02's source audit (pins, blobs, inherited inputs, review scope; both parts)
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

Not shipped from the batch-86 archives (both in arrival commit
`ae9baa422`): manuscript 01's PDF (its `oeis_advances.tex` and
`README.txt` were staged, unchanged, as the base of the A343093 report,
and are rewritten there); manuscript 02's `oeis_research.tex`,
`README.txt`, PDF and checksum manifest `MANIFEST.sha256` (24 of 24
entries verified at placement). Manuscript 02's A321941 programs and data
are shipped with the A321941 report under the prefix `02-sign-`
(`code/02-sign-{finite_certificate,verify_sign,independent_check,large_order,asymptotic_check}.py`,
`data/02-sign-{sign_verification.json,independent_check.json,large_order_coefficients.json,asymptotic_check.txt,requirements-symbolic.txt}`);
the shared driver, its two records and the source audit are shipped
once, here.

    git show ae9baa422:docs/incoming/oeis_research_bundle.zip > orb.zip
    git show ae9baa422:docs/incoming/oeis_advances.zip > adv.zip

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

Part IV added **128** labels, all with the prefix `gdy:`: all 125 labels
of manuscript 01's Sections 3–6 and of the passages of its Sections 8
and 9 that are printed, unchanged after the prefix (`gdy:gold:…`,
`gdy:reg:…`, `gdy:dyn:…`, `gdy:ren:…`, `gdy:verify:section`,
`gdy:future:…`), and three new ones (`gdy:part`, `gdy:sec:source`,
`gdy:tab:notation`). Part V added **56** labels, all with the prefix
`bnc:`: 53 of the 61 labels of manuscript 02's Sections 8–15, unchanged
after the prefix, and three new ones (`bnc:part`, `bnc:sec:source`,
`bnc:tab:notation`). Not printed: `eq:inheritedgrowth`,
`eq:inheritedmoment`, `eq:inheritedratio` (Part III's
`ble:eq:growth`–`ble:eq:ratio`), `eq:bellrecurrence` (`ble:eq:rec`),
`lem:localcoeff` and `eq:localcoeff` (`ble:lem:coef`, `ble:eq:b`),
`eq:Bellsaddle` (`eq:bellsaddle`), and `sec:verification` (its Sections
13 and 14 are merged into Section 48). That makes **376** labels. No
earlier label was renamed or removed, and no earlier number moved (the
`.aux` numbers of all 192 earlier labels, and of Part I's table label in
`data/diagnostics_table.tex`, equal those of a build of the committed
text). Manuscript 01's Sections 3–6 are Sections 36–39 here and the
printed parts of its Sections 8 and 9 are Sections 40 and 41 (its
Proposition 3.1 is Proposition 36.1, Theorem 4.1 is Theorem 37.1,
Theorem 5.1 is Theorem 38.1, Theorem 6.1 is Theorem 39.1). Manuscript
02's Sections 8–12 are Sections 43–47 and the printed parts of its
Sections 13–15 are Sections 48 and 49 (its Theorem 9.1 is Theorem 44.1,
Theorem 10.1 is Theorem 45.1, Theorem 11.1 is Theorem 46.1, Theorem 12.1
is Theorem 47.1, Research questions 15.1–15.5 and 15.9 are 49.1–49.6);
its Tables 1 and 2 are Tables 7 and 8, and the notation tables of Parts
IV and V are Tables 5 and 6.

## Part I: what is proved

    log(a_n) = n log(n) - n log(log(n)) - n + O(n log(log(n))/log(n)),

and consequently a_n^(1/n) ~ n/(e log(n)) (Theorem 1.1), with explicit
finite-index bounds max h^(n+1-h) <= a_n <= inf (1+2/lambda)^n T_n'(lambda)
(Theorem 1.2). This is an nth-root/logarithmic asymptotic, NOT the
assertion `a_n ~ (n/(e log(n)))^n`. The ordinary generating function has
radius zero; the exponential generating function is entire.

The finer formula a_n ~ C Bell_n exp(W(n)^2 + 3 W(n)) is labelled a
CONJECTURE (Conjecture 8.1). Part I proves neither its constant nor the
existence of its limit; Proposition 8.2 identifies a ratio estimate
sufficient to prove it. It was still open after Part III, which proves
liminf (r_n - n/W(n)) >= 3/2 (Theorem 29.1; the conjecture needs the
correction 2 + W/(2(1+W)^2) -> 2) and reduces the conjecture to one
scalar estimate (Section 30). **Part V proves it** (Theorem 46.1, below),
in a proof not yet independently reviewed, and without proving Part I's
ratio estimate (8.7), which remains open.

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

## Part IV: what is proved

Part IV answers Part II's Research questions 23.1, 23.3 and 23.6.

- **Densities and support (Theorem 37.1).** mu and nu are absolutely
  continuous, with strictly positive real-analytic densities p, q on
  (0, inf), and supp mu = supp nu = [0, inf): no atoms, no singular
  continuous part, no gaps. As x -> 0,
  p(x) ~ sin(pi alpha) x^(-beta) / pi and q(x) ~ sin(pi beta) x^(-alpha) / pi;
  every fixed derivative has the corresponding equivalent (Corollary
  37.8). The proof imports Huang–Wang's global inversion theorem
  (Advances in Math. 402 (2022), Propositions 3.1–3.2) and excludes every
  density zero by a descent through the inverse identity H(K(z)) = z.
- **The correction profile (Theorem 38.1, Corollary 38.3).** There is a
  nonzero real-analytic P with P(t+1) = -P(t) such that
  log(s^alpha F(s)) = sum_{n<=N} Q_n(log_phi log s)/(log s)^(2n-1)
  + O((log s)^(-2N-1)) for every N, with Q_1 = P and the Q_n explicit;
  the full series converges for large log s, with an O(s^(-beta))
  remainder (O(s^(-1)) for G). An exact rational seed and an
  outward-rounded 100-digit interval computation prove P != 0, with
  0.00095032738531560 < P(log_phi Psi(x_*)) < 0.00095032738531562; hence
  (log s)(s^alpha F(s) - 1) has limsup M and liminf -M, M > 0.00095.
- **The companion sequence (Theorem 39.1).** For every log-convex
  sequence with a_0 = 1 and a_n/a_(n-1) ~ n/log n, and every fixed K,
  c_n = sum_{j<=K} gamma_j a_(n-1-j) + O_K(a_(n-K-2)), gamma_j = [z^j]C(z)^2;
  for A088713, c_n/a_(n-1) = 1 + 2 log n/n + o(log n/n), and
  c_(n+1)/c_n - a_n/a_(n-1) -> 0 (Corollary 39.3).

**Not claimed by Part IV:** a multiplicative far-tail equivalent for the
densities or a complete large-n moment asymptotic; global monotonicity of
p or q (the derivative equivalents hold for each fixed order, not as
complete monotonicity on one interval); the maximum of P, its zeros or
its least period (the certificate encloses one value of P, at one true
orbit point, not every point of the interval around it); any statement
off the real Stieltjes axis or a second-order law for the distribution
functions or densities; the fine Bell normalization or the finer
expansion of the ratios; historical priority (the search was bounded);
any formal verification. Finite diagnostics enter no proof.

## Part V: what is proved

- **Complementary endpoint (Theorem 44.1).** With T_n(L) the sum over
  m > L in the exact recurrence (Part III's a_n J_n) and
  D(z) = z^(-1)(1 - 1/(zA(z))') = sum delta_h z^h (delta_0..5 = 2, 5, 24,
  148, 1052, 8226): for fixed P and C log 2 > P + 5,
  T_n(ceil(C W(n))) = sum_{h<=P} delta_h a_(n-1-h) + O_P(a_(n-P-2)).
  At Part III's window, J_n = 2/r_n + 5/(r_n r_(n-1)) + O(W^3/n^3): this
  proves Part III's missing estimate (30.7) with q = 2 and turns its
  one-sided bound (Section 32) into an asymptotic equality.
- **Bounded factors (Theorem 45.1).** c N_n <= a_n <= C N_n.
- **Bounded additive ratio error (Lemma 46.2).** R_n = n/W(n) + O(1),
  unconditionally (Part III has only the liminf >= 3/2).
- **Finer Bell normalization (Theorem 46.1).**
  a_n = C_* N_n (1 + O(W(n)^5/n)), 0 < C_* < inf, so
  a_n ~ C_* Bell_n exp(W(n)^2 + 3 W(n)): Conjecture 8.1. The proof sums a
  linearized Poisson equation (Lemma 46.3) with a column-stability lemma
  (Lemma 46.4); it uses neither Part III's curvature estimate (31.1) nor
  its tilted-variance estimate (31.4). **Not yet independently reviewed.**
- **Companion (Theorem 47.1).** c_n = sum_{h<=P} gamma_h a_(n-1-h) +
  O_P(a_(n-P-2)) (the expansion of Theorem 39.1, proved independently: a
  second route), c_n ~ a_(n-1), and, new,
  c_n = C_* (W(n)/n) N_n (1 + O(W(n)^5/n)) with the same constant.

**Not claimed by Part V:** the value of C_*, or any certified interval
for it (the Table 8 decimals and their 80/120-digit agreement are a
stability check, not interval arithmetic); the pointwise ratio expansion
(8.7), R_n = n/W + 2 + W/(2(1+W)^2) + O(W^p/n) (only R_n = n/W + O(1)
is proved; the approach of R_n - n/W(n) to 2 in the table is only
consistent with it); that the rate O(W^5/n) is optimal; growing
truncation orders P; external review, worldwide priority (its source
audit records `external_peer_review`, `proof_assistant_formalized` and
`worldwide_priority_exhaustively_verified` as false), or any formal
verification. Finite checks prove no infinite statement.

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

Parts IV and V have their own notation tables (Tables 5 and 6), listing
every letter they share with the other Parts. Part IV writes
r_n = a_n/a_(n-1) like Part III; Part V writes Part I's R_n. Renamed from
manuscript 01 (no normalization changed): its d_j = [z^j]C(z)^2 is
**gamma_j** (as in Part V), its w_n = a_(n-1) is **omega_n** (w is W(n)
elsewhere), the exponent gamma of its Abelian lemma is **theta**, its
r(y) = log(1+e^(-y)) is **varrho(y)**, and its c_n in one proof is
**chi_n**. Renamed from manuscript 02: its delta(w) = 2 + w/(2(1+w)^2) is
**vartheta(w)** (it also writes delta_h for the endpoint coefficients, and
Parts I and III write delta for R_n - n/w), its linearized Poisson defect
script-E_n is **Xi_n** and its e_n is **bar-xi_n** (Part III's script-E_n
(30.8) is a different scalar defect), its abbreviation S_n = A_N(z_n) is
written out (S_n is also its model row sum), and its operator Q_n(u) is
**script-Q_n(u)** (Q_n = R_n/R_(N+2) is also used). The tempting false
readings: Part IV's P is an oscillation profile, Part V's P a truncation
order; Part V's T_n(L) is Part III's a_n J_n, not a Touchard polynomial;
Part V's s_n is the model ratio N_n/N_(n-1), not Part III's
n/w + c(w). In manuscript 01's Section 7 (printed in the A301981 report)
W(n) means n^(sigma*/3)(log n)^(m-1), not the Lambert function; in this
report W(n) is always the solution of w e^w = n.

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

## Changes made when Parts IV and V were added (batch 86, 4 October 2026)

- Parts IV and V are appended after Part III's Section 34 and before
  Appendix A, which still belongs to Part II (its one-line note now says
  it follows Parts III–V). No existing number moved (see Labels).
- Dated notes "[Batch 86, 4 October 2026.]": in Part I at the dated
  remark of Section 7.2, after Conjecture 8.1, and after the batch-76 note
  following Proposition 8.2 (the conjecture is proved in Part V, not yet
  independently reviewed; (8.7) remains open); in Part II after Research
  questions 23.1, 23.3 and 23.6 (answered in Part IV), after 23.2
  (proved in Part V, not yet independently reviewed, and still called
  open by manuscript 01) and after its Conclusion; in Part III after the
  discussion of Theorem 30.1 ((30.7) proved with q = 2), at the end of
  Section 32 (the uniform upper bound) and at the end of Section 34
  (items (i) and (iv) carried out). Part I's and Part III's statements
  that the conjecture is open "in this article" or "after Part III" are
  true of those Parts and are unchanged.
- The title, author and date lines and the abstract mention Parts IV and
  V (Part III's abstract sentence now reads "Part III leaves the finer
  conjecture open"); Table 2's caption points to Tables 5 and 6; the
  preamble adds `\Rea`, `\Ima` and `\Poisson`, declared as in the two
  manuscripts (Part IV uses the first two for its Re and Im; no existing
  macro changed); the bibliography adds Huang–Wang and records the
  batch-86 access dates of the OEIS, DLMF, Moser–Wyman and Python
  `decimal` entries.
- In Part IV: references to "the pinned report" point to Parts I–III,
  with Part II's Research question numbers; Proposition 36.1, a package of
  results of Parts I–II, names the theorems that prove them; file names
  are the shipped ones; the passages of the manuscript's Sections 1, 8
  and 9 about its other parts are printed with those parts. Five
  symbols renamed (above). Two dated notes inside Part IV (Sections 38.6
  and 41.1) record that manuscript 01 calls the normalization open and
  Part V proves it.
- In Part V: the displays of inherited results (Part III's (26.1)–(26.3)),
  the restated Lemma 28.1 with its proof, and repeated displays of (1.1),
  (28.1), (6.6) and the normalizer are replaced by references; labels
  quoted as text are cross-references; "the source report" points to the
  cited Parts. Its Theorem 12.1 is printed with a paragraph marking its
  proof of the fixed-order expansion as a second route to Theorem 39.1.
  Its Sections 13 and 14 are merged into Section 48, keeping the A088714
  rows of its Table 1 and its Table 2; its Section 14.3 (how to compile
  the delivered source) is replaced by this README; its A321941 questions
  15.6–15.8 are printed with that part, and 15.9 in both. Four symbols
  renamed (above). Dated notes in Section 48 relate its table to Parts
  III and IV.

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
- Parts IV and V come from two manuscripts that also contain other work,
  printed in three sibling reports: `enumerative-combinatorics/a343093-bridgeless-toroidal-maps`
  (manuscript 01, Section 2), Part II of
  `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301981-unitary-divisor-partitions`
  (manuscript 01, Section 7), and Part II of
  `congruences-and-valuations/a321941-asymptotic-coefficient-integrality`
  (manuscript 02, Sections 2–7). The last shares manuscript 02's driver,
  run records and source audit, which are shipped here.
- Part IV identifies mu as the rate-one free compound Poisson law with
  jump distribution nu (Section 37.1); its global inversion input is
  Huang–Wang's theorem on free Lévy processes, imported, not re-proved.
- Part V's normalizer and Bell asymptotic are Part I's (8.4) and (6.6);
  its Lambert W is the same Bell saddle as in Part III.
- No other repository file mentions A088714 or A088713 apart from the
  collection catalogue and the sibling reports above.
- Placement in this collection confers no formal status: no Lean or Rocq
  declaration states or proves any result of the five Parts.

## Build

From this directory, with a TeX installation providing pdfLaTeX:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

(or `make`). The table fragments in `data/` are input directly; no script
needs to run first. The committed PDF was built this way with MiKTeX: 101
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

**Part IV. Do not run its two programs in this directory.**
`code/04-densities-profile-verify_dynamics.py` always writes
`../data/dynamics_certificate.json` relative to itself (it has no output
option), and `code/04-densities-profile-verify_renewal.py` writes
`../data/renewal_checks.json` unless `--output` is given; in place they
would add unprefixed files to `data/`. Run them on a copy with the
delivered layout (Python 3.10 or later, standard library only; without
`-O`, since assertions implement the checks):

    mkdir -p /tmp/gdy/code /tmp/gdy/data
    cp code/04-densities-profile-verify_dynamics.py /tmp/gdy/code/verify_dynamics.py
    cp code/04-densities-profile-verify_renewal.py  /tmp/gdy/code/verify_renewal.py
    cd /tmp/gdy
    python3 code/verify_dynamics.py
    python3 code/verify_renewal.py

Rerun on 2026-10-04 (UTC) this way (Python 3.14.4, Windows, under 3 s):
both outputs equal the shipped `04-densities-profile-` JSON files after
removal of carriage returns (on Windows the scripts write CRLF). The
delivered run used Python 3.12.14.

**Part V. Do not run its programs in this directory.** The driver
`code/05-bell-norm-run_checks.py` copies every `code/*.py` beside it to a
temporary directory, runs the A321941 programs and the A088714 programs
under their delivery names, compares their outputs with
`data/<delivery name>`, and finally **overwrites
`data/verification_run.txt` and `data/verification_summary.json`** (its
two records, shipped here as `data/05-bell-norm-verification_run.txt`
and `…_summary.json`). It needs files from two reports. Reconstruct the
delivered layout on a copy (from this directory; `G` is the A321941
report):

    G=../../../congruences-and-valuations/a321941-asymptotic-coefficient-integrality
    mkdir -p /tmp/bnc/code /tmp/bnc/data
    for f in verify_complement normalization_diagnostics run_checks; do
      cp code/05-bell-norm-$f.py /tmp/bnc/code/$f.py; done
    for f in finite_certificate verify_sign independent_check large_order asymptotic_check; do
      cp $G/code/02-sign-$f.py /tmp/bnc/code/$f.py; done
    for f in endpoint_verification.json coefficients_600.txt normalization_80.json normalization_120.json; do
      cp data/05-bell-norm-$f /tmp/bnc/data/$f; done
    for f in sign_verification.json independent_check.json large_order_coefficients.json asymptotic_check.txt; do
      cp $G/data/02-sign-$f /tmp/bnc/data/$f; done
    cd /tmp/bnc
    python3 code/run_checks.py              # standard library only
    # optional SymPy cross-check (pinned in $G/data/02-sign-requirements-symbolic.txt):
    #   python3 -m pip install sympy==1.14.0 && python3 code/run_checks.py --symbolic

Rerun on 2026-10-04 (UTC) this way: without `--symbolic` (Python 3.14.4,
Windows) every check passed in 3.5 s; with `--symbolic` (Python 3.13.5,
SymPy 1.14.0, through `uv run --no-project --with sympy==1.14.0`) every
check passed in 13 s. The rewritten records differ from the shipped ones
only in the Python version, the per-check seconds and the temporary and
working paths. At placement the coefficient table was also regenerated
from scratch (`normalization_diagnostics.py` with a nonexistent
`--coefficients` path, which makes it compute and write the table): 211 s
on this machine, against "about 35 seconds" in the delivered README,
and byte-identical after removal of carriage returns. The individual
programs can also be run on such a copy, as the delivered README
describes: `verify_complement.py` prints JSON, and
`normalization_diagnostics.py` takes `--max-index`, `--precision`,
`--coefficients` and `--output`.

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
- Parts IV and V's shipped files are byte-identical to the delivery.
  Their rename maps are `code/<name>` → `code/04-densities-profile-<name>`
  and `data/<name>` → `data/04-densities-profile-<name>` for manuscript 01
  (`verify_dynamics.py`, `verify_renewal.py`, `dynamics_certificate.json`,
  `renewal_checks.json`), and `code/<name>` → `code/05-bell-norm-<name>`,
  `data/<name>` → `data/05-bell-norm-<name>` for manuscript 02, whose
  root-level `SOURCE_AUDIT.json` is `data/05-bell-norm-SOURCE_AUDIT.json`.
  Inside them the delivery names remain: the scripts read and write the
  names listed under Rerun, `run_checks.py` runs the A321941 programs by
  their delivery names (shipped in the A321941 report), and
  `verify_complement.py` names `oeis_research.tex`, which is not
  shipped.
- The JSON keys follow the manuscripts' notation, not the renamed one:
  `d_coefficients` in `04-densities-profile-renewal_checks.json` are
  Part IV's gamma_j; in `05-bell-norm-endpoint_verification.json`
  `endpoint_coefficients_d_…` are Part V's delta_h and
  `companion_endpoint_coefficients_e_…` its gamma_h; the normalization
  files' `r_n_minus_n_over_W_n` is R_n - n/W(n).
- `data/05-bell-norm-verification_run.txt` is the delivered log of the
  author's run. It records the author machine's temporary and working
  paths (`/tmp/oeis_verification_…`, `/workspace/scratch/…`); they are
  harmless (no credentials) and are kept byte-identical. The run and
  summary cover both parts of manuscript 02, including its A321941
  checks.
- No shipped script writes `data/05-bell-norm-normalization_precision_check.json`;
  it is a recorded comparison of the 80- and 120-digit runs.
- `data/05-bell-norm-SOURCE_AUDIT.json` describes manuscript 02 at its
  pin `b7e4f25b6`: it lists both of the manuscript's source reports and
  says that the deliverable changes no repository commit; that described
  the delivery.
- Manuscript 01's map program needs SymPy and mpmath; its two Part IV
  programs need only the standard library. Manuscript 01 ships no
  requirements file.
- Third-party material: the scripts embed short prefixes of OEIS A088714
  and A088713 for comparison (OEIS content is licensed CC BY-SA 4.0; the
  entries are cited in the bibliography). No third-party code, figures or
  text are reproduced; Huang–Wang, Moser–Wyman and the DLMF are cited,
  not copied.
- Manuscript 01, from which Part IV is taken, calls the finer Bell
  normalization open in its text and delivery README. It pins `eaf08931c`,
  six minutes after manuscript 02's pin `b7e4f25b6`; neither manuscript
  was in the repository at either pin and neither cites the other, so
  manuscript 01 did not know of manuscript 02's proof. Dated notes say so
  where its text calls the normalization open.
