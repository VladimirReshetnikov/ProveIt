# Permutations avoiding the vincular pattern 12–34 (A113226)

**Part I: exact enumeration and complete asymptotics. Part II: a record and cycle bijection, uniform asymptotics, and local large deviations. Part III: a diagonal-state route, block integrals and non-D-finiteness. Part IV: exact Hankel sectors at log 4 + 2πik**

A research report on OEIS A113226, the permutations avoiding the vincular
pattern 12–34. Bevan, Cheon and Kitaev (BCK) identify these with the
{3, 2+2}-free naturally labelled posets. The report is built from **four**
manuscripts. Two are from batch 77 (cluster P5) and two are from the
session bundle of batch 101.

- **Parts I–II (batch 77).** Both manuscripts are dated 1 October 2026,
  both pin ProveIt `63b9d6840`, and their author line is blank. Source 05
  is an addendum to source 04 ("The original A113226 report is unchanged",
  its delivery README). The two form a version pair, not a supersession,
  and both are printed in full.
- **Parts III–IV (batch 101, added 5 October 2026).** Report 87 is an
  independent answer to the same assignment as source 04, written the same
  day against an earlier pin. It is printed in full as Part III; its
  re-proofs are marked as second routes, and three things in it are new.
  Report 94 continues Report 87. It answers Part I's Question 4 (the
  exponentially small sectors) for every fixed sector, and is printed in
  full as Part IV.

| Source | Manuscript | Archive | Pin | Arrival | Placed | Printed as |
|---|---|---|---|---|---|---|
| 04 (base) | batch 77, manuscript 04: *Exact enumeration and complete asymptotics for permutations avoiding 12 34* (11-page PDF) | `a113226-asymptotics.zip` | `63b9d6840` | `096ee7b87` | `4f11bc9c0` | Part I: Sections 1–9 and Appendix A, with numbering unchanged |
| 05 (member) | batch 77, manuscript 05: *Refined enumeration of A113226: A record and cycle bijection, uniform asymptotics, and local large deviations* (9-page PDF) | `a113226-refined-addendum.zip` | `63b9d6840` | `096ee7b87` | `4f11bc9c0` | Part II: Sections 10–16 (source Section *n* is Section *n* + 9) |
| Report 87 | batch 101 (session bundle), Report 87: *Exact Enumeration and Complete Asymptotics for Vincular Pattern Avoidance*, 1 October 2026 (8-page PDF) | `Exact_Vincular_Avoidance_Asymptotics_Source.zip` (558,023 bytes) | `1512ef835` | `60f54ea06` | `f7c612c72` | Part III: Sections 17–24 (source Section *n* is Section *n* + 16, equation (*k*) is (*k* + 67)) |
| Report 94 | batch 101 (session bundle), Report 94: *Canonical Exponentially Small Sectors for Vincular Avoidance*, 2 October 2026 (11-page PDF) | `Canonical_Vincular_Exponential_Sectors_Source.zip` (384,547 bytes) | none (depends on Report 87's archive by SHA-256) | `60f54ea06` | `f7c612c72` | Part IV: Sections 25–34 and Appendix B (source Section *n* is Section *n* + 24, equation (*k*) is (*k* + 91), Appendix A is B) |

Two notes on the batch-101 sources:
- **Author lines.** Report 87's author line (also its PDF author field) is
  "Research note prepared for Vladimir Reshetnikov with OpenAI". Report 94's
  is "Research continuation of Exact Vincular Avoidance Asymptotics". Neither
  manuscript carries a "prepared for private review" line.
- **Pins and dependency.** Report 87's pin `1512ef835` (1 October 2026,
  08:38 PDT) is an ancestor of Parts I–II's pin `63b9d6840` (15:32 PDT the
  same day). Neither manuscript cites the other. Report 94 saw neither
  Parts I–II nor the repository. The SHA-256 it records for its input,
  `1e106596…c842` (in `data/07-sectors-dependency.json`), is the digest
  of Report 87's archive as delivered in `60f54ea06`. This was checked at
  intake and again at the write.

Status: AI-assisted and unrefereed. **Not formalized.** No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status (see "Relation to the
repository" below for the one generic lemma that is formalized). The
delivered review records describe separate proof reviews and independent
coefficient audits, all internal to the delivering pipelines. By their own
account they are not formal verification or conventional peer review.

## What the report proves, and what it does not claim

**Part I (source 04).** It derives the closed EGF
H(z) = exp{z/2 + q(3 arcsin q − π/2)/√(1−q²)}, with q = e^{z/2}/2, and the
first-order linear ODE for log H. It gives exact O(N²)-arithmetic
recurrences and identifies the cumulants as A136127 (shifted). It proves
the stretched-exponential form of BCK's Conjectures 13 and 14 with exact
constants:
A_n = D n! ρ^{−n} e^{3c n^{1/3}} n^{−5/6} (Σ a_j n^{−j/3} + O(n^{−(J+1)/3}))
for every fixed J, with ρ = log 4, c = (π²/(4ρ))^{1/3},
D = 2e^{−3}√(c/(3π)) ≈ 0.0357 (BCK's fitted estimate was near 0.032) and
β = −5/6. A finite Gaussian algorithm gives every a_j, and
a_1, …, a_4 are given exactly (Appendix A). The section on inversion gives
a controlled Lambert-W inverse and a ceiling envelope for the integer
threshold.

**Part II (source 05).** It marks the number of distinct nonempty strict
downsets (= the number of block pairs of BCK's word model) by u, and the
isolated elements by s. It proves:
- a record-to-cycle bijection that explains the exponential transform;
- exact component counts with the factor m!(m−1)!;
- a convergent local singular expansion, jointly analytic in u;
- a complex-uniform all-orders first-saddle expansion (Theorem 12.1);
- a global marking phase gap (Lemma 13.1);
- all-orders local large deviations for densities in compact subsets of
  (0, 1/2) (Theorem 14.1), with the stretched-exponential correction;
- mean and variance expansions, a central and a lattice local limit
  theorem, and asymptotic independence from a Poisson(log 4) number of
  isolated elements;
- a conditional Poisson(ρ(u)) law at atypical density, with an explicit
  n^{−2/3} correction and total-variation error O(n^{−2/3});
- Cov(K_n, J_n) = −1/2 + O(n^{−2/3}).

**Part III (Report 87).** Most of it is a **second route** to Part I; no
novelty over Part I is claimed for these results:
- Theorem 17.1 is the EGF of Part I's Theorem 1.1, written as
  A = exp ∫_1^{e^z} x dx/(x² − e^z x + e^z).
- Its recurrences are Part I's (3), (12) and (13).
- Its identification of T' with the EGF of A136127 goes through the
  Clark–Ehrenborg formula. Part I uses Testart's antidiagonal identity.
- Theorem 17.2 is Part I's (4). Its c_1, c_2 and c_3 are Part I's a_1, a_2
  and a_3: they are symbolically identical, as checked at the write.
- The inversion of Section 23 is a variant of Part I's Section 7.

New in it:
- the derivation from the permutations themselves. It uses continuous
  labels and the state (lowest ascent top, last label), with the diagonal
  kept separately; it does not use BCK's word bijection;
- integral forms of Elizalde's block functions b_k, c_k, and the exact
  identity Σ(b_k + c_k) = log A;
- **Proposition 22.1:** the EGF is differentially algebraic (an explicit
  second-order equation for A'/A) but **not D-finite**, so **A113226 is not
  P-recursive**. Every ρ + 2πik is an essential singularity on every branch.

The write adds three results of its own, each marked [write]:
- Remark 19.1 proves the integral forms. It also shows that Elizalde's
  index k is not Part II's block-pair grading;
- Remark 20.1 proves the "farther chord parts" estimate, with a loss that
  is exponential in n;
- Proposition 23.2 proves the displayed two-term reversion and the decay
  of every reversion term.

**Part IV (Report 94).** Everything in it is new except the k = 0 sector,
whose expansion re-proves Part I's theorem (C_0 = D, c_{0,j} = a_j). It
proves:
- a global single-valued branch A(z) = F(e^{z/2}) on ℂ minus the
  horizontal cuts ζ_k + [0, ∞), where ζ_k = log 4 + 2πik. The branch has
  period 4πi, not 2πi, and singular strength π at even k and 2π at odd k
  (Lemma 26.1);
- exact bank values on the cuts (Lemma 27.1);
- **Theorem 28.1:** A_n/n! = Σ_k H_k(n) exactly, for n ≥ 1, with
  contour-defined "full-cut" sectors H_k(n). The endpoint loop is kept. The
  sum converges absolutely, with |H_k(n)| ≤ C_r(|ζ_k| − r)^{−n−1} uniformly
  in k and n, and H_{−k} is the complex conjugate of H_k;
- **Corollary 28.2:** A_n/n! = H_0(n) + 2 Re H_1(n) + O(R^{−n}) for
  |ζ_1| < R < |ζ_2|;
- **Theorem 30.1:** a complete expansion of each fixed sector,
  H_k(n) = C_k ζ_k^{−n} e^{3κ_k n^{1/3}} n^{−5/6} (Σ c_{k,j} n^{−j/3} + …),
  with explicit c_{k,1} and c_{k,2};
- an additive first-pair formula with an absolute error, (131).

The write adds Remark 27.3 [write]: B(x) < 2e^{−x}. The delivered numerics
use this bound for their tail estimates but do not prove it. At intake,
Theorem 28.1 was also checked numerically, independently of the delivered
code, by contour quadrature for n = 6, 15 and 30.

**Not claimed** (every source disclaimer is kept in the article):
- convergence of any correction series;
- an exponentially complete transseries, Borel summability, resurgence or
  optimal truncation. The exponentially small contributions of the other
  singularities ρ + 2πik were excluded by Parts I–II. They are now given
  exactly by Part IV for each fixed k, but no expansion uniform in a
  growing k is claimed;
- a relative equivalent, or a lower bound, for the oscillating first pair
  near its zeros;
- a canonical analytic interpolation of A_n. Part IV's "canonical" means
  only its stated branch and horizontal cuts;
- certified finite-n error constants or threshold envelopes. The numerical
  comparisons and Part IV's quadratures are checks, not certificates;
- unconditional rounding of a truncated inverse;
- endpoint densities (k = o(n) or n/2 − k = o(n));
- an identification of Part II's statistics with a usual permutation
  statistic;
- a direct bijection to a previously named A136127 model;
- exhaustive priority. Every source's literature search is bounded;
- that BCK's fitted amplitude equals the limiting one.

The binary-word model, its bijections, BCK's insertion state, Elizalde's
block recurrences and envelopes, the Clark–Ehrenborg formula, A136127 and
its leading asymptotic, and the standard saddle and contour methods are
credited to their authors.

Status of Part I's research questions (dated notes in Section 9):
- Questions 1 and 2 are answered by Part II as far as the batch-77 note
  states. Part III asks Question 1 again, and asks for limit laws of the
  number of components, which no Part treats.
- **Question 4 is answered for every fixed sector by Part IV.** Growing k,
  optimal truncation and lower bounds remain open (Section 34).
- Question 3 (certified constants) remains open.

## Files

```
article.tex                                     the merged report, standalone LaTeX, internal bibliography
article.pdf                                     the compiled report, 54 pages (title and contents pages 1–3,
                                                "About this report" pages 4–7, Part I pages 7–18,
                                                Part II pages 18–26, Part III pages 27–40, Part IV pages 40–52,
                                                Appendices A–B pages 53–54, references page 54)
README.md                                       this guide
04-asymptotics-proof.md                         source 04's proof revision (SHA-256 5398b71c…, pinned by its review), as delivered
04-asymptotics-root-mathematical-review.md      source 04's proof review and independent a_1, a_2 check, as delivered
04-asymptotics-root-prior-art-check.md          source 04's source and known-transform verification, as delivered
05-refined-refined-proof.md                     source 05's expanded companion proof, as delivered
05-refined-mathematical-review.md               source 05's fresh independent mathematical audit, as delivered
05-refined-root-refinement-review.md            source 05's earlier pinned mathematical reviews, as delivered
05-refined-reproduction-review.md               source 05's replay environment, tests and limits, as delivered
05-refined-typesetting-review.md                source 05's report-to-proof and visual checks of its 9-page PDF, as delivered
05-refined-literature-screen.md                 source 05's attribution and overlap screen, as delivered
06-diagonal-exact_egf_proof.md                  Report 87's working derivation of the EGF and the block integrals, as delivered
06-diagonal-all_orders_proof.md                 Report 87's contour proof, coefficient algorithm and inversion (writes a for kappa)
06-diagonal-structural_corollaries.md           Report 87's differential-algebraic equation and non-D-finiteness argument
06-diagonal-source_status.md                    Report 87's bounded literature and repository screen (at pin 1512ef835)
06-diagonal-audit-structural_exact_review.md    Report 87's internal review of the EGF derivation
06-diagonal-audit-structural_all_orders_review.md  Report 87's internal review of the contour proof, inverse and corollaries
07-sectors-proof_notes.md                       Report 94's expanded proof note
07-sectors-source_status.md                     Report 94's bounded source comparison
07-sectors-audit-global_hankel_review.md        Report 94's internal audit of the global branch and the sector sum
07-sectors-audit-sector_remainders_review.md    Report 94's internal audit of the saddle, remainders and c_{k,2}
                                                (it cites the proof note as canonical_sectors_proof.md, see below)
07-sectors-qa-visual_review.md                  Report 94's rendering and clean-replay record of its 11-page PDF
code/04-asymptotics-exact_recurrence.py         source 04: cumulant/EGF recurrence, insertion rules (n <= 65), brute force (n <= 8);
                                                writes exact_values.json beside itself
code/04-asymptotics-asymptotic_coefficients.py  source 04: the finite Gaussian generator of a_j (default order 4)
code/04-asymptotics-validate_asymptotics.py     source 04: scaled residuals and inverse errors; reads exact_values.json
code/04-asymptotics-root_coefficient_audit.py   source 04: separate hand expansion of a_1, a_2 (prints JSON)
code/04-asymptotics-replay.sh                   source 04: the short replay (delivery names; reads exact_values.json)
code/04-asymptotics-build.sh                    source 04: its PDF build (builds the unshipped a113226-asymptotics.tex)
code/05-refined-refined_coefficients.py         source 05: first- and second-saddle coefficient algorithms (order 3)
code/05-refined-validate_refinement.py          source 05: exact refined rows, literal word counts, saddle samples;
                                                imports refined_coefficients; writes exact_rows.json and validation.json
code/05-refined-verify_record_bijection.py      source 05: record/cycle round trips through n = 8
code/05-refined-root_two_saddle_audit.py        source 05: separate hand expansion of b_1, b_2 (prints JSON)
code/05-refined-independent_b3_audit.py         source 05: separate degree-six check of b_3; reads refined_coefficients.json
code/05-refined-fresh-independent-audit.py      source 05: direct-poset audit through n = 8 and independent saddle expansions;
                                                hashes and reads unshipped files (see below)
code/05-refined-verify_package.py               source 05: whole-release verifier (needs the complete delivered package)
code/05-refined-verify.sh                       source 05: runs verify_package.py
code/06-diagonal-check_exact.py                 Report 87 (stdlib only): t_n and a_n through n = 600, BCK insertion tree and
                                                Elizalde block recurrences (71 terms), brute force and excedance sets (n <= 8),
                                                21 OEIS terms; writes exact_checks.json and counts_600.json beside itself
code/06-diagonal-check_saddle.py                Report 87: the Gaussian algorithm, c_0..c_3 exactly; writes saddle_checks.json beside itself
code/06-diagonal-check_structure.py             Report 87: exact elimination behind (89); writes structure_checks.json beside itself
code/06-diagonal-check_numerics.py              Report 87: the ratio table; reads counts_600.json and saddle_checks.json beside
                                                itself, writes numeric_regression.json
code/06-diagonal-build.sh                       Report 87: its PDF build (builds the unshipped delivered article.tex)
code/07-sectors-check_sector_coefficients.py    Report 94: circle and chord Gaussian checks of c_{k,0..2}; writes checks/symbolic_checks.json
                                                relative to the working directory
code/07-sectors-check_sector_numerics.py        Report 94: loop-plus-bank quadratures for k = 0, 1, 2 and n = 512, 4096;
                                                writes checks/numerical_checks.json relative to the working directory
code/07-sectors-replay.sh                       Report 94: clean replay (needs the unshipped delivered article.tex and requirements.txt)
code/07-sectors-build.sh                        Report 94: its PDF build (needs the unshipped delivered article.tex)
data/04-asymptotics-asymptotic_coefficients.json   source 04: constants and a_0..a_4, symbolic and 70-digit decimal
data/04-asymptotics-validation.json                source 04: sampled ratios, scaled residuals and inverse errors (n <= 1000)
data/04-asymptotics-root_coefficient_audit.json    source 04: output of the a_1, a_2 audit
data/04-asymptotics-quality_checks.json            source 04: release checks (pins the delivered tex, PDF and proof hashes)
data/04-asymptotics-repository-check.json          source 04: its ProveIt search at 63b9d6840 (no matches)
data/04-asymptotics-short_replay.log               source 04: recorded output of its short replay
data/04-asymptotics-requirements.txt               mpmath==1.3.0, sympy==1.14.0
data/05-refined-refined_coefficients.json          source 05: first- and second-saddle coefficients through order 3
data/05-refined-validation.json                    source 05: word counts, singular, moment, local-count, complex-u and
                                                   conditional samples (N = 400; also the rows for n <= 8)
data/05-refined-record_bijection_validation.json   source 05: 30,326 round trips through n = 8, one-cycle counts
data/05-refined-root_two_saddle_audit.json         source 05: output of the b_1, b_2 audit
data/05-refined-independent_b3_audit.json          source 05: output of the b_3 audit
data/05-refined-fresh-independent-audit.json       source 05: output of the fresh audit (pins its inputs' SHA-256)
data/05-refined-requirements.txt                   sympy==1.14.0, mpmath==1.3.0 (same pins as source 04's, other order;
                                                   byte-identical to Report 94's requirements.txt)
data/06-diagonal-exact_checks.json                 Report 87: output of check_exact (21 OEIS terms, counts' SHA-256)
data/06-diagonal-counts_600.json                   Report 87: a_0..a_600 (363,736 bytes; regenerated by check_exact in seconds)
data/06-diagonal-saddle_checks.json                Report 87: c_0..c_3, symbolic (in a for kappa) and 30-digit decimal
data/06-diagonal-structure_checks.json             Report 87: the equation for u = A'/A and the cleared third-order equation for A
data/06-diagonal-numeric_regression.json           Report 87: normalized ratios and truncations at n = 50, 100, 200, 400, 600
data/06-diagonal-audit-structural_first_correction.json  Report 87's audit: c_1 by an independent central-contour expansion
data/06-diagonal-requirements.txt                  Report 87: sympy>=1.12, mpmath>=1.3 (unpinned)
data/07-sectors-checks-symbolic_checks.json        Report 94: output of check_sector_coefficients
data/07-sectors-checks-numerical_checks.json       Report 94: output of check_sector_numerics (60 digits; tail bounds)
data/07-sectors-dependency.json                    Report 94: its input, Report 87's archive, by SHA-256
```

**Not shipped:**
- the four delivered PDFs (`article.pdf` is a build of the merged text);
- the four delivered READMEs (this README replaces them);
- the manuscripts of source 05 and of Reports 87 and 94 (their text is
  Parts II–IV);
- source 04's `manifest.json` (SHA-256 of 20 files, verified 20/20 at
  placement and retired);
- source 05's `SHA256SUMS` (verified 26/26 and retired);
- Reports 87 and 94's `manifest.json` (verified 21/21 and 16/16 at intake,
  and retired);
- source 05's `build.sh` (builds only its unshipped manuscript);
- Report 94's `requirements.txt`, which is byte-identical to the shipped
  `data/05-refined-requirements.txt`;
- the two heavy exact tables of Parts I–II, which are regenerable (next
  section).

All of these survive in the arrival commits: `096ee7b87` for Parts I–II and
`60f54ea06` for Parts III–IV. Source 04's manuscript was staged as
`article.tex` and is replaced by the merged text.

## Reconstructing the excluded data

Nothing of Reports 87 and 94 was excluded for size. Report 87's
`counts_600.json` is shipped, and `check_exact.py` regenerates it
byte-identically (after CRLF→LF) in a few seconds.

The two exact tables of Parts I–II are not shipped, because they are
heavy and regenerable (Vladimir, 2026-10-02). Both survive in the arrival
commit:

```
git show 096ee7b87:docs/incoming/a113226-asymptotics.zip      > a.zip
git show 096ee7b87:docs/incoming/a113226-refined-addendum.zip > b.zip
```

**Part I: A_n and the cumulants ℓ_n through n = 1000** (`exact_values.json`,
2,236,789 bytes, LF). Run on a copy, because the script writes beside
itself:

```
mkdir p1 && cp code/04-asymptotics-exact_recurrence.py p1/exact_recurrence.py
cd p1 && python3 exact_recurrence.py --n 1000 --check-n 65 --brute-n 8
```

This writes `exact_values.json` and took about 2.5 minutes (141 s) on the
intake machine under load. Under Windows Python the file is written with
CRLF line endings (2,238,803 bytes). After CRLF→LF it is byte-identical to
the delivered file; this was checked at intake and re-checked at the write.

**Part II: the refined triangle A(n, k) for n ≤ 400** (`exact_rows.json`,
18,071,638 bytes, one line). Copy the script and the module it imports:

```
mkdir p2 && cp code/05-refined-validate_refinement.py p2/validate_refinement.py
cp code/05-refined-refined_coefficients.py p2/refined_coefficients.py
cd p2 && python3 validate_refinement.py --n 400 --brute 8
```

This writes `exact_rows.json` and `validation.json` and takes several
minutes. The delivery reports about 4 minutes for the whole n = 400
validation, and its recorded `elapsed_seconds` is 214.6. The full n = 400
regeneration was not rerun here: its cost grows roughly like N⁵. The rows
were regenerated for n ≤ 200 at intake (112 s) and for n ≤ 120 at the write
(4 s, the `exact_rows` function alone). Both are value-identical to the
corresponding prefix of the delivered file. Under Windows Python the
single-line file gains one CR byte.

Both scripts write beside themselves, so always run them on copies. In
the shipped layout they would write unprefixed files into `code/`.

## Rerunning the checks

Python 3 with the pins in `data/04-asymptotics-requirements.txt` is
needed (equivalently `uv run --no-project --with sympy==1.14.0 --with
mpmath==1.3.0 python …`; `py` on this Windows machine). Every script finds
its inputs and writes its outputs **under the delivered names**. Sources 04,
05 and Report 87 write **beside themselves**, and Report 94 writes
**relative to the working directory**. So none of them runs from `code/` as
shipped. Run them on a copy with the delivered layout. That copy is either a
fresh extraction of the archives or the shipped files with their prefix
stripped:

- **Part I short replay** (`code/04-asymptotics-replay.sh`). It reruns the
  generator, the audit and `validate_asymptotics.py`, then checks the
  exact prefix n ≤ 100, the insertion rules (n ≤ 40) and brute force
  (n ≤ 8). It **reads `exact_values.json`**, as does
  `validate_asymptotics.py`. In a fresh extraction of `a.zip` the file is
  present; in a copy of the shipped files, regenerate it first (previous
  section). The replay overwrites `asymptotic_coefficients.json`,
  `root_coefficient_audit.json` and `validation.json` in its directory,
  so never run it in place.
- **Part II verifier** (`code/05-refined-verify_package.py`, run by
  `code/05-refined-verify.sh`). It checks the delivered package as a
  whole. It aborts without `SHA256SUMS` and requires the manuscript, the
  PDF, the README, `build.sh` and `exact_rows.json`, none of which is
  shipped. **Run it in a fresh extraction of `a113226-refined-addendum.zip`
  from `096ee7b87`** (`b.zip` above): `bash verify.sh`, or
  `bash verify.sh --full --build` for the n = 400 rows and the PDF rebuild.
  Byte-identity of the rebuilt PDF is promised only on the delivery's TeX
  toolchain.
- **Part II fresh audit** (`code/05-refined-fresh-independent-audit.py`).
  It hashes `refined-proof.md`, `a113226-refined-addendum.tex`,
  `refined_coefficients.json` and `exact_rows.json`, and reads the last
  two. Run it in the fresh extraction too.
- **Single Part II programs.** `refined_coefficients.py --order 3`,
  `root_two_saddle_audit.py`, `independent_b3_audit.py` (reads
  `refined_coefficients.json`) and `verify_record_bijection.py` run in a
  copy that holds only the unprefixed code and that JSON file.
- **Part III (Report 87).** Make a flat copy with the prefix stripped, and
  run the four checkers in this order. `check_numerics.py` reads the
  outputs of the first two.

  ```
  mkdir p87
  for f in check_exact check_saddle check_structure check_numerics; do
    cp code/06-diagonal-$f.py p87/$f.py; done
  cd p87
  python -O check_exact.py        # stdlib only; writes exact_checks.json, counts_600.json
  python -O check_saddle.py       # writes saddle_checks.json
  python -O check_structure.py    # writes structure_checks.json
  python -O check_numerics.py     # reads the two files above; writes numeric_regression.json
  ```

  Compare each output with `data/06-diagonal-<name>` using
  `diff --strip-trailing-cr`. At intake all four ran, under sympy 1.14.0
  and mpmath 1.3.0, in 20 s, 54 s, 41 s and 6 s, and all five outputs were
  identical up to CRLF. At the write, `check_exact.py` was rerun by this
  route (7 s): its two outputs were again identical up to CRLF. Report 87's
  own `requirements.txt` (`data/06-diagonal-requirements.txt`) is
  unpinned. The pins above are the tested ones.
- **Part IV (Report 94).** Copy the two checks and run them from the copy.
  They create `checks/` in the working directory.

  ```
  mkdir p94
  cp code/07-sectors-check_sector_coefficients.py p94/check_sector_coefficients.py
  cp code/07-sectors-check_sector_numerics.py     p94/check_sector_numerics.py
  cd p94
  python -O check_sector_coefficients.py   # writes checks/symbolic_checks.json
  python -O check_sector_numerics.py       # writes checks/numerical_checks.json
  ```

  At intake they took 49 s and 113 s, and both outputs were identical to
  `data/07-sectors-checks-*.json` up to CRLF. At the write the symbolic
  check was rerun by this route (12 s), with the same result. Report 94's
  `replay.sh` and `build.sh` need the delivered `article.tex` (not shipped).
  Run them only in a fresh extraction on a POSIX host:

  ```
  git show 60f54ea06:docs/incoming/Canonical_Vincular_Exponential_Sectors_Source.zip > c.zip
  unzip c.zip && cd Canonical_Vincular_Exponential_Sectors_Source && bash replay.sh
  ```

  `replay.sh` copies everything into a fresh temporary directory
  (`${TMPDIR:-/tmp}`, or its first argument), so it does not write into
  the extraction. `build.sh` sets `TEXMF` to
  `{/usr/share/texlive/texmf-dist,/usr/share/texmf}` when the first of
  these exists. These are generic Linux TeX locations, not paths of the
  delivering machine. It then builds a private format under `build/`.
  Report 87's `build.sh` likewise compiles its delivered `article.tex` and
  runs only in a fresh extraction of
  `Exact_Vincular_Avoidance_Asymptotics_Source.zip` from `60f54ea06`.
- **CRLF on Windows.** Every program writes its JSON with Python's
  text-mode `write_text`. Under Windows Python the outputs therefore have
  CRLF line endings. Source 04's README promises byte-identical JSON
  outputs; compare after converting to LF (`diff --strip-trailing-cr`), or
  run under a POSIX Python. The delivered verifiers compare parsed JSON,
  not bytes, and are unaffected.

The checks at intake (copies under the intake scratch area) were:
- source 04's full exact regeneration: PASS, byte-identical after CRLF→LF;
- source 05's row regeneration: value-identical through n = 200;
- Reports 87 and 94: every delivered check, PASS, outputs identical up to
  CRLF.

The other suites of sources 04 and 05 were not rerun at intake. Two things
were checked independently at intake. First, the EGF's Taylor
coefficients reproduce 1, 1, 2, 6, 23, 107, 585, 3669, 25932. Second, the
residual (r − 1 − a_1 n^{−1/3}) n^{2/3} at n = 250, 500, 1000 (0.886,
0.907, 0.923) approaches a_2 = 0.9816, with the drift expected from
a_3 = −0.530. At the write, every u = 1 specialization stated in the
article's notation table was rechecked to 40 digits: Part II's ρ, c, D, K,
q, s_1, s_2, r_1, a_1, a_2, α(1) and V(1) against Part I.

For Parts III–IV the intake also ran its own code, independent of the
delivered checks:
- Theorem 28.1 by contour quadrature of H_k(n) for 0 ≤ k ≤ 6. The relative
  error of the truncated sum was 3.5·10⁻¹², 3.5·10⁻²⁶ and 1.5·10⁻³⁹ at
  n = 6, 15 and 30 (the note after Corollary 28.2);
- the printed sector constants;
- the inverse comparison of Proposition 23.2;
- the residual of (89).

At the write, the following were checked:
- the identity of c_{k,2} at k = 0 with Part I's a_2, symbolically;
- the constants κ_k, C_k, c_{k,1} and c_{k,2} for k = 0, 1, 2, numerically;
- Remark 19.1's identity I_{m,n}'' = mn e^z I_{m−1,n−1}, numerically for
  six (m, n) pairs;
- sup B(x)e^x ≈ 0.25, numerically (Remark 27.3 proves the bound 2).

**OEIS data.** The 21 initial terms of A113226 embedded in
`code/06-diagonal-check_exact.py` and recorded in
`data/06-diagonal-exact_checks.json` are OEIS data, licensed CC BY-SA 4.0.
They are compared with values computed by the program.

## Labels and numbering

Every label carries the prefix `vav:`. Part II's labels carry `vav:rf:`,
Part III's `vav:dg:` and Part IV's `vav:hk:`.

For Parts I–II, the staged `article.tex` (source 04 as delivered) had 39
unprefixed labels. All 39 are kept with the prefix `vav:`. Source 05's 34
labels are kept with the prefix `vav:rf:`. The batch-77 write added the
following:
- 8 `vav:sec:*` labels on Part I's unlabelled sections;
- 8 `vav:rf:sec:*` labels on Part II's sections and on its one subsection;
- `vav:part:one`, `vav:part:two` and `vav:tab:notation`.

That made 92 labels. The batch-101 write added 101, for **193** in all
(pattern `\\label(\[[^]]*\])?\{`):
- **Part III (`vav:dg:`, 42).** Report 87's 28 labels are kept with the
  prefix. The write added 14 more:
  - the Part label;
  - the notation table;
  - 9 section and subsection labels, among them `vav:dg:sec:questions`;
  - the three write results `vav:dg:rem:elizalde`, `vav:dg:rem:farchord`
    and `vav:dg:prop:reversion`.
- **Part IV (`vav:hk:`, 59).** Report 94's 49 labels are kept with the
  prefix. The write added 10 more:
  - the Part label;
  - the notation table;
  - 6 section labels;
  - `vav:hk:app:dependency`;
  - `vav:hk:rem:bankbound`.

No existing label is renamed, renumbered or removed. The `.aux` file of
the new build was compared with a build of the committed text: all 92
existing labels keep their numbers.

**Part I keeps its delivered numbering exactly.** Its Sections 1–9,
equations (1)–(36), Theorem 1.1 and Appendix A are unchanged. The front
section "About this report" is unnumbered, and Part I's appendix is placed
after Parts II–IV. **Part II:** source Section *n* is Section *n* + 9, and
source equation (*k*) is equation (*k* + 36). Its Theorem 1, Lemma 1 and
Theorem 2 are Theorem 12.1, Lemma 13.1 and Theorem 14.1, because theorems
and lemmas share Part I's section-based counter. The `.aux` numbers of all
73 batch-77 delivered labels were compared with builds of the two delivered
sources: there were 0 mismatches against this rule. The delivered reviews
of source 05 cite its own equation numbers, so for example its "formula
(30)" is equation (66) here.

**Part III:** source Section *n* is Section *n* + 16 and source equation
(*k*) is equation (*k* + 67). Its Theorems 1.1, 1.2, Proposition 6.1 and
Theorem 7.1 are Theorems 17.1, 17.2, Proposition 22.1 and Theorem 23.1.
**Part IV:** source Section *n* is Section *n* + 24 and source equation
(*k*) is equation (*k* + 91). Its Lemmas 2.1, 3.1, Theorem 4.1,
Corollary 4.2 and Theorem 6.1 are Lemmas 26.1, 27.1, Theorem 28.1,
Corollary 28.2 and Theorem 30.1, and its Appendix A is Appendix B. The
`.aux` numbers of all 77 labels of Reports 87 and 94 were compared with
builds of the two delivered manuscripts: there were 0 mismatches against
these rules. The write's own remarks and proposition come after the
source's numbered items in their sections, so no source number moves.

**One displaced number.** Part I's Appendix A has two unlabelled displays
(a_3 and a_4). They followed Part II's equations as (68)–(69) and now follow
Part IV's as (132)–(133). This is the only number of the existing text that
changed. Nothing cites them.

## Merge decisions and notation

- The Parts are printed one after the other. Part II re-derives Part I's
  analysis at a general marking parameter u, and its u = 1
  specializations are kept where Part II states them; nothing is deduplicated
  away.
- Parts III and IV are separate Parts, not merged into Part I. Part I is
  already written, and Report 87's proofs differ from Part I's.
  - Each re-proof in Part III is marked as a second route, naming the Part I
    label it re-proves (the note at the head of Part III).
  - Report 87's pin is earlier than Part I's, but Part III is printed
    second. No priority between the two is asserted.
- The bibliographies are merged.
  - Part II's keys `BCK`, `OEIS`, `Elizalde`, `A136127` and `Testart` point
    to Part I's entries for the same works. Its `ProveIt` entry is added as
    `proveit`.
  - Reports 87 and 94's keys for OEIS A113226, BCK, Elizalde and A136127
    likewise point to Part I's entries. Report 94's revision and URL details
    are kept in a note in Section 33.
  - New entries: `clark`, `excedance`, `fs` and `proveitdg` (Report 87;
    `clark`, `fs` and `proveitdg` are listed but never cited by the
    source), and `hkprior` (Report 94's entry for Report 87, which says it
    is printed as Part III).
- **Renamed symbols** (each is disclosed in the article's tables):
  - Part II: Stirling numbers `S(n,m)` are printed `{n brace m}` (they
    clashed with the analytic factor `S(w,u)`);
  - Part II: `T = coth((ρ−w)/4)` is printed `𝒯` (it clashed with `T(x,y,u)`);
  - Part II: the compact parameter interval `U` is printed `𝒰` (it clashed
    with Part I's Gaussian variable `U`);
  - Part IV: the endpoint circle `C_k(r)` is printed `𝒞_k(r)` (it clashed
    with the amplitude `C_k` and the constant `C_r`).

  No normalization changed.
- Part II's phrase "the original report" is replaced in four places by
  "Part I", with a cross-reference.
- Part II's `\,\dd x` is printed with Part I's `\dd` macro, which already
  contains the thin space. Part IV's `\dd` is identical to Part I's.
- The preamble merges all sources' packages and macros. It adds `corollary`
  and the Part III–IV macros (`\ee`, `\Rea`, `\Ima`, `\atanh`, `\asinh`,
  `\acosh`, `\cO`, `\C`, `\Z`, `\R`), none of which clashes. It also allows
  URL breaks at `-` and `_` for the file names in the notes.
- Table 1 of the article lists every letter whose meaning changes between
  Parts I and II, or inside Part II, with the false reading beside the true
  one.
  - The letters are a, b, L, ℓ, S, s, T, U, X, q, h, N, α, d, f, C, P, R,
    M, J, K_n and k.
  - It also gives the u = 1 identities ρ(1) = log 4, c(1) = c,
    D(1) = D, K(1) = K, a_j(1) = a_j and L_n(1) = ℓ_n.
- Tables 2 and 3 do the same for Parts III and IV against the earlier
  Parts. The most important clashes:
  - Report 87's `C` is Part I's amplitude `D` (Part I's `C` is 3c);
  - Report 87's `κ` and `c_j` are Part I's `c` and `a_j`, and Report 87's
    `a_n` are Part I's `A_n`;
  - Report 87's `b_n` counts A136127, but Report 94's `b_n` is a_n/n!;
  - Report 94's `H_k(n)` is a number, not Part I's `H(z)`;
  - Report 94's `g_k` is a strength, not Part I's Puiseux `g_j`;
  - `δ` is ρ − z or ζ_k − z in Parts III–IV, not Part I's n^{−1/3}.
- Dated write notes, of two dates:
  - **2 October 2026, batch 77P5** (Parts I–II):
    - after Part I's citation of Elizalde (the sibling report);
    - at the end of Part I's Section 1 (Part II extends Theorem 1.1);
    - after Part I's open bijection question in Section 3 (answered by
      Section 10.1, narrower form open);
    - at the end of Section 7 (transseries volume and staircase theorem);
    - in Section 8 (shipped names, excluded data);
    - in Section 9 (repository context; the status of questions 1–4);
    - at the start of Part II;
    - in Section 16, three times (excluded rows and shipped names, the
      "original release", repository context).
  - **5 October 2026, batch 101**, in the existing text:
    - in the abstract;
    - in "About this report" (sources, choices, notation, status);
    - at the end of Section 1 (Parts III–IV re-prove and complete
      Theorem 1.1);
    - in Section 3 (the second route to A136127);
    - in Section 4 (the singularities are genuine; the global branch);
    - at the end of Section 7 (Part III's inversion);
    - in Section 9 (Question 4 answered for fixed k; status of 1–3);
    - in Section 16 (the other sectors at u = 1);
    - in Appendix A.
  - **5 October 2026, batch 101**, in Parts III–IV: notes at their heads
    (provenance, numbering, reading conventions) and after the results they
    comment on.

  No statement of any source is changed.

## Standing rule: unproved and wrong claims

No claim of Reports 87 and 94 was found wrong. Their unproved items are
collected in the further-questions sections. Section 24.1 holds Report
87's; Section 34, with a dated note, holds Report 94's and the open parts
of Part I's Questions 3 and 4. The items:
- **Report 87:**
  - a direct bijection for A' = BA (open; Part II's separated cycles
    explain the transform on the poset side);
  - the exponentially smaller sectors (answered for fixed k by Part IV);
  - limit laws for the number of components of A = e^T (open; Part II
    marks block pairs and isolated elements, not cycles);
  - that every finite truncation of the reversion (90) is justified. This
    is open in general; Proposition 23.2 [write] proves the displayed
    truncation and the decay of every term;
  - the "farther chord parts" estimate. This is proved by Remark 20.1
    [write], so it is not open.
- **Report 94** (its own five questions):
  - expansions uniform in a growing sector index;
  - late coefficients, optimal truncation, Borel summability and
    resurgence;
  - certified (interval) values of the sectors;
  - lower bounds for the oscillating pair;
  - other EGFs with the same structure.
- **The write** adds one question: the sectors of Part II's marked
  function at u ≠ 1.

## Relation to the repository and to neighbouring reports

- **Sibling report on A113227.**
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113227-powered-catalan/`
  is built from batch-77 manuscripts 57 and 56 of cluster P2, and was
  written concurrently with this report. It treats the powered Catalan
  numbers, the avoiders of the sibling vincular pattern 1–23–4.
  - Elizalde (2006) bounded both sequences without a precise equivalent.
    The two reports supply the precise asymptotics for the two patterns,
    by unrelated methods: here an EGF and a stretched-exponential saddle,
    there a positive Bessel spectral representation. They are siblings,
    not duplicates.
  - Neither pair of manuscripts cites the other, because they are
    contemporaneous. Part I does, however, cite Callan's paper on the
    1–23–4 pattern (its Section 9) for the fast recurrence. So "neither
    cites the other" holds for the manuscripts, not for the patterns'
    literature.
  - The two were kept as separate reports, one sequence per report as
    elsewhere in this collection, rather than as Parts III–IV of this one.
    Reports 87 and 94 concern A113226 only, so they are Parts of this report.
- **Transseries volume.** The Lambert-W inverse and the integer-threshold
  envelope of Section 7 re-derive the inversion apparatus of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
  namely `p0:thm:lambert-core`, `p0:thm:perturbed-inversion` and
  `p0:thm:staircase`. So do Part III's Theorem 23.1 (staircase separation
  for the finite models f_K) and its gamma-core reversion (90) (perturbed
  inversion). No novelty is claimed there. Report 87's source screen names
  the volume *Combinatorial Transseries Inverses*
  (`Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/`)
  at its pin as background; that volume has no A113226 target.
- **Formal status.** No statement about A113226 is formalized. The only
  related formal statements are generic: the separation clause of the
  staircase theorem, and its failure for arbitrarily small error. These
  are the Lean theorems `Fabius.staircase_separation` and
  `Fabius.staircase_separation_fails` in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
  They say nothing specific to this sequence. Proposition 22.1
  (non-D-finiteness) and Part IV's sector theorems are not formalized.
- **Repository searches in the sources.**
  - Sources 04 and 05 searched ProveIt at `63b9d6840` and found nothing.
    Report 87's source screen (`06-diagonal-source_status.md`) found no
    A113226 or A136127 target at `1512ef835`. That was true at that pin;
    the report was placed later, in `4f11bc9c0`.
  - The pins are kept as provenance. Dated notes record that the repository
    now contains this report and the sibling report.
  - No other report treats A113226, A136127 or the BCK model (`rg` of the
    repository at the batch-77 write). No other package of the session
    bundle mentions A113226 (intake search).

## Delivered files that use delivery names or name unshipped files

- `code/04-asymptotics-replay.sh`, `code/04-asymptotics-build.sh`,
  `code/05-refined-verify.sh`, `code/05-refined-verify_package.py` and
  `code/05-refined-fresh-independent-audit.py` all run on the delivered
  unprefixed names.
  - `build.sh` compiles `a113226-asymptotics.tex`, which is not shipped
    (it is `article.tex` before the merge). It also contains a branch for
    the delivery's own environment (`/tmp/hamiltonian-rank-build`).
  - `verify_package.py` requires the unshipped `SHA256SUMS`, PDF,
    manuscript, README, `build.sh` and `exact_rows.json`.
- `04-asymptotics-proof.md` and source 04's review use delivery names.
  `data/04-asymptotics-quality_checks.json` pins the SHA-256 of the
  delivered manuscript and of its 11-page PDF, neither of which is shipped
  (`article.tex` is the merged text). Its proof hash `5398b71c…` matches
  the shipped `04-asymptotics-proof.md`.
- `data/04-asymptotics-short_replay.log` is the delivery's own run.
- `data/05-refined-fresh-independent-audit.json` records several SHA-256
  values:
  - of the excluded `exact_rows.json` (`2a155664…`);
  - of the unshipped manuscript (`b4fe1a9e…`);
  - of `refined-proof.md` (`c35244db…`, equal to the shipped
    `05-refined-refined-proof.md`);
  - of `refined_coefficients.json` (`49ea4010…`, equal to the shipped
    `data/05-refined-refined_coefficients.json`).

  The pins on the excluded and unshipped files refer to the copies in the
  arrival commit. `05-refined-mathematical-review.md` pins the same
  manuscript, and `05-refined-typesetting-review.md` pins it and the
  delivered PDF (`b15521c0…`). The manuscript and PDF hashes in
  `data/04-asymptotics-quality_checks.json` (`f1c8aa69…`, `9c78222a…`) are
  those of source 04's delivered files.
- Source 05's reviews cite the delivered nine-page PDF's equation and
  section numbers (see "Labels and numbering"). Its reproduction review
  describes the complete package with `SHA256SUMS` and the exact rows.
- **Report 87.**
  - Its markdown records and reviews name the delivered files
    `exact_egf_proof.md`, `all_orders_proof.md` and `article.tex`.
  - Its four checkers read and write the unprefixed names beside
    themselves (`exact_checks.json`, `counts_600.json`,
    `saddle_checks.json`, `structure_checks.json`,
    `numeric_regression.json`). The article's "`saddle_checks.json`" is
    `data/06-diagonal-saddle_checks.json`.
  - `code/06-diagonal-build.sh` compiles the unshipped delivered
    `article.tex`.
- **Report 94.**
  - `07-sectors-audit-sector_remainders_review.md` says it was audited
    against `canonical_sectors_proof.md`. That is a pre-delivery name of the
    shipped `07-sectors-proof_notes.md`; no file of that name was
    delivered.
  - `07-sectors-audit-global_hankel_review.md` cites
    `sector_remainders_review.md`.
  - `07-sectors-source_status.md` cites `dependency.json`,
    `all_orders_proof.md` and `article.tex` of Report 87.
  - `07-sectors-qa-visual_review.md` describes the unshipped 11-page PDF.
  - `code/07-sectors-replay.sh` copies the unshipped `article.tex` and
    `requirements.txt`.
  - `code/07-sectors-check_sector_numerics.py` states in a comment that
    B(x) ≤ 2 exp(−x), without proof. Remark 27.3 proves it.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses pdfLaTeX (MiKTeX here) and needs the `lmodern`, `microtype`,
`float`, `array` and `booktabs` packages. It gives 54 pages with 0 errors,
0 warnings (no undefined references or citations, no multiply defined
labels, no duplicate destinations) and no overfull or underfull boxes.
Build in a scratch directory and keep only `article.pdf`.
