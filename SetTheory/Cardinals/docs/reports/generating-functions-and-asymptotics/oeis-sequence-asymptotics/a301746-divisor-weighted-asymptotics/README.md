# Divisor-Weighted Partition Products and Assemblies

**Logarithmic hierarchies, exact-saddle expansions and inverse localization
for OEIS A301746 (`∏(1+q^k)^(d(k)^2)`) and A294363
(`n![z^n] exp(Σ d(k) z^k)`)**

A research report in two Parts, built from two manuscripts of batch 77, both
dated 1 October 2026 and merged on 2 October 2026.

| Source | Batch-77 manuscript | Archive (arrival commit `096ee7b87`) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| A301746 | 50 | `oeis-divisor-square-asymptotics-result.zip` (main file `article/divisor-square-partitions.tex`, 10 pages; author line empty) | none: no ProveIt commit is named; its approval records name only the producer's working directory `/workspace/shared/oeis-a301746-research` | `aa7345800` | Part I (base), Sections 1–7 |
| A294363 | 49 | `oeis-divisor-assembly-result.zip` (main file `divisor_assembly_asymptotics.tex`, 9 pages; author line "Research note for OEIS A294363") | `f7e7d8607` (`search_snapshot_commit` of `data/49-assembly-provenance.json`; an ancestor of the placement commit) | `aa7345800` | Part II, Sections 8–15 |

**Status:** AI assistance unstated (neither delivery names an author or a
tool); unrefereed; not formalized. Exact integer recurrences and exact formal
reversions check the displayed coefficients; the high-precision saddle
comparisons are diagnostics, not interval-certified bounds, and no proof rests
on them.

## What it proves

**Part I (A301746, manuscript 50).** `a_n = [q^n] ∏_{k≥1}(1+q^k)^(d(k)^2)`.

- Proposition 2.1: the cumulants of the tilted size have the expansion
  `κ_r(t) = t^(-r-1) P_r(L) + O(t^(-σ-r))`, `L = log(1/t)`, from the
  fourth-order pole at `s = 1` of `Γ(s)(1-2^(-s))ζ(s+1)ζ(s)^4/ζ(2s)`; the
  cubic `P` has explicit constants `B_1, B_2, B_3` (Stieltjes constants and
  `(log ζ)^(j)(2)`).
- Theorem 3.1: a relative expansion of `a_n` to every fixed order in exact
  saddle cumulants, remainder `O_R(M^(-R-1))`, `M = t^(-1)L^3`; the minor
  arcs need only one slot per active size (Lemma 3.2).
- Proposition 4.1: `a_{n+1} > a_n` for every `n ≥ 1` (Euler-product
  factorization with exponents `(2a+1)d(m)^2 ≥ 1`).
- Theorem 4.2 and Corollary 4.3: the integer threshold `N(y)` lies between
  two ceilings of width `O(t^R/L^(3R+3))` around an explicit positive-real
  inverse, with the first inverse shift `9/(4L^3)`.
- Theorem 5.2: `log a_n = √n H^(3/2)/(2√6) {1 + F_1/H + F_2/H^2 + F_3/H^3 +
  O((log H)^4/H^4)}`, `H = log n`, which **proves Kotěšovec's 2018
  conjecture** `log a_n ~ √n (log n)^(3/2)/(2√6)` recorded in A301746, with
  a constructive expansion to every further order; Theorem 6.1: the matching
  inverse `N(y) = 3Y^2/Z^3 {1 + I_1/Z + …}`, `Y = log y`, `Z = log Y`.

**Part II (A294363, manuscript 49).** `b_n = a_n/n! = [z^n] exp(Σ d(k) z^k)`.

- Theorem 8.1: `a_n/n! ~ M(n)` with a shifted Lambert saddle
  (`N = n - 1/144`, `u = W(2e^(2γ+2)N)/2`) and explicit first and second
  relative corrections `R_1(u)`, `R_2(u)`.
- Theorem 10.1: an exact-saddle Poisson Edgeworth expansion to every order;
  Theorem 11.1: an all-orders expansion with `R_j ∈ ℚ(u)` and a finite
  recurrence (computed exactly through `j = 5`).
- (12.4): `log(a_n/n!) = √(2n log n) + …`, which proves the OEIS
  logarithmic statement (the Part stresses that this is far weaker than
  Theorem 8.1).
- Theorem 13.1: a factorial-core inverse to every order around
  `X = y/W(y/e)`; Corollary 13.2: `n = X - S(X)/log X + 1/4 + o(1)` for
  exact inputs `y = log a_n`; smooth envelopes for the integer threshold and
  strict increase of `a_n`.

## What is not claimed

Every non-claim and priority caveat of both deliveries is kept in the
article. In brief:

- **No priority for the methods.** Part I: "We give a self-contained
  treatment of this sequence and do not claim that the underlying saddle or
  Mellin methods are new" (credits Bridges–Brindle–Bringmann–Franke,
  Berndt–Robles–Zaharescu–Zeindler, Ahmadi–Gómez-Aíza–Ward). Part II: "These
  are classical analytic methods applied to this particular assembly, and no
  priority claim is made"; targeted searches on 1 October 2026 "did not
  locate this sequence-specific multiplicative expansion or inverse; priority
  remains unverified".
- Part I: no convergence of the formal hierarchies, no complete
  exponentially improved transseries; the contributions of zeta zeros at
  `s = ρ/2` are not represented by the cubic model and are left open; a
  multiplicative equivalent cannot be obtained by exponentiating a finite
  logarithmic truncation. The inverse error constants are asymptotic
  existence constants, not optimized thresholds. No external publication or
  submission is asserted (delivery README).
- Part II: no Lean formalization, no effective constants for the remainders,
  no exponentially improved expansion of secondary root-of-unity
  contributions, no new general method; "a broad fixed-σ_k extension … is not
  counted as an additional result"; no effective starting index for the
  rounding of Corollary 13.2; no unconditional ceiling rule near a jump.
- Open questions: Part I's arithmetic sectors and zeta-zero terms
  (Section 7); Part II's three questions (Section 15: effective enclosures,
  secondary arcs, a bivariate local limit theorem). No source of this batch
  answers any of them.
- **Inversion: no novelty.** The Lambert-W starts of both Parts are the
  exact Lambert core `p0:thm:lambert-core` of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  (Part I: `a = 2, b = 3` forward and `a = 1, b = 3` inverse; Part II:
  `a = 2, b = 1` for the saddle and `a = b = 1` for the factorial core), with
  corrections by `p0:thm:lambert-centered`; Part II's reversion coefficients
  are `p0:thm:LB` / `p0:thm:core-reversion` (its Rouché–Cauchy remainder is
  its own); the two-ceiling brackets of both Parts are `p0:thm:staircase`
  with `p0:thm:backward-error`. Six dated `[write]` notes say so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status. Neither
manuscript ships or uses Lean or Rocq.

**Before this report** no ProveIt file mentioned A301746 or A294363 (checked
with `git grep` at the parent of the placement commit). Part II's sentence
"The already developed divisor-square exclusion product A301746 is a
different model" refers to the sibling manuscript 50, now Part I; a `[write]`
note says so.

**Neighbouring reports** (same collection, `oeis-sequence-asymptotics/`):

- `a022629-distinct-partition-norms` (products `∏(1+k^α q^k)`) uses the same
  consecutive-block inequality (its Lemma `dpn:lem:block` = Lemma 3.2 here)
  and the same Gaussian-moment Edgeworth sum (`dpn:thm:saddle`). Its fifth
  source, batch-77 manuscript 51 (same day, same style), states Part I's
  `E_R` formula and block lemma again for `∏(1+k^α q^k)^(k^β)`. Part I's
  independent audit `50-divsq-ind-AUDIT.md` (line 29) cites "the
  independently reviewed A022629 proof": that is manuscript 51's audit,
  shipped as `a022629-distinct-partition-norms/77-51-fp-ind-AUDIT.md`.
- `a301981-unitary-divisor-partitions` (`∏(1∓q^m)^(∓σ*(m))`) has a zeta
  denominator `ζ(2s-1)` whose zero-poles refute the recorded OEIS
  equivalents there; a `[write]` note in Part I, Section 7, compares the
  location of the zero-poles (here `0 < ℜs < 1/2`, so they do not affect
  Part I's theorems). The comparison was added at the merge.

## Labels

Every label carries the prefix `dwa:`: Part I's 52 delivered labels became
`dwa:sq:…`, Part II's 38 became `dwa:as:…`, and 11 were added in writing (two
Part labels, five front-matter sections, and the section labels
`dwa:sq:sec:scope`, `dwa:as:sec:inverse`, `dwa:as:sec:scope`,
`dwa:as:sec:questions`): 101 in all. Part I keeps its delivered section,
statement and equation numbers; Part II's delivered Section `k` is Section
`k+7`, and its equations, delivered consecutively, are numbered by section.
The front matter (guide, status table, a notation table of 21 rows of symbols
that change meaning between the Parts, provenance and merge
decisions, relation to the repository) and eleven dated `[write]` notes
were added; no delivered statement, proof or number was changed and no symbol was
renamed. The bibliographies were merged (Ahmadi–Gómez-Aíza–Ward, cited by
both, is printed once).

## Files

```text
README.md                                        this guide (replaces manuscript 50's delivery README)
article.tex                                      the merged report (manuscript 50 delivered as article/divisor-square-partitions.tex)
article.pdf                                      compiled report, 27 pages
50-divsq-INTEGRATED_REVIEW.md                    50: integrated transcription review (audits/INTEGRATED_REVIEW.md)
50-divsq-ind-AUDIT.md                            50: independent mathematical audit (audits/independent/AUDIT.md)
50-divsq-proofs-PROOF_NOTES.md                   50: proof notes (proofs/)
50-divsq-proofs-INVERSE_SHIFT_ADDENDUM.md        50: inverse-shift addendum (proofs/)
50-divsq-proofs-NUMERICAL_SUMMARY.md             50: numerical summary (proofs/)
50-divsq-proofs-SOURCE_STATUS.md                 50: OEIS and literature status (proofs/)
49-assembly-audit_note.md                        49: independent audit (audit/audit_note.md)
code/50-divsq-verify.py                          50: root driver (verify.py); cannot run in this layout, see below
code/50-divsq-producer-verify.py                 50: producer numerics (checks/producer/verify.py)
code/50-divsq-producer-verify_log_series.py      50: producer symbolic F_j/I_j (checks/producer/verify_log_series.py)
code/50-divsq-ind-check.py                       50: independent stdlib checker (audits/independent/check.py)
code/50-divsq-build.sh                           50: PDF build (article/build.sh)
code/49-assembly-verify_divisor_assembly.py      49: exact integers to 1200, R_0..R_5, inverse
code/49-assembly-audit_checks.py                 49: independent audit checks (audit/audit_checks.py)
code/49-assembly-build.sh                        49: PDF build (build.sh)
data/50-divsq-producer-verification.json         50: producer numerics receipt
data/50-divsq-producer-log_series_verification.json  50: producer symbolic receipt
data/50-divsq-ind-verification.json              50: independent checker receipt
data/50-divsq-ind-approval.json                  50: independent approval (pins delivered files)
data/50-divsq-ind-optimization-negative-control.txt  50: expected stderr under python -O
data/50-divsq-integrated_approval.json           50: integrated approval (pins delivered files)
data/50-divsq-root-visual-approval.json          50: visual approval (pins the delivered tex and PDF)
data/50-divsq-visual-qa.json                     50: visual QA of the delivered 10-page PDF (article/visual-qa.json)
data/50-divsq-requirements.txt                   50: sympy, mpmath, numpy, scipy (unpinned)
data/49-assembly-verification.json               49: producer receipt
data/49-assembly-coefficients.txt                49: R_0..R_5 as rational functions
data/49-assembly-audit_results.json              49: audit receipt (audit/audit_results.json)
data/49-assembly-provenance.json                 49: literature links, repository search and pin
data/49-assembly-quality_receipt.json            49: visual and build receipt of the delivered 9-page PDF
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Not shipped (all recoverable with
`git show 096ee7b87:docs/incoming/<archive>`): both delivered PDFs; 50's
`SHA256SUMS` (verified 23/23); 49's `manifest.json` (a SHA-256 ledger,
verified 13/13), its main `.tex` (printed as Part II), its delivery README,
and `audit/replay.log` (a byte copy of `audit/audit_results.json`). Nothing
was excluded as a heavy artifact (the largest delivered non-PDF file is
50's 26,622-byte manuscript).

**Delivered text that names old or unshipped paths:**

- `code/50-divsq-verify.py` reads `SHA256SUMS`, `audits/…`, `article/…`
  and `checks/…` relative to itself and pins the delivered PDF; it cannot pass
  in this layout. `code/50-divsq-build.sh` builds
  `divisor-square-partitions.tex` from its own directory;
  `code/49-assembly-build.sh` builds `divisor_assembly_asymptotics.tex` from
  its own directory. To rebuild a delivered PDF, use the arrival archive.
- The approval and QA receipts of 50 and the quality receipt of 49 pin the
  delivered `.tex` and PDF; `article.tex` here is the merged report and does
  not match those pins.
- `code/49-assembly-audit_checks.py` defaults to the producer's directory
  `/workspace/shared/oeis-divisor-assembly-research` and hashes the
  unshipped `divisor_assembly_asymptotics.tex`; it writes
  `audit_results.json` beside itself. `49-assembly-audit_note.md` refers to
  `audit/audit_checks.py` and `audit_results.json` by their delivered names.
- `code/49-assembly-verify_divisor_assembly.py` writes `coefficients.txt`
  and `verification.json` beside itself.
- `50-divsq-ind-AUDIT.md`:29 "the independently reviewed A022629 proof" is
  manuscript 51's audit (see above).
- 49's unshipped delivery README says "Independent audit details are supplied
  separately in the final release package", although the audit was in the
  same package (now `49-assembly-audit_note.md` and its two files): stale
  delivery wording. 50's unshipped delivery README called the work "a
  ten-page report" at `article/divisor-square-partitions.pdf`.

## Rerunning the checks (on a copy)

Requirements: Python 3 with SymPy and mpmath (Part II), and also NumPy and
SciPy (Part I's producer); the independent checker of Part I needs only the
standard library. Do not use `python -O` (the delivered scripts rely on
assertions). Never run a script in place: several write beside themselves. On
Windows, Python writes CRLF, so compare modulo CR. From this directory (Git
Bash):

```sh
R=$(mktemp -d)
# Part I, independent checker (seconds); compare with the shipped receipt
cp code/50-divsq-ind-check.py "$R/check.py"
py "$R/check.py" --output-dir "$R/ind"
diff <(tr -d '\r' < "$R/ind/verification.json") data/50-divsq-ind-verification.json
# Part I, producer numerics (about 40 s) and symbolic series (over three minutes here)
py code/50-divsq-producer-verify.py --output-dir "$R/num"
py code/50-divsq-producer-verify_log_series.py --output-dir "$R/sym"
diff <(tr -d '\r' < "$R/num/verification.json") data/50-divsq-producer-verification.json
diff <(tr -d '\r' < "$R/sym/log_series_verification.json") data/50-divsq-producer-log_series_verification.json
# Part II, producer (about 5 minutes on a loaded machine); writes beside itself
mkdir "$R/as" && cp code/49-assembly-verify_divisor_assembly.py "$R/as/verify_divisor_assembly.py"
py "$R/as/verify_divisor_assembly.py"
diff <(tr -d '\r' < "$R/as/coefficients.txt") data/49-assembly-coefficients.txt
diff <(tr -d '\r' < "$R/as/verification.json") data/49-assembly-verification.json
```

The two producer programs of Part I refuse to overwrite an existing receipt
or to write into their own directory; give each run a fresh `--output-dir`.
Part II's audit needs the unshipped manuscript in its source directory:

```sh
A="$R/audit" && mkdir "$A"
git show 096ee7b87:docs/incoming/oeis-divisor-assembly-result.zip > "$R/49.zip"
unzip -q "$R/49.zip" -d "$R/z49"
cp "$R/z49/oeis-divisor-assembly-result/divisor_assembly_asymptotics.tex" "$A/"
cp code/49-assembly-audit_checks.py "$A/audit_checks.py"
cp code/49-assembly-verify_divisor_assembly.py "$A/verify_divisor_assembly.py"
cp data/49-assembly-verification.json "$A/verification.json"
py "$A/audit_checks.py" "$A"
diff <(tr -d '\r' < "$A/audit_results.json") data/49-assembly-audit_results.json
```

At the write (2 October 2026) the independent checker of Part I reproduced
its receipt byte for byte, and Part II's audit reproduced its receipt except
the `seconds` field (87 s here against the recorded 14 s; the machine was
shared). At placement, Part I's producer numerics and Part II's producer
reproduced their receipts modulo CR; Part I's symbolic producer and root
driver did not finish within the time limit and were not rerun.

The root driver `code/50-divsq-verify.py` (manifest coverage, approval-pin
chains, the `-O` negative controls) needs the delivered layout with
`SHA256SUMS` and the PDF. Run it on an extraction of the arrival archive:

```sh
git show 096ee7b87:docs/incoming/oeis-divisor-square-asymptotics-result.zip > "$R/50.zip"
unzip -q "$R/50.zip" -d "$R/z50" && cd "$R/z50/oeis-divisor-square-asymptotics-result" && py verify.py
```

## Building the PDF

```sh
B=$(mktemp -d) && cp article.tex "$B" && (cd "$B" && latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex) && cp "$B/article.pdf" .
```

`pdflatex` via MiKTeX or TeX Live; packages: geometry, fontenc, lmodern,
microtype, amsmath, amssymb, amsthm, mathtools, booktabs, array, enumitem,
hyperref, xurl. The build has no errors, undefined references, multiply
defined labels, duplicate destinations or overfull boxes.
