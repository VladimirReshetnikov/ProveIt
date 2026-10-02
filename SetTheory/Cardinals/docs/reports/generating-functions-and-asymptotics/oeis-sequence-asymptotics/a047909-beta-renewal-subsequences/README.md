# Complete Increasing Subsequences in Multiset Permutations (OEIS A047909 and A268485)

**Quantitative Beta renewal asymptotics: central, diagonal and separated-ratio expansions, and transition-uniform relative accuracy**

This research report was merged on 2 October 2026 from two manuscripts of
batch 77. Both arrived in commit `096ee7b87` and were placed in
`4f11bc9c0`. The second is an addendum to the first: it calls the first
its companion report, says it does not replace it, and pins the first's
TeX, PDF and archive by SHA-256.

| Part | Source | Batch-77 manuscript | Archive (delivered main file, PDF pages) | Pin | Placed | Printed as |
|---|---|---|---|---|---|---|
| I | central and separated regimes | 13 | `beta-renewal-asymptotics-reproducibility.zip` (`beta-renewal-asymptotics.tex`, 14 pp.) | `4b874cea0` | `4f11bc9c0` | Sections 1–10, pages 8–20 |
| II | transition-uniform addendum | 14 | `beta-renewal-uniform-reproducibility.zip` (`beta-renewal-uniform-addendum.tex`, 12 pp.) | none (pins manuscript 13's bytes) | `4f11bc9c0` | Sections 11–19, pages 21–32 |

Part I's pin is the ProveIt commit of its scoped repository overlap check
(its Section 9, and `data/13-central-source-hashes.json`). Manuscript 14
names no repository commit. Its `data/14-uniform-source-hashes.json`
records the SHA-256 of manuscript 13's TeX (`df1e8c2d…`), PDF
(`284e4b28…`) and archive (`2479476d…`). At the write all three equal the
delivered bytes in `096ee7b87`.

Delivered author lines: "Research report for OEIS A047909 and A268485"
(13) and "Research addendum for OEIS A047909 and A268485" (14). Neither
names a person or a tool.

**Status.** The report is AI-assisted and unrefereed, and nothing in it is
formalized. Its proofs have been checked only by the reviews recorded in
the delivered `VALIDATION.md` files (shipped below) and by the intake and
write checks described under "Rerunning the checks". No referee and no
proof assistant has checked them.

## What is claimed

Let `H(m,k)` count words with `m` copies of each of `1, …, k` that contain
`12⋯k` (A047909; its diagonal `a(n) = H(n,n)` is A268485), and
`p_m(k) = H(m,k)(m!)^k/(mk)!`. The renewal identity
`p_m(k) = P(B_1 + ⋯ + B_k ≤ 1)` with independent `Beta(1,m)` increments,
and the Gaussian limit, are El Maazouz and Pitman's (CPC 33 (2024),
Proposition 5.13 for the limit). Neither Part claims them; Part I gives a
direct proof of the identity.

- **Part I** (Theorem 3.1): for every fixed order `R` and window
  `|x| ≤ C`, `x = (k−m)/√m`,
  `p_m(k) = Φ(−x) + φ(x) Σ_{j≤R} P_j(x) m^{−j/2} + O(m^{−(R+1)/2})`, with
  explicit `P_1, …, P_4` (`P_1 = (x²+8)/6`). Corollary 4.1: on the
  diagonal only odd half-integer powers occur beyond `1/2`, with
  corrections `4/3, −101/135, 19819/7560, −4463177/272160` (times
  `1/√(2π)`). Proposition 5.1: a smooth probability quantile with two
  correction terms and integer ceiling brackets. Proposition 6.1: a
  Lambert-`W` inverse for diagonal counts, with smooth displacement
  tending to `1/4`; diagonal counts are strictly increasing. Theorem 7.1:
  for `k/m` in a compact set inside `(0,1)` or `(1,∞)`, the rare failure or
  success probability to every fixed order, with explicit `c_1(ρ)`.
- **Part II** (Lemma 14.1, Theorem 13.1): a `(1+z²)`-weighted density
  remainder for the tilted triangular family, and with it relative error
  `O(m^{−(R+1)/2})` for both tails, uniformly for `a ≤ k/m ≤ b`, through
  moderate deviations and the exact zero-saddle point `k = m+1` (12.4).
  Section 16 re-derives `P_1` and `c_1` from this formula and identifies
  every `P_j` and `c_j` by uniqueness. Corollary 17.1: both real
  Lambert-`W` branches for separated tail thresholds `e^{−mℓ}`, two inverse
  corrections and qualified integer brackets.

**What neither Part claims.** Growing truncation order or uniformity when
`R` or `C` grows with `m`; convergence of the formal series; optimal
truncation, Stokes phenomena, exponentially improved remainders or an
exponential-sector theorem; ratios `k/m` tending to `0` or `∞`; growing
windows for the central polynomial expansion itself (Part II's theorem
covers moderate deviations through its unexpanded kernels, and says it
does not justify substituting a growing `x` into Part I's polynomials);
effective constants; certified integer thresholds or exact rounding; a
transition-uniform inversion; numerically stable or interval-certified
evaluation. The smooth inverse carriers are chosen, not canonical real
extensions of the integer-indexed quantities. Part I's rare-tail theorem
uses the exact integer ratio `k/m`. Neither Part claims a new general
Edgeworth, saddle-point or tilting method; Part II attributes its method
to Esscher and Cramér through Daniels (1987), with Lugannani–Rice,
Robinson and Jensen as related classical work, and claims no priority for
its family-specific theorem. Finite computations (exact rational
probabilities, word counts, symbolic re-derivations, mpmath quadrature
at 65 digits, not interval-certified) check formulas, signs and indexing
and prove no asymptotic statement. The literature and repository searches
are bounded and are not novelty certificates. The Horton–Kurn paper was
not inspected in full; its enumeration was consulted through Clifton et
al., Theorem 2.1.

**Statements that Part II answers** are printed as delivered in Part I,
each followed by a dated `[write, 2 October 2026]` note:

- the abstract's "no transition-uniform matching … is claimed" and the
  paragraph after Theorem 7.1 (poles at `ρ = 1`): Part II's Theorem 13.1;
- research direction 1, "Uniform matching across the transition":
  answered at every fixed order on every fixed compact positive ratio
  range;
- research direction 2, "Moderate deviations": answered in part, for the
  kernel formula; growing windows for the `P_j`-expansion remain open;
- the Conclusion's "join their ranges with explicit, transition-uniform
  and practically effective error estimates": joined, but not explicitly
  or effectively.

Research directions 3–5 of Part I stay open; the notes cross-reference
Part II's open questions (Section 19).

## Files

The numerals I and II name the Part that a delivered file belongs to.

```
article.tex                                     the merged report (standalone LaTeX, internal bibliography)
article.pdf                                     the compiled report, 33 pages
README.md                                       this guide
13-central-proofs-central.md                    I: central expansion, diagonal and inverse proof notes
13-central-proofs-rare-tails.md                 I: separated-ratio rare-tail proof notes
13-central-SOURCES.md                           I: sources, search limits and the scoped ProveIt overlap check (pin 4b874cea0)
13-central-VALIDATION.md                        I: delivered verification summary
14-uniform-SOURCES.md                           II: bounded attribution of the general method
14-uniform-VALIDATION.md                        II: delivered verification summary
code/13-central-build.sh                        I: delivered PDF build script
code/13-central-replay.sh                       I: delivered replay entry point
code/13-central-check_manifest.py               I: SHA-256 manifest check (reads the unshipped SHA256SUMS)
code/13-central-central_polynomials.py          I: P1..P4 by the cumulant recurrence
code/13-central-derive_diagonal_fast.py         I: diagonal coefficients through order 7
code/13-central-check_renewal.py                I: exact simplex probabilities and diagonal counts
code/13-central-check_transition.py             I: exact central-window diagnostics
code/13-central-check_rare_tail.py              I: exact separated-ratio diagnostics
code/13-central-independent_central.py          I: raw-moment logarithm route, direct word counts, inverse coefficients
code/13-central-independent_rare.py             I: independent transform/saddle route, second exact recurrence
code/13-central-validate_outputs.py             I: asserting validator and baseline comparison
code/14-uniform-replay.sh                       II: delivered replay entry point
code/14-uniform-check_manifest.py               II: SHA-256 manifest check (reads the unshipped SHA256SUMS)
code/14-uniform-check_symbolic.py               II: saddle, kernel, P1 and c1 identities; parity through order 10
code/14-uniform-check_inverse.py                II: inverse cancellations, Lambert branches, carrier crossings
code/14-uniform-check_uniform.py                II: exact probabilities vs R = 0, 1, 3 at 16 pairs (mpmath, 65 digits)
code/14-uniform-validate_outputs.py             II: comparison with the recorded checks
code/14-uniform-make_archive.py                 II: rebuilds the delivered ZIP and its SHA256SUMS
data/13-central-central-polynomials.json        I: recorded P1..P4
data/13-central-diagonal-coefficients.json      I: recorded diagonal coefficients
data/13-central-renewal-exact-checks.json       I: recorded exact probabilities and counts
data/13-central-renewal-output.txt              I: its log
data/13-central-transition-exact-checks.json    I: recorded central-window diagnostics
data/13-central-transition-output.txt           I: its log
data/13-central-rare-tail-exact-checks.json     I: recorded rare-tail diagnostics
data/13-central-rare-tail-output.txt            I: its log
data/13-central-independent-central-results.json  I: recorded independent central results
data/13-central-independent-central-output.txt  I: its log
data/13-central-independent-rare-results.json   I: recorded independent rare-tail results
data/13-central-independent-rare-output.txt     I: its log
data/13-central-source-hashes.json              I: hashes of inspected external sources; the overlap-check record
data/13-central-requirements.txt                I: sympy==1.14.0, mpmath==1.3.0
data/14-uniform-symbolic.json                   II: recorded symbolic checks
data/14-uniform-inverse.json                    II: recorded inverse checks
data/14-uniform-uniform.json                    II: recorded numerical checks
data/14-uniform-source-hashes.json              II: SHA-256 of its source notes and of manuscript 13's TeX, PDF and ZIP
data/14-uniform-requirements.txt                II: sympy==1.14.0, mpmath==1.3.0 (same bytes as 13's)
```

The directory holds 46 files: 9 at the root, 18 in `code/` and 19 in
`data/`. Every file except `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery. Nothing was excluded as heavy: the
largest shipped delivered file is `13-central-proofs-central.md`
(11,258 bytes), the largest in `data/` is
`data/14-uniform-uniform.json` (7,538 bytes).

**Delivery names.** Files were renamed when placed. Manuscript 13's
`scripts/X` and the root scripts became `code/13-central-X`, its
`checks/X`, `source-hashes.json` and `requirements.txt` became
`data/13-central-X`, `proofs/X.md` became `13-central-proofs-X.md`, and
`SOURCES.md` and `VALIDATION.md` became `13-central-*.md`. Manuscript 14
likewise became `code/14-uniform-*`, `data/14-uniform-*` and
`14-uniform-*.md`. Its three recorded checks are
`data/14-uniform-{symbolic,inverse,uniform}.json`, delivered as
`checks/{symbolic,inverse,uniform}.json`. The placement plan
(`b77P5_plan.tsv`, one row per delivered file) maps every name. Delivered
files whose text still uses delivery names or names unshipped files:

- Every shipped script. The two `replay.sh` scripts first run
  `scripts/check_manifest.py`, which reads a `SHA256SUMS` that is not
  shipped, then copy `scripts/*.py` to `build/replay/`. 13's
  `build.sh` builds `beta-renewal-asymptotics.tex`, which is shipped
  only as Part I of `article.tex`. 13's scripts write to
  `../checks/` relative to their own directory, and 14's write
  `checks.json`, `recomputed.json` and `inverse.json` next to
  themselves. 14's `make_archive.py` rewrites `SHA256SUMS` and builds a
  ZIP in its parent directory from a file list that includes the
  unshipped TeX, PDF, README and `build.sh`.
- `13-central-proofs-rare-tails.md` says "The central theorem is in
  PROOF.md"; that note is shipped as `13-central-proofs-central.md`.
  `13-central-proofs-central.md` cites `SOURCES.md`, the script names
  under `scripts/` and the outputs under `checks/`.
  `13-central-SOURCES.md` cites `source-hashes.json`.
- `13-central-VALIDATION.md` and `14-uniform-VALIDATION.md` describe the
  delivered 14- and 12-page PDFs, `replay.sh --with-pdf` and the
  `SHA256SUMS` ledgers, none of which is shipped. They record the SHA-256
  of the reviewed TeX files (`df1e8c2d…`, `9b81ead7…`), which equal the
  delivered manuscripts in `096ee7b87`, not `article.tex`.
- `data/14-uniform-source-hashes.json` hashes two approved proof notes
  that were never delivered ("integrated into the article, not
  redistributed") and manuscript 13's PDF and ZIP, which are not shipped.
- `data/13-central-source-hashes.json` hashes external copies (the OEIS
  records, Clifton et al., El Maazouz–Pitman) that are not redistributed.

**Not shipped** (all survive in `096ee7b87`): both delivered PDFs; 13's
delivery README (placed here in `4f11bc9c0`, now replaced by this README)
and 14's; manuscript 14's TeX (printed as Part II) and `build.sh`; and
the two `SHA256SUMS` ledgers, verified at placement (32/32 and 18/18).

**Kept duplicates.** `data/13-central-requirements.txt` and
`data/14-uniform-requirements.txt` are byte-identical; each sits beside
its own scripts.

## Rerunning the checks

Never run the shipped scripts in this directory: they write into
`code/` or a new `checks/` directory, and the replays need the unshipped
manifests. Rerun each suite in a fresh extraction of its delivered
archive, outside the repository (in Git Bash; PowerShell redirection may
not preserve the ZIP bytes):

    git show 096ee7b87:docs/incoming/beta-renewal-asymptotics-reproducibility.zip > a.zip
    unzip a.zip && cd beta-renewal-asymptotics && PYTHON=py bash replay.sh

    git show 096ee7b87:docs/incoming/beta-renewal-uniform-reproducibility.zip > b.zip
    unzip b.zip && cd beta-renewal-uniform-addendum && PYTHON=py bash replay.sh

The delivered entry points default to `python3`, which on this Windows
machine is the Microsoft Store alias, so set `PYTHON=py` (or a Python
with `sympy==1.14.0` and `mpmath==1.3.0`, as in the requirements files).
Fresh outputs go to `build/replay/` inside the extraction, and the
recorded baselines are not overwritten. The validators compare parsed
JSON, so the CRLF line endings that Python writes on Windows do not
affect them; a byte comparison of regenerated files would differ in line
endings only.

- **Part I.** At intake (2 October 2026, Windows, Python 3.14.4, sympy
  1.14.0) all seven scripts exited 0, and they reproduced the printed
  `P_1, …, P_4` and the seven diagonal coefficients, including the
  vanishing even ones. `validate_outputs.py` passed every exact and
  symbolic assertion (`P_1…P_4`, diagonal orders, word counts, rare-tail
  agreement between the two exact algorithms). It then failed its
  baseline comparison at
  `transition-exact-checks.json[14].scaled_error4`: −0.027437159064043114
  against the recorded −0.027437159064113332, a relative difference of
  2.6e-12, above its tolerance `rel_tol=1e-12`
  (`code/13-central-validate_outputs.py`, line 44). At the write a full
  `PYTHON=py bash replay.sh` in a fresh extraction (2 min 58 s, manifest
  32/32) ended in exactly the same assertion with the same two values. The quantity is a
  cancellation `exact − approximation` computed in binary64 with
  `math.erfc`/`math.exp` and scaled by `m^{2.5}` at `m = 40`. Its last
  digits depend on the platform's math library. The replay's float
  comparison is therefore platform-sensitive at the 1e-11 level for the
  scaled fourth-order transition errors. A failure there, with all exact
  assertions passing, is a math-library difference, not a mathematical
  one.
- **Part II.** At the write (2 October 2026, same machine), a fresh
  extraction ran `PYTHON=py bash replay.sh` to completion in 4 min 3 s:
  "PASS: 18 manifest-pinned files" and "PASS: all symbolic and numerical
  outputs agree with the recorded checks". At intake `check_symbolic.py`
  and `check_inverse.py` had already reproduced their recorded JSON;
  `check_uniform.py` had been cut off at 170 s. The recorded sample maxima
  of `k^{(R+1)/2}|p̂ − p|/min(p, 1−p)` are 0.307223831873, 0.0819420489345
  and 0.0346592177493 for `R = 0, 1, 3` (`14-uniform-VALIDATION.md`).
  They are sample values, not constants.

Neither intake nor write re-derived Part II's analytic arguments beyond
these suites; Part I's `P_1…P_4` and diagonal corrections were reproduced
by its own scripts, and Part II's recovered `P_1` and `c_1` coincide with
Part I's printed formulas.

## Labels

Every label in `article.tex` carries the prefix `brs:`: `brs:` for Part I
(manuscript 13) and `brs:un:` for Part II (manuscript 14), followed by
the delivered name. There are 105 labels: 43 delivered in manuscript 13,
53 in manuscript 14, and 9 added at the merge (`brs:sec:guide`,
`brs:sec:status`, `brs:sec:notation`, `brs:sec:mergeprovenance`,
`brs:part:central`, `brs:part:uniform`, and the section labels
`brs:sec:central`, `brs:sec:further`, `brs:un:sec:open`). The placed
`article.tex` (manuscript 13 alone) had 43 unprefixed labels. Eight
delivered names occur in both manuscripts for different equations
(`eq:renewal`, `eq:density`, `eq:Kexp`, `eq:tshift`, `eq:rare`, `eq:c1`,
`eq:Q1`, `eq:ceil`); the sub-prefix separates them.

## Numbering

Part I keeps manuscript 13's section, statement and equation numbers
(Sections 1–10). Part II's Section k is Section k + 10, so its equation
(k.n) is (k+10.n) and its statements follow: its Theorem 3.1 is
Theorem 13.1, Lemma 4.1 is Lemma 14.1 and Corollary 7.1 is Corollary 17.1.

## How the merge was done

Each Part prints its manuscript from the abstract to the end of its text,
with every result, proof, remark, question and limitation; the residue
check confirms that both delivered bodies and abstracts are contained
verbatim once the label prefixes and notes are removed. The changes:

- the label prefixes above;
- one shared preamble, the union of the two, in which every shared macro
  has the same definition; `xurl` added for long file names. The
  `\pdfmapfile{+lm.map}`, `{+cm.map}` and `{+symbols.map}` lines of both
  preambles were removed (on MiKTeX they only produce "fontmap entry
  already exists" warnings). Letter paper throughout (13 set no paper
  size, 14 set letter); one running head;
- the two title blocks printed as Part headings with a source line, and
  the abstracts as "Abstract of this Part (as delivered)"; manuscript 13's
  table of contents replaced by one;
- the two bibliographies merged. The five shared entries are kept once:
  manuscript 13's copies of the two OEIS entries add an inspection date
  and an indexing note, and the other three are identical in content.
  14's entry `base` (the companion report) is kept, with a note that it is
  Part I;
- 19 dated `[write, 2 October 2026]` notes, and front matter: a guide, a
  table of what is proved where, a notation table and a provenance
  section.

No symbol was renamed. The front-matter notation table lists the symbols
that change meaning between the Parts, among them `B` (Part I's unscaled
increments vs Part II's kernel sum `B_R^ε`), `t` (Fourier variable vs the
exact saddle), `T`, `E_j` (Part II's `E_j` is not Part I's `[h^j]E`, a
tempting false reading), `A`, `u`, `Q`, `K` (Part II uses `K_m(t)` for the
cumulant generating function and `K_m(ℓ)` for a carrier crossing), `F`,
`q`, `κ` (cumulants in Part I, a bracket centre in Part II), `L`, `D`,
`J`, `ε` and `r`.

**Where the merge had to choose.**

- *Base and order.* Manuscript 13 is the base and Part I; manuscript 14,
  its addendum, is Part II. Nothing is superseded.
- *Re-derived material.* Part II restates Part I's definitions, the
  renewal identity in scaled form, the transform expansion and the saddle
  displacement, and recomputes `Q_1`, the three contributions to `c_1`,
  `c_1` and `P_1`. They are printed where they stand, because Part II's
  proofs cite them. Notes identify them with Part I's equations, and
  Part II's recovery of `P_1` and `c_1` is marked as a consistency check
  by a second route, not a second statement.
- *Answered non-claims.* Part I's "no uniform bridge" statements and its
  open questions 1 and 2 are printed as delivered and followed by notes;
  question 2 is re-scoped because Part II answers it only for the kernel
  formula.
- *Inversion.* The Lambert-`W` inverses of both Parts are credited, in
  notes and in the front matter, to the repository's transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`):
  Part I's count inverse is the case `a = b = 1` of
  `p0:thm:lambert-core` after taking logarithms; the corrections are
  instances of `p0:thm:perturbed-inversion`; the integer brackets are of
  the first-crossing kind of `p0:thm:staircase`. No novelty is claimed for
  the inversion method.
- *Stale repository statement.* Part I's overlap check found no report
  on these sequences at `4b874cea0`. That is still true apart from this
  report; a note says so and keeps the pin.

## Relation to other reports and to formal work

- No other report in the repository mentions A047909, A268485, El
  Maazouz–Pitman or Beta renewal (`git grep` of `HEAD` at the write).
  The nearest reports in this collection treat other sequences by
  saddle-point and singularity analysis; none shares a theorem with this
  one.
- The inverses are instances of the transseries volume's inversion
  theorems, as described above.
- **No formal status.** No Lean or Rocq declaration in the repository
  states or proves any result of this report, and none was delivered with
  it. Its place in the `SetTheory/Cardinals` report collection confers no
  formal status.

## Building

From a copy of this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

This uses pdfLaTeX with lmodern, microtype, amsmath, amssymb, amsthm,
mathtools, geometry, booktabs, array, longtable, enumitem, hyperref, xurl
and fancyhdr. The build at the write (MiKTeX, 2 October 2026) gave 33
pages: title page and contents (pages 1–2), front matter (3–7), Part I
(8–20), Part II (21–32) and the references (33). It had 0 errors, 0
warnings, 0 undefined references or citations, 0 multiply defined labels,
0 duplicate PDF destinations, and no overfull or underfull boxes.
