# Corner Polyhedra and Schnyder Labelings

**Polynomial exponents, non-D-finiteness and limiting amplitudes for OEIS
A377922, A377920 and A377921 (Fusy–Narmanli–Schaeffer Conjecture 25)**

A research report dated 2 October 2026, built from two manuscripts, each
printed in full. Part I's author line is "Research note"; Part II's is
"Research addendum" (its PDF metadata also say "Research note"). Neither
names a tool or an author.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 45 | batch 77, manuscript 45 | `oeis-bimodal-cone-research.zip`, arrival commit `096ee7b87` (wrapper `oeis-bimodal-cone-report/`, main file `article.tex`, 15-page PDF; PDF and `SHA256SUMS` not shipped) | none: no ProveIt commit is named; the only repository input was a GitHub code search, which returned nothing | `aa7345800` | Part I: Sections 1–10, Appendix A |
| 46 | batch 77, manuscript 46 | `oeis-bimodal-full-asymptotics.zip`, arrival commit `096ee7b87` (wrapper `oeis-bimodal-amplitude-report/`, main file `addendum.tex`, 14-page PDF; manuscript, PDF, README, `SHA256SUMS`, `build.sh`, `requirements.txt` and the embedded Foundation copy not shipped) | none: no ProveIt commit is named; the repository input is source 45's code search | `aa7345800` | Part II: Sections 11–21 |

**Status:** AI-assisted? Not stated by either delivery. Unrefereed, not
formalized. Both parts are backed by exact symbolic checks and finite
enumeration (coefficients through `n = 30`); these check identities,
normalizations and indexing, not the limit theorems. The shipped mathematical
reviews are the deliveries' own, not external peer review.

Source 46 is an addendum to source 45: it embeds an unchanged copy of all 30
files of source 45's package (byte-identical at placement), cites it as "the
Foundation", and does not repeat its proofs. The copy is not shipped; source
45 is printed once, as Part I.

## What it proves

`p_n` counts corner polyhedra with `n + 3` flats (polyhedral orientations
with `n` inner vertices, A377922), `s_n` counts 3-connected Schnyder
labelings with `n` inner faces (A377920), and `s̃_n` counts rigid orthogonal
surfaces (A377921), indexed as in Fusy–Narmanli–Schaeffer (Electron. J.
Combin. 30(2) (2023), P2.17). Put `μ_P = 9/2`, `μ_S = 16/3`,
`α_P = 1 + π/arccos(9/16) = 4.227476082…` and
`α_S = 1 + π/arccos(22/27) = 6.080304846…`.

**Part I (source 45)**
- `p_n = Θ(μ_P^n n^(-α_P))` and `s_n = Θ(μ_S^n n^(-α_S))` on the full
  integer sequence (Theorem 1.1). This proves the exponents of
  Fusy–Narmanli–Schaeffer's Conjecture 25. The method regenerates at
  returns to a parity state, uses a one-unit buffer for excursions within a
  cycle (Lemma 4.1), a random-clock transfer, a Fourier local limit and an
  interior gluing argument.
- Both exponents are irrational, and the ordinary generating functions of
  A377922, A377920 and A377921 are not D-finite (Corollary 9.4), by a
  positive-derivative criterion that works from `Θ` bounds.
- First-threshold inverses `N(Y) = (log Y + α log log Y)/log μ + O(1)`,
  without monotonicity (Lemma 9.5).

**Part II (source 46)**
- Finite positive constants `κ_P`, `κ_S` with
  `p_n ~ κ_P μ_P^n n^(-α_P)`, `s_n ~ κ_S μ_S^n n^(-α_S)` and
  `s̃_n ~ (16/19)^3 κ_S μ_S^n n^(-α_S)` (Theorem 11.1): the two
  positive-amplitude equivalents of Conjecture 25, and a coefficientwise
  equivalent for A377921 by a dominated signed convolution.
- On the way: a boundary-shift comparison of harmonic functions (Lemma
  14.1), harmonic and endpoint limits for valid cycles (Theorem 15.1), exact
  counted-time survival constants (Theorem 16.1), a uniform interior killed
  local limit (Lemma 17.1), fixed-endpoint bridge amplitudes (Theorem 18.1)
  with the universal Brownian factor evaluated (Section 18.1), and the
  amplitude formulas (19.1) and (19.3).
- A Lambert-`W_{-1}` inverse with a vanishing-width two-ceiling bracket
  (Theorem 20.1).

## What is not claimed

- **No numerical digits** of `κ_P` or `κ_S`, no rate of convergence and no
  correction term (Part II). The amplitudes are characterized by positive
  killed-harmonic and Brownian heat-kernel expressions; only the universal
  Brownian factor is evaluated.
- No unconditional rounding formula `N(Y) = ⌈r(Y)⌉` (Part II); Part I's
  inverse has `O(1)` error and no next additive constant.
- **A377923** (its OEIS entry was exported with the others) is a different
  sequence and is outside both theorems.
- No general cone theorem for Markov-modulated walks: the argument uses a
  fixed cycle buffer specific to these two tandem-walk models. Part II
  assumes no cone-killed local theorem for the two-state chain.
- The counting bijections and conjectures are Fusy–Narmanli–Schaeffer's,
  the iid cone input (Theorems 2–3 of *Random walks in cones revisited*) is
  Denisov–Wachtel's, the non-D-finiteness step uses the
  André–Chudnovsky–Katz theorem in Fischler–Rivoal's form, and the
  Brownian cone kernel is Bañuelos–Smits'. **Neither source claims
  publication priority**; both literature checks are bounded snapshots
  (2 October 2026, 01:22–01:39 UTC) that do not establish novelty.
- Finite computations corroborate formulas and indexing; they do not prove
  the cycle lemma, the probabilistic estimates or any limit.

Part I's text (its abstract, Sections 1, 9 and 10) says that the amplitudes
are unresolved and that no coefficientwise estimate for A377921 follows.
Those sentences
describe source 45's own scope and are printed unchanged; dated `[write]`
notes point to Part II. Still open after the merge: the values of `κ_P` and
`κ_S`, rates, corrections, exact rounding, and other parity-dependent tandem
models with a fixed cycle buffer (Part I, Section 10).

**Inversion mechanics.** Lemma 9.5 and Theorem 20.1 are instances of the
transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
the model equation `λr − α log r = log(Y/γ)` is `p0:thm:lambert-core`
(`a = log μ`, `b = −α`, branch `W_{-1}`), its expansion is the first step
of `p0:thm:lambert-centered`, and the ceiling bracket is the separation
situation of `p0:thm:staircase`. No novelty is claimed for the inversion
mechanics; dated notes in Sections 9.2 and 20 say so.

## Notation

Both manuscripts use the same normalizations (`μ`, `α`, `L`, `K_P`, `K_S`,
`q_n`, `Σ_P`, `Σ_S` per counted step, `θ`, `p = π/θ = α − 1`). No symbol was
renamed and no normalization changed. Several letters clash; Table 1 of the
guide lists them with the tempting false readings. The dangerous ones:

- Part II's `D` is the valid complete-cycle kernel; Part I's `D` is the
  denominator `(1 − 1/(3x²))(1 − y²/3)`, which Part II calls `D_P`.
- Part II's `T = (2Σ)^(-1/2)` is a whitening matrix; Part I's `T(z)` is the
  generating function of A377921, which Part II calls `S̃(z)`.
- Part II's `𝓗` is a harmonic function; Part I's `H` (Part II's `H_S`) is
  the denominator of the Schnyder kernel.
- Part I's `A(z)` is a generating function, Part II's `A(a)` a survival
  amplitude; Part I's `β = k − α`, Part II's `β` a survival constant.
- In both parts the roman `e` is the even parity state, not Euler's number.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status. The only
related formal statement is the generic staircase lemma
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, which
concerns an arbitrary monotone interpolation, not these sequences.

**Neighbouring reports.** No other report mentions these sequences,
Schnyder labelings or corner polyhedra (repository search, 2 October 2026).
No other report cites Denisov–Wachtel's cone theorems. The closest in
subject is `a227578-ordered-rook-paths`, which counts lattice walks in a
Weyl chamber by exact coefficient identities and mentions, without using,
the Denisov–FitzGerald harmonic determinant; no theorem is shared. This
pointer is made here only.

**Stale delivery statements.** Both literature receipts
(`45-cone-literature-status.md`, `46-amp-literature-status.md`) and
`data/45-cone-public-overlap-check.json` record that a GitHub code search of
ProveIt for A377920, A377921, A377922, "Schnyder" and "corner polyhedra"
returned nothing. That was true on 2 October 2026 before placement; the only
matches now are this report's files.

## Labels

Part I's labels carry the prefix `cps:` (source 45's 73 labels, prefixed
before anything cited them); Part II's carry `cps:amp:` (source 46's 78
labels). The merge added four: `cps:sec:guide`, `cps:tab:notation`,
`cps:part:exponents`, `cps:part:amplitudes`. Total 155. Every label keeps its
source number: Part I's numbers are source 45's (checked against a build of
the delivered `article.tex`), and Part II's are source 46's with 10 added to
the section number (checked against a build of `addendum.tex`).

Apart from labels, the only changes to the manuscripts' text are: source
46's eight references to the Foundation (one citation, seven numbered
references), which became cross-references with the same numbers
("Foundation Lemma 2.1" is Lemma 2.1 here); its citation key `DW`, which
became source 45's `DWrevisited` (the same paper); and ten dated `[write]`
notes (five in Part I's body, one in Appendix A, four in Part II). The editorial guide before Part I is unnumbered. No statement,
proof, symbol or number of either manuscript was changed.

## Files

```text
README.md                                    this guide (replaces both delivery READMEs)
article.tex                                  the report (source 45 delivered as article.tex, source 46 as addendum.tex)
article.pdf                                  compiled report, 36 pages
45-cone-literature-status.md                 source 45: bounded literature and overlap receipt (as delivered)
45-cone-mathematical-verification.md         source 45: the delivery's own mathematical review (as delivered)
46-amp-integrated-mathematical-review.md     source 46: the delivery's own review of the addendum with the Foundation
46-amp-literature-status.md                  source 46: literature snapshot (source 45's, with a preface)
code/45-cone-run_all.py                      Part I: runs the four checks below, writes results/verification-summary.json
code/45-cone-verify_symbols.py               Part I: exact kernels, correctors, covariances, cycle laws, angles (SymPy)
code/45-cone-independent_corner_checks.py    Part I: separate P algebra, 25,900 bounded cycle shapes, p_n to n = 15
code/45-cone-independent_schnyder_checks.py  Part I: separate S resolvent, moments, direct aggregate enumeration to n = 14
code/45-cone-enumerate_schnyder.py           Part I: weighted recurrence to n = 30, compared with sources/A377920.seq
code/45-cone-build.sh                        Part I: two-pass pdfLaTeX build of a delivery-layout article.tex
code/46-amp-run_all.py                       Part II: integrity check, new algebra, isolated Foundation replay
code/46-amp-verify_foundation.py             Part II: hashes the embedded Foundation copy (not shipped; see below)
code/46-amp-verify_addendum.py               Part II: exact Brownian/Gamma, determinant, multiplier and inverse checks
data/45-cone-A377920.seq                     Part I: OEIS entry A377920 (s_n), oeisdata export da8d37c6 (CC BY-SA 4.0)
data/45-cone-A377921.seq                     Part I: OEIS entry A377921 (rigid surfaces), same export
data/45-cone-A377922.seq                     Part I: OEIS entry A377922 (p_n), same export
data/45-cone-A377923.seq                     Part I: OEIS entry A377923 (outside both theorems), same export
data/45-cone-provenance.json                 Part I: export commit, source URLs, sizes and SHA-256 of the four entries
data/45-cone-public-overlap-check.json       Part I: GitHub code-search receipts (ProveIt: 0 hits on 2 October 2026)
data/45-cone-requirements.txt                Part I: sympy>=1.12,<2
data/45-cone-symbolic-checks.json            Part I: recorded output of verify_symbols.py
data/45-cone-verify_symbols.stdout.txt       Part I: its stdout
data/45-cone-independent-corner-checks.json  Part I: recorded output of independent_corner_checks.py
data/45-cone-independent_corner_checks.stdout.txt
data/45-cone-independent-schnyder-checks.json  Part I: recorded output of independent_schnyder_checks.py
data/45-cone-independent_schnyder_checks.stdout.txt
data/45-cone-schnyder-enumeration.json       Part I: s'_n, s_n, s̃_n to n = 30
data/45-cone-enumerate_schnyder.stdout.txt   Part I: its stdout
data/45-cone-verification-summary.json       Part I: run_all.py summary (Python 3.12.14, SymPy 1.14.0)
data/45-cone-mathematical-verification.json  Part I: hash-bound receipt of the review
data/45-cone-visual-validation.json          Part I: layout check of the unshipped 15-page PDF
data/46-amp-addendum-symbolic-checks.json    Part II: recorded output of verify_addendum.py
data/46-amp-verify_addendum.stdout.txt       Part II: its stdout (byte-identical to the JSON)
data/46-amp-verify_foundation.stdout.txt     Part II: "PASS: 30 unchanged Foundation files …"
data/46-amp-foundation-replay.stdout.txt     Part II: stdout of the Foundation replay
data/46-amp-verification-summary.json        Part II: run_all.py summary (Python 3.12.14, SymPy 1.14.0)
data/46-amp-integrated-mathematical-review.json  Part II: hash-bound receipt of the review
data/46-amp-provenance.json                  Part II: Foundation hashes and source provenance
data/46-amp-visual-validation.json           Part II: layout check of the unshipped 14-page PDF
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. The delivered files have LF line endings.

**Renames.** Placement prefixed every shipped name of source 45 except
`article.tex` and `README.md` (since replaced) with `45-cone-`, and every
shipped name of source 46 with `46-amp-`. Scripts went from `scripts/` (and
`build.sh` from the package root) to `code/`; `results/*`, `sources/*`,
`requirements.txt` and `audit/*.json` to `data/`; `audit/*.md` and source
46's `sources/literature-status.md` to the report root.

**Not shipped** (all in the arrival commit): both delivered PDFs; both
`SHA256SUMS` ledgers (verified 29/29 and 49/49 at placement); source 46's
manuscript, README, `build.sh`, `requirements.txt` (identical to source
45's), its embedded 30-file Foundation copy, and
`results/foundation-integrity.json` (a SHA-256 ledger of that copy).

**Delivered text that still uses delivery names.**
- The article's Appendix A and Section 10, and source 45's delivered README
  (replaced), name `scripts/run_all.py`, `build.sh`, `results/`, `sources/`
  and the package PDF; dated notes in Section 10 and Appendix A say so.
- `code/45-cone-*.py` resolve `scripts/`, `results/` and `sources/`
  relative to their parent directory; `code/45-cone-build.sh` builds
  `article.tex` beside itself.
- `code/46-amp-run_all.py` and `code/46-amp-verify_foundation.py` need
  `foundation/` with its `SHA256SUMS`, `article.pdf` and
  `audit/mathematical-verification.json`, none of which is shipped in that
  layout. Part II's Section 21 (dated note added) describes that package.
- The two review receipts, both review markdown files,
  `46-amp-provenance.json` and the two visual-validation records name and
  hash `article.tex`, `article.pdf`, `addendum.tex`, `addendum.pdf`,
  `foundation/…` and `results/foundation-integrity.json` at their delivery
  paths. The shipped `article.tex` is the merged report, not the reviewed
  source (SHA-256 `849e5150…`); the reviewed sources are in the arrival
  commit.
- `46-amp-literature-status.md` points to
  `foundation/sources/public-overlap-check.json`, shipped as
  `data/45-cone-public-overlap-check.json`.

## Rerunning the checks

Run on scratch copies, never in place: the scripts write `results/` beside
their parent directory, so running them from `code/` would create a
`results/` directory in the report and fail on the missing `sources/`.
On Windows the outputs have CRLF line endings; compare modulo CR
(`diff --strip-trailing-cr`).

**Part I** (from this directory, Git Bash):

```sh
R=$(mktemp -d) && mkdir "$R/scripts" "$R/sources"
for f in run_all verify_symbols independent_corner_checks independent_schnyder_checks enumerate_schnyder; do
  cp code/45-cone-$f.py "$R/scripts/$f.py"; done
for s in A377920 A377921 A377922 A377923; do cp data/45-cone-$s.seq "$R/sources/$s.seq"; done
(cd "$R" && uv run --no-project --with sympy==1.14.0 python scripts/run_all.py)
for f in "$R"/results/*; do diff -q --strip-trailing-cr "$f" "data/45-cone-$(basename "$f")"; done
```

On 2 October 2026 this took 49 s here and passed. All eight outputs equalled
the recorded ones modulo CR; `verification-summary.json` differed only in its
Python version (3.13.5 here, 3.12.14 recorded).

**Part II, new algebra only** (needs nothing else):

```sh
R=$(mktemp -d) && mkdir "$R/scripts" && cp code/46-amp-verify_addendum.py "$R/scripts/verify_addendum.py"
(cd "$R" && uv run --no-project --with sympy==1.14.0 python scripts/verify_addendum.py)
diff --strip-trailing-cr "$R/results/addendum-symbolic-checks.json" data/46-amp-addendum-symbolic-checks.json
```

This took 33 s and matched modulo CR.

**Part II, complete suite** (needs the Foundation copy, so run it from the
delivered archive):

```sh
R=$(mktemp -d) && git show 096ee7b87:docs/incoming/oeis-bimodal-full-asymptotics.zip > "$R/a.zip"
cd "$R" && unzip -q a.zip && cd oeis-bimodal-amplitude-report
uv run --no-project --with sympy==1.14.0 python scripts/run_all.py
```

On Windows this stops at `scripts/run_all.py` line 27 with
`AssertionError: symbolic-checks.json`. That line compares the replayed
Foundation outputs with the delivered ones byte for byte, and Windows text
mode writes CRLF. Every check before it passes (integrity of the 30
Foundation files, the new algebra, the four Foundation programs), and every
output equals the delivered one modulo CR (119 s here on 2 October 2026; the
placement run took 88 s). On a POSIX system it should pass as delivered. Do
not run the archive's `build.sh` scripts in the repository.

The archive of source 45 can be retrieved the same way:
`git show 096ee7b87:docs/incoming/oeis-bimodal-cone-research.zip`. No
delivered file was excluded as a heavy artifact (the largest is 46 KB), so
nothing needs reconstructing.

## Build the PDF

pdfLaTeX with Latin Modern, amsmath, amssymb, amsthm, mathtools, booktabs,
array, longtable, microtype, enumitem, xcolor and hyperref. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX. It has 36
pages (title and contents 1–2, guide 3–6, Part I 7–20, Part II 21–34,
Appendix A 34–35, references 36), with no errors, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations and no
overfull boxes. Three underfull lines remain in one `[write]` note of
Section 20. The delivered manuscripts alone build without box warnings.

## Provenance

- Source 45: batch 77 of `docs/incoming`, manuscript 45, archive
  `oeis-bimodal-cone-research.zip`; arrival `096ee7b87`, placement
  `aa7345800`, written in the batch-77 write phase (2 October 2026). No pin.
  Inputs: Fusy–Narmanli–Schaeffer (EJC 2023, arXiv:2202.09172v3),
  Denisov–Wachtel (AIHP 2024; Ann. Probab. 2015), Fischler–Rivoal (2014),
  Bostan–Raschel–Salvy (2014), the OEIS entries (oeisdata `da8d37c6`).
- Source 46: batch 77, manuscript 46, archive
  `oeis-bimodal-full-asymptotics.zip`; arrival `096ee7b87`, placement
  `aa7345800`, same write. No pin. Inputs: source 45 (embedded),
  Fusy–Narmanli–Schaeffer, Denisov–Wachtel, Bañuelos–Smits (PTRF 1997).
- Where the merge had to choose:
  - Source 45 is printed once; source 46's embedded copy is not shipped.
  - The guide is unnumbered, so Part I keeps source 45's numbers and the
    numbers in source 46's Foundation references stay correct.
  - Source 46's Section 2 (Section 12 here), a restatement of Part I's
    inputs in its own notation, is kept with a pointer note, because Part
    II cites its displays.
  - Appendix A (source 45's) is placed after Part II.
  - Letters are kept, with a clash table, rather than renamed.
  - One bibliography: source 45's entries, plus Bañuelos–Smits; source 46's
    entries for Fusy–Narmanli–Schaeffer and Denisov–Wachtel are the same
    papers; its `Foundation` entry is replaced by Part I; its uncited `OEIS`
    entry duplicates source 45's two OEIS entries and is omitted. Source 45's
    uncited entry for Denisov–Wachtel 2015 is kept, as delivered.
