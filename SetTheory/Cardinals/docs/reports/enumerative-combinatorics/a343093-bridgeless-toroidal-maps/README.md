# Bridgeless Toroidal Maps

**A proof of Bala's square-convolution conjecture for OEIS A343093, positive coefficient formulas, and a three-term asymptotic expansion**

A research report dated 4 October 2026 (UTC), printing Section 2 of one
three-subject manuscript, *Three advances on OEIS conjectures and
asymptotics. Bridgeless toroidal maps, golden-ratio moment laws, and
unitary-divisor partitions*. Its title page reads "Prepared with ChatGPT /
Building on Vladimir Reshetnikov's ProveIt research repository"; the PDF
author field reads "Prepared with ChatGPT". No human author is named.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 86, manuscript 01 | `oeis_advances.zip` (wrapper directory `oeis_advances/`, 580,552 bytes, 11 files), arrival commit `ae9baa422`; main file `oeis_advances.tex` | `eaf08931c` (`eaf08931cbfd0132dd36ab82a7743ccb02506dc7`, 3 October 2026 17:59:12 Pacific, quoted in Section 1, the delivery README and both ProveIt bibliography entries) | `0f084afa9` (batch 86A) | Sections 1 (adapted) and 2 (whole) of this report, with the map parts of its Sections 8 and 9; its Sections 3-7 are printed elsewhere (below) |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The manuscript says it
"has received internal mathematical review but has not been externally
refereed or formalized in a proof assistant", and that "a bounded literature
search is not an exhaustive priority search". Its finite checks are checks of
implementations and constants, "not proofs of infinite asymptotic claims".

## What it proves

`b_n` counts rooted toroidal maps with `n` edges and no bridges (isthmuses):
maps are connected graphs, loops and multiple edges allowed, cellularly
embedded in the oriented torus, rooted at a dart; cut vertices are allowed.
This is OEIS A343093 (`b_0 = b_1 = 0`, then 1, 14, 159, 1680, …).

- **Theorem 2.2 (Bala's conjecture).** With `U = t(1+U)^4`,
  `Σ b_n t^n = U²/(1−3U)²`, and hence
  `Σ_{n≥2} b_n t^n = ((1/4) Σ_{n≥1} C(4n,n) t^n)²`, the identity posted as a
  conjecture by Peter Bala (24 July 2025) in A343093.
- **Proposition 2.1 (bridge decomposition)**, with the root accounted for:
  `M(z,u) = 1 + z M² + B(z/(1−zM)², u)` for all rooted maps `M` and
  nonempty bridgeless maps `B`, genus marked by `u`, and its inverse form
  (2.4). A re-proof, with explicit root normalization, of a classical
  decomposition (Courtiel–Yeats–Zeilberger 2019, Proposition 23, with a
  different root convention).
- **Corollary 2.3:** `b_n = (1/16) Σ_{k=1}^{n−1} C(4k,k) C(4(n−k),n−k) =
  (1/n) Σ_{j=0}^{n−2} (j+1)(j+2) 3^j C(4n, n−2−j)`; since
  `C(4k,k)/4 = C(4k−1,k−1)`, the numbers count ordered pairs of binary words
  (no bijection with maps is claimed). The algebraic equation (2.14) of
  degree 4 in `B_1`.
- **Theorem 2.4:** `b_n = (256/27)^n [1/24 − 7√6/(216√π) n^(−1/2) +
  217√6/(93312√π) n^(−3/2) + O(n^(−5/2))]`, with a full expansion in odd
  powers of `n^(−1/2)` available by the same procedure; and (2.17)
  `b_n / m_{1,n} ~ (64/81)^n`, where `m_{1,n} ~ 12^n/24` counts all rooted
  toroidal maps.
- Section 2.6: the four local research questions (a direct bijection; a
  vertex/face refinement via A343092; genus two and higher; marking bridges).

## What is not claimed

- **Classical inputs, credited, not new:** the planar and toroidal
  generating functions (Bender–Canfield–Robinson 1988, equations (4.20) and
  (4.22)), the bridge decomposition (Courtiel–Yeats–Zeilberger), Lagrange
  inversion and singularity analysis. The new statement is the proof of the
  posted identity and its consequences.
- Priority: the producer's bounded source audit found the conjecture still
  marked as such in A343093; this "does not establish that every equivalent
  specialization is absent from the older map-enumeration literature".
- The algebraic equation (2.14) is an elimination relation; it does not by
  itself select the branch.
- No direct bijection is given for the square; the binary-word model is an
  equinumerosity, not a bijection.
- The numerical diagnostics (`(27/256)^n b_n` at `n = 32, 128, 512`) only
  check the implemented constants; the error term is proved.
- **Nothing was submitted to OEIS**, by the producer ("No update or
  submission has been made as part of this work") or by the intake.

The manuscript's other subjects carry their own non-claims, kept with them
(see "Where the rest of the manuscript is printed").

## Checks made at intake

On 3 October 2026 the intake reran `code/verify_maps.py` on a scratch copy
(`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0`, Python
3.13.5, Windows): exit 0 in about 30 s (including environment setup); its
JSON output and its standard output both equal `data/maps_checks.json` after
removal of carriage returns. Independently, the intake expanded
`U²/(1−3U)²` with `U = t(1+U)^4` as a power series and found it equal to the
convolution formula through `t^59` (the first ten values are the
manuscript's list), and computed `((27/256)^n b_n − three-term
approximation)·n^(5/2)` as `−2.2132·10^(−5)` at `n = 1000` and
`−2.2079·10^(−5)` at `n = 4000`, consistent with the `O(n^(−5/2))` error
(the shipped file records about `−2.22·10^(−5)` at `n = 32, 128, 512`). The
intake also re-derived by hand the `n^(−3/2)` coefficient from the Puiseux
coefficients (2.16) and the ratio (2.17) from (2.2) and Theorem 2.4. The
rotation-system counts in `data/maps_checks.json` agree with the known
values (all rooted planar maps 2, 9, 54, 378 for 1-4 edges; all rooted
toroidal maps 1, 20, 307 and bridgeless toroidal maps 1, 14, 159 for 2-4
edges).

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats maps, and the report's place
in the collection confers no formal status. The one formal neighbour is
general: a Lagrange–Bürmann theorem,
`Fabius.Lagrange.coeff_solution_subst_derivative` in
`Analysis/FabiusFunction/Lean/FabiusFunction/LagrangeInversion.lean`
(`n [z^n] H(g) = [w^(n−1)] H'(w) φ(w)^n` for `g = z φ(g)`). The two
Lagrange-inversion steps of Section 2 (Theorem 2.2 with `H = log(1+w)`,
Corollary 2.3 with `H = w²/(1−3w)²`, both with `φ = (1+w)^4`) have that
form, but nobody has instantiated it for them.

**No previous treatment.** At placement and again at this writing, a search
of the tracked tree for A343093, "bridgeless", "rooted map", "chord
diagram", Bender–Canfield–Robinson and `\binom{4n}{n}` found nothing outside
this report. The manuscript's sentence that the inspected snapshot has no
A343093 match remains true. The report continues no repository material and
answers no question of another report.

**Where the rest of the manuscript is printed.** The manuscript's Sections
3–7 continue two existing reports and were placed with them in `0f084afa9`
(paths relative to
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- Sections 3–6 (its Part II: A088714/A088713 moment densities, the
  golden-ratio correction profile and its interval certificate, the
  fixed-shift renewal expansion), answering Research questions 23.1, 23.3
  and 23.6: **Part IV** of
  [`a088714-bell-scale-growth`](../../generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth/)
  (Sections 35–41, prefix `gdy:`; Theorem 37.1 `gdy:reg:thm:main`,
  Theorem 38.1 `gdy:dyn:thm:allorders`, Theorem 39.1 `gdy:ren:theorem`), with
  `code/04-densities-profile-verify_dynamics.py`,
  `code/04-densities-profile-verify_renewal.py` and their two `data/` files;
- Section 7 (its Part III: two-sided oscillation of A301981/A301982),
  answering question 3 of Section 11: **Part II** of
  [`a301981-unitary-divisor-partitions`](../../generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301981-unitary-divisor-partitions/)
  (Sections 12–13, prefix `udp:tw:`; Theorem 12.5 `udp:tw:thm:main`), with
  `code/02-two-sided-verify_partitions.py` and
  `data/02-two-sided-partition_verification.json`.

Those Parts were written in the same batch as this report; the section,
theorem and label numbers above (also in Section 3 of the article) were
added in the batch-86 reciprocal notes, once all of them existed. The
manuscript's statement that the finer Bell
normalization of A088714 "remains open" (its Section 9.1 and delivery
README) was stale on arrival: manuscript 02 of the same batch
(`oeis_research_bundle.zip`, same arrival, pin `b7e4f25b6`) proves it, as
Part V of `a088714-bell-scale-growth` (Sections 42–49, Theorem 46.1,
`bnc:thm:bell`; AI-assisted, unrefereed; the intake asks for an independent
review before calling it settled). No statement of this report depends on
it. Both of those reports point back here: the A088714 report's Part IV
provenance (its Section 35) and README, and the A301981 report's README, name
this report as the home of the manuscript's Section 2 and of its
manuscript-wide non-claims.

**Neighbouring reports.** Other OEIS-numbered reports in
`enumerative-combinatorics/` (for example `a181280-binary-matrix-formula`,
`a195806-hexagonal-lattice`) share the format but no mathematics; nothing in
the collection treats maps on surfaces.

## What the write changed

`article.tex` is the delivered manuscript cut to this subject. Printed
unchanged: the introduction's opening, Section 1.1, Section 1.4 (the
manuscript-wide novelty boundary), the whole of Section 2, the opening paragraph
of Section 8, the map row of its table, its review disclaimer, the
introduction of Section 9, and Sections 9.4 and 9.7. The map diagnostics of
Section 8.3 are kept with their first sentence adapted ("The maps likewise
have" became "The maps have").
Changed:

- title, PDF metadata, running head and abstract adapted to the map subject
  (the abstract's first sentence is the delivered one; a marked `[write]`
  sentence replaces the rest);
- Sections 1.2 and 1.3 (summaries of the other subjects, with equations
  (1.2)–(1.4)) replaced by a dated note; Section 8.2, the renewal part of
  Section 8.3, Section 8's closing partition paragraph, and Sections 9.1–9.3,
  9.5 and 9.6 removed, each with a dated note saying where it is printed;
  the `\part` headings removed;
- a new Section 3, "The manuscript's Sections 3–7: where they are printed",
  and a new Section 6, "Provenance", both dated `[write]` notes; the
  delivered Sections 8 and 9 are Sections 4 and 5 here;
- eight dated `[write]` notes in all (end of Section 1.4: provenance, pin
  and repository claims, notation; Section 1.2; Section 3; Section 4.1, the
  shipped program and the intake rerun; Section 4.2; the start of Section 5;
  end of Section 5.2; Section 6), defined by a `writenote` environment in
  the preamble;
- the title page wrapped in `\hypersetup{pageanchor=false}` …
  `{pageanchor=true}`;
- the bibliography reduced from 21 to the 5 entries this report cites: the
  three map sources and the two ProveIt reports (cited by Sections 1 and 3).

The notation note at the end of Section 1.4 fixes the letters of Section 2:
`z` (edges of all maps) against `t` (edges of bridgeless cores; the
introduction's (1.1) writes `z` for the same series as (2.1)), the genus
marker `u` against the parameter `U`, and `R`, defined twice
(`√(1−12z)` in (2.2), `(1−3U)/(1+3U)` in the proof of Theorem 2.4; the same
expression under `z = U/(1+3U)²`, but a function of `t` in that proof). No
symbol was renamed. No statement, proof, number or table of Section 2 was
changed.

## Labels

Every label carries the prefix `btm:`. The delivered manuscript has 181
labels; the 28 `map:` labels of Section 2 became `btm:map:…` (25 `\eqref`
and 1 `\ref` updated), the introduction's `intro:results` and `intro:maps`
became `btm:intro:…`, and `verify:section` and `future:section` became
`btm:verify:section` and `btm:future:section`. The other 149 labels
(`intro:oscillation`, `intro:renewal`, `intro:partitions`, and the `gold:`,
`reg:`, `dyn:`, `ren:` and `part:` labels of Sections 3–7) left with their
text. Four labels were added (`btm:intro:other`, `btm:sec:elsewhere`,
`btm:future:submission`, `btm:sec:provenance`), so the report has 36 labels.
Every theorem, equation and subsection number of Section 2, and equation
(1.1), is unchanged (checked against the `.aux` of a build of the delivered
source). The bibliography keys `map:oeis343093`, `map:bcr1988` and
`map:cyz2019` are citation keys, not labels, and keep their delivered names.

## Files

```text
README.md              this guide (replaces the delivery README)
article.tex            the report: manuscript 01 cut to Section 2 (labels prefixed; dated [write] notes)
article.pdf            compiled report, 14 pages
code/verify_maps.py    exact, symbolic and enumerative checks of Section 2 (SymPy, mpmath; writes JSON)
data/maps_checks.json  recorded output of verify_maps.py (delivered as verification/maps_checks.json)
```

`code/verify_maps.py` and `data/maps_checks.json` are byte-identical to the
delivery; placement moved `verification/maps_checks.json` to `data/`.
`article.tex` was staged as the delivered `oeis_advances.tex` and the
delivery `README.txt` as `README.md`; both are replaced by the written
versions. Not shipped here: the delivered 40-page `oeis_advances.pdf`
(532,372 bytes; the delivery has no checksum manifest). The other subjects'
programs and data are shipped with the reports named above. Everything
survives in the archive:
`git show ae9baa422:docs/incoming/oeis_advances.zip > <scratch>/oeis_advances.zip`.
Nothing was excluded as heavy.

**Delivery names in shipped text.** `code/verify_maps.py` writes by default
to `../verification/maps_checks.json` (from `code/`, a directory this report
does not have); the article's Sections 2.6 and 4 name the program correctly.
The delivery README (replaced) told the reader to run all four programs from
the package root and named `verification/`. The opening paragraph of
Section 4 ("four verification programs") is delivered text about the whole
archive; the note after the table of Section 4.1 says where the other three
are.

**Third-party data.** `code/verify_maps.py` embeds the first 20 terms of
A343093 (`b_2 … b_21`) transcribed from The On-Line Encyclopedia of Integer
Sequences (https://oeis.org/A343093, read 4 October 2026 UTC according to the
program); `data/maps_checks.json` records the check against them. OEIS
content is published by The OEIS Foundation Inc. under the Creative Commons
Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); these terms are
third-party data under that licence, **not** MIT-0 like the rest of the
repository. The entry is by Andrew Howroyd and the conjecture is Peter
Bala's, as attributed in the entry. No program contacts OEIS.

**Requirements.** `verify_maps.py` needs SymPy and mpmath (the recorded run
used SymPy 1.14.0 and mpmath 1.3.0 under Python 3.12.14, according to the
delivery README); the delivery ships no requirements file, so the versions
are given on the command line below.

## Rerun the checks (on a scratch copy)

The program writes its JSON to `../verification/maps_checks.json` relative
to `code/` unless `--output` is given, and prints the same JSON. Run it on a
copy with an explicit output path, never into `data/` (Git Bash, from this
directory):

```sh
R=$(pwd); T=$(mktemp -d); cp -r code data "$T/"; cd "$T"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 \
  python code/verify_maps.py --output out/maps_checks.json > maps.out   # ~30 s
tr -d '\r' < out/maps_checks.json | cmp - "$R/data/maps_checks.json" && echo same
```

(On a POSIX host use `python3` with SymPy and mpmath installed. Do not use
`python -O`: the checks are assertions. On Windows the program writes CRLF
line endings, while the shipped file is LF; compare after stripping `\r`.)
Options: `--exhaustive-max-n` (1–5, default 4; 5 enumerates 10! rotation
systems) and `--formula-max-n` (default 100).

## Build the PDF

pdfLaTeX (fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, tabularx, graphicx, xcolor, microtype, enumitem,
xurl, hyperref, fancyhdr). The article is self-contained. Build in a scratch
copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 14 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 40 pages, also without warnings.

## Provenance

- Sources cited by Section 2: OEIS A343093 (entry by Andrew Howroyd,
  conjecture by Peter Bala, 24 July 2025); E. A. Bender, E. R. Canfield and
  R. W. Robinson, *The enumeration of maps on the torus and the projective
  plane*, Canad. Math. Bull. 31 (1988) 257–271; J. Courtiel, K. Yeats and
  N. Zeilberger, *Connected chord diagrams and bridgeless maps*, Electron. J.
  Combin. 26(4) (2019) P4.37.
- Repository input: the pin `eaf08931c`, for a bounded identifier search;
  Section 2 uses no repository theorem. Sections 1 and 3 cite the ProveIt
  reports `a088714-bell-scale-growth` and `a301981-unitary-divisor-partitions`
  as hosts of the manuscript's other subjects.
- Batch 86 of `docs/incoming`, manuscript 01; arrival `ae9baa422`,
  placement `0f084afa9` (batch 86A), written in the batch-86 write phase
  (3 October 2026). Single source: the only choices were how to divide the
  shared Sections 1, 8 and 9 and the bibliography among the three
  destinations (statements about the whole manuscript are kept here in
  full).
