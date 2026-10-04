# The Source Boundary of Extensional Acyclic Digraphs

**An OEIS conjecture (A182220), finite-defect enumeration of the source
triangle A182162, and dyadic non-holonomicity**

A research article dated 3 October 2026, built from one manuscript. Its title
block reads "Prepared for Vladimir Reshetnikov / In the mathematical research
context of the ProveIt repository", and its PDF author field "Research
prepared for Vladimir Reshetnikov": the package names no human author and no
tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 07 | `OEIS_A182220_Source_Boundary_Research.zip` (wrapper directory `oeis_source_boundary/`, 864,793 bytes), arrival commit `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, the bibliography entry for ProveIt and `SOURCES.md`) | `ddf8df5d5` (batch 85C) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs; the exact integer computations check the
finite statements on recorded ranges, and the Decimal computations are
numerical diagnostics, not interval bounds.

## What it proves

An *extensional acyclic digraph* (EAD) is a finite acyclic digraph whose
vertices have pairwise distinct out-neighbourhoods. `u_m` = A001192(m) counts
EAD isomorphism classes on `m` vertices (`u_0 = 1`), `u(n,k)` those with `k`
sources (the labelled count `n! u(n,k)` is A182162), `q = ⌈log₂ n⌉`, and
`b_n^(d) = u(n, n−q−d)` is the boundary diagonal at defect `d`.

- **Theorem 3.1 (complete source support).** An EAD on `n` vertices with
  exactly `k ≥ 1` sources exists iff `k ≤ n ≤ 2^(n−k)`; hence
  **`A182220(n) = n − ⌈log₂ n⌉`**, and A182162 has no holes in any row. The
  upper bound is Tomescu's (2011, see below); the construction for every
  admissible `k` is the manuscript's.
- Proposition 3.2: the lacunary generating function of `a(n)`, with the unit
  circle as natural boundary. Lemma 2.1, Corollary 2.2, Lemma 2.3: finite
  (Mostowski) collapse onto transitive sets, rigidity (`n!` labelled copies
  per class), `1 ≤ u_m ≤ 2^C(m,2)` (classical; proofs included).
- **Theorem 4.2 (classification of extremizers):** extremal classes ↔ pairs
  (transitive core of size `q`, `(n−q)`-subset of `P(C) \ C`), so
  `b_n^(0) = u_q C(2^q − q, n − q)`; Corollary 4.3: `b_{2^m−r}^(0) =
  u_m C(2^m − m, r)`.
- Proposition 5.1, Corollary 5.2: the marked-source identity, its binomial
  inversion (the known source sieve) and the total recurrence, re-proved in
  this normalization and credited. **Theorem 5.3:** the exact `(d+1)`-term
  finite-defect formula for `b_n^(d)` (a short consequence of the sieve, as
  the article says).
- **Theorem 6.1:** `0 ≤ u_m C(M,k) − u(m+k,k) ≤ m 2^(−k) u_m C(M,k)`,
  `M = 2^m − m`, with an exact rejection sampler and a core-law
  total-variation bound `m 2^(−k)`.
- **Theorem 7.1 (entropy profile):** `log b_n^(d) = n Φ_d(ρ_n) +
  O_d((log n)²)` uniformly on each dyadic block, `ρ_n = n/2^q`; **Theorem
  7.2:** the subsequential limits of `(b_n^(d))^(1/n)` fill exactly
  `[e^(λ_d), e^(λ_(d+1))]`, `λ_d = 2^d H(2^(−d))`; for `d = 0` this is
  `[1, 4]`.
- **Lemma 8.1 (exponential-jump obstruction)** and **Theorem 8.2:** no
  `b^(d)` and no `n! b^(d)` is P-recursive; `B_d(z) = Σ b_n^(d) z^n` is not
  D-finite and has radius `e^(−λ_(d+1))` (`1/4` for `d = 0`).
- Theorem 9.1: an all-orders expansion of `log b_n^(d)` away from `p = 1`,
  with `u_m` kept exact (Stirling and Bernoulli terms), and the exact
  fixed-deletion series near complete layers.
- **Theorem 10.1, Corollary 10.2:** the arc deficit of a uniform extremizer at
  `n = 2^m − r` is within total variation `(rm + C(r,2))/2^m` of
  `Bin(rm, 1/2)`, hence a central limit law; exact conditional moments.
- Section 11: the exact checks (Tables 1–2); Section 12: a formalization
  route (a plan only) and ten research questions; Appendix A: **draft**
  OEIS-facing statements (see below); Appendix B: a proof-status ledger.

## What is not claimed

- **The formula `a(n) = n − ⌈log₂ n⌉` is not presented as new.** Its upper
  half is in Tomescu's thesis *Sets as Graphs* (Udine, December 2011),
  printed p. 29, credited in the manuscript; the intake read that page (the
  count of classes with `s` sources vanishes unless `2^(n−s) ≥ n`, "by
  extensionality and the pigeonhole principle"). The matching construction
  for every admissible source count is supplied here, without a priority
  claim. OEIS still labels the formula a conjecture, but an OEIS label is not
  a priority certificate or evidence that the problem was open in the
  literature.
- Not new either: the collapse to transitive sets, rigidity, the source sieve
  and total recurrence (Johnston's 2012 Maple program in A182162;
  Policriti–Tomescu; Tomescu), and Tomescu's source-deletion recurrence used
  by the code. The exact boundary formulas are short consequences of the
  sieve, and the article says so.
- No historical priority is established for the boundary refinements
  (entropy profiles, rate intervals, non-P-recursiveness, the arc law); the
  searches were limited. Wagner's ANALCO 2012 paper and Peddicord's 1962
  paper were not read in full, Policriti–Tomescu only at abstract level; no
  unchecked theorem from them is used.
- No natural-boundary claim for `B_d` (Remark 8.3: non-D-finiteness does not
  imply one); no asymptotic expansion of `u_m`; nothing for defects growing
  with `n`; the expansion of Theorem 9.1 excludes the complete-layer edge
  `p → 1`; the sampler is conditional on sampling the core.
- No Lean, Rocq or interval-arithmetic certification; Section 12.1 is a
  development plan, not a claim about existing declarations. The finite
  checks are tests, not proofs.
- **Appendix A is draft OEIS text and stays so.** Nothing was submitted to
  OEIS by the package's author (`STATUS.md`: "No GitHub mutation, OEIS
  submission, or external publication") or by the intake; a dated `[write]`
  note at the appendix says so. The intake did not search OEIS for the
  boundary sequence `1, 1, 2, 1, 20, 20, 10, 2, 7128, …`, which the appendix
  proposes as a possible new entry only after such a search.

## Checks made at intake

On 3 October 2026 the intake read A182220 on `oeis.org`: its formula section
lists four conjectural expressions (Karttunen 2013, Hurt 2014, Barry 2017,
Krivilev August 2026), each equal to `n − ⌈log₂ n⌉` (checked for `n < 600`),
and its 30 displayed terms agree. It read printed pages 26–29 of Tomescu's
thesis (the PDF linked in the bibliography): the source bound is on p. 29,
rigidity (Lemma 2.1.3) on p. 27, the deletion recurrence (Corollary 2.1.7)
on p. 28, as the manuscript cites them. The delivered programs passed on
scratch copies (see "Rerun the checks").

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
no formal development in ProveIt treats extensional digraphs, transitive-set
enumeration or this triangle, and the report's place in the collection
confers no formal status. The hereditarily-finite-set codings in
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean` and
`Logic/Interpretability/PAHF/Coq/PAHF.v` are syntax codings, unrelated. The
manuscript uses no repository theorem.

**Neighbouring reports** (related, no shared theorem):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a003407-dyadic-scaling-rigidity`,
  Part II: its Corollary `dsr:nh:cor:jumps` (from the local-growth rigidity
  theorem `dsr:nh:thm:rigidity`) says an integer, exponentially bounded
  P-recursive sequence without an `n`th-root limit must have exponentially
  large upward jumps. Lemma 8.1 here (`sbd:lem:jump`) is the complementary,
  elementary sufficient condition: a jump after a plateau of every fixed
  length excludes P-recursiveness. The boundary sequences here do jump, so
  a003407's criterion cannot apply to them; a dated note after Lemma 8.1
  explains this, with a003407's example `3^n + (−3)^n + 2^n` showing why the
  plateau hypothesis is needed.
- `Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets`:
  its `hset:lem:collapse` is the same classical Mostowski collapse as
  Lemma 2.1, for rooted codes.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a116379-bounded-identity-trees`:
  rooted identity trees, the other classical coding of hereditarily finite
  sets.

**Stale claims.** The manuscript's repository statements (Section 1.3 and
`SOURCES.md`: no treatment of A182220 found; the Mahonian growing-powers
alternative rejected because
`oeis-sequence-asymptotics/a380274-mahonian-growing-powers` exists) are true
at the pin and at the time of writing, and stay as dated provenance.

## Notation

The manuscript reuses several letters with local meanings (`d` as defect and
in `d/dp`; `B_d` vs the Bernoulli numbers `B_{2j}`; `T = 2^m` vs the labelled
count `T(n,k)` of Appendix A; `C`, `L`, `N`, `p`, `R`, `M`, `A`). The
labelled count `E(n, a(n))` in eq. (11) is not defined in the text; it is
`n! u(n, a(n))`. A table in the first `[write]` note (end of Section 1)
fixes each meaning, with the tempting false reading that the phase
`p = n/2^(q+d)` of Section 9 equals `ρ_n = n/2^q` (true only for `d = 0`). No
symbol was renamed.

## Labels

Every label carries the prefix `sbd:`. The manuscript's 63 labels (44 `eq:`,
9 `thm:`, 4 `lem:`, 4 `cor:`, 2 `prop:`) were prefixed before anything cited
them, and every reference was updated (28 `\eqref`, 14 `\ref`). Five section
labels were added for the notes (`sbd:sec:entropy`, `sbd:sec:expansion`,
`sbd:sec:formal`, `sbd:sec:questions`, `sbd:app:oeis`), so the report has 68
labels.

The writing step also:

- added four dated `[write]` notes: end of Section 1 (provenance, Tomescu's
  credit and the meaning of the OEIS label, the intake's OEIS check,
  repository relations, the notation table), after Lemma 8.1 (the a003407
  counterpart), end of Section 11 (shipped layout, the unshipped transcript,
  the intake's rerun, the OEIS licence), and end of Appendix A (draft, not
  submitted);
- kept the title page out of the PDF page anchors (`pageanchor=false`), which
  removes the duplicate `page.1` destination of the delivered source;
- disabled the `--` ligature in typewriter text (microtype
  `\DisableLigatures`): the delivered PDF printed `--max-n 64 --brute-n 7` in
  Section 11.2 with en dashes;
- let URL-style paths break after hyphens, and set the bibliography ragged
  right (three underfull lines in the delivered build).

No statement, proof or number of the manuscript was changed.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered main file; labels prefixed, four [write] notes)
article.pdf                  compiled report, 23 pages
SOURCES.md                   the package's source and provenance notes (as delivered)
STATUS.md                    the package's proof and verification status (as delivered)
manifest-entry.tex           the package's suggested catalogue paragraph (as delivered)
code/verify.py               exact checks and brute-force enumeration (delivered at the package root)
code/check_asymptotics.py    Decimal diagnostics of the first correction (delivered at the package root; imports verify.py)
data/verification.json       recorded exact run: counts of checks and the n <= 7 enumeration
data/source_triangle.csv     u(n,k) and n! u(n,k) for every positive cell, n <= 64 (1759 rows; CRLF)
data/boundary_counts.csv     a(n), b_n^(0), b_n^(1), b_n^(2), n! b_n^(0) for n <= 64 (64 rows; CRLF)
data/asymptotic_checks.csv   relative errors before and after the first correction (12 rows, 70 digits; CRLF)
data/asymptotic-output.txt   printed transcript of check_asymptotics.py
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement moved `verify.py` and
`check_asymptotics.py` to `code/` and staged the delivery README as
`README.md`, which this guide replaces. Not shipped, and recoverable from the
archive
(`git show 9d6968c8a:docs/incoming/OEIS_A182220_Source_Boundary_Research.zip > <scratch>/a182220.zip`):

- the delivered 21-page `article.pdf` (437,459 bytes);
- `SHA256SUMS`, the checksum manifest (14 of 14 entries verified at
  placement; repository policy ships no checksum manifests);
- `data/verification-output.txt` (2,127 bytes), which the delivery README
  calls "human-readable output" but which is a **byte copy of
  `data/verification.json`**: `verify.py` prints the JSON report it writes.

Nothing was excluded as heavy; the largest file, `data/source_triangle.csv`
(852,626 bytes), is regenerated byte for byte by `verify.py` in seconds.

**Third-party data.** `code/verify.py` embeds, as test fixtures, the first
17 terms of A001192 and the first 25 flattened terms of A182162, copied from
The On-Line Encyclopedia of Integer Sequences (https://oeis.org). OEIS
content is published by The OEIS Foundation Inc. under the Creative Commons
Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); those fixture lists are
third-party data under that licence, not MIT-0 like the rest of the
repository. The program never contacts OEIS.

Delivered text that names the delivery layout or a file not shipped:
`SOURCES.md` and `STATUS.md` are unchanged (`STATUS.md`'s "The final PDF was
compiled with pdfLaTeX" describes the delivered 21-page PDF);
`manifest-entry.tex` calls itself "not uploaded or committed" (it is now
committed as a delivered file; the collection's own catalogue entry is
separate); `code/verify.py`'s docstring says `python verify.py` from the
package root; both programs default their output to a `data/` directory next
to the script. The article's mentions of "the accompanying program" and
`verify.py` mean `code/verify.py`.

**Byte-level notes.** The three CSV files are CRLF throughout (Python's `csv`
module); three lines `docs/reports/…/a182220-source-boundary/data/<name>.csv
-text` in `SetTheory/Cardinals/.gitattributes` keep their bytes.
`verify.py` writes `verification.json` in text mode, so on Windows a rerun
emits it with CRLF where the shipped file is LF; compare after stripping
`\r`.

## Rerun the checks (on a scratch copy)

Never run the programs in place: `verify.py` defaults `--out` to `code/data/`
beside itself, and `check_asymptotics.py` has no output option and writes to
`data/asymptotic_checks.csv` next to the script (in place it fails, or, once
`verify.py` has created `code/data/`, writes there). Rebuild the delivered layout on a copy
(Git Bash, from this directory; standard library only, Python 3.10 or later):

```sh
T=$(mktemp -d); X="$T/oeis_source_boundary"; mkdir -p "$X"
cp code/verify.py code/check_asymptotics.py "$X/"
cd "$X"
py verify.py --max-n 64 --brute-n 7 > "$T/verify.out"   # about 7 s
py check_asymptotics.py > "$T/asym.out"                 # about 4 s
cd - >/dev/null
for f in "$X"/data/*; do
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/$(basename "$f")") \
    && echo "same  $(basename "$f")" || echo "DIFF  $(basename "$f")"; done
tr -d '\r' < "$T/verify.out" | cmp - data/verification.json && echo "stdout = verification.json"
tr -d '\r' < "$T/asym.out"   | cmp - data/asymptotic-output.txt && echo "transcript matches"
```

(On a POSIX host use `python3` for `py`.) At intake (3 October 2026, Windows,
Python 3.14.4) this printed `same` for all four files (the three CSV files
byte for byte, `verification.json` after CRLF stripping) and both matches.
The run checks 2,080 triangle cells by two recurrences (the marked-source
sieve and Tomescu's deletion recurrence), 2,080 covering inequalities, 64
extremizer counts and 354 finite-defect entries (`d ≤ 5`), the 17 + 25 OEIS
fixture terms, and an exhaustive enumeration through `n = 7` (75,598 classes
at `n = 7`) with its source rows and extremal arc distributions;
`check_asymptotics.py` confirms at `n = 192, 768, 3072, 12288` and
`d = 0, 1, 2` that the first correction improves all 12 leading
approximations. `--brute-n 0` skips the enumeration; `--max-n` extends the
exact triangle.

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, booktabs, array, longtable,
enumitem, xcolor, graphicx, fancyhdr, hyperref, lmodern, microtype); the
bibliography is embedded. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 23 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 21 pages with one duplicate destination
(`page.1`) and three underfull bibliography lines.

## Provenance

- Sources cited by the manuscript: OEIS A182220, A182162, A001192, A182161;
  Tomescu, *Sets as Graphs* (PhD thesis, Udine, 2011); Policriti–Tomescu,
  Inform. Process. Lett. 111 (2011) 787–791; Wagner, ANALCO 2012, 1–8;
  Peddicord, Proc. AMS 13 (1962) 825–828.
- Repository input: the pin `6bf7f30d0` (3 October 2026), used for a limited
  non-duplication search; no repository theorem is used.
- Batch 85 of `docs/incoming`, manuscript 07; arrival `9d6968c8a`, placement
  `ddf8df5d5` (batch 85C), written in the batch-85 write phase
  (3 October 2026). Single source, so the write made no merge choices.
