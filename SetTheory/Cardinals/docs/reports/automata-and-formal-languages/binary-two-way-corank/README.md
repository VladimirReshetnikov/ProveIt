# Binary Two-Way Automata and Corank Budgets in Brauer Monoids: an Explicit Exponential Binary 1NFA-to-2DFA Lower Bound

**For every `h ≥ 2`, an explicit language `B_h ⊆ {0,1}*` with a
`(6h+2)`-state one-way NFA such that every `s`-state two-way DFA for it
satisfies `8s + 2 ≥ 2(5/2)^⌊(h−2)/9⌋`; hence, for `n ≥ 14`, an `n`-state
binary 1NFA may need at least `¼(5/2)^⌊(n−14)/54⌋ − ¼` 2DFA states (exponent
coefficient `log₂(5/2)/54 = 0.0244801499…`). Ingredients: a
repetition-independent corank budget for words in Brauer idempotents
(`corank(w) ≤ Σ corank(e_i)`), used twice in a `p × q` relation-addition
amplifier (`p = q = 5` optimal there), giving degree `≥ 2(5/2)^⌊(h−2)/9⌋`
for any Brauer submonoid with a unital surjection onto the full relation
monoid on `h` points; a symbol-local sparse-slot matching representation of
an `s`-state 2DFA over `a` letters in degree `≤ 2(a+2)s + 2` (`8s + 2` for
binary), with linear order necessary; a two-register four-letter compiler on
`2h` states with a `6h+2`-state binary decoder. Also: the sharp support
bound for idempotents with equality count `m!/(q!(m−3q)!)` and stability
constants 5 and 4; a parity-aware integer recurrence `D(h)`;
`2(5/2)^⌊(h−2)/9⌋ ≤ β(h) ≤ 12·4^h + 26`; a union-graph obstruction in
`𝓑_4`; and a binary 2NFA complementation bound that is
conditional on an external, unverified premise (Theorem 5.4).**

A research article dated 7 October 2026, built from one manuscript. Its
title page, PDF author field and delivery README read "Prepared with ChatGPT
for Vladimir Reshetnikov"; its verification section says its own review "was
an additional AI-assisted mathematical review, not independent human peer
review". It names no human author.

| Source | Delivery | Archive | Pins | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | non-Gowers intake NG3, manuscript 01 | `ProveIt_Binary_Two_Way_Corank.zip` (32 files in one wrapper directory `Binary_Automata_Corank/`, 581,213 bytes, SHA-256 `e1817c4d2f42…65b36439c`), arrival commit `964621dd2`; `article.tex` + 7 section files (2,214 lines, 31 pp.) | ProveIt `670a67d35` (7 October 2026, 13:09 −0700; exists); external `openai/math` `adc7f1241b42` (not checked) | `bdcae034b` (29 files, delivered layout, unprefixed) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report.

## Trust boundaries

- **What is proved in the text.** Theorem 1.1 (the binary determinization
  bound) and everything it uses: Lemmas 2.1, 2.7–2.9, Theorems 2.2, 2.5,
  2.12, 2.13, Corollaries 2.3, 2.6, Propositions 2.11, 2.14, 2.15 (Section
  2); Theorems 3.1 and 3.4 (Section 3); Theorem 4.1, Corollary 4.2,
  Proposition 4.3, Lemma 4.4 (Section 4); and Propositions 7.1 and 7.2.
- **What is conditional — not a proved result of this report.** Theorem 5.4
  (binary nondeterministic complementation: every `s`-state 2NFA for
  `{0,1}* \ B_h` has `s ≥ ½·2^⌊(h−2)/127⌋ − 1`; for `n ≥ 14`,
  `½·2^⌊(n−14)/762⌋ − 1`) assumes Theorem 5.1, the "Order-reversing image
  bound" (`amp:image`) of the companion OpenAI manuscript on two-way
  nondeterministic complementation, stated but **not proved here and not
  checked by the write**. Lemma 5.2 and Proposition 5.3 (the transfer) are
  proved here; Lemma 5.2 normalizes the companion's construction.
- **What rests on computation.** Nothing in the proofs; the shipped audits
  and the write's own code are finite diagnostics.
- **What is prior.** The cap-component classification of Brauer idempotents
  (Dolinka et al. 2015); the relation-corner and tree-contour architecture
  (the OpenAI liveness manuscript of 25 September 2026, adapted with
  attribution; its bounds `2^⌊(h−2)/31⌋` and `4(s+1)²`); fixed-alphabet
  transfer (TheoremDB R816: `3h` four-letter, `9h` binary states); the
  exponential order of `β(h)`.

## What it proves

Machine model: two distinct endmarkers, start on `⊢`, moves `−1, 0, +1`,
partial transitions, acceptance on entering an accepting state at any time
(including initially), all states counted (`8s + 10` under a convention that
forbids initial acceptance). `𝓑_m` is the Brauer monoid, `𝓡_H` the monoid of
relations on `H`. Statement and equation numbers are the delivered ones (the
article numbers equations consecutively).

- **Theorem 1.1 (`btc:intro:main`)**: (1)–(2), as in the headline.
- **Theorem 2.2 (`btc:alg:budget`)**: `corank(w) ≤ Σ_i corank(e_i)` for every
  word `w` in idempotents `e_1, …, e_v` (4); Corollary 2.3 relative to an
  idempotent (6); Remark 2.4 on sharpness.
- **Theorem 2.5 (`btc:alg:support`)**: `|supp(e)| ≤ min{m, 3c/2}`, exact
  maximum; deficit identity (8); equality iff all nontrivial components are
  three-vertex paths; stability constants 5 and 4, both sharp; Corollary 2.6:
  `m!/(q!(m−3q)!)` maximizers (9).
- **Lemmas 2.7–2.9**: faithful rank-preserving corner reduction; minimum-rank
  corners lift units; the full relation corner `Q = PEP`.
- **Proposition 2.11 (`btc:alg:amplification`)**: an addition bound `L` at size
  `h − p − q + 1` gives `pqL/(p + q)` at size `h`; **Theorems 2.12–2.13**:
  `F(h) = 2(5/2)^⌊(h−2)/9⌋` (18) and `k ≥ F(h)` (19) for any
  identity-containing submonoid of `𝓑_k` mapping unitally onto `𝓡_H`.
- **Proposition 2.14**: `p = q = 5` maximizes `log(pq/(p+q))/(p+q−1)` (rate
  `log₂(5/2)/9 = 0.1468808994…`); **Proposition 2.15**: the recurrence `D(h)`
  (21), `k ≥ 2D(h)`.
- **Theorem 3.1 (`btc:mach:representation`)**: symbol-local diagrams in
  `𝓑_k`, `2 ≤ k ≤ 2(a+2)s + 2` (22); **Theorem 3.4**: degree `≥ s` is
  sometimes necessary (binary, via the symmetric group).
- **Theorem 4.1, Corollary 4.2**: the four-letter compiler `w(R)` (31) with
  exactly one path per entry and integer path-count products, `|w(R)| =
  h² + h + 1 + |R|`; **Proposition 4.3**: the `6h+2`-state binary 1NFA and
  (34); **Lemma 4.4**: the encoded singleton-context quotient onto `𝓡_[h]`;
  (35): `s ≥ max{1, ⌈(D(h) − 1)/4⌉}`.
- **Section 5 (conditional)**: Theorem 5.1 imported; Lemma 5.2, Proposition
  5.3 proved; Theorem 5.4 conditional (40)–(41).
- **Proposition 7.1**: `2(5/2)^⌊(h−2)/9⌋ ≤ β(h) ≤ 12·4^h + 26`;
  **Proposition 7.2**: two rank-two idempotents in `𝓑_4` with connected union
  cap graph and `ab = b`, `ba = a`.

Added by the write (7 October 2026), marked `[write]`:

- A status and trust-boundary note after the title page (what is proved,
  what is conditional, what is prior).
- Subsection 1.5 (`btc:intro:provenance`): provenance, the sources as the
  write read them, what was checked, relation to the repository, the
  collected non-claims, reading conventions.
- Dated notes at the ends of Sections 2, 3, 4, 5, 6 and 7.

## What is not claimed

From the source, kept in the article (collected in Subsection 1.5):

- No priority certification ("A targeted literature and repository review
  cannot certify priority against all existing work"; the corank budget's
  priority "unconfirmed" in the ledger; the negative search in East–Gray "is
  not a proof of novelty"); binary transfer is not claimed to originate here.
- The coefficient `log₂(5/2)/54`, the constant 8 in `8s + 2` and the compiler
  size are not claimed optimal; `p = q = 5` is optimal only within the
  rectangular amplifier; the block-length counting bound does not bound
  states.
- No `L ≠ NL` or other uniform space separation; nothing about time,
  reversals or witness length.
- Finite audits are diagnostics; no Lean formalization (the upstream Lean
  development was neither extended nor rerun); no human peer review;
  Theorem 5.4 rests on an external premise that is not reproved.

The write adds: its checks are exact finite computations or hand
computations; it read the imported premise's statement only.

## Further questions

Section 7 keeps the source's eight research questions: the exponential rate
of `β(h)`; nonrectangular amplifiers; when the generated minimum rank attains
the union parity floor; the least fixed-alphabet compiler and its ambiguity;
a constant `c < 8` in sparse matching representations; a
repetition-independent budget in the ordered path-diagram monoid (to improve
the constant 127); short distinguishing witnesses; a staged formalization.
A dated note (Vladimir's standing rule of 4 October 2026) records that no
claim of the source is unproved as stated outside them and none is wrong;
**nothing was moved or refuted**. Theorem 5.4 is stated by the source as
conditional and stays in Section 5, marked so.

## Checks

- **At placement** (NG3 dossier, 7 October 2026): the 29 staged files
  byte-identical to a fresh extraction; `SHA256SUMS` 31/31; the pin exists and
  the three neighbour README blobs it cites are unchanged; the manuscript read,
  no error found; by hand: the main arithmetic, the corank budget, the
  amplifier, the optimization, the compiler, the quotients, Theorem 3.4 and
  Proposition 7.1; own code: idempotent counts for `m ≤ 6`, the support
  bound and equality counts, the budget on 30,756 random word prefixes, the
  union obstruction, `D(h)` for `h ≤ 256`, `p = q = 5` over `p, q ≤ 300`, the
  floor identities, the compiler's exact path counts; the suite rerun on a
  copy (pass). The sparse-slot wiring and the imported premise read, not
  re-derived.
- **At the write** (7 October 2026; Windows 11, Python 3.14.4, mpmath 1.3.0;
  own code in the intake work area, not shipped):
  - every proof of Sections 2–4 and of Lemma 5.2, Proposition 5.3 and
    Theorem 5.4 (as a deduction) read line by line, with no error found; the
    steps rechecked by hand are listed in the notes at the ends of Sections
    2–5 (among them the connector argument, the parity step of the budget,
    the deficits and attaining configurations, `Q = PEP`, the amplifier's
    images and budgets, `312/343`, `5⁷ > 2¹⁶`, the compiler path analysis,
    the floor identities `/54` and `/762`, the antitone step);
  - own Brauer multiplication: all 146,600 perfect matchings for `m ≤ 7`,
    idempotents `1, 1, 2, 10, 40, 296, 1936, 17872`, support equality cases
    `1, 1, 1, 7, 25, 61, 481, 2731` (`= Σ_q m!/(q!(m−3q)!)`), as in the
    table of Section 6; the budget on every ordered idempotent pair and every
    two-generator monoid for `m ≤ 4` (the shipped counts 1,706, 1,898, 826
    and 4,280 reproduced) and on 42,000 random word prefixes for
    `4 ≤ m ≤ 10` (no violation); Proposition 7.2's `ab = b`, `ba = a`;
  - `D(h)` for `h ≤ 256` against all 255 CSV rows and the table of Section 6;
    the rates `0.1468808994…`, `0.0244801499…` (truncations); argmax `(5, 5)`;
    floor identities for `14 ≤ n ≤ 2·10⁵`; `12(2^{2h}+2)+2 = 12·4^h + 26`;
    the audit case counts of Section 6 from their definitions (66,066,
    262,404, 4,674, 32,764, total 365,908; 288 machines, 63 words, 50,400
    comparisons, 3,200 diagrams);
  - the shipped suite rerun on a copy (`py code/run_all.py --output-dir
    <scratch>`, 97 s): PASS; every certificate equal to the shipped one as
    data except `elapsed_seconds`, `python` and `limits/output`;
    `finite_bounds.csv` byte-identical;
  - the imported Theorem 5.1 compared, as a statement, with a copy of
    `sections/diagrams.tex` of the companion manuscript at `adc7f1241`
    fetched at the write: same hypotheses (surjective multiplicative,
    inclusion-reversing, identity preservation not assumed) and bound
    `2m ≥ 2^⌊(h−2)/127⌋`; its proof (`sections/amplification.tex`) not read;
  - the bibliography: 27 entries, 19 cited and printed, the built
    `article.bbl` equal to the delivered one.
- **Not read**: the OpenAI liveness manuscript, its Lean summary, TheoremDB
  R816 and the cited literature; the manuscript's accounts of them are
  reported, not confirmed.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status. No Lean or Rocq declaration in ProveIt
concerns Brauer monoids, matching diagrams, relation monoids or two-way
automata.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/`): the
manuscript read the READMEs of `shuffle-six-state-bound`,
`dfao-reversal-coloring-obstruction` and `constrained-crossover-closure`
(blobs `077d0777`, `92fa1fc9`, `e8ff27d7` at the pin, unchanged at the
write) for context; no theorem of theirs is a premise and none shares a
result with this report, so no reciprocal note is proposed.
`shuffle-six-state-bound` draws the same distinction between a full
transformation alphabet and a fixed small alphabet that motivates the binary
compiler.

**Words that mean something else elsewhere.** "Liveness" here is the
one-way liveness language family of two-way automata theory; the
`hilbert-tenth-problem/liveness-beyond-halting` report treats temporal
liveness of computations. `lib/openai-math` holds an unrelated family of the
external release; the manuscripts this report adapts are not vendored.

**Stale claims.** None: the manuscript's statements about the repository
were true at its pin and still are.

## Notation

A table at the end of Subsection 1.5 fixes the letters the manuscript
reuses, with the tempting false readings: `s` (states; an arm sum in
Proposition 2.15), `k` (Brauer degree; a set size in Proposition 2.11), `m`
(Brauer degree; labels per direction of `𝒯_m`), `a, b, t, r`, `U, V`,
`F, E, P, Q`, `β, ρ, δ`, `R, R_e`, `D(h), D^±`, `L, J, C`, and "liveness".
No symbol was renamed.

## Labels

Every label carries the prefix `btc:` (none existed in the repository). The
manuscript's 91 labels kept their section prefixes after it (`alg:` 40,
`comp:` 19, `complement:` 11, `mach:` 10, `intro:` 5, `research:` 5,
`verify:` 1; for example `alg:budget` → `btc:alg:budget`) and the 85
references to them (53 `\ref`, 32 `\eqref`; `cleveref` is loaded but not
used) were updated. `THEOREM_LEDGER.csv` keeps the delivered names; prefix
them with `btc:` to find them in `article.tex`; its 20 numbers are the
delivered ones. The write added 1 label, `btc:intro:provenance`; the report
has 92. Builds of the delivered text and of this one give all 91 delivered
labels the same numbers (aux files compared): the added subsection is the
last of Section 1, the notes follow the last delivered text of their
sections, and no numbered statement, display, table or figure was added.

## Files

```text
README.md                              this guide (replaces the delivery README.txt)
article.tex                            main file (delivered; preamble macros, status note added)
article.pdf                            compiled report, 37 pages (built by the write)
sections/introduction.tex              problem, sources, main theorem; Subsection 1.5 added
sections/algebra.tex                   budget, sharp support, corners, amplifier, recurrence
sections/machines.tex                  sparse-slot representation, linear necessity
sections/compiler.tex                  four-letter compiler, binary decoder, quotient, main proof
sections/complement.tex                imported premise and the conditional complementation bound
sections/verification.tex              audit design, counts, reproduction
sections/research.tex                  research questions, beta bounds, union obstruction
references.bib                         bibliography (27 entries, 19 cited; delivered)
Makefile                               pdflatex/bibtex build and audit target (delivered)
SOURCE_AUDIT.txt                       source versions, paths, blob ids, limits (delivered)
source_manifest.json                   hashes of the producer's local source snapshots (delivered)
THEOREM_LEDGER.csv                     claim-to-proof map with delivered labels (delivered, CRLF)
THIRD_PARTY_NOTICES.txt                attribution of the adapted exposition (delivered)
LICENSE-APACHE-2.0.txt                 Apache License 2.0 text supplied with the upstream source (delivered)
code/run_all.py                        runner; runs the five audits under python -O (delivered)
code/brauer_audit.py                   perfect matchings through degree 7, idempotents, support (delivered)
code/idempotent_budget_audit.py        corank budget, exhaustive through degree 4, sampled to 12 (delivered)
code/relation_compiler_audit.py        compiler and decoder path counts, 365,908 cases (delivered)
code/sparse_slots_audit.py             local matching diagrams against direct execution (delivered)
code/finite_bounds.py                  D(h) through h = 256 and the union obstruction (delivered)
certificates/brauer_audit.json         reference output (delivered)
certificates/idempotent_budget_audit.json  reference output, with seed (delivered)
certificates/relation_compiler_audit.json  reference output, with case-stream digest (delivered)
certificates/sparse_slots_audit.json   reference output (delivered)
certificates/finite_bounds.json        reference output (delivered)
certificates/finite_bounds.csv         D(h) table, h = 2..256 (delivered, CRLF)
certificates/run_summary.json          runner summary (delivered)
```

There are 30 files. Every file except `README.md`, `article.tex`, the seven
`sections/*.tex` and `article.pdf` is byte-identical to the delivery.
`THEOREM_LEDGER.csv` and `certificates/finite_bounds.csv` are delivered with
CRLF line ends and kept byte-for-byte by two `-text` lines in
`SetTheory/Cardinals/.gitattributes`.

**Licence.** The repository is MIT-0, but the adapted exposition is
distributed with the upstream Apache License 2.0 text and
`THIRD_PARTY_NOTICES.txt`, which are this report's nested licence.

**Not shipped**, recoverable from the arrival commit (next section): the
delivered `article.pdf` (31 pages, 493,967 bytes), the prebuilt
`article.bbl` (5,736 bytes; the collection's `.gitignore` un-ignores `.bbl`
files) and `SHA256SUMS` (2,779 bytes, 31 entries, verified at placement;
repository policy ships no checksum manifests); the delivery `README.txt`
(5,782 bytes) was staged as `README.md` at placement and is replaced by this
guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.** The
delivery README's file map lists `article.pdf` (now the write's build),
`article.bbl` and `SHA256SUMS`; the verification section and the README run
`python3 code/run_all.py --output-dir reproduced` and the `Makefile`'s
`audit` target does the same, which writes `reproduced/` inside the report
directory — run on a copy instead; `SOURCE_AUDIT.txt` and
`source_manifest.json` name the producer's local snapshots (`ProveIt_0.md`,
`complementation/*.tex`, `formalization129.md`, …), none shipped, so their
hashes cannot be checked here; `certificates/relation_compiler_audit.json`
records the producer's sandbox output path
`/workspace/scratch/3b2ceb1576c8/research_checks/relation_compiler_audit.json`
(no personal data; kept byte-for-byte).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 964621dd2:docs/incoming/ProveIt_Binary_Two_Way_Corank.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # e1817c4d2f42d0067d38aa11ee3cb27d703c6c0e7d551fbe66b4ad865b36439c, 581,213 bytes
cd "$T" && unzip -q a.zip   # creates Binary_Automata_Corank/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run the suite inside the
repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/binary-two-way-corank
C=$(mktemp -d); cp -r "$R/code" "$C/"; cd "$C"
python code/run_all.py --output-dir out    # about 100 s
```

Compare `out/` with `$R/certificates/`: the counts, seeds and the compiler's
case-stream digest must agree; `elapsed_seconds`, `python` and the absolute
`limits/output` path differ. At the write (Windows, `py` for `python`) the run
passed in 97 s with exactly those differences and `finite_bounds.csv`
byte-identical.

## Build the PDF

pdfLaTeX and BibTeX (fontenc, inputenc, lmodern, geometry, amsmath, amssymb,
amsthm, mathtools, microtype, booktabs, longtable, array, enumitem, xcolor,
tikz, fancyhdr, xurl, hyperref, cleveref), in a scratch directory:

```sh
B=$(mktemp -d); cp -r article.tex sections references.bib "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 7 October 2026: 37
pages; no errors or warnings (LaTeX or BibTeX), no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes. The delivered text also builds without any (31
pages), and its `article.bbl` equals the one built here.

## From the delivery README

The delivery `README.txt` (replaced by this guide) gave the entry points and
the main result as above, with the machine model; summarized the
contributions and attribution ("No global priority certification is
claimed"; the complementation consequence "imports exactly the
order-reversing path-diagram image theorem stated in Section 5"; "No new Lean
formalization or independent human peer review is asserted. No uniform
logarithmic-space separation is claimed."); gave the build (`make`, or
pdflatex–bibtex–pdflatex–pdflatex; "The included article.bbl permits
compilation without rerunning BibTeX") and the audit command, with the
reference run on Python 3.12.14 in about 98 seconds and the coverage
(146,600 matchings, 365,908 compiler cases, 50,400 machine comparisons,
`D(h)` through `h = 256`); listed the files; and proposed this directory as
the ProveIt placement.

## Rights

Repository contents are MIT-0, except that this report's adapted exposition
comes with the upstream Apache License 2.0 (`LICENSE-APACHE-2.0.txt`) and the
attribution in `THIRD_PARTY_NOTICES.txt`. Short quotations of the cited works
are for attribution. No third-party PDF is shipped.

## Provenance

- Sources cited by the manuscript: the OpenAI manuscripts *An exponential
  two-way deterministic state lower bound for one-way liveness* and *An
  exponential state lower bound for two-way nondeterministic complementation*
  (25 September 2026, `openai/math` at `adc7f1241`) and its Lean summary
  `lean/docs/129.md`; TheoremDB R816; Sakoda–Sipser (1978), Pighizzini
  (2012), Brauer (1937), Auinger (2012), East–Gray (2017), Dolinka et al.
  (2015), Pin (1997), Sipser (1980), Lange–McKenzie–Tapp (2000), Yan (2008),
  Kapoutsis (2013), Adeogun–Kapoutsis (2026); three ProveIt automata READMEs.
- Non-Gowers intake NG3, manuscript 01; arrival `964621dd2` (7 October 2026),
  placement `bdcae034b` (delivered layout kept, archive retired), written
  7 October 2026. Single source, so no merge choices.
