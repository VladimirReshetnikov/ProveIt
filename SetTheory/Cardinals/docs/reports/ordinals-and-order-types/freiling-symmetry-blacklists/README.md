# From Finite Blacklists to Freiling Symmetry

**Exact avoidance thresholds, critical tournaments, choice-sensitive
colourings, and perfect safe sets: the finite theory of blacklist systems
(each point refuses at most `k` others), its infinite partition over ZF, and
its definable forms beside Freiling's axiom of symmetry**

A research report dated 5 October 2026, built from one manuscript. It is an
**AI-assisted, unrefereed external manuscript**: its status box says so, and
its author line and PDF author field read "Research report prepared for
Vladimir Reshetnikov". It contains no e-mail address, no "prepared for
private review" line and no personal data.

| Source | Batch | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 114 (non-bundle arrival) | `From_Finite_Blacklists_to_Freiling_Symmetry.zip` (468,852 bytes, SHA-256 `57c2af7c…02832`; wrapper directory of the same name, 6 files, 514,199 bytes unpacked), arrival commit `2399df2bd` ("New research reports", 5 October 2026); main file `From_Finite_Blacklists_to_Freiling_Symmetry.tex` (1,291 lines, 19-page PDF) | `a763feee1` (`a763feee1f3703dc710d9b810b1de66168f1e266`, bibliography entry `ProveIt` of the article; it is the batch-98A write commit of this repository) | `99053b5d1` (batch 114) | the whole report |

**Status:** unrefereed, not formalized: no Lean or Rocq declaration exists
for any statement of this report, and its place in the collection confers no
formal status. The finite statements for `k = 1` were checked exhaustively
for `n ≤ 7` by the delivered program; everything else rests on the written
proofs.

## Trust boundaries

- **Classical, credited.** The partition of an arbitrary (infinite) system
  into `2k + 1` safe sets is Theorem 3 of de Bruijn and Erdős, *Proc. KNAW
  Ser. A* 54 = *Indag. Math.* 13 (1951), 371–373, which the write read in
  full: their paper adopts the Axiom of Choice "throughout", proves the
  finite case by the same edge-count and low-degree-vertex induction as the
  source's Corollary 3.3, and gets the infinite case from colouring
  compactness (their Theorem 1). Their Theorem 4 is the countable-colour
  theorem of the source's Question 12.3.
- **Quoted, not proved.** Turán's theorem with its equality case
  (Theorem 5.1); propositional compactness from the Boolean prime ideal
  theorem (Theorem 8.1); the Kuratowski–Ulam and Mycielski theorems
  (Theorem 9.1, "classical tools, derived here"); Tonelli (Theorem 9.3).
- **Proved in the text.** Everything else, read in full at intake and again
  at the write; no error found. The write made one step of the proof of
  Theorem 6.3 explicit (why a minimizer may have all components unicyclic).
- **The computation proves nothing beyond its cases.** `code/verification.py`
  checks `k = 1`, `n ≤ 7` by enumeration, counts the 40 critical systems at
  `(k,r,n) = (1,3,6)` by enumeration and `R_3, R_5` by brute force, but
  obtains 72,576 at `(2,3,10)` only by evaluating formula (6) — no
  two-bounded system is enumerated.
- **No priority.** The source makes "no historical-priority claim for the
  finite refinements without a more exhaustive literature review"; the
  write did no such review either. A safe set is de Bruijn–Erdős's
  "independent set" and the set-mapping literature's "free set"; that
  literature (Hajnal's free set theorem and its relatives) was surveyed by
  neither.

## What it proves

A *k-bounded blacklist system* is `F : X → [X]^{≤k}` with `x ∉ F(x)`; a set
is *safe* if no two members blacklist each other, i.e. independent in the
conflict graph `G_F`; `A_r(n,k)` is the least number of safe `r`-sets over
systems on `n` points; `q = 2k + 1`. Statement numbers are those of the
committed PDF (theorem counter per section; no delivered number moved).

- **Lemma 3.1, Theorem 3.2, Corollaries 3.3–3.4**: edge budget
  `e_F(S) ≤ k|S|`; list colouring from lists of size `2|F(x)| + 1`; a
  partition into `2k + 1` safe sets; a weighted safe set.
- **Theorem 4.1, Corollary 4.2**: `min α(G_F) = ⌈n/(2k+1)⌉` for every `n`;
  a safe `r`-set is forced exactly when `n > (r − 1)(2k + 1)`.
- **Theorem 5.1, Corollary 5.2**: at `n = (r − 1)q` every system without a
  safe `r`-set has conflict graph `(r − 1)K_q` with each block a regular
  tournament; the number of such labelled systems is
  `(tq)!/((q!)^t t!) · R_q^t` (40 and 72,576 in the examples).
- **Theorems 6.1–6.3**: `A_2(n,k) = max{0, C(n,2) − kn}`; the two-term
  asymptotic `A_r(n,k) = C(n,r) − kn·C(n−2,r−2) + O(n^{r−2})`; the exact
  `A_3(n,1) = C(n,3) − n(n−2) + c_n` with `c_n = 2a, 2a+2, 2a+3`.
- **Proposition 7.1**: linear-time peeling.
- **Theorem 8.1** (de Bruijn–Erdős under `BPI`), **Theorem 8.3** (over ZF,
  `BPI ⇒ SAP_k ⇒ C_2 ∧ … ∧ C_{k+1}`), **Theorem 8.4** (`SAP_k` holds in ZF on
  well-orderable sets; Lemma A.1, compactness for well-orderable languages).
- **Theorem 9.1, Corollary 9.2**: a Borel relation with countable vertical
  sections on a perfect Polish space has a perfect safe set (a definable
  strengthening of Freiling's conclusion); **Theorem 9.3**: almost every
  i.i.d. sample from an atomless measure is a countably infinite safe set.
- Section 10: the phase diagram; Section 11: the computation; Section 12:
  research program (Conjectures 12.5, 12.6; Questions 12.1–12.4, 12.7–12.15);
  Section 13: a Lean plan M1–M7 (a proposal); Section 14: claim ledger.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Proposition 12.16 (`fbl:prop:small`)**: Conjecture 12.5 (pseudoforest
  minimizer `H_n`) holds for `3 ≤ n ≤ 9`, because the coefficients of
  `z^0 … z^3` are proved and `I_{H_n}` has degree at most 3 there;
  Conjecture 12.6 holds for `n ∈ {q, 2q}`, and for all `n` in the
  coefficients `r ≤ 2` and `r > n/q`.
- **Proposition 12.17 (`fbl:prop:three`)**: over ZF, `SAP_k ⇒ C_3` for every
  `k ≥ 1`; new for `k = 1`, where it gives `SAP_1 ⇒ C_2 ∧ C_3` (two
  3-cycles on each triple, and a symmetric rule from their two selections).
- **Proposition 12.18 (`fbl:prop:finite`)**: over ZF,
  `BPI ⇒ SAP⁺_fin ⇒ SAP_fin ⇒ C_fin` and `SAP⁺_fin ⇒ SAP_k`, where
  `SAP_fin` is de Bruijn–Erdős's countable-colour theorem and `SAP⁺_fin`
  adds `c(x) ≤ 2|F(x)|`.
- An exact computation (not shipped): Conjecture 12.5 holds for every
  `n ≤ 18`, so `A_r(n,1) = [z^r] I_{H_n}` there.
- Notes: status and trust boundary; Section 1.4 (provenance, sources as
  read, intake checks, repository relation, collected non-claims, reading
  conventions and notation table); de Bruijn–Erdős and Freiling/Sierpiński
  as read; credit after Corollary 3.4; the step in Theorem 6.3; the scope of
  the third certificate of Section 7; what the program computes; names in
  Appendix B; Section 12.6.

## What is not claimed

From the source, kept in the article (collected in Section 1.4):

- The infinite `(2k+1)`-partition is de Bruijn and Erdős's (1951), "not …
  this report"; their paper assumes the Axiom of Choice.
- "No exhaustive priority search has been made for the finite refinements";
  the ledger's "no priority claim after an exhaustive search" means that no
  priority is claimed (Section 1.4 reads it so).
- No endorsement, collaboration or authorship by Elliot Glazer; the
  motivation rests on his public work.
- The computation "is verification, not proof"; the perfect-set theorem is
  "classical tools, derived here"; the regularity theorems give no partition
  into finitely many definable safe sets; the conjectures are "supported
  only by the proved coefficients and small exhaustive checks"; the exact
  choice strength of `SAP_k` is open; the research program and the Lean plan
  are proposals.
- Freiling's axiom and its equivalence with ¬CH are not proved here. The
  source proves only that under CH a well-ordering of ℝ in type `ω_1` gives
  countable blacklists with no safe pair (remark after Corollary 9.2).

## Further questions

Section 12.6 ("Further questions and research", `fbl:sec:further`) states
every unproved claim as an open question with its source, sketch and what is
missing (Vladimir's standing rule of 4 October 2026). **Nothing in the source
was found to be wrong.** Its 17 items are the two conjectures, the thirteen
questions, and two further items (certificates; formalization and OEIS).
Re-scoped:

1. **Conjecture 12.5** (`fbl:fq:pseudoforest`): proved for `n ≤ 9`
   (Proposition 12.16); confirmed for `n ≤ 18` by the write's exact
   computation (coefficientwise-minimal pruning over all-unicyclic graphs,
   cross-checked without pruning for `n ≤ 11` and against brute force for
   `n ≤ 7`). First open coefficient: `z^4` at `n = 10`, where
   `[z^4] I_{H_10} = 18`.
2. **Conjecture 12.6** (`fbl:fq:critical-block`): proved for `n ∈ {q, 2q}`;
   for `k = 1` it is part of item 1. Open from `k = 2`, `n = 15`, coefficient
   `z^3` (125 for `3K_5`).
3. **Strength of `SAP_1`** (`fbl:fq:sap1`): `SAP_1 ⇒ C_2 ∧ C_3`; so it is
   equivalent to choice for pairs only if `C_2 ⇒ C_3` over ZF. The
   independent check (below) supplied the answer, confirmed in Jech, *The
   Axiom of Choice* (1973), Theorem 7.16, p. 111 (Mostowski's condition (S)
   fails for `m = 2`, `n = 3`): `C_2` does not imply `C_3` over ZF, so
   `SAP_1` is strictly stronger than choice for pairs. Its exact strength
   remains open.
4. **Hierarchy** (`fbl:fq:hierarchy`): the source's sentence that `BPI` is
   "substantially stronger" than the finite-choice principles has no proof or
   reference (not checked); Läuchli's paper, in the bibliography but uncited,
   is related (abstract seen only in a search excerpt).
5. **Countable-colour theorem** (`fbl:fq:countable`): de Bruijn–Erdős
   Theorem 4; over ZF between `BPI` and `C_fin` (Proposition 12.18).
6. **Exact `A_r(n,k)`** (`fbl:fq:exact`): known for `r = 2`, `(3,1)`, the
   zero range, and all `r` for `k = 1`, `n ≤ 18` (computation).
7. Stability; 8. enumeration (the "one expects" sentence is a heuristic);
   9. **linear-time certificates** (`fbl:fq:certificate`; the third
   certificate of Section 7 is proved only for critical systems and `A_2`
   minimizers); 10. Borel partition number; 11. measurable positive safe
   sets; 12. regularity strength in ZF; 13. cardinal blacklists; 14. random
   systems (the "substantially larger safe sets" sentence is a heuristic;
   the worst case is `⌈n/(2k+1)⌉`, printed `n/(2k+1)`); 15. hypergraph
   avoidance; 16. games; 17. formalization and sequences (proposals).

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`bf70d7db4`) found no item needing a
correction. It reread the proofs of Propositions 12.16–12.18 and the note
completing Theorem 6.3's minimizer step, and confirmed that Proposition 12.17
is new exactly for `k = 1`. With its own program, by a different method from
the write's (trees plus tree-plus-one-edge as connected pseudoforests,
bitmask independence polynomials, coefficientwise minima over all
partitions; not shipped), it found the coefficientwise minimum over all
`n`-vertex pseudoforests to be exactly `I_{H_n}` for `3 ≤ n ≤ 15`; brute
force over all `n^n` one-bounded systems (`n ≤ 6`) and all `11^5`
two-bounded systems on five points agreed, as did `A_2(n,1)`, `A_3(n,1)`,
the table, `[z^4] I_{H_10} = 18` and `[z^3] I_{3K_5} = 125`. It checked the
de Bruijn–Erdős account and pagination against the scan (the variant
369–373 for *Indag. Math.* found by a web search remains unresolved). Its
one lead — `C_2 ⇏ C_3` over ZF — was confirmed in Jech's Theorem 7.16 when
the check was recorded and now answers item 3. The record is a dated note at
the end of Section 12.6.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement (batch-114 dossier): `code/verification.py` in 15 s, output
  equal to `data/verification_output.txt` up to blank lines and line
  endings; independent checks of the `A_2(n,1)`, `A_3(n,1)` tables for
  `n ≤ 12` from the closed forms, the counts 40 and 72,576, `R_5 = 24` by
  brute force, and `I(C_4) = 1 + 4z + 2z^2`, `I(C_5) = 1 + 5z + 5z^2`.
  The dossier read every proof (block construction, Turán count, arc
  saturation, the `i_3` formula, component costs, partition optimization,
  clique-fibre choice, Lindenbaum recursion): no error.
- At the write: the verifier on a fresh copy in about 6 s, output identical
  up to line endings; both shipped delivered files byte-identical to the
  archive. A brute-force run of its enumeration printing the full minimum
  vectors for `n ≤ 7`, and the write's own computation for
  Conjecture 12.5 (`n ≤ 18`; not shipped).
- The distinct-conflict-graph counts 1, 2, 8, 57, 608, 8524, 145800 are
  OEIS A133686 (labelled graphs with at most one cycle per component), and
  `R_1, R_3, R_5 = 1, 2, 24` are A007079 (labelled regular tournaments),
  identified by the write.
- Sources read by the write: de Bruijn–Erdős (in full, scan of the reprint
  in the TU/e repository; the bibliography's "Indag. Math. 13 (1951),
  369–373" is not supported by the reprint, which gives 371–373 for both
  series); Freiling, J. Symbolic Logic 51(1) (1986) 190–200 (data, abstract
  and reference list only: the abstract credits "an old theorem of
  Sierpiński" and the reference list cites Sierpiński's *Hypothèse du
  continu*, 2nd ed., 1956, not read); Crossref data of Läuchli (1971) and
  Mycielski (1964). Not read: Glazer, Cowen, Howard–Rubin, Kechris, Turán,
  Jech (apart from Theorem 7.16 and the notes to Chapter 7, read when the
  independent check was recorded), Bollobás, Erdős (1950), Hajnal (1961).

## Relation to the repository

**Formal status.** No statement of this report is formalized. At the
write's base commit no Lean or Rocq file mentions blacklists, free sets of set
mappings, Freiling's axiom, `SAP_k` or the Boolean prime ideal theorem; the M1–M7 plan
is a proposal.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `ordinals-and-order-types/bounded-width-power-set-compression` (same
  batch; **see also**): another exact finite extremal theory with a
  choiceless infinite form over ZF (an infinite set with a bounded-width
  compression of its power set is Dedekind-infinite), which also asks for the
  weakest standard choice principle that suffices. No shared theorem;
  neither cites the other.
- `ordinals-and-order-types/measurable-box-games`: cited by the source as
  background only ("substantial work on measurable box games and infinite
  hat guessing" — correct at the pin and at the write's base commit: five
  Parts, unchanged between the two). Shares the Glazer motivation, no
  theorem.
- Same batch and category, no shared theorem: `noisy-parity-cubes`,
  `robust-neutral-choice`, `random-bits-arithmetic-cuts`.

**Stale claims.** None: the source's one repository statement is correct.

## Notation

A table at the end of Section 1.4 fixes the letters the source reuses, with
the tempting false readings: `F` (blacklist) against the families `𝒜_e`,
`𝒜`; `A_r(n,k)` against a safe set `A` and a member of `𝒜`; `C_m` (choice for
`m`-sets, sans-serif) against `C = R ∪ R⁻¹` and cycles `C_s`; `q = 2k + 1`
against the cost `Q(H)`; `t = r − 1` against the triangle count `t(G)`; the
relation `R` against `R_q`; `H_n` against a component `H`; `s`, `a`, `m`, `c`
and `c_n`. "Safe" is de Bruijn–Erdős's "independent". No symbol was renamed.

## Labels

Every label carries the prefix `fbl:` (none existed in the repository). The
manuscript's 36 labels were prefixed before anything cited them, and all 34
references were updated (`\pageref*{LastPage}` is the `lastpage` package's
and untouched). The write added 45: eight delivered headings
(`fbl:sec:freiling`, `fbl:sec:dbe-credit`, `fbl:sec:critical`,
`fbl:sec:algorithms`, `fbl:sec:definable`, `fbl:sec:computation`,
`fbl:sec:formal`, `fbl:sec:ledger`), `fbl:cor:freiling`,
`fbl:conj:critical-block`, the thirteen questions `fbl:q:sap1` …
`fbl:q:game`, the new `fbl:sec:provenance` and `fbl:sec:further`, the 17
items `fbl:fq:…`, and `fbl:prop:small`, `fbl:prop:three`,
`fbl:prop:finite`. The report has 81 labels; builds of the delivered text
and of this one give all 36 delivered labels the same numbers (aux files
compared). The three propositions are the last numbered statements of
Section 12, so no theorem or equation number moved.

## Files

```text
README.md                        this guide (replaces the delivery README.txt)
article.tex                      the report (delivered From_Finite_Blacklists_to_Freiling_Symmetry.tex; labels prefixed, [write] additions)
article.pdf                      compiled report, 28 pages
code/verification.py             exhaustive checks for k = 1, n <= 7, and the two critical examples (standard library)
data/verification_output.txt     the program's recorded output
```

`code/verification.py` and `data/verification_output.txt` are byte-identical
to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit (next section): the
delivered 19-page PDF (457,358 bytes), `SHA256SUMS.txt` (four entries, all
verified at placement) and the delivery `README.txt` (1,223 bytes), staged
at placement and replaced by this guide (summarized under "From the delivery
README").

**Delivered text that names the delivery layout.** Appendix B of the article
lists `article.tex`, `article.pdf`, `verification.py` and `README.txt` as
"the archive", and says the checks are described in Section 12; in the
delivery the source and PDF had the long name, and the checks are in
Section 11. A dated note under Appendix B says so.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 2399df2bd:docs/incoming/From_Finite_Blacklists_to_Freiling_Symmetry.zip > "$T/fbl.zip"
sha256sum "$T/fbl.zip"   # 57c2af7cf12c13b48b39b4240d323751e09efe05e1f647290602524695c02832, 468,852 bytes
cd "$T" && unzip -q fbl.zip     # creates From_Finite_Blacklists_to_Freiling_Symmetry/
```

## Rerun the checks

Python 3.10 or later (it uses `int.bit_count`), standard library only. The
program writes no file, so it may be run in place; a copy is shown for
uniformity with the collection:

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/freiling-symmetry-blacklists
T=$(mktemp -d); cp "$R/code/verification.py" "$T/"; cd "$T"
python3 -I -B verification.py > out.txt     # a few seconds; ends "All checks passed."
diff <(tr -d '\r' < out.txt) "$R/data/verification_output.txt" && echo same
```

Tested at the write (Windows, `py` for `python3`): about 6 s, identical up
to carriage returns. The delivery README warns that the `n = 7` step "may
take several seconds to a few minutes, depending on the machine".

## Build the PDF

pdfLaTeX (geometry, fontenc, inputenc, lmodern, microtype, amsmath, amssymb,
amsthm, mathtools, booktabs, longtable, tabularx, array, enumitem, xcolor,
graphicx, tikz, fancyhdr, lastpage, hyperref, cleveref); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026, and
rebuilt after the independent check: 28 pages (unchanged); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull boxes,
and 15 underfull-box messages, all in delivered lines (the phase-diagram
table, the ledger and two bibliography entries), which a build of the
delivered text shows identically (19 pages).

## From the delivery README

The delivery `README.txt` (replaced by this guide) listed the `.tex`, the
19-page US Letter PDF, `verification.py` ("Independent exhaustive checks
for all one-blacklist systems through n=7, plus the two critical
labelled-enumeration examples reported in the paper" — the second example
is a formula evaluation, see Trust boundaries), its captured output and
`SHA256SUMS.txt`; gave two `pdflatex` passes and `python3 verification.py`;
and stated: "AI-assisted and unrefereed. Classical results are credited in
the article; no historical-priority claim is made for the finite refinements
without a more exhaustive literature review."

## Rights

Repository contents are MIT-0. The package contains no OEIS or other
third-party data; the A-numbers above were identified by the write (OEIS
data are CC BY-SA 4.0). Nothing was submitted anywhere. The de Bruijn–Erdős
scan was read online and is not shipped.

## Provenance

- Sources cited by the manuscript: Glazer (dissertation 2023,
  arXiv:2211.10474, arXiv:2311.13699; motivation), Freiling (JSL 1986),
  de Bruijn–Erdős (1951), Turán (1941), Cowen (1990, 1998), Läuchli (1971),
  Howard–Rubin (1998), Jech (1973), Mycielski (1964), Kechris (1995),
  Bollobás (1998), ProveIt at `a763feee1` and `measurable-box-games`. Added
  by the write: Erdős (1950), Sierpiński (1956), Hajnal (1961), the OEIS.
- Repository input: `measurable-box-games` at the pin, unchanged at the
  write's base commit `9ccf04eae`.
- Batch 114 of `docs/incoming` (non-bundle arrivals); arrival `2399df2bd`,
  placement `99053b5d1`, written 5 October 2026. Single source, so no merge
  choices. The delivered `.tex` is shipped as `article.tex`; the delivered
  program and output as listed above.
