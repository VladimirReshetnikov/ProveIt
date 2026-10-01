# A bicyclic 30-vertex graph with domination root -4

**Part II: cycle budgets for integer domination roots**

This is a research report in two parts on integer roots of the domination
polynomial `D(G,x)`, built from two manuscripts. Part I (18 September 2026)
constructs a connected planar 30-vertex graph with the simple domination root
-4, which answers negatively the question whether 33 vertices are needed.
Part II (30 September 2026) studies the alternating evaluation `D(G,-1)`. It
proves that `|D(G,-1)|` is at most `3^β`, with β the cycle rank. It
determines the exact values for β ≤ 2 and β ≤ 3. It shows that Part I's
search method can produce no integer root below -2 other than a simple -4.
Both parts were prepared with ChatGPT; Part II's title page adds "for
Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 18 Sep 2026 (*A bicyclic 30-vertex graph with domination root -4: A counterexample to the proposed 33-vertex minimum*) | `domination_root_30_research.zip` | (none) | unpacked in `a3fe9660e` of the Cardinals history, in ProveIt since `dc54c3cb3` | Part I: Sections 1–8 (pp. 3–13) and Appendix A (p. 30) |
| 02 | batch 67, manuscript 04 (*Cycle Budgets for Integer Domination Roots: A sharp alternating-sum bound, exact low-cycle spectra, and a structural obstruction to a repository search method*, 30 Sep 2026, 19-page A4 PDF and 1,229-line `article.tex` as delivered) | `ProveIt_Domination_Cycle_Obstructions.zip` (inner `ProveIt_Domination_Cycle_Obstructions/`), arrived in `ffddaa8b9` | `0744012ba` | `d281a285a` (prefix `02-cycle-budgets-`) | Part II: Sections 9–22 (pp. 14–30) and Appendices B–C (pp. 31–32) |

The pin `0744012ba` is ProveIt commit
`0744012ba29db0e345c44be953c6de3e000439e6`, an ancestor of the placement.
Part II's manuscript read Part I's `README.md`, `domination_root_30.tex` and
`code/search.py` at that commit (`02-cycle-budgets-SOURCE_AUDIT.md`). No
commit touched this directory between the pin and the placement, so
everything the manuscript says about "the repository report" refers to Part I
as printed here. Its archive arrived in `ffddaa8b9` and was retired in the
placement commit. Its manuscript, PDF and delivery README are not shipped and
survive only in `ffddaa8b9`.

**Status:** AI-assisted, unrefereed, and not formalized. Neither part has
been peer reviewed or checked in a proof assistant. Part II's three-cycle
classification is computer-assisted. Neither part makes a publication-priority
claim.

## Files

```
domination_root_30.tex                              the report, standalone LaTeX with an internal bibliography
domination_root_30.pdf                              the compiled report, 32 pages (title, abstract and contents pp. 1–2,
                                                    Part I pp. 3–13, Part II pp. 14–30, appendices pp. 30–32,
                                                    references p. 32)
README.md                                           this guide
code/domination.py                                  Part I: exact polynomial and graph routines, with documented states
code/verify.py                                      Part I: independent certificate checks and exhaustive small-graph tests
code/search.py                                      Part I: portable, uncached reconstruction of the successful search
data/graph30.json                                   Part I: canonical graph and coefficients in ascending degree order
data/edges.txt                                      Part I: all 31 edges, one unordered pair per line
data/coefficients.csv                               Part I: coefficients of degrees 0 through 30
data/leaf_certificate.csv                           Part I: the 118 triples (a,b,m) for sum m*x^a*(1+x)^b
data/graph30.dot                                    Part I: Graphviz representation of the same graph
results/verification.json, results/verification.txt Part I: completed exact checks
results/search.json, results/search.txt             Part I: completed deterministic search
02-cycle-budgets-SOURCE_AUDIT.md                    Part II: source, dependency and claim audit, as delivered
code/02-cycle-budgets-verify.py                     Part II: exact certificates and implementation checks (standard library)
code/02-cycle-budgets-check_repo_example.py         Part II: D(G30,-1), the graph X_5, and the extremizers for β = 1..6
code/02-cycle-budgets-Makefile                      Part II: the delivered Makefile (must not be run here; see below)
data/02-cycle-budgets-kernel_certificate.json       Part II: the 18 kernel records (3 for β = 2, 15 for β = 3)
data/02-cycle-budgets-spectrum_witnesses.json       Part II: connected witnesses for the ten values of A_3
data/02-cycle-budgets-kernel_table.tex              Part II: standalone extract of Table 3 (not input by the report)
data/02-cycle-budgets-witness_table.tex             Part II: standalone extract of Table 4 (not input by the report)
data/02-cycle-budgets-verification.json             Part II: recorded run of the verifier
data/02-cycle-budgets-verification.txt              Part II: byte-identical copy of the previous file, as delivered
data/02-cycle-budgets-example_checks.json           Part II: recorded run of the example check
data/02-cycle-budgets-example_checks.txt            Part II: byte-identical copy of the previous file, as delivered
```

Every Part I file is as it arrived in the Cardinals collection, except
`domination_root_30.tex`, `domination_root_30.pdf` and this README. Every
`02-cycle-budgets-` file is byte-identical to the batch-67 delivery. The
delivery names map to the shipped paths as follows:

| Delivered as | Shipped as |
|---|---|
| `article.tex`, `article.pdf`, `README.md` | not shipped (Part II of `domination_root_30.tex`, its PDF and this README replace them) |
| `SHA256SUMS.txt` | not shipped (all 15 entries verified at placement; repository policy retires checksum ledgers) |
| `SOURCE_AUDIT.md` | `02-cycle-budgets-SOURCE_AUDIT.md` |
| `Makefile` | `code/02-cycle-budgets-Makefile` |
| `code/verify.py` | `code/02-cycle-budgets-verify.py` |
| `code/check_repo_example.py` | `code/02-cycle-budgets-check_repo_example.py` |
| `data/kernel_certificate.json` | `data/02-cycle-budgets-kernel_certificate.json` |
| `data/spectrum_witnesses.json` | `data/02-cycle-budgets-spectrum_witnesses.json` |
| `data/kernel_table.tex` | `data/02-cycle-budgets-kernel_table.tex` |
| `data/witness_table.tex` | `data/02-cycle-budgets-witness_table.tex` |
| `results/verification.json`, `results/verification.txt` | `data/02-cycle-budgets-verification.json`, `data/02-cycle-budgets-verification.txt` |
| `results/example_checks.json`, `results/example_checks.txt` | `data/02-cycle-budgets-example_checks.json`, `data/02-cycle-budgets-example_checks.txt` |

The two `.txt` records are byte-identical to their `.json` twins (same
bytes, JSON text despite the extension). Neither program writes a `.txt`
file; they were staged as delivered.

## Labels and numbering

Part I's 40 labels are bare (`thm:root`, `eq:edges`, `prop:cycle`, …) and
unchanged. Every label of Part II carries the prefix `cb:`: the manuscript's
42 labels and 21 added in the write (14 section labels `cb:sec:*`, the two
appendix labels `cb:app:kernel` and `cb:app:audit`, and the five questions
`cb:q:minus6`, `cb:q:bicyclic`, `cb:q:mult`, `cb:q:spectra`,
`cb:q:equality`): 103 labels in all. The `.aux` numbers of all 40 Part I
labels were compared with a build of the committed text and are unchanged;
in particular Part I's equation (2.1), which Part II's audit and
`check_repo_example.py` cite, is still (2.1).

The manuscript's Section *n* is Section *n* + 8 here, and its Theorem, Lemma,
Corollary, Question and equation *n.m* are (*n* + 8).*m* (for example its
Theorem 11.1, the search obstruction, is Theorem 19.1; its Corollary 8.2,
no root -6 at β ≤ 2, is Corollary 16.2). Its Tables 1 and 2 are Tables 3
and 4. Its Appendices A and B are Appendices B and C. Subsections 9.1
(provenance, with the manuscript's abstract and result box) and 9.2 (notation
conventions) were added before its Section 1.1, which is Section 9.3 here,
retitled "The question from Part I"; they contain no numbered statement or
equation. The `\part*` headings are unnumbered and change no number of
Part I.

The write added, besides the contents, the part headings and a title-page
line ("Part II … added in batch 67"), text marked
`[Added 30 September 2026, batch 67]`:

- in Part I, a paragraph in the abstract and notes after Section 1 (the
  root -6), after equation (2.2) (cycle rank in Part II), after equation
  (5.3) (a second route to simplicity), after Theorem 6.4 (cycle cost of
  multiplicity), in Section 7.2 (what escapes the tested class), at the end
  of Section 8 (the search equation, answered negatively), and at the end of
  Appendix A;
- in Part II, notes after Theorem 14.2 (relation to Certificate B), in
  Section 20.2 (shipped names) and at the end of Section 21.6 (formal
  status);
- dated sentences in the bibliography entries [1] and [2].

Sections 9.1 and 9.2 are new as a whole. In the manuscript's own text the
write changed only references and names: "the repository", "the repository
report", "this article" and the citation `\cite{Repo}` became references to
Part I or Part II (Sections 9.3, 9.4, 19, 20.2, 20.3, 21.3, 22 and
Appendix C); Section 20.1 and the caption of Table 4 gained the shipped file
names beside the delivered ones; Sections 9.3, 19 and 22 were retitled ("The
question from Part I", "Why Part I's four-cycle search cannot find another
root", "Conclusion of Part II"); and Appendix C's "Sections 3–8 and 11" and
"Section 9" are cross-references to Sections 11–16, 19 and 17. No statement
of either source was changed.

## Notation

Part II keeps the manuscript's notation, except for three renamings forced
by Part I. Section 9.2 has a table of every letter that means different
things in the two parts, with the tempting false reading beside the true
one. The renamings:

- The manuscript's path transfer matrices `F_1, …, F_4`, `F_ℓ` are printed
  `M_1, …, M_4`, `M_ℓ` (also in the pseudocode of Appendix B), because
  Part I's `F_1, F_2, F_3` are the rooted gadgets of Proposition 4.1.
- The manuscript's eight-vertex graph `H_5` with `D(H_5,-1) = 5` is printed
  `X_5`, because Part I's `H_5` is Theorem 6.4's graph `H_k` at `k = 5`
  (150 vertices). The delivered `02-cycle-budgets-check_repo_example.py` and
  its record `02-cycle-budgets-example_checks.json` still call it `H5`.
- The manuscript's sharpness chain `G_b` is printed `G^ch_b`, because
  Part I's `G_t` (Theorem 6.2) is a different family.

The manuscript's abstract writes multiplicities `m_j` (and `m` is also its
edge count); they are written `r_j` here, as in its own theorems. Its macro
`\N` (blackboard N, unused) is dropped and Part I's `\N` kept; its `\pin` is
spelled out. Its bibliography entries `AG` and `Oboudi` are the same works as
Part I's and are merged with them (its annotations kept as dated sentences);
its entry `Repo` (the repository report) became references to Part I; its
entries `Intro`, `AlikhaniMinusOne` and `Kotek` were added. No normalization
changed. Other shared letters (`W`, `T`, `E`, `H`, `K`, `J`, `c`, `r`, `s`,
`t`, `𝒫`) keep their manuscript meanings inside Part II and are listed in the
table. Part II's cycle rank `β(G) = |E| − |V| + c(G)` equals Part I's
cyclomatic number `|E| − |V| + 1` on connected graphs.

## What the report claims

### Part I (Sections 1–8, Appendix A)

The explicit graph in `data/graph30.json` is connected and planar, has
30 vertices, 31 edges, treewidth 2, domination number 10, and

    D(G,x) = x^10 (x+4) Q_19(x),    Q_19(-4) = -38318272.

This gives a negative answer to the explicit question whether 33 is the
minimum order in Alikhani and Griswold, arXiv:2608.00109v1, Section 4,
question 2. Their earlier 33-vertex example already disproved the
original integer-root conjecture. This artifact does NOT claim the first
counterexample to that older conjecture or that 30 is globally minimal.
Part I also gives connected planar examples at order 30 and every order at
least 32, connected examples with multiplicity exactly `k` at -4 for every
`k` (Theorem 6.4), and, with Oboudi's theorem, minimum cycle rank 2 for a
root -4 (equation (2.2)).

### Part II (Sections 9–22, Appendices B–C)

With `β(G) = |E| − |V| + c(G)`:

- **Theorem 12.1 (sharp budget).** `1 ≤ |D(G,-1)| ≤ 3^β` for every finite
  simple graph, with equality at the upper end for connected planar subcubic
  graphs of every positive cycle rank. The proof rests on Theorem 11.1: for a
  forest with arbitrary pins and waived domination requirements, the
  alternating count lies in {-1, 0, 1} (thirteen signed rooted states).
  Lemma 10.1: `D(G,-1)` is odd (classical, attributed to Brouwer; reproved).
- **Theorem 13.1 (simultaneous root budget).** If the distinct roots `-k_j`,
  `k_j ≥ 2`, have multiplicities `r_j`, then `Π (k_j − 1)^{r_j}` divides
  `D(G,-1)` and is at most `3^β`. So a root -4 of multiplicity `r` needs
  `β ≥ r`.
- Tree-decoration deletion (Theorem 14.2), sign reversal by a pendant path
  (Corollary 14.3), and four-subdivision invariance of `D(G,-1)` (Theorem
  15.1, with 3×3 transfer matrices of period four).
- **Theorem 16.1 (two-cycle spectrum, conventional proof).** The values of
  `|D(G,-1)|` for `β ≤ 0, 1, 2` are exactly {1}, {1,3}, {1,3,7,9}.
  **Corollary 16.2:** for `β ≤ 2` every nonzero rational root is in
  {-2, -4, -8, -10}, so `D(G,-6) ≠ 0`.
- **Theorem 17.1 (three-cycle spectrum, computer-assisted).** For `β ≤ 3`
  the values are exactly {1,3,5,7,9,11,15,17,21,27}, from fifteen kernels and
  26,688 residue assignments (Table 3). Corollary 17.2: roots -14, -20, -24,
  -26, and a double root -6, need `β ≥ 4`. The eight-vertex graph `X_5` has
  `D(X_5,-1) = 5` and `D(X_5,-6) = 407160`, so the divisibility obstruction
  alone cannot exclude -6 at `β = 3`.
- **Corollary 18.1.** The least cycle rank `μ(a)` with `|D(G,-1)| = a`
  (connected `G`): `μ(5) = 3`, `μ(7) = μ(9) = 2`, `μ(3^b) = b`, and
  `μ(a) ≥ 4` for `a = 13, 19, 23, 25` (Table 4).
- **Theorem 19.1 (search obstruction).** Every graph built by Part I's
  zero-C four-cycle architecture at a target `-k`, `k ≥ 3` — any number of
  attached trees with `C_T(-k) = 0`, a hub with at least one leaf, the fourth
  corner may be decorated — has `|D(G,-1)| = 3`; so `D(G,-k) = 0` forces
  `k = 4`, and that root is simple. Section 19.2: `D(G30,-1) = -3` (three
  of nine case vectors contribute -1), a second proof that Part I's root -4
  is simple.
- Five research questions (Questions 21.1–21.5) and a proposed formalization
  plan (Section 21.6).

## What the report does not claim

- No graph with root -6 or -8 is constructed by either part, and whether
  one exists is open. Part II excludes -6 only for `β ≤ 2`.
- The minimum order of a graph with root -4 is not settled; 30 is an upper
  bound. Part I's search was restricted, not exhaustive.
- The divisibility conditions are necessary, never sufficient (Part II's
  remark after Theorem 13.1). The sharp `3^β` bound does not make
  `-(3^β+1)` a root of an extremal graph.
- Part II does not re-prove the lower bound of Part I's equation (2.2): it
  still rests on Oboudi's Theorem 7.
- The three-cycle table is computer-assisted: its finite part is an exact
  enumeration by the delivered program, not checked in a proof assistant.
  Seeded tests are supplementary.
- Neither part claims publication priority. Part II does not claim that its
  lemmas or the `3^β` inequality are absent from the literature on
  evaluations at -1 (Alikhani 2013) and splitting formulas (Kotek et al.
  2012).
- Neither part is peer reviewed or Lean/Rocq-formalized.

## Relation to other work in ProveIt

- **Answered question.** Part I's closing question (Section 8: the search
  equation `c + r(a+b) = z^3 + 4z^2 + 6z + 3` for other integer targets `z`)
  is answered negatively by Part II's Theorem 19.1. A dated note in Section 8
  records this. Part I's remark in Section 7.2 that a decorated fourth corner
  or larger forests "can escape the tested class" stays true for the order
  of a root -4 but, by the same theorem, not for any other root.
- **Neighbouring reports.**
  [`trapezohedral-minimal-dominating-sets`](../trapezohedral-minimal-dominating-sets)
  counts minimal dominating sets (A381190), not roots of the domination
  polynomial; no result is shared. No other report of the collection
  evaluates `D(G,-1)`.
- **Formal status.** No Lean or Rocq development in ProveIt defines dominating
  sets or the domination polynomial (a search of all tracked `.lean` and `.v`
  files on 30 September 2026 found none), so no statement of either part has
  been formalized. Placement in this repository confers no formal status.

## Read

- `domination_root_30.pdf`: the complete report with proofs, the labelled
  30-vertex graph, and Part II's tables and figures.
- `domination_root_30.tex`: self-contained LaTeX source, including its TikZ
  drawings.

## Build the PDF

    latexmk -pdf -interaction=nonstopmode -halt-on-error domination_root_30.tex

Build in a scratch copy and keep only the PDF; auxiliary files are not
committed. The source now has a table of contents, so a bare `pdflatex`
needs three runs. A standard TeX installation with newtx, TikZ, tcolorbox,
longtable and xurl is sufficient. No custom font files or external figures
are distributed. The committed PDF was built with MiKTeX (pdfTeX): 32 A4
pages, every font embedded, no Type 3 font, and no warning.

## Verify Part I (Python 3.10+, standard library only)

From this directory:

    python3 code/verify.py

On Windows use `py` for `python3`. Three exact polynomial computations must
agree:
1. A denominator-free four-cycle/gadget identity.
2. Pendant-tree elimination followed by 32 subsets of the five-vertex 2-core.
3. An independent enumeration of 32,768 subsets of the original non-leaves.

The two general enumeration algorithms are tested against direct vertex-subset
brute force on all 1,100 labeled simple graphs with 0 through 5 vertices, plus
120 seeded larger examples. Five connected-family identities are also tested.
The verifier also checks the exact factorization, derivative, rooted states,
and rational cancellation. It raises an error on any discrepancy.

`results/verification.json` and `results/verification.txt` contain a completed run.
The verifier regenerates the coefficient and leaf-certificate CSV files, and
it rewrites `results/verification.json` in place.

### Reproduce the discovery

    python3 code/search.py

This reconstructs the rooted-tree catalogue (orders <= 14) from scratch,
constructs minimum-cost forest ratios (total order <= 14 at each site), and
solves the exact equation

    c = -21 - r_m (a+b),    r_m = 4^(m-1) / (4^(m-1) - 3^m).

It tests m=5 first and then the other integers from 1 to 15, with an initial
strict order bound of 33. The included run returned the 30-vertex example,
with 6,118 forest ratios and 2,547,880 exact rational lookups in about 6.2 seconds.
Timings depend on the machine. This is a restricted construction search,
NOT an exhaustive search through all graphs with at most 29 vertices.

Options are available through `python3 code/search.py --help`.
The search output graph can have a different edge-record order from the
canonical data file; its vertex labels, edge set, and polynomial agree here.

## Rerun Part II (on a copy only)

**Do not run Part II's programs in this directory.** Both write into the
directory above their own: in place, `02-cycle-budgets-verify.py` would
overwrite Part I's `results/verification.json` and add unprefixed
`data/kernel_certificate.json` and `data/spectrum_witnesses.json`, and
`02-cycle-budgets-check_repo_example.py` would add
`results/example_checks.json`. The example check also does
`from verify import …`, which the prefixed file name cannot satisfy. The
delivered `code/02-cycle-budgets-Makefile` targets `article.tex` and
`python3 code/verify.py`, which here are a missing file and Part I's
verifier; do not run it.

Run them on a copy under their delivered names (Python 3.10+, standard
library only):

    T=$(mktemp -d)
    mkdir -p "$T/code"
    cp code/02-cycle-budgets-verify.py "$T/code/verify.py"
    cp code/02-cycle-budgets-check_repo_example.py "$T/code/check_repo_example.py"
    (cd "$T" && python3 code/verify.py && python3 code/check_repo_example.py)

The copy then holds `results/verification.json`,
`data/kernel_certificate.json`, `data/spectrum_witnesses.json` and
`results/example_checks.json`, to compare with the shipped
`data/02-cycle-budgets-*` records. (`verify.py --output-dir DIR` writes its
three files under `DIR` instead; the example check has no such option.)
On this machine (Python 3.14.4, Windows, 30 September 2026) both passed in
about 3 seconds. The regenerated files equal the shipped records except
that, on Windows, Python writes CRLF line endings, and
`verification.json`'s `elapsed_seconds` differs (recorded 1.7). The run also
creates `code/__pycache__/` in the copy.

What the recorded runs contain: `02-cycle-budgets-verification.json` records
13 signed forest states, path lengths 1–12, the 1,100 labeled graphs through
order 5 with 366 integer-root instances, 300 seeded constrained forests and
120 seeded graphs (seed 20260930), kernel counts 3 (β = 2) and 15 (β = 3),
26,832 residue assignments in all (26,688 at β = 3), 78 small expanded-kernel
brute-force checks, and the cumulative spectra for β ≤ 3.
`02-cycle-budgets-example_checks.json` records `D(G30,-1) = -3` with case
counts {-1: 3, 0: 6, 1: 0}, the graph `X_5` (key `H5`) with its coefficients
and `D(-6) = 407160`, and the extremizers for β = 1..6 with values
`(-1)^{β-1} 3^β`.

## Discrepancies and delivery names

- `02-cycle-budgets-SOURCE_AUDIT.md`, both programs and the Makefile use
  delivery names (`article.tex`, `code/verify.py`, `results/…`,
  `data/kernel_certificate.json`, `SHA256SUMS.txt`); the table above maps
  them. Part II's own text (Section 20.2) prints the delivered commands
  verbatim, followed by a dated note with the shipped names.
- `02-cycle-budgets-kernel_table.tex` and `02-cycle-budgets-witness_table.tex`
  are the manuscript's standalone extracts of its two tables. The report does
  not input them, and they carry the unprefixed labels `tab:kernels` and
  `tab:witnesses` (Part II prints the tables itself, labelled
  `cb:tab:kernels` and `cb:tab:witnesses`). The witness-table caption names
  `data/spectrum_witnesses.json`.
- In `02-cycle-budgets-spectrum_witnesses.json` the witness for value 7 has
  `kernel_index: 1`, an index into the three β = 2 kernels, not row 1 of
  Table 3. The other witnesses with a `kernel_index` (5, 11, 15, 17) refer to
  Table 3.
- The `.txt` records are JSON duplicates (see Files).
- The delivered README calls its PDF "the complete article"; it is not
  shipped, and `domination_root_30.pdf` replaces it.

## Status

Part I was prepared with ChatGPT on 18 September 2026; Part II with ChatGPT
"for Vladimir Reshetnikov" on 30 September 2026. Neither part is peer
reviewed or Lean-formalized. Part I's finite graph and proofs can be
independently checked without trusting the search. Part II's sharp bound,
root budget, pruning and transfer identities, two-cycle classification and
search obstruction have conventional proofs; its three-cycle classification
is computer-assisted. Literature searching cannot guarantee publication
priority. The true minimum order for a root -4 and the existence of roots -6
or -8 are not settled in this report.

Part I's supporting-edge family construction is an elementary product
mechanism, not claimed as a newly discovered general principle. Its
applications to the explicit seed give connected planar families and
arbitrary multiplicity at -4.
