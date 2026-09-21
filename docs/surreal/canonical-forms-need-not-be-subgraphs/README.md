# Canonical Forms Need Not Be Subgraphs

**Rigidity and sparsity of surreal option graphs:** two five-vertex
counterexamples, sharp graph minima, minimal-form enumeration, an exact
girth–size tradeoff, and planar high-girth forms.

A research article, two exact-arithmetic implementations, exhaustive small-form
verification, and reconstructible graph certificates.

Prepared 20 September 2026. The PDF contains 36 pages.

## Provenance

This archive merges two independently prepared research packages on the same
question, `canonical-forms-need-not-be-subgraphs` (the merge base) and
`sparse-option-graphs` (the donor). Both answered the question negatively at the
weakest reading, with a five-vertex form of value 1/2 whose option graph is a
pentagon against the canonical triangle, and both used the same conventions
(structurally distinct raw forms as vertices, the reduced Dali canonical map,
the dependency DAG with unique sink `{ | }`). The two witnesses are different
forms, not renamings, and both are kept. Beyond the shared pentagon the packages
diverge almost completely — one supplies the rigidity results, the other the
sparsity results — and where they proved the same statement by different routes,
both proofs are retained and labelled in the article.

## Main result

Matthew Roughan explicitly asked whether the canonical graph of a surreal value
is a subgraph of every other form of that value (2018, Figure 3 caption, p. 7).
Two sets of five structurally distinct forms give a negative answer.

The first, which is rank-minimal:

    O = { | }
    P = { O | }
    N = { | O }
    Z = { N | }
    F = { Z | P }          values 0, 1, -1, 0, 1/2;   rank 3

The second, which uses no negative value and has the empty form as a direct
option of the root:

    O  = { | }
    P  = { O | }
    Z' = { | P }
    P' = { Z' | }
    G  = { O | P' }        values 0, 1, 0, 1, 1/2;    rank 4

In both cases the graph of the root is a pentagon while the canonical graph of
1/2 is a triangle. The obstruction remains after directions, roots, values, and
option-side labels are forgotten. Exhaustive search shows there are exactly 16
five-vertex counterexamples; these two are entries 0 and 3 of that certified
list. Eight of the 16 are triangle-free and four of those have value 1/2, so no
uniqueness is claimed for either witness.

### On the rigid side

Five vertices and rank three are both smallest possible for a counterexample.
Canonical prefix values occur along a directed path in every finite
representation. The exact minimum vertex count, edge count, and cycle rank are
b+1, b+k, and k; there are exactly 2^(b(b-1)/2-k) vertex-minimal forms, all
containing the canonical graph as a value- and side-preserving spanning
subgraph; and the canonical form is the unique edge-minimizer. Here b is the
intrinsic birthday and 2^k the reduced denominator. Rank minimality alone does
*not* force containment: an explicit form of value 1/4 with rank equal to
b(1/4) fails it.

### On the sparse side

Every finite-birthday value admits forms of arbitrarily large girth, proved by
two independent constructions with two different non-collapse arguments: a
spaced-spine construction (exact vertex, edge, cycle-rank and rank formulas,
non-collapse by rank arithmetic) and a tree-and-spine construction (output
additionally **planar** with **maximum degree at most three**, non-collapse by
value parity and a template descent). For the single value 1/2 the tradeoff is
exact: the minimum number of vertices at girth at least g is 3 for g=3, 5 for
g=4, and g for every g>=5, and every cycle length 3 or >=5 is realized exactly
as a whole option graph (C_4 at no noninteger value).

### Classification and transfinite results

The values whose canonical graphs are unavoidable are exactly the integers, in
two senses with two independent proofs: the weakest unlabelled-undirected sense,
and a strictly stronger rooted, direction- and L/R-preserving sense. Two
disjoint results are proved at omega: a limit-stage obstruction showing that
individual prefix occurrence need not give coherent representatives, and a
triangle-free (indeed girth d+2) representation of omega with unchanged
birthday, together with the König-lemma fact that no transfinite form can have
finite outdegree everywhere.

“Finite value” means finite birthday (a dyadic rational), not merely bounded
absolute value. Vertices are structural forms, never equivalence classes of
all forms with equal numerical value, and never separately allocated copies of
one form. “Canonical” in the graph-minimum theorems means the reduced Dali
form, not the full sign-prefix cut.

## Files

- `surreal_graphs.pdf`: the article, with full proofs and three graph figures.
- `surreal_graphs.tex`: self-contained LaTeX source with embedded bibliography.
- `references.bib`: reusable bibliographic records; not required for compilation.
- `code/surreal_forms.py`: exact forms, canonical values, graph algorithms,
  exhaustive enumeration, prefix paths, the odd-cycle and spaced-spine families.
- `code/verify.py`: reproducible assertions and an independent cut evaluator.
- `code/sparse_forms.py`: the second implementation — `sparse_form()`, the full
  cycle spectrum, the recursive Conway comparison oracle, graph metrics,
  certificates, and its own small-form enumeration.
- `code/verify_sparse.py`: the tree-and-spine and cycle-family test suite, with
  the reusable `check_certificate()` routine.
- `results/summary.json` and `results/verification.txt`: core verification
  summary.
- `results/named_certificates.json`: the pentagon and minimum-rank quarter.
- `results/all_small_counterexamples.json`: all 16 counterexamples at size 5.
- `results/*.csv`: enumeration, minima, odd cycles, high-girth examples, and
  Fibonacci leaf-count checks.
- `results/sparse_results.json`, `results/sparse_verification.txt`: full
  numerical results and readable log of the tree-and-spine suite.
- `results/sparse_build_report.txt`: build and visual-inspection summary of the
  donor package, retained as a record.
- `examples/*.json`: eight complete form certificates — the C_3, C_5, C_6 and
  C_12 representations of 1/2, and the four tree-and-spine showcase outputs.
- `examples/*.dot`: matching Graphviz option graphs (rendering is optional).
- `SOURCES.md`: source locations, provenance, and the limits of the search.
- `Makefile`: compilation, checking, and removal of compilation intermediates.

No SHA manifest is shipped and none is needed; certificates are reconstructible
from their option sets alone.

## Reproduce the exact checks

Python 3.10 or newer is required. No external Python dependencies are used.
The bundled run used Python 3.13.5. Do **not** use Python's `-O` flag, which
disables assertions and therefore disables most of the suite.

From this directory:

```sh
python3 code/verify.py
python3 code/verify_sparse.py
```

or `make check`, which runs both. To preserve the bundled results and write a
separate run of the core suite:

```sh
python3 code/verify.py --bound 5 --output fresh_results
```

The complete enumeration by number of distinct subforms is:

| Vertices | Forms | Noninteger | Triangle-free noninteger | Of value 1/2 | Canonical-subgraph failures |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 0 | 0 | 0 |
| 2 | 2 | 0 | 0 | 0 | 0 |
| 3 | 10 | 2 | 0 | 0 | 0 |
| 4 | 123 | 32 | 0 | 0 | 0 |
| 5 | 3724 | 1200 | 8 | 4 | 16 |

Both statistics are real and neither implies the other. The 16 failures are the
broader test and include girth-3 forms of ±1/4 and ±3/4, whose canonical diamond
needs two triangles; filtering the 16 to noninteger values of girth at least 4
returns exactly the 8 triangle-free forms, of which 4 have value 1/2 and 4 have
value −1/2. The 3860 distinct forms were obtained from 4651 retained topological
labellings.

All 3860 forms passed prefix-path and graph-minimum assertions, and all 3860
cut values were checked by a second evaluator. The minimal-form counting formula
and unique edge-minimizer were checked in all 31 value classes of birthday at
most four. Additional core checks cover 20 odd-cycle forms, 126 spaced-spine
forms, and 4096 leaf-count instances spanning denominator exponents 0 through
12. The sparse suite checks 61 cycle certificates (length 3 and every length 5
through 64), 645 sparse constructions on the grid p/32 with -64<=p<=64 at
requested girths 3, 4, 5, 8 and 12, and four showcase examples — 710
certificates in all; the largest grid graph had 176 vertices and height 166.
Measured maximum leaf counts for denominator exponents 1 through 8 are
2, 3, 5, 8, 13, 21, 34, 55. All assertions passed.

These counts refer to structural forms, not vertex-labelled graphs, and not to
counts by birthday. The search allows any finite number of left and right
options within the vertex bound. It is not restricted to unary/binary forms.

To check an included certificate directly:

```sh
python3 -c "import json, sys; sys.path.insert(0, 'code'); \
 from verify_sparse import check_certificate; \
 check_certificate(json.load(open('examples/half_cycle_5.json'))); \
 print('Certificate passed')"
```

A small construction example:

```python
import sys; sys.path.insert(0, 'code')
from fractions import Fraction
from sparse_forms import sparse_form

arena, root, bounds = sparse_form(Fraction(5, 8), minimum_girth=5)
print(arena.metrics(root))
# {'value': '5/8', 'vertices': 30, 'edges': 33,
#  'height': 27, 'max_degree': 3, 'girth': 7}
arena.save(root, 'my_5_8_certificate.json')
```

In these outputs `height` is the form rank of the article, and `girth: null` in
JSON (Python `None`) denotes an acyclic graph with infinite girth. Values are
exact rational strings and node IDs are not numerical values.

The software is intended for exact small-instance research. Exhaustive search
scales quickly, girth is computed by breadth-first search from every vertex, and
very large canonical integers or deep recursive inputs can exceed Python's
ordinary recursion limit. The core verifier intentionally restricts its
exhaustive vertex bound to at most five. Graphviz is not a dependency of the
tests or of the PDF build; with it installed,
`dot -Tsvg examples/half_cycle_5.dot -o half_cycle_5.svg` renders one optional
standalone picture. Graph planarity is proved in the article; it is not
separately software-tested.

## Rebuild the PDF

A normal LaTeX installation with pdfLaTeX, AMS packages, newtx fonts, TikZ,
cleveref, hyperref, listings, microtype, and the usual supporting packages is
required. No font files are distributed in this archive.

```sh
latexmk -pdf -interaction=nonstopmode surreal_graphs.tex
latexmk -c
```

Alternatively, run `make -B all`, which uses three `pdflatex` passes. BibTeX is
not required: the bibliography is embedded in the `.tex` file. The separate
`.bib` file is provided for reuse.

## Status

This is an unrefereed AI-assisted research draft. It contains explicit proofs,
not a claim of independently certified priority. A targeted search found the
published question and relevant later work but did not find a resolution. Search
coverage and publisher access were limited, and that is not an exhaustive
novelty audit. Bibliographic metadata for the 2023 Mathematics Magazine version
of the source was located, but its full text was not retrievable; no claim is
made that the 2018 wording persists unchanged there or that the journal version
contains no answer. No Lean or other proof-assistant formalization was
performed.

The exact computations are supplementary finite checks, not substitutes for the
mathematical proofs. Within each implementation the evaluator and the
certificate reconstruction share one arithmetic kernel, so the genuinely
separate checks are the recursive Conway comparison, which uses no rational
values at all, and the breadth-first girth computation. The all-dyadic girth
theorems, planarity, the extremal lower bound, the classifications, and the two
omega results are proved mathematically, not inferred from a finite test set.

The PDF was compiled with a clean log — no unresolved references, no overfull or
underfull boxes, and no pdfTeX warnings. Third-party source PDFs are not
redistributed.
