# Ordinal complexity of graph minors

**Component splitting, degree-two graphs, and discontinuous limits**  
Research manuscript prepared for Vladimir Reshetnikov, 20 September 2026.

## Read the manuscript

`graph_minor_ordinals.pdf` is the compiled 21-page article. Its complete source is
`graph_minor_ordinals.tex`; the bibliography is included in that source.

The selected research direction is the ordinal measurement of graph-minor
orders, identified in Isa Vialard's 2024 thesis. This archive gives a partial
attack on that broader program, with exact calculations for a concrete family.
It does **not** calculate the maximal order type of the minor order on all
finite graphs. Historical novelty of the special-case formulas has not been
established; the manuscript does not claim priority or resolution of a named
conjecture.

All graphs in the article are finite, simple, undirected, and considered up to
isomorphism. The empty graph is included. The order is ordinary graph-minor
containment, not induced-subgraph containment or a relation requiring one
source component per target component.

## Main calculations

Let D be all graphs of maximum degree at most two. For maximal order type o,
ordinal antichain-tree width w, and descending-tree height h, the article proves

    o(D) = w(D) = omega^(omega * 2),       h(D) = omega.

Here `*` is ordinary ordinal multiplication. Ordinal width is a tree rank, not
the cardinality of an antichain.

More generally, D_(b,k) allows path components with at most b vertices and at
most k cycle components. An absent bound is denoted infinity; cycle lengths
remain unrestricted in every row.

| Path-size bound | Cycle-count bound | Maximal order type | Ordinal width |
| --- | --- | --- | --- |
| finite b >= 1 | finite k >= 0 | omega^(b+k) | omega^(b+k-1) |
| unrestricted | finite k >= 0 | omega^(omega+k) | omega^(omega+k) |
| finite b >= 1 | unrestricted | omega^omega | omega^omega |
| unrestricted | unrestricted | omega^(omega*2) | omega^(omega*2) |

Height is omega throughout. Finite-b classes with cycles need not be
minor-closed; their order is inherited from the ambient minor relation.

A general connected-component theorem is also proved. If C is a well-partial-
order of connected graphs with maximal order type alpha < epsilon_0, then its
finite disjoint-union closure has maximal order type omega^alpha. The proof
combines established finite-multiset machinery with an explicit argument
showing why splitting connected components does not destroy the lower bound.

The formulas yield a failure of continuity even for increasing unions of
minor-closed classes: if K_m bounds every component size by m, then

    sup_m o(K_m) = omega^omega < o(union_m K_m) = omega^(omega*2).

## Archive contents

- `graph_minor_ordinals.pdf` — compiled article, including detailed proofs,
  examples, computational methodology, bibliography, and proof audit.
- `graph_minor_ordinals.tex` — editable LaTeX source.
- `build.py` — PDF rebuild helper.
- `code/verify_degree_two.py` — dependency-free exhaustive finite checker.
- `results/verification.json` — actual machine-readable verification report.
- `results/counts.csv` — enumeration counts by vertex number.
- `notes/proof_audit.md` — critical proof checks and scope boundaries.
- `notes/source_review.md` — source review and research-status notes.

## Reproduce the finite checks

Use Python 3.9 or later, with assertions enabled (do not use `python -O`).
No third-party Python packages are needed. From this directory:

```console
python code/verify_degree_two.py --max-vertices 14 --out results
```

The saved run used Python 3.13.5 and passed all 2,250,000 ordered-pair comparisons
on all 1,500 isomorphism classes with at most fourteen vertices. It found
378,324 minor pairs, including equality, and checked strict ordinal-code decrease
on 376,824 proper minor pairs. It also checked the equal-cycle-count product
identity on 732,568 pairs and individual finite height ranks on all 1,500 graphs.

The checker compares closure under elementary minor operations with exact
cycle reservation and path bin packing. A third version uses the proved greedy
cycle reservation rule; its path packing is still exact, not greedy. The two
packing versions share that path-packing subroutine. Counts are independently
checked against a generating function. Nine targeted regression tests are
included.

The recorded runtime was approximately 10.1 seconds in the original execution
environment. This is not a portable performance claim. Rerunning overwrites the
report and CSV and will change recorded environment/runtime information; update
checksums afterward when maintaining a modified archive.

These are finite implementation and lemma checks. They do not verify the
transfinite order-type proofs, which are written mathematical arguments rather
than a Lean/Coq/Isabelle formalization.

## Rebuild the PDF

Install a TeX distribution containing `pdflatex` and the packages in the source
preamble, including `newpxtext`, `newpxmath`, `tcolorbox`, and `cleveref`. The
supplied PDF can be read without installing TeX. To rebuild:

```console
python build.py
```

Alternatively:

```console
latexmk -pdf -interaction=nonstopmode -halt-on-error graph_minor_ordinals.tex
```

The PDF was compiled successfully and visually inspected. No font files or
third-party full-text papers are distributed in this archive.

## Mathematical status

The article provides proofs of its stated restricted-family formulas, conditional
only on the explicitly cited established theorems about well-partial-orders.
The proofs have been checked in the course of this analysis, but have not been
externally refereed or formally certified. Novelty and bibliographic completeness
are separate questions from the internal proof arguments. See the two notes for
precise dependency and source-review boundaries.
