# Friendly order type and incomparability components

Research report dated 19 September 2026.

## Main result and scope

For a finite poset P, the report proves

    f(P) = |P| - number_of_connected_components(Inc(P)).

Isolated vertices count as components; the empty graph has zero components.
Here f is Vialard's friendly order type (rank of open-ended bad sequences).
Combining the result with Vialard's existing width-transfer theorem gives

    ordinal_width(M_DM(P)) = omega ^ f(P).

M_DM is the multiset ordering, not injective multiset embedding.

The article also classifies all maximum friendly subsets, constructs
spanning-forest certificates, proves finite Cartesian-product and
lexicographic-substitution formulas, derives an enumerative generating
function, and treats well-ordered sums of finite posets.

This is a finite-case answer to a broader published research question, not
an asserted solution of that question for arbitrary infinite wpos. The
proofs have not been independently refereed or formalized. The literature
search did not locate the main component formula, but priority is not
certified.

## Files

- `article.pdf`: the full article.
- `article.tex`, `sources.bib`, `build.sh`: editable LaTeX and bibliography.
- `src/friendly.py`: finite-poset engine, graph formula, independent residual
  dynamic program, optimal sequence constructor, and certificate verifier.
- `src/verify.py`: reproducible exhaustive and composition tests.
- `src/check_distribution.py`: check the generating-function convolution
  against the saved rank distribution.
- `data/verification.json`, `data/verification.txt`: the executed test report.
- `data/rank_distribution.csv`: exact counts by support size and friendly rank.
- `examples/*.json`: concrete posets, given by strict generating relations.
- `proof_audit.md`: assumptions, proof dependencies, and limitations.

Only Python's standard library is used. Python 3.10 or newer is required.
No downloaded literature PDFs or font files are distributed.

## Calculate a finite example

From this directory:

```sh
python src/friendly.py examples/diamond.json --dp
python src/friendly.py examples/chain_plus_isolate.json --dp
python src/friendly.py examples/N_poset.json --dp
python src/friendly.py examples/empty.json --dp
```

The two four-element examples `diamond.json` and `chain_plus_isolate.json`
have the same cardinality, height, and ordinary width, but friendly ranks
1 and 3. Their multiset ordinal widths are omega and omega^3.

Input format:

```json
{"n":4,"relations":[[0,1],[0,2],[1,3],[2,3]]}
```

Labels are integers 0 through n-1. Relations are *strict generating*
relations (Hasse edges are acceptable); the program takes transitive closure.
Cycles and out-of-range labels are rejected. Labels need not be a linear
extension. With no `relations`, the input is an antichain.

Optional `"roots":[...]` requests specific roots: provide exactly one root
per incomparability component, each minimal within its own component.
For example, the diamond accepts `"roots":[0,2,3]` and returns a sequence
using only vertex 1. A root of a later component can be removed when an
earlier component is processed; it remains a root of the certificate forest,
not necessarily an element of the final residual.

`--dp` requests the independent exponential reference computation. Avoid it
for large posets: the formula itself is quadratic on a comparison matrix,
but the reference recursion may visit up to 2^n subsets.

## Reproduce the checks

```sh
python src/verify.py --max-n 7
python src/check_distribution.py
```

The delivered run passed:

- 101,660 naturally labelled posets through seven elements, with independent
  residual ranks, dual ranks, and optimal certificates;
- 90,655 connected-case maximal non-cut checks;
- 2,601 Cartesian-product pairs (factor sizes at most four, supports at most 16);
- 10,725 heterogeneous lexicographic substitutions;
- 2,365 candidate maximum friendly subsets through size five, including
  1,052 prescribed-root certificates;
- eight invalid inputs or malformed friend claims, all rejected.

These are naturally labelled orders, not unlabelled posets and not all
labelled orders. Every finite isomorphism type through the bound is
represented, potentially many times. Exhaustive tests do not replace the
proof for unbounded sizes or verify any transfinite theorem.

The script overwrites reports in `data/`. Use `--out OTHER_DIRECTORY` to
keep the delivered results unchanged. A quick smoke test is
`python src/verify.py --max-n 4 --out /tmp/friendly-check`; the composition
and maximum-subset checks still run over their documented fixed ranges.

## Compile the article

```sh
./build.sh
```

The script uses `pdflatex` plus an available `bibtex`, `bibtex8`, or `bibtexu`.
A reasonably complete TeX Live installation supplies the required packages:
newpx fonts, amsmath/amsthm, mathtools, microtype, geometry, booktabs,
longtable, enumitem, xcolor, tcolorbox, fancyhdr, titlesec, needspace,
aliascnt, listings, hyperref, and cleveref.

The PDF was rendered and visually checked. No formal proof assistant was
used, and the archive does not contain Lean code or a claim of machine-
checked mathematical correctness.
