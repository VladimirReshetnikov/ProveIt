# Friendly Order Types Through Incomparability Components

Research manuscript prepared for Vladimir Reshetnikov, 19 September 2026.

## Main files

- `friendly_order_types.pdf`: the complete mathematical article.
- `friendly_order_types.tex`: editable LaTeX source.
- `references.bib` and `friendly_order_types.bbl`: references and prebuilt bibliography.
- `code/friendly.py`: finite-poset implementation, exact residual-rank oracle,
  component formula, and optimal friendly-sequence construction.
- `code/verify.py`: reproducible exhaustive verification.
- `code/test_friendly.py`: unit tests.
- `results/verification.json`: actual exhaustive-run output.
- `results/unit_tests.txt`: actual unit-test output.
- `notes/literature-status.md`: source/version distinctions and scope of the status check.
- `notes/proof-audit.md`: dependencies, boundary cases, and verification limitations.
- `build.py`: cross-platform PDF build driver.

## Results

For a finite poset P, its friendly order type is |P| - c(P), where c(P) is the
number of components of the incomparability graph. This is also the edge count
of a spanning forest of that graph.

For a connected infinite wpo C, let T(C) consist of points with finite principal
upsets and let C° = C \ T(C). The tail is finite. Write o(C) = lambda + n, where
lambda = o(C°) is a nonzero limit and n = |T(C)|. The friendly rank is
lambda + (n - epsilon), where epsilon is 0 precisely when stripping the
friendless points of C° leaves its maximal order type unchanged; otherwise it
is 1. Ordinary ordinal-sum additivity extends this component calculation to
all wpos.

Consequences include an exact disjoint-sum law and equality f(A disjoint B) =
o(A) natural-sum o(B) for any two infinite summands, with no limit-type
hypothesis on their total maximal order types.

Two explicit counterexamples are given. One refutes the unrestricted identity
printed in Proposition 4.1(2) of the 2023 MFCS paper. The other proves that
the four input invariants (maximal order type, height, width, friendly order
type) do not determine the friendly order type of a disjoint sum—even when
the second summand is just one point.

## Verification

The included run checked **101,660 naturally labeled posets on 0 through 7
vertices**, comparing an independent memoized residual recurrence against the
graph formula. It also constructed and checked every optimal witness, tested
the maximal-cut-vertex lemma on connected inputs, and checked 25 rectangular
grids. There were no failures. Ten unit tests passed.

“Naturally labeled” is not the count of isomorphism classes and not the count
of all arbitrarily labeled posets. Every finite isomorphism class occurs,
sometimes in multiple natural labelings. The generator's construction is
explained in the article and its docstring.

The exhaustive run used Python 3.13.5. The code is written for Python 3.9+
and uses no third-party Python packages. From this directory:

```sh
python code/verify.py --max-n 7 --grid-max 6 --output results/verification.json
python -m unittest discover -s code -v
```

A quick sample:

```python
import sys
sys.path.insert(0, "code")
from friendly import FinitePoset

p = FinitePoset.chain(3).product(FinitePoset.chain(4))
assert p.graph_rank() == 9
assert p.exact_rank() == 9
witness = p.optimal_witness()
assert len(witness) == 9 and p.is_friendly(witness)
```

The rank oracle is exponential in general and is intended for small independent
checks. The graph formula takes quadratic time on a dense transitive relation;
a witness can be constructed in cubic time.

## Building the PDF

Install a normal LaTeX distribution containing `newpxtext` and `newpxmath`.
No font binaries are distributed in this archive. Run:

```sh
python build.py
```

The driver uses `pdflatex`, then `bibtex` (or `bibtex8` / `bibtexu`), then two
additional LaTeX passes. It can also use the included `.bbl` file when BibTeX
is unavailable. Alternatively:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error friendly_order_types.tex
```

## Status and boundaries

These are research arguments with detailed proofs, not an independently
refereed publication or a proof-assistant formalization. The general infinite
classification uses a precisely identified published limit-floor bound.
The finite theorem and the two explicit counterexamples do not depend on that
bound. Finite tests do not establish transfinite ranks. Novelty and priority
have not been independently established.

The article does not claim a decision procedure for arbitrary presentations
of infinite wpos, and does not claim to have settled every construction in
the broader compositional-computation program.
