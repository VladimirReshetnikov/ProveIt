# Jacobsthal Products All at Once

## A Cantor-block construction and a finite-tail reduction

Research manuscript dated 20 September 2026. Prepared with ChatGPT in response
to a request to select and attempt an open problem in order theory or ordinal
combinatorics.

## Selected problem and status

The target is Question 2.16 of Harry Altman's *Intermediate arithmetic operations
on ordinal numbers* (Mathematical Logic Quarterly 63 (2017), 228–242): find an
all-at-once order-theoretic model of finite and infinitary Jacobsthal products,
rather than defining the higher arities by parenthesized multiplication or a
limit. The associativity identity and the binary Cantor-normal-form formula
are classical, not new claims of this manuscript.

The article proposes a constructive affirmative answer in a specific sense:
a CNF-based comparison rule on actual tuples or finite-support functions,
invariant under order isomorphisms and extending the componentwise order.
Its definition does not evaluate a Jacobsthal product. It is accompanied by
proofs, a restricted maximality characterization, and executable checks.

This is an unrefereed research attempt. No independent peer review, proof-assistant
verification, or exhaustive novelty certification is claimed. Targeted searches
located the published question and related work but no later resolution. The
construction is not claimed to be preserved by arbitrary order embeddings.
Coordinate flattening is generally not the associativity isomorphism.

## Main results

For finite factors, a tuple has a pivot: its last coordinate after the first
which lies in a positive-exponent Cantor block, or its first coordinate if there
is no such later coordinate. Its pivot, block, and later finite-tail entries
specify a cell. Ordinary colex is used inside each cell. Cells are ordered by
decreasing pivot, then decreasing input block exponent, with deterministic
finite tie rules. No prefix ordinal arithmetic is needed to compare tuples.
The resulting order has the Jacobsthal product as its type. Comparing the cell
types proves compatibility with finite regrouping without assuming Jacobsthal
associativity.

For every nonzero ordinal-indexed sequence, ordinary partial products O_xi and
Jacobsthal partial products J_xi have identical CNF exponent supports and
identical leading monomials, with coefficient domination and

    O_xi <= J_xi < O_xi * 2.

At a limit with cofinally many factors greater than 1, the two products agree
and are a pure power of omega. Delete unit factors and write the order type of
the active index as lambda+n, where lambda is zero or a limit and n is finite.
The whole Jacobsthal product is the ordinary finite-support product on the
lambda-prefix, followed by one finite pivot product on the n remaining factors.
This yields a direct finite-support model at arbitrary ordinal arities.

A three-state automaton decides equality with the ordinary product from that
finite active suffix. The finite tuple model also gives an order-theoretic
proof of the binary inequality J(a,b) <= a tensor b, using Carruth's theorem.
This addresses only the binary multiplication portion of Altman's Question 5.2.

## Files

- `article.tex`, `article.pdf`: manuscript with detailed proofs, examples,
  scope qualifications, bibliography, and computational methodology.
- `code/ordinals.py`: exact hereditary CNF arithmetic below epsilon_0,
  the binary formula, the all-arity cell formula, equality automaton,
  and two equivalent tuple-comparison rules.
- `code/verify.py`: reproducible verification driver.
- `results/verification_results.json`: machine-readable executed test results.
- `results/verification_report.txt`: readable version of those results.
- `notes/proof_audit.md`: dependency map, delicate points, and verification scope.
- `notes/source_search.md`: primary-source references and search limitations.
- `Makefile`: build and verification commands.

No third-party article PDFs, font files, or LaTeX build intermediates are included.

## Run the checks

Requires Python 3.10 or later and only its standard library.

```sh
python3 code/verify.py
```

The supplied run passed 729 binary pairs, 17,576 exhaustive triples, 3,500
additional lists with nested ordinal exponents, 86,216 split checks, and
56,769 tuple-pair checks. The primitive and cell-degree comparators agreed on
all 56,769 tested pairs. Of those pairs, 12,107 were componentwise comparable;
4,000 additional tuple-triple checks tested transitivity. Zero and empty-list
cases were also checked. The random seed is 20260920. Runtime is recorded but
will vary across machines.

These checks are finite tests below epsilon_0, not proofs over all ordinals.
No arbitrary transfinite limit is evaluated in Python. The symbolic limit
examples substitute values justified by the manuscript's proofs. The direct
and binary arithmetic paths share the same low-level CNF implementation.

## Rebuild the PDF

Requires `latexmk`, `pdflatex`, and the common LaTeX packages listed in the
source. The bibliography is internal; no BibTeX or Biber run is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, use `make check`, `make pdf`, or `make all`. `make clean`
removes generated LaTeX intermediates and Python caches, not the PDF.
