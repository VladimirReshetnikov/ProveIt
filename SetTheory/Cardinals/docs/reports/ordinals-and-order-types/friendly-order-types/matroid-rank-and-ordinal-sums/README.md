# Friendly order type through incomparability components

A research article, proofs, and a reproducible computational audit.
Prepared 19 September 2026.

## Main result

For every finite poset P,

    friendly_order_type(P) = |P| - number_of_incomparability_components(P).

Isolated vertices count as components. The empty poset has both counts zero.
The same number is the graphic-matroid rank and the incidence-matrix rank of
the incomparability graph. Combined with Isa Vialard's published multiset-width
theorem, it gives width(M^r(P)) = omega^(|P|-c(P)). M^r denotes the
Dershowitz–Manna multiset ordering, NOT injective multiset embedding.

The article also proves a substitution formula, a finite Cartesian-product
formula, and additivity over arbitrary well-ordered ordinal sums. It evaluates
all well-partial-orders whose incomparability components are finite. Explicit
countable counterexamples delimit stronger infinite extrapolations.

## Status and scope

The selected problem is a concrete finite structural subproblem of Vialard's
published open-ended program to understand friendly order type. It is not
represented as a separately named conjecture, or as the full infinite problem.
All claimed new mathematical statements have proofs in the article. Those
proofs have not been externally refereed or formally checked. Priority is
unverified: the targeted literature search did not find the component formula,
but that is not a proof that it was previously unknown.

The general theorem converting friendly order type to multiset-order width is
Vialard's result and is cited as an external dependency. See RESEARCH_STATUS.md.

## Read and build

- `article.pdf` is the compiled 19-page article.
- `article.tex` is complete LaTeX source with an embedded bibliography.
- `build.sh` rebuilds the PDF using a normal TeX Live installation.

Run:

```sh
sh build.sh
```

The build requires pdflatex and standard TeX packages including newtx,
amsthm, mathtools, microtype, tcolorbox, booktabs, listings, titlesec,
hyperref, and bookmark. No external images, bibliography processor, shell
escape, network access, or font-file downloads are needed. The script places
intermediates in `.build/`.

## Reproduce the computations

Python 3.10 or later; only the standard library is required.

```sh
python3 code/audit.py --max-n 7 --output data
```

This overwrites the three machine-readable output files in `data/` with the
new run's counts and timings. To retain the provided outputs use another
output directory, for example `--output my_audit`.

The reported run used Python 3.13.5. It checked:

- All 101,660 naturally labelled poset relations on 0 through 7 elements:
  independent residual rank, graph component formula, incidence rank over F_2,
  and validity of every step in a constructed optimal witness.
- 351 seeded relabelling cases.
- All 164,836 ordered pairs of naturally labelled factors of sizes 2 through 5:
  direct product-graph component checks; 241 products of size at most 9 also
  received independent exact-rank checks.
- All 7,211 substitutions with naturally labelled index size at most 3 and
  nonempty naturally labelled fibers of sizes 1 through 3: independent exact
  residual rank and graph formula checks.

Every reported check passed. The full run took approximately 31 seconds in
the original environment; this is not a portable performance benchmark.

“Naturally labelled” means x <_P y implies x < y as integer labels. These
are not isomorphism classes and not all arbitrary labellings. Every finite
poset is isomorphic to a naturally labelled one, so this suffices to cover
all isomorphism types through the stated size.

An optional slower audit is:

```sh
python3 code/audit.py --max-n 8 --output data_n8
```

No exhaustive eight-element run is claimed in this package.

## Library example

From the `code/` directory:

```python
from friendly_order import chain, cartesian

p = cartesian(chain(2), chain(3))
assert p.friendly_formula() == 3
assert p.exact_friendly_rank() == 3
witness = p.optimal_witness()
p.verify_witness(witness)
print(witness)
```

A `Poset` stores reflexive principal upsets as integer bit masks. Construction
validates reflexivity, antisymmetry, transitivity, and the mask range. Labels
need not be natural for the rank or witness routines. The exact-rank algorithm
is exponential and is intended as an independent reference check, not the
production value algorithm.

## Files

`code/friendly_order.py` — data representation, exact rank, graph formula,
incidence rank, witness construction, ordinal/disjoint sums, substitution,
Cartesian products, and exhaustive generator.

`code/audit.py` — full verification driver.

`data/audit_results.json` — actual counts, timings, and pass status.

`data/audit_console.txt` — captured console output from the provided run.

`data/rank_distributions.csv` — rank distributions by finite size.

`data/examples.json` — small examples with explicit legal-sequence and forest
certificates. “Omitted roots” are omitted from the selected sequence, not
necessarily retained in the final residual.

No downloaded third-party papers are redistributed. Primary-source citations
and links appear in the article and RESEARCH_STATUS.md.
