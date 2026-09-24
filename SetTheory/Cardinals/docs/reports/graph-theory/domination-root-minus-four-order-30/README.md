# A bicyclic 30-vertex graph with domination root -4

The explicit graph in `data/graph30.json` is connected and planar, has
30 vertices, 31 edges, treewidth 2, domination number 10, and

    D(G,x) = x^10 (x+4) Q_19(x),    Q_19(-4) = -38318272.

This gives a negative answer to the explicit question whether 33 is the
minimum order in Alikhani and Griswold, arXiv:2608.00109v1, Section 4,
question 2. Their earlier 33-vertex example already disproved the
original integer-root conjecture. This artifact does NOT claim the first
counterexample to that older conjecture or that 30 is globally minimal.

## Read

- `domination_root_30.pdf`: complete research note with proofs and a labeled graph.
- `domination_root_30.tex`: self-contained LaTeX source, including its TikZ drawing.

## Verify (Python 3.10+, standard library only)

From this directory:

    python3 code/verify.py

Three exact polynomial computations must agree:
1. A denominator-free four-cycle/gadget identity.
2. Pendant-tree elimination followed by 32 subsets of the five-vertex 2-core.
3. An independent enumeration of 32,768 subsets of the original non-leaves.

The two general enumeration algorithms are tested against direct vertex-subset
brute force on all 1,100 labeled simple graphs with 0 through 5 vertices, plus
120 seeded larger examples. Five connected-family identities are also tested.
The verifier also checks the exact factorization, derivative, rooted states,
and rational cancellation. It raises an error on any discrepancy.

`results/verification.json` and `results/verification.txt` contain a completed run.
The verifier regenerates the coefficient and leaf-certificate CSV files.

## Reproduce the discovery

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

## Build the PDF

    pdflatex -interaction=nonstopmode -halt-on-error domination_root_30.tex
    pdflatex -interaction=nonstopmode -halt-on-error domination_root_30.tex

A standard TeX Live installation with newtx, TikZ, and tcolorbox is sufficient.
No custom font files or external figures are distributed.

## Files

- `code/domination.py`: exact polynomial and graph routines, with documented states.
- `code/verify.py`: independent certificate checks and exhaustive small-graph tests.
- `code/search.py`: portable, uncached reconstruction of the successful search.
- `data/graph30.json`: canonical graph and coefficients in ascending degree order.
- `data/edges.txt`: all 31 edges, one unordered pair per line.
- `data/coefficients.csv`: coefficients of degrees 0 through 30.
- `data/leaf_certificate.csv`: the 118 triples (a,b,m) for sum m*x^a*(1+x)^b.
- `data/graph30.dot`: Graphviz representation of the same graph.
- `results/verification.json`, `results/verification.txt`: completed exact checks.
- `results/search.json`, `results/search.txt`: completed deterministic search.

## Status

Prepared with ChatGPT on 18 September 2026. The note is not peer reviewed or
Lean-formalized. The finite graph and proofs can be independently checked
without trusting the search. Literature searching cannot guarantee publication
priority. The true minimum order and existence of roots -6 or -8 are not
settled in this artifact.

The supporting-edge family construction is an elementary product mechanism,
not claimed as a newly discovered general principle. Its applications to the
explicit seed give connected planar families and arbitrary multiplicity at -4.
