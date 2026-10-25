# Shared arithmetic certificates and graph energies for Con(ZFC)

Prepared for Vladimir Reshetnikov's ProveIt research program, 24 October 2026.

The article is **report/main.pdf**; its complete editable LaTeX source is
**report/main.tex** with the adjacent included sections. All final equations
are ordinary polynomials with fixed integer coefficients. The archive contains
their literal coefficient lists or arithmetic circuits, source identities,
ordinary mathematical proofs, independent exact checkers, and recorded reviews.

## Results

| Construction | Domain | Variables | Exact total degree | Other exact metrics |
|---|---|---:|---:|---|
| Principal graph polynomial | all integers | **2,215** | **4** | **30,468 monomials; every coefficient ±1; constant 1** |
| Matched graph comparison, individual degree ≤2 | all integers | 2,988 | 4 | 31,218 monomials; coefficient height 1 |
| Matched graph comparison, square aliases | all integers | 2,776 | 4 | 30,554 monomials; coefficient height 1 |
| Oriented common Pell cap | all integers | **381** | **4** | 225 residuals; 13,179 monomials; height 2,445,790,974,704 |
| Lower-height oriented-cap companion | all integers | 391 | 4 | 235 residuals; 10,764 monomials; height 80,496,640 |
| Shared cap and modular binomial digits | nonnegative integers | **240** | **4** | 188 residuals; 25,987 monomials; height 90,589,484 |
| Denser natural companion | nonnegative integers | 239 | 4 | 187 residuals; 360,097 monomials; height 491,869,488 |
| Linear strong multiplier, centered | all integers | **11** | **412** | **127** live binary arithmetic operations |
| Linear strong multiplier, direct | all integers | 11 | 440 | 126 live binary arithmetic operations |

The graph and direct-cap branches use the numerical C222 proof calculus,
without simulating K215 or specializing Jones's universal polynomial. The
eleven-variable branch retains its separate native/source34/K215 calibration
and its complete six-numeral coefficient tuple. Those numerals are fixed
coefficients, not additional unknowns.

For each equation the ordinary proof, composed with its explicitly retained
calibration, establishes in ZFC:

> The equation has no solution in its stated domain if and only if Con(ZFC).

This does not prove either side of the equivalence. The release makes no
claim of a global simplicity minimum, worldwide historical priority, or a
new complete Lean/Rocq/object-language ZFC verification. The elementary graph
compiler itself proves an exact bijection of integer zero sets, independent
of any consistency assumption or number-theoretic source calibration.

## The new ideas

1. **A common graph for many residuals.** Half the sum of squared vertex
   divergences in a simple graph has unit integral coefficients. Free tree
   flows enforce the required row balances, with one shared hub block for
   all equations.
2. **Factor sharing with a proved collision rule.** Common representatives
   replace many separate factor copies. A bipartite factor graph with no
   four-cycle allows further alias reuse while preventing different edge
   products from becoming the same monomial.
3. **One congruence recovers Pell indices and signs.** A separately certified
   cap bounds all possible indices. The pooled sum of index and abscissa-sign
   errors is then a nonnegative integer smaller than its divisor, forcing
   every error to vanish. The subsequent power signs are recovered in order.
4. **A strong multiplier is forced to be a square.** In the eleven-variable
   branch, a linear multiplier is recovered as a positive square by a
   coprime product, a congruence modulo three, and prime-adic separation.
   Supported-modulus interpolation gives the converse without changing the
   strong pair after selecting its residue.

## Comparisons

The comparison boundary is ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`, including all eight incoming
archives then present. All downloaded archive bytes match their Git blob IDs.

On exactly the same 519-variable input as the incoming height-one compiler,
the new 2,988-variable form replaces 7,431 variables and 34,086 monomials by
2,988 and 31,218, preserving both total degree four and individual degree at
most two. The 2,215-variable principal form additionally uses the later
442-variable source and permits individual fourth powers.

The natural240 form improves the inspected direct natural261 form in variables,
rows and terms, with a 5.9% coefficient-height increase. The signed381 form
improves the inspected direct integer442 form in variables and rows, with
larger support and height. The eleven-variable forms lower degrees 456→440
and 416→412, adding two operations. Other ProveIt families already have fewer
variables with different coefficient/degree tradeoffs. Keep all domains and
whole coefficient bindings separate when comparing results.

## Read and reproduce

Python 3.10 or later and its standard library suffice for the supported checks.
No network, CAS, proof assistant or package installation is needed.

```sh
python3 -B verify.py
python3 -B verify.py --optimized
python3 -B verify.py --rebuild-graphs --receipt /tmp/conzfc_replay.json
```

The default runner checks the sealed manifest, all three graph polynomials,
both natural quartics, both signed quartics, both eleven-variable circuits,
and reconstruction of all six fixed numerals. It preserves delivered equation
files. The inherited coefficient recipe is always run in its supported normal
mode, including when the new algebra checkers use `--optimized`.

Component README files document their exact rebuilds and check boundaries.
The graph rebuild compares every emitted mathematical JSON file byte for byte.
Separate receipts record the direct and eleven-variable reconstructions.
To rebuild the article:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The PDF includes every new mathematical argument and the complete principal
signed residual list. The principal graph coefficient list also appears as the
readable `graph/principal/polynomial.txt`. Every graph profile has its complete
sparse JSON coefficient list. PDF bytes can vary with TeX metadata; mathematical data
rebuilds are deterministic.

## File map and scope

- `graph/`: unit-coefficient polynomials, literal sources, graph/factor
  certificates, producer, compressor, independent verifier and replay receipts.
- `direct/`: new natural and signed C222 equations, complete coefficient maps,
  new proofs, exact source/sign/projection checks and scoped inherited compiler.
- `low_variable/`: two eleven-integer circuits, complete fixed numerals and
  recipe, signed/bootstrap/interpolation proof, exact degrees and checks.
- `inherited/`, `provenance/`: unchanged source proofs and calibration interfaces,
  original licenses, source-member maps, snapshot and archive identities.
- `reviews/`: separately tasked mathematical reviews, with their explicit scope.
- `RELEASE.json`, `MANIFEST.json`: endpoint inventory and static file hashes.

Finite verification proves finite identities and correspondence certificates;
it does not prove unbounded Pell or proof-theoretic facts by sampling. Those
are ordinary mathematical dependencies and new proofs, identified in the
article. A hash manifest is an integrity inventory, not a formal proof or an
authenticated signature. Read `NOTICE.md` for authorship and attribution.

The inherited-source ledger maps byte-identical texts to a single retained
copy, sometimes in another component. Five redundant historical repository
overviews are recorded by provenance without copying their contents; the
selected mathematical proof dependencies are retained. Historical relative
links should be resolved using that ledger.
