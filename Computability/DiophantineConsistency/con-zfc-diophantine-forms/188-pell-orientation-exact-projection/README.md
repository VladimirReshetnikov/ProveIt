# Pell orientation and exact projection for Diophantine consistency of ZFC

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Start with **report.pdf**. The editable LaTeX source is **report.tex**, with
the complete generated equation tables under `generated/`.

## Results

Each supplied equation has fixed integer coefficients and the stated domain.
The ordinary mathematical proofs, composed with the explicitly retained
calibrations, establish in ZFC that absence of solutions is equivalent to
syntactic `Con(ZFC)`. No assumption of consistency is used.

| Equation | Unknowns and domain | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Main direct equation | 84 unrestricted integers | 2,097,808 | 2,351 |
| Same polynomial with all literal leaves of magnitude at most 256 | 84 unrestricted integers | 2,097,808 | 2,379 |
| Matched direct control | 85 unrestricted integers | 2,097,808 | 2,382 |
| Scaled native companion | 14 positive integers | 118 | 66 |
| Ordinary native companion | 14 positive integers | 94 | 67 |

The direct equation has 23 squared residuals, versus 24 for the matched
control. It uses the C222 proof-calculus route, without K215 or Jones's
universal polynomial. The native companions use the complete authenticated
block-mask2963 coefficient tuple; all four fixed integers are supplied.

The direct polynomial is defined by its literal arithmetic graph and also by
the report's complete finite source rows, 16-request table, 122 integral unit
substitutions, and 84-coordinate input map. No unprinted program index or
unfixed coefficient remains. The high-degree polynomial is not fully expanded
into monomials; the graph is a complete coefficient specification.

## What is and is not new

This is an explicit composition and measured improvement. It is **not** a
claimed globally simplest equation or a new encoding breakthrough.

The affine Pell orientation principle is already in ProveIt package 136:

    sum_i((Y_i-k_i)^2) + sum_{i in I}(1-X_i) = (A-1)*Q.

Its residue proof permits the orientation quotient to be unrestricted. The
present construction applies it to all fourteen principal pairs of the current
signed-parameter source and
uses its unit coefficient on a Pell abscissa difference to delete a coordinate.
Composing with source173's anchor, the incoming five-base pool, and a fixed
acyclic substitution list yields the 84-variable equation. Against the matched
control it saves one coordinate, one residual, and 31 operations at unchanged
exact degree. The triangular reformulation is an equivalent quotient shear
of the earlier affine principle; it is not represented as a separately new
mechanism.

For a broader comparison, source177 reports an 87-integer equation of degree
8,388,612 with 2,447 operations and literal magnitudes at most 256. The supplied
bounded-literal realization improves those three figures to 84, 2,097,808,
and 2,379 at the same literal bound. The source177 figures are taken from its
authenticated README; its older verifier was not rerun as part of this release.

The 14-positive-variable companions combine the earlier Carrier65 idea with
earlier reduced auxiliary/ordinary strong certificates. The immediate
Carrier65 control uses 65 operations and degree 150. Paying one or two more
operations gives degree 118 or 94. The original Carrier65 archive used an
admissible942 tuple; both polynomials in the exact zero-set comparison here
are re-instantiated at the same current block-mask2963 tuple.

## Offline verification

Python 3.10 or later and its standard library suffice:

```sh
python3 -B verify.py
```

This authenticates the inherited source bytes, checks the independently
written whole-graph audit, parses the complete printed direct definition,
runs the native verifier, regenerates and compares
the report data, and checks the delivered manifest when present. It does not
search for a refutation or decide consistency.

The direct directory contains both its producer and two separate checkers.
All fixed projection choices are included; no optimizer, SciPy installation,
or network access is required for reconstruction or verification.

```sh
python3 -B direct/verify.py
python3 -B direct/build.py --check
```

The extra 205-variable degree-26 and 120/123-variable degree-32 graphs are
retained as intermediate and diagnostic tradeoffs. They are not claimed to
improve the repository's overall frontiers at those degrees.

## Evaluate a supplied tuple

```sh
python3 -B direct/evaluate.py integer84_degree2097808 --variables
python3 -B direct/evaluate.py integer84_degree2097808 tuple.json --residuals
python3 -B direct/evaluate.py integer84_degree2097808 --zero --modulus 1000000007
```

The direct tuple is a JSON list of exactly 84 integers. Exact evaluation can
create very large integers; modular evaluation is a practical diagnostic.
A modular zero is not an integer solution. Native evaluator instructions and
the ordered positive variables are in `native/README.md`.

## Rebuild the report

```sh
python3 -B build_report.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The generated appendices define the entire direct equation and the fixed
native coefficient recipe. PDF bytes can vary with TeX versions and metadata;
the mathematical artifacts are independently reproducible.

## Proof boundary and attribution

The ordinary proofs are formalizable in ZFC and identify the internally coded
finite refutation relation. They do not assume a transitive model of ZFC.
The full inherited unbounded C222/ZF/ZFC and arithmetic calibrations are
credited dependencies. Selected logical source files and the complete
original dependency archive are retained; the full proof-assistant import
closure was not rebuilt here. No new end-to-end Lean/Rocq certificate is
claimed.

Development and the independent internal reviews were AI-assisted. The
reviews are not represented as external human peer review. Prior source
notices and licenses accompany the retained material.

## Integration

The inspected snapshot is
`cdfea7d90176775d74c1c30afbe49fa78ade9897` of
`VladimirReshetnikov/ProveIt`. A suitable new directory is
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`
with an intake number and a name such as `pell-orientation-exact-projection`.
Preserve the matched control, coefficient payloads, provenance, and dependency
archive. These are alternative measured equations, not grounds to discard the
maintained smaller-operation or smaller-variable constructions.
