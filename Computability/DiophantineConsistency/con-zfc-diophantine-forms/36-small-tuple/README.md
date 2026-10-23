# Smaller Diophantine presentations of ZFC consistency

Research synthesis for Vladimir Reshetnikov's ProveIt repository, 22 October 2026.
Comparison snapshot: `8c6eec9d19ef80538c8e61ff6e0180040583446a`.

The complete article is `report.tex` and `report.pdf`. Every recommended equation
is specified by a literal division-free arithmetic circuit, an exact variable
domain, and a complete fixed-coefficient binding. No program searches for a ZFC
refutation while constructing the coefficients.

## Results

* A smaller complete Wang943 coefficient tuple, with **B = 2^1012115** and four
  materialized ports totaling **506,664 raw bytes**, versus 977,220 at the pin.
* The same degree-1081, twelve-positive-variable polynomial template evaluated
  in **109** operations (previously 111); a corresponding three-equation system
  costs **103** operations (previously 107).
* The same degree-1069, twelve-positive-variable polynomial template evaluated
  in **120** operations (previously 123); its shifted system costs **114**.
* A combined evaluator for the degree-best nine-variable construction, with
  **1587** operations over nonnegative integers, or **1582** after converting its
  supplied variables to strictly positive integers. Its exact degree remains
  `120724*5^32+366`. The original 31-variable quartic and complete finite index
  recipe are retained. Its final index uses the new coefficient tuple.
* The inherited **67-operation** single polynomial and **59-operation** system,
  now also instantiated with the smaller complete coefficient tuple.

Each recommended form satisfies, by ordinary mathematics formalizable in ZFC,

`ZFC proves: (there is no solution in its stated domain) iff Con(ZFC)`.

The new local work consists of exact algebra, coefficient-interface proofs, and
finite certificates. It does not constitute a new end-to-end Lean/Rocq proof,
does not decide consistency, and does not establish global optimality. Positive,
nonnegative, and unrestricted-integer domains are not interchangeable.

## Choosing a presentation

For a short explicit system, use `baseline/retained16_system59.json`.
For fewer positive unknowns at moderate degree, use
`positive/circuits/short109_shifted_system.json`.
For one polynomial at the fewest inherited operations, use
`baseline/product67.json`. For the nine-variable choice, see `nine/README.md`.
All recommendations use one complete tuple from
`coefficients/COEFFICIENT_BINDING.json`; the historical files in `source/` and
`upstream/` are comparisons and keep their original identities.

The four ports are beta=B-1, K=DC+B*DR, MC, and **shifted**
MF=MF_native+B-1. Do not splice components from different tuples. All other fixed
leaves of the nine-variable equation have finite recipes in `nine/`.

## Offline reproduction

Python 3.10 or later and its standard library suffice for the main checks.

```sh
python3 verify.py
```

The command runs the independent coefficient audit, the algebra/circuit checks,
and the nine-variable binding checks; its output is `evidence/VERIFICATION.json`.
To rebuild all generated arithmetic and coefficient files before checking:

```sh
python3 reproduce.py
```

To compile the article:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

No actual zero of a consistency polynomial is searched for. Synthetic examples
test local arithmetic and the compiler interface only. Exact identities and the
unbounded semantic theorems supply the mathematical proof.

## Contents and provenance

* `coefficients/`: complete recipe, proof, literal machine transitions, binary
  payloads, independent arithmetic audit, and pinned source/license material.
* `positive/`: six new evaluators, exact reduction proof, source pins, checks.
* `nine/`: original and new coefficient bindings, quartic, index recipes, two
  nine-variable evaluators, and reproduction code.
* `baseline/`: the two small-operation presentations, rebound as a whole.
* `proofs/`: inherited Pell/compiler arithmetic proofs and the inspected Lean
  endpoint (a provenance copy, not a standalone Lean project).
* `evidence/`: the collection README at the comparison pin, audit receipts,
  source hashes, and final file checksums.
* `licenses/`, `NOTICE.md`: attribution and source licenses.

The archive is an additive research package. No repository commit, branch,
issue, pull request, or other remote state was changed.
