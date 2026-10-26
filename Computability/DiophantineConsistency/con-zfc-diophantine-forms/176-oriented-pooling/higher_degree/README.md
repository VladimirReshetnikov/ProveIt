# Certified lower-arity direct consistency polynomials

This component supplies nine explicit integer polynomial circuits obtained
by exact monic elimination from the new reciprocal-pooling equations.
Every variable ranges independently over all integers. Each no-zero
statement has the same ZFC-provable equivalence to Con(ZFC) as its source.
The source arithmetic and logical calibration are supplied by the surrounding
report. The projection theorem and finite certificate methodology are in
`PROOF.md`.

| Variables | Exact degree | Residuals | Live binary operations | Source |
|---:|---:|---:|---:|---|
| 194 | 6 | 131 | 2,682 | source211.json |
| 147 | 8 | 84 | 2,559 | source211.json |
| 135 | 12 | 72 | 2,498 | source211.json |
| 121 | 16 | 58 | 2,453 | source211.json |
| 115 | 24 | 52 | 2,438 | source209.json |
| 111 | 32 | 48 | 2,429 | source209.json |
| 105 | 64 | 42 | 2,495 | source207.json |
| 97 | 256 | 34 | 2,398 | source207.json |
| 90 | 32,768 | 27 | 2,306 | source206_joint.json |

The 121-variable equation at degree 16 is a moderate-degree alternative.
The 90-variable equation at degree 32768 gives the smallest arity in this
component; its high degree is an explicit tradeoff. These are improvements
within the direct proof-calculus branch. They do not claim globally minimal
polynomials or fewer variables than universal-polynomial constructions.

The method of acyclic unit-coefficient elimination is inherited from
ProveIt report 152. The new source equations and measured applications are
this iteration's contributions. In particular, report 152's direct profiles
include 153 variables at degree 8, 125 at degree 16, 117 at degree 32, 111 at
degree 64, 102 at degree 256, and 94 at degree 65540.

## Reproduce offline

Python 3.10 or newer and the standard library suffice:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B build.py --check
```

The independent verifier imports neither the producer nor the search program.
It authenticates all quadratic source rows, every pivot and restoration
expression, each imported circuit node and each final residual. It proves
the reported exact degrees using nonzero leading homogeneous coefficients,
and genuine occurrence of every variable using nonzero derivatives. Five
deliberately corrupted copies of each equation must be rejected. All checks
remain active under optimized Python. Actual receipts accompany the files.

The builder reconstructs all nine equation files byte for byte from the
frozen pivot certificates. To write a separate reconstruction:

```sh
python3 -B build.py --output /tmp/conzfc-monic-rebuild
```

The search is heuristic and supplies no optimality claim. It is unnecessary
for verification or byte-exact reconstruction. The ordinary proofs are not
replaced by finite examples or the verifier, and this is not a new
end-to-end Lean/Rocq build or an emitted object-language ZFC derivation.

## Equation format

Each `equations/integer*_degree*.json` is a complete finite polynomial
circuit, using only fixed integer literals and addition, subtraction and
multiplication. `output` names the single polynomial root.
`residual_roots` names its sum-of-squares components. No gate value is an
additional existential variable. There are no variable exponents, unknown
coefficient parameters or arithmetic oracles.

Every circuit's largest absolute literal is 384. This is not its expanded
coefficient height. The JSON gives a checked conservative bound of the
form 2^K on that height; exact expanded support and exact coefficient height
are not reported. Live binary operations count the emitted circuit's
sharing, not the expanded polynomial or a globally optimal circuit.

## Evaluate a supplied tuple

```sh
python3 -B evaluate.py equations/integer121_degree16.json tuple.json
```

`tuple.json` must be a JSON list of exactly 121 integers for this example.
Use `--residuals` to include the residual values. Evaluation is not a
consistency decision procedure or a root search. High-degree profiles may
produce very large integers even at small input tuples.

## Files

- `equations/`: nine complete polynomial circuits and their finite certificates.
- `certificates/`: the frozen monic pivot lists used for reconstruction.
- `source*.json`: exact source circuits and the authenticated literal P216 rows.
- `producer.py`, `build.py`, `search.py`: construction and optional search.
- `verify.py`: independently implemented exact checker.
- `evaluate.py`: exact integer evaluation.
- `PROOF.md`: zero-set bijection, degree and dependence arguments, provenance.
- `RESULTS.json`, `VERIFICATION*.json`, `REBUILD.json`: actual metrics and receipts.

The source files retain their provenance through exact SHA-256 bindings.
This component should accompany the main report and its inherited proof
closure, which identify the C222/ZF/ZFC refutation calibration.
