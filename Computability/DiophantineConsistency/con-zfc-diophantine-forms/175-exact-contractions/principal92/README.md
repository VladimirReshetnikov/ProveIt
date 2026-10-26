# An explicit 92-integer polynomial of exact degree 692

This component defines one fixed ordinary polynomial in 92 unrestricted
integer variables. Its 29 residual squares are supplied as a finite arithmetic
circuit and as an acyclic substitution specification. No unspecified coefficient,
variable exponent, division gate, factorial primitive, or external predicate
occurs in the polynomial.

Composing the exact integer zero-set bijections in this component with the
identified inherited C222/ZF/ZFC calibration establishes in ZFC that the
polynomial has no integer zero if and only if Con(ZFC). This does not establish
consistency and is not a newly compiled end-to-end Lean/Rocq proof.

## Exact measures

| Measure | Value |
|---|---:|
| Unrestricted integer inputs | 92 |
| Residuals whose squares are summed | 29 |
| Exact total degree | 692 |
| Live binary addition/multiplication gates | 2,428 |
| Live nodes including inputs and literals | 2,648 |
| Largest absolute literal integer in this DAG | 46,656 |
| Certified expanded coefficient-height bound | strictly less than 2^1655 |

The exact expanded coefficient height and expanded monomial count were not
computed. Literal height, circuit operation count, degree, and expanded height
are different measures. Every one of the 92 inputs actually occurs in the final
polynomial, as proved by explicit nonzero modular partial derivatives.

The inspected direct-calculus comparison in report 152 has 94 unrestricted
integer variables, exact degree 65,540, and 28 residuals. The new equation
improves its arity and degree, while using one more residual. Report 152's
largest DAG literal is 256, smaller than the present 46,656; that comparison
should not be concealed. Its stated expanded-height bound is 2^164870. These
are comparisons with a pinned construction, not global simplicity claims.

## Literal definitions

- `circuit92.json`: the complete finite polynomial using only integer literals,
  the 92 inputs, binary addition, and binary multiplication.
- `projection92.json`: all 99 unit-pivot definitions, the ordered 92 free source
  coordinates, the 29 retained source rows, and degree bounds.
- `sources/source191.json`: all 128 source residuals in 191 coordinates.
- `sources/bridge191.json` and `sources/source220.json`: the preceding 29 exact
  unit projections and their complete authenticated 220-variable source.
- `PROOF.md`: the algebraic theorem, degree, occurrence, and height proofs.
- `specification/`: human-readable and LaTeX exports of the complete definition.
- `PROVENANCE.json`: source identities, the pinned parent archive, and the
  identified inherited calibration.

Names of eliminated coordinates are polynomial abbreviations, not additional
quantified unknowns. The coefficient lists and gate arrays are complete finite
data; loading them requires no network or consistency decision.

## Reproduce and evaluate

Python 3.10 or later and its standard library suffice:

```sh
python3 verify.py
python3 -O verify.py
python3 build_circuit.py
python3 verify.py --receipt /tmp/fresh_factored92_receipt.json
```

The verifier does not import the producer or search code. It checks the entire
220-to-191 coefficient bridge, all 99 subsequent integral restorations, the
literal circuit by exact structural expression equality, exact degree, genuine
occurrence of every variable, the coefficient bound, and deliberate corruptions.

To evaluate at one supplied JSON list of exactly 92 integers:

```sh
python3 evaluate.py tuple.json
python3 evaluate.py tuple.json --residuals
python3 evaluate.py tuple.json --restore191
python3 evaluate.py tuple.json --restore220
```

To project a supplied 220-coordinate tuple to the retained 92 coordinates:

```sh
python3 evaluate.py old_tuple.json --project220
```

Restoration is polynomial over all integer inputs. It satisfies the exact
pullback identity P220(restore220(x)) = P92(x), and induces a bijection of
the integer zero sets. Evaluating a specified tuple is not a zero search or
a consistency decision procedure.

## Proof boundary and attribution

The unit-pivot elimination method is established prior work in the supplied
ProveIt research collection, including reports 152 and 159. The new content is
the selected literal composition, its much smaller degree/arity endpoint, and
the complete finite certificates and implementation. The inherited source
archive and its mathematical calibration are preserved by the containing
submission. New material is AI-assisted mathematical research; independent
checks refer to separately implemented audits, not external human peer review.

The included MIT No Attribution license follows the parent source.
