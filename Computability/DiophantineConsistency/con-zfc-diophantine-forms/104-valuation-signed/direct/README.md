# A 1,190-integer direct C222 quartic

The complete polynomial is in `output/expanded_polynomial.json`; equivalently,
it is the sum of the squares of the 600 literal quadratic residuals in
`output/equation.json`. It has **1,190 unrestricted integer variables**,
exact degree **4**, **26,411** nonzero monomials, and coefficient height
**83,900,628**. Its lack of integer zeros is provably equivalent in ZFC to
Con(ZFC), using the ordinary proof in `PROOF.md` and the explicitly inherited
direct-C222 calibration. Neither K215 nor Jones is used.

The frozen synchronized parent has 522 natural variables. A finite ordered
certificate infers the signs of 288 of them from 234 explicit quadratic
nonnegativity guards, yielding a 1,224-integer checkpoint. Thirty-four exact
signed monic substitutions then yield the stated endpoint. The checkpoint
has fewer expanded monomials (23,590) and is retained as a tradeoff.

Relative to the received batched 1,690-integer direct quartic, the final
equation saves 500 variables and 242 residuals, has substantially smaller
coefficients, and uses 5,030 more monomials. There is no global minimality or
worldwide novelty claim. Full details and the proof boundary are in
`PROOF.md`; `section.tex` is an editable article section.

## Reproduction

Python 3.10 or later and the standard library suffice. From this directory:

```sh
python3 build.py --check
python3 verify.py . --receipt INDEPENDENT_CHECK.json
python3 -O verify.py . --receipt INDEPENDENT_CHECK_OPTIMIZED.json
python3 verify_projection.py input/equation.json output
```

To regenerate the new literal artifacts in place, run `python3 build.py`.
To replay the entire retained parent construction, run
`python3 upstream/synchronized/verify.py`.

## Files

- `source/parent_natural.json`: byte-pinned 522-natural-variable parent.
- `input/`: 1,224-integer checkpoint, complete expansion, and all 234 guards
  plus 288 ordered sign inferences.
- `output/`: final polynomial, residual presentation, and every signed
  elimination with its inverse restoration.
- `verify.py`: independent standard-library check; imports no producer or
  optimizer and rejects four deliberate corruptions.
- `upstream/synchronized/`: complete received parent, proofs, calibration
  copies, licenses, source code, and verification certificates.
- `SOURCE_PINS.json` and `NOTICE.md`: exact provenance and licensing.

The new proof is ordinary mathematics formalizable in ZFC; no new complete
Lean/Rocq proof term or internal object-ZFC derivation is claimed. The result
is an equivalence, not a proof that ZFC is consistent or that the equation
has no solution.
