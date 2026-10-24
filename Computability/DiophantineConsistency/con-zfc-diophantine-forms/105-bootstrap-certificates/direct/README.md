# Direct C222 quartics with a polynomial factorial bootstrap

This component contains a quartic in **468 nonnegative integer unknowns**,
with **364 quadratic residuals**, **14,842 expanded monomials**, and maximum
absolute coefficient **83,850,989**. The companion with one extra unknown
has 12,051 monomials. The exact parent has 781 unknowns and 677 residuals.

A second complete alternative uses **467 nonnegative unknowns**,
363 residuals, 18,479 monomials and coefficient height 83,880,005. It
uses the output-linear radius R=n²F and its own 783-coordinate parent.
Both radius theorems and all three natural equations are supplied.

For each supplied system, the single polynomial is the sum of the squares
of its literal quadratic residuals. Every coefficient and variable is
explicitly listed. The ordinary proof, composed with the identified
inherited C222/ZF/ZFC calibration, proves in ZFC that its lack of natural
solutions is equivalent to Con(ZFC). No consistency assumption is used to
choose coefficients or prove the biconditional.

The key new theorem permits the factorial graph to use a polynomial radius
depending on its own output. If R=F², then

    F = ceil((R+1)^n / binomial(R+n,n))  iff  F=n!.

Uniqueness of this fixed point is proved in `proofs/NEW_RESULTS.md`. In the
materialized equation it removes an entire exponentiation certificate.
The same radius serves both needed factorials. A separate branch projection
removes two local proof-label coordinates, giving a nine-column source.

The inherited arithmetic/compiler facts, notices and provenance are included.
This component encodes C222 proof rules directly, with no K215 simulation
and no Jones universal polynomial. It improves the direct quartic line,
not the global fewest-variable frontier. No new full Lean/Rocq proof term or
encoded object-language ZFC derivation is claimed.

## Files

* `equations/natural468/equation.json`: all variables and all 364 residuals.
* `equations/natural468/expanded_polynomial.json`: the complete polynomial.
* `equations/natural468/elimination_certificate.json`: exact restoring maps.
* `equations/natural469/`: a smaller-support square-radius alternative.
* `equations/natural467/`: the output-linear alternative with fewer variables.
* `equations/parent783/`: its exact source parent.
* `equations/parent781/`: literal shared-arithmetic parent and macro ledger.
* `proofs/NEW_RESULTS.md`: source equivalence and factorial bootstrap proofs.
* `code/bootstrap_builder.py`: complete explicit source compiler.
* `verify.py`: portable rebuild and independent coefficient/replay checks.

A polynomial term is `[coefficient, variable_indices]`. Variable indices are
zero based and repeated indices denote powers. The empty list is a constant.
All numbers are literal integers. There are no remaining exponentiation,
factorial, binomial, variable-length-list or coefficient-port primitives in
the equation files.

## Reproduce

Only Python 3.10+ and its standard library are required. From this directory:

```sh
python3 verify.py
python3 -O verify.py
python3 code/bootstrap_builder.py --output /path/to/new-square-parent
python3 code/bootstrap_builder.py --radius linear --output /path/to/new-linear-parent
```

Verification rebuilds both parents in temporary directories, compares their
core JSON artifacts byte for byte, regenerates all three natural contractions,
replays every restoring map independently, expands every squared residual,
checks every coefficient, authenticates inherited files, and rejects two
deliberate corruptions. The finite arithmetic controls do not replace the
unrestricted proofs. Verification never searches for a polynomial solution.

The wider package supplies the new unrestricted-integer conversion and report.
