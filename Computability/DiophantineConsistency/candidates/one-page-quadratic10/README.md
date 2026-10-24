# Complete ten-positive equation, degree408,105 operations

`equation.pdf` and standalone `equation.tex` print the entire equation
and every fixed constant on one Letter page in9-point body type. The
only unknowns are ten strictly positive integers:

```
j_*, F, alpha, i, T, w, Y, n, eta, zeta.
```

The final equation is E^2-64*U*V_N=0, with every polynomial abbreviation
defined on the page. Its exact degree is408; the evaluator has105 live
binary operations,61 multiplications,26 additions and18 subtractions.
Every input and fixed port is live. There are no variable exponents,
hidden radicals, external coefficient tables or program oracles.

Compared with the maintained preceding ten-positive123-operation
degree816 page, this halves degree and saves18 operations. The four
fixed integers and their complete printed recipe are unchanged. This
is a significant improvement in both measured quantities at the same
unknown count; the old page is preserved in `one-page-scaled10`.
The13-positive90-operation degree51 page remains a different tradeoff.
No global simplicity minimum is claimed.

## Exact printed formula and evaluator

`polynomial.json` has the entire105-gate schedule and all four actual
coefficient payloads under `coefficients/`. Its parent is the frozen
`ten-positive-quadratic-projection-shared` evaluator. That evaluator
replaces a14-operation octic tail by the exactly equal13-operation
symmetric tail. Both tails are checked against all35 coefficients of
the independent eight-conjugate product; the centered polynomial has27
terms and unique top weight408 term omega^4.

The page writes A for the proof's A'-1, H for H', Delta for Delta',
M for Mtot, Z for Znum, S for fs and K for the fixed native port K0.
Its q_- is the already computed beta*J, equal to q-1. The new K_2 is
the polynomial X(X+2a'c)-1 and is distinct from the fixed K. The page's
Sigma1/Sigma2, P, U, V_N and E match the literal symmetric tail's
U/ab, Po, sc, aXb and Pe, respectively.

The renderer checks the entire transcribed front against all105 gates
over four free coefficient ports using exact shared terms modulo
associativity and commutativity of addition and multiplication. Thus
the displayed formula is bound universally, not merely at sampled
integers or by a hash of a claimed expanded polynomial. Both full
display schedules and alias conventions are in `SOURCE_PINS.json` and
the `PAGE_VERIFY` receipts.

## Complete constants, including the constructor

The whole TeX body from "The four fixed integers" to the end is copied
verbatim from the accepted `one-page-scaled10` template. It prints all
436 seed characters, the ordered62-character alphabet, the complete
quotient/remainder decoder, all943 tiles, the exact floor ranks, both
masks and the full native numeral formula. The corrected constructor
uses the decoded first transition's renamed target. Every index is
fixed or bound. The reciprocal intermediate in K cancels exactly.

All four compressed payloads and the seed are copied byte for byte
from that preceding page's coherent BFS-renamed compact44 tuple.
In normal and optimized Python, `verify_one_page_tuple44.py` independently
reconstructs every actual integer from the printed recipe, checks every
typed-tile/state conjugacy, and checks all66062 native basis/convolution
identities, carry threshold and controller units. All checks pass.
MF was already shifted by beta and is not shifted again.

## Ordinary correctness and its precise boundary

The original compact44 tuple and this BFS-renamed tuple differ in K.
Their numerical polynomial specializations are not being identified.
The preceding page's complete state/color, initializer, native and
controller argument supplies its ordinary calibration. Its frozen
README and whole polynomial are content-pinned in `SOURCE_PINS.json`.

The new quadratic-projection proof is uniform for beta odd and>=11,
0<MC<beta<MF<2beta and K0>0. The renderer explicitly checks those
conditions for this entire BFS tuple. The proof recovers the omitted
main Pell ordinate by all-index folding from the strong and auxiliary
Pell equations. A strict bound on the entire divisible projection
product excludes extra square-root branches without cancelling a
possibly nonunit factor. Explicit maps change only the positive
unknown n and prove equivalence of positive-zero existence with the
old scaled equation. The symmetric105-operation tail is then a
universal identity. No new native-calibration assumption is introduced.

The exact degree proof has leading part omega0^4, nonzero at beta>0;
the other three fixed ports cannot cancel it. It therefore applies
to this page tuple too. Finite modular lines supplement that ordinary
leading-form proof and are not used to establish the upper bound.

Composing the ordinary calibrated equivalences gives the same ZFC-provable
no-positive-zero/Con(ZFC) statement as the preceding construction. This
is an ordinary proof, not a new encoded object-ZFC derivation or a Lean
completion. The footer states that boundary explicitly. Neither
consistency nor the actual absence of zeros is asserted. Lean remains
paused.

From the repository root, reproduce the page and independent constants:

```sh
python -B Computability/DiophantineConsistency/tools/render_quadratic10_page.py --render
python -B Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py --output Computability/DiophantineConsistency/candidates/one-page-quadratic10
```

Both commands also pass under optimized Python. The verification,
visual inspection and complete packet seals are retained separately.
