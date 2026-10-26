# Residue ordinates for Diophantine consistency

This component supplies three literal equations in fourteen positive unknowns
and one literal equation in thirty-six unrestricted integer unknowns. The
ordinary proof restores the parent P66 equation and inherits its identified
whole-native-tuple/refutation calibration.

| Literal equation | Domain | Variables | Binary operations | Exact degree |
| --- | --- | ---: | ---: | ---: |
| `positive14_ops66_degree174.json` | Strictly positive integers | 14 | 66 | 174 |
| `positive14_ops67_degree158.json` | Strictly positive integers | 14 | 67 | 158 |
| `positive14_ops68_degree146.json` | Strictly positive integers | 14 | 68 | 146 |
| `integer36_degree288.json` | Unrestricted integers | 36 | 145 | 288 |

Positive graphs are in `equations/`; the unrestricted graph is in
`integer_equations/`. Each is a complete topologically ordered straight-line
program of additions, subtractions, and multiplications with a declared
quantifier list and output. Computed registers are abbreviations, not extra
unknowns. Every fixed exponent is evaluated through charged multiplication
gates. All fixed coefficient bytes are supplied in `coefficients/`.

## Mathematical contribution

The auxiliary Pell ordinate carries a congruence formerly certified by a
separate quantified quotient. Scaling the strong ordinate ensures the needed
modulus divides its square. The auxiliary odd-ordinate residue authenticates
the first index, and the quotient is reconstructed afterwards. Removing its
factor from the final product pays for the additional scaling gate. A smaller
modulus and removal of a known polynomial factor give the two degree reductions.

The unrestricted-integer presentation uses a specific sign audit: f,tau,n
already permit arbitrary integer values in soundness, so only the other eleven
coordinates require a three-variable positive parameterization. This gives
36 variables rather than the naive 42.

The main argument is in `PROOF.md`; the integer-domain proof is in
`INTEGER_DOMAIN.md`. `section.tex` and `coefficients.tex` are the report inputs.
`inherited/` contains the exact immediate P66 graph, the imported mathematical
proofs and finite native certificate, with source pins in `SOURCE_PINS.json`.

## Exact coefficients

All four numbers are the unchanged coherent Start-only4127 tuple from ProveIt
package 174, pinned at commit `02a78a08603cbae248c19c23a75907c6c6bd6443`.
The four unsigned big-endian byte files total 97,046 bytes. The largest has
194,440 bits. The complete closed finite recipe is printed in
`coefficients.tex`, including the 436-character seed and the full indexed tile
decoder. `rebuild_coefficients.py` reconstructs the entire four-number tuple
from that seed and verifies every supplied byte and hash.

These constants retain K215/native ancestry. The polynomial contains no
variable exponent, factorial, Turing machine predicate, or nonpolynomial gate.
The arithmetic cost does not include the bit length of a fixed integer leaf.

## Reproduce

Python 3.10 or newer and the standard library suffice:

```sh
python3 -B verify.py
python3 -B verify_integer.py
python3 -B rebuild_coefficients.py
```

The checks authenticate graph closure and liveness, all three exact positive
leaders, the main-norm cancellation, the independent displayed formulas, the
integer-domain substitutions and weighted leader, the coherent native
certificate/proof identities, and every fixed coefficient byte. They are
finite artifact checks, not a search for a refutation or a substitute for the
unbounded ordinary proof. `build.py` and `lift.py` regenerate the literal graphs.

The polynomial equivalence is not newly formalized end to end in Lean/Rocq.
No consistency assumption, consistency proof, minimum-variable theorem, global
optimality claim, or literature-priority claim is made. The documented
fourteen-positive-variable comparisons are 70 operations/degree 189 and
71/157; lower-variable constructions and small-coefficient quartics remain
different tradeoffs.
