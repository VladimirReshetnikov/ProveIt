# Four fixed consistency polynomials with one fewer quotient variable

This portable packet supplies four explicit ordinary integer polynomials,
all with coefficients fully specified by one coherent indexed943/radix67
tuple from ProveIt package142. Their strictly positive zero existence is
equivalent to the existence of a finite syntactic ZFC refutation, by the
ordinary proof in `FIXED_CARRIER_PROOF.md` composed with the retained
native/refutation calibration. No global minimality claim or new
end-to-end Lean/Rocq certificate is made.

| Literal source | Positive coordinates | Operations | Multiplications | Additions | Subtractions | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| `fixed_13_residue_70_degree206.json` | 13 | 70 | 40 | 18 | 12 | 206 |
| `fixed_13_residue_71_degree162.json` | 13 | 71 | 40 | 18 | 13 | 162 |
| `fixed_13_residue_q4_72_degree154.json` | 13 | 72 | 41 | 18 | 13 | 154 |
| `fixed_12_rational_74_degree438.json` | 12 | 74 | 42 | 20 | 12 | 438 |

An operation is one binary addition, subtraction or multiplication;
squaring and multiplication by small constants each count once. Reused
registers and fixed integer leaves are free. The four fixed integers
total **295,388 canonical raw bytes**. This substantial fixed-data cost
is stated separately from the arithmetic-program count.

## Mathematical change

The first two sources eliminate the parent's positive index quotient
`h=(k-R-1)/E` by making the auxiliary Pell ordinate carry its residue
modulo `E`. Scaling a free strong multiplier by `E` enforces the needed
modulus without increasing the gate count. Signed main-index recovery
and a growth bound force the correct residue sign, restoring a positive
integer `h` in the soundness direction.

The third source uses only modulus `q^4`, which is larger than the
decoded index `R`. Scaling the multiplier by the existing `q^2` makes
`q^4` divide the square `S^2`; the full first Pell recurrence restores
the original `E` divisibility afterwards. This lowers the total degree
to 154 at one additional gate.

The fourth source applies the inherited rational adjacent-Pell
integrality lemma to the anchored parent. The polynomial substitutes
`t=n+(k-R-1)/E` and clears the denominator, then integrality forces the
deleted quotient to be an integer. A cofinal completion makes it
positive. The old lemma itself is not claimed as new.

## Contents and exact reconstruction

- `FIXED_CARRIER_PROOF.md` gives all polynomial definitions, the
  unbounded existence maps, signed index recovery, cofinal completeness,
  and attained leading coefficients.
- The four JSON files are complete topologically ordered arithmetic
  programs, with exactly their advertised quantified inputs.
- `coefficients/` and `COEFFICIENTS.json` contain the four entire
  fixed integers and their byte-level bindings.
- `rebuild_fixed_coefficients.py` reconstructs every coefficient from
  the fixed436-character seed, the complete943-tile formula, and finite
  radix formulas. It does no machine simulation or unbounded search.
- `fixed_constant_recipe_body.tex` prints the full finite constant
  recipe, including the literal seed, for inclusion in a report.
- `fixed_parents/` freezes the three immediate parent graphs, their
  ordinary proofs, the P66 graph/proof, and original coefficient binding.
- `fixed_sources/` preserves the ordinary indexed-native/Pell source
  proofs, explicit predecessor for rational integrality, source pins,
  coefficient specification, and upstream license notices. These retain
  their historical text and source identifiers.
- `SOURCE_MANIFEST.json` records every frozen retained-source byte hash.
- `build_fixed_carriers.py` reproduces all four source transformations.
- `verify_fixed_carriers.py` is an independent standard-library-only
  checker; it does not import the producer.

The underlying native computation is the inherited K215/Wang943
calibration. These constructions improve the arithmetic compilation of
that fixed calibration; they do not claim a new foundational proof system
or a machine-free equivalence.

## Reproducible checks

With Python3, run from this directory (or give absolute script paths
from another working directory):

```sh
python3 rebuild_fixed_coefficients.py
python3 verify_fixed_carriers.py
python3 -O verify_fixed_carriers.py
```

The producer is optional: the exact complete graphs are already present.

```sh
python3 build_fixed_carriers.py
```

The independent checker verifies all four frozen coefficient byte
strings, coefficient inequalities, graph topology, full gate/input
liveness, exact local integer-polynomial identities covering every gate,
the complete symbolic top homogeneous forms including the main-norm
cancellation, and one nonzero fixed-coefficient monomial per profile.
It also checks separately written scalar formulas and the frozen-parent
substitutions at actual-coefficient modular samples, and rejects
reachable arithmetic, degree, and operation-count mutations. Ordinary
and optimized-Python runs produce identical mathematical receipts.

These finite checks certify the files and algebra they inspect. They
are not an executable search for a ZFC contradiction, and they are not
an end-to-end proof-assistant verification of the native calibration.
The positive domain is essential to the theorem; the unmodified formulas
are not claimed to characterize consistency over unrestricted integers.
