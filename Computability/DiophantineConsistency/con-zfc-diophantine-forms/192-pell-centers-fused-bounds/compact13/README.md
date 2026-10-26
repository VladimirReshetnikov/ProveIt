# Two Pell roots carry two quotients

This component supplies new explicit consistency polynomials from the incoming
Carrier65 construction. Its main arithmetic idea uses the stronger residue
`psi_S(2j+1) = (-1)^j mod 4S^2` to remove a native divisibility quotient.
A positive free coordinate supplies the deleted quotient's sign before rank
decoding. See **PROOF.md** for the complete ordinary argument.

| Literal equation | Domain | Variables | Exact degree | Live binary operations |
| --- | --- | ---: | ---: | ---: |
| positive13_square.json | Strictly positive integers | 13 | 174 | 69 |
| positive13_oriented.json | Strictly positive integers | 13 | 170 | 70 |
| integer39_square.json | Unrestricted integers | 39 | 348 | 160 |
| integer39_oriented.json | Unrestricted integers | 39 | 340 | 161 |

The integer equations substitute `1+a^2+b^2+c(c+1)` for each positive
coordinate. Every polynomial is specified by an acyclic arithmetic graph;
registers are expression abbreviations, not quantified unknowns. The four
complete fixed integers are in coefficients/, with a finite reconstruction
from the 399-character literal SEED.txt. They occupy 94,689 uncompressed bytes.
They are the exact admissible942 tuple of the parent, not the indexed943
tuple used by several earlier compact equations.

Composing the new ordinary proof with the retained native/K215/syntactic
refutation calibration gives, inside ZFC, that each equation has a zero
in its stated domain if and only if a finite syntactic ZFC refutation exists.
Negation gives no zero if and only if Con(ZFC). No consistency assumption
is used or conclusion of actual consistency made.

## Verification

Python 3.10 or later, standard library only, no network:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B reconstruct_coefficients.py
```

The checker imports neither the graph builder nor its parent producer.
It checks exact formula cuts, all gate/input/port liveness, the full highest
homogeneous forms, exact degree on the actual numerical coefficient tuple,
all fixed coefficient bytes, finite reconstruction, and arithmetic fixtures.
It also validates all positive-coordinate substitutions in the integer lifts.
These exact finite checks supplement the unbounded proofs; they do not search
for roots or prove a quantified semantic theorem by testing examples.

To reproduce the four graphs, run `python3 -B build.py` in a working copy.
The builder overwrites only those four JSON outputs. For a supplied list of
39 integers, run `python3 -B evaluate.py tuple.json`; use `--profile` to select
another equation. `--modulus 1000000007` requests a modular diagnostic.

## Provenance and comparison

The comparison snapshot is ProveIt
`b42c796d1f5de9912a576bc2fd77b778ae7402bf`. The exact immediate source is
`docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip`. Its 14-positive-variable
equation has 65 operations and degree150; its standard integer lift has
42 variables, 163 operations and degree300. Our integer main equation uses
three fewer coordinates and three fewer operations, at increased degree.

Source170 supplies distinct 13-positive-variable profiles at70 operations /
degree206 and71 /162. Its coefficients total295,388 bytes. Our main69 /174
point is a measured tradeoff on a different complete calibrated tuple;
global minimality, dominance of every other equation, and worldwide novelty
are not asserted. The general idea of carrying quotients in Pell ordinates
already appears in source170. The new factor-four residue, native sign
recovery, and composition with the first root are identified in PROOF.md.

`inherited/` contains the exact first-carrier proof, its admissible942 native
proof, the uniform P66 arithmetic proof, finite controller certificate,
constant recipe and original notices. These are a scoped source subset,
not a newly rebuilt complete Lean/Rocq dependency closure. PARENT_REPLAY.json
records the original parent's finite checker run before this subset was made.
No fresh end-to-end proof assistant theorem or encoded object-ZFC derivation
is claimed. New material follows the retained MIT No Attribution license.
