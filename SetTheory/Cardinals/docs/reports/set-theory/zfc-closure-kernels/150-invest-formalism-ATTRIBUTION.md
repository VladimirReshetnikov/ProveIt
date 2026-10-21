# Attribution and inherited proof boundaries

Source repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `9adcaff0a72486ecc81242e0eca86e428c74879e`.

The following files are unchanged copies, with paths relative to
`Computability/BusyBeaver/Research/ZFC/`:

| Packet file | Original path |
|---|---|
| `upstream_quantifier_checker.py` | `k218-quantifier-stability/check_derivation.py` |
| `inputs/source_language.py` | `k219-continuation-search/compiler-inputs/source_language.py` |
| `inputs/build221.py` | `k219-continuation-search/compiler-inputs/build221.py` |
| `inputs/sites218.json` | `candidate-k218/sites218.json` |
| `inputs/k218.native.tm` | `candidate-k218/k218.native.tm` |

The `flat` and closed-forest `splice` routines in the measurement script are
adapted from `k219-pivot-fusion/code/measure.py` at the same commit.

The persistence-stability lemma, Hilbert deduction transformation, and
unrestricted-rho8 recovery helper were already supplied by
`k218-quantifier-stability`. Own-code freshness is also inherited:
`Sound230.D_fr` and `D_fr_self` already prove the necessary free-label
bound, and `Sound222.V_bundle222` already uses `D_fr_self` for the seed
matrix. The new contribution specializes persistence to the binder equal
to the formula's own native code, gives the resulting classicality
replacement and decoded-theory calibration, records a direct stronger
bound for all occurring labels, measures the direct source replacement,
and supplies the explicit fixed-B matrices and Heyting-fragment witness.

The exact Rocq decoder uses a closed T0 at zero and primitive negation
when an implication code's right child is native 1. Its implication
equivalence is proved in the IR comparison theory. The relevant pinned
vendor sources, relative to the repository root, are

- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-settheory-KDecoder230.v`;
- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-logic-Sound230.v`.

The inherited set-theory interpretation and original numerical calibration
are in `k225-formal/rocq224/src/Sound222.v` and `Complete222.v`, with their
imported dependencies. This packet does not rerun or modify their proof
assistant builds. It spells out the ordinary proof adaptations for the new
schema and checks only the finite Hilbert derivations claimed in the note.

The ProveIt repository root license is reproduced below.

## MIT No Attribution License

Copyright 2026 ProveIt Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
