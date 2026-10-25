# Shared XY carriers and partial q-saturation

This component supplies six literal ordinary polynomial equations, all with
ten independently strictly positive integer unknowns and the entire same
four-coefficient directly indexed BFS943 tuple. The main new operation/degree
points are:

| Equation | Operations | Exact degree | Proof |
|---|---:|---:|---|
| `equation_76_626.json` | 76 | 626 | `PROOF.md` |
| `equation_77_464.json` | 77 | 464 | `PROOF.md` |
| `equation_80_382_partial.json` | 80 | 382 | `PARTIAL_Q2_PROOF.md` |

The shifted companions 77/626 and 78/464 document the intermediate
transformation. The partial V-squared companion 79/516 is dominated by
77/464 and is included only to make the construction reproducible.

The ordinary proofs compose with named inherited universal Pell and native
calibration theorems to show that ZFC proves absence of a positive zero iff
Con(ZFC). This is a conditional equivalence theorem, not a proof of
consistency or unsolvability, and not a newly emitted formal proof object.
No claim of a global simplest equation or fewer unknowns than the existing
nine-positive equations is made.

The structural changes are:

1. Use the product `XY` as the index denominator and also in `A-1=XY+Y`
   and `V0=XY*Y`. Recover a sufficient divisor `q^4` before recovering
   the exact index and the full denominator.
2. Apply a fully proved unshifted auxiliary input, with the short exclusion
   of main index three from `q|X,Y`.
3. In the degree-382 alternative start with `Y=q^2s`, retain the positive
   fractional carrier term `s/q`, authenticate the first index, project
   `X=2^R`, and only then recover `q|s` and the original `q^3|Y` condition.

`build.py` reads the frozen parent JSONs only. It imports or runs no upstream
executable. `verify.py` checks all six circuits, exact whole highest
components, topology and liveness, literal transformations, coefficient
bytes, independent formula evaluations, and five actual artifact mutations.
`rebuild_coefficients.py` reconstructs the four whole numerals independently
from the inherited finite source recipe; its sole adaptation is its local
binding-file path.

Run with Python 3.10 or later:

    python3 -B build.py --check
    python3 -B verify.py
    python3 -O -B verify.py
    python3 -B rebuild_coefficients.py

`CHECK.json` and `CHECK_OPTIMIZED.json` are the actual local check receipts.
Upstream notices and licenses are retained. New research, code, and exposition
were prepared with AI assistance, under the same MIT No Attribution terms.
The mathematical proofs are ordinary arguments, not an outside human
endorsement or a machine-checked end-to-end proof.

Source snapshot: `e0c98c629bf10d30b695884f6b1d2ab361bdf513`, including the
incoming Certificate Reductions archive. The copied `upstream/` directory
contains its scale-one proof and mathematical dependency files, plus the
repository's unshifted-T proofs. Main fixed-coefficient byte lengths are
590,069 / 592,884 / 590,069 / 590,070 bits for beta/K0/MC/MF.
