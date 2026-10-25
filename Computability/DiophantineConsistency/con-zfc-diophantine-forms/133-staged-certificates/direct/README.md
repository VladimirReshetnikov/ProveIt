# Staged Pell-index certificates for Diophantine consistency

This portable mathematical packet supplies four literal ordinary quartics over
nonnegative integers. Their new unbounded proof is `PROOF.md`; the inherited
shared-binomial, bounded-Pell, arithmetic and C222/ZFC calibration texts are
retained under `upstream/`, with hashes in `SOURCE_LEDGER.json`.

| Equation | Variables | Quadratic residuals | Expanded terms | Coefficient height |
|---|---:|---:|---:|---:|
| principal239 | 239 | 187 | 20,015 | 84,062,635 |
| sparse240 | 240 | 188 | 12,836 | 84,062,620 |
| minimum237 | 237 | 185 | 69,710 | 133,499,131 |
| small_support255 | 255 | 203 | 5,743 | 64,214,623 |

For each endpoint the equation is exactly the sum of the squares of all
residuals in `equations/NAME/natural/equation.json`. Every collected coefficient
is separately supplied in `expanded_polynomial.json`. In these files
`[c,[i,j,...]]` means coefficient c times the product of the indexed coordinates;
repeated indices are powers, and the empty list means the constant term.
Every listed coordinate ranges independently over N={0,1,2,...}.

The ordinary proof, composed with the identified inherited source calibration,
shows in ZFC that absence of a zero is equivalent to Con(ZFC). No consistency
assumption is used to prove this equivalence. This does not decide consistency,
claim a global optimum, or provide a newly completed Lean/Rocq/object-ZFC proof.
The equations encode the C222 proof calculus without simulating K215 or
instantiating Jones's universal expression.

The new step splits index authentication into two phases. One shared indexed
Pell cap bounds all actual indices. The first five requested indices are bounded
from raw rows and recover six exact powers, one binomial and the factorial.
The remaining ten requested indices become bounded only after that decoding.
A second error congruence then authenticates them. Thus the large label index
never needs to enter the early frame. The credited dominant-denominator lemma
from the incoming residue-compiler package supplies the smaller common modulus
M=N*D_x, after a raw endpoint argument made before factorial decoding. It
removes three product gates from the preceding 242-variable checkpoint.

## Verification and reconstruction

Python 3's standard library is sufficient. From this folder:

    python3 -B verify.py --rebuild --receipt receipt.json
    python3 -B -O verify.py --rebuild --receipt receipt-optimized.json

`verify.py` authenticates every retained upstream file, independently verifies
each natural monic-elimination certificate, checks every expanded coefficient,
and runs an independent audit of all 55 audited cap, frame, group, modulus, denominator and endpoint identities. With
`--rebuild` it reconstructs all literal JSON files in a temporary directory and
requires byte equality. Checks remain active under optimized Python.

To generate a separate copy:

    python3 -B build.py --output NEW_EMPTY_DIRECTORY

Builders write only beneath that output directory or a temporary directory;
they do not install dependencies or use the network. The supported entry
points are `build.py` and `verify.py`. Earlier programs retained under
`upstream/` are source/proof dependencies and historical provenance, not a
promise that every predecessor release entry point is included or supported.

The projected equations retain all domains through exact integer restoration
polynomials. Two restorations have negative coefficients but come with exact
rational sum-of-squares certificates of nonnegativity. These algebra checks
verify syntax and transformations; the unbounded number theory and calibration
are ordinary mathematical proofs, not conclusions inferred from finite tests.

Prepared with AI assistance for Vladimir Reshetnikov's ProveIt project,
24 October 2026. Inherited files retain their original notices and licenses.
