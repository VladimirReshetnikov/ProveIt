# Thirteen integer variables through a single five-radical norm

Research contribution prepared for Vladimir Reshetnikov's ProveIt project.
Review date: 24 October 2026. Repository snapshot:
9a33342a03d19cf5b061b2083c6b5d3f27f752ed.

## Main result

The preferred equation has **13 unrestricted integer variables, exact degree
1088, and 195 live binary arithmetic operations**. A simpler carrier gives
degree 1392 in 186 operations. All fixed coefficients are literal, authenticated
integers; all circuit gates are addition, subtraction, or multiplication.
There are no unspecified coefficient parameters, variable exponents,
division or square-root operations, or hidden existential variables.

Read [the paper](report/report.pdf), whose editable source is
[report/report.tex](report/report.tex). The additional degree-1088 construction
is explained in [report/crt1088.tex](report/crt1088.tex).

The new idea is a guard inside a radical norm. Four radicands are positive on
every integer input. A norm zero therefore forces the remaining guard radicand
to be nonnegative. Its positivity consequences separate all five radical
magnitudes, making their roots rational and then integral. This avoids large
separating weights. The degree-1088 variant additionally uses one coprime
congruence carrier to restore the cubic Pell scale and the main congruence.

## Exact scope of the consistency claim

The paper proves the new algebraic and number-theoretic reduction. Composing
it with the named, pinned ordinary native/compiler and K215 calibration
theorems gives the ordinary mathematical theorem

    ZFC proves:
      [for every x in Z^13, P(x) != 0] iff Con(ZFC).

Here Con(ZFC) is syntactic consistency for the same finite proof coding used
by the imported calibration. The result neither assumes nor proves Con(ZFC).

The inherited calibration is an explicitly imported ordinary theorem, not
a new verification result of this archive. The repository's full native
kernel certificate and encoded object-language ZFC derivation remain separate
formalization obligations. This archive does not claim to close them.
If the inherited ordinary calibration is treated as an outstanding theorem
to be independently re-established, the final consistency conclusion is
conditional on it; the new algebraic reduction remains independently proved.
See [CALIBRATION_STATUS.md](provenance/CALIBRATION_STATUS.md) and the verbatim
ordinary sources under [provenance/upstream_ordinary](provenance/upstream_ordinary/).

No claim of global minimality, world variable-count record, or historical
priority is made. The comparison includes both requested repository
locations and their incoming proposals at the pinned snapshot.

## Delivered equations

Every row below has domain Z, with every input unrestricted.
Counts use shared identical subexpressions, binary +, -, and multiplication,
and do not count numeral or variable leaves as operations.

| Literal JSON stem | Integer variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| norm13_crt_degree1088 | 13 | 1088 | 195 |
| norm13_degree1392 | 13 | 1392 | 186 |
| norm13_degree1408 | 13 | 1408 | 185 |
| norm14_degree696 | 14 | 696 | 150 |
| norm14_degree792 | 14 | 792 | 137 |
| norm15_degree344 | 15 | 344 | 131 |
| quotient20 | 20 | 24 | 120 |
| quotient20_transport | 19 | 28 | 116 |
| quotient19_transport | 18 | 32 | 112 |
| quotient18_transport | 17 | 88 | 110 |

The first six are in [equations](equations/). The four quotient companions,
their proof and independent verifier are in
[companions/quotient_fusion](companions/quotient_fusion/).

The principal variables are, in circuit order:

    j, C, z, h, r, v, w, T, c, n, t, p2, p3

Case matters: C and c are distinct unknowns. All other named registers
are polynomial abbreviations, not quantified coordinates.

## Reproduction

Python 3.10 or later and its standard library suffice for the arithmetic.
No network connection, theorem-prover installation, numerical solver,
or simulation of the blank machine is required.

From the archive root:

    python3 build_equations.py
    python3 verification/verify_release.py
    python3 -O verification/verify_release.py

The builder rewrites the six principal JSONs and the metrics deterministically.
The release verifier is read-only unless an explicit output receipt is requested:

    python3 verification/verify_release.py --output /tmp/release-receipt.json

To rebuild the PDF with an ordinary TeX installation, run twice:

    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=report report/report.tex

The paper uses standard LaTeX packages including amsmath, amsthm, mathpazo,
geometry, booktabs, microtype, listings, fancyhdr, and hyperref.

## Verification

The release verifier:

- Checks the complete fixed coefficient byte strings and reconstructs their
  entire integer values from the finite tile recipe.
- Replays the original source-34 bounded recipe, including all 943 tiles and
  69,230 basis-convolution checks.
- Rebuilds every delivered circuit and checks declarations, liveness,
  topological order, and binary-operation counts.
- Verifies all coefficients of the generic cleared radical norms, with
  35, 495, and 20,349 nonzero monomials for three, four, and five roots.
- Checks the cancellation-sensitive exact degree certificates and explicit
  nonzero leading coefficients on the actual fixed-coefficient slice.
- Compares literal circuits with independently implemented formal conjugate
  products modulo three primes, including c=0, v=0, and their intersection
  where applicable. These are labelled finite transcription diagnostics.
- Runs a negative control that corrupts a norm coefficient while preserving
  graph shape; the independent arithmetic check must reject it.
- Verifies the four low-degree quotient companions, including their exact
  leading coefficients and actual-coefficient transcription diagnostics.
- Checks the delivered file manifest when present.

Normal and optimized Python runs pass. Acceptance does not depend on
removable assertions. The JSON receipts in verification record the results.
These finite checks do not prove the unbounded inherited compiler theorem;
the paper and retained ordinary source proofs supply that logical argument.

## Fixed coefficient provenance

The six coefficients are the coherent source-34
mixed-parity-unrounded-1064921 tuple and source-71 determinant scales:

    beta = 2^1064921 - 1
    K0, MC, MF = exact source-34 ports
    cone_A = 2^1113
    cone_B = 2^666104

MF is already MF_native + beta and must not be shifted a second time.
All six minimal unsigned little-endian payloads are supplied, gzip-compressed
with a fixed timestamp. Together they occupy 615,883 raw bytes.
[coefficients/BINDING.json](coefficients/BINDING.json) binds their exact hashes.
The finite mathematical definition is in the paper's coefficient appendix;
the full machine and tile data are also included, so the tuple is recoverable
offline rather than identified only by a hash.

## Integration

This is a self-contained proposal directory suitable for a new
con-zfc-diophantine-forms package. No existing repository file is overwritten,
no new Lean endpoint is asserted, and the original proof/formalization
boundaries remain explicit. The principal innovations are described in the
paper; research notes and independent reviews are retained for auditing.
Original licenses and notices are in licenses. New authored code and text
follow the repository's MIT No Attribution license, subject to the retained
notices for verbatim upstream material.
