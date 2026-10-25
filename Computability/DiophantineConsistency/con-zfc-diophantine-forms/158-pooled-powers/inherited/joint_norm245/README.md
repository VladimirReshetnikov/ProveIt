# A common norm removes all initial sign guards

Prepared for Vladimir Reshetnikov and the ProveIt research program,
25 October 2026, with AI assistance.

## Explicit equation

The delivered equation is

    P245(x_0,...,x_244) = sum_{j=0}^{180} R_j(x)^2 = 0,

over unrestricted integers. Every quadratic residual is in
`equation/equation.json`; every collected coefficient is in
`equation/expanded_polynomial.json`. A term `[c,[i,j,...]]` means the ordinary
monomial `c*x_i*x_j*...`, with zero-based indices. Repeated indices are
repeated factors, and an empty index list is a constant. Thus the definition
contains no unspecified coefficient, variable exponent, binomial, or
external predicate.

| Direct equation | Integer variables | Quadratic residuals | Degree | Collected terms | Coefficient height |
| --- | ---: | ---: | ---: | ---: | ---: |
| Pinned normalized-remainder parent | 252 | 182 | 4 | 5,340 | 128,446 |
| New common ceiling-and-digit norm | **245** | **181** | **4** | **5,304** | **128,446** |

The largest residual coefficient is 256. Every final coordinate is live.
These are exact finite counts, not estimates or minimality claims.

The ordinary proof, composed with the retained C222/ZF/ZFC refutation
calibration, establishes that ZFC proves

    (P245 has no zero in Z^245) if and only if Con(ZFC).

The report and mathematical proof provide the unbounded argument. The
scripts verify its finite polynomial objects and algebraic transformations.
This is a reduction within the direct numerical proof-calculus lineage;
it does not simulate K215 or instantiate Jones's universal polynomial.
It does not decide the equation's solvability, prove consistency, establish
a global optimum, or provide a newly checked end-to-end proof-assistant term.

## What changed

The normalized-remainder parent used one spherical bound for eleven digit
remainders and still required three initial ternary sign certificates.
The new construction puts the ceiling error into that same sphere. If
`M=q^x`, `V=(F^2+1)^t`, and `B` is the factorial-binomial output, the two
new quadratic rows are

    B*vB = M,
    F*M - vB*V - S = 0.

The old norm is enlarged by `4*S^2`. This gives
`|F*B-V|<|B|/2` once the raw nonzero divisor is identified. Three original
sign graphs, their nine private coordinates, and the old ceiling rows are
deleted. Only `vB` and `S` are added, giving seven fewer final variables.

The self-sized radix multiplier changes to `H=1+2*sum(a_i)` for the nine
actual representatives. It is odd and nonzero before their signs are known.
Signed-base Pell power recovery, the existing exact denominator-ratio rows,
and a nearest-integer factorial fixed-point theorem then recover the
deleted signs. The zero candidate `F=0` is treated separately; it cannot
be dismissed using the positive-argument binomial estimate.

Changing H changes a semantic witness construction. The new source is
proved equivalent in existence of zeros through the decoded refutation;
it is not asserted to be an integral coordinate chart of the entire old
source. The later monic eliminations and integral translations have their
explicit restoration certificates.

## Reproduce offline

Python 3.10 or newer and its standard library suffice. From any working
directory, run

    python3 -B /path/to/rounded245/code/verify.py
    python3 -B -O /path/to/rounded245/code/verify.py
    python3 -B /path/to/rounded245/code/verify.py --rebuild

The checker imports no producer module. It reconstructs every source edit,
checks the 88 inherited source files against their saved hashes, replays all
18 Horn factoring edits and 202 integral monic eliminations, verifies the
complete integer translation, and independently expands all 181 residual
squares. Six targeted corruptions are rejected. The `--rebuild` option
generates all 16 JSON artifacts in a fresh temporary directory and checks
them byte for byte against the delivered copies.

To write a receipt without changing an existing receipt, add
`--receipt /path/to/new-receipt.json`.

To build an additional copy manually:

    python3 -B code/build.py --output /tmp/new245/data
    python3 -B inherited/normalized252/code/center_integer.py /tmp/new245/data /tmp/new245/equation

The second command performs a fixed finite coordinate-translation search.
Its achieved chart and full translation certificate are already delivered;
no optimization result is required as an unproved mathematical premise.

For exact evaluation at a JSON list of 245 integers:

    python3 -B code/evaluate.py point.json

The evaluator is not a solver or a consistency decision procedure.

## File map and provenance

- `equation/`: final residuals, full quartic, exact metrics, and integral chart.
- `data/`: changed source and all factoring/projection certificates.
- `code/`: constructor, independent finite checker, and exact evaluator.
- `verification/`: actual check and reproduction receipts.
- `inherited/normalized252/`: the unchanged parent construction, its proof,
  original checks, and complete retained ordinary arithmetic/calibration
  source closure with licenses and notices.
- `SOURCE_PINS.json`: current comparison commit, incoming archive hash,
  every retained source hash, and final polynomial hashes.

The repository comparison is pinned to commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`, with input archive
`docs/incoming/ConZFC_Common_Remainders_Radix47_2026-10-25.zip`.
The named logical interfaces remain
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

New mathematics, code, and exposition were developed with AI assistance.
Independent reviews in this workflow refer to separately assigned research
agents, not external human review. Inherited files retain their exact
identities and notices. No upstream repository mutation is part of this
deliverable.
