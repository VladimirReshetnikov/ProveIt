# Semantic signs: direct quartics for Con(ZFC)

Prepared with AI assistance for Vladimir Reshetnikov and ProveIt,
24 October 2026. The inspected baseline is repository commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`.

## Fixed equations

| Endpoint | Domain | Variables | Degree | Quadratic rows | Monomials | Height |
|---|---|---:|---:|---:|---:|---:|
| Principal | Unrestricted integers | 286 | 4 | 196 | 6,607 | 128,446 |
| Parity companion | Unrestricted integers | 319 | 4 | 207 | 5,779 | 128,446 |
| Matched package-131 parent | Unrestricted integers | 324 | 4 | 208 | 5,808 | 128,446 |

The principal equation is exactly the sum of the squares of all residuals
in `principal/centered/equation.json`. The companion is defined in the
same way by `generated/centered/equation.json`. The corresponding
`expanded_polynomial.json` files supply every collected coefficient.
Coefficients are integers; repeated coordinate indices mean repeated
factors; an empty index list denotes a constant term. Coordinate order
and source names are specified by each equation file's `variables` list.

Both equations have ordinary proofs, formalizable in ZFC, that their
integer unsolvability is equivalent to Con(ZFC). They encode the numerical
C222 proof calculus directly and use no K215 simulation, Jones universal
polynomial, or Sun reduction. No proof of consistency, global minimality,
literature-wide priority, or new end-to-end proof-assistant object is claimed.

## Mathematical contribution

`PROOF.md` proves the compatible even-frame and odd-anchor reductions.
`PROOF_ORIENTED.md` gives the complete larger reduction, including the
noncircular recovery of ten front signs from their existing integer power
certificates, the zero-representative extension of CRT decoding, the odd
square radix, and the improved cofinal beta modulus. The 286-variable
equation trades additional monomials for 38 fewer variables; the
319-variable companion improves every varying metric of the matched parent.

`INDEPENDENT_REVIEW.md` records a separately performed mathematical review
within this AI-assisted workflow. It is not external human peer review.

## Offline reproduction

Only Python 3.10 or newer and its standard library are needed. From this
component directory run:

    python3 -B verify.py
    python3 -B verify.py --rebuild
    python3 -O -B verify.py --rebuild

The checker verifies exact new source rows, the nine source power calls,
the fourteen remaining guards, source hashes, Horn factorization, monic
integer projection certificates, integral translations, and the complete
collected polynomial. `--rebuild` independently regenerates both selected
endpoints in a temporary directory and compares the mathematical files
exactly. `--receipt PATH` writes its finite-check receipt outside the frozen
release if desired. Finite arithmetic regressions supplement the ordinary
unbounded proofs; they do not replace them.

The direct authoring commands are:

    python3 -B build.py --output DEST --orient --odd-radix --linear-cofinal --center
    python3 -B build.py --output DEST --center

The first builds the principal equation and the second the parity companion.
Do not regenerate into a frozen release directory when checking its hashes.

To evaluate a supplied JSON array of 286 integers exactly, run
`python3 -B evaluate.py point.json`. Add `--companion` for an array of 319
integers. This is an exact evaluator, not a solver or consistency test.

## Source and logical closure

`input/` retains the exact signed source, its parent metadata, and its full
ordinary proof. `inherited/` retains the arithmetic, factorial, CRT, Horn
flow, local majorant, and proof-calculus exposition. `calibration_primary/`
contains the named unconditional C222/ZF and ZF/ZFC theorem interfaces and
the actual numerical calculus definitions. These are provided as source
evidence; the full transitive Lean build is not claimed or invoked.

`SOURCE_PROVENANCE.json` identifies every retained source file, its repository
path, snapshot, and exact SHA-256. Original notices and licenses are retained.
The new material follows the repository's MIT No Attribution terms.

The canonical equation SHA-256 values are:

- Principal: `5039d1907601db05946a6535a3f83edcb6e96c5b2469e8062fa99472ec32c6d1`.
- Parity companion: `22478ad55f603ff4a4d7650cd7867ce905c93d64c3cad2eb382d2b9771d65e74`.

The corresponding complete polynomial SHA-256 values are:

- Principal: `5f06e2b519dc1a5981c18caa056d95553150ef4126bd071a4479dac5411cb588`.
- Parity companion: `397de49033d9587791d80b18d5ef3882c71dfbe6f7752fb87995112ee71f6455`.
