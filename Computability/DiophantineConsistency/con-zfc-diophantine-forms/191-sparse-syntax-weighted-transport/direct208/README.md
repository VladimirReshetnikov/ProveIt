# A sparse-code quartic for Con(ZFC)

The literal endpoint is `equations/principal208/equation.json`:

\[
P_{208}(x_0,\ldots,x_{207})=\sum_{j=0}^{147}R_j(x)^2=0,
\qquad x\in\mathbb Z^{208}.
\]

Every variable is an unrestricted integer. Every residual is a completely
specified quadratic polynomial. The single quartic has **5,987 collected
monomials** and coefficient height **2^44 = 17,592,186,044,416**; its maximum
residual coefficient is **2^22 = 4,194,304**. All collected coefficients,
all 148 readable residuals, their LaTeX, and the complete variable order are
supplied beside the defining JSON.

The ordinary proof, composed with the explicitly retained C222/ZF/ZFC
calibration, establishes in ZFC that absence of integer zeros is equivalent
to syntactic Con(ZFC). It proves that equivalence, not consistency or
absence of zeros. The new bridge is not claimed to be an end-to-end
Lean/Rocq theorem.

## What changes

The four syntax constructors become offsets of one sparse quadratic:

    q(a,b)=(a+b)^2+a,
    I=4q, M=4q+1, A=4q+2, E=4q+3.

Their union does not cover all natural numbers. The supplied finite-proof
translation replaces the finitely many extra atoms in a derivation by
distinct tall constructor trees. It preserves constructor identities,
truth, falsity and the guarded disequalities. This proves equivalence of
refutability without a global bijection of numerical codes.

The larger constructor majorant is supplied by a Pell equation with center
8t+1. An affine signed horizon t=2+4z removes one more coordinate; the sign
of t is recovered from the already retained exact-power request q^t. Five
certified integral projections and 48 invertible coordinate/row operations
produce the final quartic.

| Equation | Integer variables | Rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Pinned incoming parent | 210 | 150 | 4 | 5,282 | 2^40 |
| This endpoint | 208 | 148 | 4 | 5,987 | 2^44 |

This is a dimension/row-count improvement with an explicit increase in
support and coefficient height. No global simplest-equation claim or
worldwide novelty priority is made. Neither K215 simulation nor Jones's
universal polynomial is used by this direct C222 branch.

## Read and reproduce

`PROOF.md` explains the whole new composition and source interface.
`proofs/` supplies the finite recoding theorem, the complete local bound,
the affine-horizon proof and the pinned parent Pell/radix proofs.

Python 3.10+ and the standard library suffice, from any working directory:

```sh
python3 -B /path/to/direct208/verify.py
python3 -O -B /path/to/direct208/verify.py
python3 -B /path/to/direct208/build.py --output /tmp/direct208-rebuilt
```

The verifier independently checks all nine axiom trees and all 75 acyclic
local gate definitions by exact rational elimination; every growth and
horizon edit; all five projection/reconstruction certificates; all 48
forward and inverse operations; every collected coefficient; all printed
LaTeX coefficients; input liveness; and a fresh byte-identical rebuild.
It rejects 20 deliberately corrupted projection certificates and a
corrupted printed variable. These checks do not search for a zero or
decide consistency. `--receipt PATH` writes a receipt at an explicit path;
otherwise verification is read-only apart from temporary rebuild files.

`evaluate.py point.json` evaluates the exact equation at a supplied JSON
list of 208 integers. Its optional `--modulus p` is only modular evaluation;
a modular zero is not asserted to be an integer zero.

## Provenance and inheritance

The pinned repository snapshot is
`d123610bc98fef2006bff1c9466bc3f1221003e7`. The immediate arithmetic parent
is `docs/incoming/ConZFC_Pell_Growth_210_2026-10-25.zip`. The enclosing
research archive retains that complete unchanged packet once under
`dependencies/`; this component keeps only its required finite inputs,
helpers and selected proof notes. `SOURCES.json` binds their exact bytes.
The new component runs without unpacking the ancestral ZIP.

The old `horn.F_times_S` definition is retained initially as a harmless
definitional extension and is removed by one of the five certified
projections. The semantic interface between the new syntax block and the
retained arithmetic has exactly two outputs, at old coordinates 79 and 95.

The inherited logical endpoint names are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The preserved parent
identifies their source and ordinary dependency boundary. The complete
transitive proof-assistant closure has not been freshly rebuilt. Internal
independent reviews are AI-assisted checks, not outside human refereeing.
Original notices and the source license are retained. No remote repository
write is performed by this component.
