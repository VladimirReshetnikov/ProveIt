# Independent review of the balanced 214-variable companion

Prepared 26 October 2026 by the separately assigned quartic research agent.
This is an independent implementation check inside the same AI research team,
not external peer review or a complete formal proof-assistant verification.

## Result

The balanced companion passed exact verification, both with ordinary Python
and with `python3 -O`. The final equation has 214 unrestricted integer
variables, 153 squared quadratic residuals, degree four, 5,699 nonzero
collected monomials, coefficient height 91,679, and residual coefficient
height 192. Every reported coordinate occurs in the final polynomial.

The final equation JSON has SHA-256

    f351ebddacc0515984a00617a8bd7c318a24beaa48b5ad4bfff5aa99f6c383b6

The comparison with the frozen incoming balanced endpoint is a saving of one
coordinate and one residual at the same coefficient height. The monomial
count rises from 5,660 to 5,699, so it is a tradeoff rather than a strict
improvement in every complexity measure.

## Exact source delta

The starting point is the frozen 221-coordinate uncontracted anchor source.
The new affine base is `D=2(C+F+1)`. The checker binds the actual coordinates
`F=x2`, `C=2*x17`, the old base `x194`, and `B=x4`; it independently verifies
the old base formula, including the historical offset of the first CRT
representative. It removes precisely the old base-defining residual and
substitutes the affine replacement everywhere. Exactly three retained
interfaces change: the base's power modulus, its multiplication wire, and
the shared square frame. The checker explicitly verifies the retained
divisibility `B*eta=C+F+1`, the essential source of `B|D`.

Compaction produces 220 variables and 159 residuals. Every resulting row and
every collected coefficient is compared exactly with the archived data.
The semantic soundness and completeness of this source change are proved
in the separate affine-radix proof; this finite comparison does not replace
that arithmetic argument.

## Projection and optimization

The preserved independent projection checker verifies five common-Hessian
projections, each with an integral reconstruction, leaving 215 variables and
154 residuals. It then verifies the affine consequence and its integral
restoration, leaving 214 variables and 153 residuals. The affine certificate
in this branch predates added input/output hash fields, so the independent
checker checks the exact polynomial identities and records the corresponding
input/output hashes in its receipt.

Using independently implemented sparse polynomial operations, the checker
executes all 75 integral coordinate and residual operations and compares the
result with the final equation. It then composes the inverse operations and
recovers the exact pre-optimization rows. A separate sum-of-squares expansion
recomputes every final quartic coefficient and all complexity measures.

Seventeen corruption controls are rejected: four source or expansion changes,
eight common-Hessian certificate changes, two affine certificate changes,
and three noninvertible or incomplete optimization changes. Requirements use
explicit exceptions, so the successful `python3 -O` run verifies that
disabling Python assertions does not disable these checks.

## Portable checker and receipts

`verify_balanced.py` imports the adjacent independent `verify_growth.py`,
not the construction program or its polynomial helpers. Its explicit
arguments are `--parent`, `--source`, `--radical`, `--affine`, `--optimized`,
and `--projection-helper`. The corresponding `check(...)` function accepts
paths or path strings. The ordinary and optimized-mode receipts are
`BALANCED214_INDEPENDENT_CHECK.json` and
`BALANCED214_INDEPENDENT_CHECK_OPTIMIZED.json`.

## Scope

The semantic radix proof and inherited numerical-calculus/ZF/ZFC calibration
remain mathematical dependencies. The check establishes exact source
fidelity and zero-set-preserving algebraic transformations. It does not
establish global minimality, worldwide novelty, or the nonsolvability of the
final polynomial.
