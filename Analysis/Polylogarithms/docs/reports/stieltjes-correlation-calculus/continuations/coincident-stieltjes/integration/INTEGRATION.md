# Integration proposal

## Placement

Continue the existing thematic spine rather than create a rival top-level report:

    Analysis/Polylogarithms/docs/reports/
      stieltjes-correlation-calculus/continuations/coincident-stieltjes/

Preserve the package's delivered layout. This is a new research delivery suitable for `docs/incoming`; it is not an applied repository patch.

## Relation to the earlier question

The source

    Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/
      continuations/shifted-hurwitz-jets/sections.tex

at observed commit `16c7e342d7a4a15f59911f322eb90b7f96c2a8b5` contains the further-research subsection **Collision and renormalized same-point products**. Its question includes both local off-point behavior and delta-supported distributional terms.

The new report proves:

- the exact off-point decomposition at every `(m,n,p,q)`;
- a single inverse-power logarithmic polynomial and an analytic remainder;
- equality of that remainder's value at zero with the unit-coordinate same-point Hadamard integral;
- a complete formula for those same-point moments.

It does **not** resolve the additional delta-supported extension coefficients. Mark the earlier question **partially resolved with a complete finite-constant solution**, not fully closed. The supplied `COLLISION_STATUS_NOTE.tex` is an optional review note, not an instruction to rewrite a preserved historical source.

## Suggested mathematical insertion order

1. Fixed-coordinate finite parts and the local completion lemma.
2. The base all-index Stieltjes formula and missing-index corollary.
3. Derivative closure, polygamma parity, and corrected integration by parts.
4. The raw Laurent-constant conversion warning.
5. Exact collision subtraction and its all-index logarithmic polynomial.
6. Collision antiderivatives, followed by the classical/compatible primitive bridge.

The article's labels and bibliography keys have prefix `csc:`. The source is a standalone article, not a drop-in chapter. Its small macros are in the preamble. When extracting material into the canonical book, preserve the distinction between spectral square-bracket derivatives and parenthesized argument derivatives.

## Acceptance checklist

Read the proofs of the local completion and collision theorems before promoting the coefficient tables. Confirm that the physical endpoint coordinate is unchanged. Re-run both scripts; successful finite replay is supporting evidence and does not by itself prove the analytic statements. Keep S6, S8, period independence, and the distributional delta-extension problem outside the proved scope.

The incoming binary archives were not read in this run. Check their contents for overlap before assigning novelty or placement among concurrent deliveries. Do not treat this package's inspection scope as an exhaustive repository audit.

No repository files were changed, no historical archive was deleted, and no automatic patch has been applied.
