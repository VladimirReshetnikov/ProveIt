# POWER with twelve positive leaves

A separate arithmetic continuation, 4 October 2026. All earlier packets remain unchanged.

For every integer b>=2 and C,o>0, the explicit polynomial in `PROOF.md` vanishes at some positive auxiliary tuple exactly when o=b^(C-1).

- 12 positive module leaves including the output, or 11 auxiliary leaves beyond it
- 5 residuals, combined as one sum-of-squares equation
- Exact degree 20 for fixed b, and 24 for an independent or positive affine base input
- Infinite full witness fibers at every accepted argument
- Native-gap composition with the retained three-witness bounded compiler: 29 positive witnesses, 3 external positive inputs, 18 residual slots, one final equation

The new direct positive q_alpha permits elimination of the positive Pell witness u. Two rational-square arguments and a sign argument recover alpha and u as ordinary positive integers. The witness bijection is with the strict-q_alpha subset of the old 13-leaf formula; the beta progression establishes existential equivalence with its full solution set. It is not a global bijection of the old and new tuples.

## Files

- `PROOF.md`: all formulas, domain recovery, completeness, image description, degrees, infinite fibers, and explicit bounded composition
- `REVIEW.md`: separate domain/degree review and execution-scope record
- `static_algebra.py`: fresh inspected standard-library exact algebra and finite fixture checker
- `evidence/results.json`: actual check counts and degree receipts
- `evidence/*.polynomial.json`: fully expanded fixed-base-two and positive-variable-base residuals and polynomials
- `evidence/full_fixtures.json`: complete finite positive assignments, including exponent zero and exponent one
- `SOURCE_PINS.json`: unchanged mathematical dependencies, origin locations and SHA-256 hashes
- `MANIFEST.sha256`: hashes of every packet file except the manifest itself

Only the new inspected checker was executed. It passed five complete module expansions, five generic elimination identities, twenty complete fixtures evaluated in both fixed and variable forms, five symbolic family identities, and six full 29-witness composition expansions. Before/after inventories verify that the old packet is unchanged.

The all-exponent theorem still uses the pinned constructive Pell theorem pair; this is not a new Lean build. No upstream or source-author script, counter interpreter, physical simulator, saved schedule, or science pipeline was executed. No minimum-arity, minimum-degree, efficient-witness, finite-fold, novelty, priority, or universal-polynomial record claim is made.
