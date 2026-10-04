# POWER with 22 positive leaves

Separate arithmetic continuation, 4 October 2026. No numbered report is changed.

The four signed congruence quotients in the retained POWER module are nonnegative in every positive solution. Replacing each pair of natural aliases with one natural quotient leaves **22 positive module leaves including the output**, **21 auxiliary leaves beyond the output**, **15 residuals**, and **exact degree 12** after summing squares. The index and any separately supplied base are excluded from the module count.

The all-exponent equivalence still depends on the pinned constructive Pell theorem pair. Removing the paired aliases does **not** give finite fibers: the Pell parameter beta can vary through an explicit infinite progression at every accepted input.

- `PROOF.md`: full equations, sign proof, both witness maps, exact accounting, and infinite-fiber proof
- `ELIMINATION_VARIANTS.md`: further exact alternatives: 16 leaves/9 residuals/degree 12; 14 leaves/7 residuals/degree 16; 13 leaves/6 residuals/degree 16 at fixed base (degree 20 for a variable base)
- `check_reduction.py`: freshly written exact polynomial/Pell fixture checker; no prior code is imported or run
- `evidence/results.json`: finite checks, counts and degree receipts
- `SOURCE_PINS.json`: unchanged, inert mathematical dependencies with source locations and byte hashes
- `MANIFEST.json`: final packet hashes

The native-gap decoding overhead becomes 46 positive witnesses, and composition with the retained three-witness bounded certificate uses 49 positive witnesses and 38 residual slots. These are separate replacement constructions, not edits or retroactive count corrections to Reports 65/66. There is no minimality, universal-polynomial record, finite-fold, arithmetic-gate, or witness-height claim.
