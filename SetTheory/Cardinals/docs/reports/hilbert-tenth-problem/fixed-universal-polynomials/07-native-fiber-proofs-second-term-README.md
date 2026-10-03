# Full-fiber second-term analytical addendum

Date: 2026-10-03. Frozen reviewed result, separate from all earlier packets.

## Result

For the already classified complete native witness fiber, with T=log H and fixed data,

    N(H)=κT+ζ(1/2)√T/(M0√λ)+O(T^(1/3)).

For nondecreasing witness heights counted with multiplicity,

    log H_v=v/κ−ζ(1/2)√v/(M0√λ κ^(3/2))+O(v^(1/3)).

The exact κ from the leading-term result is unchanged. The estimate is unsmoothed and covers every threshold, including height ties. This is not a multiplicative equivalent for H_v.

## Files

- THEOREM.md: complete deterministic-cutoff proof, controlled clipping/corners, exact κ, and tied-height inversion
- INDEPENDENT-COUNT-REVIEW.md: independent PASS using exact sign-specific cutoff rectangles
- CHECKS.md: finite test scope, numerical tables, and evidence limitations
- ../../check_second_term.py: portable standard-library supporting checks
- ../../SECOND-TERM-RECEIPT.json: saved deterministic result, compared read-only by default
- ../../provenance/second-term-original-MANIFEST.sha256: SHA-256 checksums of the original source filenames and bytes; use the root provenance verifier for the adapted delivered copies

## Replay

    python ../../check_second_term.py
    python -O ../../check_second_term.py

Run from any directory; file paths are relative to the script. The default replay does not modify the packet. To intentionally replace the receipt, use `python ../../check_second_term.py --write`.

## Dependencies and attribution

The underlying native parametrization and exact maximum height are the conclusions in the separate entire-native-fiber packet dated 2026-10-03. This addendum does not reclassify the source or modify it. Both analytical proofs need only bounded error in β_(M0l)=M0λl+O(1), together with the exact Pell energy and exact slope series.

The summation method is the classical generalized-divisor hyperbola / Euler–Maclaurin method. The zeta partial-sum formula is NIST DLMF 25.2.8, https://dlmf.nist.gov/25.2.E8. No literature-wide novelty claim or optimal remainder claim is made. Numerical checks are supplementary and are not substituted for universal arguments.
