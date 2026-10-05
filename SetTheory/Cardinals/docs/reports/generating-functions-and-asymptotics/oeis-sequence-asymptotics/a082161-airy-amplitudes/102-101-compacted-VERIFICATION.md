# Mathematical verification and reproducibility

The compacted argument uses the relaxed Jacobi spectral, localization, drift, and boundary-kernel estimates stated in Lemma 3.1, with complete proofs in the supplied private companion. The compacted proof itself retains the signed three-level recurrence; it never assumes a positive or contractive memory operator.

The principal logical checkpoints are:

1. Exact elimination of odd times, with the exceptional first row and actual upper supports preserved
2. Global gauged-memory bounds of order 1/n and 1/n², including the region where the Jacobi edge tends to zero
3. A comparison-derived O(n^(1/4)) initial norm estimate, followed by the sequential perpendicular and scalar bootstraps
4. Cancellation of the scalar 1/(4n) drift into a delayed difference, yielding absolutely summable increments
5. Boundary smoothing of signed forcing through the relaxed propagator and use of the already-published lower bound only after the endpoint estimate
6. A forced signed-memory bootstrap and compatible constant-one carriers with exact ghost boundary, all-lag cutoff control, and global residual O(n^(-(D+3)/3))
7. An all-order forward expansion with one amplitude, followed by mean-value and finite Newton inverse estimates

The exact scripts validate finite algebra and coefficient computations using explicit exception gates. They are run in both normal and optimized Python. Both modes must reject ten compacted negative cases and 53 formal-package negative cases. The scripts and declared finite coverage are reproducible; none is a substitute for the analytic proof.

The PDF is rebuilt from a fresh archive extraction. Every final page is rendered and visually checked for clipping, overlap, missing glyphs, and equation layout. The fresh rebuild is compared with the released PDF by extracted text and rendered pixels. A release record states the actual results and hashes after those checks finish.

The numerical value approximately 173.12670485 is quoted from earlier work. Neither that value nor the archived higher-precision extrapolations have certified error intervals in this package. The asymptotic inverse cutoffs are eventual, not effective finite guarantees. No summability or exponentially small sector is established.
