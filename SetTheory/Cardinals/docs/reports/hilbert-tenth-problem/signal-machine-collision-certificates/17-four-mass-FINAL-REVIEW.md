# Final article review

The full 12-page article was mathematically reviewed after incorporating the independent audit's required clarifications:

- Mass at most three is explicitly dispatched before the mass-exactly-four classification
- All four-mass contacts use occupied-site proximity at most 2S
- The finite seed bound and N=4B+12S, W=N+2B are noncircular
- The previously stationary target coordinate is tagged when the packet consists of unit symbols
- At designated emission checkpoints, D>N selects the live tag even when geometric span<=W; other dispatch states use the ordinary span test first
- The final anchored-observation cutoff uses a separate index n*
- The binary example's noninjectivity is explicit
- No generic unique-witness theorem is inferred from decidability

The final PDF was inspected page by page, including the vector spacetime trace. There are no overfull, underfull, undefined-reference or compilation warnings in the final build log. The PDF has 12 letter-sized pages.

Verified PDF SHA-256:

0d1280e962e64e8e13486aaac0fae2498ac908f37feeeffba0d682df865f3f5e

The figure is a mandatory source dependency in the final build. Rebuilding after making that dependency mandatory left the verified PDF bytes unchanged.

The public exact-arithmetic helper surface was separately hardened and tested. See exact-boundary-results.json at the package root; its source hashes pin the validated implementation. These API checks are separate from the mathematical theorem and the exact conservation certificate.

The audit scripts in this directory have only their original absolute workspace paths replaced by relative paths. Their logic is unchanged, and all scripts were replayed from an unrelated working directory.
