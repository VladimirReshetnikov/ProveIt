# Independent final review

The standalone article is mathematically approved at TeX SHA256 `0f7bd4823e017932e9538c9a6837a8fe386c353c2619161fe607cc8cd97048f9`. The reviewed delivered PDF has SHA256 `ca3f2b816ee1018c8ca9e1a4b81a6ea0c2495a955d686c6dd31c083d6ca852c9`.

## Approved scope

- Real stability of signed physical monomers for a role-graph cover with at most two selected tail roles and two selected head roles, allowing overlapping physical cover sets and arbitrary nonnegative independent role activities
- The exact support identities for every subset of the four balanced cross-core arcs, all twelve arbitrary-class Rayleigh square identities, and the physical-copy merge without double use
- The rank-two matroid free-product corollary with the correct factor order
- Negative real roots and actual-degree ultra-log-concavity of the support polynomial, including degree loss at zero activities
- The elementary gamma-expansion root transfer for any integer N at least twice the actual support degree; no geometric identification is assumed

The argument remains an ordinary mathematical proof with explicitly cited external stability theorems. The finite checks are supplementary. No statement about every degree-four preorder, proof-assistant formalization, or literature-wide priority is inferred.

## Independent portable replay

A separate copy of the staged package was verified without access to producer executables. It passed all 20 pinned proof/audit/checker hashes, all 12 exact formal-moment identities, and all four Hall-based monomer checkers: 4,845 type multisets and 14,535 activity-weighted identities per core pattern, totaling 58,140 identities. The copied verifier ran successfully in 7.796 seconds. Detailed outputs are in `independent_verification.json`.

The README correctly states Python/SymPy/GNU C++17 requirements, rejects disabled assertions, distinguishes exact finite checking from arbitrary-size proof, and explains portable translation of historical provenance paths. The build script contains no machine-specific TeX paths. Final PDF visual inspection and ZIP checksum/extraction checks are separate producer responsibilities; this review does not substitute for them.
