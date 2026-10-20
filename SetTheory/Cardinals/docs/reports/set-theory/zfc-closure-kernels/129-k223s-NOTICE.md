# Attribution and license scope

This contribution was prepared for Vladimir Reshetnikov's ProveIt repository.
Its new prose, construction scripts and certificates use the MIT No Attribution
license in `LICENSE`. Existing third-party materials retain their original
terms; this notice does not replace or expand those terms.

The immediate predecessor is the exact 224-state research packet at ProveIt
commit `49ee7cfdc8e0364c6db3614675d141d66f9350ed`, included unchanged. That
packet retains the K225 construction and the Source 116 logical bootstrap.
The K230 source development is pinned to
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The K theory, seed reformulation, K0 quotient interpretation and consistency
proofs are due to Elliot Glazer and the attributed predecessor developments.
The proof-search and compiler architecture builds on the work credited in
the pinned packets, including Mira, ProveIt, Jeff's busy-beaver development,
Andrew James Wade, BusyCoq and the Coq Library of Undecidability.

The new use of the seed presentation as the actual emitted axiom, the
209-subtree grammar, the 223-state table and its new audit adapters are the
substance of this packet. No global priority or minimality claim is made.

`portable/verification/local_bisimulation.py` is copied unchanged from the
K224 verifier. `source_language.py` is a documented excerpt of the pinned
source-language verifier. The runtime engines and logical proof dependencies
are used directly from the unchanged predecessor archive. Its manifests,
provenance and file-level license notices are retained, including the notices
for MIT, MIT X11, MIT No Attribution and MPL2.0 components. No new
repository-wide license is asserted for upstream files with unspecified
licensing.

The original formal endpoint belongs to the pinned K230 machine. The new
223-state result has an ordinary mathematical proof and executable
certificates; it does not claim a newly compiled proof-assistant endpoint.
