# Attribution and scope

This research packet was prepared for Vladimir Reshetnikov's ProveIt project.
Its new contribution is the semantic simulation interface implementation,
exact decoder/suffix attachment and checked literal example, the Rocq rendering
and numerical attachment of the maintained shared implication derivation,
component verification and source audits, and the accompanying report.

The 58-step truth-free condensed-detachment derivation is inherited unchanged
from ProveIt's `k225-formal/rho8cd/derivation_core.txt`. The representation-independent
Lean interface, exact decoder and source-binding proofs, K215 machine, numerical
calculus, compiler and runtime development, and earlier simplification proposals
are inherited work. The broad semantic-contract direction and source-certificate
mirror theorems are not claimed as new discoveries here.

Pinned project revision: `6f0d42d368506bc29c70ace1c992ed88b2651346`.
The component source pins retain individual paths and SHA-256 digests. The Rocq
numeric reference files also retain their upstream k230 source pin.

Original module headers, project terms, K215 attribution, and the applicable
inherited license notices are preserved under `licenses/` and in the component
directories. They credit, within their stated scopes, ProveIt contributors,
Elliot Glazer's K/K230 work, Jeff Ketchersid's reference verification, Andrew
James Wade's compiler ancestry, BusyCoq, and the Coq Library of Undecidability.
The root MIT No Attribution license applies to new project material and does
not relicense inherited third-party components.

The reviews here are independent task reviews within the same assistant
collaboration, not an external human endorsement. Component compilation is
reported separately from a full production endpoint rebuild. No new proof of
unconditional nonhalting, internal PA/ZFC proof serialization, proof-length
optimality, or machine-state lower bound is asserted.
