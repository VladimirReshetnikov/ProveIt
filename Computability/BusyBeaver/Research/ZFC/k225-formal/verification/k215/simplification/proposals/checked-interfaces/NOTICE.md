# Attribution and scope

This research packet was prepared for Vladimir Reshetnikov's ProveIt project
against commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

The accepted K215 construction, numerical calculus, source correspondence,
register compiler, model calibration, and original formal proofs are inherited
from ProveIt and its credited contributors. In particular, the inherited chain
credits Elliot Glazer's K/K230 work, Jeff Ketchersid's busy-beaver formalization,
Andrew James Wade's compiler ancestry, BusyCoq, and the Coq Library of
Undecidability. Their notices and licenses are retained with the Rocq sources.
The root LICENSE applies to new material under the project's MIT No Attribution
terms and does not relicense third-party components.

The lookup-coverage design is already present in the maintained Lean
`RMBisim.lookupC_all` theorem and was identified for Rocq in the earlier
`guarded-core` and `sharing-interfaces` research packets. This packet completes
a current normalized Rocq component and records its concrete checks; it makes
no discovery-priority claim for the general principle.

The Lean patch changes five proof bodies using existing lemmas. The current
source census is static analysis. Component compilation and recursive checker
results have the exact scopes described in report.pdf and the component READMEs.
No full K215 binary-machine/ZFC endpoint rebuild or internal PA/ZFC derivation
is claimed by this packet. The literal machine is unchanged.
