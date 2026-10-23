# Provenance and scope

This packet is a technical proposal prepared with ChatGPT for Vladimir
Reshetnikov's ProveIt repository at revision
cbf94cb552a3b49509e0eee80e7455d4eb5974c6.

The accepted K215 machine, its source program, numerical calculus, compiler,
runtime constructions, semantic model, and existing formal proofs remain
the work credited in the repository. Inherited notices credit, within their
respective scopes, Mira and ProveIt, Elliot Glazer, Jeff's Busy Beaver/Rocq
reference, Andrew James Wade, BusyCoq, and the Coq Library of Undecidability.
The unchanged K215 and K217 notices, inherited license texts, and relevant
small provenance documents are retained under licenses/.

The guarded-image/native Replacement idea is already present in the
collection-first and native-replacement proposal packets. Positive simulation
and its extraction occur in the existing implementation and proof-core packet.
Reachable-suffix induction is suggested in further-interface/report.tex.
The present contribution implements current-source adapters, separates the
actual import boundary, checks components, records source metrics, and
specifies a concrete Rocq runtime-sharing plan.

The production overlays and exact source snapshots contain existing ProveIt
code as well as the stated changes. The sparse tables in Support215217.v
are generated from the pinned repository inputs. This packet does not
claim authorship or discovery priority for those inherited constructions.

New report, scripts, and proof additions are provided under the project's
MIT No Attribution terms in LICENSE. Existing third-party terms remain
those supplied by their original authors; this statement does not relicense
inherited components.

Checks and reviews in this packet were performed within this ChatGPT
collaboration. They are not an external human endorsement. The report and
component READMEs distinguish fresh component checks from the unperformed
literal K215 integration build and from historical full-machine evidence.
No smaller-state theorem, unconditional nonhalting claim, or new internal
PA/ZFC derivation is asserted.
