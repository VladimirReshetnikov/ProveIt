# Reuse b: four saturated-Pell equations with one fewer multiplication

This separate extension removes the private L=k(T+alpha) multiplication
from each sealed saturated-Pell equation and rebinds its sole consumer
to the existing b=cTR register. Its profiles are91/283,92/278,
97/258 and98/254 (operations/exact degree). The complete literal source,
whole fixed tuples, every parent-row map and degree checks are included.
No canonical page or frozen parent is modified by this packet.

PROOF.md proves b>c,k,|R| before the transport sign, using the existing
first/strong/auxiliary root meanings and unconditional mask estimate.
Then u<b/Delta and rho<2b/mu² make negative transport impossible with
W=1+g*b. A fresh positive canonical n uses the parent's explicit auxiliary
growth bound and the new nonnegative Wt. No monotonicity of the new weight
relative to the old k(T+alpha) is needed.

The full normalized rational remainder now has degree6; its cleared
numerator has degree19. All parent formal center defects have degree17
or greater, so the complete nonzero global leading forms and exact
degrees remain unchanged. These are global polynomial proofs, supplemented
by four independent exact univariate replays and actual source bindings.

The primary four JSON files retain the entire calibrated compact44 BFS
tuple. INDEXED_BINDING.json retains the separate WHOLE indexed tuple and
all four payloads. The sealed parent's free-port/native composition applies
to both instances jointly; their different K constants and native words
are never identified. The one-gate transformation is coefficient-uniform.

SOURCE_PINS.json authenticates every whole sealed parent member and all
inherited source files. CUTS.json accounts for every parent row, exactly
one removed multiplication and exactly one rebound consumer per graph.
parents/ contains complete copied parent graphs, ordinary proof and seal.
Copied source/ papers and REVIEWED_INCOMING_VERIFICATION records describe
the92-operation parent and are retained as provenance. They do not claim
to verify this new source. New evidence is BUILD/CHECK/ARTIFACT_CHECK in
normal and optimized modes. Neither builder nor checker imports any
incoming program or parent program.

    python build.py --check
    python -O build.py --check
    python check.py --output /tmp/reused-b-check.json
    python -O check.py --output /tmp/reused-b-check-optimized.json
    python artifact_checks.py --output /tmp/reused-b-artifacts.json
    python -O artifact_checks.py --output /tmp/reused-b-artifacts-optimized.json

The closed MANIFEST.json pins every member except itself. Peer review and
any canonical-page promotion are separate root tasks. Lean remains paused.
