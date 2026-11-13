# Protected quotient search for the combined 197-state layout

This search targets the experimental [combined negation and MP
layout](../../source-search/negation-mp197/README.md), which has 197 working
states, 3,573 source sites and 4,641 symbolic primitive cases. It found **no
smaller machine**. Its local search constraints and the sampled follow-up do
not give a state-count lower bound or prove a PA-consistency equivalence.

[`replay.py`](replay.py) pins the exact combined native table and source tree,
and the incoming `pa_consistency_research_2026-11-13.zip` containing the
MIT-licensed symbolic executor and quotient-search programs. The combined
source/table derivation is described in its sibling README. The replay imports
the archive's executor unchanged, runs all primitive cases and exact blank
startup, and collects 12,759 distinct partial tape windows from their observed
symbolic transitions plus the 58,154-step startup. A `-1` cell is unknown,
not an assertion that a particular bit occurs on the blank run. The replay
checks the serialized contexts against their pinned SHA-256.

The archive's protected quotient family deletes one state, retains another,
and redirects targets of the deleted state. The final two rows at the retained
state may be inherited or synthesized, depending on the selected mode. The
search tests symbolic windows for each merged state with an at-most-71-step
positive block and exact projected control, head and tape at each boundary.
It rejects a candidate on a read from an unknown cell or outside the
seven-left/three-right window. The engine's protected states and any deletion
that would redirect a protected state's outgoing row are excluded. This scope is
narrower than arbitrary Turing-machine compression.

The inherited-or-one-synthesized-row screen tests 45,745,616 choices. The
bit-preserving left/left two-row mode tests 561,872,416 choices; the other 15
write/direction modes test 5,363,641,920 choices across four partitions. None
passes. These are choices within the archived algorithm's protected and
prefiltered family, and can represent duplicate tables. The replay compiles and
runs the archive's C++ searches and checks every count and empty result.

As a separate exploratory sample, candidate generation treats unknown reads
and window exits as inconclusive instead of automatic failures. It additionally
protects every state visited during the original startup, selects at most one
candidate from each pair, and stops after 2,000 sampled pairs. The selection is
deterministic and pinned by hash; it is **not an exhaustive search**. The
unchanged symbolic executor rejects each sampled candidate on a primitive
contract. Source cases whose baseline execution visits either changed state
are tried first; any candidate passing them would be run against every case.
A checker failure can mean an unsupported symbolic step; it is not necessarily
a concrete counterexample and need not show a difference on the blank run.

From the repository root, with Python 3.10+ and a C++17 compiler:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/negation-mp197-quotients/replay.py --output /tmp/combined197-quotients.json
```

The command extracts the pinned small archive and builds binaries in a
private temporary directory. It runs six C++ jobs concurrently and checks the
result against [receipt.json](receipt.json); elapsed time depends on the host.
The inherited executor uses Python assertions, so the wrapper rejects `python -O`.
The executable symbolic verifier is not an independently checked proof kernel. Finding a 196-state quotient here would still require another state
reduction and proofs connecting startup, source, machine and PA.
