# Actual C222 append: independent peer review

26 October 2026. **PASS; no source correction requested.** I independently
read all 252 main lines, 40 check lines, root's author receipt and complete
driver, the actual replacement/parser modules, the complete Foundation PRF
module, the used Seq lookup/append contracts, and the actual EnumPerm
command/pack/decode definitions before replay. Root authored this packet;
I authored earlier WordPerm222 and StepPerm222 dependencies, so this is
independent review of the new append leaf, not independent authorship of
every prerequisite. I did not modify any frozen source or cached object.

The history parameter is exactly the fixed right word. History index zero
contains that word, while raw index z constructs the append result for the
shifted left pointer z+1. The successor uses tailValue z directly, without
a second subtraction. tailValue z≤z puts its child inside the already
constructed history of length z+1. Sequence validity and older-entry
preservation yield lookup at every internal i≤left; outside that interval
the actual total znth definition returns zero. This proof does not replace
internal indices by external finite lists.

The exact successor equation and the unconditional raw replacement laws
justify right-zero identity and associativity by definable internal IΣ1
order induction. The arguments left/middle/right are in the stated order;
the other inputs stay fixed while left decreases to its decoded tail.
Empty-result characterization preserves the distinction between empty
shifted word zero and raw command zero (NIP).

The finite adapter separately quantifies over every actual EnumPerm.Cmd
list, using pack NIP/DROP/MP/AX and AX's actual y-before-x layout. It proves
list concatenation for these shifted encodings; it is not a command-run
composition or scheduler theorem. The source graph witnesses are unbounded,
and unique Σ1/Δ1 graph totality is proved in every stated IΣ1 model. The
closed IΣ1/PA totality proofs use classical arithmetic completeness, openly;
they are not new HA proofs or consistency equivalences.

The independent driver derived the full import closure from current source
headers, including implicit Init, and matched all 117 cached modules,
95 Foundation modules, 402 existing artifacts and 38 explicit external
boundaries. No metadata normalization was needed. It rehashed the frozen
author summary and all sixteen author bundle members, inherited provider
records, current source/object companions, explicit external records, exact
toolchain/package files, and compiler. The 660 distinct pins were checked
before and after both fresh runs; no cached client imports a fresh leaf.
This inherits the recorded authenticated prerequisite scope; it is not a
fresh replay of those 117 modules or a whole-package audit.

Both fresh private builds passed on their first independent attempts with
Lean4.32.0, -M6000 -j1 -DElab.async=false and the 512MiB reserve guard:
main 8.777 seconds, checks 2.158 seconds. Main diagnostics were empty.
All sixteen reports contain only propext, Classical.choice and Quot.sound.
Both objects are byte-identical to the frozen author objects. The observed
cumulative child maximum RSS was 1,832,692KiB. Outputs are new nonsymlink
files under `/tmp/command-appendperm222-independent-sgx7fc0j/lib`; only
prerequisites are read-only symlinks. No dependency/Foundation compilation,
shared-object overwrite, or Git action occurred.

Exact main source:
`4ef6b31415ec97e066390f082b50e363ff23454ae1d48545a657f0491c7a962b`.
Checks:
`72c66f0695da31a423dc7321c72e0445966fa543e5afb3c8ff2aecf4bd97f5dd`.
Main/check objects:
`2a6436ad01d68aeb488a411165190d114df6b06a3025c62af87829d7e3e5dac1` /
`cd5bbea253d022f6c13309ae8326f3c5e930290a0710af6f85205d09e3e498a4`.

The [peer replay summary](arithmetic-command-appendperm222-peer-replay.json)
is `807b51f71a37be1e7c65a32e6bd223386d80189653ab71d4a616bcc6dfae6626`;
the [twelve-file manifest](arithmetic-command-appendperm222-peer-replay/FILES.json)
is `4d8820889e0e4b189280548e60106f0d5dfab1bfad136b089f1e442101ef16f2`.
The frozen author evidence retains its earlier check-only raw-zero
simplification failure and exact initial check bytes, distinct from the
final accepted pair. There were no independent preflight or compiler
failures. Execution decomposition, compiler/proof invariants, scheduling,
actual 215 simulation, and the final HA equivalence remain separate work.
