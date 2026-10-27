# Actual C222 command-word tick: root author receipt

26 October 2026. Root authored this147-line main and36-line checks,
adapting the completely read generic evaluator structure of CommandTick254.
The only import is the actual new CommandStepPerm222; no old254 tick,
parser or command-step semantic theorem is imported.

The live encoding is P(word,working)+1. Evaluator0 is halt; a live word0
is successful completion, remains positive and is absorbing. A live word1
executes actual raw command0. Every nonzero internal scalar decodes without
a validity test. The exact fixed Σ1 graphs range over arbitrary IOpen
inputs and retain unbounded intermediate witnesses. Positive command
results lose their successor tag before being paired with the actual
permuted tail.

An active tick either halts or satisfies remaining(next)+1≤remaining(old).
The measure is the remaining shifted word, independent of the changing
working-state size. Its proof uses the accepted literal tail≤raw theorem;
it infers no bound on command intermediates. The Nat next-step adapter
uses the actual EnumPerm.cstep/decode for every raw code and working state.

Both leaves passed their first compiler invocations in7.609s and1.699s,
with an empty main log and thirteen reports containing only propext,
Classical.choice and Quot.sound. There were no failed preparations or
compiler runs. Pinned Lean4.32.0 used `-M6000 -j1 -DElab.async=false`,
actual source paths and new private nonsymlink outputs under
`/tmp/arithmetic-command-tickperm222-root-author-kys0hepw/lib`.
The512MiB reserve was enforced. The preflight and postchecks authenticated
107 cached current-source modules,86 Foundation modules,365 cached
artifact records,37 explicit external boundaries and515 pin observations.
Only the two new leaves were compiled; no Foundation or shared-cache
mutation occurred.

Main source SHA:
`2edee8fb7e5f5234136583ddb551222828b3c0e130415d9d76b1322e945ff348`.
Checks: `60dc46b1a94fe81b7ce628a64e601f11ffccb63aa5fb22c07f4873ee11869ce4`.
Main object: `f003db1b839446e68051c8f75beb94b4263d54090d59e80233c6be7d48966e0e`.
Checks object: `4a47f54e1d3261eee408564d839ca31a378a4ebc3cf323f27a6172403e2b5a7d`.
The [author summary](arithmetic-command-tickperm222-replay.json) has SHA
`5dda196edcae181a9d332f9a4d5b41080c15142ccdf7424c9468d64703f18f1f`;
the [nine-file manifest](arithmetic-command-tickperm222-replay/FILES.json)
has SHA `f5edcce38c7897e263645403291f25bd4bbd8db95cff32307c17b74b03d70c1c`.

The [independent peer review](arithmetic-command-tickperm222-peer.md)
read all sources/contracts and rebuilt both leaves with identical primary
objects and thirteen standard-only reports. Root rehashed its12-file
bundle and541 deduplicated input pins after reading the receipt. This
author receipt itself is not independent review.

The tick/control-measure theorem does not prove a complete word's draining
bound, scheduling fairness, compiler correctness, proof invariants,
exact215 simulation or the equation's HA consistency equivalence.
