# A source-aware 225-state composition

This packet constructs a two-symbol deterministic Turing machine with **225 working states, 450 transition rows, and one distinct halt**. Its canonical start state is 0, halt is 225, and dispatcher is 83. It is an ordinary mathematical extension of the pinned K226 construction in `baseline226/`. The inherited ZFC consistency interpretation and its qualifications are documented in that immutable baseline. This packet does not claim a fresh Rocq kernel build.

## Reproduction

Python 3.10 or newer, standard library, assertions enabled:

    python3 -B reproduce.py --output-dir /tmp/k225-quick
    python3 -B reproduce.py --full --output-dir /tmp/k225-full

The first command replays the pinned baseline in quick mode, reconstructs all final machine/source artifacts, checks the all-tape local fold and complete blank startup, audits the stored final runtime case array, and runs a separately implemented whole-source/local-fold/canonical-startup audit with three rejected tamper controls. The second also freshly rederives every one of the 6,656 unbounded final instruction cases. Add `--full-baseline` to freshly rederive the inherited K226 runtime proof too. Output must be outside this packet.

## Exact final files

- `results/k225.tm`: canonical table, SHA256 `f5d69a16a0324c69c8c6c407dbf18abcccf0e2d2a2283d5101ebc4591964140c`
- `results/candidate225.tm`: legacy labels, start95/halt254, SHA256 `6aab1f0f98b3764ba43c05bd6aad0d6d77a7dbac576ab733c8b02664b4b04fc2`
- `results/candidate225.klabels.tm`: original K labels, start0/halt254, SHA256 `0847184fa05327daefa45c7012ce2c75fe58bf03d1dc930fe152e9fac55b4fbc`
- `results/sites225.json`: complete final source, SHA256 `86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b`
- `results/renumbering225.json`: complete bijection
- `results/construction.json`, `local_fold225.json`, `startup225.json`, `runtime225.json`, `runtime225_cases.json`: distinct proof obligations

## Construction

All labels here are original K labels. Start from the pinned 226-state 49-atom-layout construction. Its extra208→76 fold uses state152 as a decoder helper, while the other 226-state construction suggests using152 as the retained host for a final split-entry fold. These savings cannot simply be added: the helper roles have to be reconciled.

Apply four closed source reassociations:

1. Right rotation169/136.
2. Right rotation170/169.
3. Left rotation169/154.
4. Right rotation159/118.

The complete ordered instruction list and full guarded source graph are checked after each rotation, by both arithmetic successor and independent interval/ancestor resolvers. The final source has 5,121 leaf occurrences, 211 DAG nodes, maximum depth38, and maximum zero run6. The existing CB callback repairs remain in the pinned table; the rotations only edit pure decoder rows.

These rotations expose helpers159 and170. The new final fold merges zero-tagged229 into one-tagged152 with rows152/0=0L159 and152/1=1L170. A checked inductive bit invariant establishes the preceding one at152 even for the left-moving76/0 arrival. Both folded branches are exact positive one-to-three-step whole-tape simulations. The final table removes original labels79,140,175,208,229.

The complete blank startup takes409,835 steps and reaches the same dispatcher/head and exact351-one tape as the baseline; every other tape cell is zero. Universal runtime independently covers all nine natural registers, both decrement guards, arbitrary natural extra gap and first spare, and an arbitrary finite remaining spare list. Positive affine durations and whole-tape endpoints are derived symbolically, not sampled.

## Provenance and licensing

`baseline226/` is an unchanged copy of the supplied `k230-transfer-20261019` proof bundle (excluding Python bytecode caches). See its attribution and licenses. `tools/verify_state_fold.py` is copied byte for byte from the supplied `k-transplant-research-20261019` bundle; its attribution is retained beside it. New work consists of the four-rotation composition, final fold, exact replay adapter, and accompanying receipts. Nothing in this packet was published by this task.
