# Additional source-control experiments

These are source optimization experiments, not certificates of a smaller
Turing machine. They preserve every primitive effect and guarded ordinal
control-flow edge before invoking an exploratory incremental compiler.
Changes to an apparently pure decoder state can also change an arithmetic
routine, so source equivalence and decoder binding do not establish the
runtime semantics of the resulting table.

The scripts use the pinned modules in the sibling `../encoding/` directory.
They need Python 3, with assertions enabled. No network access is required.
By default generated results go into `generated/root_work/` under this
directory. Set `ROOT_RESEARCH_WORKSPACE` to a separate scratch directory to
choose another location.

```sh
python3 -B control_rotation219.py --depth 1
python3 -B increment_commute219.py
python3 -B reset_bound219.py --rounds 30
python3 -B audit_checkpoint.py
```

`control_rotation219.py` rotates binary source association trees, preserving
primitive order and retargeting structured break/continue levels. Both
independent full guarded-graph resolvers check saved sources.
`control_rotation_fast219.py` proves equality of local open control outcomes
before using a subtree rotation in context; it also rechecks the whole graph
before saving a proposed size improvement. `reset_bound219.py` uses that
local rule to try to lower the maximum run of zero bits in a program code,
which could permit a shorter reset marker. Even a successful source bound
would still need a new machine implementation and full reset proof.

`increment_commute219.py` swaps adjacent increments of different registers
only when no other guarded edge enters the second instruction. It considers
all seven nonempty combinations of the three identified disjoint groups.

`receipts/` records completed and explicitly partial searches. The fast
general rotation search was interrupted by resource exhaustion after four
completed rounds; it is not reported as a completed search to its requested
depth. The reset-directed search checkpoint has its actual completed round
count recorded. Beam selection depends on Python set iteration and is not
claimed deterministic across hash seeds; exact candidate identities and
independent graph verification are the relevant reproducible objects.
The checkpoint auditor reconstructs each retained source from its saved
rotation chain and checks both complete guarded graphs against the original.
This audit is independent of the beam's order and selection decisions.

No search in this directory established the requested 218-state result.
