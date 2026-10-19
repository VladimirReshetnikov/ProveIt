# Independent audit of the newly published236-state machine

**The local237→236 fold passes an independent, pinned, whole-tape audit.** The new archive arrived in ProveIt commit `0b5fec6980cc3a5ba7dd47b404f0cbbe9a451c02` while the older237-based searches were being finalized. This folder audits that upstream construction and records one targeted attempt to reach235 states. It does not claim authorship of the236-state construction.

Run the independent mathematical-premise checker:

```sh
python code/audit_fold236.py
```

It imports no upstream proof/search module and checks:

- exact input hashes and state sets;
- all470 ordinary row equalities;
- complete incoming-row lists yielding the predecessor guards;
- all four exceptional3-step blocks, reading only the current cell and its left neighbor;
- whole-tape preservation and absence of interior halts;
- exact commutation of the previous235→98 fold with the new source rotation.

The unbounded consequence follows by mapping each old transition to a positive new block of length1 or3. It holds for every initial binary tape and every initial integer head position at state95. Source calibration and the changed source's register-machine semantics are separate obligations handled by the parent audit.

## Exact changes that enable the reduction

The first stage changes only four rows, keeping237 states:

| Row | Original237 | Reassociated237 |
|---|---|---|
|177/0|0R165|0R185|
|177/1|1R185|1R212|
|185/0|0R192|0R165|
|185/1|1R212|1R192|

These are the literal tree rotation from `(165,(192,212))` to `((165,192),212)`. In particular, it creates the direct edge177/1→212.

The second stage merges223 into182:

| Row | Reassociated237 | New236 |
|---|---|---|
|182/0|0R187|0L198|
|182/1|1R212|1L210|
|237/0|0R223|0R182|
|223/0|0R23|deleted|
|223/1|1R70|deleted|

Old182 is entered only by76/1, which writes1 and moves right. Old223 is entered only by237/0, which writes0 and moves right. The left neighbor therefore distinguishes the two old controls. Four three-step read-only blocks recover their behavior:

| Old state | Current bit | Left bit | Three successive new states | Final old target |
|---:|---:|---:|---|---:|
|182|0|1|198,136,187|187|
|182|1|1|210,177,212|212|
|223|0|0|198,206,23|23|
|223|1|0|210,114,70|70|

All four blocks move L,R,R, preserving the entire tape and ending one cell right of entry. The other470 old rows commute in one step. On the original237 table, the proposed182/1 block would end at185 instead of212; the source rotation is the specific enabling change. The old baseline's fixed-source local search classes did not allow that semantic source transformation.

## Targeted235 attempt

The archive had already searched plain folds and one neutral helper on its236 table. We additionally tested freely synthesized helper compensation on the eight common-row pairs touching the newly used source/fold controls:74/210,185/229,198/205,198/219,198/221,198/246,200/210,210/232.

The first helper must pass all merged-state profile cases before a second free helper is used to compensate its original contexts. Target254 is permitted and halted tapes/heads are identified. The search uses the archive's28,926 finite radius5 profile windows and old/new horizons65. No235-state candidate was found. Larger edits and other pairs are not exhausted; this is no lower bound.

`results/focused235_receipt.json` contains each exact command, exit code and completed counters. The final program counter `pairs228` names its entire indexed catalogue; each recipe processes one pair, as specified by its final two arguments. Replay all eight recipes with:

```sh
python code/replay_focused235.py --out /tmp/zfc236-focused-replay
```

## Pins and provenance

| Input | SHA-256 |
|---|---|
|Original237|`a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a`|
|Reassociated237|`da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724`|
|New236|`ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3`|

The new tables/profile come from `ZFC236_Construction_2026-10-19.zip`; original237/238 inputs come from the pinned earlier repository state. Inherited author credits and licenses remain those of the parent integration package. The independent Python checker and the focused helper-compensation implementation were written for this follow-up.
