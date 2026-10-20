# A separately verified alternative 219-state machine

This package records a different 219-state binary Turing machine, obtained by
reassociating the published source decoder. It does **not** improve the current
219-state count and does not claim a machine with218 or fewer states.

The construction starts from the published219 archive at ProveIt commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72`. The exact archive is included under
`portable/vendor/`; its SHA-256 is
`04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b`.

## What the package checks

`portable/build_alternative219.py` applies exactly35 literal row replacements
to the pinned published219 machine. It adds and removes no working state.
It compares the complete primitive word and both guarded successor graphs
against the published source, using the two separately implemented source
target resolvers from the authenticated K221 parent. It also checks every
internal decoder prefix using literal transitions.

The runtime driver freshly proves all6,167 primitive interfaces, including
both decrement cases. Each proof covers arbitrary natural primary-register
values, an arbitrary natural extra gap, the first spare value, and an arbitrary
finite spare tail. The certificate contains1,512,606 symbolic rules and has
minimum constant duration13. These are executable mathematical induction
checks; they are not a new proof-assistant kernel endpoint.

The startup checker runs two literal tape representations and checks the
entire resulting tape. After312,617 blank-start steps, the machine reaches
native dispatcher84 at head−5 with logical registers
`[3,0,0,0,3,0,0,0,0]`, gap80,130 spare registers equal to1, and exactly277
one-cells. Every other tape cell is zero. The second simulation uses the
canonical state numbering and also matches all transition-visit counts.

The copied published219 runtime auditor is specialized only to the alternate
artifact hashes and its symbolic-rule count. It independently rederives the
four block schemas from literal rows, checks exact guard and row coverage,
checks strictly positive affine durations, and checks dependency provenance.
The symbolic induction engine and its helper are unchanged and hash-pinned.
The parent source calculus and its relation to ZFC consistency are inherited
from the bundled published construction.

## Offline reproduction

From any working directory, with Python3 and assertions enabled:

```sh
python3 -B portable/reproduce.py --output-dir /tmp/alternative219-full
```

The output directory must initially be absent or empty. The default replays
the bundled parent construction, derives the alternate table and source
equivalence, replays complete blank startup, freshly proves the final unbounded
interfaces, and audits the resulting certificate. The paths in this command
assume the current directory is this package's root.

For a faster check of the stored final runtime certificate:

```sh
python3 -B portable/reproduce.py --quick --output-dir /tmp/alternative219-quick
```

`--full-baseline` additionally requests fresh inherited runtime proofs.
Quick mode does not rederive the final symbolic interfaces. Both modes replay
the parent construction and verify the exact checked inputs offline.

## Exact artifacts

| Artifact | SHA-256 |
|---|---|
| Native table, `machine/k219.native.tm` | `142cb09f13f336cf23330f959d5e78e4249c47a3d8f728efed7c61cc38825a11` |
| Canonical table, `machine/k219.tm` | `cce85a9adaf104ee4cbddd927a6bbb1b5b3fdf06fffb4a23b68faded169d36dc` |
| Source, `machine/sites219.json` | `e2e41a573aba9f6a763bca387900fd383a737822776b48e6a853db1714bb9adf` |
| Guarded cases, `portable/reference_results/cases.json` | `90c34e52aef9c1776b89160001d245ec470aa8e1348639c55d488ee77bede2f7` |

The table has219 working states and438 binary transition rows. Halt254 is
excluded from the native count. Canonical halt219 is excluded from the
canonical count. The source has206 distinct syntax-DAG nodes,4,744 leaf
occurrences, maximum depth38, and maximum consecutive-zero run6.

The native table/source here are the accepted alternative. Earlier research
tables without the final leaf-entry repair belong to a different exploratory
phase and are not incorporated in this package.
