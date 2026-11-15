# Late-HEAD supplement: no new transition graph

The primary comparison remains pinned to commit
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`: **110 recognized 194-state
classes and 86 deliveries (82 filed, four incoming)**. This supplement records
the separately audited late snapshot
`19b9ea945cc95fe25535d44d949904843f4a824a` without changing that baseline.
The late snapshot has **the same 110 classes and 87 deliveries: 86 filed,
one incoming**.

## What changed

Commit `459123aa3f` files the four already-audited incoming packets. An
independent Git-object comparison found that every one of the 869 added files
is byteidentical to its corresponding original ZIP member. This includes the
updated AX11H packet, now under `pa194_ax11h_research_2026-11-14_2`.
No other `.tm`, `.json`, or `.zip` payload changes outside these imports,
the removal of those four ZIPs, and the addition below affect the requested
source locations. The separate source/code changes continue the Lean work.

Commit `603c58ca3bd6bf3222fcfc4e308e6b079f65d573` adds
`docs/incoming/pa194_frontier_2026-11-14.zip`. That is a retrospective report
pinned to the older commit `32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.
Its two principal machines are **PA194AX11G and PA194GH**, both already
present in our baseline. It claims no accepted sub-194 machine.

The complete new ZIP was inspected as data, without executing its scripts.
The same numeric-table/explicit-JSON recognition rules as the baseline found:

| Quantity in new ZIP | Count |
|---|---:|
| Selected outer/archive payloads inspected | 420 |
| Complete one-terminal table occurrences | 116 |
| Normalized labeled tables | 110 |
| Complete spanning graph classes | 102 |
| 194-state classes | 96 |
| 193-state classes | 2 |
| 201-state classes | 4 |
| Classes absent from the baseline census | **0** |

One auxiliary positive-control literal fragment has no external halt and is
recorded separately. All 110 baseline 194-state classes also have concrete
retention witnesses at the late HEAD: 94 through an unchanged tracked Git
blob, and 16 through a byteidentical relocated archive member. Thus the equal
frontier count follows from both absence of additions and retention of all
baseline classes.

PA194AX11GH and PA194AX11GHS remain distinct from every recognized historical
graph. The offline checker compares complete tuples, allowing all spanning
roots, control renaming, reflection, global bit exchange, and ignored terminal
write/move. Global bit exchange is only a structural novelty test; it is not
asserted to preserve a zero blank tape.

## Proof chronology

The retrospective frontier report says the absolute iPRA calibration remains
open at its **older source snapshot**. That discussion does **not** assess the
subsequently updated AX11H manuscript contained in the baseline incoming ZIP
and now filed under the `_2` directory. The latter explicitly presents an
ordinary written absolute iPRA calibration. Our separate inherited-calibration
audit identifies its statements, interfaces, and proof scope; the new relative
preservation proofs use that manuscript as an explicit inherited premise.

This delta audit proves graph identities and source-file identities only. It
neither upgrades a finite replay to an arithmetic theorem nor supplies a new
Lean kernel proof. The two known 193-state inputs in the retrospective ZIP
remain runtime/startup research objects; the packet does not report an
accepted 193-state consistency machine.

## Reproduction

Place this directory beside the baseline `comparison` directory, or supply its
location explicitly. Python 3 with its standard library suffices:

```sh
python3 -B verify_latest_head.py --baseline ../comparison --receipt fresh.json
```

This verifies the manifest, reads the complete new source ZIP, redoes table
recognition, checks all 96 late-ZIP 194-state graph classes against exact
baseline representative tuples, and checks both new candidate tuples against
the new ZIP. The 193/201-state classes are matched to the baseline full census
identifiers; those historical representatives are not duplicated here. The
ZIP is inert input; no archived verifier or builder is executed.

With both Git snapshots available locally, additionally run:

```sh
python3 -B verify_latest_head.py --baseline ../comparison --repository /path/to/ProveIt --receipt fresh_with_git.json
```

The optional mode rechecks every imported file's Git identity and all 110
retention witnesses. It does not change the repository checkout. The original
baseline's own checker remains the authoritative full 110-class novelty
replay; this supplement checks only the later delta.

## Materials and attribution

`source_archive/` retains the exact new ZIP. `source_tables/` provides its
recognized literal sources and the excluded control fragment for convenient
inspection; their paths and byte hashes are in `source_table_bindings.json`.
`source_text/` retains the original README, result summary, and notices.
`packets87.csv/json` is the later delivery ledger; the baseline ledger remains
unchanged. `head_persistence.json` and `latest_delta_relocation_audit.json`
record the exact late-HEAD source identities.

Imported material retains its original authorship and licenses, including the
notices in the original ZIP. The new audit scripts and this supplement are
research artifacts produced for the present comparison. SHA-256 and Git blob
identifiers bind provenance; complete tuple comparisons establish the stated
194-state graph subset and candidate novelty claims.
