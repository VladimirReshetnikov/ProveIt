# Stable placement-snapshot replay for Reports 35–38

This successor keeps the four original Reports35–38 archives replayable after
editorial changes to the published turmite manuscript. It authenticates placed
members at their **original placement commits**, while continuing to check five
existing frozen research sources in the current worktree. It leaves the earlier
[replay trio](reviewed_reports35_38_archive_replay.md) unchanged.

Upstream commit `c2fe5f03ba0f708362d972849dfb39b0d8784b9b` rewrote the published turmite `README.md` and
`article.tex`, and added an `article.pdf` outside the audited member inventory.
The earlier helper correctly rejects the two changed current-byte matches.
This new helper does not relax those pins or accept the edited bytes: it
compares the original archive members with their exact original Git placement
blobs instead. The current published README, article source, and PDF are not
read or pinned by this receipt. No claim is made here about their mathematics
or their identity with the reviewed originals.

## Immutable inputs and precise correspondence

The [new helper](reviewed_reports35_38_placement_snapshot_replay.py) reads the
old [JSON receipt](reviewed_reports35_38_archive_replay.json) as inert inventory.
Its required SHA256 is
`73f427c5bd74ea00e1aea1af40b550404346eecb08adf52606094cee471c623c`.
The old Python is neither imported nor executed. The new source embeds the
reviewed guard implementation, copied from predecessor Python SHA256
`09af8babf9c1a68b33b42374c475b473939613a5ccbc01f85ef2453ab9554d69`.
This is source provenance, not a runtime dependency on that Python file.

The archive source commit remains
`7f9672c599194e150dee64ebaa0b19f0e035ba15`. All four exact archives, sizes,
SHA256 pins, Git blob SHA1 pins, and selected member identities are inherited
from the authenticated inventory. They total **3,075,016 bytes**. The helper
checks these values anew rather than trusting the predecessor's PASS status.

There are 24 named members, divided as follows:

| Member category | Verification performed now |
|---|---|
| 17 originally placed members | Direct byte comparison against placement Git blobs, covering 16 distinct `(commit,path)` pairs |
| Five embedded frozen-source members | Direct byte comparison against the existing five current WIP sources |
| Two Report37 context members | Pinned archive-member hash and size; no current or placement-file claim |

The placement revision is exactly
`216bd81e116297214f443afddc2fc6252a7767a6` for Reports35 and36, and
`a51a439cdcb43701241c83fdf8d185630df0b18d` for Reports37 and38. This includes
Report36's approved base prism source, which is byte-identical to the Report35
source already placed at the first commit. Every historical path is read with
`git cat-file blob COMMIT:PATH`; no checkout or repository mutation is needed.
The [new receipt](reviewed_reports35_38_placement_snapshot_replay.json) records
`placement_commit` and `placement_path` explicitly for each historical match,
so these cannot be mistaken for current-file comparisons.

The five remaining current matches, in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`, are

- `complete74_negative_index_refinement.md`
- `complete74_nonlinear_index_projection_scout.json`
- `complete75_half_binomial_compiler.md`
- `complete75_positive_elimination.py`
- `review_complete74_nonlinear_index_bootstrap.md`

Their source identities still have to match exactly. The two archive-only
notes remain `Research_Report37/evidence/context/RAW-POSITIVE-REDUCTION.md` and
`Research_Report37/evidence/context/PRIOR-INDEPENDENT-REVIEW.md`.

Thus the receipt is stable under unrelated editorial HEAD changes, provided
these five frozen current sources and the three required historical commits
remain available. It intentionally does not record hashes of current edited
publication files. The fixed original ZIPs preserve all original members,
including members outside this selected 24-member audit.

## External cache and strict write behavior

The four archive names and cache layout remain unchanged:
`EXTERNAL_CACHE/docs/incoming/NAME.zip`. Every archive is checked for exact
size, SHA256 and Git blob identity; every selected member is checked for size
and SHA256. Duplicate ZIP names are rejected. ZIP entries are read as bytes
only: nothing is extracted, imported, or executed.

The repository argument must be the actual Git worktree root. The cache must
neither lie inside nor contain the worktree, Git directory, or common Git
storage. Receipt outputs must also remain outside that protected storage.
Parent-traversal output paths are rejected. Directory-descriptor traversal and
`O_NOFOLLOW` prohibit following output ancestor or leaf symlinks. New files
use exclusive creation. Existing regular files are reused only when their
complete bytes already match; differing data is never overwritten.

All immutable inputs, historical/current member comparisons, destination
preflights, and optional expected receipt are checked before materialization.
No source-tree bridge is created. The explicit exceptions remain active under
optimized Python. As before, this is not an atomic multi-file transaction under
storage failure or hostile concurrent directory renaming.

## Installed replay commands

Run from any working directory, including `/`:

```sh
replay_repo=/home/codex/.codex/worktrees/2a71/Proofs
replay_wip="$replay_repo/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue"
replay_cache=/tmp/reports35_38_snapshot_cache
python3 "$replay_wip/reviewed_reports35_38_placement_snapshot_replay.py" --repo-root "$replay_repo" --output-root "$replay_cache" --inventory "$replay_wip/reviewed_reports35_38_archive_replay.json" --expect "$replay_wip/reviewed_reports35_38_placement_snapshot_replay.json"
python3 -O "$replay_wip/reviewed_reports35_38_placement_snapshot_replay.py" --repo-root "$replay_repo" --output-root "$replay_cache" --inventory "$replay_wip/reviewed_reports35_38_archive_replay.json" --expect "$replay_wip/reviewed_reports35_38_placement_snapshot_replay.json"
```

Without `--inventory`, the old JSON is sought beside the new helper, with the
same strict hash check. `--output /external/path/receipt.json` can replace
`--expect`; an existing differing receipt is rejected. The receipt contains
this new helper's own SHA256 and is type-exactly compared on replay.

The same unmodified scientific helpers can use the recovered archives:

```sh
replay_archives="$replay_cache/docs/incoming"
python3 "$replay_wip/sandpile_shared_arithmetic35_36.py" --repo "$replay_repo" --incoming "$replay_archives" --expect "$replay_wip/sandpile_shared_arithmetic35_36.json"
python3 "$replay_wip/review_sandpile_shared_arithmetic35_36.py" --root "$replay_wip" --incoming "$replay_archives" --expect "$replay_wip/review_sandpile_shared_arithmetic35_36.json"
python3 "$replay_wip/review_exact_negative_obstruction37.py" --repo "$replay_repo" --archive "$replay_archives/Exact_Negative_Index_Obstruction_for_Positive_Diophantine_Interfaces_Package.zip" --expect "$replay_wip/review_exact_negative_obstruction37.json"
```

Report38's scoped intake is prose, with original pinned files preserved in the
fourth cached ZIP and their original placement identities verified above.
Neither the resolver nor the cache changes that intake's scientific scope.

## Checks performed

The writer authenticated all four blobs, all 24 members, all 17 historical
matches, and all five current frozen sources. A new CLI harness passed 16
negative guards, including all predecessor output-path/no-overwrite cases and
rejection of a changed frozen inventory. It verified fresh optimized cache
creation, normal idempotent replay, and unchanged existing file bytes and
modification times. This harness is supplementary, not a runtime dependency.
Fresh normal and optimized exact-receipt replays from `/` both passed, including
a fresh optimized-run cache.

Root independently materialized a new cache after the editorial merge and
successfully replayed all three affected scientific receipts against that
cache. It also confirmed that the old frozen helper still rejects the changed
current turmite README before creating a fresh cache. The new successor is a
change in which immutable versions are compared, not a fallback accepting
mismatched current proofs. No scientific conclusion, new operation bound, or
archived verifier run is claimed by this relocation helper.
