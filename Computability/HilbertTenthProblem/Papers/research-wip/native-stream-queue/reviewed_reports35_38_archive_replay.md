# Exact external-cache replay for the relocated Reports 35–38

This relocation-only supplement restores four exact historical ZIP files to an
explicit external cache. It keeps the frozen scientific review and circuit
receipts replayable after their archives were removed from `docs/incoming/`.
It changes no scientific claim or frozen predecessor artifact. No archive is
extracted, imported, or executed; repository files and Git metadata are read
only.

The [helper](reviewed_reports35_38_archive_replay.py) obtains bytes with
`git cat-file blob` from the fixed commit
`7f9672c599194e150dee64ebaa0b19f0e035ba15`. Placement commits are
`216bd81e116297214f443afddc2fc6252a7767a6` and
`a51a439cdcb43701241c83fdf8d185630df0b18d`. The helper independently verifies the
current placed files; their existence is not inferred solely from these commit
messages. It does not require the current branch to remain at a particular HEAD.

## Exact archive inventory

All four paths at the historical revision have prefix `docs/incoming/`.
The total is **3,075,016 bytes**. SHA256, byte length, and the Git blob SHA1 are
checked before any output is written. Full blob identities and every selected
member pin are in the [receipt](reviewed_reports35_38_archive_replay.json).

| Archive | Bytes | SHA256 |
|---|---:|---|
| `Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip` | 1645467 | `3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d` |
| `Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip` | 423395 | `72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac` |
| `Exact_Negative_Index_Obstruction_for_Positive_Diophantine_Interfaces_Package.zip` | 501623 | `018b960efd8069db99ec3eaa9b691cb2ca60edbc88932cc6e37cbf3562d169f9` |
| `Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip` | 504531 | `e5abfdbfbbc9c203bdfafb040cba7f8c280af8b031b02103c989aeb97e085277` |

This is exactly the four-report supplement, not an inventory of all incoming
ZIPs or a replacement for the earlier
[23-archive replay helper](reviewed_report_archive_replay.md).

## Selected member-to-source correspondence

The helper reads 24 explicitly named ZIP members as inert bytes. Each member's
size and SHA256 are pinned. Every declared current match is additionally checked
by direct byte equality, not merely by comparing two filenames or trusting a
relocation manifest. There are **17 new-placement matches, five existing-source
matches, and two archive-only context members**, covering 21 distinct current
files. Duplicate ZIP member names are rejected.

The common placed-report prefix is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/`.

| Historical member group | Current byte-identical destination |
|---|---|
| Report35 `evidence/composition/PROOF.md` | `canonical-diophantine-certificates/22-literal-sandpiles-evidence-composition-PROOF.md` |
| Report35 `evidence/composition/prism_certificate.py` | `canonical-diophantine-certificates/code/22-literal-sandpiles-evidence-composition-prism_certificate.py` |
| Report35 `evidence/loader/LOADER-PROOF.md` | `canonical-diophantine-certificates/22-literal-sandpiles-evidence-loader-LOADER-PROOF.md` |
| Report36 `evidence/real/PROOF.md` | `canonical-diophantine-certificates/23-real-sandpiles-evidence-real-PROOF.md` |
| Report36 `evidence/real/real_certificate.py` | `canonical-diophantine-certificates/code/23-real-sandpiles-evidence-real-real_certificate.py` |
| Report36 `evidence/real/approved_base/prism_certificate.py` | The identical Report35 placed prism source above |
| Report37 `evidence/EXACT-OBSTRUCTION.md` | `fixed-universal-polynomials/15-neg-obstruction-evidence-EXACT-OBSTRUCTION.md` |
| Report37 `evidence/independent/INDEPENDENT-REVIEW.md` | `fixed-universal-polynomials/15-neg-obstruction-evidence-independent-INDEPENDENT-REVIEW.md` |
| Report38 `README.md`, `Research_Report38.tex` | `periodic-turmite-first-revisits/README.md`, `article.tex` |
| Report38 source-packet `PROOF.md`, `complexity-review.md`, `review.md` | `periodic-turmite-first-revisits/source-packet-PROOF.md`, `source-packet-complexity-review.md`, `source-packet-review.md` |
| Report38 boundary-context `proof.md`, `source-audit.md` | `periodic-turmite-first-revisits/source-packet-boundary-context-proof.md`, `source-packet-boundary-context-source-audit.md` |
| Report38 source-packet `one_visit.py`, `observations.py` | `periodic-turmite-first-revisits/code/source-packet-one_visit.py`, `code/source-packet-observations.py` |

Report37's two pinned context notes,
`evidence/context/RAW-POSITIVE-REDUCTION.md` and
`evidence/context/PRIOR-INDEPENDENT-REVIEW.md`, are not relabeled as newly
placed files. They remain accessible in the restored exact archive. Five
additional Report37 `evidence/sources/` members are checked against the existing
frozen files in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:

- `complete74_negative_index_refinement.md`
- `complete74_nonlinear_index_projection_scout.json`
- `complete75_half_binomial_compiler.md`
- `complete75_positive_elimination.py`
- `review_complete74_nonlinear_index_bootstrap.md`

This is a byte-level compatibility check. It neither extends the scientific
review scope of the cited intakes nor revalidates archived mathematical tests.

## Cache and write behavior

`--repo-root` must be the actual Git worktree root. `--output-root` names the
external cache; the four ZIPs are written below its `docs/incoming/` directory.
The cache may neither lie inside nor contain the worktree, Git directory, or
common Git storage. The optional receipt output must also remain outside
protected repository storage. Parent-traversal output paths are rejected.

Output ancestors are opened through directory descriptors with `O_NOFOLLOW`;
output leaves also use `O_NOFOLLOW`. A new file uses exclusive creation. An
existing regular file is accepted only if its complete bytes already equal the
requested bytes; it is not rewritten. A differing file, directory, or symlink is
rejected. All archives and current-source matches, all destination preflights,
and the optional exact expected receipt are checked before materialization.
No source-tree symlink bridge is needed because the frozen affected helpers
already accept separate archive locations.

The helper uses explicit exceptions, so optimized Python retains the guards.
Its scope assumes an ordinary stable filesystem; it does not promise an atomic
multi-file transaction under storage failure or hostile concurrent directory
renaming.

## Replay commands

For example, with the actual repository at
`/home/codex/.codex/worktrees/2a71/Proofs`, first restore the cache. The following
commands run from any working directory, including `/`:

```sh
replay_repo=/home/codex/.codex/worktrees/2a71/Proofs
replay_wip="$replay_repo/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue"
replay_cache=/tmp/reports35_38_cache
python3 "$replay_wip/reviewed_reports35_38_archive_replay.py" --repo-root "$replay_repo" --output-root "$replay_cache" --expect "$replay_wip/reviewed_reports35_38_archive_replay.json"
python3 -O "$replay_wip/reviewed_reports35_38_archive_replay.py" --repo-root "$replay_repo" --output-root "$replay_cache" --expect "$replay_wip/reviewed_reports35_38_archive_replay.json"
```

These commands use the installed WIP helper and receipt; the external cache
location remains explicit. To generate a new matching receipt, `--output /external/path/receipt.json` may
replace `--expect`; an existing differing receipt is rejected too.

The three frozen affected receipts can then use their existing interfaces,
without modifying their source or pins:

```sh
replay_archives="$replay_cache/docs/incoming"
python3 "$replay_wip/sandpile_shared_arithmetic35_36.py" --repo "$replay_repo" --incoming "$replay_archives" --expect "$replay_wip/sandpile_shared_arithmetic35_36.json"
python3 "$replay_wip/review_sandpile_shared_arithmetic35_36.py" --root "$replay_wip" --incoming "$replay_archives" --expect "$replay_wip/review_sandpile_shared_arithmetic35_36.json"
python3 "$replay_wip/review_exact_negative_obstruction37.py" --repo "$replay_repo" --archive "$replay_archives/Exact_Negative_Index_Obstruction_for_Positive_Diophantine_Interfaces_Package.zip" --expect "$replay_wip/review_exact_negative_obstruction37.json"
```

Report38's scoped intake is prose, not a receipt-replay helper. Its pinned
original members are preserved in the fourth cached ZIP and matched as above.

## Checks performed for this supplement

The writer authenticated all four archive blobs, all 24 selected members, and
all 21 distinct current files. Fresh normal and optimized exact-receipt replays
from `/` both passed, including materialization into a new optimized-run cache. A separate new CLI guard harness passed
15 rejection cases: protected repository/cache intersections; symlink cache,
ancestor, archive, directory, or receipt paths; non-directory cache and
non-regular archive destinations; differing existing archives or receipts;
repository-contained receipt output; a type-mismatched expected receipt; and
parent traversal. It also verified fresh optimized materialization, normal
idempotent replay, and preservation of existing file bytes and modification
times. The harness is supplementary validation, not an imported runtime
dependency or a scientific theorem checker.

Root independently restored a fresh external cache and obtained exact saved-receipt
PASS results from all three affected frozen helpers: the sandpile author, its
independent reviewer, and the Report37 negative-index intake. Those were runs of
the three existing bounded research helpers, not archived programs. The archive
resolver itself does not invoke them. Their unchanged receipts remain the
scientific evidence; this supplement establishes replay compatibility.
