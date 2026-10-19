# Batch 171: recovery and selected finite replay

Placement `950e2f0ff6` imports all twenty queued packages as Sources 81–100 and
retires their incoming ZIPs. The [placement map](data/intake171-placement.json)
accounts for 8,564 original members: 5,999 new ancillary files, 2,384 exact
aliases and 181 archive-only manuscript/PDF/delivery README files. The latter
remain recoverable from their committed arrival archives. Standalone proof
notes, research READMEs, experiment logs and offline nested dependencies are
preserved. The eight nested ZIPs are dependency members, not eight additional
manuscripts.

Files use the host's local source number, a short topic slug, the original
member's sorted ordinal, and its basename. The map supplies every original
name and destination, including duplicate aliases. Its internal text and
relative imports still use the delivered layout. Do not run the flattened
host files in place.

From the repository root, recover all original layouts into a new directory:

```bash
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover171.py \
  --repo "$PWD" --output /tmp/intake171-recovered
```

The helper executes no delivered code. It reads the committed arrival ZIPs,
rejects unsafe members, restores every file and checks every ancillary alias
against its current maintained target. Root's [actual recovery](data/intake171-recovery.json)
passes all 8,564 members and 8,383 ancillary occurrences. Historical placement
trees were checked separately in the [history findings](data/intake171-history-findings.json);
the recovery helper's PASS concerns current bytes.

The [fresh replay record](data/intake171-fresh-replay.json) contains 39 actual
attempts: 38 passes and one preserved failure. All 38 selected jobs pass after
the documented compatibility retry. Three jobs prepare local inputs; the
remaining 35 are substantive jobs, some of which invoke several finite leaf
checks. All twenty sources are represented. These are selected finite suites,
not a claim that every optional search, inherited suite or full symbolic
runtime was freshly rerun. Source 100's already maintained seven machine
checks are reused as earlier evidence; its finite-algebra check is fresh.

The first Source 89 run failed only because Python 3.13's default AST dump
omits empty fields. The fresh and delivered JSON differed at exactly the
selected AST fingerprint. A new copied run adds `show_empty=True` at that
serialization call, restoring the exact delivered fingerprint and passing
the unchanged complete comparison and all remaining gates. Both attempts and
the independent diagnosis are preserved. The delivered loader is unchanged.

For a portable replay, use Python 3.13 or newer with assertions enabled. First
prepare a plan against the recovered layouts:

```bash
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/prepare_replay171.py \
  --recovered /tmp/intake171-recovered \
  --runner SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay171.py \
  --output /tmp/intake171-plan --work /tmp/intake171-replay
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay171.py \
  /tmp/intake171-plan/jobs.json --output /tmp/intake171-replay
```

Root ran the original four job plans plus the separate Source 89 retry. The
portable plan's preparation was checked against the complete fresh recovery;
no second full execution of that path-adapted plan is claimed. `--source N`
selects a source in both recovery and preparation. Sources 87 and 96 also
need recovered Source 91 as an inert local archive dependency.

The runner creates persistent disposable copies, clears inherited Python
optimization/path overrides, bounds each process group, records exit status
and elapsed time, and keeps stdout/stderr. Review the substantive result
JSON and logs as well as exit status. Some delivered wrappers combine child
outputs before deleting their own temporary directory; their retained
aggregate output does not become a separate raw stream for every child.

Copy-only adaptations omit bulk delivery-manifest audits in Sources 85, 93,
95 and 99, plus the Source 89 AST compatibility adjustment. Exact functional
source/table/codec identities and mathematical certificate gates remain.
No checksum normalization, discovery campaign, network download, Lean or Coq
compiler, or delivered article build is claimed. Optional and inherited
scopes are listed in the individual source notes and original manuscripts.

The [replay history](data/intake171-replay-history.json.gz) is a compressed
JSON map from recorded relative paths to base64 bytes. It preserves actual
logs, generated or changed disposable-copy files, executed root helpers,
plans, reviews and the failed attempt. Unchanged copied inputs are recovered
from the arrival archives. Its [index](data/intake171-replay-history-index.json)
lists the retained entries. The host's original article is unchanged. Delivered PDFs remain in their
arrival archives; no merged host PDF exists or is built. The catalogue
manifest is built separately.
