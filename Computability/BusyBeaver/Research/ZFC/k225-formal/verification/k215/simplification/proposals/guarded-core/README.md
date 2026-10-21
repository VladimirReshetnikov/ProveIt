# K215: guarded proof core and certificate refinements

Review cutoff: `aa66d0a33f1f8237a348899eb8095b045a502832`, 21 October 2026.

Start with **report/report.pdf**, the seven-page review, or its editable
**report/report.tex**. This is a new, independently sealed review package; it
does not replace or modify the two earlier simplification releases.

## Main result and limits

- The 1,426-vertex source checkpoint graph contracts first to the received
  367-vertex affine core, then to a new **189-vertex guarded arithmetic core**:
  188 tests and one halt. The second contraction removes 174 triangular loops
  and four conditional-clear loops. These are proof-graph vertices, **not 189
  Turing-machine states**. The accepted machine remains K215. For the current
  identical source graphs, direct normalized equality or the existing compiled
  1,426-entry route remains the first choice; the guarded core is a research
  alternative, not an established shortest-proof replacement.
- The zero-counter branches are essential. Checked path suffixes cover the
  removed vertices, avoiding separate rank and entry-path certificates.
  `affine/NEW_LOOP_PROOF.md` and `guarded_review/REVIEW.md` state the mathematical
  contracts and remaining formalization assumptions.
- Certificate refinements include a positive-address trie, concrete marker
  data checks, and zero-credit/lowering corroboration. Existing Lean M124/FM215
  transfer theorems are not presented as missing or newly proved; the remaining
  integration boundary is explicitly separated.
- The checked packet's decoder evidence concerns internal prefix behavior,
  not a complete primitive-semantics theorem or a new ZFC endpoint.
- Incoming compiler logs and receipts are preserved and their source bindings
  audited. They are **recorded evidence, not compiler runs performed here**.
  New formal proposals are uncompiled. The included finite Python checks are
  not Lean/Rocq kernel proofs or measured proof-assistant speedups.
- The intake commit adds three ZIP files only. Production is unchanged from
  the reviewed `0359ebda60aaf52758358e1450a04988136db67e` phase-five baseline.

## Reproduce the bounded review

With Python 3.10 or newer on a POSIX-compatible system, unset `PYTHONOPTIMIZE` and run:

```sh
python3 -I -B verify_release.py --negative-controls
```

For byte-integrity checks only:

```sh
python3 -I -B verify_release.py --hash-only
```

The verifier first checks a SHA-256-pinned manifest and the exact file set. It
then runs only seven explicitly named, owned Python checkers in a disposable
copy from an unrelated working directory. Every declared regenerated output
must match the archived bytes; no other input may change. The original package
is checked again before success. No received script, shell build, proof
assistant, package manager, or network command is executed. See PORTABILITY.md
for the full allowlist and trust boundary.

## Contents

- `affine/`: received affine packet as data, source pins, new guarded core,
  zero-counter counterexamples, mathematical review, and owned reconstruction.
- `guarded_review/`: separate literal-data verifier, arithmetic and path review,
  loop bindings, suffix certificates, and relocation/rejection evidence.
- `refinements/`: complete received certificate packet as data, owned audits,
  positive-trie artifact and uncompiled coverage draft, current interface notes.
- `checked/`: complete received simplification packet as data, receipt audit,
  decoder-prefix replay, pinned comparison sources, and portability controls.
- `report/`: the reader-facing PDF and TeX, plus QA and source-binding metadata.
- `downloads/affine.zip`: exact original archive required by the independent
  verifier; it is only hashed and read as data. Nested archives required by the
  received affine manifest are likewise data-only.
- `licenses/`: preserved attribution and third-party notices.
- `SOURCE_BINDING_INDEX.json`, `SOURCE_PIN_CHECKS.json`: portable source and
  intake bindings; `OUTER_NEGATIVE_CONTROLS.json`: deterministic rejection result.
- `MANIFEST.json`, `verify_release.py`: sealed payload inventory and verifier.

The complete received-manifest trees are retained, including proof source,
receipt logs, compressed search evidence, and historical program text. Only
unmanifested caches, compiled build debris, redundant run logs, bulk report
renders, and unnecessary duplicate outer archives are omitted. Received text
may contain historical build commands or claims; it is not the execution
allowlist and does not override the scope stated here.

`STAGING_SELECTION.json` records copied and intentionally omitted source files.
The affine `FINAL_FREEZE.json` is the author's original tree receipt, including
its omitted redundant stdout log; the release inventory is `MANIFEST.json`.
