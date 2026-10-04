# Portable replay of the frozen chronological matrix audit

This adapter replays the two independently authored audit checkers against the exact frozen science packet. It does not modify either input tree, and it executes no science builder, author checker, upstream program, saved accepting schedule, or Lean code. All 184,016 arithmetic gates are read as formal polynomial syntax by the original independent checker.

## Run after extracting or moving the release

Python 3 with its standard library is sufficient; no package installation, network, original `/workspace` location, or executable permission on the input files is needed. Tested with Python 3.12.14. The release can use these sibling directories:

- `science/`: the complete frozen 19-file science tree, including its manifest
- `independent_audit/`: the complete frozen 12-file independent audit tree, including its manifest
- `audit_replay/`: these portable adapter files

Supply **absolute explicit paths**. For example, after placing the release at `/home/user/chronological-report55`, run:

```sh
python3 -I -S /home/user/chronological-report55/audit_replay/replay_audit.py \
  --packet /home/user/chronological-report55/science \
  --audit /home/user/chronological-report55/independent_audit \
  --output /tmp/chronological-report55-replay-1
```

The output directory must not exist; its parent must already exist. Choose a fresh location outside the release, as shown. The adapter enforces that output is outside both immutable input trees. It never overwrites or reuses an earlier output. Paths must contain no symbolic-link component or `..` traversal. Input trees must have exactly their frozen contents: extra files or empty directories are rejected too. Keep editor backups and platform metadata outside those two directories.

Both input trees may be read-only. Do not run their original audit checkers directly in the extracted audit directory: those historical scripts write receipts next to themselves. The adapter preserves their original bytes, copies them into the new external output, and passes the packet path explicitly. The historical absolute paths in their source/report/manifest are retained as provenance, but are not used as execution fallbacks.

## What happens

1. The adapter authenticates the hard-pinned audit and science manifests, then every listed byte and the exact input inventories
2. It creates the new output only after preflight passes, and builds a read-only byte-exact science snapshot there
3. It copies the two pinned independent checkers into separate `normal/` and `optimized/` output directories
4. Each checker runs using isolated Python (`-I -S`), once normally and once with `-O`, with no stdin and a five-minute per-checker timeout
5. All four generated audit receipts must equal the frozen expected receipt bytes; a merely successful exit is insufficient
6. Input bytes, modes, modification times, identities, and inventories are checked again, and the read-only snapshot is reauthenticated
7. Only after all checks pass is `replay-receipt.json` published as the final success marker, accompanied by `replay-manifest.json`

Successful stdout is the same deterministic JSON as `replay-receipt.json`. The two core receipt SHA256 values are:

- `source-audit-receipt.json`: `128649a386d2fbd62f8218a07daa86a1477d6a83812addd7eed9a88c3e5a265b`
- `interface-audit-receipt.json`: `1091a01f3a809304b4024e22637932a35ded1c62bc8a4e24c30c246d2905d9c3`

The successful portable replay receipt SHA256 is `0473dfdb398a6f8a9aa266798d06265a5cff0e5f3c1d826178c59dd7fc8a8f1e`.

An invalid input/path fails before new output is created. A runtime failure returns a nonzero exit and may leave a partial external output for diagnosis, without the final success receipt. Pick a new output name for any retry. The adapter neither deletes failed outputs nor repairs altered science/audit files.

The static symlink checks and no-follow regular-file opens are fail-closed path safeguards; this is not a security sandbox against a hostile process concurrently replacing directories, a compromised Python executable, or a maliciously modified adapter. Verify this adapter against the enclosing release manifest. The scientific theorem retains its explicit inherited Pell and matrix-interface dependencies; replay does not rebuild Lean or reprove them.

## QA and reproducibility

`qa-receipt.json` records 28 rejected input/output/tamper/symlink cases and two successful moved, ZIP-extracted, read-only replays. The adapter itself was launched once normally and once optimized; each launch ran both independent checkers in both modes. All core receipts matched the frozen bytes, and both outer success receipts were byte-identical. Original and extracted input bytes, modes, and modification times were preserved.

To repeat the separate QA in a new external work directory:

```sh
python3 -I -S /home/user/chronological-report55/audit_replay/test_replay.py \
  --packet /home/user/chronological-report55/science \
  --audit /home/user/chronological-report55/independent_audit \
  --adapter /home/user/chronological-report55/audit_replay/replay_audit.py \
  --work /tmp/chronological-report55-adapter-qa-1
```

The QA workspace must be new and external to both inputs. Its tests mutate only freshly made fixture copies. They never execute any science/author/upstream code or stored accepting schedule. `REPLAY_QA.md` summarizes the coverage and known boundaries; `release-files.json` lists the files to copy into `audit_replay/` with their hashes.
