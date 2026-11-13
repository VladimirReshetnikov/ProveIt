# Restoration of the P64 package's pinned sources

On 2026-11-04 the P64 `positive14` package was missing 34 of the 40 paths
listed in its `SOURCE_PINS.json`, including `native/COEFFICIENT_BINDING.json`
and the four compressed coefficient payloads. The six existing pinned files
already matched. The original absence observation and retained-payload
comparison are recorded in the [companion note](README.md).

[`restore.py`](restore.py) verified each pin's historical `commit:path`,
Git blob ID, and SHA-256 against the local Git object database before writing.
It then created the 34 missing paths exclusively, without overwriting the six
existing files. [`restoration.json`](restoration.json) lists the restored
paths, hashes, Git modes and sizes. A second invocation found all 40 files
already present and exact, and wrote none. The script refuses optimized Python;
it may be run from the repository root, requires the pinned historical Git
objects, and refuses mismatching or symbolic-link package paths.

The existing package `verify.py` was run on an isolated temporary copy of
all 40 restored package files, plus its current JSON and verifier. It exited
0: all 40 source hashes and four compressed payload hashes matched, all 83
live graph operations were checked, the external degree certificate gave 30,
and its generated `CHECKS.json` was **byte-identical** to the previously
committed package receipt. The output is retained as
[`restoration-verifier-output.txt`](restoration-verifier-output.txt) and the
hashes and scope are in [`restoration-verification.json`](restoration-verification.json).
The separate updated provenance checker also passed after restoration; see
[`observation-after-restoration.json`](observation-after-restoration.json).

Six restored historical blobs contain an extra blank line at EOF. The default
`git diff --check` reports those lines; checking with only `blank-at-eof`
disabled passes. Their bytes are intentionally preserved to match the pins.

This restores the package's referenced external artifacts and reproduces its
finite checks. It does not prove inside Lean that the compressed payloads or
JSON encode the symbolic ports, interpret a PDF, authenticate the inherited
Lean provider ancestry, or independently prove ZFC consistency.

```text
fea76d250b55c7a4af19057319d6f416e46979256167c6063972259be797db32  restore.py
583cc7273f31b0c0ca95304422da0042c921a09752de324b3581526d41c09c81  restoration.json
557d35d87dd5881e42abc4ed60859e99043eb832a35da76646223af0184fbd55  restoration-verification.json
3dabc7a5da56f0e8c04bac2cbecd91bf691a771572c68256e0f39113c8eef7b8  restoration-verifier-output.txt
```
