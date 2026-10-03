# Portable, offline full Grill arithmetic replay

This subtree is self-contained. Extract the release, then use Python 3.10 or newer on Linux (the resource-limited scientific checkers use the standard-library `resource` module and Linux RSS units). No network, installed package, repository checkout, symlink, upstream executable, or original working directory is needed. Allow roughly 1 GiB RAM, 250 MiB temporary disk space, and several minutes for a complete replay. The actual full 61,209,290-byte `frozen/arithmetic/universal.dag` is included.

From **any current working directory**, replace the example relative path below by the path to this extracted subtree:

```sh
python3 -B /path/to/reproducibility/replay.py --verify-only
python3 -B /path/to/reproducibility/replay.py
python3 -B -O /path/to/reproducibility/replay.py
python3 -B /path/to/reproducibility/test_integrity.py
python3 -B -O /path/to/reproducibility/test_integrity.py
```

For retained regeneration outputs, add `--work-dir /path/to/an/empty/output-directory` outside this subtree. By default all generated outputs are written to a fresh temporary directory and removed after success. No delivered file is changed. Execution fails nonzero on any failed invariant, missing file, extra file or directory, byte mutation, or symlink. Optimized Python does not disable validation.

## What the replay establishes

1. Exact package inventory, file sizes and SHA-256 hashes, and the delivered-byte side of every provenance entry
2. Reconstructed literal U15/tag/Genera source table; independent static source and bounded queue semantics checks
3. Exact 397,488-entry run table, block identities, phase alignment and first-empty cleanup tests
4. Two complete recoder interfaces and native source/streamed-backend identities, plus positive-domain interface tests
5. Independent inspection of all 3,600,546 original DAG rows and exact integer coefficients
6. Full re-emission of the DAG from the portable local generators, with byte-exact SHA-256 equality and complete scientific-manifest equality (only timing/resource snapshots and adapted local-code hashes are excluded)
7. Independent whole-DAG structural and seven full-size numerical differential checks

The exact full DAG hash is `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`. The gate count is 803,517 multiplications plus 2,797,029 additions/subtractions. The 797,135 positive witnesses are separate from six external positive coordinates. The degree 71,731,007 is an upper bound, not a proven exact degree.

The universal-language theorem remains conditional on the included pinned U15/recoder/native mathematical premises and applies to the explicitly valid fixed five-parameter program slices with ordinary positive input. Tests do not materialize astronomical complete Pell witnesses and are not a machine-checked proof of all imported theorems.

## Files and trust

- `frozen/`: preserved scientific artifacts, primary PDFs and page images, full data, proofs, source pins, and recorded reviews; **all retained original Python ends in `.py.txt` and is inert**
- `replay_code/`: only locally authored generators and independent checkers, ported as described in `PORTABILITY.md`
- `PROVENANCE.json`: original sizes, original SHA-256/Git-blob hashes, delivered sizes/hashes, and transformations
- `INVENTORY.json`, `INVENTORY.sha256`: exact delivered file and directory inventory, including replay scripts and provenance
- `test_integrity.py`: adversarial source/data/DAG/manifest, missing-file, extra-file, extra-directory and stale-cache tests

`INVENTORY.sha256` is the local root digest; the externally supplied release/ZIP hash is the distribution trust anchor. Hashes detect corruption or unauthorised single-file changes relative to that anchor. They cannot authenticate a maliciously replaced package together with a replaced root digest. Frozen historical manifests describe **original bytes**; their hashes are not silently relabelled as hashes of path-sanitized copies. Use `PROVENANCE.json` for that distinction.
