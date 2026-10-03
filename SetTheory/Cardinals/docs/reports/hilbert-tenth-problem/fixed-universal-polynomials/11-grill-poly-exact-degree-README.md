# Exact degree: portable extension

The **same pinned universal Grill polynomial has total degree 69,339,973**, when all six external coordinates and 797,135 witnesses have degree one. The historical 71,731,007 upper bound remains valid and is larger by 2,391,034. No circuit gate, coefficient, input or residual was changed.

Read `frozen/DEGREE_PROOF.md` for the complete unrestricted first-norm cancellation identity, the full highest homogeneous component and the exact nonzero diagonal-ray coefficient. `frozen/independent-review/INDEPENDENT_LEADING_PROOF.md` gives a separately implemented symbolic/raw-source verification. The proof is about this fixed polynomial; it is not a minimum-degree claim or an independent universality theorem.

## Offline replay

This extension uses Python 3.10 or newer on Linux and only the standard library, including `resource`. Keep it next to the original `reproducibility/` subtree. The full DAG is **not duplicated**: both new local checkers read the existing `../reproducibility/frozen/arithmetic/` data. The entire historical subtree is checked against its original inventory anchor before and after replay. No network, source checkout, private working directory, upstream executable or third-party package is needed.

From any current working directory, replace `/path/to/release` by your extracted release location:

```sh
python3 -B /path/to/release/exact-degree/replay.py --verify-only
python3 -B /path/to/release/exact-degree/replay.py
python3 -B -O /path/to/release/exact-degree/replay.py
python3 -B /path/to/release/exact-degree/test_integrity.py
python3 -B -O /path/to/release/exact-degree/test_integrity.py
```

A complete degree replay usually takes under a minute and uses at most 512 MiB per checker. Each checker has 180-second CPU limits and periodic wall-time checks; the runner imposes a 210-second subprocess timeout. No giant coefficient or full multivariate expansion is materialized. The modular checker propagates two compact arrays over all 3,600,546 gates; the independent checker also verifies the leading form symbolically in 23 sparse monomials in its named base form and coordinate atoms.

To retain regenerated receipts and logs, add `--work-dir /path/to/an/empty/directory` outside the entire release. The default is a fresh temporary directory, removed after success. Delivered files are not modified. The local checker entry points require an explicit `--output` outside the entire release; the replay runner supplies this and the sibling data route automatically.

## What is verified

1. Exact extension file/directory inventory, hashes and original/delivered provenance
2. Byte identity of the complete historical `reproducibility/` subtree, using its frozen inventory anchor
3. Original pins for the full DAG, scientific JSON and 67-row native kernel
4. The first-norm identity as exact sparse coefficient-dictionary equality on independent indeterminates
5. Cancellation-aware degree bounds for the complete source and all 86 residuals
6. Degree 69,339,973 with leading coefficient 3 modulo 17 and 53,942,795 modulo 1,000,000,007
7. A separately implemented raw-source check of the full leading form, all 794,976 Shat coordinates and the uniquely largest residual square
8. Exact equality of regenerated scientific certificates with both frozen normal and optimized-Python certificates; only local checker hashes and timing/resource measurements are excluded from these comparisons

The diagonal-ray coefficient is exactly

−2^148 (2^551891 · 794976)^23113311.

It is nonzero. Either modular residue independently suffices to certify that the degree bound is attained; this is deterministic, not a probabilistic identity test.

## Evidence and integrity

- `frozen/`: all 15 frozen research packet files, with every original Python source retained inert as `.py.txt`; original file contents are byte-identical
- `replay_code/`: the two newly authored independent local checkers, with output-location safety adaptations only
- `PROVENANCE.json`: separately records original and delivered byte sizes/hashes, original Git-blob hashes, filename changes and executable adaptations
- `PORTABILITY.md`: the precise scope of the packaging transformations
- `INVENTORY.json`, `INVENTORY.sha256`: exact extension inventory and local root digest
- `test_integrity.py`: adversarial mutations, missing/extra files, extra directories, symlinks, stale caches, false certificates and in-release output rejection

`frozen/MANIFEST.json` describes original research names and hashes; `.py` names there map to inert `.py.txt` names through provenance. Original certificate checker hashes likewise describe original checker bytes. They are never relabelled as hashes of adapted executable code.

The extension inventory is a local corruption-detection anchor; the externally supplied release/ZIP hash anchors the distribution. It cannot authenticate a maliciously replaced package together with a replaced anchor. The mathematical theorem follows from the proof and the checked arithmetic, not from a hash alone.
