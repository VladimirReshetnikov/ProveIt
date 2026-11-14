# Unified PA194 source-step: coherent machine-specific rebuild

This is a staged source rebuild of the entire machine-specific dependency
closure of `PA194UnifiedSourceStepSentence`, starting from the previously
source-built startup/header baseline. It extends that baseline in a **single
fresh output**, without a machine-specific fallback overlay. The existing
baseline is a prerequisite: this wrapper does not rebuild or independently
revalidate its startup proof, dense certificate, parent startup, or general
logic foundations. For a fully reproducible audit those prerequisites must be
created first with the repository's coherent startup and header rebuilds and
their documented retained project/foundation/Lake objects.

The input baseline must be the pinned header-coherent manifest
`24cb6eca676a5a6d74c4ac4a96b4d611b618c907f6b9a698f21a62c088640cc4`.
That manifest records 155 source-built header-extension modules and explicitly
lists its own preexisting startup modules. The wrapper checks those 155
recorded source hashes against the current repository. It rejects symlinks,
then creates independent byte-verified copies of all baseline objects and
records their SHA-256 hashes in `baseline-object-receipt.json`; this confirms
copy integrity, not that preexisting baseline objects were independently built
from the claimed source. No baseline file is modified or removed.

`build-unified-coherent.py` follows the exact imports of
`PA194UnifiedSourceStepSentence`, stops at objects in that copied baseline,
and rebuilds every missing machine-specific source in dependency order into
the same output. It records source hashes and preexisting imports, detects
source changes and refuses overwritten or symlinked objects. Before staging,
the wrapper rejects PA19*, M6, packed machine, configuration, table and
`PRAEquality` object roots in fallback search directories. The only fallback
roots are the supplied general project/foundation objects and ordinary Lake
paths; they remain precompiled and are not independently authenticated by this
wrapper. Missing optional Lake search directories are ignored.

The target and key correspondence theorems are audited for `sorryAx` and
required axiom printouts. Source/object pinning does not itself establish
transitive provenance. `nativeIPRA` remains a finite step for the source site
25 instruction with a canonical input, chosen clock and output; it is not a
proof of either direction of consistency versus nonhalting.

From the repository root, choose a nonexistent output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-unified-coherent.sh \
  "$PWD" \
  /dev/shm/pa194-header-coherent/hardlink-baseline \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-unified-coherent/build
```

The baseline and output paths above are session-local. For a fresh run use a
new output path. The checker rejects inherited Git internal environment
variables and does not set them. The external baseline manifest's pinned hash
contains the original source-build roots, so reproducing it bit-for-bit outside
this session requires preserving that manifest or deliberately changing the
pin after separately auditing a newly generated baseline.

The staged rebuild on 2026-11-14 passed all 60 newly compiled modules and
the named native equality audits; the output manifest SHA-256 was
`d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944`.
