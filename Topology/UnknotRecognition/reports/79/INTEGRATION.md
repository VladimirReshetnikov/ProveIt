# Integration and reproducibility

The package includes a self-contained `repro/fast` tree, the selected native
`repro/reports` and `repro/synthesis` dependencies needed by inherited tests,
and an exact file manifest. Python bytecode caches and transient reproduced
directories are omitted.

The native baseline is ProveIt commit
`8188525b70033dcfe7c51ea5ae2c8723ad0c0198`.
`integration_manifest.json` classifies each payload file as **native unchanged**,
**incoming absent addition**, or **new report addition**. The incoming additions
are the 89 files recorded by the trace-search baseline overlay; existing native
files were preserved exactly. `provenance/native_prerequisites.json` records
the exact contents required of all 749 supplied native dependency files.
One incoming test, `tests/test_normal_ray_blocks.py`, has an explicit
compatibility adaptation for the current native unit-ray shortcut and the
supported legacy orbit-query schedule. Its manifest entry records the original
incoming hash and links the compatibility note and patch. Native production
code is unchanged.

## Verify the downloaded package

From the package directory:

```bash
python scripts/verify_package.py --strict
```

This reads `SHA256SUMS` and verifies every listed file. Strict mode also requires
all non-generated files to be listed. Bytecode caches created by running tests
are ignored. The checksums establish file integrity; mathematical claims are
checked by the independent replay tools supplied in `repro/fast`.

## Preview integration

Use an existing ProveIt checkout as the destination:

```bash
python scripts/integrate.py --repo /absolute/path/to/ProveIt
```

The default is a dry run. It checks every recorded native prerequisite first,
then every package payload and destination. It prints the exact proposed file
additions. It creates no destination directories and writes no files.

## Add the files

After reviewing the dry-run result:

```bash
python scripts/integrate.py --repo /absolute/path/to/ProveIt --apply
```

The complete preflight runs again before writing. The script adds absent files,
accepts byte-identical existing files, and refuses any differing existing file.
All known conflicts are reported before any write. Native prerequisites must
already exist with their recorded contents; they are not silently reconstructed.
A later checkout can be used if all recorded prerequisites remain identical.

The destination should have no concurrent writers during integration. Files
are created exclusively, so an existing file cannot be overwritten by a race.
The script does not change branches, create commits, or update the remote.
It installs only the `repro` payload under `Topology/UnknotRecognition`; the
article and package-level provenance can be filed separately during review.

## Run the focused checks

```bash
cd repro/fast
python -m unittest tests.test_pachner_cover_search tests.test_pachner_composition -v
python -m shared_cover_research.benchmark --replay shared_cover_research/results/exhaustion.json
python -m shared_cover_research.benchmark --replay shared_cover_research/results/descent.json
python -m causal_research.composition_audit --replay causal_research/results/disjoint_composition.json --output /tmp/disjoint_composition_replay.json
```

The complete benchmark drivers, raw records, test logs, and independently
replayable certificates are retained. The article specifies which findings
are theorems, which are conditional complexity consequences, and which are
measurements on the finite fixture cohort.
