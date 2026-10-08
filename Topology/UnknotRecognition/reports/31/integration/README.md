# Integration snapshot

The `tree/` directory contains the complete maintained Python source, tests, fixtures and required earlier reference packages at assembly time. Its paths start at the repository root. Historical benchmark results are omitted; the new measurements are provided separately in this package.

The exact baseline is recorded in `baseline.txt`. `changes.patch` contains all changed and added source/test files against that commit; `changes.stat` summarizes it, and `manifest.json` binds the patch and every snapshot file by SHA-256. No remote operation was performed.

Apply from a clean checkout of the pinned baseline:

```sh
git apply --check /absolute/path/to/integration/changes.patch
git apply /absolute/path/to/integration/changes.patch
```

Ordinary tests can also run directly in `tree/Topology/UnknotRecognition/fast`. The historical overlap benchmark additionally needs the pinned Git object, as explained in the main reproduction guide.
