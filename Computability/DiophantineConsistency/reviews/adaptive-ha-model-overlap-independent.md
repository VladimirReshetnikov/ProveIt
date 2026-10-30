# Independent HA/model object-overlap observation

**Inventory correction:** `Path.rglob` did not traverse symlinked namespace directories in the HA overlay. The 119 compared paths and their hashes remain valid observations, but the counts and difference total are incomplete; they do not cover all shared project objects. In particular, symlinked BusyBeaver, FirstOrder, PAHF and other namespaces require a separate symlink-aware audit. See [the scope correction](adaptive-ha-model-overlap-scope-correction.md).

Root peer `/tmp/adaptive-ha-model-overlap-7i29g2br` **PASS** as a read-only observation and produced the same complete result hash as the author scan: 119 common traversed object paths, of which 118 have unequal SHA-256 hashes. Every common path, both resolved provider paths and both hashes are preserved in the result. The scan rehashed both provider states and all observed objects after collecting the inventory.

The three-file `adaptive-ha-model-overlap-independent-evidence/FILES.json` manifest has SHA-256 `700332a32612358c3d57b438a15d45681f59f0f9dc6519a0001d0ce8073b20ef`. Differing bytes do not establish semantic inequivalence; they prevent assuming that either full overlay preserves the other's recorded object boundary. No overlay was combined or changed.
