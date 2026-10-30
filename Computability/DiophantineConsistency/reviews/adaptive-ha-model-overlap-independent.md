# Independent HA/model object-overlap observation

Root peer `/tmp/adaptive-ha-model-overlap-7i29g2br` **PASS** as a read-only observation and produced the same complete result hash as the author scan: 119 common project object paths, of which 118 have unequal SHA-256 hashes. Every common path, both resolved provider paths and both hashes are preserved in the result. The scan rehashed both provider states and all observed objects after collecting the inventory.

The three-file `adaptive-ha-model-overlap-independent-evidence/FILES.json` manifest has SHA-256 `700332a32612358c3d57b438a15d45681f59f0f9dc6519a0001d0ce8073b20ef`. Differing bytes do not establish semantic inequivalence; they prevent assuming that either full overlay preserves the other's recorded object boundary. No overlay was combined or changed.
