# Independent audit of the replacement Foundation provider

[`audit.py`](audit.py) is prepared to rehash a completed provider receipt,
its observed process exit, all pinned Foundation source/configuration files,
the full Foundation artifact inventory, direct external guards, the build log,
the overlay and all Foundation targets directly imported by the pinned AQ29
project snapshot. It additionally recomputes current namespace-first external
resolution, rather than relying on per-module search-path fallback.

The verifier [exited 0](terminal-observation.json); its [receipt](receipt.json)
records 477 source files, 1,540 Foundation artifacts, 14,764 guarded paths,
140 target objects, and all 37 direct Foundation imports in the frozen AQ29
project snapshot. It rechecked current namespace-first resolution. The
provider receipt records inner Lake exit 0 and the wrapper printed its final
`BUILT` line, but the wrapper's own exit code was not captured.

The audit is not a second Foundation build. Its checks are point-in-time and
do not establish source-to-object provenance for inherited package inputs,
exclude transient mutation, trace dynamic loads, or constitute a project proof
replay. A `receipt.json` is generated only after all checks pass.
