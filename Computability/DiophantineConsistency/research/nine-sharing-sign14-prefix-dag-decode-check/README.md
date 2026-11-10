# Decode five fragment-DAG rows: guarded author result

Five compiled stages prove depth checks and parser-reflection decoding of each
composed short-fragment byte list into the actual staged Lean row, for arbitrary
ports. The 20-stage audited composition provider, sources, objects, logs and
outer receipt are pinned. Its embedded fragment bytes were checked by its own
terminal audit; the relation to the original prefix/JSON files remains an
independent external check, not a Lean theorem. The author run and [independent terminal audit](../../reviews/nine-sharing-sign14-prefix-dag-decode-terminal-independent/README.md) passed. Limits are `-M3600`, 120 seconds
per child, 4-GiB sampled RSS, 10-GiB host available-memory floor and 5-GB disk
precheck. Inherited point-in-time and failed-parent qualifications remain.

Author [no-Lean preflight](preflight.json) exited 0; [Independent prelaunch review](../../reviews/nine-sharing-sign14-prefix-dag-decode-prelaunch-independent/README.md) passed; the allocated Lean run passed with outer session 13345, numeric exit 0 ([receipt](attempt01/outer-result.json)).
