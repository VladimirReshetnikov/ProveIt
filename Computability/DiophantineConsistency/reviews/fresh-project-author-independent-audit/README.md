# Independent audit of the historical AQ29 author artifacts

`audit.py` passed with actual session 67627 exit 0. Its [receipt](receipt.json)
has SHA-256 `d21db65b29de29614976a3f32e42a1f44d8ddad60b30e5894abb473cfb5e9bcf`.
The independent pass checked all 1,210 ordered source files, output objects and
logs; 1,212 recorded Git blobs including configuration; 4,766 direct input
occurrences; 13,150 guarded companion paths; and 1,540 Foundation artifacts.
It checked the four exact endpoint report names and permitted Lean metatheory
axioms, not just a report count. The audit also binds the preserved observation
of `author exit 0`; it does not observe the Foundation wrapper's outer exit.

Run at idle I/O priority, for example `ionice -c 3 nice -n 19 python audit.py`.
The script rate-limits bytes read for hashing and refuses to overwrite its
receipt. It checks files at observation points, not transient changes between
them. It does not replay Lean, validate unobserved package-transitive or dynamic
ancestry, or establish a matched peer result. The parent records 15 workspace
source drifts, so the proof snapshot is historical.
