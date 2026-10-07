# Frozen numerical regression fixtures

These canonical JSON fixtures contain the numerical data of the audited
precision-70 finite-core computation and its coefficient assembly:

- `core_reference.json`: the expected domain, 562-panel count and core enclosure
- `panels_reference.json`: all terminal intervals, sorted by exact left endpoint
- `coefficient_reference.json`: the full integral, positive prefactor and
  coefficient enclosures after adding the separate absolute tail bound 0.141

The public replay generates the partition from scratch, recomputes every panel
again, proves rational coverage/aggregation, and recomputes coefficient
arithmetic. Loading a fixture is never taken as proof. These data have no
external service dependency. Their canonical-byte hashes are pinned in
`certificate_io.py` and recorded with all other inputs in `PROVENANCE.json`.
The source was hardened for explicit input validation and safe offline I/O;
the expected mathematical enclosure and panel endpoints remain unchanged.
