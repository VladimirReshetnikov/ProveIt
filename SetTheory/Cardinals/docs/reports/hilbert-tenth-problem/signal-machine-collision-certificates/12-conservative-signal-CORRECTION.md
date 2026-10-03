# Generic packet API correction — 2 October 2026

This is a corrected reproducibility archive for **Conservative signal machines
as Diophantine frontends**. The article PDF, its TeX source, the literal machine,
and the complete numeric event data are unchanged. The original archive is
preserved separately; this archive supersedes its generic packet evaluator.

## What was wrong

The original `code/quadratic_packet.py` did not fully enforce the exact-natural
domain and dimensions declared for its generic packet API. For a one-dimensional
identity branch with a valid identity witness, `polynomial_value` returned zero
even with target `(1, 999)`, source `(1.0,)`, or an extra `(None,)` slack row.
It could also retain mutable lists inside nominally frozen mathematical records.
These were genuine validation defects, including false acceptance of malformed
calls. They should not be used as evidence that an arbitrary submitted packet is
well formed.

The correction snapshots coefficient/matrix/guard data and checks exact built-in
integer types, natural endpoint and witness coordinates, matching dimensions,
known guard kinds, and exact slack counts before evaluation. Booleans, floats,
surplus coordinates and surplus slacks are rejected. Signed integer inputs
remain supported by the algebraic `Branch.output` method. Properly shaped
natural residuals and complementarity products have not changed.

## Mathematical scope

The affected helper is the generic evaluator and small demonstration. The
literal construction and its separate numeric exporter are unchanged:

- 18 live signals, 114 meta-signals and 445 injective two-to-two rules
- 17 gaps plus one finite-mode coordinate
- 49,700 modes and 80,501 event branches
- 4,196,998 auxiliary variables and 2,762,961 affine-square residuals

The correction does not alter the finite-horizon theorem, its coefficients or
its ledger. Universality still relies on the cited source theorem. The mode
closure is an overapproximation of numerical histories, and no fixed-arity
unbounded history decoder or improved universal-operation bound is asserted.
The unique-witness statement uses disjoint event domains; arbitrary caller-made
overlapping branch families are not made disjoint by this patch.

## Verification and reproduction

The full original ten-command replay is retained in `run-replay.sh`. Run it from
this directory with Python 3.10+ and assertions enabled:

```
sh run-replay.sh
```

The new independent regression test checks all three malformed-call defects,
1,200 complete literal-formula evaluations across dimensions 1–6 and branch
counts 0–4, 72 canonical sections, 66 malformed-call rejections, immutable
snapshots, and signed branch algebra:

```
python3 correction/verify_packet_correction.py code/quadratic_packet.py
python3 -O correction/verify_packet_correction.py code/quadratic_packet.py
```

The second command verifies that the new boundary checks do not depend on
assertions. It is not permission to run the original mathematical replay with
`-O`. To additionally compare every valid test with the original released
module, unpack the original archive elsewhere and pass its module path:

```
python3 correction/verify_packet_correction.py code/quadratic_packet.py --original /path/to/original/code/quadratic_packet.py
```

The corresponding independent verification receipts and the full-replay
preservation receipt are included under `correction/`. Every original JSON
export is retained byte-for-byte. `SHA256SUMS` covers this corrected release.

## Provenance

The isolated repair is the exact patch from the
[public review commit](https://github.com/VladimirReshetnikov/ProveIt/commit/9f033fa6e4752140bac03bb7256e393378b27348),
which independently reviewed the same original archive. The patch is included
at `correction/conservative_signal_packet_domains.patch` for reference; it has
already been applied here. No external repository has been changed.

- Original archive SHA-256: `43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73`
- Original evaluator SHA-256: `94fb0aa513fc4c07860e2edab98bbb9d75fe713ed724f94e437e297a09a8666e`
- Patch SHA-256: `c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033`
- Corrected evaluator SHA-256: `96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef`
- Unchanged article PDF SHA-256: `d33d3b6fdd7ac00ac3937a400b2b6b4906a09f77e08e21e805379153520bf33e`
