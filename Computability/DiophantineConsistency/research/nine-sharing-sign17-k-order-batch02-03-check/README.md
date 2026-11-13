# K candidate index and order batches 02–03: rows 96–223

This checked 20-stage attempt replays the independently audited pair of
Fin64 weight batches, then applies the checked order-sample proof template
for both blocks and a numeric plus actual-weight comparison at their boundary
(rows 159 and 160). Each block asserts 64 nonzero candidate indices and 63
decreasing adjacent weights. The runner pins the earlier sample audit and
checks that the new block sources match its source with names changed. Other
boundaries and blocks, actual candidate ranks, full K and external file
binding remain separate. Usual per-child resource guards apply. Author
no-Lean preflight exited 0.

Runner SHA-256:
`6b6b3822b91fea94f6483256d61b69e9b5fb011202fc77f743538e931d258cda`;
manifest SHA-256:
`6d62b5f21725f10d1ce721d2db09562232ae59a68fa1067b23a58e4af9a9f3f1`.
Order sources 02 and 03 and boundary source have respective SHA-256:
`427715e3bbcac0b4106e834fa57ce9063b1d1941f8d9a1a90577a4d4fe87840c`,
`c6eb20803f54cd64cdd0a4161f12e2d238a6f9cb8b5a9c6e6f72be174830e9c8`, and
`3acd8adb84adee86dc6a673ebfc75cfb5951f5de124d95fd77d7bc2388960451`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-batch02-03-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-order-batch02-03-terminal-independent/README.md) passed; the packet is frozen.
