# Attribution and scope

The compact K theory, K230 machine, and K230 Rocq development are credited to
Elliot Glazer and the contributors identified by the pinned
`elliotglazer/k230-rocq` repository.

The original compact set-theoretic source and 254-state construction are
credited to Mira-Cult; the reference Rocq development to Jeff Ketchersid and
contributors; and the inherited compiler framework to Andrew James Wade.

The ProveIt contributors supplied the preceding reductions, source and
consistency calibration, symbolic induction machinery, and equational packet
foundations. The transfer-plus-one and delayed-erasure ideas used here are
inherited from those reductions. The pinned 235-state archive is retained
byte for byte with its notices.

This delivery contributes the concrete K228 transfer and composition, portable
construction and verification interfaces, independent audits, report, and
K-specific portability findings. It does not claim historical priority for
the inherited optimizations or global minimality.

`verification/kernels/runtime_engine.py` and `runtime_support.py` are minimal
extractions of the ProveIt induction engine and support. Retained ASTs and
entry-label specializations are recorded in `receipts/engine_port_audit.json`.
That receipt records earlier source hashes; the source archive is included.

The discovery versions `verification/kernels/symbolic_runtime.py` and
`independent_runtime.py` are preserved byte for byte for the historical receipt
hash checks. Their legacy command-line entry points are inactive in the portable
replay; use `reproduce.py` and its documented verification drivers.

The upstream K230 attribution file is retained as
`upstream/k230/THIRD_PARTY.md`. Its license-scope statements continue to apply;
this delivery does not assign a blanket license to upstream material.
Preserved notices are in `licenses/`. New report and code material in this
delivery is offered under the retained ProveIt MIT No Attribution license.

The separate E639 experiment retains its own attribution and inherited code.
It is not a component of the K228 proof.
