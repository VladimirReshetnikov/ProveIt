Independent literal-table verification
======================================

Run with Python 3 and assertions enabled (do not pass -O):

    python3 -B verify_all.py --literal

Or, to write new receipts directly into the working machine directories:

    python3 -B verification/check.py machines/PA194ORHF machines/PA194ORHBF

The checker and the adjacent vendor/ directory may be moved together. They use
only the Python standard library and contain no absolute paths or imports from
the construction code. A machine directory must provide these six files:

    machine.tm
    machine.native.tm
    labels.json
    sites.json
    instructions.json
    receipt.json

receipt.json must include startup.steps. Successful checking writes a separate
independent/ directory containing contracts.json, list_lemmas.json and receipt.json.

The checker verifies complete deterministic 194-state binary tables, native/dense
conjugacy, two independently implemented source successor resolvers, four generic
list traversal lemmas derived from the literal rows, every source instruction on
arbitrary primary register values and an arbitrary nonempty finite spare list,
and the complete blank startup up to the specified seed frame. No arithmetic
box oracle is imported. The header gap is an arbitrary natural affine variable.

These finite symbolic certificates and their elementary induction interpretation
are executable mathematical evidence. They are not a proof-assistant kernel and
do not independently establish the inherited Hilbert proof compiler or its PA
consistency calibration.

Provenance
----------

Copied without semantic changes from VladimirReshetnikov/ProveIt at commit
43d9041f5571936c45c583f7f9d7f6eed9e0fd84:

Computability/BusyBeaver/Research/PA/docs/
pa194_loop_continuation_research_2026-11-14/verification/check.py

and its vendor/ directory. The generic symbolic implementation in that packet
in turn states its provenance in its module docstrings. This README is new.

The checker reports an explicit scope string in its receipt, and leaves complete
per-outcome affine durations, literal row sets and list lemmas for further audit.
