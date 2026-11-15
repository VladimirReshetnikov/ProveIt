# PA194AX11GDHR: a bootstrap-safe history-recovery companion

This supplementary construction has **194 working states**, not 193. It
implements the same source calculus as PA194AX11GDH with a different physical
control graph. Its exact relative halting and nonhalting equivalence has a
written iPRA proof in `proof.tex`; no new compiled Lean endpoint is claimed.

The transformation deletes native control 301, identifies it with 88, and
introduces helper 3000. Its rows are `0 R 122` and `1 R 3000`; row 88/read0
becomes `0 L 3000`. Native register marker 51 remains unchanged. The four
parent-state/read cases execute in 3, 1, 5 and 1 child steps. The incoming
guards follow directly from the literal parent transition graph, on every
tape when starting in control 74.

The local simulations give constructive clock bounds:

- Parent halting by time t implies child halting by time 5t.
- Child halting by time t implies parent halting by time t.

The proof composes these finite blocks using primitive recursion and
quantifier-free induction. It transfers the parent's absolute arithmetic
calibration; it does not assert a separate PA-proof compiler for this table.

## Reproduce

Run with Python 3.10 or later, without `-O`:

```
python3 build_helper.py --output /tmp/PA194AX11GDHR-fresh
```

Only Python's standard library is needed. The builder pins its included
parent table by SHA-256, checks all local guards and four full-tape identities,
checks all other rows, and synchronizes every parent step through the complete
initialization prefix. It reconstructs dense/native tables, label bijection,
local certificates, startup tape and a fresh receipt.

The child has 388 rows, dense start 0, terminal label 194, a two-way binary
tape and an all-zero initial tape. The halt label is excluded from the count.
It reaches the same clean source tape in 58,022 steps; the parent uses 57,922.

Dense-table SHA-256:

`d9ff827eed1bb6a2b0d64cb17525a7613b2d1805eef788f3ac3ccd35b1738f5c`

`PA194AX11GDHR/novelty.json` records zero matches with the 521 current
reference classes under the enclosing census's strong symmetry conventions.
`new_companion_comparison.json` also excludes matches with the new plain and
accelerated designs. The full corpus and its novelty checker are in the
enclosing comparison directory.

## Independent literal audit

The enclosing independent checker also passed all **4,778 source outcomes**
over **3,671 source sites**, using nine arbitrary primary register values,
both decrement branches, an arbitrary nonempty finite spare list and affine
tape padding. It rederives four generic list lemmas from the literal table,
uses no arithmetic-box oracle, resolves the source graph in two independent
ways, and checks the exact complete startup tape. Its 1,096,717 symbolic
updates are not a bound on literal Turing time. The receipt and contracts are
in `PA194AX11GDHR/independent/`.

This finite symbolic audit supplements the direct relative proof. The
standalone builder does not rerun it; use the enclosing package's independent
checker with the repaired machine directory to reproduce this audit.

## Files and attribution

- `build_helper.py`: standalone reconstruction and relative certificate.
- `proof.tex`: section fragment containing the written iPRA proof.
- `parent/`: pinned parent table and initialization specification.
- `PA194AX11GDHR/`: new tables, labels, local guards, traces and receipts.

The parent is the enclosing report's PA194AX11GDH construction, derived from
ProveIt's PA consistency-machine program and the attributed James Chang /
K-family implementation. The transformation and its proof are new in this
research package. The enclosing package's upstream licenses and provenance
apply to the inherited parent rows.
