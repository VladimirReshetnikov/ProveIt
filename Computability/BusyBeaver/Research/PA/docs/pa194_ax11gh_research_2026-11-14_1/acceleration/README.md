# Exact physical accelerations

This directory belongs directly inside the AX11GH/GHS research packet.
It adds two 194-state machines with the same source programs and exact
halting equivalence to their respective parents.

| Machine | Parent | Source outcomes | Blank initialization | Saved initialization steps |
|---|---|---:|---:|---:|
| PA194AX11GHF | PA194AX11GH | 4,778 | 57,870 | 52 |
| PA194AX11GHSF | PA194AX11GHS | 4,774 | 57,712 | 56 |

Both change only native rows `26/1` and `101/0`. Each changed step executes
exactly three parent steps. A three-clause tape invariant follows directly
from the finite incoming-transition graph, independently of the source
calculus or register encoding. This proves the relative iPRA halting and
nonhalting equivalence, with absorbing-clock bounds
`H_parent(t) -> H_fast(t)` and `H_fast(t) -> H_parent(3*t)`.

Read `acceleration_proof.pdf` for the complete argument; its editable source
is `acceleration_proof.tex`. The proof has been rendered and visually checked.
The absolute PA consistency calibration is supplied separately in the
enclosing report and its cited written proof. No new end-to-end Lean theorem
is claimed here.

## Reproduce offline

From the enclosing packet root:

```bash
python3 acceleration/build_fast.py --full
python3 acceleration/check_literal_fast.py
```

Alternatively pass `--packet /path/to/AX11GH-packet` to both scripts.
The first checker verifies all structural guard hypotheses, twelve local
three-to-one identities, all source outcomes, exact whole blank initialization,
and step-by-step synchronization with the parent throughout initialization.
The second imports the enclosing independent literal checker, reconstructs
the four list-sweep lemmas from the rows, resolves the source graph in two
independent ways, and repeats every source outcome without importing the
construction compiler or an arithmetic-box oracle.

Complete tables are in `machines/<name>/machine.tm` and
`machines/<name>/machine.native.tm`; the dense tables start at 0 and halt at
194, and the native tables start at 74 and halt at 254. Exact label arrays,
source arrays, finite guard certificates, hashes and verification receipts
are supplied beside them. Independent literal results are in
`independent_results/<name>/`.

For standard TeX Live installations:

```bash
cd acceleration
pdflatex -interaction=nonstopmode -halt-on-error acceleration_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error acceleration_proof.tex
```
