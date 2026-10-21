# DR215 — direct transfer with a reparameterized sixth axiom sampler

This packet contains a concrete binary, one-tape Turing machine with 215
working states and 430 transition rows. It combines the accepted ST215 direct
single-guard transfer with a local rho6 parameter change. The sixth AX slot
now emits `Ex_A(Q_A B) -> B`, instead of `Ex_A(Q_A C) -> C`. Each row family
ranges over all natural arguments, so the numerical axiom family is unchanged.
The accompanying repaired compiler and exact source/runtime/startup bridge
give the inherited ZFC-consistency equivalence for this exact table.

No 214-state machine or new proof-assistant kernel endpoint is claimed. The
two component ideas are acknowledged predecessor work. The newly checked
composition is not a rooted state renaming or reflected copy of any of 84
distinct 215-state graphs in the pinned corpus.

## Replay

Python 3.10 or newer and its standard library suffice; assertions must be enabled.

```sh
python3 -B verify.py
python3 -B verify.py --runtime
```

The first command takes about a second and checks exact reconstruction,
all source control edges through two independent resolvers, complete native
and dense blank prefixes, the 177-step source-prefix match, the inherited
3,728-node propositional recovery certificate, saved runtime metadata and
every frozen graph comparison. The second command additionally rederives all
6,151 universal whole-tape primitive contracts and compares each fresh case
record with the saved evidence. It takes about two minutes on the development
machine. Both commands write results into a fresh temporary directory; use
`--work PATH` to choose a new output directory.

## Exact conventions and files

`machine/dr215.native.tm` uses native start 0, dispatcher 84 and halt 254.
`machine/dr215.tm` uses working labels 0 through 214, start 0, dispatcher 81 and
halt 215. Halt is not counted as a working state. Blank is 0 and every move is
one cell left or right. The tape is infinite in both directions.

`source/dr215.sites.json` contains 4,732 ordered primitive leaves; the tree has
201 distinct hash-consed subtrees, maximum depth 44 and maximum zero run 6.
`checks/rebuild.py` applies the exact two transition changes and four source
operand changes to the pinned ST215 parent. All 215 counted states are reachable
in the directed transition graph from start.

`proofs/DR215_calibration.md` explains the all-natural changed-row argument,
repaired sixth-row compiler and exact dirty-tail bootstrap bridge.
`evidence/` contains complete saved runtime case metadata and replay receipts.
`comparison/` contains 84 frozen graph representatives and the 321-occurrence
provenance manifest. `references/` and `licenses/` retain predecessor theorems,
calibration, source attribution and licensing.

The actual blank startup takes 70,506 transitions to source ordinal 58, with
logical vector `[1,0,0,0,0,0,0,18,0]`. It matches a partial AX execution above
tail 2; its completion supplies ten theorem heads, while the infinite schedule
requires only two heads of conservative protection. Historical tail 4/ordinal 55
examples in inherited references are not used as the DR215 startup certificate.

The universal runtime replay proves 6,151 guarded cases using 1,618,678 symbolic
rule applications. It covers all 430 transition rows, and the minimum affine
duration constant is 5. These are ordinary symbolic induction proofs, not
bounded simulations of register values or a proof-assistant theorem.
