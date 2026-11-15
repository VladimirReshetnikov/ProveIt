# PA194AX11GDHS

A new 194-state composition with an eleven-entry, four-operand AX command,
explicit generalization binder `c`, offset diagonal `Gamma(d+x)`, ordinary
universal distribution, visible no-push MP, and the symmetric implementation of the cached-only halt test.

The authoritative dense table is `machine/machine.tm`; its SHA-256 is
`2d5b61572ee6e7dd19e23d7e10181c2f28410cddf0970fd145211c88ebca44cc`.
It has start state 0, working states 0 through 193, halt state 194, 388 rows, one two-way
binary tape, an initially all-zero tape and head position 0. State count
excludes halt. Native start 74 and halt 254 are kept for proof comparison.

Relative to the incoming GDHS native table, exactly one row changes:
`2068 1 0 L 302` becomes `2068 1 1 R 19`. This changes every AX execution:
the guarded gate is pushed, execution continues into the full MP field
reader, and a real fourth operand is consumed. It is a composition of
previously supplied ideas; no claim is made that the AX11 technique itself
is new. The resulting table is new against all 521 current 194-control
classes, including 520 spanning classes and the disconnected diagnostic.

## Replay

Use Python 3.10 or later and its standard library, with assertions enabled:

```sh
python3 -B verify.py
python3 -B verify.py --full
```

The first command reconstructs all 11 core source/table artifacts in a fresh
temporary directory, runs all 4,774 construction-side contracts and the
free-term command identities, verifies the recorded independent literal
certificate against the exact tables and complete source graph, and checks
its outcome coverage and positive affine duration vectors. The second also
replays all 4,774 independent literal outcomes; that full replay has already
passed for the delivered table. These are supporting executable checks,
not a proof-assistant kernel certification of the arithmetic theorem.

A fresh standalone construction can be written with:

```sh
python3 -B build.py --output rebuilt
```

All 3,668 source instructions and all their jump/decrement successors are
included. Exact blank initialization reaches the full source seed frame in
57,768 physical steps. The independent verifier derives four generic list
lemmas from literal rows and covers nine arbitrary natural registers,
arbitrary affine nonnegative gap and an arbitrary nonempty spare list.
Its minimum positive duration constant is 3. The changed native row occurs
in 25 checked branch outcomes from 19 distinct primitive source sites.

`comparison/native_deltas.json` records the exact native-label comparisons.
The surrounding research package includes the full 521-class table corpus
and a standalone strong novelty comparator. The graph comparison permits
arbitrary control names and spanning roots, reflection, global symbol
exchange, and ignored final actions; symbol exchange is only a structural
screen, not a zero-blank semantic equivalence.

The mathematical argument uses the existing numerical calculus and the
specifically identified revised AX11H written calibration. The new local
word identities, source/physical binding and native change are independent
of that absolute calibration. No machine below 194 states or completed Lean
consistency endpoint is claimed by this bundle.

The shared mathematical fragment in `proof/ax11gdh_preservation.tex` treats both the H machine and this symmetric HS sibling. The symmetric Shift is bound to the same abstract cache-only operation; the machine-specific source and literal receipts keep the two implementations separate.
