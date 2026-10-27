# Internal Pell recurrence: author checkpoint

26 October 2026. **Frozen author PASS; independent review pending.** ROOT
fully read the complete final main, Checks, source-only cache plan, plan
auditor and compilation driver before execution. No imported Foundation
source or existing shared object was changed.

The actual parameter is b+2 and the discriminant is (b+1)(b+3), so their
square relation is an identity over natural arithmetic. A fixed PR blueprint
starts at the represented pair (1,0) and advances by

    x'=(b+2)x+(b+1)(b+3)y,  y'=x+(b+2)y.

`run_defined` and `run_defined_delta` are fixed Sigma1/Delta1 graphs for
this total construction in every IΣ1 model. Both coordinate graphs are
explicit Sigma1 formulas. Genuine Sigma1 model induction proves the norm,
x>=1, y>=time and the two addition formulas for arbitrary internal indices.
The ordinate strictly increases at every successor. The norm-step proof
uses two commutative-semiring polynomial identities and no subtraction.
No unrestricted Lean induction on arithmetic model elements is used.

The internal state uses Foundation's represented Szudzik pairing. It has
no dependency on the machine's Cantor code and makes no assertion that
the two encodings coincide. Focused Checks bind the actual coordinate
graphs, initial step, discriminant identity, norm, growth and addition.

Only two new leaves were compiled. Their closure consists of95 cached
Foundation modules,380 selected artifacts,38 explicit external names and
114 boundary object companions. The read-only inventory checks every
selected current source header, existing source/object pin and external
source/companion. Its631 pins are rechecked before and after compilation.
There is no Foundation build or prerequisite refresh.

Both attempts are retained. Attempt1 rejected two proof elaboration details:
Foundation's addition-inequality lemma required a commutativity rewrite,
and the conjunction's second addition identity needed its own explicit
recurrence rewrites. No statement, import, heartbeat or memory cap changed.
Attempt2 passed main and Checks without warnings/errors. All snapshots,
drivers, inputs, commands, logs and timings survive in the author bundle.

Final provider: `/tmp/arithmetic-pell-recurrence-author-4bp5dmvd/lib`.
Commands use pinned Lean4.32 `-M6000 -j1 -DElab.async=false`, one thread,
explicit private LEAN_PATH, fresh regular outputs and a512MiB reserve.
Main passed in13.658 seconds, empty diagnostics,1,840,720KiB peak RSS.
Checks passed in2.389 seconds,1,790,956KiB peak RSS, with nine reports
limited to propext, Classical.choice and Quot.sound.

Main source SHA: `92acf4d2ce4d63e13cccb1afc5ebe5731e3648957dfd18a5311e537c41597c0e`.
Checks source SHA: `e3e166191d19d5d96a7b99112a0de4de15975bfc958626842ecc5b007e84a072`.
Main object SHA: `17f45d72cbc6e3388dc1bd34e7e57868ef57dc99c0d5b7b14a8334726ea71f62`.
Checks object SHA: `e2fcab83d6211410ca76551401518b6b2a7f73928e83eab273e3848018a01d41`.

[Replay packet](arithmetic-pell-recurrence-replay.json) SHA:
`022e44d19bec3bd4fe3de9e130d601ea31179bb73efcee51deb6233fe71e183d`.
[23-file manifest](arithmetic-pell-recurrence-author-replay/FILES.json) SHA:
`1613e9690d7287bae5cbec832fc613d6b553818a5f296840a0e1f897f2618bac`.

This proves the represented recurrence and its stated identities. It does
not yet classify all Pell solutions, identify every external Pell API,
prove carrier congruences or full cofinal witness bounds, or provide the
equation/ConZFC PA or HA theorem. The displayed decimal equation and PDF
are unchanged.
