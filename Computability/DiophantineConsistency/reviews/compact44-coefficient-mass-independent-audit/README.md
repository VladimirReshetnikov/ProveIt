# Independent finite compact44 coefficient-mass review

This reviews source and paired replay `49d10be3df`. For the pinned Lean table
of 943 compact rows, the source proves every payload
`v=w+2^8 n+2^17 e+2^25 s+127·2^34` lies strictly between 0 and `2^41`.
It then proves exact natural-number masses:

```
selector sum           12734826094758831
41 copy/anchor weights  2251799813684224
combined coefficient   14986625908443055
stencil = 2·combined+6 29973251816886116
```

All three displayed natural inequalities were verified, including
`3·stencil+1 < 2^66`; the exact positive difference is
`73697056539387548115`. These numerical theorems alone do not prove a
model-level weighted bound, graph word decomposition, fractional rotation,
carry reset, machine simulation, or iPRA consistency statement.

The audit separately reads all 943 rows from the pinned compact JSON,
recomputes the payloads and all selector masses, and runs the pinned
coefficient builder's `recipe()` without writing its materialized files. It
checks the ordered table and **each** selector coefficient, the 41 individual
copy/anchor powers plus the two zero dummy coefficients, and all totals. The
builder starts `dc` with four unit bare shifts and adds every nonzero
coefficient twice; its coefficient sum is `2·combined+4`. Adding one spatial
`DR` coefficient and one temporal coefficient gives the recorded `+6`
stencil. This is a finite source interpretation of the recipe, **not** a Lean
identity to the graph's K or an all-model graph-to-carry decomposition. The
JSON-to-Lean table match is inherited from the separately audited external
ordered source checker.

The read-only artifact audit checks exact packet/source bytes, both recorded
compiler and direct-import exits, full two provider overlays and matching
943-table seeds, source/object/log hashes, and reruns the independent 943-row
parent. Outer session 96941 is recorded as exit 0. The exact eight named
Lean reports all list `[propext]`, with no warnings or `sorryAx` in successful
logs. The failed exploratory session is retained in the source packet and is
not evidence of a successful theorem. The inherited provider has no complete
printed axiom inventory; package-transitive and dynamic ancestry are not fully
authenticated. RSS is sampled, not a hard process-tree quota; the `--deps`
timeout is not a whole-tree guarantee.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-coefficient-mass-independent-audit/audit.py
```

Actual audit session 84072 exited 0; see `CHECK.json` and
`terminal-observation.json`. The script checks its pinned recipe inputs both
before and after use and reads the original `/tmp` objects, with fail-closed
behavior if they are gone or change. These are point-in-time checks; no Lean
compilation is launched by this audit.
