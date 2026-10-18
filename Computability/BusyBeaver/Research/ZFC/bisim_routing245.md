# Complete source-program equivalence for routing245

[BisimRouting245.lean](../../Lean/BusyBeaver/ZFC/BisimRouting245.lean)
proves that the routed245 register program and the original `Prog254` program
have the same halting behavior for every initial register function
`R : Nat → Nat`, at empty pointers:

```lean
Halts ProgramRouting245.program ⟨[], R⟩ ↔ Halts Prog254.program ⟨[], R⟩
```

The corresponding nonhalting equivalence is also proved. Neither theorem
assumes decoder coverage, a simulation, bounded register values, or a bound
on execution time. The exact 245-state binary simulation, blank-tape startup,
and proof inside PA remain separate obligations. The encoded theory is unchanged.

The proof checks all **3,013 entries** of the delivered bisimulation certificate
against the [exact routed decoder](program_routing245.md) and the original tree.
The [initial-segment proof](bisim_routing245_pilot.md) supplies the entry relation.
[BisimRouting245Data.lean](../../Lean/BusyBeaver/ZFC/BisimRouting245Data.lean)
projects 95 blocks from that same public certificate and proves their exact
reassembly. Each block uses the full certificate for successor lookup. The final
module combines every block and applies `RMBisim.check_halts_iff`.

All 95 block sources and audits passed: 95 named theorem probes and 190 typed
callers, with zero warnings. Their source checks took 321.724 seconds in total;
their audits took 23.684 seconds. The slowest source took 4.124 seconds. They use
`decide +kernel`, default proof limits, and the existing segment bound of 1,000.
That bound checks finite segments; it places no bound on program executions.

The final assembly passed five theorem probes and six callers, with zero
warnings, taking 0.309 seconds for the source and 0.270 seconds for its audit.
Its three certificate facts use `propext`; the two equivalence theorems use
`propext` and `Quot.sound`. Including the Data unit, this production stage
contains 97 checked modules, 104 theorem probes and 201 typed callers.

The [actual final record](results/bisim-routing245-verification.json) has identity
`a2093e5c80fd41dbfff2d59931319b4c971967b50166ae0838166086b982349b`.
The final source identity is
`04d0c9f55b6f576c01c30ed49f39fd5e23eeacec4ea10cf7d1f2917a503e8ba5`;
the fresh object identity is
`43bdcc8c25150ed4e22c182ce2e3082940ee9d971906267c2c34eeb7edb6ae3b`.
The final guard admitted exactly 104 checked project providers plus `Init`,
binding all 95 successful block records. Each source/audit pair ran serially
with `-j1 -M4096` and a shared 120-second limit. Every fresh source object was
recorded before its audit; input and provider hashes were checked afterwards.
No dependency rebuild, download or compiler-version query was performed.

The [publication manifest](bisim-routing245/publication.json) enumerates all
97 modules, their exact audits, actual records, logs and object identities.
The [text history](bisim-routing245/history.json) preserves preparations,
reviews, original tools and source snapshots with their historical paths.
It also preserves an emission-inventory path correction made before the
remaining 94 block proof runs and an unused CLI proposal. Compiled caches
are excluded.

The maintained Lean modules have ordinary imports and can be built with their
dependencies. Such a build is a new verification run. The unchanged guards in
[provenance](bisim-routing245/provenance/) document the archived run and require
its exact historical input layout, compiler and cached objects; this publication
does not supply a portable cache-reconstruction runner.

Original-machine and submission attribution, the ordinary mathematical proof,
and the complete executable replay remain in the
[245-state candidate documentation](candidate-routing245/README.md).
