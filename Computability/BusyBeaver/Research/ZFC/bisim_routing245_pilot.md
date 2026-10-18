# First checked source-bisimulation entries for routing245

The [complete certificate and source-program equivalence](bisim_routing245.md)
are now checked. This note records the earlier pilot and its narrower scope.

[BisimRouting245Pilot.lean](../../Lean/BusyBeaver/ZFC/BisimRouting245Pilot.lean)
contains the complete delivered 3,013-pair certificate and checks seven finite
obligations against the original `Prog254` tree and the
[exact routed245 decoder](program_routing245.md). These are the initial
segment and entries 0, 90, 103, 329, 791 and 3012. They include the halt pair,
the first changed address and the deepest old and new addresses.

All seven theorem audits and seven typed callers passed, with zero warnings.
Source checking took 9.971 seconds and the audit 0.244 seconds. Each theorem
uses only standard `propext`. The proofs use `decide +kernel`, default proof
limits and the existing `RMBisim.segFuel = 1000`. The supplied Python checker's
larger bound does not substitute for these Lean checks.

**This is partial certificate verification.** It proves neither the global
`allC` condition nor halting equivalence. The remaining entries must all be
checked and assembled before applying `RMBisim.check_halts_iff`. The intended
conclusion compares the two programs at the empty pointer for every register
function `Nat → Nat`; it will require no bound on register values.

The input order, both branch targets and raw pointers are preserved. Pointers
use the binary sentinel encoding `1P`, without adding trailing zeroes. Only
the halt pair's unused null successors become zero. A separate parser checks
all 3,013 rendered entries and lookup positions, including every left-subtree
size used by the balanced certificate tree. Its 95 chunks contain 94 blocks
of 32 entries and a final block of five.

The [actual run](results/bisim-routing245-pilot-verification.json) has identity
`4598ab1e2160d49e8774e0f71cf883b4766198342cdb088c6f6e27b630fa174f`.
The checked source is
`b7b061dffcdaddf856eabbf6a2cc826e22431bbbc74d0d9e8704167bbe1801b1`;
the fresh object is
`da87fcdecd9ade0ce3bc407b18da7ed013b12548690c57ef54cb250da77d1380`.
The [history](results/bisim-routing245-pilot-history.json) preserves source,
audit, inputs, reviews and raw logs. It also preserves the earlier preparation
failure: a Python loop variable shadowed the parsed arguments. That attempt
invoked no compiler; renaming the loop variables fixed the guard, with the
Lean source and certificate unchanged.

The guard selects exactly seven previously checked project providers plus
`Init`, using the successful 246 endpoint and routed245 program records.
Source and audit share a 120-second limit with `-j1 -M4096`. The fresh object
is recorded before the audit; all inputs and providers are checked afterwards.
No dependency build, download, compiler-version query or raised proof limit
is used. The historical compiler and object providers are prerequisites.

From this directory, using fresh external output directories:

```sh
python3 -B check_bisim_routing245_pilot.py --output /tmp/routing245-bisim-pilot-prepared --prepare-only
python3 -B check_bisim_routing245_pilot.py --output /tmp/routing245-bisim-pilot-checked
```

The [publication record](results/bisim-routing245-pilot-publication.json)
binds maintained files to the actual run. The
[maintained-path check](results/bisim-routing245-pilot-maintained-publication.json)
confirms those installed files and preparation without replaying Lean.
The subsequent [complete source bisimulation](bisim_routing245.md) discharges
the remaining certificate entries. Binary simulation, blank startup and the
245-state consistency endpoint remain separate obligations.
Original-machine and submission attribution remains
in the [candidate documentation](candidate-routing245/README.md).
