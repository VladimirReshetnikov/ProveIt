# Direct PA195 source-to-physical site checks

`PA195SourcePhysical.lean` constructs each symbolic physical contract inside
Lean directly from an ordinal of the generated formal PA195 source tree. It
uses the upstream `nthSite`, `resolveTree`, and `physicalRegister` functions,
and obtains every target path from the same source tree. Increment, jump,
halt, and both decrement outcomes are handled; unresolved targets cause the
check to fail. Lean checks that the tree has exactly 3,700 sites and 4,815
branch outcomes.

For a site whose `acceptedSite` test has been kernel-checked,
`site_cases_sound` proves positive reachability on the exact unfolded parent
for every generated branch contract, every valid complete register file, and
every gap. `generate.py` emits closed Lean tests for ordinal ranges; no
`source.json` sites, successor ordinals, or recorded symbolic outcomes are
used to construct these contracts.

From the repository root, rebuild pinned dependencies in a private `/dev/shm`
directory and check every site sequentially:

```sh
Computability/BusyBeaver/Research/PA/pa195-direct-coverage/check.sh
```

The default is ten sites per batch. For a smaller check, pass, for example,
`--start-site 0 --stop-site 10`. Generated batch counts are intended coverage,
not evidence that a complete run has finished. The formal tree is generated
from the pinned upstream source program and PA195 grammar; the small Python
grammar-to-Lean translator remains an explicit source-generation boundary.
Positive reachability for individual symbolic branches is not yet a full
source-program execution theorem or a PRA/iPRA consistency equivalence.
