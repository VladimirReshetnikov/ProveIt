# Conditional PA194 blank-start/source endpoint

`PA194SeedBridge.parent_blank_iff_source` proves that the exact unfolded
parent machine halts from its blank tape if and only if the formal PA194
source program halts from site 25 and the complete seeded register file.
`PA194SeedFacts.lean` independently checks that the physical seed has 35
blocks and represents logical register N = 2 with the remaining logical
registers equal to zero.

Both the per-site `Coverage` proof and exact blank-to-seed-frame reachability
are explicit hypotheses. The theorem combines the source/parent simulation
with deterministic prefix comparison, and is a standard-Lean result rather
than an internal PA/PRA/iPRA statement.

The independent full site and startup checkers are in `../pa194-coverage`
and `../pa194-startup`. They can supply the hypotheses once their complete
runs pass. A fresh pinned-source rebuild of this conditional endpoint is:

```sh
Computability/BusyBeaver/Research/PA/pa194-seed-bridge/check.sh
```

The Lean source was checked against rebuilt private dependencies. The full
fresh build is documented for sequential execution after the longer coverage
and startup jobs, to avoid competing with their resource use.
