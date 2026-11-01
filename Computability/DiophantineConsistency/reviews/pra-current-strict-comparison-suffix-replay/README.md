# Strict comparison suffix on the refutation-bound union

This suffix rebuilds the 11 strict-comparison and bound-certificate modules
absent from the independently replayed ZFC refutation-bound union. It does not
reuse the old comparison overlay: 183 shared objects differed from the fresh
union, so those objects are taken from the coherent union parent instead.

```
python3 Computability/DiophantineConsistency/reviews/pra-current-strict-comparison-suffix-replay/replay.py
```

The driver uses the precise parent Lean binary and package-only fallback;
it guards 274 current project sources covering both the 198-source comparison
graph and 259 observed union sources, all 268 parent project objects, 144
observed Foundation/ZFC objects, 11 frozen sources and the Lean binary before
and after compiling. It rejects warnings, errors and `sorryAx`. External
transitive Foundation, ZFCinPA, toolchain and package ancestry remains
inherited. The suffix supplies generic comparison machinery; the exact
current equation's IΣ₁ equivalence and final PRA comparison still require a
coherent source-current integration.

Author and independent peer passed with identical source, object and log
hashes for all eleven rebuilt modules.
