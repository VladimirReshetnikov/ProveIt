# Exact row bases and bounded replay caches

Run from `fast/` with Regina available for the audit:

```sh
python -B -m euler_basis_research.audit --output ../synthesis/data/euler-basis-audit.json
python -B -m euler_basis_research.benchmark --output ../synthesis/data/euler-basis-benchmark.json
python -B -m euler_basis_research.replay_benchmark --output ../synthesis/data/euler-basis-replay.json
python -B -m euler_basis_research.check_evidence --publication
```

Run timing commands separately without competing CPU jobs. The original-standard
audit repeats all 88 masks, four model/strategy combinations, and circle,
trefoil and bounded figure-eight diagrams from the previous tree audit with
current native sources. Every negative tree and positive crushing ray is
independently replayed; original-standard vertex membership and all labelled
quotients are compared with Regina. Inconclusive outcomes retain only partial
chains. Historical evidence remains unchanged.

The full-query benchmark uses five randomized four-arm pairs, batch size one,
and one A/A pair on complete circle and trefoil queries. Arms select the prior
LP and verifier, row reduction alone, replay caching alone, or both changes.
The two historical modules are byte-pinned to commit `1c1665d2c`; the driver
and shared dependencies use current pinned sources. Native construction,
shelling, preprocessing, discovery, internal replay, patch setup and full-result
serialization are timed. Every timed output must match its independently
verified warmup. The circle terminates during vertex preprocessing and is an
overhead control. The trefoil exercises complete negative tree discovery.

The separate replay benchmark uses the exact same historical trefoil
certificate in both arms. It measures tree-only and complete diagram-bound
recognition replay with nine randomized pairs, batches of three, and three
A/A pairs. Each call starts with fresh source-local caches. It excludes
certificate loading, imports and patch setup, and performs no discovery.
Separate untimed instrumentation counts all parsed duals, matrix products,
objective constructions and cache hits.

All current native files and imported research dependencies are pinned at
both ends of each run. The checker replays saved evidence, verifies hashes,
recomputes timing arithmetic, and writes article tables and a publication
manifest. Neither exact row selection nor bounded replay caching supplies a
polynomial simplex pivot bound or a general quasi-polynomial tree-size bound.
