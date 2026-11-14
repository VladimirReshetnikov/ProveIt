# Independent comparison artifacts

These two comparison programs are self-contained and need only Python 3's standard library. Run from any directory:

```bash
python3 compare_tables.py
python3 compare_sources.py
```

Each script locates `inputs/` beside itself and regenerates its JSON result beside itself. `--inputs PATH` and `--output PATH` override those defaults. The checks use explicit exceptions and remain active under `python3 -O`.

`inputs/tables_manifest.json` identifies the original archive and internal path of each of the nine exact final dense tables. Each input is bound by its SHA-256 digest. `compare_tables.py` fixes start state 0, read symbols, write symbols, move directions, and the halt endpoint, then constructs a deterministic breadth-first canonical labeling. The generated complete label maps witness two graph isomorphism classes; the hashes merely identify their canonical serializations.

`inputs/sources_manifest.json` identifies the two exact source maps. `compare_sources.py` verifies identical opcode/operand order and ordinal control graphs, using explicit source-prefix intervals to resolve branches. It also records the different source addresses, maximum depth, zero runs, and source-file digests.

All inputs originate in `VladimirReshetnikov/ProveIt`, commit `c086b5adaa6228009365768946d691dfc49a20bb`, `docs/incoming`. Filenames in `inputs/` are short local aliases; manifests preserve the original provenance. `comparison_audit.md` gives the substantive comparison, interpretation review, and proof-status qualifications.

The `replays/` logs document fresh quick or finite executions of all five original packages. Those package-specific commands require the original extracted archives and are outside the two self-contained comparisons. Their full symbolic-runtime phases were explicitly skipped in the initial quick runs. A subsequent full `u208_research` execution freshly regenerated and passed both final graph classes' symbolic interpreter contracts; `replays/research_full.json` records 5,084 contracts and 416 covered rows for each class, with 1,250,564 symbolic applications for class B and 1,251,865 for class A. Elapsed time was about 187.24 seconds. This is symbolic interpreter evidence, not an exported proof-assistant certificate for the complete PA endpoint.

None of these comparisons proves a new PA formalization, a smaller Turing machine, or a lower bound on the number of states.
