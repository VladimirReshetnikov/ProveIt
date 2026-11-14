# Source-reduction research status

## Positive result

`source_optimization/` is a complete, reproducible **source-level** specialization from3,909 to3,904 primitives and from5,083 to5,076 ordinal edges. Its two removed tests are identities whenever reached. Single-register abstract invariants have6,430 and9,651 pairs, respectively. The source checker verifies both CFG resolvers, the exact surviving instruction/edge projection, and every finite inductive closure. Ordinary and `python -O` outputs agree. The proof is `source_optimization/PROOF.md`.

The transformed source has200 distinct syntactic subtrees, compared with197 before specialization. A further source-only reassociation search found199; see `source_dag_199/`. That result raises maximum depth to53 and maximum zero run to11, so it worsens the delimiter requirement and is not an improved baseline. This does **not** imply a physical state saving. The199-node result relies on source transformations that have not been physically allocated; no literal interpreter table accompanies it.

## Literal table searches

- A random closed-factor source reassociation walk without runtime screening rediscovered the known invalid85/154 merger. It is labeledREJECTED in `found_519/`.
- A finite-runtime-filtered walk examined7,017 distinct table layouts, accepting approximately1,600 intermediate layouts. It found no surviving exact row duplicate. The walk later became stuck at previously visited restart neighbors, so its4,000 nominal iterations are not4,000 independent extensions; the distinct-layout figure is the meaningful count.
- A mixed walk allowed closed rotations, occasional broader exact-CFG rotations, and commuting closed source factors with disjoint touched-register sets. It examined12,691 distinct table layouts;2,980 intermediate moves passed its finite screen. No exact duplicate-row saving survived. The finite screen is a discovery filter, not an arbitrary-register proof.
- Five finite-validated, startup-preserving208-state layouts were exported under `safe_layouts/` for the independent endpoint-fold search. Their primitive word and ordinal graph are unchanged, every row used during the baseline48,140-step startup is unchanged, and all15,252 finite primitive cases pass. They have not undergone universal symbolic replay.
- The six-zero delimiter shortcut fails because runtime temporarily extends a trailing six-zero source word to seven zeros. Stable source and successor words have internal zero runs at mostfive, but that bound omits the transient field. `u207_threshold/` is explicitly labeledREJECTED.

## Reusable finite screen

`finite_fast.cpp` and `runtime_screen.py` implement a fast bounded primitive-contract screen using fixed-size binary tape arrays. Its15,252 baseline contracts take roughly0.05 seconds in the preparation environment. It checks zero/positive decrement branches, three concrete register/spare/gap assignments, and complete finite tape equality at the expected return frame. Compile with:

```bash
g++ -shared -fPIC -O3 -std=c++17 finite_fast.cpp -o lib_finite_fast.so
```

The wrapper returns zero on success and a case index on failure. This is intentionally not a quantified simulation theorem. A candidate that passes requires the independent arbitrary-natural symbolic runtime checker and an exact startup argument.

## Useful next direction

The existing U208 table implements the inherited dual-Cantor numerical calculus with unrestricted covering/vacuity and collision handling. It does not implement the separate nine-pairing frozen-guard positive emitter described in `pa_unary_power_cover.zip`. Compiling that alternative interface, rather than only rearranging the current emitter, is a distinct avenue. It requires a corrected context-aware allocator, complete arithmetic entry protection, fresh startup transport, and the corresponding proof-search calibration.

The newly proved unreachable source branches offer a second precise allocation target: retain generic transfer and comparison helpers for their many old call sites, but implement the two specialized calls using context-dependent decoder entries. Merely pruning their leaves increases DAG size because those old helper subtrees were shared; a net state saving needs physical sharing or an additional association choice.

No validated table with fewer than208 states was obtained by this source-reduction subtask.
