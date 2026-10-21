# Source-compression research checkpoint

This checkpoint records source-level work toward a machine with at most 217 working states. **It does not contain a verified 217-state candidate.** The important constructive result is a reversed Cantor stack encoding whose PUSH routine uses 16 primitive instructions instead of 19. The associated 206-node source still allocates 229 raw physical states with the current allocator. A separate merged-command source reaches 204 DAG nodes, but has both a completeness gap and a 223-state allocation.

The detailed mathematical derivations and bounded-search findings are in `reports/source_research.tex`. The source macro arguments apply to arbitrary natural register values. Finite diagnostic tests and exact decoder-prefix binding are separate evidence and are labeled as such.

## Included files

- `inputs/`: the pinned K218 source and transition table used by this study.
- `candidates/cantor-fast-f0-s1-p1.*`: the 206-node reversed-stack source and its 229-state raw allocation. This raw allocation is not claimed to pass complete runtime/startup validation.
- `candidates/omit-zero-push.*`: a 218-state alternative; its primitive runtime and exact startup have passed independent checks. The changed proof compiler must account for the omitted proved-zero stack entry.
- `candidates/merged-n-*.sites.json`: four 204-node sources with the merged N command. Logical completeness remains open; the successful allocation requires 223 states.
- `candidates/prefix-q0-i2.sites.json`: the best changed constructor code in the 444-variant prefix-code sweep. It has 206 DAG nodes and maximum zero run 10.
- `candidates/grammar204-balanced-best.sites.json`: a pure reassociation specimen with 204 nodes. It has maximum zero run 7 and fails the existing decoder allocation's marker-context obligations.
- `candidates/zero_abstract_r6.sites.json`: the source equivalent guarded-zero rewrite. This file is a source certificate target; no machine-runtime claim is attached to it.
- `results/`: exact bounded-search records and selected allocation/startup receipts.
- `certificates/`: Boolean and ternary invariants. The ternary bitmap is gzip-compressed; its uncompressed SHA-256 is `4d8cd1c46705ea14998be21d3f3a67023371727d7cb5e6feba7d39c528ab08e3`.
- `code/`: pinned source utilities, macro builders, selected search replays, and independent certificate checkers. Paths are relative to this checkpoint.

## Reproduction

Run from this directory with Python 3. No repository checkout or transient absolute path is required.

```sh
python3 code/verify_checkpoint.py
python3 code/verify_invariants.py
```

The first command checks file identities, source metrics, independent CFG agreement, and reconstructs the shorter push and merged-command sources. The second checks the Boolean invariant, reconstructs the arithmetic CFG, decompresses the ternary bitmap, compiles the independent C++17 closure checker, and checks every included ternary configuration and edge. It needs a C++17 compiler available as `c++`.

The optional full prefix-code measurement takes a few minutes and writes only under `reproduced/`:

```sh
python3 code/prefix_constructor_codes.py
python3 code/cantor_scratch_choices.py
```

The raw-allocation checks are intentionally not substitutes for primitive-runtime or blank-startup proofs. The one-step source operations, local arithmetic contracts, global logical calibration, decoder binding, primitive runtime, and startup are separate obligations.

## Bounded results

| Family | Recorded scope | Best result |
|---|---:|---|
| Native source | pinned baseline |205 DAG /218 physical |
| Omit successful-MP dummy zero | complete primitive runtime and startup checks |205 DAG /218 physical |
| Merged N command | two associations, with/without dummy zero |204 DAG /223 raw physical; completeness open |
| Reversed stack and proof-input pairing | eight direct orientations |206 DAG with optimized PUSH16 /229 raw physical |
| Coherent arithmetic scratch choices |64 choices |206 DAG |
| Binary constructor prefix codes |444 distinct concrete variants |205 native;206 best changed code |
| Three unreachable primitive leaves |12,167 assignments |205 native minimum |
| Two dead subtree contexts |42,025 assignments |205 native minimum |
| Existing guarded identity substitutions |690 pairs |205 native minimum |

All negative entries are bounded search outcomes, not lower bounds. The complete scratch tables for the older negative searches are not included; their receipts record the bounded families. The constructive arithmetic changes, merged command, prefix-code sweep, and inductive certificates have portable reproduction scripts.
