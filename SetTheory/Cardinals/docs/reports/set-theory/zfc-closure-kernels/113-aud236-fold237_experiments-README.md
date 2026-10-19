# Additional local reductions below the composed237 candidate

**Outcome:** no sub-237-state candidate was found in the completed search classes. This package records extensions of the local search space, a legitimate omission in earlier halt-target domains, and reproducible positive controls. It does not establish a state lower bound.

The baseline is ProveIt commit `ecb4df12d256704d9115d4860f6ccb7b3443ef4a`, inherited-label `candidate-composed237/zfc_composed237_old.tm`: 237 working states, start95, halt254. The table SHA-256 is `a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a`. The positive-control238 table omits a start declaration; its start is explicitly95 in the searches and verifier.

## Mathematical changes

1. **Coupled helper compensation.** The first helper need not be independently neutral. It must first repair the merged-state contexts; a freely synthesized second helper can then repair its original contexts. This is a restricted sequential compensation class, not arbitrary two-helper synthesis.
2. **Caller-cell and head representations.** Each merged state may independently keep, erase, set, or negate its caller cell and shift its head by0 or2 cells. Both retained and deleted states may change representation. External caller rows are derived exactly, and the merged rows and helper compatibility are checked separately.
3. **Terminal observation.** New target domains include halt254, and any halted tape/head may match any other halted tape/head. Nonhalting checkpoints still require exact represented tapes and heads. Earlier freely synthesized folds involving state77 excluded all new halt targets even though77/1 is the table's only halting transition.

`research_notes.tex` supplies the caller formula, its proof, and the positive-block halting-simulation argument, as well as precise search limitations.

## Run the checks

The quick independent control verification needs only Python3:

```sh
python code/verify_controls.py
```

Recompile and replay the two search-engine positive controls with a GCC-compatible C++17 compiler:

```sh
python code/run_searches.py --controls --out /tmp/zfc-local-controls
```

Replay one family, or all completed families, into a separate directory:

```sh
python code/run_searches.py --family terminal_pair77_h65 --out /tmp/zfc-local-terminal
python code/run_searches.py --all --out /tmp/zfc-local-all
```

The full helper searches take several minutes each. The runner verifies byte-identical candidate output and completion; elapsed times in logs naturally vary. `search_receipt.json` records every exact argument list, source, coverage restriction and retained output. Negative candidate files are intentionally empty.

## Positive controls

- The known238→237 fold deleting235 and retaining98 is recovered exactly. An independent verifier reconstructs the237 table, checks30,112 predecessor-invariant closure cases, three open-tape blocks, and473 commuting rows.
- A synthetic three-state machine validates the terminal relation by reducing to two working states with different halted tapes/heads. This is a search-engine test fixture, not a consistency machine or a research candidate.
- All29,192 windows in the empirical profile lie in the93,177-window all-tape abstraction. The finite profile is still not exhaustive.
- The terminal-neutral catalogue adds exactly three alternatives at77/1 to the601 inherited alternatives. All three are excluded from helper selection whenever77 is a merge endpoint, so the active helper domains in the focused terminal searches are unchanged.

## Scope and provenance

Discovery uses a finite source-constrained empirical profile at radius5, not an unbounded runtime proof. Horizons are17,33, or65 according to the receipt. Common-row, single-direction, helper-count, encoding, and sequential-compensation restrictions are explicit. Larger state clusters, arbitrary predecessor-specific encodings, and transformations that need longer traces are not exhausted.

The machine tables, finite profile, and strict helper catalogue are retained from the named ProveIt baseline and the earlier `zfc_sub237_research_20261019` report. `neutral_terminal.cpp` directly adapts that report's `neutral_domains.cpp`, adding the halt target and relaxed terminal relation. The remaining C++ implementations and the independent control/replay scripts were written for this follow-up. Original calculus, machine and compiler attribution remains with the upstream notices; this research does not replace those credits. The parent integration package should retain its inherited licenses and source notices.
