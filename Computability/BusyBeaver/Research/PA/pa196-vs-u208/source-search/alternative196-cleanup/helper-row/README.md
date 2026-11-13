# Arbitrary helper-row folds of alternative196

This screen finds **no** 195-state survivor within its stated local simulation template. It uses the alternative196 literal table in the parent directory, SHA-256 `aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95`. This is a bounded search result, not a state-count lower bound or a PA-consistency theorem. The baseline alternative layout and its incoming archive provenance are documented in [the parent README](../README.md).

For each of the 38,220 ordered choices of deleted and retained working states, the search redirects all targets of the deleted state to the retained state, then permits replacing **one row at any retained state**, including a third helper. The original machine's radius-six blank-start window closure has 270,841 state/windows, projecting to 2,756 distinct five-cell state/windows; abstract halt is reachable. An independent C++ closure implementation reproduces the closure, projection, and abstract-halting counts. The search requires each original step at either merged state or the modified helper to be matched by 1–16 candidate steps using only that five-cell window and ending with the projected state, same head position, and same complete five-cell tape. Other parent rows commute in one step. The closure is an overapproximation: it forgets the newly entered bit as the head moves.

The visited-row intersection prefilter is necessary for any one-row repair within that template: every failing unpatched local block must pass through the row whose replacement repairs it. It leaves 2,148 candidate row locations, 805 at a state other than the keeper, and the C++ engine tests 1,684,032 replacement triples. Five pass their representative windows; none passes every affected-state window. Each rejecting context is re-executed by the independent Python block interpreter, and any survivor would be independently checked on **all** contexts of every affected parent state. The standard U209-to-U208 known fold and a synthetic fold requiring a third helper both pass the search and independent Python controls. See [receipt.json](receipt.json) for exact literal state numbers, rejection windows, checks, and input hashes.

A near miss deletes literal state 45, keeps 161, and changes helper row `(190,1)` from `1 R 78` to `1 L 75`. It fails the full local template at state 190/read 1 with five-cell mask 6. This is an abstractly admitted context, not by itself an actual blank-run counterexample.

## A source-reached frame for the near miss

[source_actual_witness.py](source_actual_witness.py) resolves the complete alternative source CFG by two methods and executes its exact source program from site 25 and logical registers `[2,0,0,0,0,0,0,0,0]`. At source step 32,037 it reaches site 604 with registers `[4,1,75,0,0,0,0,0,0]`, after 10,544 increments and 10,466 positive decrements. The decoded source frame has right marker position 10,514 and physical file `[75,0,1,0,0,0,4,0,0]` followed by 10,570 ones. Both literal tables hit the adverse state 190/read 1/mask 6 at frame step 29.

The original table reaches the exact site-605 frame in 84,146 steps, with the first physical register decremented to 74, marker at 10,515, and 10,570 spare ones. The near-miss table instead reaches the exact site-615 frame in 147,968 steps, with physical registers `[75,0,1,0,0,0,4,0,1]`, marker at 10,514, and 10,571 spare ones; it does not visit the original endpoint in that checked prefix. The script compares full finite-support tapes, heads, and states, and records hashes of complete transition traces in [source-actual-receipt.json](source-actual-receipt.json).

This is an exact source execution plus a concrete frame replay. The alternative's physical connection from blank tape through this entire source prefix is supported by its executable startup and arbitrary-value instruction checks, but has not been Lean-certified here or replayed as one continuous literal blank run. The modified machine might already diverge before this frame. This evidence refutes this specific source-cycle preservation argument; it does not rule out later rejoining or another equivalence proof.

## Reproduction

From this directory, with Python 3.10+ and a C++17 compiler:

```sh
python3 -B replay.py --output /tmp/alt196-helper.json --candidate-dir /tmp/alt196-helper-candidates
python3 -B source_actual_witness.py --output /tmp/alt196-source-actual.json
```

Both outputs are deterministic and match the retained receipts. The first compiles the existing [helper search](../../../search/helper-row/scan_helper.cpp) and independent [window closure](../../../search/helper-row/window_closure.cpp) in a temporary directory; no executable is retained in the repository. It pins the incoming archive via the parent directory's `check_archive.py` and checks the existing U209 control's exact archive-member hash. The candidate directory is only used if a survivor is found.

The five-cell/16-step simulation, direct state projection and single changed row are restrictions of this search. The negative result says nothing about multistep parent matching, two patched rows, different tape encodings, or arbitrary other machines.
