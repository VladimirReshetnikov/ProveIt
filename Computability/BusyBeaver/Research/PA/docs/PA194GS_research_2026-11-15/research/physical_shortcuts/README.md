# Finite-window physical reduction screen

`shortcuts.cpp` is a standalone exploratory screen for semantic shortcuts and control deletions in a two-symbol blank-start Turing machine. The frozen native tables in `inputs/` use start control 74 and halt target 254. No candidate with fewer controls was found in the recorded runs.

The screen first computes an inductively closed overapproximation of reachable local configurations. A radius `K` window moves with the head. When a boundary cell is exposed, both possible bits are admitted; this keeps the abstraction closed without assuming facts about the unseen tape. The abstract computation begins at the all-zero window in control 74.

For each reachable abstract state/read context, the program follows the original machine for at most `F` steps while staying within that window. It records an endpoint as a legal semantic shortcut only if the head is one cell to the left or right, only the originally scanned tape cell may have changed, and every other represented tape bit is restored. It intersects these possibilities over all abstract contexts for that state/read pair. The original transition is always an available option. Every state/read context set in these runs was nonempty.

Using those uniform options, it checks whether one or two controls can be removed by redirecting all surviving transitions away from them. It also checks whether a pair of controls has common legal transition actions after aliasing one to the other. This does not cover arbitrary replacements, additional helper controls, tape recodings, or histories outside the chosen window.

## Results

`results.json` lists exact input SHA-256 hashes, radius, fuel, abstract context counts, and logs. Nine incoming 194-control tables were screened at radius 7 and fuel 129. ORH and the new gate-reassociated machine were also screened at radius 9 and fuel 257, with 10,601,743 and 10,650,383 closed abstract contexts respectively. All runs produced zero control-deletion or pair-merger candidates.

On tables without the corresponding accelerations already present, the only additional shortcut options were the previously known return accelerations `26,1 -> 1 R 91` and `101,0 -> 0 R 17`. Such a speedup does not reduce the number of controls here. The `*.options.tsv` files contain all admitted actions, including ordinary transitions.

## Replay

From this directory:

```sh
g++ -O3 -std=c++17 shortcuts.cpp -o shortcuts
./shortcuts inputs/PA194GS.native.tm replay_gs 9 257
```

Output goes to the chosen prefix. The program expects plain five-column native tables with no header. Use the radius and fuel in `results.json` to reproduce any other run. Radius 9 requires more memory than radius 7 because the window abstraction has exponentially many bit patterns.

The negative results are scoped to this sufficient local test. They are not a proof that the machines are minimal or that a 193-state PA-consistency machine cannot exist. The code and all input snapshots are retained so the assumptions and implementation can be reviewed independently.
