# Completed reduction attempts

No experiment in this directory supplies an accepted machine below 194
states. `summary.json` records ten completed emitter-allocation runs,
totaling 14,425,456 mutation iterations. They are bounded heuristic
searches, not an exhaustive state-count lower bound.

## Emitter searches

The files `exchange0.txt` through `exchange7.txt` and their formula JSON
companions encode premise-exchange subsets of the third, fourth, and
sixth ordinary heads. The three bits of the mask select those changes
in that order. Mask 4 is the Q quantifier-head exchange; mask 0 is the
unchanged premise order. Six searches of the other masks are recorded
as `run1`, `run2`, `run3`, `run5`, `run6`, and `run7`.

`radix{k}_mask{m}.txt` contains coefficient `k` in {5,6}, with the primary
word (`m=0`) or Q word (`m=4`). The radix screen includes the extra fixed
control and allows its 41/99 fold together with decoder folds. The score
convention is `134 + score` projected working states. A score below 60
would nominate a table below 194 for full checking. None was found.

Example optional discovery commands, from `search/emitter/`:

```sh
c++ -O3 -std=c++17 search_adaptive.cpp -o search_adaptive
c++ -O3 -std=c++17 search_radix.cpp -o search_radix
./search_adaptive exchange1.txt leaf_attrs.txt fresh_exchange1 240 140214
./search_radix radix5_mask4.txt radix_attrs.txt fresh_radix5_q 240 140214
```

The stored logs give the actual seeds and elapsed budgets for the runs in
this session. Mutation counts are wall-time dependent. A grammar produced
by a search still requires source binding, simultaneous fold checks,
complete primitive contracts, and exact blank startup. The accepted Q5/Q6
grammars are frozen separately under `construction/`; their reconstruction
does not run these searches.

## Physical invariants and new history marking

`physical_invariants/` is a complete independent subpackage using the
previously supplied PA194QN machine. Two complete context derivations
cover all 4,755 source outcomes and all 194 controls. A stronger
zero/positive/modulo-four invariant plus one-valued spare lists removes
5,091 of the first screen's 29,479 radius-five windows.

Both context sets were subjected to common-action merging, per-edge
bypass, and predecessor-history marking. Every screen completed at a
300-step detour bound and found zero candidates. The marking search
allows predecessor writes to carry a control-role bit which the detour
must erase while restoring the original tape. It checks 14,401 independent
pairs and 22,148,352 candidate first-action trials per context set.

See that subpackage's README, proofs, hashes, and `replay.py` for precise
scope and reproduction. Its table and startup counts differ from Q5/Q6
because it is searching the supplied QN construction.

## Logical and compiler obstructions

`fresh_gate_analysis.tex` explains why an automatically fresh separator
can be arithmetically sound yet fail the required arbitrary-label vacuity
interface in the current completeness proof.

`REJECTED_EXPERIMENTS.md` records the contradiction-at-MP compiler attempt
and its failed source contract, so it cannot be mistaken for a verified
replacement. Overlapping savings also matter: existing SUMS and radix
folds both use native control 41 and cannot simply be added.
