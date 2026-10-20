# Equality search with all accepted K219 subtrees

Neither bounded pass found an equality replacement reducing the accepted source below **206 distinct subtrees**. The only 206-node result in each pass is the original equality macro. These finite experiments produced no new machine or all-natural correctness proof.

The [literal library](inputs/atoms.json) contains all 19 accepted K219 subtrees using only CI/CD on registers 5 or 6 and CB/CC, excluding the complete equality macro. It extends the [earlier 14-atom search](../k219-equality-extension/README.md) with five existing subtrees:

| Name in this note | Literal tree |
|---|---|
| Z | `(CD5, CC1)` |
| U | `((CD6, CC2), CB1)` |
| A | `(CD5, U)` |
| L | `(Z, U)` |
| R | `(A, CD6)` |

The complete accepted equality is `(R, L)` and is deliberately excluded as an atom. [library.py](code/library.py) independently resolves open Break/Continue control from leaf paths. It evaluates both registers on 0..9, treating overflow or repeated bounded configurations as unknown. All **1,400 entries** of the original 14 atom signatures match exactly; the [control record](results/library-review.json) and both original and expanded signature tables are retained.

Each new binary composition has tree cost one; a supplied atom has cost zero. The cost-4 pass keeps intermediate costs at most 3 and tests cost-4 roots only against the equality goal. The cost-5 pass keeps intermediate costs at most 4 and tests cost-5 roots only. Intermediate signatures cover 0..9. Root goals require both registers cleared, Normal exactly on equal inputs, and Break(1) otherwise, on inputs 0..4. Unknown root outcomes reject. Keeping one first representative per intermediate signature can discard useful alternatives, so this is not a complete search for the smallest full-source DAG.

| Pass | Trials | Stored nodes | Finite hits | Search seconds | Minimum full-source DAG |
|---|---:|---:|---:|---:|---:|
| [Cost 4](results/cost4/execution.json) | 881,549 | 14,559 | 172 | 0.349 | 206 |
| [Cost 5](results/cost5/execution.json) | 10,766,801 | 146,855 | 1,711 | 4.303 | 206 |

Both passes completed. Each invocation had a 109-second internal deadline, a hard external 110-second timeout, and a cap of 800,000 stored nodes checked before insertion. The exact [C++ source](code/search.cpp), [change from the earlier search](code/search-from-root.diff), logs and compressed node recipes are preserved.

Every reported finite hit was reconstructed and substituted at all four exact occurrences of the accepted macro. The [cost-4 census](results/cost4/census.json) is 206:1, 207:10, 208:28, 209:133. The [cost-5 census](results/cost5/census.json) is 206:1, 207:4, 208:154, 209:262, 210:1290. Complete literal macros and metrics are retained in compressed analyses, without duplicating 1,883 whole source files. No wider finite check was needed to reject these results as a route to fewer source DAG nodes. The finite goal itself does not prove all-natural equivalence.

From the repository root, use fresh output paths and enabled Python assertions:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-atom-extension/code/prepare_library.py \
  --output /tmp/k219-atoms-fresh
g++ -O3 -std=c++17 \
  -o /tmp/k219-atoms-fresh/search \
  Computability/BusyBeaver/Research/ZFC/k219-atom-extension/code/search.cpp
python3 -B Computability/BusyBeaver/Research/ZFC/k219-atom-extension/code/run.py \
  --work /tmp/k219-atoms-fresh --binary /tmp/k219-atoms-fresh/search --cost 4
python3 -B Computability/BusyBeaver/Research/ZFC/k219-atom-extension/code/analyze.py \
  --work /tmp/k219-atoms-fresh --cost 4 --output /tmp/k219-atoms-analysis4-fresh
```

Repeat the last two commands with cost 5 and a fresh analysis directory for the second pass. The runner rejects an existing `cost4/` or `cost5/` output directory. The exact original scratch scripts and wording are preserved in [compressed history](history/scratch-texts.json.gz); portable path/output adapters have explicit adjacent diffs and were not used to rerun the searches during publication.

Reconstruct any retained literal macro as a full source without running a search:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-atom-extension/code/reconstruct.py \
  --cost 4 --id 0 --output /tmp/k219-macro-reconstruction-fresh
```

This was checked for macro 0: the [reconstruction receipt](results/reconstruction-control.json) binds all four replacements and reproduces the accepted source bytes exactly. Reconstruction checks literal identity and DAG metrics, not runtime behavior. [Provenance](provenance.json) binds the actual scripts, inputs, compressed records and omitted build product. The Source 140 submission contributed the original C++ finite-signature search. Root adapted it for the bounded cost-6/cost-8 searches; `drop_contract` adapted that successor and authored the independent library, wrappers, analyses and publication adapters. The historical scratch note's attribution to root is corrected here. The accepted candidate files and proof sources were not changed.
