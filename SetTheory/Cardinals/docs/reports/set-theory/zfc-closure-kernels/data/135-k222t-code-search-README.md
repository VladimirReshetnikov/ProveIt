# Optional contextual-fold research

This folder reproduces the scoped implementation search reported in
`../../evidence/additional_search_summary.json`. It is separate from the
mathematical K222 replay: the main `reproduce.py` needs only Python's standard
library, while this optional research uses a C++17 compiler.

The recorded direct screen found no additional fold of either final 222-state
table. On the conditional-G table, a further screen considered all 404 accepted
single neutral row rewrites, followed by fold synthesis after each rewrite,
and found no 221-state survivor. These results are not state lower bounds.

## Reproduce the neutral-then-fold experiment

Run the following from the package root. Build products and search output stay
outside the delivered packet. The Python driver's output directory must be
absent or empty.

```bash
mkdir -p ../K222-search-build
g++ -O3 -std=c++17 code/search/fold_search.cpp -o ../K222-search-build/fold_search
python3 code/search/neutral_search.py \
  --table machines/conditional/candidate222.k.tm \
  --executable ../K222-search-build/fold_search \
  --output-dir ../K222-neutral-replay
```

The driver first rederives the accepted neutral actions on that exact table;
it does not trust the stored action list. It then screens every resulting
table. The original run considered 404 variants and found zero survivors.
The driver writes its new action list, per-variant screen records, final
summary, and any surviving table proposals in the selected output directory.

For a direct fold screen, invoke the compiled binary as
`fold_search ABSOLUTE_K_TABLE_PATH 24` from a separate working directory.
It prints any `FOLD` proposals to standard output, counts to standard error,
and its final known-cell invariant to `last_facts.txt` in that directory.
Appending the argument `neutral` prints the accepted neutral row actions
instead of running the direct fold screen.

The alternative supplied K table is `machines/seed/candidate.k.tm`.
Use K-labelled tables with halt 254. The canonical files ending in
`candidate222.tm` have a different halt label and are not accepted by this
search kernel.

## Input requirements and exact search scope

- The table has one explicit `#! start` declaration, two binary transitions
  per working state, only left/right moves, and the distinguished halt 254
  with no outgoing transitions. Every declared working state must be graph
  reachable. Labels must lie in 0 through 1023. The Python driver additionally
  requires the supplied K convention of start state 0.
- An inductive abstraction records conjunctions of known tape bits at offsets
  -6 through +6 from the head. Initially every binary tape is permitted at the
  start state. This abstraction can lose useful relationships between bits.
- Candidate folds identify two distinct nonstart states. Both retained rows
  are synthesized together. Candidate first actions write 0 or 1, move left
  or right, and target an existing working state. A direct halt target is not
  among the enumerated first actions.
- Each local simulation block has positive length at most 24 by default.
  It must reach the mapped old one-step target with exactly the same head
  position and complete represented tape. Reading any unknown cell is
  rejected; an unfinished block is never accepted.
- The neutral experiment changes exactly one individually accepted row, then
  repeats the fold screen. It does not search arbitrary compositions of
  neutral rewrites, unbounded blocks, new encodings, or source-dependent
  invariants.

A search survivor is a proposal for a separate positive certificate and full
machine audit. No 221-state result is claimed by the archived negative screen.

## Original evidence and portable editions

`fold_search_original.cpp` and `neutral_search_original.py` preserve the exact
sources used for the measured run, including its original workspace paths.
They are retained to match the original SHA-256 records, and are not the
recommended portable entry points. `hybrid222-neutrals.txt` is the original
404-action list.

`fold_search.cpp` adds input validation around the unchanged search kernel.
`neutral_search.py` supplies explicit paths and a fresh output directory,
rederives the neutral list, and writes a complete portable summary. These
editions do not expand the recorded search family. `provenance.json` maps
the original and portable source files to their hashes.

The main construction and proof replay do not require running this search.
