# Reproducible negation-encoding and decoder searches

These are **discovery searches**, not accepted smaller machines and not lower bounds. Their best recorded effective AX-reader score is 62. With the fixed 134-state kernel, that is the existing 196-state benchmark. A score of at most 61 would nominate a possible machine below 196 states, but would still require simultaneous-fold, full-runtime, startup, source-semantics, and logical verification.

The positive, fully specified 197-state NEG18 implementation is supplied separately in the companion package. No file in this search directory is presented as a verified 195-state transition table.

## Model

The input is the existing 190-token separate-equality-vacuity emitter. The search changes permitted head roles, head order, binary associations, and the encoding chosen at each of its eight negation occurrences. Equal subtrees share readers. Candidate contextual folds use existing rows as helpers. A maximum matching gives an optimistic fold count; it does not certify that all chosen helpers can be used simultaneously.

All following negation spellings preserve the clean-store macro effect. The new arithmetic-core variants use `p(t,1)=p(0,t)+2` and the general pairing-core contract proved in the companion package.

| Kind | Three macro tokens | Primitive source sites |
| --- | --- | ---: |
| 0 | `push ; INC1 ; cons` | 47 |
| 1 | `node37 ; INC1 ; node64` | 20 |
| 2 | `node64 ; node61 ; node61` | 24 |
| 3 | `INC7 ; INC7 ; node64` | 18 |
| 4 | `INC7 ; node64 ; node61` | 21 |

`node37` enters at native 28, `node64` at 106, `node61` at 190, and `INC7` at 82. These states are already in the fixed kernel. The binary search uses kinds 0 and 1 with one mask bit per occurrence. The ternary search uses kinds 0, 1, and 2 with two bits per occurrence. The five-way search uses kinds 0 through 4 with three bits per occurrence. Occurrences are numbered from left to right after the head and role choices are assembled.

The final search also chooses between the original closing transition and `1 R 113`. On a closing `1` followed by `0`, existing rows `113/0 = 0 L 302` and `302/1 = 0 L 302` make the latter a three-step implementation of the original `0 L 302` action. It leaves the source instruction unchanged and can make its parent reader available as a pure helper. This local observation does not replace a complete candidate runtime check.

## Reproduction

A C++17 compiler is the only dependency. The commands below generate the original experimental budgets. The stochastic runs may take several minutes each. They use self-contained input headers; no repository checkout, Python modules, or network access is required.

```
g++ -O3 -std=c++17 mask_search.cpp -o mask_search
./mask_search 10000000 567892 binary_replay

g++ -O3 -std=c++17 ternary_search.cpp -o ternary_search
./ternary_search 10000000 567893 ternary_replay

g++ -O3 -std=c++17 ternary_one_rotation.cpp -o ternary_one_rotation
./ternary_one_rotation one_rotation_witnesses.jsonl > one_rotation_receipt.json

g++ -O3 -std=c++17 five_close_search.cpp -o five_close_search
./five_close_search 10000000 567896 five_closing_replay
```

Each stochastic run takes an iteration-slot budget, a random seed, and an output prefix. It saves a summary JSON, a final best witness, and any improving discovery witnesses. A `winner` file, if a future run creates one, is still a discovery object rather than an accepted machine. The exact source trees and decisions are represented by the supplied JSON inputs and witness records.

The one-rotation program is exhaustive within its stated family: all `3^8 = 6,561` encoding masks in the original head order and role assignment, followed by zero or one admissible global tree rotation of the assigned baseline grammar. It checks 703,446 scores and has minimum 62. This does not cover arbitrary source rewrites or arbitrary physical machines.

## Recorded results

- `mask_run.json`: 10,000,000 iteration slots; 8,718,871 score evaluations; best score 62.
- `ternary_run.json`: 10,000,000 iteration slots; 8,699,367 score evaluations; best score 62.
- `ternary_one_rotation.receipt.json`: 6,561 masks and 703,446 score evaluations; best score 62.
- `five_close_run.json`: 10,000,000 stochastic iteration slots, preceded by all `2 * 5^8 = 781,250` initial mask/closing assignments; 9,443,373 total score evaluations; best score 62.

Elapsed time is intentionally not used as a verification criterion. Random-search traces are reproducible experiments, not proofs of optimality. Searches that were interrupted while being replaced by broader versions are not counted as completed budgets here.

## Provenance and limits

`PROVENANCE.json` pins the source revision, input family, and random seeds. Original ProveIt and James Chang licenses are preserved. The C++ search is an adaptation of the inherited source-tree/read-state/helper machinery, extended during this investigation.

The additional scratch hypotheses are proved at macro boundaries for the clean-store implementations, but this discovery score does not check whole-program invariants for every generated grammar. Likewise, it does not establish the missing reverse PA-internal consistency implication for the imported baseline. Every claim here is restricted to the exact reported computational model and finite budget.
