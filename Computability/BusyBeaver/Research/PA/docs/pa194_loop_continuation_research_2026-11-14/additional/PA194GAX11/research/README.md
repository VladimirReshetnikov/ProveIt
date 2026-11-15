# Fresh source and combined-core searches

These are optional discovery experiments. They are not required to rebuild
or check the delivered PA194GAX11 table.

The two original-core runs completed 2,500,000 and 10,000,000 stochastic
iteration slots. They varied ordinary-head order and independent parameter
permutations, admissible gate variants, and binary source reassociations.
Both had best effective reader score 60. With 134 fixed controls this is
a projected total of 194 states, before physical fold validation.

Combined searches used the new loop-continuation cores numbered 3, 6, 7,
and 8 in the main package. They completed 2,000,000, 5,000,000, 2,000,000,
and 2,000,000 slots respectively. All had best effective reader score 60.
Core 6 has 134 fixed controls; the other three have 135. No score for a
sub-194 candidate was reached.

Three subsequent corrected-metadata runs were **interrupted**, with logs
covering at least 1,300,000 slots for core 3, 1,300,000 for core 6, and
1,700,000 for core 7. They have no final receipts. Their requested budgets
were 3,000,000 each, but those budgets must not be reported as completed.
The last logged best score was 60 in all three.

Thus 23,500,000 slots are supported by completed receipts, with at least
4,300,000 additional slots in interrupted logs. `search_ledger.json`
records every seed, count, status, and scope.

The score subtracts a maximum matching of potential contextual folds.
Simultaneous compatibility and literal source execution must be checked
separately for a promising result. A negative stochastic result is not a
state lower bound. The initial combined searches retained conservative
source-address attributes; the corrected runs reduced the increment-path
attributes of `node65` and `node75` for cores 3, 6, and 7. The corrected
runs also initialize the pool score from the actual baseline score.

To reproduce a completed run, use a C++17 compiler inside its directory:

```
g++ -O3 -std=c++17 source_search.cpp -o source_search
./source_search ITERATION_SLOTS SEED fresh_run
```

For the interrupted corrected family, compile `search_precise.cpp`
instead. It reads `inputs_precise.hpp`. The delivered logs remain the
record of what was actually executed; reruns are new experiments.
