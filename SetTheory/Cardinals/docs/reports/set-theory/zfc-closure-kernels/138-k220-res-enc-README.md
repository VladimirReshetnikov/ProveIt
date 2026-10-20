# Supplemental engine and encoding experiments

This directory records complementary research on the original K221 machine.
The accepted K220 machine is provided by the main construction packet. **The
two state-deletion patches reconstructed here are rejected examples, not valid
K220 constructions.**

`encoding_report.tex` is a report section suitable for inclusion in the main
LaTeX document. `receipts/` contains compact finite-search outcomes and exact
counterexample data. `traces/` contains five short native-transition CSV files.
`scripts/` reproduces the specified experiments using the original extracted
K221 packet. The baseline table and source hashes are enforced by
`scripts/context.py`.

## Inputs and output

Use Python 3.10 or newer. Extract the original `K221_Construction_2026-10-20`
packet and set `K221_BASE` to its absolute path. Run the following commands from
this supplement's directory. No third-party Python packages are needed.

```sh
export K221_BASE=/absolute/path/to/K221_Construction_2026-10-20
python scripts/counterexamples.py
python scripts/rows/exhaustive.py
python scripts/rows/row_order_atoms.py
```

Generated files go to `generated/`. Set `ENCODING_OUTPUT` to choose another
output directory. The supplied `receipts/` and `traces/` are retained research
records; a replay writes separately and does not replace them.

The first command reproduces a 662-step valid-frame failure of the proposed
state-50 deletion, a 2,010-step valid-frame failure of the proposed state-198
deletion, and its exact 76-step blank-start entry into a provably divergent
rightward ray. The baseline comparison traces have 586 and 602 transitions.

The next two commands exhaust, respectively, all 1,679,616 fixed-shape joint
row parameter permutations and all 40,320 row orders with a fixed binary
concatenation shape over closed atoms. Their exact optimum is 208 distinct
source subtrees. The parameter search has two minimizers; the order search
has one. This is a source grammar objective, not a proof that no such variant
could compile below 221 states using a different decoder.

These three commands and the all-one-spare usage audit below were freshly
replayed after the scripts were made portable. Wall-clock times in receipts are historical diagnostics and need not
match another run. Ordered counts, optima, counterexample tapes, and trace
hashes are the reproducible results.

## Additional finite experiments

To reproduce bounded local fold searches:

```sh
python scripts/local_folds/invariant_search.py 3
python scripts/local_folds/invariant_search.py 5
python scripts/local_folds/invariant_search.py 7
python scripts/local_folds/fold_engine.py 3
python scripts/local_folds/fold_engine.py 5
python scripts/local_folds/fold_engine.py 7
python scripts/local_folds/fold_all.py 5
python scripts/local_folds/pair_selection.py
python scripts/local_folds/double_fold.py
python scripts/local_folds/double_fold_nonpure.py
python scripts/local_folds/shifted_folds.py
```

The invariant scripts compute finite-window overapproximations of initialized
reachability. Positive replacement blocks must leave the same tape, head, and
quotient state. They may not inspect the unknown exterior of their represented
window. The one-row families keep one common branch; the two-row families have
disjoint admitted windows and restrict revisits to the merged state. The
head-shift family adds a two-cell displacement and reverses the affected
incoming moves. Replacement lengths are at most 21, or 23 for head shifts.
Counters measure individual row-action choices, not complete distinct tables.
All reported searches act on the unchanged K221 encoding and found no fold.
The precise loops and early filters in the scripts define the finite scope.

The remaining scripts reproduce smaller experiments:

```sh
python scripts/rows/search.py
python scripts/rows/order35.py
python scripts/rows/swap_u.py
python scripts/local_folds/super66.py
python scripts/local_folds/commute_blocks.py
python scripts/spare_usage.py
python scripts/spare_usage.py --uniform
```

`rows/search.py` tests 48 individual emitter permutations. `rows/order35.py`
exchanges the equal-length rho3 and rho5 emitters, then repeats all 6^8 joint
parameter permutations. `rows/swap_u.py` tests 12 specified rho8 fourth-argument
splice variants. The row binding files record exact source ordinal intervals
and macro matches. The final two commands rerun the original K221 unbounded
symbolic engine for source-interface transition usage, with and without the
all-one spare specialization. Their row-usage conclusion is not a claim that
each transition occurs on the single initialized blank run.

## Proof boundaries

The accepted K220 proof is checked elsewhere in the main packet. None of the
negative searches here establishes a global state lower bound. In particular,
they do not exhaust all source layouts, all helper compositions, all coupled
row rewrites, or all parenthesizations of reordered emitters. Register
coalescing was not investigated to completion. Source-interface counterexamples
are identified as such; only the short state-198 divergence certificate starts
from the required blank tape.

## Attribution

These experiments adapt the pinned K221 compiler, source-language definitions,
and runtime verifier in Vladimir Reshetnikov's ProveIt research packet. The
underlying consistency construction and prior attribution are retained in
`licenses/K221_NOTICE.md`; the original repository license is copied in
`licenses/ProveIt_LICENSE`. New research prose and scripts use the MIT No
Attribution terms in `LICENSE`. Existing third-party terms are not replaced.

The main construction packet includes a separate independent runtime auditor
and its receipt; those checks are not substitutes for freshly replaying the
symbolic induction driver.
