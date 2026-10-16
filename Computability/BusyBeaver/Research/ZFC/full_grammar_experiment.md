# Overlap-safe grammar search on the complete frontend

The bounded comparison **matches 269 states and does not improve it**. It keeps
the original equality logic, CP/GIC theory, both atomic vacuity arms, four-tag
formula coding, parameter reads, gates and cleanup. This is a complete original
source frontend, distinct from the retired reduced equality-free calculi.
The public Wade binary compiler and blank initializer remain unproved interfaces.

`full_grammar_experiment.py` applies the overlap-safe pair counting introduced
in the batch 147 experiment to both full-word tokenizations:

- source 08's 185-token word of closed source subroutines;
- batch 148's 186-token expansion into 17 primitive macro roots.

Their further expansions are checked to be exactly the original macro word.
The original symbolic contract checks GEN, all eight original logical rows,
the old nonlogical bundle, both vacuity types and cleanup. Every retained
subroutine is checked closed with respect to escaping break/continue levels.

For seeds 0–1999 and frequency exponents 1, 2, 4, 8, each tokenization receives 8,000
overlap-safe grammars and 8,000 paired legacy grammars. The full comparison thus
evaluates 32,000 DAGs. Two disjoint seed ranges took 117.2 seconds combined in the
recorded environment. Search results are in `full-grammar-safe-results.json`.

The table entries are minimum **decision-node counts**, before the fixed 62-state
framework cost:

| Tokenization | Exponent | Overlap-safe | Legacy |
|---|---:|---:|---:|
| Coarse 185 | 1 | 209 | 209 |
| Coarse 185 | 2 | 208 | 209 |
| Coarse 185 | 4 | 207 | 207 |
| Coarse 185 | 8 | 207 | 207 |
| Expanded 186 | 1 | 211 | 211 |
| Expanded 186 | 2 | 210 | 209 |
| Expanded 186 | 4 | 208 | 208 |
| Expanded 186 | 8 | 208 | 208 |

The correction changes actual results. An equal-token run can have a larger
overlapping adjacency count than the number of disjoint replacements. The old
algorithm can choose a pair with only one disjoint occurrence and stop while
other reusable pairs remain. The new algorithm weights actual replacement
counts and excludes those unusable choices. A small explicit negative control
checks this difference. Across the 16,000 paired samples, 13,473 grammar outputs
and 10,078 node counts differ: the safe version is smaller 6,125 times and the
legacy version 3,953 times. The random choices change when weights change, so
the correction does not give pointwise cost monotonicity. The best sampled
state count remains 269, and none of these minima is a lower bound.

The selected safe winner uses the coarse word, exponent 4, seed 209, 26 grammar
productions and 77 residual tokens. Actual backend compilation checks
**207 decision +62 framework =269 working states**. The named source has 537
rows, and its sole `1.inc/read1` missing transition is totalized with
write1/R/halt to 538 rows. Standard numbering starts at 0 and halts at 269.
The total-table SHA-256 is
`bb595d66d852ae3e34f7720e31d79d0b890b15a0db6b1c54e0562efebd4577d8`.
Artifacts remain outside the checkout because this does not improve prior 269.

An independent source 08 checker validates the original 219-node/candidate 207
operation relation: 4,533 pairs, 2,601 increments, 1,931 decrements and 1 halt,
including both decrement branches. Contracted control paths have length at
most 4. Six mutations are rejected, including wrong zero/positive exits and
wrong entry. This finite certificate supports register-level halting
equivalence from equal registers; it is not a binary-interpreter theorem.

The fast recipe independently regenerates the same seven program artifacts
as the full search. A conservative audit of the total table finds all 269
working states graph-reachable, 269 singleton exact-bisimulation classes after
12 rounds, and no radius 4/64-step safe merge. The 11 auditor regressions pass.
No blank-run prefix is needed for these finite transformation checks.

Run the fast fixed recipe from the repository root:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/full_grammar_experiment.py \
  --output /tmp/zfc-complete-safe-fixed --start-seed 209 --seeds 1 --exponents 4
```

To reproduce the full bounded comparison, use `--start-seed 0 --seeds 2000`
with `--compare-legacy` and the default four exponents. The output includes
both DAGs, the exact grammar, operation certificate, independently checked
result, rejected mutations, named/total tables and relabelling. All outputs
must be outside the checkout.

The script reuses the **unchanged, attributed source 08** grammar transformer,
path engine and independent verifier at
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-{rebracket_axioms,verify_rm_certificate}.py`.
The public backend and original program come from the immutable imported
upstream `297ab8df7e5de329605c3875b4934643b371a5e3`. Andrew James Wade's
backend license and Mira-Cult/Jeff attribution are retained. No new vendor
snapshot, Lean build or claimed ZFC endpoint accompanies this experiment.

Batch149 source19 subsequently supplies a **268-state** complete-logic control
by changing the theory's conjunction layout before grammar search. This does
not change the negative result above, which fixes the original word. Its
independently reproduced53,760-choice grid retains all eight logical rows,
both atomic vacuity components and the62-state framework. Its separate ordinary
source bridge uses relative conjunction commutation/association and context
lifting, without assuming F=false. The operation certificate compares the
revised217-node reference with206 nodes, not the original219-node reference.
The next comparison applies overlap-safe counting to that revised word;
[intake149](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch-149-binding-certificates-and-shared-substitution)
records its artifacts, attribution and remaining proof obligations.
