# Extending the finite K219 equality search

These experiments found no smaller source or machine. They complete two
additional families in Source 140's finite-signature search, recover every
reported root, and measure the smallest resulting sources. The accepted
[219-state construction](../candidate-k219/README.md) is unchanged.

## Search and its limits

The submitted search uses 14 literal fragments, observations on counter
values 0–9, and semantic deduplication. Its cost counts binary compositions
of library fragments before shared subtrees are identified. Its published
cost-seven run skipped the cost-six intermediate layer and found the 16
previously studied routines. We retain the same fragment library and the
same intermediate layers through cost five, containing 377,821 stored nodes.

| New root cost | Eligible child costs | Root pairs tested | Root hits on inputs 0–4 |
| --- | --- | ---: | ---: |
| 6 | 0+5, 1+4, 2+3, 3+2, 4+1, 5+0 | 18,258,114 | 0 |
| 8 | 2+5, 3+4, 4+3, 5+2 | 657,253,656 | 263 |

Each child-cost sum receives one additional composition for the root.
Cost eight does **not** include 0+7, 1+6, 6+1 or 7+0: those intermediate
layers were not generated. Semantic deduplication may also discard a
structurally useful equivalent tree. Unknown overflow and loop observations
are merged by the original finite signatures. Consequently even a completed
family is not an exhaustive syntactic search or a lower bound.

The cost-six process finished in 6.677 seconds. The first cost-eight process
hit its 110-second internal wall limit before evaluating trial 511,455,232.
The successor skips preceding root trials and starts at that exact index;
it completed the remaining family in 54.870 seconds. Its intermediate-node
stream matches the first process byte for byte. The two root intervals are
disjoint and consecutive, with 227 and 36 hits. Each invocation also had a
120-second external timeout. The original 800,000-node cap was not reached.

The exact executed [first search](search.cpp), [resuming search](search-resume.cpp),
logs and process outcomes are retained. [Provenance](provenance.json) records
the input hashes, trial intervals and exact output-stream hashes. To avoid
storing the same six-megabyte prefix three times, the shared node stream is
stored once under `results/`, compressed without modification; appending
each run's root lines reconstructs its exact original output.

## Independent finite diagnostics and actual source cost

Each recovered root replaces the four exact accepted equality occurrences.
Both whole-source control-flow resolvers agree for all 263 resulting sources.
The separately written Source 140 CFG simulator tests all 256 pairs through
15 and five boundary/large pairs: `(0,100)`, `(100,0)`, `(100,100)`, `(99,100)`
and `(100,99)`. Other registers start nonzero and must be preserved; both
operands must finish zero, with normal exit exactly on equality.

| Whole-source distinct subtrees | Finite passes | Finite failures |
| ---: | ---: | ---: |
| 207 | 17 | 0 |
| 208 | 225 | 21 |

The [complete diagnostics](results/analysis.json) retain every macro and the
first failing input where applicable. These 261-pair checks do **not** prove
termination or correctness for arbitrary natural operands. No new routine
here has an all-natural contract. The accepted source has 206 distinct
subtrees, so none improves its source census.

## Compiler measurements

The 17 smallest sources were separately measured using the existing K219
allocator. Both compiler identity controls reproduce all 438 accepted rows.
Seven sources pass strict decoder-prefix binding: three use 220 raw states
and four use 221. Four others need a right-child CI6 entry; the separately
labeled hypothesis `1 R 13` gives 221 states for each. Five are rejected for
a missing right-child CD5 entry and one for a missing right-child CC3 entry.

The [allocation result](results/allocations.json) and
[exact output archive](results/allocations.tar.gz) retain all 17 source files,
21 attempts, 11 raw tables, controls, and the executed measurement script.
This batch used the first partition's diagnostic file, retained inside the
archive. Completing the second partition adds no further 207-node source.
No primitive runtime, startup, or consistency calibration was claimed for
these tables; the smallest raw result is 220 states.

## Reproduce the recorded finite checks

From the repository root, with assertions enabled:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-equality-extension/replay.py \
  --output /tmp/k219-equality-extension-fresh
```

This reconstructs and hashes all three original search outputs, rebuilds
the 263 macros, rechecks literal replacement and both CFG resolvers, repeats
the finite diagnostics, and emits the 17 smallest source files. It does not
repeat the discovery search or run any machine verifier. The original
workspace-dependent analysis scripts are preserved under `history/`; the
portable replay is the supported entry point.

Attribution: the fragment library, finite-signature C++ search and independent
CFG verifier are Source 140 contributions from commit `26d5de6d21`; see the
[accepted construction's attribution](../candidate-k219/ATTRIBUTION.md).
The bounded root-six/root-eight extension, partition reconciliation and
source reconstruction are follow-up work by root on 20 October 2026.
The separate allocation batch was performed by `review_upstream_reflection`.
