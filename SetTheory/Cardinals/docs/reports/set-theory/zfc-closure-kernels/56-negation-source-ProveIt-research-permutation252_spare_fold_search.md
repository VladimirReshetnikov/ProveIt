# Folding box states while forgetting spare values

The runtime relation permits an arbitrary valid spare suffix. Earlier mutation
searches froze all55 rows in an intentionally conservative box footprint and
compared the original suffix effects exactly. This experiment instead tests
folds of those excluded states, with only the first nine register values fixed
and any valid finite spare suffix accepted. Every sampled box transition is
literal; the sample phase uses no register-box oracle.

There are29 eligible deleted labels: the protected box states and their target
labels, except the actual blank start64 and dispatcher96. Redirecting each to
any of251 other working states gives7,279 recipes. Four operations at each of
nine register indices, five primary vectors, and three spare vectors give540
baseline samples. Values include0,1,2; spares include empty, `[0]`, and
`[2,0,1]`. Every sample checks the entire nine-register prefix, unchanged left
context, exact relocated return state at its first leftward boundary exit,
and the complete remaining spare-block shape, with exterior blank implicit.
The initial left context is fixed at one header and two separated bits; this
is finite testing, not universal quantification over left contexts or values.

All540 baseline samples passed. All7,279 recipes completed in the90-second
search allowance, taking about10.3seconds including the later affine screen.
There were294,661 candidate sample executions, bounded by1,000 literal moves
per sample. The519 sample survivors comprise:

| Deleted state | Number of alternative targets |
| --- | ---: |
| 3 | 3 |
| 6 | 11 |
| 7 | 251 |
| 9 | 251 |
| 48 | 3 |

States7 and9 lie outside the sampled box bodies, so all of their targets pass
that first stage. The remaining survivors merge box return states. Their
proposed macro outputs can therefore be relocated without deleting a macro
entry state. The second stage runs the attributed strict affine instruction
checker with those **proposed** output contracts, after checking all8,391
baseline cases. It performs913 candidate checks before rejecting every one
of the519 candidates. No altered table is given a blank run.

These conditional screens do not establish any changed unbounded box
contract. Fuel exhaustion and the fixed first-exit restriction can exclude a
machine that would work under a different simulation relation. The result is
no survivor in this particular diagnostic family, not a251-state lower bound.
The frozen252 table is never edited. The promising general idea—charge only
semantic register data, allow disposable tape data to change—remains available
to multirow rewrites or different boundary relations.

The [driver](permutation252_spare_fold_search.py) and [record](results/permutation252-spare-fold-search.json)
include every first failing sample, every conditional runtime failure, exact
source identities, bounds and attribution. Run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_spare_fold_search.py \
  --output /tmp/permutation252-spare-fold-search.json --seconds 90
```

Attribution: Mira-Cult's original machine, Jeff's verification, Wade's compiler,
mira-emmy's public253 reduction and the ProveIt register-permutation candidate.
The conditional executor is the unchanged closure-kernel source27 checker.
