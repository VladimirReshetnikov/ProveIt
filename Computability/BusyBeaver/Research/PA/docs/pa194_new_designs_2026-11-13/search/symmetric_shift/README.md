# Targeted symmetric Shift follow-up

The new symmetric cached-Shift parent has 195 controls before identifying
native states 41 and 330. This follow-up exhausts the stated finite local
rewrite rule from that parent and from its 202-control version with the
seven AX folds undone. No 193-state machine was found.

| Starting parent | Merge endpoints | Distinct tables | Best | Queue left |
|---|---|---:|---:|---:|
| 195 | Arithmetic-box endpoints excluded | 3 | 194 | 0 |
| 195 | All working controls except start allowed | 3 | 194 | 0 |
| 202 | All working controls except start allowed | 576 | 194 | 0 |

Every search uses all-tape abstract reachable 11-cell windows at native
start state 74, a 300-step local bound, and pairwise identification with
arbitrary first actions. These results concern this sufficient rewrite rule
only; they are not a state lower bound. Positive construction certification
is provided separately in the symmetric-Shift machine package.

The first retained fold removes 41, keeps 330, and gives state 330 actions
`0 L 31` and `1 L 46`. This is the same fold found independently by the
source-construction agent. Four 194-state tables occur in the 202-parent
closure. Every closure queue was exhausted, and no 10,000-table cap was hit.

`summary.json` records exact identities and counts. The 202-parent input
retains the 67 unfused AX readers and substitutes the new 135-control fixed
part. Applying the original seven jointly checked AX folds reconstructs
the 195-parent table exactly; all 28 two-cell cases were rechecked.

To repeat from this directory:

```sh
g++ -O3 -std=c++17 action_merge.cpp -o action_merge
g++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
python3 quotients.py parent195.native.tm original_endpoint_policy 10000
python3 quotients_all.py parent195.native.tm all_endpoints 10000
python3 quotients_all.py parent202.native.tm all_unfolded 10000
```

These scripts derive from the primary PA194 packet's local-action merger
and quotient enumerator, with the step bound increased and an additional
version permitting arithmetic controls as merge endpoints. Original license
notices are retained. This follow-up is separate from the earlier frozen
search ledger and does not change its counts.
