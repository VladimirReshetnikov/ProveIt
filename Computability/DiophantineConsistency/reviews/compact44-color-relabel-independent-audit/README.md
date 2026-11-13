# Independent finite 942-to-943 relabeling audit

This is an external finite check of `check.py` and `receipt.json` from
`7c56dfbb7c`. It does not prove the relabeling in Lean, prove existence of a
matching left neighbor, discharge graph boundary or wrap conditions, simulate
a machine in arbitrary models, bind the compact44 ports, or prove iPRA
provability. The separately compiled local exclusion theorem and its audit
`dea34b76f6` retain their matching-left premise.

The independent script pins the old Lean action cache, old table source,
state permutation, dense action JSON, compact ordered 943-row JSON, and the
original checker and receipt. It parses the two literal old `targetList`s and
both 216-entry `railCache`s directly from the old Lean source, checks their
agreement with all 430 old actions and the rail cardinality formula at every
cache index, and checks all 430 action conjugacies under the complete 215-state
permutation. This takes a different route from the original checker's computed
target ranks. The script manually transcribes the ordered-row family formulas
from the pinned `WangTiles942TableData.lean`; it is not a general Lean parser
or a Lean proof of equivalence with those definitions.

It reconstructs all 942 old indexed rows, the complete horizontal permutation
on 250 colors and vertical permutation on 439 colors, checks both are
bijections, translates every old row, and compares every state/color/row
permutation with the retained receipt. The translated rows are exactly compact
indices `{0} ∪ {2,…,942}`; start index 0 is preserved and the sole additional
compact row is index 1 `(5,0,0,0)`. The 943 compact rows have no east color
5 and only index 1 has west color 5. Accordingly the extra row is excluded
only when an actually matching left row is supplied.

From the repository root run:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-color-relabel-independent-audit/audit.py
python3 -O -I -S Computability/DiophantineConsistency/reviews/compact44-color-relabel-independent-audit/audit.py
```

Both actual independent commands exited 0 and produced the same
`CHECK.json` result. Each also ran the original checker in normal mode
(exit 0, exact receipt) and optimized mode (exit 1, explicit fail-closed
message). The independent script uses explicit checks in either mode and
rehashes its inputs afterward; this gives point-in-time drift detection, not
continuous protection. No Lean compilation is performed.
