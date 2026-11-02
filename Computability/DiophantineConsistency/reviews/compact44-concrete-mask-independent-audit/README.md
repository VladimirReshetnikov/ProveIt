# Independent concrete mask review

This audits the paired packet `20b9a0a28d`. The Lean source defines a finite
support as the union of `[0,943)`, `[983,993)`, `[1003,1012)`,
`[1013,1032)` and `{1063,1064,1095,2195,3296}`, with 1 removed. It proves
that the support is below 8807 and contains 0 and 1063, and specializes the
previous generic finite-list defect identity to prove

```
Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support)
  = 2^590069 − 1 − ∑ j ∈ support, 2^(67*j) − 2·2^(67·1063).
```

The special slot 1063 therefore contributes three weighted units in total,
and position 1 contributes none. The standard Lean natural-number list
value's cast into each IΣ₁ model has all digits at model indices below 8807 in
`{2^67−1, 2^67−2, 2^67−4}`, is below `2^(67·8807)`, and has origin digit
`2^67−2`. These are statements about the cast of the explicit list value.

The independently rerun external support/defect check `aabfd87212` confirms
the recipe support before erasing 1 has these same intervals and singleton
positions, and that the external retained MC integer satisfies the same
finite defect expression. **This external byte comparison is not a Lean
proof equating the list value with retained MC bytes, a graph port, or any
equation input literal.** Nor does this result establish graph no-carry
premises, model-level transport, machine semantics, or iPRA provability.

The read-only artifact audit checks all committed packet files, both reported
compiler and `--deps` exits, complete paired provider overlay inventories,
source/object/log and `CompactListMask` seed hashes, exact direct imports,
and five exact named axiom reports. Both runs' objects match; all five
reports contain `propext`, `Classical.choice`, `Quot.sound`, with no warning
or `sorryAx` in the successful logs. The independent generic finite-list
parent audit is rerun, including its own 342-module endpoint parent audit.
The original wrapper's outer session 23362 is recorded as exit 0. Failed
exploratory source/log history remains in the packet and does not establish a
successful theorem.

The inherited provider has no complete printed axiom inventory, and
package-transitive and dynamic ancestry are not fully authenticated. RSS is
sampled rather than a process-tree quota; a dependency subprocess timeout is
not a whole-tree resource guarantee. The audit reads the original `/tmp`
artifacts and launches no Lean compiler. Hashes are point-in-time checks.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-concrete-mask-independent-audit/audit.py
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-support-defect-independent-audit/audit.py
```

Actual artifact audit session 59649 and the separate support check each exited
0; see `CHECK.json` and `terminal-observation.json`.
