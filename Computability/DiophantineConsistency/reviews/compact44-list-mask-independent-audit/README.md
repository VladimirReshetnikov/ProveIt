# Independent generic finite-list mask review

This reviews the paired packet `e86fdb8ad6` and its exact source
`CompactListMask.lean`. For a standard natural base `B≥4`, finite set `S`,
length `len`, and arbitrary `special`, its `digit` function is `B−4` at
`special`, `B−2` at other members of `S`, and `B−1` elsewhere. `defect`
is respectively 3, 1, or 0. The checked Lean theorem states

```
Nat.ofDigits B (digits B len special S)
  + ∑ j ∈ range len, defect special S j * B^j + 1 = B^len.
```

The special case is checked first even when `special ∉ S` or is outside the
list; there is no hidden support-membership premise. The proof derives the
finite `ofDigits` sum and geometric identity by external induction on the
standard length. The model theorems apply to **the cast of this particular
standard-list value** in any model of IΣ₁: every digit at an index below the
standard `len` is one of `2^67−1`, `2^67−2`, or `2^67−4`, and the value is
below `2^(67·len)` in that model. If `0<len`, `special≠0`, and `0∈S`, the
origin digit is exactly `2^67−2`. The proof uses `eq_nat_of_lt_nat` to bring
an index below standard `len` back to a standard index; it does not establish a
general nonstandard-length list construction.

The source does not choose the concrete 986-position support or identify its
weighted defect with the retained MC value or actual graph port. It does not
supply the graph's no-carry hypotheses, machine semantics, or an iPRA
provability result. The separate finite Python recipe check does not itself
transport equality into all models.

The read-only `audit.py` verifies all committed packet files against the
exact commit, the reported outer session 18605 exit 0, both compiler and
`--deps` exits, the source/object/log hashes, the full two parent overlays,
the exact direct imports, and four named axiom reports. Both corresponding
objects match. Each report lists the Lean metatheoretic axioms
`propext, Classical.choice, Quot.sound`; the compiler logs contain no warnings
or `sorryAx`. It independently reruns the pinned 342-module endpoint successor
parent audit. The record of failed exploratory attempts is retained in the
reviewed packet; the `sorryAx` appearing in their failed logs is not part of
the final successful compiler logs. Parent-provider limitations remain:
package-transitive and dynamic ancestry are not completely authenticated,
sampled resource usage is not a hard process-tree quota, and the wrapper's
`--deps` timeout is not a whole-process-tree resource guarantee.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-list-mask-independent-audit/audit.py
```

The audit reads the original `/tmp` artifacts. Their removal or any later
change to pinned packet inputs causes a fail-closed result; its output is a
point-in-time artifact check, not a continuous integrity guarantee. It does
not launch Lean or rerun the paired compilation.
