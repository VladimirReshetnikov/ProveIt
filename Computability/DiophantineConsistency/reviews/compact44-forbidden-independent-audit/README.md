# Independent compact forbidden-row review

This audits the Lean source from `7c56dfbb7c` and paired replay from
`24f401be94`. The source proves by finite Lean kernel computation that the
943-row Lean table has no row with east color 5 and that a row with west color
5 must be `(5,0,0,0)`. Its indexed theorem then says that if a specified left
row's east color equals a specified current row's west color, the current
row's west color cannot be 5. The theorem requires the matching left row; it
does not construct it or establish the needed boundary or cyclic-wrap cases.

As an additional external cross-check, the independent audit checks all 943
ordered JSON rows: no east color is 5, and the only west-5 row is index 1,
`[5,0,0,0]`. The association between those JSON rows and the Lean table is
provided by the independently rerun 943-table audit and its external ordered
source checker; it is not itself an internal table-to-JSON theorem. This does
not prove the color-relabeling correspondence, model-level tiling existence,
actual compact44 graph obligations, machine simulation, or an iPRA endpoint.

The artifact audit checks packet and source commits, exact receipt and outer
session 24468 exit 0, both source/object/log/seed chains and full inherited
provider overlays, exact direct imports and two zero compiler/`--deps` exits.
It also reruns the audited 943-row parent without compiling Lean. Both
corresponding objects match. The exact successful compiler output reports no
Lean axioms for the two table-wide Boolean lemmas and `propext, Quot.sound`
for each of the two indexed lemmas and matching-left lemma; it has no warnings
or `sorryAx`.

Provider package-transitive and dynamic ancestry are not completely
authenticated, and the inherited provider has no complete printed axiom
inventory. Memory values are samples rather than a process-tree quota;
`--deps` is subject to its subprocess timeout, not a whole-tree guarantee.
The audit uses original `/tmp` artifacts, and replays fail closed if they are
removed or pinned bytes change. Hash checks are point-in-time checks.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-forbidden-independent-audit/audit.py
```

Actual read-only audit session 54140 exited 0; see `CHECK.json` and
`terminal-observation.json`. No Lean compilation was started by this audit.
