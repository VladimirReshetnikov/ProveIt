# Independent heterogeneous-carry review

This reviews source and paired evidence `a863457ff0`, with both compiler logs
added in `b35ed42256`. The theorem is a conditional statement in every model
of IΣ₁, for an **externally finite** index type; the word length itself is a
model element and is not assumed standard. It does not establish any of its
hypotheses for the compact44 graph.

Let the model base be `B=2^w`, word length `n`, and `M=B^n−1`. The explicit
`CarryInput` assumptions are `n>0`, `M>0`, every word `X_i<B^n`, each
radix digit of `X_i` at every `k<n` at most its own cap `D_i`, `F<M`, the
congruence `sum(a_i X_i) mod M = F mod M`, and

```
sum(a_i D_i) + 1 ≤ (b+1)(B−1).
```

The source bounds each word's remainder by `D_i·rep(w,k)`, multiplies by
`a_i` and sums over the external finite family. With the other stated
hypotheses it derives `excess≤b`, defines cyclic carries, and proves for each
model position `k<n` the bound `carry(k)≤b`, output digit bound, and the
exact cyclic digit/carry equations. No inference that graph-specific digit
bounds, weighted mass, congruence, or a clean predecessor hold is included.
In particular the finite fractional-rotation calculation is not an all-model
rotation theorem and does not supply these premises. No machine-simulation or
iPRA proof follows from this packet alone.

The reproducible `audit.py` checks all packet bytes against the follow-up
commit, the recorded outer session 69417 exit 0, both compiled source/object
and retained log hashes, both zero compiler and direct-import exits, exact
named axiom reports, all provider overlay `.olean` objects and the added
scaled-digit seed. It reruns both the independently audited 24-module window
parent and the independently audited scaled-digit parent, with exits 0.
Both source and compiled objects match across the two runs; the four exact
reports `excess_le`, `carry_le`, `carry_column`, and `end_around_carry` list
only `propext`, `Classical.choice`, and `Quot.sound` as Lean metatheoretic
axioms. The final logs contain no warnings or `sorryAx`. The original wrapper
checked report count and allowed axiom sets; this review additionally checks
the declaration names and parses multiline axiom reports.

The inherited parent has no complete printed provider axiom inventory;
package-transitive and dynamic ancestry are not fully authenticated. Reported
RSS is sampled, not a hard process-tree quota; the `--deps` timeout applies to
its subprocess rather than establishing a whole-tree resource bound. This
audit reads the original `/tmp` artifacts and does not run Lean.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-heterogeneous-carry-independent-audit/audit.py
```

The actual audit session 98970 exited 0; see `terminal-observation.json` and
`CHECK.json`. Later changes to pinned files or deletion of the temporary object
trees make a replay fail closed. Hash checks are point-in-time checks.
