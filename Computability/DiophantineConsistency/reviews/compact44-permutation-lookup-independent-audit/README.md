# Independent generic permutation lookup audit

This reviews the paired source/evidence `f914244f1f`. Given a **standard
finite** Lean list `xs` and a proof `xs.Perm (List.range n)`, the source first
constructs an index equivalence preserving lookup. In any model `V` of IΣ₁ it
then proves:

- if model indices `i,j` are below the standard list length and
  `tabValue xs 0 i = tabValue xs 0 j`, then `i=j`;
- for any model value `a<n`, there is an index `i<xs.length` with
  `tabValue xs 0 i=a`.

The standard list length and `n` are external Lean naturals; the bounded model
indices are converted to standard numerals using the existing model lemma.
This does not assert that all model naturals are standard. The required list
permutation is an explicit hypothesis. The theorem does not instantiate the
compact horizontal/vertical arrays, address the omitted 943rd row index,
prove matching neighbors or wrap, transport an arbitrary model tiling,
calibrate compact44, or construct an iPRA derivation.

The read-only artifact audit checks both source/object/log/dependency rows,
full same-side 342-module parent overlays, all 30 direct-companion guards,
exact same-side direct imports and four named axiom reports, and reruns the
independent endpoint parent audit. Outer session 56475 and both compiler and
`--deps` queries are recorded as exit 0; the paired objects match. The four
reports list Lean metatheory `propext`, `Classical.choice`, `Quot.sound`.
Neither actual compiler log contains a warning, error or `sorryAx`. The
original wrapper rejects compiler errors and `sorryAx` but does not itself
reject warnings; the no-warning observation here comes from independent log
inspection, not from that guard.

The inherited Foundation outer-wrapper and package-transitive/dynamic
ancestry limits remain. RSS is sampled, not a hard process-tree quota, and
`--deps`/audit subprocess timeouts are not whole-tree resource bounds. The
recorded clean-loader command and outer exit are checked as observations;
source/provider hashes are point-in-time checks. Original `/tmp` objects are
needed to rerun this audit, which performs no Lean compilation.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-permutation-lookup-independent-audit/audit.py
```

Actual read-only audit session 91505 exited 0; see `CHECK.json` and
`terminal-observation.json`.
