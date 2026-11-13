# Independent symbolic low-mask population audit

This reviews paired evidence `3db369c56a`. The final Lean theorem
`CompactLowExact.model_population` proves, in every IΣ₁ model, that the cast
of the explicitly defined standard finite-list low mask has binary population
**589083**. It does not assume `support.card=985`: a separate compiled Lean
theorem proves that cardinality from the disjoint intervals and erased index
1, and the final theorem supplies it to the general population lemma. The
arithmetic is `67·8807−985−1=589083`; the last 1 is the additional deficit
at special slot 1063.

The result is about that symbolic list value. The separate finite external
recipe audit checks that a corresponding integer matches the retained MC
bytes, but this pair does **not** prove a Lean equality between those bytes or
the equation's graph port and the list value. It does not establish the
high-mask population, compact44 checker calibration, machine simulation or a
PRA proof.

The read-only audit verifies all six source/object/log/import rows, both full
concrete-mask parent overlays and same-side seeds, exact named axiom reports,
and the independently audited concrete-mask parent chain. The recorded
protected outer session 67237 and all compiler/`--deps` exits are zero;
corresponding objects and logs match. The four named reports per side list
Lean metatheory `propext`, `Classical.choice`, `Quot.sound`; the successful
logs contain no warnings, errors or `sorryAx`. The prelaunch audit is pinned
separately. The terminal record reports launch HEAD
`0a5f299b082b2fb216c6eaaf6557ce81fb9b912e` and removal of three loader
variables before Python; this audit checks that record, not a continuous
external HEAD/environment history.

The inherited Foundation outer-wrapper and complete package-transitive and
dynamic ancestry remain unverified. Sampled RSS is not a hard process-tree
quota; `--deps`/audit subprocess timeouts are not whole-tree resource bounds.
Hashes are point-in-time checks; original `/tmp` object trees are needed.
The audit starts no Lean process.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-low-exact-independent-audit/audit.py
```

Actual read-only audit session 59314 exited 0; see `CHECK.json` and
`terminal-observation.json`.
