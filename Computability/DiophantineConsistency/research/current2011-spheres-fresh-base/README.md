# Fresh-base iPRA endpoints for the 71/80 and 72/68 spheres

`FreshCarrierSpheres.lean` checks, for each of the two current-port expressions, both a same-valuation equivalence of their positive-shifted zero predicate with `ObjectCurrentEquation2011.naturalExpression` in every model of IΣ₁ and a standard-iPRA derivation of its no-zero sentence iff the intuitionistic negation of the mapped native ZFC-refutation sentence. These are existential Lean proofs of internal derivability; they do not assert that ZFC is consistent. The iPRA endpoint uses the mapped refutation statement as defined by the checked provider; a Gödel–Gentzen consistency formulation is a separate corollary.

The generic ordered-ring proof and syntax are adapted from `Lean/DiophantineConsistency/ModelCarrierSpheres.lean`: the current-base client imports `FreshModel106`, uses its model positivity and 65-expression evaluation theorems, and assembles the bridge directly from the current14 polynomial bridge. The generic proof applies `ModelArithmetic`'s IΣ₁-model near-square, consecutive-norm and mod-four facts, rather than treating an integer-only theorem as a model theorem. Both formulas use `CurrentWindowCarry2011.ports` and the same 14 positive coordinates as the current parent.

`bind_graphs.py` independently parses the actual source's `frontAt` and both final expressions and compares their entire expression DAGs to the pinned 71-row and 72-row JSON graphs modulo associativity and commutativity. It checks all 21 named intermediate cuts, row/input liveness, and a changed-witness negative control. `binding-result.json` records its successful isolated-Python run. This comparison is an external syntactic check; the Lean theorems are about `expressionAt71` and `expressionAt72`, and the comparison does not prove a PDF binding or port-byte identity in Lean.

The separate existing finite artifacts [`polynomial71.json`](../fourteen-nonzero-spheres/polynomial71.json), [`polynomial72.json`](../fourteen-nonzero-spheres/polynomial72.json), [`CERTIFICATE.json`](../fourteen-nonzero-spheres/CERTIFICATE.json) and [`audit.py`](../fourteen-nonzero-spheres/audit.py) report 71 operations / degree 80 and 72 operations / degree 68, and bind the current2011 four integer-port bytes. These count and degree statements are not Lean total-degree theorems. See that packet for the finite audit's exact assumptions and provenance. This packet does not change the maintained 65/150 PDF or claim a global minimum.

## Retained checks

Attempt01 has Lean exit 0 and all four axiom reports, but the outer guard returned exit 1 because two unused ordered-ring assumptions triggered warnings. Its exact source and logs are retained. Attempt02 changes only the evaluator section to require `[CommRing R]`; outer session 31123 and Lean both exited 0, no warnings or `sorryAx`, 233 recorded stable guard slots, 56 RSS samples and no stop. Its four reports contain `[propext, Classical.choice, Quot.sound]`. The output `/tmp/current2011-spheres-fresh-base-priority-check02/FreshCarrierSpheres.olean` has SHA-256 `37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020`.

The guarded command uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, a sampled 3.5-GiB process-group RSS stop, and a 10-GiB available-host-memory stop. `attempt02/result.json` captures child exit and guard data; `attempt02/outer-observation.json` records the actual outer terminal exit separately. The direct `FreshModel106` provider SHA-256 is `d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942`; its own source and recorded producer dependency/companion/shadow slots are rechecked before and after. The guard does not trace every transitive dynamic load, rebuild the fresh base, or retroactively apply its limits to the producers. The fresh extension build's first final client failed; the corrected separate producer passed, with captured input guards.

From the repository root, the read-only binding audit is:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-spheres-fresh-base/bind_graphs.py
```

The checker pins the exact source and both graph bytes. To reproduce the Lean check, inspect and use `check02.py` with its fixed input paths and an absent output path.

| Artifact | SHA-256 |
| --- | --- |
| `FreshCarrierSpheres.lean` | `a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5` |
| `check02.py` | `c39d7551394fb32a02f36017145f52ce8016072517f7398d12c6ba462dea035d` |
| `attempt02/result.json` | `67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9` |
| `attempt02/compile.log` | `0add61f4cb95515a1541d4f206f7ea00357f33e67a5300e9e9085203a6af790e` |
| `bind_graphs.py` | `ad6eb9e2d99a17bd23baa0ea94e18c3e47ee40673472f930be3365a6f2b87452` |
| `binding-result.json` | `d46e0bc55e41538da7414b56d20745a46588e5ab8220a1d4cd3cbe5801e3f3b1` |
| `polynomial71.json` | `937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2` |
| `polynomial72.json` | `70d6bd4ab1f4d4a868a4718543502734d250fca6a38eb64a5b90dda8107b3280` |
| `CERTIFICATE.json` | `99a901c08cd45b549a638ddd051ce80a0bf7a833231b52bc2b29d5390feb37ec` |
