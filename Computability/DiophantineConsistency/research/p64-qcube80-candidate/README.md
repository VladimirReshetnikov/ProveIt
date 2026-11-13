# P64 q-cube absorption: 14 positive variables and 80 operations

Starting with the checked 81-operation q-cube graph, let `r0 = rho + s` and
replace its first residual

```
A0 = (ell + rho + s)^2 - (ell * (ell + k) + 1)
```

by `A0 = (ell + r0)^2 - (ell * (ell + k) + 1)`, with `r0` a separate
positive coordinate. All other graph gates and all other coordinates remain
unchanged. The resulting graph has 80 live gates, comprising 42 multiplications,
22 additions and 16 subtractions, and 14 positive witness variables. Forward
substitution from any positive 81 tuple is immediate at the algebra level.
For the converse, the checked [actual-zero remainder theorem](../fourteen-p64-qcube80-gap-draft/README.md)
establishes `r0 > s`, allowing the positive witness `rho = r0 - s`.
The checked [positive-zero equivalence](../fourteen-p64-qcube80-existence-draft/README.md)
proves both directions for arbitrary natural ports in the stated IΣ₁ models.
The [iPRA endpoint client](../p64-qcube80-ipra-draft/README.md) checks the
native, standard and equality-only proof-existence statements for the Lean
graph at the symbolic compact44 ports, using the selected mapped Foundation
refutation negation. These checks use captured providers and do not establish
the complete transitive source-to-object ancestry or a formal identification
of the retained payload and display with the Lean graph. No change to
`equation.tex` or `equation.pdf` is claimed here.

## Evidence and scope

[`build.py`](build.py) checks the exact changed first-residual polynomial
identity under `r0 = rho+s`, that the remaining 79 graph rows are exactly the
corresponding parent rows, that every gate and input reaches the output, and
600 deterministic modular comparisons of all five residuals and output. It
also reruns the pinned P64 polynomial verifier’s four residual identities
and computes symbolic leading forms using its polynomial machinery. The residual degrees are 12, 34, 22, 23 and 2; the output has degree
68 when `beta != 0`, with leading homogeneous form

```
64 * beta^46 * J^46 * w^4 * s^14 * (eta+zeta)^2 * gamma^2.
```

These external symbolic and finite checks do not themselves prove the Lean
equivalence described above or the external JSON's relationship to the object
language. They do not establish global minimality.

[`generate_lean.py`](generate_lean.py) transcribes the 80 gate rows to
[`P64QCube80.lean`](P64QCube80.lean). The guarded Lean compilation in
[`lean-check.json`](lean-check.json) exited 0 with empty output, and checked
source, Lean executable, and direct `P64Graph` object hashes before and after.
It proves only that the generated definition elaborates. The complete
transitive source/object, package, dynamic-loading and search-path ancestry of
the captured providers was not independently audited by this compilation.

Recheck the deterministic external construction and transcription with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube80-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube80-candidate/generate_lean.py
```

The compiler receipt is produced by `check_lean.py`, which refuses to
overwrite existing outputs and uses explicitly named temporary providers; a
repeat requires a fresh output/receipt location in a copy of the runner.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `8f2c5953879cc6f4f10a1b1d8024906d7c5f81760351521bd27d6a67ab50948e` |
| `graph.json` | `50e65396385a108eb340a7d117ce490e7ae671452acb5df3574f61b75aeb8825` |
| `checks.json` | `5cfd7bd327e786be24a7b5f59e254c59e0921d26b857b7b5739f0d2debcd237a` |
| `generate_lean.py` | `4c3fb48c6320b3c1fcc82ae50b008eb3465cf257137ca236edc88edcfb4a07a9` |
| `P64QCube80.lean` | `00336034317938068f49c8e4a05dc919155f7d397e4ed7d41db0a0f73dc68168` |
| `check_lean.py` | `a5921be0076e8f8c4ac1f8c0d96d574f61df95e9c14e05e01c2b7f0fe54a81ba` |
| `lean-check.json` | `a67035749ef4e4374caedb7353d758c1d627f3ad0908259a8fb4bffe5c0ee007` |
| `/tmp/P64QCube80.olean` | `e8829517e10e4c3d2423594dd884b86466834d7714038660030d16861c8abd68` |
