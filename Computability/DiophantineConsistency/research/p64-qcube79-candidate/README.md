# P64 first-root candidate: 14 positive variables and 79 operations

Starting from the 80-operation q-cube graph, replace its positive witness
`r0` by an independent positive first-root witness `t`, and change
`first_unscaled_square = (ell+r0)*(ell+r0)` to
`first_unscaled_square = t*t`. The `ell+r0` gate is then eliminated; the
first residual becomes `A0 = t² - (ell*(ell+k)+1)`. All other gates and
coordinates are retained. The graph has 79 live gates: 42 multiplications,
21 additions and 16 subtractions, with 14 positive witness variables.

Forward substitution `t = ell+r0` preserves all residuals. For a reverse
existence map one needs to prove that every positive 79 zero has `t>ell`;
then `r0=t−ell` is a positive witness. The intended route is that residual
splitting forces `t² = ell*(ell+k)+1`, while `ell` and `k` are positive.
This argument and the graph equivalence are **not yet checked in Lean**.
Neither an iPRA endpoint nor a file/display binding is claimed. In particular,
the maintained root `equation.tex` and `equation.pdf` are unchanged.

[`build.py`](build.py) verifies that the remaining 78 parent rows are
structurally identical, all inputs/gates are live, the first residual's
expanded identity holds exactly, and 600 deterministic modular evaluations
preserve each residual and the output under `t=ell+r0`. It reruns the four
pinned P64 residual identities and computes exact leading forms using the
verifier's symbolic polynomial machinery. Residual degrees are 22, 34, 22,
23 and 2; the total degree remains 68 for `beta != 0`, with leading form

```
64 * beta^46 * J^46 * w^4 * s^14 * (eta+zeta)^2 * gamma^2.
```

This is external symbolic and finite evidence, not a Lean proof of the graph
transcription, zero equivalence, iPRA endpoint, or global minimality. The
[`generate_lean.py`](generate_lean.py) script transcribes the graph to
[`P64QCube79.lean`](P64QCube79.lean); that definition has not yet been
compiled in Lean.

To reproduce the external checks:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube79-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube79-candidate/generate_lean.py
```

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `60ee74c0c6519148b9862eab6e1990c3ceb757a1fda417fb638ad2f6c592a01a` |
| `graph.json` | `d70bbed8b36895ffcf144f51bf78287e03fb2942d62c016ac9c845e691820b9b` |
| `checks.json` | `f133f497d90d3e60c81bb349839644e3f149b20f6c91e7c8a3b89d35058c62c6` |
| `generate_lean.py` | `2d5e554ed93027ba24d13d82c73c141afde378a2e5d909eb3697434c32901de4` |
| `P64QCube79.lean` | `377abf054d664130d10e781e5b239f6776f4f3e31c175bfcbff27fb3f2002d4f` |
