# P64 unit-product candidate: 14 positive variables and 77 operations

Starting from the 78-operation graph, retain its five residuals `A1`, `M`,
`W`, `Na`, and `Lt`, and replace the sum of five squares minus two by

```
(A1*Na − 1)^2 + M^2 + W^2 + Lt^2.
```

This changes the polynomial, rather than a local pointwise rewrite. The new
graph has 77 live gates: 42 multiplications, 19 additions, and 16 subtractions;
it retains 14 positive witness variables. A zero forces `A1*Na=1` and the
other three residuals to zero in an ordered ring. The checked [positive-zero
equivalence](../fourteen-p64-qcube77-unit-draft/README.md) rules out the
`A1=Na=−1` branch, proves the converse and establishes both directions on
the same valuation for arbitrary natural ports in the stated IΣ₁ models. The
[iPRA endpoint client](../p64-qcube77-ipra-draft/README.md) checks native,
standard and equality-only proof-existence statements for the Lean graph at
symbolic compact44 ports and the selected mapped Foundation refutation
negation. These checks inherit captured-provider ancestry and do not establish
formal file/display binding. The root `equation.tex` and `equation.pdf` are
unchanged.

A proposed [unsquared unit-residual probe](UNSQUARED_UNIT.md) would save one
operation, but its output permits cancellation at the unrestricted residual
level. Its actual-graph zero-existence equivalence remains open.

[`build.py`](build.py) checks that the first 68 parent graph rows are
unchanged, all inputs and gates are live, the unit-product polynomial identity,
and 600 deterministic modular comparisons of all five residuals and the
new output formula. It reruns the four pinned P64 residual identities and
computes symbolic leading forms. The graph has degree 90 for `beta != 0`,
with leading homogeneous form

```
4 * beta^50 * J^50 * T^2 * e^2 * f^8 * s^14 * w^8 * (eta+zeta)^6.
```

These external symbolic and finite checks do not themselves prove the Lean
zero-set equivalence or iPRA endpoint above, external-file identification, or
global minimality. The [`generate_lean.py`](generate_lean.py) script transcribes the
graph to [`P64QCube77.lean`](P64QCube77.lean). Its guarded
[Lean definition check](lean-check.json) exited 0 with empty output and stable
direct input hashes. This checks that the definition elaborates, not its
external JSON correspondence or full transitive provider ancestry.

To reproduce the external checks:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube77-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube77-candidate/generate_lean.py
```

The compiler runner refuses to overwrite outputs and uses explicitly named
temporary providers; use fresh output paths in a copy for a repeat.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `e38c3c0e527c80420348bb68f6b46e6cb8581c09102b4e804174f842ec30a4a6` |
| `graph.json` | `8cda8e5729f7af6b725631a0a9a5b5d8886c24a4e62d94d889ada47ce54e7315` |
| `checks.json` | `c0b96a098f76365f7c6403296651c50c1a90a1978bef508b3dd13fe0f9e37228` |
| `generate_lean.py` | `10ffeb4f6118da5f16d90cff91a23852a436cdfe35db5ea5fea62b3e931e6889` |
| `P64QCube77.lean` | `1def5d3c7c3d2a9711f2119c47925959fcfe2c86aae469ede9672d0c74f149a0` |
| `check_lean.py` | `f0da120fb08fd8ce957e0fa86b3b82c2ee259aff00232c8833aa0297cb3c9de6` |
| `lean-check.json` | `489f41300627c1ebd824467c849b86b8831d4dde1a32858d7791f9297342bd50` |
| `/tmp/P64QCube77.olean` | `daa0b689982287a74991a14c588a23d64f7bc1b5959a2528d000a6f64c0bc99d` |
