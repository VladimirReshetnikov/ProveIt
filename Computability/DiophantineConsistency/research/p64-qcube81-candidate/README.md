# P64 q-cube quotient: 14 positive variables, 81 operations, degree 68

This is a **candidate**, not yet a proved replacement for P64 or an iPRA
endpoint. Starting with the 14-positive, 83-operation, degree-30 P64 graph,
replace its positive witness `Y` with a positive witness `s` and set
`Y=q³s`. Replace only the first residual

```text
A0_old = (q³(ell+rho)+Y)² − q⁶(ell(ell+k)+1)
```

by

```text
A0_new = (ell+rho+s)² − (ell(ell+k)+1).
```

The exact polynomial identity is `A0_old=q⁶*A0_new`. The other four
residuals are unchanged after substituting `Y=q³s`. The output remains the
sum of their five squares minus one. The unscaled first factor and removal of
`q⁶` save three gates; constructing `Y` costs one, for a net saving of two.

[`graph.json`](graph.json) has 14 distinct strictly positive witnesses and
81 live binary operations: 42 multiplications, 23 additions and 16
subtractions. It references P64's restored coefficient binding. Its exact
symbolic leading-form calculation gives degree **68** when `beta ≠ 0`, with
leading form

```text
64 beta^46 J^46 w^4 s^14 (eta+zeta)^2 gamma^2.
```

The residual degrees are 12, 34, 22, 23 and 2 for `A0`, `M`, `W`, `Na` and
`Lt`. P64's actual fixed `beta` is positive, so the leading form is nonzero.
The degree and operation counts are checked externally; neither is a Lean
degree or minimality theorem. P64 remains the lower-degree equation.

[`build.py`](build.py) pins the 83-gate parent and its verifier, checks the
first-residual identity and four parent local polynomial identities exactly,
computes the symbolic leading form, verifies liveness and the 76 unchanged
parent rows, and compares the two graphs on 600 deterministic modular
assignments. Those samples are additional transcription checks; the first
identity is checked as an exact polynomial identity, and the unchanged
residual rows are compared structurally. The exact
identity for the outputs is

```text
P64(lift(v)) = P81(v) + (q^12−1)*A0_new(v)^2,
```

where `lift` sends the index-7 input to `Y=q³s`. The formula follows from
the exact first-residual identity and the structurally unchanged other rows;
this does not itself establish the model-level zero equivalence.
[`generate_lean.py`](generate_lean.py) generates the 81 gate rows of
[`P64QCube81.lean`](P64QCube81.lean), importing the canonical P64 graph.
The generated graph definition has [compiled in Lean](../fourteen-p64-qcube-quotient-binding-draft/CANDIDATE_CHECK.md)
on a captured provider. That check does not establish zero-equivalence or
an iPRA endpoint.

## Missing proof obligations

For an old P64 zero, the checked `P64Root.first_root` gives `q³ ∣ Y`;
positivity should supply a positive `s` and first-residual cancellation.
For a new zero, the key missing step is a model-level version of P64's
five-square residual split that works with the unscaled first residual.
Once it forces `A0_new=0` and the four unchanged residuals to their required
values, the lift gives an old P64 zero. Both directions must be checked on
the same tuple in every intended `IΣ₁` model, joined to the P64 halt bridge,
and transported to the selected iPRA proof-existence statements. A first
attempt at the generalized split timed out during provider loading and did
not establish a theorem. The compressed-file and JSON bindings remain
external. Neither `equation.tex` nor `equation.pdf` was changed.

## Reproduce the finite checks

From the repository root, run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube81-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube81-candidate/generate_lean.py
```

Both exited 0 on 2026-11-04. [`checks.json`](checks.json) records the finite
counts, source hashes and exact leading form. The scripts reject optimized
Python; `build.py --write` creates its two outputs only when neither exists,
and `generate_lean.py --write` likewise refuses to overwrite its output.
The parent graph SHA-256 is
`b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e`.

```text
cc8dc4dfbc7ffe0002b0f341496e1323d61198bf076544d279456b78c3c702eb  build.py
41c8602480cee0e9a21d3a4cd2a7719fa395bd6aabba821aeb7a9f5c776a3db3  graph.json
353ebd987679cbc08b35bf6cbb3f9ad43364ce1b8f6047c9dc127d96587d018e  checks.json
de7d64c90ac8eb9850c3e655bf10a9dafcc1d726e5af92ad68df5f74288a9a1d  generate_lean.py
25f05a17cf291072514bbbe1b477edad173bd497e5dc019be01df811fd5661eb  P64QCube81.lean
```
