# P64 shifted-residual candidate: 14 positive variables and 78 operations

Starting with the 79-operation graph, replace its first residual

```
A0 = t² − (ell*(ell+k)+1)
```

by `A1 = t² − ell*(ell+k)`, and replace the final `−1` by `−2`. The
`first_radicand = first_product+1` gate is now unnecessary. All coordinates
are retained. The result has 78 live gates: 42 multiplications, 20 additions
and 16 subtractions, with 14 positive witness variables.

The two graphs are not pointwise equal: `A1 = A0+1`, and their outputs obey
`output78 = output79 + 2*A0`. An actual 79 zero maps forward if its old first
residual is zero. The reverse requires showing that, for every positive 78
zero, the shifted first residual is exactly 1 and the remaining residuals
have the required values. A separate generic residual-splitting and norm
exclusion effort is in progress; **this graph has no checked zero-existence
or iPRA equivalence here**. The maintained root `equation.tex` and
`equation.pdf` are unchanged.

[`build.py`](build.py) checks the 76 unchanged parent graph rows, that all
inputs and gates are live, the exact polynomial output-difference identity,
and 600 deterministic modular comparisons of both first residuals, the four
unchanged residuals, and the output difference. It reruns the four pinned P64
residual identities and computes exact symbolic leading forms. Residual
degrees are 22, 34, 22, 23 and 2; total degree is 68 when `beta != 0`, with
leading form

```
64 * beta^46 * J^46 * w^4 * s^14 * (eta+zeta)^2 * gamma^2.
```

These external symbolic and finite checks do not prove zero equivalence,
an iPRA endpoint, external-file identification, or global minimality.
[`generate_lean.py`](generate_lean.py) transcribes the graph to
[`P64QCube78.lean`](P64QCube78.lean). Its guarded [Lean check](lean-check.json)
exited 0 with empty output and stable direct input hashes. It checks the graph
definition elaborates, not the external JSON-to-Lean correspondence or full
transitive provider ancestry.

To reproduce the external checks:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube78-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube78-candidate/generate_lean.py
```

The compiler runner refuses to overwrite outputs and uses explicitly named
temporary providers; use fresh output paths in a copy for a repeat.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `ffb2721381554da668ea399cb8a0df874a43b554ed9c03d5de7e391aae97396d` |
| `graph.json` | `8037b90bdeb55c5fe91ab2db7e96b8c200f6c48c3ae6f0902e87435d1f1ba096` |
| `checks.json` | `9e1ce7f2612c491026609e8cd1c8d2c603cef399612ab372b1c6aadce73da5b3` |
| `generate_lean.py` | `38c3237c39cae109dbe9e7195bf2af03fb5d74b833dcb42e8d22fd843a2fb9c9` |
| `P64QCube78.lean` | `6a86588ec322601eebe44fb65c2c91303be142101bedffcbe2714396fa996fc3` |
| `check_lean.py` | `709e65124faeeab6b4b329aa0ce0f0bb0b7838cf19b54f22b017f929a26f6f6f` |
| `lean-check.json` | `ccc1276212bbad6dcba763cbe9048a017661390b56d70f713beedf1ac6f952e6` |
| `/tmp/P64QCube78.olean` | `112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5` |
