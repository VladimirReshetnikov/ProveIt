# 76-operation transport-coordinate proposal

This proposal changes the 77 graph's positive witness `alpha` to a new
positive witness `C` and uses the substitution

```
C = q − F − alpha
(q−1)*(q−F) + alpha = q*(q−F) − C.
```

It removes the gate that computed `C`, changes the two `gap` rows as shown,
and leaves the remaining 74 rows and all other coordinates unchanged. The
candidate has 14 positive witnesses and 76 live operations: 42
multiplications, 18 additions, and 16 subtractions. Its external symbolic
leading-form calculation gives degree 90 when `beta != 0`, with leading form

```
4 * beta^50 * J^50 * T^2 * e^2 * f^8 * s^14 * w^8 * (eta+zeta)^6.
```

**This is only a candidate.** The exact algebra preserves the graph under
`alpha=q−F−C`, but the 77 witness requires `alpha>0`; hence a reverse
positive-witness map requires the strict inequality `C<q−F`. A positive 77
zero does give `C>0` from its transport equation, because `q−1≥0`, `F>0`,
and `K0+w>0`. Whether every positive 76 zero satisfies the reverse bound is
not established. No zero-existence equivalence or iPRA endpoint is claimed.

## Transport alone does not force the reverse bound

For arbitrary natural `K0≥0` and `beta≥1`, the following positive partial
assignment satisfies the transport equation while `alpha` is negative:

```
J = 1, q = beta+1, F = 1, C = q,
w = 1+(q−2)*K0, z = 1+q*K0.
```

Indeed `(K0+w)*C = F+z*(q−1)`, but `q−F−C = −1`. The builder checks these
identities over the exact polynomial ring. This assignment does **not**
establish a zero of the full 76 graph: it only shows that the transport
equation and positivity by themselves cannot justify the reverse bound, even
for a fixed positive `beta` and fixed nonnegative `K0`.

[`build.py`](build.py) checks the gap identity exactly, the transport-only
counterexample identities, the 74 structurally unchanged parent rows, all
gate/input liveness, the symbolic leading form, and 600 deterministic modular
substitution comparisons of the residuals and output. Its captured external
check, along with the graph transcription check, is in
[`external-check.json`](external-check.json). The generated
[`P64QCube76.lean`](P64QCube76.lean) has **not** been compiled or proved
related to the parent in Lean. The external checks do not prove the guards,
a full-graph counterexample, source/file semantics, or global minimality.
The root `equation.tex` and `equation.pdf` are unchanged.

To repeat the external checks:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-transport-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-transport-candidate/generate_lean.py
```

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `a5f3d01781d18eabf704c68321494fa0f075c4cbb66ff0f4d7f450595181fb5d` |
| `graph.json` | `58b259ef212dded883ef0e36aedad303d07dad5ae00d7b1c6674ce4178a09de8` |
| `checks.json` | `6a6e2f28e880db43b9ebdce313eddc64a2ce17e0a6228760963614483bb02d13` |
| `generate_lean.py` | `c29c644e9f023823ef56d8dd25e443a922bed72d79486f7c8bb05790fcbf1b33` |
| `P64QCube76.lean` | `dd33ce742f7a8ca01b50f2dbe11cbe4233e1fad495ac16de52b6d7929fa7035b` |
| `external-check.json` | `8437ea5a2e5af7b914ca3cb4d4ecf9402e82f75a858f1030226e0eee4d5bd364` |
