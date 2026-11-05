# Independent review of the P64 q-cube candidate

The frozen [81-gate candidate](../../research/p64-qcube81-candidate/graph.json)
passes the independent structural and exact small-polynomial checks in
this packet. This review did not run Lean and does not establish zero-set
equivalence or an iPRA endpoint.

Replacing the old witness `Y` by `q³*s` adds one gate. Of the parent
graph's 83 rows, seven first-residual rows are replaced by four; the
other 76 rows match in order and operation exactly. The candidate has
81 topologically ordered live gates: 42 multiplications, 23 additions,
and 16 subtractions. Its generated Lean source has exactly the JSON gate
rows, witness indices, port indices, and residual tuple. This is a source
transcription check, not a proof that Lean elaborated or verified the
graph semantics.

With `ell`, `rho`, `s`, and `k` denoting the indicated registers, an
independent sparse-integer-polynomial calculation checks

```
(q³*(ell+rho)+q³*s)² − q⁶*(ell*(ell+k)+1)
  = q⁶*((ell+rho+s)² − (ell*(ell+k)+1)).
```

The unchanged rows therefore give exactly the same `M`, `W`, `Na`, and
`Lt` residuals under the substitution. The **outputs** satisfy

```
P64(Y=q³*s) − P81 = (q¹²−1)*(A0_new)²,
```

not a direct polynomial equality in general.

## Degree and remaining proof obligations

Treat the four ports as coefficients and the 14 witnesses as degree-one
variables. For `beta≠0` in characteristic zero, the leading degrees of
`q,Y,X,a,c,H,U` are respectively `1,4,2,6,5,6,8`, where `U=Y²`.
Expanding the main residual cancels its apparent degree-38 terms. Its
unique degree-34 term is `2*U²*a*c*H*gamma`, with leading form

```
8*beta²³*J²³*w²*s⁷*(eta+zeta)*gamma.
```

The other residuals have degrees at most 12, 22, 23, and 2, so squaring
the main residual gives exact output degree 68 and leading form

```
64*beta⁴⁶*J⁴⁶*w⁴*s¹⁴*(eta+zeta)²*gamma².
```

The independent script verifies the first-factor, main-expansion and
auxiliary-expansion identities and this leading polynomial using its own
small sparse-polynomial implementation. The degree claim is conditional
on `beta≠0`; it does not establish that the symbolic fixed port is bound
to a particular external payload.

The factor identity alone does **not** prove equivalence of zero sets:
the outputs are sums of squares minus one, and the new first residual can
contribute a unit square unless that branch is excluded or a suitable
alternative witness is constructed. The parent-to-candidate direction
also needs positive `s` with `Y=q³*s` for each relevant parent zero.
The existing parent root/normalization results are potential inputs, but
the required model-level composition, reverse direction, and internal
iPRA equivalence are not proved by these checks. The graph definition's
reported separate compilation does not discharge those obligations.

## Checks and provenance

The frozen candidate's `build.py` and `generate_lean.py` were rerun with
30-second timeouts; both exited 0, including the builder's 600 modular
graph samples. The independent structural/algebraic check below also
exited 0 and produced [`result.json`](result.json):

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube81-independent/review.py
```

The result pins the exact candidate graph, builder, metrics, generator,
Lean source, and parent graph hashes. No fixed-payload identity or
transitive Lean provider ancestry was checked by this review.

```text
93639ee078ab37347e62bfc4ca99fc4a75ae7b6d8bf1b66e9408fd3382d6e8b8  review.py
0a763f1f9221bfda85c23d5cc3e26ffddfa93c4b07de004d5ec1a3219e7dd82b  result.json
```
