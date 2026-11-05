# A partial-factor obstruction to preserving G in normalization

The exact checker evaluates the pinned 88 DAG at small **symbolic** ports
`beta=3`, `K0=1`, `MC=MF=0`, not at the large fixed payload. Its positive
input tuple has

```
q=4, F=1, alpha=196, X=4, Y=64, P=XY²=16384,
k=8P+4=131076, first Pell index n=2,
G=205, rank=3075, Bt=-1548.
```

The actual first residual is zero, the transport magnitude is at most `P`,
the expanded main expression is positive, and both `q⁴∣k−rank−1` and
`q⁴∣2n−rank−1` hold. Nevertheless, no positive `F',alpha'` can preserve
this `G` and make transport positive while keeping `q` and `A=K0+w=2`
fixed. Indeed, positive transport forces `F'+alpha'<q`; the finite search
over the positive integer possibilities finds their maximum possible
`G'=alpha'+(q−1)(q−F')` is 11, far below 205.

This is **not** a full 88-graph zero or a counterexample to the desired
existence equivalence: the actual main and ordinary residuals are nonzero.
Moreover, `1+delta(a)*c²` is not even a square, so the main Pell norm fails
for this tuple. The example shows that the first factor together with the
listed consequences cannot by themselves prove the proposed G-preserving
normalization or the 89 rank window. It does not rule out an argument using
the remaining full graph constraints or a transformation changing other
registers.

## Exact check

`python3 -I -S -B check.py` evaluated every operation in the DAG, checked the
listed first-factor and scalar conditions and the strict nonzero/full-graph
limitations, and exited 0 on 2026-11-04. `result.json` preserves the output.
The checker raises on failed conditions even under Python optimization; the
finite search exhausts the positive representatives allowed by `q=4`.

```text
graph-dag.json SHA-256 84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25
check.py SHA-256       6a97245be5b1a691dd6f46a34c4be5f26b1a04525631ac951dd5af7258c79cf9
result.json SHA-256    c54208ad28a21fb4fdcaef2369cc44c524ef8cb01fa2b7f155781fcd42896f26
```

This is an external finite computation, not a Lean theorem or an internal
model-of-IΣ₁ construction.
