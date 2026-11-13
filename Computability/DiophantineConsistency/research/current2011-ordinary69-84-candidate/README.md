# Exact 69-operation rewrite of the current2011 70/84 equation

This 14-positive-variable integer-leaf graph has the same first 61 rows and
the same four current2011 fixed ports as the checked 70/84 graph. Its final
eight rows evaluate, with `X = P*Q*W`,

```
U² + H² + X*(X−2).
```

The parent output is `U² + (X−1)² + H² − 1`. The identity
`(X−1)²−1 = X*(X−2)` holds in every commutative ring, so the **entire two
polynomials agree**, not just their zeros. The new graph has 69 live binary
gates: 38 multiplications, 18 additions and 13 subtractions. Every one of
the 14 positive witness leaves and four fixed integer leaves is live. This
saves one subtraction relative to 70/84 without increasing its degree.

The [checker](check.py) validates the whole shared prefix and both complete
tails. It evaluates both tails as exact formal polynomials over five
independent prefix cuts and verifies equality term by term. It checks graph
topology, liveness, all port paths, compressed and raw hashes, and the fixed
integer bytes. An independent syntactic-degree upper bound uses the explicit
main-norm cancellation; substituting `t` for all witnesses and the recorded
port bytes in the complete graph modulo 1,000,000,007 yields degree 84 with
leading coefficient 589,155,221. Hence the fixed-byte polynomial has exact
degree 84. This is an external exact check, not a Lean `totalDegree` theorem
or a Lean proof of JSON/file semantics.

The later [Lean literal client](../current2011-ordinary69-84-literal/README.md)
checks the evaluator and exact ring identity with 70/84. A separate [iPRA
endpoint](../current2011-ordinary69-84-ipra/README.md), [independently
reviewed](../../reviews/current2011-ordinary69-84-ipra-independent/README.md),
checks the same-valuation all-model bridge and derivability for mapped
refutation and Gödel–Gentzen consistency. Graph and byte-file comparisons
remain external. The maintained 65/150 `equation.tex` and `equation.pdf` are
unchanged. No global operation or degree minimum is claimed.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary69-84-candidate/check.py
```

The [result](result.json) records the successful read-only run. `build.py`
creates the graph from the pinned parent and refuses to overwrite it. No Lean
process is invoked by either script.
