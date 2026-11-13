# Thirteen positive variables, 69 operations, degree 174

This [integer graph](polynomial69.json) reuses the exact 69-row gate list
from the independently documented 2471-port carrier, with the current2011
four-port tuple. Its 13 positive witness leaves, all four fixed integer
leaves, and all 69 gates are live. It uses 39 multiplications, 16 additions
and 14 subtractions. The counts are for the positive-coordinate graph before
the arithmetic sentence's shift; no global minimum is claimed.

The [finite checker](check.py) validates the complete source graph and the
recorded current-port payload hashes and paths. It compares the entire output
with the checked split-core Lean `front13` and `expressionAt69` source using
associative/commutative normalization. It checks the exact main-norm
cancellation to derive the degree upper bound 174, and evaluates the complete
graph after setting all 13 witnesses equal to `t` and the actual fixed bytes
modulo 1,000,000,007. Its nonzero degree-174 coefficient is 737,305,404, so
the fixed-byte integer polynomial has exact degree 174. The checker is an
external finite calculation, not a Lean JSON parser or Lean total-degree
proof. Byte-to-Lean-port linkage is a separate claim.

The fresh completion and bridge module includes the standard iPRA
mapped-refutation endpoint for this Lean expression. The separately checked
[focused client](../thirteen-current2011-69-endpoints-4g/README.md) also
establishes the mapped Gödel–Gentzen translated-consistency formulation.
Those theorems concern the Lean expression and its fixed `CurrentWindowCarry2011.ports`;
the graph comparison is the external source-level link. The maintained
14-variable `equation.tex` and `equation.pdf` are unchanged.

Run the deterministic check from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/thirteen-current2011-69-174/check.py
```

It exited 0 and produced [result.json](result.json). The graph SHA-256 is
`8667df5fe2f33c14a4280972336611218ebfb68883347bbfbb9215e5ab72a517`;
the checker SHA-256 is
`e4aaa2cd7aabcc54b3558c6948f9518f112ae5d2c4332c9dc8bea113e6b2ec26`;
the result SHA-256 is
`0ba9a076953cdaab688dae2c41a83a72c2e26098f66b211c414968c1fbedef53`.
The builder refuses to overwrite an existing graph.
