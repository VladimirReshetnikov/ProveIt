# Independent local Nt divisibility audit

The checker pins the sign26 AST, verifies that v4 occurs only in the Nt row,
and substitutes the proposed parameterized assignment. It derives separate
syntactic degree bounds in beta, h, K0 and v4 and verifies a grid with one
more point than each bound. Polynomial interpolation establishes the exact
identity `Nt = beta*(h*(beta−1)−v4)−1` for all integer parameters. The
checker exited 0 under `python3 -I -S -B`; checker SHA-256
`c31de68abac5ef9f95d3f1804b7ad3b337f5b4c8aef6ea9470b111e7afebadee`,
result SHA-256
`474fd16c464d808a648132707d1b6fbad7dc9a6c83aa37593fed963db24a1fb1`.

For beta≥2 the identity is −1 modulo beta for every integer v4. Choosing
h=K0+1 ensures beta*h≥K0+1 and hence v9≥0 for K0≥0. This establishes only
the stated local obstruction to dropping Nt; it says nothing about whether
other residuals vanish and is neither a full-system counterexample nor a
witness-count lower bound or Lean theorem.
