# Independent local gap/Nt obstruction audit

The independent checker confirms that only the `gap` and `Nt` rows contain
old v3. It substitutes the proposed integer assignment in those pinned ASTs,
derives separate syntactic degree bounds in the parameters a and K, and
checks a grid with one more point than each bound. Polynomial interpolation
over the integers then establishes both identities for all a and K. The
checker exited 0 under `python3 -I -S -B`; checker SHA-256
`cdb4f377201421918850e3c9fea2fb673480eed187d580fe0287a23994a147ed`,
result SHA-256
`6feab55206a74b8e23f1f8e19ab03f97251babbc05fd1385bfc433d8fbf6df12`.

For a≥1 and K≥0, `(a−1)K+a`, `a(K+1)+K+2`, and `a²−1` are nonnegative,
while v3=−2. Thus the two equations and those bounds alone do not force v3
to be natural. This is not a counterexample to the full residual system, a
witness-count lower bound, or a Lean proof.
