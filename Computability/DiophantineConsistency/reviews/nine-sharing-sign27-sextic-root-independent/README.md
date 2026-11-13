# Independent 27-witness normalized-root audit

The separately written checker pins both source ASTs and independently maps
each old coordinate: old 21 to `u+1`, old 22 to `u(u+2)`, and old 23–28
to new 22–27. It checks all 18 retained residual ASTs and metadata, the
deleted N1 row, unused input 0, syntactic residual degree at most 3, the
exact q3 syntax, all four coefficient gzip/raw hashes and bit lengths, and
the certificate and prose paths. Fixed beta is positive. The checker exited
0 under `python3 -I -S -B`; checker SHA-256
`a0bfddde533344ad1249dbb01d06845e729e0ff4e3f6872df160d65ef618c688`,
result SHA-256
`828c214a832222b8542a71a7baa997661d15a6b6d479f3134ec71169906bd8b1`.

The proposed lift makes N1 zero by `(u+1)²-u(u+2)-1=0`. Conversely, in the
intended natural model, zero of the sum of squares forces N1 zero; if old
root were zero, its equation would say `0 = old_product+1`, contradicting
nonnegativity and nontriviality. A predecessor then gives root `u+1`, and
the equation and injective natural embedding give product `u(u+2)`. This
all-model argument depends on the indicated ordered-ring, predecessor and
embedding facts and has not been checked in Lean.

The unchanged q3 residual has `−beta³` as its x₁³ coefficient when other
variables are zero. As the other residuals have degree at most 3, the x₁⁶
coefficient of the sum of squares is a sum of integer squares at least
`beta⁶ > 0`; the external polynomial's degree is exactly 6. The same row is
`−(beta+1)³` at zero. This audit does not establish a Lean degree theorem,
an all-model bridge, a port binding, an iPRA endpoint, or a Jones reduction.
