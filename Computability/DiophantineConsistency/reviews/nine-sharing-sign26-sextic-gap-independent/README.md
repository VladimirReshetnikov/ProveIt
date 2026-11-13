# Independent 26-witness gap-congruence audit

The independently written checker pins both ASTs, maps the old gap coordinate
to `g=a*q+t−a*n`, reindexes the other variables, and uses sparse integer
polynomials with fixed-length exponent tuples. It verifies the old gap row is
zero, the metadata and all 17 retained residuals, and that old lifted minus
new equals `−(a−n)*(Q−q³)` for `tau` and `cTminusR` and zero for the other
rows. It separately checks `Nt=H*(q−n−t)−n−(f−1)*a`, all coefficient
gzip/raw hashes and bit lengths, the certificate and prose paths, the q3
syntax, and the maximum residual syntactic degree 3. The checker exited 0;
checker SHA-256
`581996f207f697978392a5759b13b595d41eca7a43cada28a634d134c870d82f`,
result SHA-256
`153dc176e33f7cac31835fc8a23b1ae32353107b014f28f788ef5977fa7427c9`.

The external positivity argument is valid subject to its stated model
obligations: `H≥1`, `n,t,f≥1` and `a≥0`; if Nt vanishes, then
`H*(q−n−t)=n+(f−1)*a>0`, so ordered-ring reasoning gives `q−n−t>0` and
`g=a*(q−n)+t≥0`. A corresponding natural representative requires the
appropriate subtraction/order and embedding lemmas. The modified rows agree
only when q3 also vanishes, which follows from the required sum-of-squares
decomposition. These are proof obligations, not checked Lean results.

At fixed positive beta the unchanged q3 row has x₁³ coefficient `−beta³`
when other variables are zero. All residuals have degree at most three, so
the x₁⁶ coefficient of their square-sum is a sum of integer squares at
least `beta⁶>0`: the external polynomial has exact degree six. This audit
does not establish a Lean degree theorem, all-model zero bridge, numerical
model-port binding, iPRA endpoint or sextic-to-nine-variable Jones reduction.
