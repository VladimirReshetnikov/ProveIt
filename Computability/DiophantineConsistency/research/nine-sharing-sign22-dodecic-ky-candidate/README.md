# 22-witness degree-12 candidate by eliminating kY

This external AST candidate starts from the audited 23-witness octic seed. Its
`kY` residual is old coordinate 17 minus
`((v11 + 1) + (v12 + 1)) * v15`. Delete that row and coordinate, substitute
the displayed polynomial into every remaining row, and shift old coordinates
18–23 down one. The distinguished input coordinate zero is unchanged. The
candidate has 13 residuals and 22 witness coordinates.

For natural inputs the eliminated coordinate reconstructs as a natural
product. Conversely, a zero of the deleted row forces precisely that value.
An IΣ₁-model proof still needs the square decomposition, natural embedding
injectivity and each residual transfer; the sign23→24 and sign24→25 bridges
also remain open. The sign25→26 bridge and direct-expression zero equivalence
have been checked, but this does not yet produce a sign22 endpoint. Finite
controls are illustrations only. Coefficient hashes identify retained bytes;
they do not bind the coefficients to the Lean ports or to a PDF.

Every retained residual has syntactic total degree at most six in the
coordinates, giving a square-sum degree upper bound of twelve. Specialize
v11=v15=v16=t and all other witnesses to zero, with the input fixed at one and
ports at arbitrary fixed integers. The N0 residual becomes
`-t^6 - 4*t^5 - 5*t^4 - 4*t^3 - 4*t^2 - 1`. Every other residual has degree
at most six. The coefficient of `t^12` in the sum of their squares is thus a
sum of squares of integer leading coefficients and is at least one from N0.
Hence this fixed-input, fixed-port integer polynomial has exact total degree
twelve. The input value does not affect this N0 specialization.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

`result.json` is the author's checker output. This is a variable/degree
tradeoff against the 23-witness degree-eight candidate. The AST identities,
degree and natural lift here are external claims; no Lean degree theorem,
all-model bridge, iPRA endpoint, or Jones reduction is asserted. An
[independent external audit](../../reviews/nine-sharing-sign22-dodecic-ky-independent/README.md)
checks the substitution, coefficient hashes and degree argument.
