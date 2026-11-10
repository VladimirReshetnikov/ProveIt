# 21-witness degree-14 candidate by eliminating normalized S

This external AST candidate starts from the 22-witness degree-12 seed. Its
`normalized_S` row is old coordinate 21 minus `(v6+1) * v17 * (v17+2)`.
Delete that row and coordinate, substitute the displayed polynomial into every
remaining row, and shift old coordinate 22 down one. Distinguished input
coordinate zero is unchanged. The result has 12 residuals and 21 witnesses.

For natural inputs the eliminated coordinate reconstructs as a natural
product; conversely, a zero of the removed row forces that value. A proof in
IΣ₁ models requires square decomposition, embedding injectivity and residual
transfers. The sign22→23, sign23→24 and sign24→25 model bridges also remain
open. The sign25→26 bridge and direct-expression zero equivalence have been
checked. These observations do not yet prove an iPRA endpoint for sign21.
Finite controls are illustrations, not a proof for all models. Coefficient
hashes identify retained bytes but do not bind them to Lean ports or a PDF.

Every displayed residual has syntactic degree at most seven. Set
v6=v17=v21=t and all other witnesses to zero, fixing input coordinate zero
at one and keeping the four ports fixed as integers. The Na residual is
`-t^7 - 6*t^6 - 13*t^5 - 12*t^4 - 4*t^3`. Each residual specializes to a
polynomial of degree at most seven, so the t^14 coefficient of the sum of
squares is a sum of integer squares with the Na contribution equal to one.
Thus the fixed-input, fixed-port sum of squares has exact total degree 14;
Na does not depend on the input. The equality of this external AST and any
Lean expression is not claimed.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

`result.json` is the author's checker output. This is a variable/degree
tradeoff against the 22-witness degree-12 and 23-witness degree-eight
candidates. No Lean degree theorem, all-model bridge, iPRA endpoint, or Jones
reduction is asserted. An [independent external audit](../../reviews/nine-sharing-sign21-degree14-s-independent/README.md)
checks the substitution, coefficient hashes and degree argument.
