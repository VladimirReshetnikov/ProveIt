# 20-witness degree-20 candidate by eliminating E

This external AST candidate starts from the 21-witness degree-14 seed. Its
E row is old coordinate 16 minus `(v9+1) * (beta*(v1+1)+1) * v15`. Delete
that row and coordinate, substitute the displayed polynomial into every
remaining row, and shift old coordinates 17–21 down one. Distinguished input
coordinate zero is unchanged. The result has 11 residuals and 20 witnesses.

For natural inputs and nonnegative beta the deleted coordinate reconstructs as
a natural product. A reverse lift/drop must extract the deleted row and use
embedding injectivity in the relevant IΣ₁ models. Representing beta by a model
natural and checking residual transfers and square decomposition also remain
necessary. The sign21→22 seed bridge has been Lean-checked; the sign20→21
bridge, direct sign20 expression and iPRA endpoint have not. Finite controls
illustrate the algebra but are not an all-model proof. Hashes identify
external coefficient bytes, not Lean/PDF semantics.

Every retained residual has syntactic total degree at most ten. Fix input
coordinate zero at one, set v1=v9=v11=v15=t and all other witnesses to zero.
The coefficient of t^10 in N0 is exactly `-beta^2`, verified as a symbolic
polynomial in `Z[t,beta]`. Thus, when the fixed integer beta is nonzero, the
t^20 coefficient of the square-sum is a sum of squares of integer leading
coefficients and is at least beta^4. Since all residuals have degree at most
ten, the fixed-port sum of squares has exact total degree 20. The retained
external beta bytes decode as a positive unsigned big-endian integer (the
candidate builder writes values that way); the checker confirms the bytes
are nonzero and match the inherited hashes. This does not prove their Lean
port interpretation.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

`result.json` is the author's checker output. This is a variable/degree
tradeoff against the 21-witness degree-14, 22-witness degree-12 and
23-witness degree-eight candidates. No Lean degree theorem, model bridge,
iPRA endpoint or nine-variable Jones reduction is asserted. The
[independent review](../../reviews/nine-sharing-sign20-degree20-e-independent/README.md)
passed; the candidate packet is frozen.
