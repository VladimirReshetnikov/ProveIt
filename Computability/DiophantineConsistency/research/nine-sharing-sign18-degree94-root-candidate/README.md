# Sign18 degree-94 main-root elimination: external candidate

This external source-only candidate removes old sign19 coordinate 15 using
its main-root row. Write `A = beta * (v1 + 1) + 1`; the old row states
`v15 + 1 = ((v9 + 1) * A + B) + C`, where B and C are the other positive
summands displayed in the pinned sign19 AST. The natural replacement is

```
v15 = (v9 * A + beta * (v1 + 1) + B) + C.
```

The identity `(v9 + 1) * A = v9 * A + beta * (v1 + 1) + 1` validates
this cancellation. The replacement uses only addition and multiplication of
naturals when beta is nonnegative. The 9 retained residuals have 18 natural
witnesses, with distinguished input coordinate zero unchanged. A model bridge,
Lean expression and iPRA endpoint remain to be proved.

Each residual has syntactic total degree at most 47. Specialize every witness
to t; the Na residual does not use input coordinate zero, so it may be fixed at
one. The t^47 coefficient is `-16 * beta^28` in `Z[t,beta]`. Thus the
square-sum's t^94 coefficient is a sum of integer squares at least
`256 * beta^56`, yielding exact external fixed-port degree 94 for nonzero beta.
The retained beta bytes decode as a positive unsigned big-endian integer, with
their inherited hashes checked. This does not prove their Lean interpretation.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

The author checker verifies the AST substitution, positivity shape, degree
witness, port hashes and finite natural-lift controls. Finite controls are not
an all-model proof. This is external evidence only; no Lean degree, Lean/JSON
binding, iPRA endpoint or nine-variable reduction is asserted. The
[independent external audit](../../reviews/nine-sharing-sign18-external-independent/README.md)
passed; the candidate packet is frozen.
