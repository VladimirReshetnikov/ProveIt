# 31 positive unknowns, 22 quadratics, 61 operations

`PROOF.md` states and proves an affine simplification of the pinned wave-4
quartic31. The equation has degree 4, 31 strictly positive unknowns, and a
126-operation arithmetic circuit. Its quadratic-system presentation has
61 operations. Both save four operations against the parent; the expanded
symbolic quartic has 259 monomials instead of 306.

Reproduce with:

```sh
python3 build_and_verify.py
```

The script uses only Python's standard library and verifies all 22 residual
identities exactly with symbolic coefficient ports. Read `PROOF.md` for the
positive-domain proof, coefficient-binding requirement, source attribution,
and verification boundary.
