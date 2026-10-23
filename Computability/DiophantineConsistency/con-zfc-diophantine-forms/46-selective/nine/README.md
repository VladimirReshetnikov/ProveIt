# Support-selective nine-variable equation

Final frozen source: maximum weight 175, target range 246 through 5148,
source span 5498. The 94 raw coefficient records have only 62 protected
monomials among 528 possible padded pairs. A common target translation of
-104 removes unused leading padding and places the minimum source exponent
at zero.

| Domain | Unknowns | Exact degree | Binary operations |
|---|---:|---:|---:|
| Strictly positive integers | 9 | 19,615,180 | 606 |
| Nonnegative integers | 9 | 19,615,180 | 609 |

This improves the package-45 nine-positive-variable equation at the pinned
repository commit from degree 129,875,980 and 788 operations. It uses the
same coherent parent, numerical ratio bridge and finalizer. The selective
source and one shared positivity shift have a new proof in `PROOF.md`.

The polynomials are the `generated/selective_nine_*.json` primary circuit
files. Every fixed power is expanded, every live arithmetic gate is charged,
and named registers do not add quantified unknowns. The accompanying
`*_degree_certificate.json` files are equal polynomials with the leading
cancellation resolved; they have larger operation counts and are not the
advertised primary circuits.

`generated/VERIFICATION.json` records complete finite source separation,
coefficient payload hashes, direct source and domain-map replay, target
extraction, finalizer fixtures and exact-degree certificates. Both normal
and optimized Python runs pass. The code requires only the standard library:

```
python3 build_nine.py
python3 verify_nine.py
python3 -O verify_nine.py
```

The unbounded equivalence to finite ZFC refutability uses the cited parent
system and Jones ratio theorems and the proof here. No ZFC consistency
assumption, unknown universal-machine index or variable exponent occurs in
the coefficient recipe. This is ordinary mathematical reasoning intended
to formalize in ZFC; a new end-to-end Lean/object-language ZFC derivation is
not supplied. Interpreting the nine-variable equation over all integers
instead of its stated domain is not justified.

The files under `upstream/` are copied from ProveIt package 45 at commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`, with their source headers and
mathematical provenance retained. The parent tuple is inherited as one whole
from package 31 through package 40; the shifted MF port must not be replaced
by an unshifted mask or by a component of a different tuple.
