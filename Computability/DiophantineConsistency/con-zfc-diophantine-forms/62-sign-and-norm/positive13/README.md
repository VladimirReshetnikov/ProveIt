# Thirteen positive unknowns, exact degree 114, 83 binary operations

`polynomial.json` is the complete division-free equation. Its unknowns are
exactly `J,F,alpha,z,f,i,T,s,w,eta,zeta,gamma,t`, all strictly positive.
The four fixed coefficients are materialized under `coefficients/` and
bound together by `COEFFICIENT_BINDING.json`; `MF` is already shifted.

The new root-centered norm restores both the first Pell root and the
auxiliary ordinate directly as integers. The ordinary strong coordinate is
retained. `PROOF.md` and `section.tex` give both directions, the early
absorbed-index bootstrap, exact degree, and the scope of the inherited
native compiler/K215 endpoint.

Run from any directory:

```sh
python3 /path/to/positive13/build.py
python3 /path/to/positive13/check.py
```

Both need only the Python standard library. The checker imports no builder
and passes under optimized Python as well. It authenticates the exact
coefficient bytes and source pins, checks all 83 live gates against 41
independently stated formulas, proves the norm and cancellation identities,
and checks the fixed-instance leading forms.

The exact count is 46 multiplications, 19 additions, and 18 subtractions.
Multiplication by a fixed scalar and every square are charged; register
reuse and fixed leaves are free. The degree is in the thirteen supplied
unknowns, with all four coefficients fixed. The diagonal leading
coefficient is `2^19*beta^67` at degree 114.

The transport coordinate `z` is the old positive product coordinate. It is
one greater than a coordinate in the shifted transport equation used in
the unrestricted-integer quartic. The domain and that shift are part of
the theorem, not interchangeable conventions.

Every upstream text is preserved unchanged and pinned in `SOURCE_PINS.json`.
The complete source50 absorber, ordinary-strong proof, compact44 adapter,
and comparison proofs are included. The literal native coefficient builder
and its transition data are also included. The accompanying nine-variable
package replays that whole coefficient construction. The full transitive
Lean/Rocq K215 project is an inherited external development, not a fresh
formal build performed by these scripts.
