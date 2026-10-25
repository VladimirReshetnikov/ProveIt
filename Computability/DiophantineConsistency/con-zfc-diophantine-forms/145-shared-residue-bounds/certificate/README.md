# Symmetric residue certificates for ZFC consistency

This component contains three fully explicit ordinary quartics in unrestricted
integer variables. The primary recommendation is the 260-variable equation.
The 261-variable companion uses one fewer quadratic residual. The 259-variable
companion pays substantially greater support and coefficient height for one
fewer variable.

| Final directory | Variables | Degree | Quadratic residuals | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| `merged_aggregate_centered` | 260 | 4 | 186 | 5,325 | 128,446 |
| `grouped_centered` | 261 | 4 | 185 | 5,332 | 128,446 |
| `merged_cap32_centered` | 259 | 4 | 185 | 23,960 | 240,653 |
| retained centered parent | 282 | 4 | 192 | 5,491 | 128,446 |

For any endpoint, `equation.json` lists its complete ordered variables and
quadratic residuals. The equation is **the sum of those residual squares,
equal to zero**. `expanded_polynomial.json` supplies every collected integer
coefficient of that same quartic. A term `[c,[i,j,...]]` denotes the integer
coefficient `c` times the product of coordinates with those zero-based
indices. Repeated indices are repeated factors; `[]` is the constant monomial.
Every declared variable occurs. There are no symbolic coefficient ports,
factorials, binomial operators, variable exponents or hidden quantifiers in
these polynomial data.

`PROOF.md` proves the new arithmetic reduction, including both directions
and the crucial order of the factorial bootstrap. Its new certificate is

    L^2 - 2 sum(r_i^2) - 1 = a^2+b^2+c(c+1).

The existing radix has enough spare capacity that the true low residues are
less than `L/8`. This symmetric norm bound therefore identifies each signed
remainder with its true nonnegative residue. One certificate can replace
several individual nonnegativity certificates. The 260-variable variant
also combines the adjacent denominator groups `q^t` and `q^(t+1)`.

The ordinary source calibration is retained explicitly. Composing the new
existential equivalence with that calibration proves in ZFC that absence of
an integer zero is equivalent to `Con(ZFC)`. This is not a proof of consistency,
a global minimality claim, or a freshly compiled end-to-end Lean/Rocq endpoint.
The direct small-coefficient family being improved is distinct from the
repository's much-smaller-variable constructions with large numerical tuples.

## Reproduce offline

Python 3.10 or later, with its standard library only:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild --receipt /path/to/replay.json
```

The script resolves paths relative to itself and may be invoked from another
working directory. Ordinary checking authenticates the immutable parent,
reconstructs the complete new source transformation, verifies all inherited
Horn factorization identities and monic restoration steps, verifies the
integral translations, recomputes every quartic coefficient and checks
domains, metrics, coordinate liveness and corruption controls. It imports
the retained independent algebra checker, never the producing compiler.

`--rebuild` additionally runs the producers and translation search in a
temporary directory and compares every regenerated JSON file byte for byte.
This includes the more expensive 259-variable variant. No network, original
checkout, theorem prover, machine simulation or consistency search is needed.
The normal receipt includes this reconstruction; the optimized receipt checks
the exact algebra with Python assertions disabled.

These finite checks certify the supplied polynomials and transformations.
They do not replace the unbounded proof or determine whether a zero exists.

## Content map

- `PROOF.md`: full new ordinary theorem and its noncircular application.
- `ENDPOINTS.json`: domains, selected endpoint paths, counts and hashes.
- `build.py`: source transformation and producer.
- `verify.py`: independent proof-certificate and coefficient audit.
- `grouped/`, `merged_aggregate/`, `merged_cap32/`: complete source changes,
  factorization and monic projection certificates, and intermediate equations.
- Corresponding `_centered/` directories: the selected final literal equations.
- `parent/`: immutable signed parent inputs, its independent checker and exact
  source proofs. Its centered endpoint is independently recounted too.
- `inherited_proofs/`: retained arithmetic, logical and square-shell recoding
  arguments; see `CLOSURE_MAP.md` for the exact boundary.
- `PARENT_PINS.json`: source commit, archive identity and every inherited file hash.
- `PROJECTION_CAP_COMPARISON.json`: the finite support-cap comparison, which found
  identical extra-elimination equations at caps 32, 64 and 128.

The repository was read at commit
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`. No upstream files were modified.
The package is prepared for integration as a new contribution. All source
notices and licenses remain with their inherited material.
