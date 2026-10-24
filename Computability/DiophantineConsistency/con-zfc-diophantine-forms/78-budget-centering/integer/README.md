# Joint guards and two Pell-root translations

Three explicit fixed-coefficient Diophantine equations over unrestricted integers:

| Packet | Unknowns | Squared residuals | Exact degree |
|---|---:|---:|---:|
| `generated/octic26.json` | 26 | 14 | 8 |
| `generated/decic24.json` | 24 | 12 | 10 |
| `generated/degree16_23.json` | 23 | 11 | 16 |

Each packet specifies a single polynomial: the sum of the squares of its listed residuals. Every fixed coefficient is an actual supplied integer, with a reconstructible finite recipe. The six fixed ports are `beta`, `K0`, `MC`, `MF`, `cone_A`, `cone_B`. They are not existential unknowns. `MF` is already shifted once by `beta`.

The new equations have an integer zero exactly when the repository's calibrated ZFC refutation predicate has a witness. Equivalently, the absence of an integer zero is provably equivalent in ZFC to Con(ZFC), by composition with the explicitly identified inherited source theorem. The archive does not claim a new end-to-end proof-assistant certificate or global optimality.

## Main result

Source71's 38-integer quartic has two remaining positivity guards, each represented by a private triple. Source68's nearest-square lemma combines them using four coordinates. Keeping eta and zeta as independent coordinates makes both guard inputs quadratic. Ten monic coordinate eliminations then give the 26-integer octic, improving the inspected 27-integer octic.

Next translate both Pell roots:

```
tau_old = tau + E*(c-eta)
y_old   = V + y_tail
```

Eliminate `c=(a-E)*(eta+zeta)+eta` and `V=f*o-c`. The translations keep the resulting norms at degrees four and five instead of six. The resulting 24-integer polynomial has degree ten, certified by the fixed coefficient `[r^2*a^4*eta^4]=4`.

The optional 23-integer companion substitutes `u_old=2*q*u` and `w_scale=2*q*u^2`, then deletes the identically zero power row. Its completeness proof uses fresh canonical dyadic witnesses. It is an existence equivalence, not a bijection of every old zero. Its exact-degree certificate is `[J^8*u^8]=4096*beta^8>0`.

## Read and reproduce

- `section.tex`: full hand-readable construction, proofs, and comparison; intended for inclusion in the parent article with theorem environments and bibliography keys `source68`, `source71`, `source64`.
- `PROOF.md`: the standalone proof in Markdown.
- `build_and_verify.py`: standard-library reconstruction and exact algebra verification.
- `polynomial.py`: imported exact sparse-polynomial engine from source71, unmodified.
- `generated/`: complete residual packets and expanded sums of squares over symbolic fixed ports.
- `certificates/`: exact row-restoration, degree, coefficient, and diagnostic receipts.
- `coefficients/payloads/`: gzip streams of minimal unsigned little-endian integer bytes.
- `coefficients/recipe/`: literal K215 transition table, exact ordered tile list, and source34 coefficient builder.
- `SOURCE_PINS.json`: immutable repository source paths, hashes, and snapshot.
- `upstream/`: precise imported proof dependencies nearest the new reduction.
- `licenses/`: inherited licenses and notices.

Run from this directory:

```
python3 build_and_verify.py
python3 -O build_and_verify.py
```

The script calls the source34 builder's `construct()` function, which uses explicit `require` checks. Its historical command-line wrapper disallows `-O`, but that wrapper is not called. The new release driver works with or without Python assertions enabled. The verification requires no network and never searches for a ZFC refutation.

The literal source snapshot is ProveIt `2605669a532342f153b13eb6b4a0af4b54f5fa37`. The octic's parent is source71 `integer_forms/quartic38.json`; the nearest-square lemma is source68 `integer_system/PAIR_GUARD_PROOF.md`. The original parent uses the whole source34 tuple, inherited through source64. No ports from different native constructions are mixed.

## Scope of the evidence

Finite code checks prove exact algebra, actual coefficient bytes, residual degrees, polynomial coefficients, and variable occurrence. Universal positivity is proved in the article. The unbounded native-compiler, Pell-rank, and ZFC-refutation calibration remain the named mathematical dependencies. This new step neither fills nor hides the inherited formalization gaps. The polynomial zero-set equivalences do not assert ZFC consistency or inconsistency.
