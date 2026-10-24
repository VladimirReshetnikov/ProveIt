# Nine positive variables after main-root folding

A new ordinary two-way Pell reduction improves both simple-majorant
position-zero parents while retaining each complete fixed coefficient tuple.

| Equation | Positive variables | Live binary operations | Exact total degree |
|---|---:|---:|---:|
| boundary_simple.json, original31 | 9 | 414 | 1,355,142 |
| compact_simple.json, compact54-sharp | 9 | 422 | 1,497,238 |

All nine inputs are strictly positive integers. Numeral/fixed leaves and
reuse are free; every live binary add/sub/mul counts, including squaring
and scalar multiplication. The ordinary proof is in `PROOF.md`.

The new radicands are `a0*F` and `I`, with
`F=1+(A²−1)*a0*(iJC²)²`. Coprimality recovers the first Pell square;
absolute residue folding recovers the omitted main root. Explicit finite
matrix periods construct positive i,j, and the direct strict inequality
in Section4 constructs positive n. These are existential witness maps,
not an identity of the old and new full polynomial.

The full JSON graphs, every retained prefix register and every new local
formula are checked. An exact centered-norm identity has a unique top-degree
term; complete actual fixed integers give three redundant nonzero modular
homogeneous leading witnesses. The larger syntactic degree bounds are
recorded separately. Whole ports and all fixed payloads are loaded from
the pinned incoming archive and compared byte for byte with the previous
whole tuples; no new coefficient emitter or payload copy is needed.

From the repository root:

```
python3 -B Computability/DiophantineConsistency/research/nine-folded-saturation/build.py --check
python3 -B -O Computability/DiophantineConsistency/research/nine-folded-saturation/build.py --check
python3 -B Computability/DiophantineConsistency/research/nine-folded-saturation/check.py
python3 -B -O Computability/DiophantineConsistency/research/nine-folded-saturation/check.py
```

`CHECK.json` and `CHECK_OPTIMIZED.json` retain the two independent replay
receipts. Each includes all fixed-value bindings, live counts, complete
local-identity coverage, exact degree witnesses, four rejected corruptions,
and finite Pell/factorization controls. `BUILD.json` pins the independent
checker and builder; `MANIFEST.json` seals the complete packet.

The accepted ordinary source/native/refutation calibration remains inherited
from the exact parent source and tuple. This packet supplies no new calibration,
consistency proof, absence-of-zeros claim, global minimum or Lean/internal-ZFC
certificate. Lean remains paused. Existing candidates are unchanged.
