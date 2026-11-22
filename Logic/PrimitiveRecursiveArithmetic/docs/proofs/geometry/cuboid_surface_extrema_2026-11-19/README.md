# Farthest points and intrinsic diameter of a cuboid

Prepared for Vladimir Reshetnikov, 19 November 2026.

The complete argument is in `cuboid_surface.pdf`, with editable source
`cuboid_surface.tex`. Paths are continuous and remain on the surface at
every point; the intrinsic metric is not the spatial chord distance.

## Main results

Sort the positive side lengths as `a <= b <= c`, with the selected vertex
at `(0,0,0)`. Coordinates can then be permuted and reflected back.

For a fixed starting vertex, put

```
H = 2c² - 2bc - ac - ab
delta = a(c-b)/(2c)
Q0 = (a+b)² + c²
Q1 = (b²+c²)(a²+2ac+2c²)/(2c²)
```

The maximum distance is `sqrt(max(Q0,Q1))`. Choose the opposite vertex
`(a,b,c)` if `H <= 0`, and `(a-delta,b-delta,c)` if `H > 0`.
At `H = 0` both points are farthest; otherwise the maximizer is unique.

For free endpoints, define for `T >= Q0`

```
F(T) = sqrt(max(0,T-(a+c)²))
     + sqrt(max(0,T-(b+c)²))
     + sqrt(2T-(a+b+c)²).
```

If `F(Q0) >= c`, opposite vertices attain the diameter `sqrt(Q0)`.
Otherwise there is a unique `T` in `(Q0,(a+c)²+b²)` with `F(T)=c`.
Put

```
u = sqrt(max(0,T-(b+c)²))
v = sqrt(max(0,T-(a+c)²))
X = ((a-u)/2, (b-v)/2, 0)
Y = ((a+u)/2, (b+v)/2, c).
```

Their distance is the global diameter `sqrt(T)`. It strictly exceeds the
fixed-vertex maximum exactly when `F(Q0) < c`.

For a `1 × 1 × 2` box the fixed-vertex answer is `sqrt(65/8)` at
`(3/4,3/4,2)`. The unrestricted answer is `sqrt(16-4sqrt(3))`, with
`X=((sqrt(3)-1)/2,(sqrt(3)-1)/2,0)` and its central reflection `Y`.

## Contents

| Path | Purpose |
|---|---|
| `cuboid_surface.tex`, `cuboid_surface.pdf` | Complete proof, exact formulas, and formalization roadmap |
| `code/cuboid.py` | High-precision calculator with a formula-based root specification |
| `code/unfold_verify.py` | Independent enumeration of valid face chains, returning actual paths |
| `code/validate.py` | Cross-checks against that separate geometric algorithm |
| `code/verify_algebra.py` | Exact symbolic identity checks using SymPy |
| `code/make_figures.py` | Recreates the scientific figures |
| `figures/` | Vector PDF and PNG figures |
| `lean/CuboidSurface.lean` | Explicit definitions and named Lean proof obligations |
| `lean/README.md` | API pin, dependency plan, and status notes |
| `lean/lakefile.toml`, `lean/lean-toolchain` | Target Lean/mathlib versions |
| `verification/` | Recorded numerical, symbolic, and example results |
| `SHA256SUMS` | Integrity hashes of packaged files |

## Run the calculations

Python 3.10 or later is suitable. The calculator, geometric verifier, and
numerical validation script use only the standard library:

```bash
python3 code/cuboid.py 1 1 2
python3 code/cuboid.py 100 2 3 --precision 80
python3 code/unfold_verify.py --sides 1 1 2 --p 0 0 0 --q .75 .75 2
python3 code/validate.py
```

Optional scientific dependencies are needed for symbolic checks or figures:

```bash
python3 -m pip install sympy numpy matplotlib
python3 code/verify_algebra.py
python3 code/make_figures.py
```

A normal TeX Live installation with the packages named in the preamble builds
the report:

```bash
latexmk -pdf -interaction=nonstopmode cuboid_surface.tex
```

From `lean/`, in an environment with Elan and network access, the intended
project setup is `lake update`, then `lake exe cache get`, then
`lake env lean CuboidSurface.lean`. This is a setup/checking instruction, not
a record of a successful compilation. The scaffold contains explicit
`sorry` declarations that must be replaced to finish the formal proof.

## Validation and limits

The independent numerical comparison passed 216 comparisons across 18
boxes, plus 10 known-answer tests. It uses exact face unfoldings in the
geometric sense, rather than a mesh approximation, but floating-point
arithmetic and tolerances remain. The largest absolute difference was
approximately `7.11e-15`. These tests are cross-checks, not a proof for
arbitrary dimensions or certified interval bounds.

All 18 symbolic identities in `verify_algebra.py` simplified exactly to zero.
The human proof supplies the geometry, sign conditions, and global
optimization arguments.

**Lean status: uncompiled formalization outline, not a completed
machine-checked proof.** All major missing proofs are explicit. No axioms
are used to pretend they are completed.

## Sources and repository use

The unrestricted formula agrees with Y. G. Nikonorov and Y. V. Nikonorova,
*The Intrinsic Diameter of the Surface of a Parallelepiped*, Discrete &
Computational Geometry 40 (2008), 504–527,
[DOI 10.1007/s00454-007-9037-7](https://doi.org/10.1007/s00454-007-9037-7).
The report contains a full argument, including the necessary validity checks
for developed straight segments.

A narrow read-only inspection of
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt) found no directly
reusable completed cuboid surface-distance theorem. No repository changes
were made. The report gives the precise Lean/mathlib source pin and the
remaining formal dependencies.
