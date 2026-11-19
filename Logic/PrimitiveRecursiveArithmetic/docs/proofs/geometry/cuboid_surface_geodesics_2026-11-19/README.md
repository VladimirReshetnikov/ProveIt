# Farthest surface points and intrinsic diameter of a cuboid

This package gives exact formulas, coordinates, and proofs for two problems on

a cuboid surface:

1. the point farthest in intrinsic surface distance from a selected vertex;
2. the intrinsic diameter when both endpoints are free.

A surface path must remain on the boundary throughout. Its length is ordinary
rectifiable-curve length in three-dimensional Euclidean space.

## Main normalization

Sort the edge lengths as

```text
0 < A <= B <= C
```

and work first in the box `[0,A] x [0,B] x [0,C]`. Put

```text
L0 = sqrt((A+B)^2 + C^2).
```

`L0` is the distance between opposite vertices.

## 1. Selected vertex fixed

For `X=(0,0,0)`, define

```text
K     = 2*C^2 - 2*B*C - A*C - A*B,
delta = A*(C-B)/(2*C),
R^2   = (B^2+C^2)*(A^2+2*A*C+2*C^2)/(2*C^2).
```

Then a farthest point and the achieved distance are

```text
K <= 0:  Y = (A,B,C),                 distance = L0;
K >  0:  Y = (A-delta,B-delta,C),     distance = R.
```

At `K=0`, both displayed points are maximizers. The comparison is certified by

```text
R^2 - L0^2 = A*(C-B)*K/(2*C^2).
```

For an arbitrary selected vertex and arbitrary original ordering `(a,b,c)`,
first permute the axes into sorted order and reflect each coordinate so the
selected vertex becomes `(0,0,0)`. Apply the formula and undo the reflections
and permutation. `scripts/cuboid_surface.py` performs this transport.

## 2. Both endpoints free

Define

```text
alpha = sqrt(max(0, A^2+2*A*B-2*B*C)),
beta  = sqrt(max(0, B^2+2*A*B-2*A*C)),
ME    : alpha + beta >= 2*C-A-B,
Qdisc = A^2*B^2 - C^2*(B-A)*(A+B+2*C).
```

There are three exact regimes.

### I. Opposite vertices (`ME`)

```text
P = (0,0,0),   Q = (A,B,C),   D = L0.
```

### II. Boundary balancing (`not ME` and `Qdisc <= 0`)

Let

```text
H   = sqrt((B+C)^2 - 2*A*(C-B) - A^2),
tau = (B+C-H)/2.
```

Then

```text
P = (A/2, tau, 0),
Q = (A/2, B-tau, C),
D^2 = B^2 + 3*C^2 + 2*B*(A+C) - 2*C*H.
```

### III. Interior triple balancing (`not ME` and `Qdisc > 0`)

Let `ell >= max(B+C,L0)` be the unique root of

```text
sqrt(ell^2-(A+C)^2)
+ sqrt(ell^2-(B+C)^2)
+ sqrt(2*ell^2-(A+B+C)^2)
= C.
```

Set

```text
u = sqrt(ell^2-(B+C)^2),
v = sqrt(ell^2-(A+C)^2),
x = (A-u)/2,
y = (B-v)/2.
```

Then

```text
P = (x,y,0),
Q = (A-x,B-y,C),
D = ell.
```

At `Qdisc=0`, the boundary and interior formulas meet continuously.

## Does freeing both endpoints help?

Exactly in the non-`ME` region:

```text
ME:      D = E = L0;
not ME:  D > E,
```

where `E` is the fixed-vertex maximum.

## Included files

- `cuboid_surface_geodesics.pdf` - 16-page human-readable proof.
- `cuboid_surface_geodesics.tex` - LaTeX source.
- `references.bib` - bibliographic records.
- `lean/FiniteAlgebra.lean` - concrete finite algebra identities, with no
  `sorry`; not compiled in this environment.
- `lean/FormalizationBlueprint.lean` - definitions and theorem targets for a
  complete Lean development; explicit `sorry` markers are remaining work.
- `LEAN_ROADMAP.md` - staged path to a kernel-checked Lean proof and an
  optional internal iPRA endpoint.
- `scripts/cuboid_surface.py` - executable calculator accepting unsorted edge
  lengths and an arbitrary selected vertex.
- `scripts/verify_formulas.py` - symbolic and numerical independent checks.
- `scripts/audit_unfoldings.py` - exhaustive symbolic enumeration of all simple face chains and domination certificates.
- `VALIDATION.txt` - recorded algebra/grid validation results.
- `UNFOLDING_AUDIT.txt` - complete face-chain audit output.
- `SOURCE_NOTES.md` - provenance and scope notes.
- `EXAMPLES.txt` - representative calculator outputs.

## Reproduction

Python 3.10 or newer is sufficient for the calculator. SymPy is required only
for the symbolic validator.

```bash
python3 scripts/cuboid_surface.py 1,1,2
python3 scripts/cuboid_surface.py 3,1,2 --vertex 3,0,2
python3 scripts/verify_formulas.py
python3 scripts/audit_unfoldings.py
```

To rebuild the paper from the package root:

```bash
pdflatex -interaction=nonstopmode -halt-on-error cuboid_surface_geodesics.tex
pdflatex -interaction=nonstopmode -halt-on-error cuboid_surface_geodesics.tex
pdflatex -interaction=nonstopmode -halt-on-error cuboid_surface_geodesics.tex
```

The validation scripts are useful cross-checks, not substitutes for the proof
or for kernel checking. Lean and Lake were unavailable in the generation
environment, so the Lean files are explicitly marked uncompiled.
