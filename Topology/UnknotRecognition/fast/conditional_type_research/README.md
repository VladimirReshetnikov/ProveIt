# Conditional matching: archived rule and complete initial-mask obstruction

This research package preserves two completed scratch experiments and replays
their evidence without running a kernel constructor, LP, sufficient closure,
ray enumeration, or topology discovery. These conditional-matching experiments
add no native elimination rule; unrelated native improvements have separate
implementations and evidence.

The proposed rule tests a quadrilateral type `a` by excluding its two competitors
in that tetrahedron. If original matching equations and nonnegativity force
`a=0` under this condition, compatibility permits deleting **only `a`** globally.
Other conditionally forced coordinates cannot automatically be deleted globally.

The first experiment made 216 attempts: 215 returned and one W34 query reached
its explicit callback cap. No coordinate was deleted and no local forcing
packet was returned. The second experiment constructed and independently checked
all 276 initial conditional matching witnesses, including W34's previously
untested suffix. This proves that this initial matching-zero rule has no effect
on any of these six sources. It does not relabel the earlier capped scan as
complete.

| Source | Tetrahedra | Cheap attempts/returns | Cheap callbacks | Exact witnesses | Witness callbacks |
| --- | ---: | ---: | ---: | ---: | ---: |
| T | 7 | 21/21 | 7,924 | 21 | 3,047 |
| F | 10 | 30/30 | 30,890 | 30 | 6,242 |
| TT | 16 | 48/48 | 212,610 | 48 | 16,034 |
| T25 | 11 | 33/33 | 52,604 | 33 | 7,559 |
| T27 | 17 | 51/51 | 290,842 | 51 | 18,107 |
| W34 | 31 | 33/32 | 1,000,000 | 93 | 60,359 |
| Total | | 216/215 | 1,594,870 | 276 | 111,348 |

Each original experiment allowed 1,000,000 explicit callbacks per source,
6,000,000 total. These counters exclude independent replay and are not wall time
or exact bit-operation counts. This package makes no timing comparison.

The sources are the exact enabled endpoints of the retained fixed-U1 staged
experiment. Labels mean trefoil braid `(2,[1,1,1])`, figure-eight braid
`(3,[1,-2,1,-2])`, TT braid `(3,[1,1,1,2,2,2])`, T25 braid `(2,[1]*5)`,
T27 braid `(2,[1]*7)`, and W34 braid `(3,[1,-2]*4)`. W34 primeness is neither
assumed nor needed. Complete original PDs and source-authenticated mixed chains
are retained in `data/source-provenance/staged-audit.json.gz`.

## Portable solver-free replay

From `Topology/UnknotRecognition/fast`:

```sh
python -B -S -m conditional_type_research.replay --output ../synthesis/data/conditional-type-matching-replay.json
```

Assertions must be enabled; the entry point explicitly rejects `python -O`.
No optional packages, `/tmp` files, or old research-package imports are required.
The checker validates both levels of archival hashes, all source chains and
type-sensitive source/PD bindings, each conditional mask, literal integer
nonnegativity, all original STANDARD matching equations, the positive tested
coordinate, and the zero competing Q coordinates. It independently repeats
12 retained corruption controls. Kernel/construction metadata receives only
type, dimension, and consistency checks; its elimination trace is not replayed.

The historical scratch scripts are inert archive data and retain their original
absolute paths. Their embedded source-pin maps describe their generation and
replay environments. They are not compared with current source bytes or presented
as current pins. The portable replay records a separate fresh map covering all
native Python, all package files, and the accompanying theory article. Save new
replay output outside this package to avoid a source-hash cycle.

`data/manifest.json` records stored and uncompressed SHA-256 hashes and sizes.
Both eight-file scratch groups and both original manifests are preserved exactly;
JSON is compressed deterministically. The staged source archive is copied exactly
from the published fixed-U1 research package, and its original repository path
is recorded. Some historical notes say a later experiment had not yet run; these
are preserved chronology, not current conclusions.

## Mathematical scope

In one tetrahedron, triangle coefficients `(-1,-1,-1,-1)` and Q coefficients
`(1,1,1)` give zero trace on every face. On an initial conditional mask, each
other tetrahedron retains all three types, so these Q block-ones directions
repair any negative Q entries of a linear vector with positive tested coordinate.
Adding vertex links then repairs triangle entries. Initial conditional
nonnegative feasibility is therefore equivalent to the tested coordinate being
nonzero on the linear kernel. If it is identically zero, a unit RREF equation
already detects that fact. A full LP cannot improve this initial support test.
The argument need not survive later deletions, because block-ones directions may
leave the retained mask; the article gives a precise abstract counterexample.

The 276 retained vectors may contain incompatible Q types at other tetrahedra.
They are formal matching witnesses, with no Euler-sign, extreme-ray, embedded
surface, or knot-verdict claim. Nested-mask monotonicity concerns `h_J`; it does
not change the full-source `h(T)`. General quasi-polynomial recognition remains
unproved. The complete proof and finite scope are in
`synthesis/conditional_type_matching.tex`.
