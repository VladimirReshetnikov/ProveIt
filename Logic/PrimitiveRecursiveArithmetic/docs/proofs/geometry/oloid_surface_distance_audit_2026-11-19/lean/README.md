# Lean reproduction

All six Lean source files compiled with Lean 4.32.0, release commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, on x86-64 Linux.
The ProveIt source pin is
`09fe17194da14cdd100947737952e44100bb71b8`.
Its mathlib pin is `81a5d257c8e410db227a6665ed08f64fea08e997`.

## Effective distance observer

With the pinned `lean` on PATH, run the following in this directory.

```sh
lean -o FiniteRoutes.olean FiniteRoutes.lean
LEAN_PATH=. lean -o Observer.olean Observer.lean
LEAN_PATH=. lean --run ReplayObserver.lean
```

Observed output:

```text
P1-P2 at n=0: 5751/4096
P1-P3 at n=0: 8083/4096
P1-P7 at n=0: 10711/4096
```

The all-precision observer has exponentially sized grids. Its purpose is
to give an explicit primitive-recursive definition with elementary
uniform error estimates. The paper gives the precision analysis.
The Python certificates supplied separately resolve high precision.
`FiniteRoutes.lean` proves existence and optimality of each finite grid
witness, stability under rounded grid maps and soundness of binary
coverage of arbitrary rational parameters conditional on local leaf
certificates. The arithmetic observer is written in Lean's metatheory.

## Object iPRA and continuous curves

To check against the upstream repository, set `reportdir` to the absolute
path to this directory and `providerdir` to the desired checkout location.
Install Lean 4.32.0 with Lake and a working mathlib cache first.

```sh
git clone https://github.com/VladimirReshetnikov/ProveIt "$providerdir"
cd "$providerdir"
git checkout 09fe17194da14cdd100947737952e44100bb71b8
lake exe cache get Mathlib.Data.Fin.Tuple.Basic Mathlib.Data.Fin.VecNotation Mathlib.Tactic.FinCases Mathlib.Data.Fintype.Fin Mathlib.Tactic.Ring Mathlib.Tactic.LinearCombination Mathlib.Algebra.Ring.Hom.Defs Mathlib.Topology.EMetricSpace.BoundedVariation Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.Convex.Hull
lake build IPRADerivations.Core.Tactic IPRADerivations.Foundations.ApproximateWitness
lake env lean "$reportdir/ObjectIdentities.lean"
lake env lean "$reportdir/ObjectMesh.lean"
lake env lean "$reportdir/SurfaceDistance.lean"
```

Each of the last three commands returned exit status 0, with no warnings.
The first two files construct actual derivations in ordinary iPRA,
including five closed polynomial identities and a closed conditional
minimum-transfer schema. The third file is the earlier geometric
specification, now compiled with narrow imports. Its generic variation
and order lemmas check. `ExactTable` and `NumericalTable` are proposition
definitions. The files contain no `sorry` or new axioms. See the paper
for the remaining geometry, numerical soundness, and object-level
observer proof obligations.

## Additional concrete certificate checks

Run **lean DecimalTable.lean** for the integer decimal comparisons. In **IntegerReplay/**, run **sh build.sh** for the 219 exact integer replay assertions. Its README explains the chart enclosures that enter as geometric inputs. To regenerate the binary-tree terms from the CSV/JSON certificates, use **python3 code/emit_replay.py --out OUTPUT** from the package root. **ReplayCore.lean** contains the checker for those terms.

The revised **SurfaceDistance.lean** also proves contraction under absolute-value folding for points and curve variation, existence of a zero-coordinate hit for opposite endpoint signs, and the conditional reduced-route lower bound **route_le_curve**.
