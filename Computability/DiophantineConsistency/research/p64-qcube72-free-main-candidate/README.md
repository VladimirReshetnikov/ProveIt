# 72-gate free-main graph: checked forward map

The generated positive-14-input graph replaces the 76Y carrier coordinate
`gamma` with positive `h`. It deletes the four rows computing `k−R`, its
successor subtraction, `U gamma`, and their difference; the existing carrier
row then uses `H h`. It has **72 operations**: 41 multiplications, 18 additions,
and 13 subtractions. [`graph.json`](graph.json) specifies every gate and
[`P64QCube72Free.lean`](P64QCube72Free.lean) is its generated Lean transcription.
[`build.py`](build.py) authenticates the parent graph, reproduces both files,
and checks topological order and liveness. `check_binding.py` independently
checks the rewrite and 120 finite carrier substitutions.

Three guarded Lean checks passed:

- [`graph`](observations/graph/result.json): the generated graph compiles.
- [`binding`](observations/binding/result.json):
  `P64QCube72FreeBinding.output` proves over any commutative ring that putting
  `h=U gamma−(k−R−1)` preserves the entire 76Y output. Its axiom report is
  `[propext]`.
- [`forward`](observations/forward/result.json):
  `P64QCube72FreeForward.exists_zero` sends every positive 76Y zero in a model
  of `IΣ₁` to a positive zero of this 72-gate graph, at the same ports. The
  proof uses the checked `FreeMainGraphForward.exists_positive_main_gap`,
  changes only coordinate 13, and applies the ring binding. Its axiom report
  is `[propext, Classical.choice, Quot.sound]`.

The source headers calling the latter two files “unchecked draft” predate
these clean checks; the source snapshots are retained unchanged so their
hashes match the receipts. Each check exited 0 without warnings or `sorryAx`,
with stable direct-provider guards and no monitor stop. Their output objects
and direct-input linkage are:

| Check | Output object SHA-256 | Direct project providers |
|---|---|---|
| graph | `942251ebbb10ba1497b6e51a0e52d8ddddb3bdbaac47f5b1f84c233d2e5d226d` | captured `P64Graph` |
| binding | `0844d34caa7f43afd5ca7cfb5201f72da402282e2379a7a6e257efbf01625c04` | this graph, checked `P64QCube76Y`, captured `P64QCubeMap` |
| forward | `badddf6e4c51093226b934f98d67236a6a28857e4679ccc90ca29978d9e333ea` | this binding, checked `FreeMainGraphForward` |

The receipts and logs include exact source and provider hashes, shadow
absence checks, command, sampled resource bounds, and result. The `check_*_lean.py`
wrappers use Lean `-M2400`, a 120-second timeout, sampled 3.5 GiB process-group
RSS and 10 GiB host-available-memory stops, nice 19 and idle I/O. These checks
guard direct providers and inherit their transitive, dynamic, and between-sample
ancestry; they are not a fresh source-only closure build. The compact44 base
build was not stopped.

A syntactic degree pass gives total witness degree at most 104, treating the
four ports as coefficients. A separate modular ray has degree 104 and nonzero
leading coefficient, so this bound is attained for the displayed test ports;
see [`degree-result.json`](degree-result.json) and [`ray-check.json`](ray-check.json).
Neither check establishes the degree for every port specialization.

**The converse is open.** The new positive `h` need not make
`h+(k−R−1)` divisible by `U`, so the obvious reverse substitution is not
generally available from the graph syntax. This packet establishes no reverse
existence implication, equivalence to consistency, iPRA endpoint, or claim of
global minimality. The previously documented partial obstruction is at
[`p64-qcube72-free-main-obstruction`](../p64-qcube72-free-main-obstruction/README.md).
