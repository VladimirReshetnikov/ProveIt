# Source-bound unused handles and initial admissible cores

## Compatibility and integration scope

The prototype is based on ProveIt commit
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`. It lives outside the maintained
recognizer and changes no production defaults. Add this package's `code/`
and the pinned repository's `Topology/UnknotRecognition/fast/` to
`PYTHONPATH`.

`unused_handles.py` imports the maintained source validator, source-handle
constructor, canonical diagram-exterior constructor and checker, and raw
reference-cell constructor. Several imports are private APIs; they should
be promoted to explicit supported interfaces before a maintained integration.
The adapted cancellation scheduler is credited in the module and preserves
the maintained queue order. The independent checker uses the distinct
maintained raw-cell construction, verifies geometric occurrence counts,
and reconstructs components by breadth-first search.

The mathematical contract is an **initial empty-pattern handle
subpresentation**. It does not produce a triangulation of the retained core,
normal-coordinate transport to that core, an explicit parametrization of
every discarded ball, or transport of a later boundary pattern. Those
features require further geometric work before the output can be fed to an
arbitrary existing triangulation-based hierarchy operator.

## Public entry points

```python
from unused_handles import (
    decompose_unused_handles,
    verify_unused_handle_certificate,
    compile_diagram_initial_core,
    verify_diagram_initial_core,
)
```

`decompose_unused_handles(triangulation, max_moves=None, check=...)` accepts
the finite orientable connected torus-boundary sources supported by the
maintained validator. It returns `DECOMPOSED` with a certificate, or
`INCONCLUSIVE` with no certificate when the supplied move cap is reached.
The `check` callback supports cooperative cancellation and its exception is
propagated. Invalid inputs can raise the maintained source-validation error.

The generic certificate has schema `unused-handles-v1` and these fields:

| Field | Meaning |
| --- | --- |
| `reduction_certificate` | Geometric source cancellation trace; native schema, empty pattern, `compressing_disc=None`. |
| `decomposition.components` | Canonically ordered blocks with component ID, original zero/one/two-handle IDs, and Euler characteristic. Only used one-handles appear inside blocks. |
| `decomposition.unused_handles` | Original unused one-handle ID and ordered pair of component endpoints. Loops and multiplicity remain explicit. |
| `decomposition.cycle_rank` | `number of unused handles − number of components + 1`. |
| `torus_case` | Arithmetic case name: `cycle`, `unique_core`, or `outside_irreducible_signature`. |
| `core_component` | Unique Euler-zero component ID when the arithmetic case supplies one; otherwise `None`. |

The verifier checks source identity, the entire cancellation trace, final
geometric degrees, local tetrahedral characteristic graphs, handle
ownership, component connectivity, quotient connectivity, and all stated
counts. It checks integer labels strictly, so Boolean labels cannot alias
integers. Its local characteristic check reconstructs formal facet ports
and edge strips even when multiple local occurrences share one global
handle ID.

**Generic acceptance certifies the geometric disc-cut decomposition only.**
It does not prove irreducibility or identify a component as a ball solely
because its Euler characteristic is one. The two supplied reducible
controls have the same arithmetic `cycle` case as a solid torus and are
accepted only as geometric decompositions.

`compile_diagram_initial_core(diagram, ...)` supplies the stronger contract.
Its certificate has schema `diagram-initial-core-v1`; it contains the exact
input PD diagram, its canonical triangulation, the unused-handle
certificate, and the outcome. The independent wrapper first checks the
canonical exterior of that precise classical one-component diagram.
Knot-exterior irreducibility then authenticates the ball/genus theorem.
The outcomes are:

- `UNKNOT`: a positive certificate from the all-ball, one-cycle branch.
- `ADMISSIBLE_CORE`: the inherited empty-pattern handle presentation of the
  unique Euler-zero block. This is an intermediate result and does not
  certify knottedness.
- `INCONCLUSIVE`: the source cancellation move cap was reached.

There is no `irreducible=True` option. A future source type needs its own
authenticated provenance or irreducibility witness before it can use the
topological interpretation. The abstract attachment-forest module can
consume the quotient records, subject to its own stated ball-piece
contract.

## Reproduction

From this extracted package, with `PROVEIT_FAST` set to the pinned
repository's `Topology/UnknotRecognition/fast/` directory:

```bash
export PYTHONPATH="$PWD/code:$PROVEIT_FAST"
python -m unittest discover -s tests -p test_unused_handles.py -v
python code/audit_unused_handle_fibonacci.py --output data/unused_handles_fibonacci_audit.json
python code/audit_unused_handles_k4.py --output data/unused_handles_k4_audit.json
python code/benchmark_unused_handles.py --repeats 5 \
  --output data/unused_handles_benchmark.json \
  --tex-output article/unused_handles_measurements.tex
```

Regina is optional for the production path. When it is installed, the
tests use it as an independent oracle on known solid-torus and reducible
controls. The delivered test log includes these checks without skips.

The retained data contains 48 pinned source triangulations, 16 checked
Fibonacci sizes with 302 verified edge-link rows, an independent local
graph audit, frozen positive/intermediate/reducible-control certificates,
and all benchmark repetitions. The four nonempty local graph types are
proved for all sources covered by the deletion-only construction; the
finite audit is a separate implementation check.

The benchmark compares complete source producer plus independent replay,
excluding serialization and diagram construction. The two arms emit
different source-level proof objects. It is neither a whole-recognizer
benchmark nor evidence of new knot coverage. Some finite timings regress.
The proved asymptotic gain is the explicit Fibonacci certificate-size
comparison: the native transported coordinate list has quadratic total
bit length, whereas the new incidence/component packet has
`O(t log(t+1))` bits. This is a comparison with that explicit native
representation, not a lower bound on every possible cocycle compression.
