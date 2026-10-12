# Ordered interfaces for source parallelity bundles

This supplement adds a research prototype to the `normal_cut_parallelity`
packet at ProveIt commit `90e16db798c8d976bbe0c062e07cf20565e0b63a`.
It extracts the cyclic order of the finitely many core-facing boundary sides
without walking all intervening polygon copies. The core sides are called
*ports*. Three weighted interval-orbit queries recover:

1. Which port endpoints represent the same base vertex.
2. Which endpoint pairs are connected after removing the open port sides.
3. The interval-fibre transport between these endpoints.

Combining the second matching with each port's two endpoints produces the
cyclic boundary words. The first query distinguishes adjacent ports from
ports separated by an old-boundary arc. This distinction gives the correct
local replacement for a disc product:

| Attachment to the core | Local topological operation |
| --- | --- |
| Empty | Count an isolated ball |
| Entire boundary annulus | Add one relative 2-handle |
| `r` disjoint rectangular discs | Add `r-1` relative 1-handles after collar transport |

In particular, an attached disc with one proper rectangular attachment is
a collar addition. It does not add a 2-handle.

## Scope

The source geometry must first be authenticated using the maintained
`verify_normal_cut_parallelity`. The new verifier checks only the additional
cyclic, gap and fibre data, using independently reconstructed query systems
and the maintained weighted certificate checker. It does not call the
producer's query builder, decoder or traversal.

The prototype returns a local relative-handle **plan**. It does not perform
surgery, certify an essential boundary pattern, construct an admissible
handle structure, or decide whether a knot is trivial. The mathematical
section distinguishes the abstract polynomial reduction to the AHT theorem
from the trace-dependent bound for the repository's present orbit engine.

The elementary method of cutting a circle at marked edges is not claimed
as a new general combinatorial theorem. The contribution here is its
application to the complete all-dimensional source parallelity packet,
its signed source charts, the distinction between full and partial disc
attachments, and independently replayable implementation evidence.
The existence of polynomial parallelity algorithms with cyclic attachment
data is already covered by Lackenby's 2021 paper, Theorems 9.2 and 9.3:
https://people.maths.ox.ac.uk/lackenby/knp13nov20.pdf .
Report 68 in the repository already proves the general degree-two ordered
boundary principle (summarized in `synthesis/completion_theorems.tex`), using
endpoint count, sum, square sum and length to recover endpoint occurrences.
This prototype integrates that earlier principle with the later complete
source-parallelity geometry and adds zero-gap flags, fibre transport and
the partial-disc relative-handle plan.

## Files

- `parallelity_boundary.py`: compressed interface producer and disc replacement plan.
- `parallelity_boundary_verify.py`: independent reconstruction and certificate replay.
- `parallelity_boundary_reference.py`: finite oracle that explicitly walks the
  actual polygonal boundary, with a mandatory expansion cap.
- `test_parallelity_boundary.py`: focused regression and adversarial tests.
- `audit_parallelity_boundary.py`: reproducible test run, source/code pins,
  and complete small source-plus-interface certificates.
- `port_boundary_theorems.tex`: article section with complete proofs and
  further research questions; expected bibliography keys are `AHT2006`,
  `Lackenby2021`, and `Lackenby2026`.
- `parallelity_interface_section.tex`: compact 1,806-word main-article version
  with the same complete central proofs. Include this or the longer section,
  rather than both.
- `results/`: test transcript, audit summary and complete small examples.

## Reproduction

Set `PROVEIT_FAST` to the `Topology/UnknotRecognition/fast` directory in the
pinned ProveIt checkout. Run from this supplement's directory:

```bash
export PROVEIT_FAST=/path/to/ProveIt/Topology/UnknotRecognition/fast
PYTHONPATH="$PROVEIT_FAST:$PWD" python -m unittest -v test_parallelity_boundary
PYTHONPATH="$PROVEIT_FAST:$PWD" python audit_parallelity_boundary.py --output results
```

The rich-source tests also read the maintained
`synthesis/data/cut-complement-audit.json` and `parallelity-audit.json` files.
No additional Python package is required beyond the maintained repository.

Example usage:

```python
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from parallelity_boundary import parallelity_boundary_interface, disc_replacement_plan
from parallelity_boundary_verify import verify_parallelity_boundary_interface

source = normal_cut_parallelity(triangulation, coordinates, record_certificate=True)
assert source["status"] == "COMPLETE"
assert verify_normal_cut_parallelity(triangulation, coordinates, source["certificate"])

extra = parallelity_boundary_interface(source["geometry"], record_certificate=True)
assert extra["status"] == "COMPLETE"
assert verify_parallelity_boundary_interface(source["geometry"], extra["certificate"])
plan = disc_replacement_plan(extra["interface"], source["summary"]["base_profiles"])
```

Each producer shares its supplied discovery limit across its own queries.
An exhausted limit returns `INCONCLUSIVE` without an interface or certificate.
The verifier's operation cap covers all three supplied extra traces.
Cancellation callbacks propagate to the caller.

## Evidence

The focused audit performs 184 literal geometric comparisons, including 54
authenticated source comparisons, across 11 test methods. The synthetic
portion checks all 126 port subsets of discs with 1 through 6 boundary sides.
Other cases include annular and Möbius base charts, an interior-edge-cap base
with eight core ports, source relabellings, rich manifold fixtures, forged
certificates, shared limits, cancellation, and exact JSON replay for
`2**8192` parallel meridians on a four-tetrahedron source. Literal expansion
is deliberately refused for that large case.

The small full-circle example is the source `fibonacci_lst_02` with coordinate
rows `(0,0,1,1,1,0,0)` and `(1,1,1,1,0,0,0)`. Its base is a disc supplied
only by one selected 2-handle, and its eight ports cover its whole boundary.
The partial-collar example is three parallel meridians in the two-tetrahedron
layered torus. It has two attached disc bases, each meeting the core in one
proper interval, and two unattached ball products.

The audit records actual source and prototype hashes; `results/audit.json`
contains the measured time for the saved run. Runtime measurements are
observations on these inputs, not a proof of a global complexity bound.
