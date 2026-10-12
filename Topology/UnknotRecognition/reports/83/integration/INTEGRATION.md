# Integration contract and outstanding geometric obligations

## Placement and opt-in behavior

Keep this delivery as a separate research candidate until a native adapter
has its own geometric correctness proof and regression tests. Suggested
initial placement: `Topology/UnknotRecognition/reports/four_copy_patterns/`.
The package imports as `pattern_kernel` with its `code/` directory on
`PYTHONPATH`. No maintained recognizer file has been patched.

The implemented entry points are:

```python
from pattern_kernel.core import Tile, Block, solve
from pattern_kernel.verify import verify_result, verify_source_witness

# Tile vertices are 0..n-1; each edge occurrence has its own list position.
# Pass tuples for immutable Tile fields, and an integer for Block.copies.
result = solve(chain)                # chain: tuple[Block, ...]
assert verify_result(chain, result)  # no max-flow discovery is invoked here
```

`solve` validates a nonempty closed cubic serial chain. Tiles have nonempty,
injective, disjoint ordered input/output ports of equal width; every block
has the same width. Only connected tiles with more than four copies may be
capped. A disconnected tile of at most four copies remains explicit. Loops
and multiple edges are retained. Exponents are positive integers internally;
external JSON uses `0x` strings. A generic graph context is covered by the
paper's theorem, but is **not** accepted by the current serial-chain API.

## What a faithful native producer must certify

A future importer needs a source-bound record binding all of the following:

1. The actual terminal boundary pattern, including its source chamber/ball
   ownership, inherited pattern labels, and a spherical embedding.
2. A separate certificate that the containing 3-dimensional component is a
   ball. Sphere boundary and homology are not substitutes.
3. A complete tile decomposition with fresh interiors and edge occurrences,
   ordered injective interfaces, exact wiring, positive binary counts, and
   no silently omitted graph components or vertex-free circles.
4. Correct local degrees and closure/gluing degrees. Connectedness must refer
   to each abstract tile graph, not to a parallelity component or a source
   rank interval that happens to carry several separate strands.
5. Source charts mapping `(block, binary copy index, local edge index)` to
   native embedded pattern edges; analogous charts for vertex/color data.
6. Size and construction-time bounds for the descriptor and source charts.
   The proved width-independent bound concerns a **flat** descriptor. It
   does not justify uncontrolled recursive/DAG expansion of nested macros.

The all-dimensional source-parallelity packet is a plausible starting point
because it retains ports, fibre bits, source indices and attaching charts.
Its base genera or Euler characteristic summaries alone do not supply this
adapter. The current work does not prove that arbitrary normal cuts produce
the required connected repetitions.

## How to interpret a result

- `NO_LOW_CYCLIC_CUT`: the supplied abstract cubic graph has no cyclic cut of
  size at most three. Only after all geometric conditions above are verified
  may a native caller interpret this as essentiality of a ball pattern.
- `LOW_CYCLIC_CUT`: the supplied original graph has a marked cut of size at
  most three. `verify_source_witness` returns at most three original cut-edge
  addresses and two monochromatic-edge addresses. It does not construct an
  embedded noose/disc or pull that disc back through a hierarchy.
- Invalid input, unsupported tile type, timeout, cancellation, exhausted work
  or a failed proof check: decline the shortcut. Preserve the maintained
  recognizer's remaining budget and exact fallback. Never convert a declined
  query into essentiality, ball recognition, or unknot recognition.

Empty patterns and vertex-free circle components must be handled separately:
empty or exactly one circle is essential on a ball; multiple components of
that kind, or a circle plus a cubic graph, are inessential. Artificial
valence-two vertices are outside the cubic API and must not be used to hide
this distinction.

The source SHA-256 field is a convenient input binding, not a substitute for
semantic reconstruction. The checker rebuilds the kernel from the actual
supplied source, rechecks the connectivity hypotheses, and independently
checks finite graph evidence. Source witness checking scans actual tile
edges and seam colors. Only source schemas/local validation utilities are
shared with the producer; graph assembly and residual replay are separate.

## Source checkpoint and documentation clarification

The reviewed checkpoint is
`ed166080d7db14dd7a91d07788996f02947dd92a`.
`source_manifest.json` records the two pinned files central to this adapter.
This is not a full repository snapshot or a claim to have replayed upstream
geometry certificates.

The root README's October-11 summary emphasizes raw cuts and leaves bounded
admissible cores among the open tasks. The already-present
`synthesis/parallelity.tex` gives a bounded **inherited source core** with at
most 30T handles, and still leaves the admissible **patterned** hierarchy to
be constructed. The proposed README insertion records that distinction.
It does not assert a theorem in the repository was false.

The patch is a short context insertion. Review it against current `main`;
apply only after `git apply --check` succeeds. It contains no claim that this
new package is already integrated. Repository history may have advanced
since the recorded checkpoint.

## Acceptance work before native integration

Build source-complete geometric fixtures; compare expanded and encoded
patterns at small multiplicities; check that component inventories and edge
addresses match native source flags. Add forged-owner, omitted-component,
wrong-fibre, wrong-interface and disconnected-tile tests. Produce the
compressed noose/disc pullback, or restrict the integration to a decision
query that does not require it. Run the full native suite and paired native
recognition benchmarks under the same global budget, retaining regressions.

For complexity, account separately for descriptor discovery, pattern
transport, ball certification, repairs/resets, terminal-query count and
terminal-query size. The four-copy theorem removes numerical repetition
from one terminal cost; it proves none of those remaining global bounds.
