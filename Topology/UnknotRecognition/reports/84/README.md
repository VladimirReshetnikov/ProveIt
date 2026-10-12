# Bounded-interface integral homology

**Research continuation for ProveIt — 12 October 2026.**

This package develops the integral-homology layer after a compressed normal
cut has been decomposed into a bounded inherited core and interval bundles.
The 25-page `article.pdf` contains the statements, proofs, limitations,
source audit, controlled measurements, and eight further research directions.
Its editable source is `article.tex` with the two generated table inputs in
`results/`.

**This is not a complete unknot recognizer.** It provides a proved exact
algebraic reduction and a tested research implementation. It does not change
`fastunknot` dispatch, authenticate native source geometry, implement an
embedding-ancestry checker, or establish a general quasi-polynomial running
time for recognition. No remote repository was modified.

## Main result

Write a cut as a core `K` plus interval bundles over connected surfaces `B_i`,
meeting the core over intervals and complete boundary circles in `∂B_i`.
An attached base is *saturated* when all of its boundary circles are attached.
Let `R` present `H_1(K; Z)`. Let `S_O` and `S_N` contain the oriented
boundary-sum vectors for saturated orientable and nonorientable bases, with
`t` columns in `S_N`. The interacting homology is presented by

```text
        [ R   S_O   S_N ]
    C = [ 0    0    2I  ].

    H_1(X; Z) ≅ coker(C) ⊕ Z^β ⊕ (Z/2)^μ.
```

The article gives complete binary formulas for `β`, `μ`, `H_0`, Euler
characteristic, and (under the three-manifold hypotheses) `H_2`. Matrix
dimensions do not grow with the numerical genera or unported multiplicities.
One saturated twisted base introduces only one additional generator and
one relation `2h+s=0`.

Further proved consequences include an exact sequence controlling twisted
torsion, an odd-primary invariance and torsion-exponent bound, a finite
endpoint-port reconstruction, canonical torsion runs without expanding
multiplicities, incidence-sensitive torsion bounds, and primitive-lattice
and parity constraints for certified descendants in `S^3`.

For a connected compact locally flat PL submanifold of `S^3`, with `b`
boundary components and total boundary genus `G`, the integral homology is
`(Z, Z^G, Z^(b-1), 0)`. A single sphere boundary then certifies a ball.
**The embedding hypothesis is essential.** The delivered boundary helper
computes the consequent only and explicitly does not verify that premise.

## Reproduce

Use Python 3.10 or later. The implementation itself uses only the standard
library. Independent tests require SymPy; this delivery was tested with
SymPy 1.14.0.

```sh
python -m pip install -r requirements-test.txt
python validate.py
python examples/replay_saved.py
python benchmark.py
python make_tables.py
sh build.sh
```

`build.sh` requires `pdflatex` with ordinary AMS, Latin Modern, microtype,
listings, fancyhdr, hyperref, and table packages. It runs three passes.
Existing results are delivered; rerunning validation or benchmarks replaces
the corresponding result files. Timings are machine-specific.

For direct use, execute Python from this package directory:

```python
from interface_homology import Core, Loop, Surface, Model
from interface_homology import condense, verify_condensation
from interface_homology.smith import smith, verify_smith, torsion_blocks

model = Model(
    Core(vertices=1, edges=((0, 0),)),
    (Surface(orientable=False, complexity=1, boundary=1,
             circles=(Loop(anchor=0, word=(1, 1)),)),),
)
packet = condense(model)
assert verify_condensation(model, packet)
certificate = smith(packet.matrix, cols=packet.relation_count)
assert verify_smith(packet.matrix, certificate,
                    cols=packet.relation_count)
rank = packet.rows - len(certificate.diagonal) + packet.free_bulk
assert rank == 1
assert torsion_blocks(certificate.diagonal, packet.two_torsion_bulk) == ((2, 1),)
```

This example has abstract group `Z ⊕ Z/2`. It is not labelled as a cut of a
knot exterior. `examples/mobius_certificate.json` saves the model, condensation,
and Smith trace. `examples/replay_saved.py` checks them without calling either
producer. The delivered replay was additionally tested with the producers
disabled. Resource exhaustion is never converted to a topological verdict.

## Validation and measurements

The delivery passes **25 unittest methods**, including **4,800 seeded cases**
across six independent comparison/property families. These include 1,200
expanded graph-of-surfaces comparisons, 1,800 Smith comparisons against
SymPy, 200 determinantal-divisor audits, 500 canonical torsion-run comparisons,
700 twisted-quotient checks, and 400 oriented port-cycle checks. Additional
deterministic tests cover malformed inputs, forged packets, resource caps,
empty cases, orientation reversals, and binary parameters `2^16384`.

The paired benchmark has 330 completed samples: 33 warmups and 297 measured
samples, including identical compressed A/A controls. Both main arms finish
the same abstract `H_0/H_1` query, replay their algebra, and serialize the
answer. They use the same Smith backend. The condensed arm additionally
replays its condensation. No source extraction or whole-knot recognition
is timed.

At genus 4096, the literal matrix has 8196 rows versus one condensed row;
the median paired expanded/condensed time ratio is 116.599. Tiny cases
regress: at genus zero the ratio is 0.647. All gains, regressions, and
controls are retained. The huge binary case has genus-related parameters
and multiplicity `N=2^16384`, an empty interacting matrix, and a 16,477-byte
serialized answer. It is an abstract algebra test, not a realizable normal
cut of a fixed small triangulation.

The reference Euclidean Smith routine is exact and independently replayable,
but **is not claimed to have a polynomial worst-case bit bound**. The
article's polynomial homology theorem uses a polynomial integer-normal-form
algorithm such as Kannan–Bachem. This distinction is explicit throughout.

## Repository placement and scope

Suggested additive placement:

```text
Topology/UnknotRecognition/research/interface_homology/
```

The audited repository revision is
`ed166080d7db14dd7a91d07788996f02947dd92a`. The existing repository already
has all-dimensional parallelity and a 30T-handle inherited complementary
core; this package does not claim to invent those components.

Read `integration/INTEGRATION.md` before attempting a native adapter.
`integration/CLAIMS.json` records proved, implemented, conditional, and
unimplemented claims. `integration/SOURCE_AUDIT.json` records inspected
source pins, and `integration/PROOF_REVIEW.md` describes proof dependencies
and hazards. `SHA256SUMS` authenticates the delivered files relative to the
package root; the ZIP is an additive delivery, not a patch that overwrites
production code.

The native repository regression suite and Regina cut oracle were **not**
run for this delivery. The tests are evidence for the algebraic component,
not a substitute for the article's proofs or for geometric integration.

License: MIT-0, matching the destination repository's stated project license.
