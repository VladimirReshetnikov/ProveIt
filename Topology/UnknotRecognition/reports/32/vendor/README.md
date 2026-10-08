# Attribution of unchanged reference code

These four Python files were copied byte for byte from
`unknot_radical_transfer_20261007.zip`, a prior ProveIt research contribution
prepared on 7 October 2026. They are reference geometry/algebra, not a checkout
of the maintained `fastunknot` implementation.

| This package | Member in the prior archive |
|---|---|
| `braid_scan.py` | `radical_transfer_20261007/code/braid_scan.py` |
| `radical.py` | `radical_transfer_20261007/code/radical.py` |
| `reference_planar.py` | `radical_transfer_20261007/vendor/reference_planar.py` |
| `reference_cube.py` | `radical_transfer_20261007/vendor/reference_cube.py` |

The prior archive attributes `reference_planar.py` to the component-entropy
research package's static numerical excerpt, and `reference_cube.py` to the
twist-compression research package. The upstream planar source identity recorded
there is Git blob `1078526e7e7dbaf0b7267728105d870d94136769` in
`Topology/UnknotRecognition/fast/fastunknot/planar.py`. That attribution is
inherited; it is not a claim that this new package runs the current upstream
source tree.

The archive hash, member hashes, and byte-equality checks are recorded in
`../PROVENANCE.json`. All four files carry MIT-0 attribution. The new scanner
in `../src/graded_scan.py` adds absolute grading, local sparse cancellation,
canonical-boundary coefficient transport, and graded closure.
