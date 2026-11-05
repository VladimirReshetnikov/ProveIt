# Independent review of the norm38 seed split

The proposed ten-stage runner recompiles `SharingGateModel` and
`ForwardWitness38` as its first two stages; it does **not** inherit the two
objects from the earlier partial retry. The review separately rechecked that
prior retry's retained state, both successful source/object/log records, their
200 direct guard slots and the forward-to-gate provider link. The following
monolithic seed compile timed out and produced no accepted object; the prior
outer session 16634 exit 1 is author-reported in its retained README.

The split checker was rerun and verified the retained declaration/proof text;
all ten manifest snapshots and original source hashes match, stage imports
are topological, normalization precedes weighted degree, and none of the ten
output names collides with the inherited Jones base overlay. The runner differs
from the reviewed six-stage retry only in its fresh output path, manifest pin,
and scope/result wording. Its no-Lean preflight was independently rerun and
exited 0. It rechecks the Jones source/object/log, direct guards and overlay;
the new two gate/forward stages remain subject to their own monitored builds.

The [checker](check.py) exited 0 and produced [result.json](result.json).
Its SHA-256 is `c651285ac837f2f91db9fcb6b2080281bb0862f8a87d99c405120e0098f0cb09`;
the result SHA-256 is
`a0a944804efae3db4eb8954cadbe3d015844aac56fc9e05db6556dc1a85c6dbe`.
This is a source/provider observation, not a Lean replay, proof of the split
modules, all-model norm bridge or iPRA endpoint. The runner retains sampled
resource, incomplete package-transitive/dynamic ancestry and transient-change
limits.
