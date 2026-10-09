# Proposed integration into ProveIt

The original repository is unchanged. Suggested new destination:
`Topology/UnknotRecognition/research/rooted_disc_components/`.
This is a proposed directory, not a claim that it exists at the reviewed snapshot.

## Native admission gate

The maintained `normal_component_census`, `verify_normal_component_certificate`, and `normal_compressing_disk_count` APIs are relevant producers/checkers of componentwise information. They operate on supplied normal surfaces; they do not automatically supply a complete family of alternative collared fragments. The kernel belongs in a search table over alternatives, not as a replacement for a census of one fixed vector.

Before reducing a native table, establish:

1. The exact knot diagram and its authenticated exterior are bound to the stage.
2. Every candidate is an actual embedded fragment in its designated region. Every interface label denotes a specific collared boundary interval. Complete boundary maps and endpoint conventions are authenticated.
3. The partition and disc/non-disc flags are componentwise correct. Components with no future contact may leave the state, but not the selected witness or its cost.
4. All candidates in a reduction have one uniform future-geometry contract. The source region, active labels, map data, chosen torus cocycles, charge-ownership convention, and any necessary normal trace or framing belong in the type. No unrecorded same-component guard is allowed.
5. Component charges evaluate the owned physical-boundary chains in one common two-bit basis. Internal seams have zero charge, or an explicitly proved correction is supplied. Aggregate boundary parity is not a substitute.

Once these inputs are available, the actual reduction API is:

```python
from rooted_disc.kernel import reduce_candidates
from rooted_disc.verify import verify_reduction

retained, evidence = reduce_candidates(candidates, geometry_key=frame_digest)
assert verify_reduction(candidates, evidence, geometry_key=frame_digest)
```

Here `candidates` and `frame_digest` must come from a separately authenticated adapter. No such native adapter is represented as implemented by this snippet. The function retains original witness references and never interprets a sum of feature rows as a geometric surface.

## Final positive acceptance

Recover the actual selected assembly, reconstruct its geometry and component-local values, and replay it with the maintained source-bound verifier. A positive abstract answer is not itself an unknot certificate. When the root is a properly embedded disc with nonzero boundary class on the exterior torus, it is a compressing disc and gives the desired positive topological certificate.

## Negative answers and fallback

`verify_search` checks completeness only for the explicit finite layered language: it independently rebuilds all local option products, checks every retained basis, and recomputes the terminal answer. An accepted negative transcript means no success exists **in that language**. A negative knot verdict additionally requires proof that the language represents a witness for every positive source instance. Until such a producer theorem is established, failure in this stage is inconclusive and must leave the current complete fallback intact.

Do not run the “bad is permanent” rule across circle capping, arbitrary cutting, surgery, or other operations that lower first Betti number. It is a rule for certified interval-gluing phases. Do not identify exponentially many physical arcs with one label solely because their population is binary encoded.

## Suggested native evaluation

Keep this stage opt-in. Freeze a source revision and native corpus; preserve per-query source hashes and final verifier outcomes. Compare the same producer and geometry checks with and without table reduction, and include identical-arm controls. Charge interface construction, basis generation, source authentication, and final replay. Record resource exhaustion separately from completed negatives. The abstract controls already show that table reduction is not always profitable.

No native benchmark, optional Regina installation, or maintained production test suite was run here. The delivered tests and timings apply to the new standalone package only.
