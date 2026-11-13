# Independent source review: positive 75→74 and conditional reverse

The forward witness updates only h to h+1 and preserves positivity. The
`cast_forward` equality has the same orientation as the reviewed ring output
identity, so a 75 own-zero is transported to a 74 zero for arbitrary integer
ports. The reverse witness updates h to h−1 only under the explicit hypothesis
`1<h`; that bound proves both positivity and the premise of `P72Root.ι_tsub`.
The cast equality and use of the ring output identity are oriented correctly.
At h=1 the proposed predecessor is zero, so the strict hypothesis cannot be
removed from this witness map.

The checker pins the author files and the ring and subtraction sources,
reproduces the author receipt and separately reruns the reviewed literal
75/74 graph checker. It checks 200 positive coordinate controls and 2,025
signed guard-cut arithmetic controls. The finite checks do not replace the
ring identity or prove that any 74 graph zero satisfies h>1.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B reviews/ordinary14-75-74-positive-map-independent/check.py | cmp - reviews/ordinary14-75-74-positive-map-independent/observation.json`.
This is source/interface review only; Lean elaboration, an unconditional
reverse implication, provider coherence, model/iPRA endpoint and physical-byte
or PDF binding remain open. No Lean run was performed.
