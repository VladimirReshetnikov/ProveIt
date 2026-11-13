# Positive 75→74 map and conditional reverse — source draft

The proposed 75→74 map replaces slot 13 by `h+1`, preserving every other
positive coordinate. Its all-model proof uses the literal ring identity and
`internalZero_iff`; integer ports are arbitrary. The reverse map explicitly
assumes the 74 input has `h>1`, replaces h by natural `h−1`, and uses the
strict bound to establish both positivity and the subtraction cast.

The draft does not prove that the 74 graph's own zero forces `h>1`; that
requires binding the independently reviewed guard fact and five-unit product
extraction to the literal graph. Its dependencies are unelaborated. No Lean,
provider, iPRA, physical-byte or PDF claim is made.

Independent source review: [75/74 positive maps](../../reviews/ordinary14-75-74-positive-map-independent/README.md).
